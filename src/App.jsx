import { useState, useRef, useEffect, useMemo, useCallback, useId } from 'react'
import './App.css'

/* Portable Encrypted Vault — format v1
   Header (60 bytes, plaintext, authenticated as AD on every chunk):
   "PVLT" | version u8 | kdf u8 (1=Argon2id) | cipher u8 (1=XChaCha20-Poly1305 secretstream) | 0
   | opslimit u32 | memKiB u32 | chunkSize u32 | salt[16] | streamHeader[24]
   Body: repeated [u32 ctLen][ciphertext]; last chunk carries TAG_FINAL.
   Plaintext: [u32 manifestLen][manifest JSON][file bytes in manifest order]. Names live only inside the ciphertext. */

const FORMAT_VERSION = 1
const MAGIC = [0x50, 0x56, 0x4c, 0x54]
const HEADER_LEN = 60
const ABYTES = 17
const CHUNK = 1 << 20
const KDF = { ops: 3, memKiB: 65536 }
const MAX_BYTES = 512 * 1024 * 1024
const MAX_ENTRIES = 50000
const MAX_DEPTH = 32
const MAX_MANIFEST = 16 * 1024 * 1024
const ROOT = 'root'
const BAD = 'Wrong password or damaged vault.'

class VaultError extends Error {}
const CANCELLED = Object.assign(new Error('cancelled'), { cancelled: true })
const tick = () => new Promise((r) => setTimeout(r, 0))
let idCounter = 0
const newId = () => `n${++idCounter}`

/* ---------- crypto (libsodium: Argon2id + secretstream) ---------- */
let sodiumPromise
const getSodium = () =>
  (sodiumPromise ??= (async () => {
    const m = await import('libsodium-wrappers')
    const s = m.default ?? m
    await s.ready
    return s
  })().catch((e) => { sodiumPromise = null; throw e }))

const normalizePw = (p) => p.normalize('NFKC')

async function parseHeader(file) {
  if (file.size < HEADER_LEN + 4 + ABYTES) throw new VaultError('This file is too small to be a vault.')
  const h = new Uint8Array(await file.slice(0, HEADER_LEN).arrayBuffer())
  if (MAGIC.some((b, i) => h[i] !== b)) throw new VaultError('This is not a vault file.')
  if (h[4] !== FORMAT_VERSION) throw new VaultError(`Unsupported vault version (${h[4]}). Update the app to open it.`)
  if (h[5] !== 1 || h[6] !== 1 || h[7] !== 0) throw new VaultError('This vault uses an unknown algorithm.')
  const dv = new DataView(h.buffer)
  const ops = dv.getUint32(8, true), memKiB = dv.getUint32(12, true), chunk = dv.getUint32(16, true)
  if (ops < 1 || ops > 16 || memKiB < 8192 || memKiB > 1048576 || chunk < 4096 || chunk > 16 << 20)
    throw new VaultError('The vault header has invalid parameters.')
  return { bytes: h, ops, memKiB, chunk, salt: h.slice(20, 36), streamHeader: h.slice(36, 60) }
}

function serializeTree(nodes) {
  const index = buildIndex(nodes)
  const entries = [], blobs = []
  const walk = (id, prefix) => {
    for (const n of sortNodes(index.get(id) || [])) {
      const p = prefix ? `${prefix}/${n.name}` : n.name
      if (n.type === 'dir') { entries.push({ p, t: 'd', m: n.mtime || 0 }); walk(n.id, p) }
      else { entries.push({ p, t: 'f', s: n.size, m: n.mtime || 0 }); blobs.push(n.blob) }
    }
  }
  walk(ROOT, '')
  const manifest = new TextEncoder().encode(JSON.stringify({ v: 1, created: Date.now(), entries }))
  const len = new Uint8Array(4)
  new DataView(len.buffer).setUint32(0, manifest.length, true)
  return new Blob([len, manifest, ...blobs])
}

async function encryptVault(nodes, password, onProgress, cancelled) {
  const sodium = await getSodium()
  const plain = serializeTree(nodes)
  onProgress({ stage: 'Deriving key (Argon2id)…', done: 0, total: plain.size })
  await tick()
  const salt = sodium.randombytes_buf(sodium.crypto_pwhash_SALTBYTES)
  let key
  try {
    key = sodium.crypto_pwhash(32, normalizePw(password), salt, KDF.ops, KDF.memKiB * 1024, sodium.crypto_pwhash_ALG_ARGON2ID13)
  } catch { throw new VaultError('Key derivation failed. This device may not have enough memory.') }
  const { state, header: sh } = sodium.crypto_secretstream_xchacha20poly1305_init_push(key)
  sodium.memzero(key)
  const head = new Uint8Array(HEADER_LEN)
  head.set(MAGIC, 0); head[4] = FORMAT_VERSION; head[5] = 1; head[6] = 1
  const dv = new DataView(head.buffer)
  dv.setUint32(8, KDF.ops, true); dv.setUint32(12, KDF.memKiB, true); dv.setUint32(16, CHUNK, true)
  head.set(salt, 20); head.set(sh, 36)
  const parts = [head]
  for (let off = 0; off < plain.size; off += CHUNK) {
    if (cancelled()) throw CANCELLED
    const end = Math.min(off + CHUNK, plain.size)
    const msg = new Uint8Array(await plain.slice(off, end).arrayBuffer())
    const tag = end >= plain.size ? sodium.crypto_secretstream_xchacha20poly1305_TAG_FINAL : sodium.crypto_secretstream_xchacha20poly1305_TAG_MESSAGE
    const ct = sodium.crypto_secretstream_xchacha20poly1305_push(state, msg, head, tag)
    const l = new Uint8Array(4)
    new DataView(l.buffer).setUint32(0, ct.length, true)
    parts.push(l, ct)
    onProgress({ stage: 'Encrypting…', done: end, total: plain.size })
    await tick()
  }
  return new Blob(parts, { type: 'application/octet-stream' })
}

async function decryptVault(file, password, onProgress, cancelled) {
  const hdr = await parseHeader(file)
  const sodium = await getSodium()
  onProgress({ stage: 'Deriving key (Argon2id)…', done: 0, total: file.size })
  await tick()
  let key, state
  try {
    key = sodium.crypto_pwhash(32, normalizePw(password), hdr.salt, hdr.ops, hdr.memKiB * 1024, sodium.crypto_pwhash_ALG_ARGON2ID13)
  } catch { throw new VaultError('Key derivation failed. This device may not have enough memory for this vault.') }
  try { state = sodium.crypto_secretstream_xchacha20poly1305_init_pull(hdr.streamHeader, key) }
  catch { throw new VaultError(BAD) }
  finally { sodium.memzero(key) }
  const parts = []
  let pos = HEADER_LEN, plainTotal = 0, final = false
  while (pos < file.size) {
    if (cancelled()) throw CANCELLED
    if (final || pos + 4 > file.size) throw new VaultError(BAD)
    const len = new DataView(await file.slice(pos, pos + 4).arrayBuffer()).getUint32(0, true)
    if (len < ABYTES || len > hdr.chunk + ABYTES || pos + 4 + len > file.size) throw new VaultError(BAD)
    const ct = new Uint8Array(await file.slice(pos + 4, pos + 4 + len).arrayBuffer())
    let res
    try { res = sodium.crypto_secretstream_xchacha20poly1305_pull(state, ct, hdr.bytes) } catch { res = false }
    if (!res) throw new VaultError(BAD)
    parts.push(res.message)
    plainTotal += res.message.length
    if (plainTotal > MAX_BYTES + MAX_MANIFEST) throw new VaultError(BAD)
    if (res.tag === sodium.crypto_secretstream_xchacha20poly1305_TAG_FINAL) final = true
    pos += 4 + len
    onProgress({ stage: 'Decrypting and verifying…', done: pos, total: file.size })
    await tick()
  }
  if (!final) throw new VaultError(BAD) // truncated
  return parseContainer(new Blob(parts))
}

async function parseContainer(plain) {
  const fail = () => new VaultError('The vault authenticated but its contents are invalid.')
  if (plain.size < 4) throw fail()
  const mlen = new DataView(await plain.slice(0, 4).arrayBuffer()).getUint32(0, true)
  if (mlen > MAX_MANIFEST || 4 + mlen > plain.size) throw fail()
  let manifest
  try { manifest = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(await plain.slice(4, 4 + mlen).arrayBuffer())) }
  catch { throw fail() }
  if (manifest?.v !== 1 || !Array.isArray(manifest.entries) || manifest.entries.length > MAX_ENTRIES) throw fail()
  const nodes = emptyTree()
  const dirs = new Map([['', ROOT]])
  const seen = new Set()
  let off = 4 + mlen
  for (const e of manifest.entries) {
    if (!e || typeof e.p !== 'string' || (e.t !== 'f' && e.t !== 'd')) throw fail()
    const parts = e.p.split('/')
    if (parts.length > MAX_DEPTH || !parts.every(validName)) throw fail() // blocks absolute, ../ and odd paths
    const lower = e.p.toLowerCase()
    if (seen.has(lower)) throw fail()
    seen.add(lower)
    const parent = dirs.get(parts.slice(0, -1).join('/'))
    if (parent === undefined) throw fail()
    const id = newId()
    const mtime = Number.isFinite(e.m) ? e.m : 0
    if (e.t === 'd') {
      nodes[id] = { id, parent, name: parts.at(-1), type: 'dir', mtime }
      dirs.set(e.p, id)
    } else {
      if (!Number.isSafeInteger(e.s) || e.s < 0 || off + e.s > plain.size) throw fail()
      nodes[id] = { id, parent, name: parts.at(-1), type: 'file', size: e.s, mtime, blob: plain.slice(off, off + e.s) }
      off += e.s
    }
  }
  if (off !== plain.size) throw fail()
  return nodes
}

/* ---------- virtual file tree ---------- */
const emptyTree = () => ({ [ROOT]: { id: ROOT, parent: null, name: 'Vault', type: 'dir' } })
const ILLEGAL = /[/\\:*?"<>|\u0000-\u001f\u007f]/

function validName(n) {
  return typeof n === 'string' && n.length > 0 && n.length <= 255 && n !== '.' && n !== '..' && !ILLEGAL.test(n) && !/[. ]$/.test(n)
}
function sanitizeName(n) {
  let s = n.normalize('NFC').replace(ILLEGAL, '_').replace(/[. ]+$/, '').slice(0, 255)
  return s && s !== '.' && s !== '..' ? s : '_'
}
function buildIndex(nodes) {
  const m = new Map()
  for (const n of Object.values(nodes)) if (n.parent) (m.get(n.parent) || m.set(n.parent, []).get(n.parent)).push(n)
  return m
}
const sortNodes = (list) =>
  [...list].sort((a, b) => (a.type === b.type ? a.name.localeCompare(b.name, undefined, { numeric: true, sensitivity: 'base' }) : a.type === 'dir' ? -1 : 1))
const pathOf = (nodes, id) => {
  const out = []
  for (let n = nodes[id]; n && n.parent; n = nodes[n.parent]) out.unshift(n)
  return out
}
function treeStats(nodes) {
  let files = 0, folders = 0, bytes = 0
  for (const n of Object.values(nodes)) {
    if (n.id === ROOT) continue
    if (n.type === 'dir') folders++
    else { files++; bytes += n.size }
  }
  return { files, folders, bytes }
}
function nameProblem(nodes, parent, name, selfId) {
  if (!validName(name)) return 'Names can’t be empty, end in a dot or space, or contain / \\ : * ? " < > |'
  const clash = Object.values(nodes).some((n) => n.parent === parent && n.id !== selfId && n.name.toLowerCase() === name.toLowerCase())
  return clash ? 'An item with that name already exists here.' : ''
}

function addEntriesToTree(prev, parentId, entries) {
  const next = { ...prev }
  const key = (p, n) => `${p}\u0000${n.toLowerCase()}`
  const lookup = new Map()
  let { files, folders, bytes } = treeStats(prev)
  let count = files + folders
  for (const n of Object.values(next)) if (n.parent) lookup.set(key(n.parent, n.name), n.id)
  const baseDepth = pathOf(prev, parentId).length
  const unique = (p, name, isFile) => {
    if (!lookup.has(key(p, name))) return name
    const dot = isFile ? name.lastIndexOf('.') : -1
    const base = dot > 0 ? name.slice(0, dot) : name, ext = dot > 0 ? name.slice(dot) : ''
    for (let i = 2; ; i++) if (!lookup.has(key(p, `${base} (${i})${ext}`))) return `${base} (${i})${ext}`
  }
  const ensureDir = (p, name) => {
    const ex = lookup.get(key(p, name))
    if (ex && next[ex].type === 'dir') return ex
    const nm = unique(p, name, false), id = newId()
    next[id] = { id, parent: p, name: nm, type: 'dir', mtime: Date.now() }
    lookup.set(key(p, nm), id); count++
    return id
  }
  let added = 0
  for (const e of entries) {
    const parts = e.parts.map(sanitizeName)
    if (baseDepth + parts.length > MAX_DEPTH) return { error: 'Folders are nested too deeply for a vault.' }
    let p = parentId
    for (const d of e.file ? parts.slice(0, -1) : parts) p = ensureDir(p, d)
    if (!e.file) continue
    bytes += e.file.size; count++
    if (bytes > MAX_BYTES) return { error: `This preview release is limited to ${formatBytes(MAX_BYTES)} per vault.` }
    if (count > MAX_ENTRIES) return { error: `A vault can hold at most ${MAX_ENTRIES} items.` }
    const nm = unique(p, parts.at(-1), true), id = newId()
    next[id] = { id, parent: p, name: nm, type: 'file', size: e.file.size, mtime: e.file.lastModified || Date.now(), blob: e.file }
    lookup.set(key(p, nm), id); added++
  }
  return { nodes: next, added }
}

/* ---------- misc helpers ---------- */
function formatBytes(n = 0) {
  if (n < 1024) return `${n} B`
  const u = ['KB', 'MB', 'GB']
  let i = -1
  do { n /= 1024; i++ } while (n >= 1024 && i < 2)
  return `${n.toFixed(n < 10 ? 1 : 0)} ${u[i]}`
}
const formatDate = (ms) => (ms ? new Date(ms).toLocaleDateString(undefined, { year: 'numeric', month: 'short', day: 'numeric' }) : '—')
const plural = (n, w) => `${n} ${w}${n === 1 ? '' : 's'}`

function estimateStrength(pw) {
  if (!pw) return { score: 0, label: 'Empty' }
  let pool = 0
  if (/[a-z]/.test(pw)) pool += 26
  if (/[A-Z]/.test(pw)) pool += 26
  if (/\d/.test(pw)) pool += 10
  if (/[^A-Za-z0-9]/.test(pw)) pool += 33
  let bits = pw.length * Math.log2(pool || 1)
  if (new Set(pw).size < pw.length / 2) bits *= 0.6
  if (/(password|qwerty|123456|letmein)/i.test(pw)) bits = Math.min(bits, 20)
  const score = bits < 35 ? 1 : bits < 55 ? 2 : bits < 75 ? 3 : 4
  return { score, label: ['', 'Weak', 'Fair', 'Good', 'Strong'][score] }
}

function downloadBlob(blob, name) {
  const url = URL.createObjectURL(blob)
  const a = Object.assign(document.createElement('a'), { href: url, download: name })
  document.body.appendChild(a); a.click(); a.remove()
  setTimeout(() => URL.revokeObjectURL(url), 60000)
}

async function readDropped(dt) {
  const entries = [...dt.items].map((i) => i.webkitGetAsEntry?.()).filter(Boolean) // must run synchronously
  if (!entries.length) return [...dt.files].map((f) => ({ parts: [f.name], file: f }))
  const out = []
  const walk = async (en, prefix) => {
    if (en.isFile) {
      const file = await new Promise((res, rej) => en.file(res, rej))
      out.push({ parts: [...prefix, en.name], file })
    } else if (en.isDirectory) {
      const reader = en.createReader()
      let all = []
      for (;;) {
        const batch = await new Promise((res, rej) => reader.readEntries(res, rej))
        if (!batch.length) break
        all = all.concat(batch)
      }
      if (!all.length) out.push({ parts: [...prefix, en.name], file: null })
      for (const c of all) await walk(c, [...prefix, en.name])
    }
  }
  for (const en of entries) await walk(en, [])
  return out
}

/* ---------- small UI pieces ---------- */
const ICONS = {
  folder: 'M3 7a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v8a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z',
  file: 'M6 3h8l4 4v14H6z M14 3v4h4',
  lock: 'M6 11h12v9H6z M8 11V8a4 4 0 0 1 8 0v3',
  up: 'M12 19V5 M6 11l6-6 6 6',
  plus: 'M12 5v14 M5 12h14',
  folderplus: 'M3 7a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v8a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z M12 10v5 M9.5 12.5h5',
  trash: 'M4 7h16 M9 7V4h6v3 M6 7l1 13h10l1-13',
  edit: 'M4 20h4L19 9l-4-4L4 16z',
  download: 'M12 4v11 M7 11l5 5 5-5 M5 20h14',
  save: 'M5 4h11l3 3v13H5z M8 4v5h7V4 M8 20v-6h8v6',
  open: 'M3 8a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v1H3z M3 11h19l-2 8H5z',
  check: 'M5 12l5 5 10-10',
  warn: 'M12 3l10 18H2z M12 10v5 M12 18v.5',
  x: 'M6 6l12 12 M18 6L6 18',
}
const Icon = ({ name, size = 18 }) => (
  <svg className="icon" width={size} height={size} viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="1.8" strokeLinecap="round" strokeLinejoin="round" aria-hidden="true">
    {ICONS[name].split(' M').map((d, i) => <path key={i} d={(i ? 'M' : '') + d} />)}
  </svg>
)

function Modal({ title, onClose, children }) {
  const ref = useRef(null)
  const titleId = useId()
  useEffect(() => {
    const prev = document.activeElement
    ;(ref.current.querySelector('[data-autofocus]') || ref.current.querySelector('input,button'))?.focus()
    return () => prev?.focus?.()
  }, [])
  const onKeyDown = (e) => {
    if (e.key === 'Escape' && onClose) { e.stopPropagation(); onClose() }
    if (e.key !== 'Tab') return
    const f = [...ref.current.querySelectorAll('button,input,select,textarea')].filter((x) => !x.disabled)
    if (!f.length) return
    if (e.shiftKey && document.activeElement === f[0]) { e.preventDefault(); f.at(-1).focus() }
    else if (!e.shiftKey && document.activeElement === f.at(-1)) { e.preventDefault(); f[0].focus() }
  }
  return (
    <div className="backdrop">
      <div className="modal" role="dialog" aria-modal="true" aria-labelledby={titleId} ref={ref} onKeyDown={onKeyDown}>
        <h2 id={titleId}>{title}</h2>
        {children}
      </div>
    </div>
  )
}

function ConfirmDialog({ title, body, confirmLabel = 'OK', cancelLabel = 'Cancel', danger, onDone }) {
  return (
    <Modal title={title} onClose={() => onDone(false)}>
      <p className="modal-body">{body}</p>
      <div className="modal-actions">
        {cancelLabel && <button className="btn" onClick={() => onDone(false)}>{cancelLabel}</button>}
        <button className={`btn ${danger ? 'btn-danger' : 'btn-primary'}`} data-autofocus onClick={() => onDone(true)}>{confirmLabel}</button>
      </div>
    </Modal>
  )
}

function PromptDialog({ title, label, initial = '', confirmLabel, validate, onDone }) {
  const [v, setV] = useState(initial)
  const ref = useRef(null)
  const id = useId()
  useEffect(() => {
    const dot = initial.lastIndexOf('.')
    ref.current?.setSelectionRange(0, dot > 0 ? dot : initial.length)
  }, [initial])
  const problem = validate(v.trim())
  return (
    <Modal title={title} onClose={() => onDone(null)}>
      <form onSubmit={(e) => { e.preventDefault(); if (!problem) onDone(v.trim()) }}>
        <label htmlFor={id}>{label}</label>
        <input id={id} ref={ref} data-autofocus value={v} onChange={(e) => setV(e.target.value)} aria-invalid={!!problem} aria-describedby={`${id}-e`} autoComplete="off" spellCheck={false} />
        <p id={`${id}-e`} className="field-error" role="alert">{problem && v !== initial ? `Error: ${problem}` : ''}</p>
        <div className="modal-actions">
          <button type="button" className="btn" onClick={() => onDone(null)}>Cancel</button>
          <button type="submit" className="btn btn-primary" disabled={!!problem}>{confirmLabel}</button>
        </div>
      </form>
    </Modal>
  )
}

function SaveDialog({ defaultName, stats, onDone }) {
  const [name, setName] = useState(defaultName)
  const [pw, setPw] = useState('')
  const [pw2, setPw2] = useState('')
  const [show, setShow] = useState(false)
  const [ack, setAck] = useState(false)
  const [verify, setVerify] = useState(true)
  const s = useMemo(() => estimateStrength(pw), [pw])
  const todo = []
  if (!name.trim()) todo.push('Enter a file name.')
  if (pw.length < 8) todo.push('Use at least 8 characters (a long passphrase is better).')
  else if (pw !== pw2) todo.push('Make both passwords match.')
  if (!ack) todo.push('Confirm that you understand there is no password recovery.')
  const type = show ? 'text' : 'password'
  return (
    <Modal title="Encrypt and save vault" onClose={() => onDone(null)}>
      <form onSubmit={(e) => { e.preventDefault(); if (!todo.length) onDone({ name: name.trim(), password: pw, verify }) }}>
        <p className="modal-body">{plural(stats.files, 'file')} and {plural(stats.folders, 'folder')} · {formatBytes(stats.bytes)}</p>
        <label htmlFor="v-name">Vault file name</label>
        <div className="suffix-input"><input id="v-name" data-autofocus value={name} onChange={(e) => setName(e.target.value)} autoComplete="off" /><span>.vault</span></div>
        <label htmlFor="v-pw">Password</label>
        <input id="v-pw" type={type} value={pw} onChange={(e) => setPw(e.target.value)} autoComplete="new-password" spellCheck={false} />
        <div className="meter" aria-hidden="true">{[1, 2, 3, 4].map((i) => <span key={i} className={i <= s.score ? `on s${s.score}` : ''} />)}</div>
        <p className="hint" aria-live="polite">{pw ? `Estimated strength: ${s.label}. A rough hint, not a guarantee.` : 'Longer passphrases beat short complex ones.'}</p>
        <label htmlFor="v-pw2">Confirm password</label>
        <input id="v-pw2" type={type} value={pw2} onChange={(e) => setPw2(e.target.value)} autoComplete="new-password" spellCheck={false} />
        <label className="check"><input type="checkbox" checked={show} onChange={(e) => setShow(e.target.checked)} /> Show password while typing</label>
        <label className="check"><input type="checkbox" checked={verify} onChange={(e) => setVerify(e.target.checked)} /> Verify the vault decrypts before saving</label>
        <label className="check"><input type="checkbox" checked={ack} onChange={(e) => setAck(e.target.checked)} /> I understand a forgotten password means permanent data loss.</label>
        <p className="hint" aria-live="polite">{todo.length ? `Still needed: ${todo[0]}` : 'Ready to encrypt.'}</p>
        <div className="modal-actions">
          <button type="button" className="btn" onClick={() => onDone(null)}>Cancel</button>
          <button type="submit" className="btn btn-primary" disabled={todo.length > 0}><Icon name="lock" /> Encrypt and save</button>
        </div>
      </form>
    </Modal>
  )
}

function ExtractDialog({ count, canPickFolder, onDone }) {
  const [scope, setScope] = useState(count ? 'selected' : 'all')
  return (
    <Modal title="Extract files" onClose={() => onDone(null)}>
      <fieldset>
        <legend className="sr-only">What to extract</legend>
        <label className="check"><input type="radio" name="scope" checked={scope === 'selected'} disabled={!count} onChange={() => setScope('selected')} /> Selected items ({count})</label>
        <label className="check"><input type="radio" name="scope" checked={scope === 'all'} onChange={() => setScope('all')} /> Everything in the vault</label>
      </fieldset>
      <p className="hint"><Icon name="warn" size={14} /> Extracted files are saved unencrypted.</p>
      <div className="modal-actions">
        <button className="btn" onClick={() => onDone(null)}>Cancel</button>
        {canPickFolder
          ? <button className="btn btn-primary" data-autofocus onClick={() => onDone({ scope })}>Choose folder…</button>
          : <button className="btn btn-primary" data-autofocus onClick={() => onDone({ scope })}>Download file</button>}
      </div>
      {!canPickFolder && <p className="hint">This browser can’t write to folders, so each file downloads separately (folders are flattened into their names).</p>}
    </Modal>
  )
}

function ProgressPanel({ p, onCancel }) {
  const pct = p.total ? Math.min(100, Math.round((p.done / p.total) * 100)) : 0
  return (
    <Modal title={p.title}>
      <p className="modal-body" aria-live="polite">{p.stage}</p>
      <progress max="100" value={pct} aria-label={p.title} />
      <p className="hint">{pct}% · {formatBytes(p.done)} of {formatBytes(p.total)} · keep this tab open</p>
      <div className="modal-actions">
        {p.cancellable ? <button className="btn" data-autofocus onClick={onCancel}>Cancel</button> : <span className="hint">Finishing…</span>}
      </div>
    </Modal>
  )
}

/* ---------- pages ---------- */
function Home({ onCreate, onOpen }) {
  const support = [
    ['WebAssembly (encryption)', typeof WebAssembly !== 'undefined'],
    ['Secure context (HTTPS)', window.isSecureContext],
    ['Save to chosen location', !!window.showSaveFilePicker],
    ['Extract into a folder', !!window.showDirectoryPicker],
  ]
  return (
    <div className="home">
      <div className="home-copy">
        <h1>Keep private files in one locked container.</h1>
        <p className="lead">Encrypt files and folders in your browser into a single <b>.vault</b> file you can carry on a USB drive. Nothing is uploaded, and there are no accounts.</p>
        <div className="row">
          <button className="btn btn-primary btn-lg" onClick={onCreate}><Icon name="plus" /> Create a vault</button>
          <button className="btn btn-lg" onClick={onOpen}><Icon name="open" /> Open a vault</button>
        </div>
        <ul className="notes">
          <li>Argon2id key derivation with XChaCha20-Poly1305 authenticated encryption (libsodium).</li>
          <li>File names and folders are encrypted along with the contents.</li>
          <li>This is a container file, not a mounted drive. Passwords can’t be recovered, and this version hasn’t had an independent security review.</li>
        </ul>
        <h2 className="small-h">This browser</h2>
        <ul className="support">
          {support.map(([l, ok]) => <li key={l}><Icon name={ok ? 'check' : 'warn'} size={15} /> {l}: {ok ? 'available' : 'not available'}</li>)}
        </ul>
      </div>
      <svg className="dial" viewBox="0 0 240 240" role="img" aria-label="Combination dial illustration">
        <circle cx="120" cy="120" r="112" className="d-ring" />
        <circle cx="120" cy="120" r="86" className="d-ring d-thin" />
        {Array.from({ length: 48 }, (_, i) => {
          const a = (i / 48) * Math.PI * 2, long = i % 4 === 0
          const r1 = 112, r2 = long ? 96 : 103
          return <line key={i} x1={120 + Math.sin(a) * r1} y1={120 - Math.cos(a) * r1} x2={120 + Math.sin(a) * r2} y2={120 - Math.cos(a) * r2} className="d-tick" />
        })}
        <circle cx="120" cy="120" r="54" className="d-hub" />
        <path d="M104 126h32v22h-32z M110 126v-8a10 10 0 0 1 20 0v8" className="d-lock" />
      </svg>
    </div>
  )
}

function OpenPage({ onUnlock }) {
  const [file, setFile] = useState(null)
  const [hdr, setHdr] = useState(null)
  const [pw, setPw] = useState('')
  const [err, setErr] = useState('')
  const [busy, setBusy] = useState(false)
  const pick = async (f) => {
    setErr(''); setHdr(null); setPw('')
    if (!f) return
    setFile(f)
    try { setHdr(await parseHeader(f)) } catch (e) { setErr(e instanceof VaultError ? e.message : 'Could not read that file.') }
  }
  const submit = async (e) => {
    e.preventDefault()
    setBusy(true); setErr('')
    const msg = await onUnlock(file, pw)
    setPw('')
    if (msg) setErr(msg)
    setBusy(false)
  }
  return (
    <div className="narrow">
      <h1>Open a vault</h1>
      <label htmlFor="vault-file">Vault file</label>
      <input id="vault-file" type="file" accept=".vault" onChange={(e) => pick(e.target.files[0])} />
      {hdr && (
        <form onSubmit={submit}>
          <p className="hint">{file.name} · {formatBytes(file.size)} · format v{FORMAT_VERSION} · Argon2id ({hdr.memKiB / 1024} MiB, {hdr.ops} passes)</p>
          <label htmlFor="open-pw">Password</label>
          <input id="open-pw" type="password" data-autofocus autoFocus value={pw} onChange={(e) => setPw(e.target.value)} autoComplete="current-password" spellCheck={false} />
          <div className="row"><button className="btn btn-primary" disabled={!pw || busy}><Icon name="lock" /> Unlock</button></div>
        </form>
      )}
      <p className="field-error" role="alert">{err && `Error: ${err}`}</p>
    </div>
  )
}

/* ---------- file explorer ---------- */
function Explorer({ nodes, vaultName, mode, dirty, ops }) {
  const index = useMemo(() => buildIndex(nodes), [nodes])
  const [cwd, setCwd] = useState(ROOT)
  const [sel, setSel] = useState(() => new Set())
  const [anchor, setAnchor] = useState(null)
  const [dragging, setDragging] = useState(false)
  const fileIn = useRef(null)
  const dirIn = useRef(null)

  useEffect(() => {
    if (!nodes[cwd]) setCwd(ROOT)
    setSel((s) => { const n = new Set([...s].filter((id) => nodes[id])); return n.size === s.size ? s : n })
  }, [nodes, cwd])

  const items = useMemo(() => sortNodes(index.get(cwd) || []), [index, cwd])
  const crumbs = pathOf(nodes, cwd)
  const go = (id) => { setCwd(id); setSel(new Set()); setAnchor(null) }
  const select = (id, e) => {
    if (e.shiftKey && anchor) {
      const a = items.findIndex((i) => i.id === anchor), b = items.findIndex((i) => i.id === id)
      if (a >= 0 && b >= 0) { setSel(new Set(items.slice(Math.min(a, b), Math.max(a, b) + 1).map((i) => i.id))); return }
    }
    if (e.ctrlKey || e.metaKey) setSel((s) => { const n = new Set(s); n.has(id) ? n.delete(id) : n.add(id); return n })
    else setSel(new Set([id]))
    setAnchor(id)
  }
  const onKey = (e) => {
    const one = sel.size === 1 ? nodes[[...sel][0]] : null
    if (e.key === 'Delete' && sel.size) ops.remove([...sel])
    else if (e.key === 'F2' && one) ops.rename(one.id)
    else if (e.key === 'Enter' && one?.type === 'dir') go(one.id)
    else if (e.key === 'Backspace' && nodes[cwd].parent) go(nodes[cwd].parent)
    else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'a') { e.preventDefault(); setSel(new Set(items.map((i) => i.id))) }
    else if ((e.key === 'ArrowDown' || e.key === 'ArrowUp') && items.length) {
      e.preventDefault()
      const cur = items.findIndex((i) => i.id === [...sel].at(-1))
      const next = items[Math.max(0, Math.min(items.length - 1, cur < 0 ? 0 : cur + (e.key === 'ArrowDown' ? 1 : -1)))]
      select(next.id, e)
      document.getElementById(`item-${next.id}`)?.scrollIntoView({ block: 'nearest' })
    }
  }
  const fromInput = (e) => {
    ops.add(cwd, [...e.target.files].map((f) => ({ parts: f.webkitRelativePath ? f.webkitRelativePath.split('/') : [f.name], file: f })))
    e.target.value = ''
  }
  const onDrop = async (e) => {
    e.preventDefault(); setDragging(false)
    ops.add(cwd, await readDropped(e.dataTransfer))
  }
  const one = sel.size === 1 ? nodes[[...sel][0]] : null
  const stats = treeStats(nodes)

  return (
    <div className="explorer" onDragOver={(e) => { e.preventDefault(); setDragging(true) }} onDragLeave={(e) => { if (e.currentTarget === e.target) setDragging(false) }} onDrop={onDrop}>
      <div className="ex-head">
        <div>
          <h1 className="ex-title">{vaultName}.vault {dirty && <span className="badge">Unsaved changes</span>}</h1>
          <p className="hint">{mode === 'create' ? 'New vault' : 'Unlocked'} · {plural(stats.files, 'file')}, {plural(stats.folders, 'folder')} · {formatBytes(stats.bytes)}</p>
        </div>
        <div className="row">
          <button className="btn" onClick={() => ops.extract([...sel])}><Icon name="download" /> Extract</button>
          <button className="btn btn-primary" onClick={ops.save}><Icon name="save" /> Encrypt and save</button>
          <button className="btn" onClick={ops.close}>Close vault</button>
        </div>
      </div>

      {mode === 'create' && <p className="banner"><Icon name="warn" size={16} /> Keep your original files until you’ve opened the saved vault and checked it. Forgotten passwords can’t be recovered.</p>}

      <div className="toolbar" role="toolbar" aria-label="File actions">
        <button className="btn btn-sm" disabled={!nodes[cwd].parent} onClick={() => go(nodes[cwd].parent)} aria-label="Up one folder"><Icon name="up" /></button>
        <nav aria-label="Current folder" className="crumbs">
          <ol>
            <li><button onClick={() => go(ROOT)} aria-current={cwd === ROOT ? 'page' : undefined}>{vaultName}</button></li>
            {crumbs.map((c) => <li key={c.id}><button onClick={() => go(c.id)} aria-current={c.id === cwd ? 'page' : undefined}>{c.name}</button></li>)}
          </ol>
        </nav>
        <button className="btn btn-sm" onClick={() => fileIn.current.click()}><Icon name="plus" /> Add files</button>
        <button className="btn btn-sm" onClick={() => dirIn.current.click()}><Icon name="folderplus" /> Add folder</button>
        <button className="btn btn-sm" onClick={() => ops.newFolder(cwd)}><Icon name="folderplus" /> New folder</button>
        <button className="btn btn-sm" disabled={!one} onClick={() => ops.rename(one.id)}><Icon name="edit" /> Rename</button>
        <button className="btn btn-sm" disabled={!one || one.type !== 'file'} onClick={() => ops.download(one)}><Icon name="download" /> Download</button>
        <button className="btn btn-sm btn-danger-quiet" disabled={!sel.size} onClick={() => ops.remove([...sel])}><Icon name="trash" /> Delete</button>
        <input ref={fileIn} type="file" multiple hidden onChange={fromInput} />
        <input ref={dirIn} type="file" multiple hidden webkitdirectory="" onChange={fromInput} />
      </div>

      <div className="list-wrap">
        <div className="list-head" aria-hidden="true"><span>Name</span><span>Modified</span><span>Size</span></div>
        {items.length === 0 ? (
          <div className="empty">
            <Icon name="folder" size={36} />
            <p>{cwd === ROOT ? 'This vault is empty.' : 'This folder is empty.'} Drop files or folders here, or use Add files.</p>
          </div>
        ) : (
          <ul className="list" role="listbox" aria-multiselectable="true" aria-label={`Contents of ${nodes[cwd].name}`} tabIndex={0} onKeyDown={onKey} aria-activedescendant={sel.size ? `item-${[...sel].at(-1)}` : undefined}>
            {items.map((n) => (
              <li key={n.id} id={`item-${n.id}`} role="option" aria-selected={sel.has(n.id)} className={`row-item ${sel.has(n.id) ? 'selected' : ''}`} onClick={(e) => select(n.id, e)} onDoubleClick={() => n.type === 'dir' && go(n.id)}>
                <span className="cell-name"><Icon name={n.type === 'dir' ? 'folder' : 'file'} /> <span className="name">{n.name}</span></span>
                <span className="cell-meta">{formatDate(n.mtime)}</span>
                <span className="cell-meta">{n.type === 'dir' ? plural((index.get(n.id) || []).length, 'item') : formatBytes(n.size)}</span>
              </li>
            ))}
          </ul>
        )}
        {dragging && <div className="drop-overlay">Drop to add to “{nodes[cwd].name}”</div>}
      </div>
      <p className="hint foot">{sel.size ? `${plural(sel.size, 'item')} selected` : 'Click to select, double-click a folder to open it. Ctrl/Shift for multiple, F2 renames, Delete removes.'}</p>
    </div>
  )
}

/* ---------- app ---------- */
export default function App() {
  const [view, setView] = useState('home')
  const [nodes, setNodes] = useState(emptyTree)
  const [mode, setMode] = useState('create')
  const [vaultName, setVaultName] = useState('PrivateVault')
  const [dirty, setDirty] = useState(false)
  const [hasVault, setHasVault] = useState(false)
  const [modal, setModal] = useState(null)
  const [progress, setProgress] = useState(null)
  const [toast, setToast] = useState(null)
  const nodesRef = useRef(nodes)
  const resolver = useRef(null)
  const cancelRef = useRef(false)
  nodesRef.current = nodes

  useEffect(() => {
    if (!dirty) return
    const h = (e) => { e.preventDefault(); e.returnValue = '' }
    window.addEventListener('beforeunload', h)
    return () => window.removeEventListener('beforeunload', h)
  }, [dirty])
  useEffect(() => {
    if (!toast) return
    const t = setTimeout(() => setToast(null), 8000)
    return () => clearTimeout(t)
  }, [toast])

  const notify = useCallback((kind, text) => setToast({ kind, text }), [])
  const ask = useCallback((type, props = {}) => new Promise((resolve) => { resolver.current = resolve; setModal({ type, props }) }), [])
  const settle = (v) => { const r = resolver.current; resolver.current = null; setModal(null); r?.(v) }
  const report = (err) => notify('error', err?.cancelled ? 'Cancelled. Nothing was written.' : err instanceof VaultError ? err.message : 'Something went wrong. No data was changed.')
  const setProg = (title, cancellable = true) => (p) => setProgress({ title, cancellable, ...p })

  const startCreate = async () => {
    if (dirty && !(await ask('confirm', { title: 'Discard current vault?', body: 'You have unsaved changes that will be lost.', confirmLabel: 'Discard', danger: true }))) return
    setNodes(emptyTree()); setMode('create'); setVaultName('PrivateVault'); setDirty(false); setHasVault(true); setView('explorer')
  }
  const closeVault = async () => {
    if (dirty && !(await ask('confirm', { title: 'Close without saving?', body: 'Unsaved changes will be lost.', confirmLabel: 'Close vault', danger: true }))) return
    setNodes(emptyTree()); setDirty(false); setHasVault(false); setView('home')
  }

  const unlock = async (file, password) => {
    cancelRef.current = false
    try {
      const n = await decryptVault(file, password, setProg('Opening vault'), () => cancelRef.current)
      setNodes(n); setMode('open'); setVaultName(file.name.replace(/\.vault$/i, '')); setDirty(false); setHasVault(true); setView('explorer')
      return ''
    } catch (err) {
      return err?.cancelled ? 'Cancelled.' : err instanceof VaultError ? err.message : 'Could not open this vault.'
    } finally { setProgress(null) }
  }

  const saveVault = async () => {
    const stats = treeStats(nodes)
    if (!stats.files && !stats.folders) return notify('error', 'Add at least one file or folder first.')
    const res = await ask('save', { defaultName: vaultName, stats })
    if (!res) return
    const fileName = `${sanitizeName(res.name).replace(/\.vault$/i, '')}.vault`
    let handle = null
    if (window.showSaveFilePicker) { // called right after the click so the browser still allows it
      try { handle = await window.showSaveFilePicker({ suggestedName: fileName, types: [{ description: 'Encrypted vault', accept: { 'application/octet-stream': ['.vault'] } }] }) }
      catch (e) { if (e?.name === 'AbortError') return }
    }
    cancelRef.current = false
    try {
      const blob = await encryptVault(nodes, res.password, setProg('Encrypting vault'), () => cancelRef.current)
      if (res.verify) {
        const check = await decryptVault(blob, res.password, setProg('Verifying vault'), () => cancelRef.current)
        if (Object.keys(check).length !== Object.keys(nodes).length) throw new VaultError('Verification failed. The vault was not saved.')
      }
      setProgress({ title: 'Saving vault', stage: 'Writing file…', done: 1, total: 1, cancellable: false })
      if (handle) { const w = await handle.createWritable(); await w.write(blob); await w.close() }
      else downloadBlob(blob, fileName)
      setDirty(false); setVaultName(fileName.replace(/\.vault$/i, '')); setProgress(null)
      await ask('confirm', { title: 'Vault saved', body: `${fileName} (${formatBytes(blob.size)}) is ready. Open it once to confirm it works before you delete any originals.`, confirmLabel: 'Done', cancelLabel: null })
    } catch (err) { setProgress(null); report(err) }
  }

  const add = (parentId, entries) => {
    if (!entries.length) return
    const r = addEntriesToTree(nodesRef.current, parentId, entries)
    if (r.error) return notify('error', r.error)
    setNodes(r.nodes); setDirty(true)
    notify('ok', `Added ${plural(r.added, 'file')} to the vault.`)
  }
  const newFolder = async (parentId) => {
    const name = await ask('prompt', { title: 'New folder', label: 'Folder name', confirmLabel: 'Create', validate: (v) => nameProblem(nodesRef.current, parentId, v, null) })
    if (name) add(parentId, [{ parts: [name], file: null }])
  }
  const rename = async (id) => {
    const n = nodesRef.current[id]
    const name = await ask('prompt', { title: `Rename ${n.type === 'dir' ? 'folder' : 'file'}`, label: 'New name', initial: n.name, confirmLabel: 'Rename', validate: (v) => nameProblem(nodesRef.current, n.parent, v, id) })
    if (!name || name === n.name) return
    setNodes((p) => ({ ...p, [id]: { ...p[id], name } })); setDirty(true)
  }
  const remove = async (ids) => {
    const ok = await ask('confirm', { title: `Delete ${plural(ids.length, 'item')}?`, body: 'They’re removed from the vault once you save. Your original files on disk aren’t touched.', confirmLabel: 'Delete', danger: true })
    if (!ok) return
    setNodes((prev) => {
      const index = buildIndex(prev), kill = new Set()
      const walk = (id) => { kill.add(id); (index.get(id) || []).forEach((c) => walk(c.id)) }
      ids.forEach(walk)
      return Object.fromEntries(Object.entries(prev).filter(([k]) => !kill.has(k)))
    })
    setDirty(true)
  }
  const download = (n) => downloadBlob(n.blob.slice(0, n.size, 'application/octet-stream'), n.name)

  const extract = async (selIds) => {
    const res = await ask('extract', { count: selIds.length, canPickFolder: !!window.showDirectoryPicker })
    if (!res) return
    let dir = null
    if (window.showDirectoryPicker) {
      try { dir = await window.showDirectoryPicker({ mode: 'readwrite' }) }
      catch (e) { if (e?.name === 'AbortError') return; return notify('error', 'Could not open that folder.') }
    }
    const cur = nodesRef.current, index = buildIndex(cur), items = []
    const walk = (n, prefix) => {
      const parts = [...prefix, n.name]
      items.push({ parts, node: n })
      if (n.type === 'dir') sortNodes(index.get(n.id) || []).forEach((c) => walk(c, parts))
    }
    const picked = new Set(selIds)
    const hasPickedAncestor = (n) => pathOf(cur, n.id).slice(0, -1).some((a) => picked.has(a.id))
    const roots = res.scope === 'all' ? sortNodes(index.get(ROOT) || []) : selIds.map((i) => cur[i]).filter((n) => n && !hasPickedAncestor(n))
    roots.forEach((r) => walk(r, []))
    const files = items.filter((i) => i.node.type === 'file')
    if (!items.length) return notify('error', 'Nothing to extract.')
    cancelRef.current = false
    try {
      if (!dir) { files.forEach((f) => downloadBlob(f.node.blob.slice(0, f.node.size, 'application/octet-stream'), f.node.name)); return notify('ok', `Downloaded ${plural(files.length, 'file')}.`) }
      const conflicts = []
      for (const it of files) {
        try {
          let d = dir
          for (const p of it.parts.slice(0, -1)) d = await d.getDirectoryHandle(p)
          await d.getFileHandle(it.parts.at(-1))
          conflicts.push(it.parts.join('/'))
        } catch { /* not found: no conflict */ }
      }
      if (conflicts.length && !(await ask('confirm', { title: 'Replace existing files?', body: `${plural(conflicts.length, 'file')} in that folder will be overwritten, for example ${conflicts.slice(0, 3).join(', ')}.`, confirmLabel: 'Overwrite', danger: true }))) return
      const total = files.reduce((s, f) => s + f.node.size, 0)
      let done = 0
      for (const it of items) {
        if (cancelRef.current) throw CANCELLED
        let d = dir
        const dirParts = it.node.type === 'dir' ? it.parts : it.parts.slice(0, -1)
        for (const p of dirParts) d = await d.getDirectoryHandle(p, { create: true })
        if (it.node.type === 'file') {
          const w = await (await d.getFileHandle(it.parts.at(-1), { create: true })).createWritable()
          await w.write(it.node.blob); await w.close()
          done += it.node.size
        }
        setProgress({ title: 'Extracting', stage: it.parts.join('/'), done, total, cancellable: true })
        await tick()
      }
      setProgress(null)
      notify('ok', `Extracted ${plural(files.length, 'file')}.`)
    } catch (err) {
      setProgress(null)
      notify('error', err?.cancelled ? 'Extraction stopped. Some files may already have been written.' : 'Extraction failed. Check that the folder is writable and has free space.')
    }
  }

  const ops = { add, newFolder, rename, remove, download, extract, save: saveVault, close: closeVault }

  let dialog = null
  if (progress) dialog = <ProgressPanel p={progress} onCancel={() => { cancelRef.current = true }} />
  else if (modal) {
    const { type, props } = modal
    if (type === 'confirm') dialog = <ConfirmDialog {...props} onDone={settle} />
    else if (type === 'prompt') dialog = <PromptDialog {...props} onDone={settle} />
    else if (type === 'save') dialog = <SaveDialog {...props} onDone={settle} />
    else if (type === 'extract') dialog = <ExtractDialog {...props} onDone={settle} />
  }

  return (
    <div className="app">
      <header className="topbar">
        <button className="brand" onClick={() => setView(hasVault && view === 'explorer' ? 'explorer' : 'home')}><Icon name="lock" size={20} /> Portable Vault</button>
        <nav aria-label="Main">
          <button className="link" onClick={startCreate}>New vault</button>
          <button className="link" onClick={() => setView('open')}>Open vault</button>
          {hasVault && <button className="link" aria-current={view === 'explorer' ? 'page' : undefined} onClick={() => setView('explorer')}>Current vault</button>}
        </nav>
      </header>
      <main className={view === 'explorer' ? 'page page-wide' : 'page'}>
        {view === 'home' && <Home onCreate={startCreate} onOpen={() => setView('open')} />}
        {view === 'open' && <OpenPage onUnlock={unlock} />}
        {view === 'explorer' && <Explorer nodes={nodes} vaultName={vaultName} mode={mode} dirty={dirty} ops={ops} />}
      </main>
      <div className="toast-region" role="status" aria-live="polite">
        {toast && (
          <div className={`toast toast-${toast.kind}`}>
            <Icon name={toast.kind === 'ok' ? 'check' : 'warn'} size={16} />
            <span>{toast.kind === 'ok' ? 'Done: ' : 'Error: '}{toast.text}</span>
            <button className="icon-btn" onClick={() => setToast(null)} aria-label="Dismiss message"><Icon name="x" size={14} /></button>
          </div>
        )}
      </div>
      {dialog}
    </div>
  )
}