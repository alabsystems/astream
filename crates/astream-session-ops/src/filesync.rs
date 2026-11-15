// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Content-addressed workspace file synchronization (`docs/ROADMAP.md` "WASM and file-sync").
//!
//! Computes deterministic SHA-256 chunk manifests ([`FileSyncManifest`]) over bounded relative
//! workspace trees, computes minimal missing-chunk wire deltas ([`FileSyncDelta`]), frames
//! deltas inside `astream_wire::Frame` envelopes, and applies deltas atomically with strict
//! path-traversal rejection (`..`, leading `/`, NUL bytes, backslashes, symlinks) and
//! Clean-origin monotone revision fencing ([`filesync_rev_advance`], [`filesync_chunk_clamp`];
//! `Astream.Engine.TlaFileSync`).

#![allow(
    clippy::manual_map,
    clippy::map_entry,
    clippy::needless_match,
    clippy::only_used_in_recursion,
    clippy::type_complexity
)]

use astream_digest::Sha256;
use astream_wire::frame::decode_frame_slice;
use astream_wire::Frame;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

#[cfg(clean_islands)]
#[path = "filesync_island.rs"]
mod filesync_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn filesync_rev_advance(cur_rev: u64, proposed_rev: u64) -> u64 {
    if cur_rev < proposed_rev {
        proposed_rev
    } else {
        cur_rev
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn filesync_chunk_clamp(chunk_len: u64, max_chunk: u64) -> u64 {
    if chunk_len < max_chunk {
        chunk_len
    } else {
        max_chunk
    }
}
#[cfg(clean_islands)]
pub use filesync_island::{filesync_chunk_clamp, filesync_rev_advance};

contract_fn! {
    /// Verified check that an incoming file-sync manifest revision `next_rev` strictly
    /// advances `cur_rev` (`cur_rev < next_rev`), linked via `clean-kernel-defeq` to
    /// `filesync_rev_is_fresh_isl`.
    #[must_use]
    pub const fn filesync_rev_is_fresh(cur_rev: u64, next_rev: u64) -> bool
    clauses [ensures result == (cur_rev < next_rev)]
    {
        cur_rev < next_rev
    }
}

/// Wire magic for encoded [`FileSyncDelta`] payloads (`"AFSY"`).
pub const FILESYNC_MAGIC: [u8; 4] = *b"AFSY";

/// Wire format version `1` for [`FileSyncDelta`].
pub const FILESYNC_VERSION: u8 = 1;

/// Fixed chunk size (`64 KiB`) for content-addressed deduplication.
pub const SYNC_CHUNK_BYTES: usize = 64 * 1024;

/// Hard ceiling (`2048`) on files tracked in one [`FileSyncManifest`].
pub const MAX_SYNC_FILES: usize = 2048;

/// Hard ceiling (`16 MiB`, matching `astream_wire::MAX_PAYLOAD_LEN`) on one [`FileSyncDelta`].
pub const MAX_SYNC_DELTA_BYTES: usize = 16 * 1024 * 1024;

/// Hard ceiling (`4096`) on total chunk references across one manifest or delta.
pub const MAX_SYNC_CHUNKS: usize = 4096;

/// Metadata and ordered 64 KiB SHA-256 chunk list for one relative file path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileEntry {
    /// Normalized `/` relative path (no leading `/`, no `.` or `..` segments).
    pub rel_path: String,
    /// Total byte length of the file.
    pub size: u64,
    /// Ordered SHA-256 digests of each [`SYNC_CHUNK_BYTES`] slice.
    pub chunks: Vec<[u8; 32]>,
}

/// Deterministic content-addressed snapshot of a workspace directory at `revision`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileSyncManifest {
    /// Monotone workspace revision number.
    pub revision: u64,
    /// Lexicographically ordered relative path -> [`FileEntry`].
    pub files: BTreeMap<String, FileEntry>,
}

/// Minimal wire delta transforming a target workspace from an older manifest to `target`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileSyncDelta {
    /// Target manifest after applying this delta.
    pub target: FileSyncManifest,
    /// Deduplicated chunk blobs (`sha256 -> raw bytes`) absent on the receiver.
    pub chunks: BTreeMap<[u8; 32], Vec<u8>>,
    /// Relative paths present on the receiver's previous manifest that must be deleted.
    pub deleted_paths: Vec<String>,
}

fn str_to_owned_string(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

fn slice_to_owned_vec(s: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(s);
    out
}

/// Validate a relative workspace path, rejecting empty strings, leading/trailing `/`,
/// backslashes, NUL bytes, `.` and `..` segments, and paths > 512 bytes.
pub fn validate_sync_rel_path(rel: &str) -> Result<(), String> {
    if rel.is_empty() || rel.len() > 512 {
        return Err(str_to_owned_string("invalid relative path length"));
    }
    if rel.starts_with('/') || rel.ends_with('/') {
        return Err(str_to_owned_string(
            "relative path must not start or end with `/`",
        ));
    }
    let bytes = rel.as_bytes();
    let mut b_idx = 0usize;
    while b_idx < bytes.len() {
        if let Some(&b) = bytes.get(b_idx) {
            if b == 0 || b == b'\\' {
                return Err(str_to_owned_string("forbidden byte in relative path"));
            }
        }
        b_idx = b_idx.saturating_add(1);
    }
    for seg in rel.split('/') {
        if seg.is_empty() || seg == "." || seg == ".." {
            return Err(str_to_owned_string("forbidden path segment"));
        }
    }
    Ok(())
}

fn validate_manifest_structure(manifest: &FileSyncManifest) -> io::Result<()> {
    if manifest.files.len() > MAX_SYNC_FILES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "manifest exceeds MAX_SYNC_FILES",
        ));
    }
    let mut total_chunks = 0usize;
    for (key, entry) in &manifest.files {
        if key != &entry.rel_path {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "manifest key mismatch with entry rel_path",
            ));
        }
        if let Err(m) = validate_sync_rel_path(&entry.rel_path) {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, m));
        }
        total_chunks = total_chunks.saturating_add(entry.chunks.len());
        if total_chunks > MAX_SYNC_CHUNKS {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "manifest exceeds MAX_SYNC_CHUNKS",
            ));
        }
        let bytes = entry.rel_path.as_bytes();
        let mut idx = 0usize;
        while idx < bytes.len() {
            if bytes.get(idx) == Some(&b'/') {
                if let Some(anc) = entry.rel_path.get(..idx) {
                    if manifest.files.contains_key(anc) {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidInput,
                            "file and directory prefix collision in manifest",
                        ));
                    }
                }
            }
            idx = idx.saturating_add(1);
        }
    }
    Ok(())
}

fn validate_deleted_paths(
    deleted_paths: &[String],
    files: &BTreeMap<String, FileEntry>,
) -> io::Result<()> {
    if deleted_paths.len() > MAX_SYNC_FILES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "deleted_paths exceeds MAX_SYNC_FILES",
        ));
    }
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut rest = deleted_paths;
    while let [del, tail @ ..] = rest {
        if let Err(m) = validate_sync_rel_path(del) {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, m));
        }
        if !seen.insert(del.as_str()) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "duplicate path in deleted_paths",
            ));
        }
        if files.contains_key(del) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "deleted_paths overlaps target files",
            ));
        }
        rest = tail;
    }
    Ok(())
}

fn sha256_bytes(data: &[u8]) -> [u8; 32] {
    Sha256::digest_slice(data)
}

fn scan_dir_recursive(
    root: &Path,
    cur_dir: &Path,
    prefix: &str,
    files: &mut BTreeMap<String, FileEntry>,
    chunk_store: Option<&mut BTreeMap<[u8; 32], Vec<u8>>>,
    total_chunks: &mut usize,
) -> io::Result<()> {
    let mut entries = Vec::new();
    for item in fs::read_dir(cur_dir)? {
        let entry = item?;
        let ft = entry.file_type()?;
        if ft.is_symlink() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "symlinks are refused by FileSyncManifest",
            ));
        }
        let Ok(name) = entry.file_name().into_string() else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "non-UTF-8 filename refused by FileSyncManifest",
            ));
        };
        entries.push((name, entry.path(), ft.is_dir(), ft.is_file()));
    }
    fn cmp_sync_dir_entry(
        a: &(String, PathBuf, bool, bool),
        b: &(String, PathBuf, bool, bool),
    ) -> core::cmp::Ordering {
        a.0.cmp(&b.0)
    }
    entries.sort_by(cmp_sync_dir_entry);

    let mut store_opt = chunk_store;
    let mut rest_entries = entries.as_slice();
    while let [(name, full_path, is_dir, is_file), tail @ ..] = rest_entries {
        let rel = if prefix.is_empty() {
            name.clone()
        } else {
            let mut s = String::new();
            s.push_str(prefix);
            s.push('/');
            s.push_str(name);
            s
        };
        if let Err(msg) = validate_sync_rel_path(&rel) {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, msg));
        }
        if *is_dir {
            let reborrow = match store_opt.as_deref_mut() {
                Some(m) => Some(m),
                None => None,
            };
            scan_dir_recursive(root, full_path, &rel, files, reborrow, total_chunks)?;
        } else if *is_file {
            if files.len() >= MAX_SYNC_FILES {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "workspace exceeds MAX_SYNC_FILES",
                ));
            }
            let mut f = File::open(full_path)?;
            let mut chunks = Vec::new();
            let mut total_size = 0u64;
            let mut io_buf = [0u8; 8192];
            loop {
                let mut chunk_buf = Vec::new();
                while chunk_buf.len() < SYNC_CHUNK_BYTES {
                    let want = SYNC_CHUNK_BYTES.saturating_sub(chunk_buf.len());
                    let cap = if want < io_buf.len() {
                        want
                    } else {
                        io_buf.len()
                    };
                    let Some(dst_buf) = io_buf.get_mut(..cap) else {
                        break;
                    };
                    let n = f.read(dst_buf)?;
                    if n == 0 {
                        break;
                    }
                    if let Some(read_slice) = dst_buf.get(..n) {
                        chunk_buf.extend_from_slice(read_slice);
                    }
                }
                if chunk_buf.is_empty() {
                    break;
                }
                if *total_chunks >= MAX_SYNC_CHUNKS {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "workspace exceeds MAX_SYNC_CHUNKS",
                    ));
                }
                let filled = chunk_buf.len();
                let clamped = filesync_chunk_clamp(filled as u64, SYNC_CHUNK_BYTES as u64) as usize;
                let Some(slice) = chunk_buf.get(..clamped) else {
                    break;
                };
                let digest = sha256_bytes(slice);
                chunks.push(digest);
                if let Some(ref mut map) = store_opt {
                    if !map.contains_key(&digest) {
                        map.insert(digest, slice_to_owned_vec(slice));
                    }
                }
                *total_chunks = total_chunks.saturating_add(1);
                total_size = total_size.saturating_add(clamped as u64);
                if filled < SYNC_CHUNK_BYTES {
                    break;
                }
            }
            files.insert(
                rel.clone(),
                FileEntry {
                    rel_path: rel,
                    size: total_size,
                    chunks,
                },
            );
        }
        rest_entries = tail;
    }
    Ok(())
}

impl FileSyncManifest {
    /// Scan `root` deterministically at `revision` and return `(manifest, chunk_map)`.
    pub fn scan_with_chunks(
        root: &Path,
        revision: u64,
    ) -> io::Result<(Self, BTreeMap<[u8; 32], Vec<u8>>)> {
        let mut files = BTreeMap::new();
        let mut chunks = BTreeMap::new();
        let mut total_chunks = 0usize;
        scan_dir_recursive(
            root,
            root,
            "",
            &mut files,
            Some(&mut chunks),
            &mut total_chunks,
        )?;
        Ok((Self { revision, files }, chunks))
    }

    /// Scan `root` deterministically at `revision`, recording chunk SHA-256 digests only.
    pub fn scan(root: &Path, revision: u64) -> io::Result<Self> {
        let mut files = BTreeMap::new();
        let mut total_chunks = 0usize;
        scan_dir_recursive(root, root, "", &mut files, None, &mut total_chunks)?;
        Ok(Self { revision, files })
    }

    /// Set of all unique chunk digests referenced across `self.files`.
    #[must_use]
    pub fn known_chunks(&self) -> BTreeSet<[u8; 32]> {
        let mut set = BTreeSet::new();
        for entry in self.files.values() {
            for &digest in &entry.chunks {
                set.insert(digest);
            }
        }
        set
    }
}

/// Compute the minimal [`FileSyncDelta`] from `receiver_manifest` (or `None` when empty) to
/// `(sender_manifest, sender_chunks)`, shipping only chunks absent from `receiver_manifest`.
pub fn compute_sync_delta(
    receiver_manifest: Option<&FileSyncManifest>,
    sender_manifest: &FileSyncManifest,
    sender_chunks: &BTreeMap<[u8; 32], Vec<u8>>,
) -> io::Result<FileSyncDelta> {
    validate_manifest_structure(sender_manifest)?;
    if let Some(prev) = receiver_manifest {
        validate_manifest_structure(prev)?;
        if !filesync_rev_is_fresh(prev.revision, sender_manifest.revision) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "sender revision does not advance receiver revision",
            ));
        }
    }
    let have = match receiver_manifest {
        Some(prev) => prev.known_chunks(),
        None => BTreeSet::new(),
    };
    let mut missing = BTreeMap::new();
    for entry in sender_manifest.files.values() {
        for digest in &entry.chunks {
            if !have.contains(digest) && !missing.contains_key(digest) {
                let Some(blob) = sender_chunks.get(digest) else {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "sender_chunks missing chunk referenced by sender_manifest",
                    ));
                };
                missing.insert(*digest, blob.clone());
            }
        }
    }
    let mut deleted_paths = Vec::new();
    if let Some(prev) = receiver_manifest {
        for old_path in prev.files.keys() {
            if !sender_manifest.files.contains_key(old_path) {
                deleted_paths.push(old_path.clone());
            }
        }
    }
    Ok(FileSyncDelta {
        target: sender_manifest.clone(),
        chunks: missing,
        deleted_paths,
    })
}

fn put_u32_le(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn put_u64_le(out: &mut Vec<u8>, v: u64) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn take_u32_le(cur: &[u8]) -> Option<(u32, &[u8])> {
    let &[b0, b1, b2, b3, ref rest @ ..] = cur else {
        return None;
    };
    Some((u32::from_le_bytes([b0, b1, b2, b3]), rest))
}

fn take_u64_le(cur: &[u8]) -> Option<(u64, &[u8])> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, ref rest @ ..] = cur else {
        return None;
    };
    Some((u64::from_le_bytes([b0, b1, b2, b3, b4, b5, b6, b7]), rest))
}

/// Encode `delta` inside an `astream_wire::Frame` bounded by [`MAX_SYNC_DELTA_BYTES`].
pub fn encode_sync_delta(delta: &FileSyncDelta) -> io::Result<Vec<u8>> {
    validate_manifest_structure(&delta.target)?;
    validate_deleted_paths(&delta.deleted_paths, &delta.target.files)?;
    if delta.chunks.len() > MAX_SYNC_CHUNKS {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "delta chunks exceed MAX_SYNC_CHUNKS",
        ));
    }
    let mut body = Vec::new();
    body.extend_from_slice(&FILESYNC_MAGIC);
    body.push(FILESYNC_VERSION);
    body.extend_from_slice(&[0u8; 3]);
    put_u64_le(&mut body, delta.target.revision);

    put_u32_le(&mut body, delta.target.files.len() as u32);
    for entry in delta.target.files.values() {
        if let Err(m) = validate_sync_rel_path(&entry.rel_path) {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, m));
        }
        put_u32_le(&mut body, entry.rel_path.len() as u32);
        body.extend_from_slice(entry.rel_path.as_bytes());
        put_u64_le(&mut body, entry.size);
        put_u32_le(&mut body, entry.chunks.len() as u32);
        for d in &entry.chunks {
            body.extend_from_slice(d);
        }
    }

    put_u32_le(&mut body, delta.deleted_paths.len() as u32);
    for del in &delta.deleted_paths {
        if let Err(m) = validate_sync_rel_path(del) {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, m));
        }
        put_u32_le(&mut body, del.len() as u32);
        body.extend_from_slice(del.as_bytes());
    }

    put_u32_le(&mut body, delta.chunks.len() as u32);
    for (digest, blob) in &delta.chunks {
        if blob.len() > SYNC_CHUNK_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "chunk exceeds SYNC_CHUNK_BYTES",
            ));
        }
        body.extend_from_slice(digest);
        put_u32_le(&mut body, blob.len() as u32);
        body.extend_from_slice(blob);
    }

    if body.len() > MAX_SYNC_DELTA_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "FileSyncDelta exceeds MAX_SYNC_DELTA_BYTES",
        ));
    }
    match Frame::new(body).encode() {
        Ok(bytes) => Ok(bytes),
        Err(_) => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "Frame encode failed",
        )),
    }
}

fn decode_sync_file_entries(mut cur: &[u8]) -> io::Result<(BTreeMap<String, FileEntry>, &[u8])> {
    let Some((file_count, c1)) = take_u32_le(cur) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "short file_count",
        ));
    };
    cur = c1;
    if file_count as usize > MAX_SYNC_FILES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "file_count exceeds MAX_SYNC_FILES",
        ));
    }

    let mut files = BTreeMap::new();
    let mut total_chunks = 0usize;
    let mut f_idx = 0u32;
    while f_idx < file_count {
        let Some((p_len, c2)) = take_u32_le(cur) else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "short path len"));
        };
        let p_usize = p_len as usize;
        let (Some(p_bytes), Some(after_path)) = (c2.get(..p_usize), c2.get(p_usize..)) else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "short path"));
        };
        let Ok(rel_str) = core::str::from_utf8(p_bytes) else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "non-UTF8 path"));
        };
        if let Err(m) = validate_sync_rel_path(rel_str) {
            return Err(io::Error::new(io::ErrorKind::InvalidData, m));
        }
        if files.contains_key(rel_str) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "duplicate file path in FileSyncDelta",
            ));
        }
        let Some((size, c3)) = take_u64_le(after_path) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short file size",
            ));
        };
        let Some((c_cnt, mut c4)) = take_u32_le(c3) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short chunk count",
            ));
        };
        total_chunks = total_chunks.saturating_add(c_cnt as usize);
        if c_cnt as usize > MAX_SYNC_CHUNKS || total_chunks > MAX_SYNC_CHUNKS {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "chunk count exceeds MAX_SYNC_CHUNKS",
            ));
        }
        let mut digests = Vec::new();
        let mut d_idx = 0u32;
        while d_idx < c_cnt {
            let (Some(d_slice), Some(after_d)) = (c4.get(..32), c4.get(32..)) else {
                return Err(io::Error::new(io::ErrorKind::InvalidData, "short digest"));
            };
            let mut d = [0u8; 32];
            d.copy_from_slice(d_slice);
            digests.push(d);
            c4 = after_d;
            d_idx = d_idx.saturating_add(1);
        }
        files.insert(
            str_to_owned_string(rel_str),
            FileEntry {
                rel_path: str_to_owned_string(rel_str),
                size,
                chunks: digests,
            },
        );
        cur = c4;
        f_idx = f_idx.saturating_add(1);
    }
    Ok((files, cur))
}

fn decode_sync_deleted_paths(mut cur: &[u8]) -> io::Result<(Vec<String>, &[u8])> {
    let Some((del_count, c_del)) = take_u32_le(cur) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "short del_count",
        ));
    };
    cur = c_del;
    if del_count as usize > MAX_SYNC_FILES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "del_count exceeds MAX_SYNC_FILES",
        ));
    }
    let mut deleted_paths = Vec::new();
    let mut seen_deleted: BTreeSet<String> = BTreeSet::new();
    let mut del_idx = 0u32;
    while del_idx < del_count {
        let Some((d_len, next_c)) = take_u32_le(cur) else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "short del len"));
        };
        let d_usize = d_len as usize;
        let (Some(d_bytes), Some(after_del)) = (next_c.get(..d_usize), next_c.get(d_usize..))
        else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "short del path"));
        };
        let Ok(d_str) = core::str::from_utf8(d_bytes) else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "bad UTF8 del"));
        };
        if let Err(m) = validate_sync_rel_path(d_str) {
            return Err(io::Error::new(io::ErrorKind::InvalidData, m));
        }
        let owned = str_to_owned_string(d_str);
        if !seen_deleted.insert(owned.clone()) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "duplicate deleted path in FileSyncDelta",
            ));
        }
        deleted_paths.push(owned);
        cur = after_del;
        del_idx = del_idx.saturating_add(1);
    }
    Ok((deleted_paths, cur))
}

fn decode_sync_chunk_blobs(cur: &[u8]) -> io::Result<BTreeMap<[u8; 32], Vec<u8>>> {
    let Some((blob_count, mut c_blob)) = take_u32_le(cur) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "short blob_count",
        ));
    };
    if blob_count as usize > MAX_SYNC_CHUNKS {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "blob_count exceeds MAX_SYNC_CHUNKS",
        ));
    }
    let mut chunks = BTreeMap::new();
    let mut b_idx = 0u32;
    while b_idx < blob_count {
        let (Some(d_slice), Some(after_digest)) = (c_blob.get(..32), c_blob.get(32..)) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short blob digest",
            ));
        };
        let mut digest = [0u8; 32];
        digest.copy_from_slice(d_slice);
        if chunks.contains_key(&digest) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "duplicate chunk digest in FileSyncDelta",
            ));
        }
        let Some((b_len, after_len)) = take_u32_le(after_digest) else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "short blob len"));
        };
        let b_usize = b_len as usize;
        if b_usize > SYNC_CHUNK_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "chunk blob exceeds SYNC_CHUNK_BYTES",
            ));
        };
        let (Some(blob), Some(rest_blob)) = (after_len.get(..b_usize), after_len.get(b_usize..))
        else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "short blob data",
            ));
        };
        if sha256_bytes(blob) != digest {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "FileSyncDelta chunk SHA-256 verification failed",
            ));
        }
        chunks.insert(digest, slice_to_owned_vec(blob));
        c_blob = rest_blob;
        b_idx = b_idx.saturating_add(1);
    }
    if !c_blob.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "trailing bytes in FileSyncDelta",
        ));
    }
    Ok(chunks)
}

/// Decode and SHA-256-verify a framed [`FileSyncDelta`].
pub fn decode_sync_delta(framed: &[u8]) -> io::Result<FileSyncDelta> {
    let (raw, consumed) = match decode_frame_slice(framed) {
        Ok(Some(dec)) => dec,
        Ok(None) => return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "short Frame")),
        Err(_) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "invalid Frame in FileSyncDelta",
            ))
        }
    };
    if consumed != framed.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "trailing bytes after Frame in FileSyncDelta",
        ));
    }
    let (Some(magic_slice), Some(&ver), Some(hdr_rest)) = (raw.get(..4), raw.get(4), raw.get(8..))
    else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "bad FileSyncDelta magic",
        ));
    };
    if magic_slice != FILESYNC_MAGIC {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "bad FileSyncDelta magic",
        ));
    }
    if ver != FILESYNC_VERSION {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "unsupported FileSyncDelta version",
        ));
    }
    let Some((revision, cur)) = take_u64_le(hdr_rest) else {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "short revision"));
    };
    let (files, cur) = decode_sync_file_entries(cur)?;
    let (deleted_paths, cur) = decode_sync_deleted_paths(cur)?;
    let chunks = decode_sync_chunk_blobs(cur)?;
    let target = FileSyncManifest { revision, files };
    if let Err(e) = validate_manifest_structure(&target) {
        return Err(io::Error::new(io::ErrorKind::InvalidData, e));
    }
    if let Err(e) = validate_deleted_paths(&deleted_paths, &target.files) {
        return Err(io::Error::new(io::ErrorKind::InvalidData, e));
    }

    Ok(FileSyncDelta {
        target,
        chunks,
        deleted_paths,
    })
}

fn safe_join(root: &Path, rel: &str) -> io::Result<PathBuf> {
    if let Err(m) = validate_sync_rel_path(rel) {
        return Err(io::Error::new(io::ErrorKind::InvalidInput, m));
    }
    let mut p = root.to_path_buf();
    for seg in rel.split('/') {
        p.push(seg);
        if let Ok(meta) = fs::symlink_metadata(&p) {
            if meta.file_type().is_symlink() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "refusing symlink along destination sync path",
                ));
            }
        }
    }
    Ok(p)
}

/// Apply `delta` onto `dest_root` from `cur_revision`, reconstructing updated files from local
/// existing chunks + `delta.chunks`, writing via `.afsy.tmp` + `sync_all` + `rename`, and
/// returning the advanced monotone revision (`filesync_rev_advance`).
pub fn apply_sync_delta(
    dest_root: &Path,
    cur_revision: u64,
    delta: &FileSyncDelta,
) -> io::Result<u64> {
    if !filesync_rev_is_fresh(cur_revision, delta.target.revision) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "stale FileSyncDelta revision",
        ));
    }
    validate_manifest_structure(&delta.target)?;
    validate_deleted_paths(&delta.deleted_paths, &delta.target.files)?;
    if delta.chunks.len() > MAX_SYNC_CHUNKS {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "delta chunks exceed MAX_SYNC_CHUNKS",
        ));
    }
    let (_local_manifest, mut pool) = FileSyncManifest::scan_with_chunks(dest_root, cur_revision)?;
    for (digest, blob) in &delta.chunks {
        if blob.len() > SYNC_CHUNK_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "chunk blob exceeds SYNC_CHUNK_BYTES in apply_sync_delta",
            ));
        }
        if sha256_bytes(blob) != *digest {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "chunk digest mismatch in apply_sync_delta",
            ));
        }
        pool.insert(*digest, blob.clone());
    }

    let mut validated_deletes = Vec::new();
    for del in &delta.deleted_paths {
        validated_deletes.push(safe_join(dest_root, del)?);
    }

    // Verify every required chunk and destination path BEFORE mutating `dest_root`.
    let mut validated_targets = Vec::new();
    for entry in delta.target.files.values() {
        let dst = safe_join(dest_root, &entry.rel_path)?;
        let mut expected_bytes = 0u64;
        for digest in &entry.chunks {
            let Some(blob) = pool.get(digest) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "missing chunk for target file",
                ));
            };
            expected_bytes = expected_bytes.saturating_add(blob.len() as u64);
        }
        if expected_bytes != entry.size {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "size mismatch on target file",
            ));
        }
        validated_targets.push((dst, entry));
    }

    // Delete retired files first and prune newly empty parent dirs strictly inside `dest_root`
    // so file <-> directory replacements across revisions succeed cleanly.
    for dst in &validated_deletes {
        match fs::remove_file(dst) {
            Ok(()) => {}
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(e) => return Err(e),
        }
        let mut cur_parent = dst.parent();
        while let Some(p) = cur_parent {
            if p == dest_root {
                break;
            }
            if fs::remove_dir(p).is_err() {
                break;
            }
            cur_parent = p.parent();
        }
    }

    for (dst, entry) in validated_targets {
        if let Some(parent) = dst.parent() {
            fs::create_dir_all(parent)?;
        }
        let mut tmp = dst.clone();
        tmp.as_mut_os_string().push(".afsy.tmp");
        let mut out = File::create(&tmp)?;
        for digest in &entry.chunks {
            if let Some(blob) = pool.get(digest) {
                out.write_all(blob)?;
            }
        }
        out.sync_all()?;
        drop(out);
        fs::rename(&tmp, &dst)?;
    }

    Ok(filesync_rev_advance(cur_revision, delta.target.revision))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn filesync_deduplicates_unchanged_chunks_and_rejects_traversal_and_stale_revisions() {
        assert!(validate_sync_rel_path("../etc/passwd").is_err());
        assert!(validate_sync_rel_path("/abs/path").is_err());
        assert!(validate_sync_rel_path("a//b").is_err());
        assert!(validate_sync_rel_path("src/main.rs").is_ok());

        let base_tmp =
            std::env::temp_dir().join(format!("astream-filesync-test-{}", std::process::id()));
        let _ = fs::remove_dir_all(&base_tmp);
        let src_dir = base_tmp.join("src");
        let dst_dir = base_tmp.join("dst");
        fs::create_dir_all(src_dir.join("sub")).expect("mkdir src");
        fs::create_dir_all(&dst_dir).expect("mkdir dst");

        let shared_block = vec![b'A'; SYNC_CHUNK_BYTES];
        fs::write(src_dir.join("shared.bin"), &shared_block).expect("write shared");
        fs::write(src_dir.join("old.txt"), b"remove-me").expect("write old");

        let (m1, c1) = FileSyncManifest::scan_with_chunks(&src_dir, 1).expect("scan 1");
        let d1 = compute_sync_delta(None, &m1, &c1).expect("delta 1");
        let wire1 = encode_sync_delta(&d1).expect("encode 1");
        let dec1 = decode_sync_delta(&wire1).expect("decode 1");
        let rev1 = apply_sync_delta(&dst_dir, 0, &dec1).expect("apply 1");
        assert_eq!(rev1, 1);

        // Stale revision replay is rejected!
        assert!(apply_sync_delta(&dst_dir, 1, &dec1).is_err());

        // Revision 2: keep `shared.bin`'s 64 KiB first chunk + append 5 bytes, delete `old.txt`,
        // add `sub/new.txt`. Only the new 5-byte tail chunk + `sub/new.txt` chunk cross the wire!
        let mut grown = shared_block.clone();
        grown.extend_from_slice(b"TAIL!");
        fs::write(src_dir.join("shared.bin"), &grown).expect("write grown");
        fs::remove_file(src_dir.join("old.txt")).expect("rm old");
        fs::write(src_dir.join("sub/new.txt"), b"hello fleet").expect("write new");

        let recv_m1 = FileSyncManifest::scan(&dst_dir, 1).expect("scan dst");
        let (m2, c2) = FileSyncManifest::scan_with_chunks(&src_dir, 2).expect("scan 2");
        let d2 = compute_sync_delta(Some(&recv_m1), &m2, &c2).expect("delta 2");
        // The 64 KiB `shared_block` chunk is NOT re-transmitted!
        assert_eq!(d2.chunks.len(), 2);
        assert_eq!(d2.deleted_paths, vec!["old.txt".to_string()]);

        let wire2 = encode_sync_delta(&d2).expect("encode 2");
        assert!(
            wire2.len() < 1024,
            "64 KiB shared chunk must be deduplicated"
        );
        let dec2 = decode_sync_delta(&wire2).expect("decode 2");
        let rev2 = apply_sync_delta(&dst_dir, rev1, &dec2).expect("apply 2");
        assert_eq!(rev2, 2);

        let final_dst = FileSyncManifest::scan(&dst_dir, 2).expect("scan final");
        assert_eq!(final_dst, m2);
        assert!(!dst_dir.join("old.txt").exists());

        // Revision 3: replace directory `sub/new.txt` with regular file `sub`!
        fs::remove_dir_all(src_dir.join("sub")).expect("rm sub dir");
        fs::write(src_dir.join("sub"), b"now-a-file").expect("write sub file");
        let (m3, c3) = FileSyncManifest::scan_with_chunks(&src_dir, 3).expect("scan 3");
        let d3 = compute_sync_delta(Some(&final_dst), &m3, &c3).expect("delta 3");
        let wire3 = encode_sync_delta(&d3).expect("encode 3");
        let dec3 = decode_sync_delta(&wire3).expect("decode 3");
        let rev3 = apply_sync_delta(&dst_dir, rev2, &dec3).expect("apply 3");
        assert_eq!(rev3, 3);
        assert_eq!(FileSyncManifest::scan(&dst_dir, 3).expect("scan 3 dst"), m3);

        // File/directory prefix collision in a manifest is rejected!
        let mut bad_files = BTreeMap::new();
        bad_files.insert(
            "a".to_string(),
            FileEntry {
                rel_path: "a".to_string(),
                size: 0,
                chunks: Vec::new(),
            },
        );
        bad_files.insert(
            "a/b.txt".to_string(),
            FileEntry {
                rel_path: "a/b.txt".to_string(),
                size: 0,
                chunks: Vec::new(),
            },
        );
        let bad_delta = FileSyncDelta {
            target: FileSyncManifest {
                revision: 4,
                files: bad_files,
            },
            chunks: BTreeMap::new(),
            deleted_paths: Vec::new(),
        };
        assert!(encode_sync_delta(&bad_delta).is_err());

        let _ = fs::remove_dir_all(&base_tmp);
    }
}
