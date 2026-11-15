// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! THE POWER-LOSS MODEL of a compaction's files, for its crash tests (`compact_tests.rs`).
//!
//! A compaction writes every file through the store's file helpers: `create_fresh` and
//! `create_like`, `rename_path`, `remove_file_path`, `flush_file` and `sync_parent_dir`. Under
//! `cfg(test)` each of them reports here once a test has ARMED this thread on the log's
//! directory, and the model keeps what a power loss at that moment would leave:
//!
//! - a file's CONTENT survives as of its last full flush (`flush_file`). A file created and
//!   never flushed survives EMPTY, however much was written to it.
//! - the directory's NAMES (which name holds which file) change in the order the calls made
//!   them. They survive up to the last directory flush (`sync_parent_dir`), and after that any
//!   PREFIX of the changes made since: metadata reaches the media in order (a journaled
//!   filesystem's contract), so no change survives without every change before it.
//!
//! [`Recorder::images`] is every directory a power loss at that moment can leave, one per
//! surviving prefix of the name changes, each with only flushed content. [`apply`] makes the
//! directory one of them. Files are told apart by inode number, and a file created afresh
//! starts with no flushed content, even when its number was used before.
//!
//! What it does not model: a flush that reaches the media only in part (a file is either
//! flushed or not), and the log's own appends (a compaction never writes the log; its records
//! were flushed by the commits that wrote them, so the armed directory is taken as durable).

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::ffi::OsString;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

/// A directory's regular files, by name: what a power loss leaves, or what a process left.
pub(crate) type Image = BTreeMap<OsString, Vec<u8>>;

/// What one armed thread recorded of one directory.
pub(crate) struct Recorder {
    dir: PathBuf,
    /// Each file's content as of its last full flush, by inode. A file with no entry was
    /// never flushed: a power loss leaves it empty.
    durable: HashMap<u64, Vec<u8>>,
    /// The directory's names after each change, oldest first; `names[0]` is the directory
    /// at the arm.
    names: Vec<BTreeMap<OsString, u64>>,
    /// The newest of `names` a directory flush made durable.
    synced: usize,
}

thread_local! {
    static ARMED: RefCell<Option<Recorder>> = const { RefCell::new(None) };
}

/// The regular files in `dir`, by name, and their inode numbers.
fn names_in(dir: &Path) -> BTreeMap<OsString, u64> {
    let mut out = BTreeMap::new();
    let Ok(entries) = std::fs::read_dir(dir) else {
        return out;
    };
    for entry in entries.flatten() {
        if let Ok(meta) = std::fs::symlink_metadata(entry.path()) {
            if meta.is_file() {
                out.insert(entry.file_name(), meta.ino());
            }
        }
    }
    out
}

/// Arm this thread on `dir`: everything in it now is taken as durable as it stands.
pub(crate) fn arm(dir: &Path) {
    let names = names_in(dir);
    let mut durable = HashMap::new();
    for (name, ino) in &names {
        if let Ok(bytes) = std::fs::read(dir.join(name)) {
            durable.insert(*ino, bytes);
        }
    }
    ARMED.with(|a| {
        *a.borrow_mut() = Some(Recorder {
            dir: dir.to_path_buf(),
            durable,
            names: vec![names],
            synced: 0,
        });
    });
}

/// Disarm this thread, handing back what it recorded.
pub(crate) fn disarm() -> Option<Recorder> {
    ARMED.with(|a| a.borrow_mut().take())
}

/// Run `f` on the armed recorder when `path` is in its directory.
fn in_armed_dir(path: &Path, f: impl FnOnce(&mut Recorder)) {
    ARMED.with(|a| {
        if let Some(r) = a.borrow_mut().as_mut() {
            if path.parent() == Some(r.dir.as_path()) {
                f(r);
            }
        }
    });
}

/// A name in the directory changed: a file was renamed onto it, or it was removed.
pub(crate) fn entry_changed(path: &Path) {
    in_armed_dir(path, |r| {
        let names = names_in(&r.dir);
        r.names.push(names);
    });
}

/// `path` was just created afresh: its file holds nothing flushed yet.
pub(crate) fn created(path: &Path) {
    in_armed_dir(path, |r| {
        if let Ok(meta) = std::fs::symlink_metadata(path) {
            r.durable.remove(&meta.ino());
        }
        let names = names_in(&r.dir);
        r.names.push(names);
    });
}

/// The file at `path` was flushed in full: its content as it stands now survives.
pub(crate) fn flushed(path: &Path) {
    in_armed_dir(path, |r| {
        if let (Ok(meta), Ok(bytes)) = (std::fs::symlink_metadata(path), std::fs::read(path)) {
            r.durable.insert(meta.ino(), bytes);
        }
    });
}

/// The directory holding `path` was flushed: every name change so far survives.
pub(crate) fn dir_synced(path: &Path) {
    in_armed_dir(path, |r| {
        r.synced = r.names.len().saturating_sub(1);
    });
}

impl Recorder {
    /// Every directory a power loss now can leave: one per surviving prefix of the name
    /// changes since the last directory flush, each file holding only what was flushed.
    pub(crate) fn images(&self) -> Vec<Image> {
        let mut out: Vec<Image> = Vec::new();
        for names in self.names.iter().skip(self.synced) {
            let image: Image = names
                .iter()
                .map(|(name, ino)| {
                    let bytes = match self.durable.get(ino) {
                        Some(b) => b.clone(),
                        None => Vec::new(),
                    };
                    (name.clone(), bytes)
                })
                .collect();
            if out.last() != Some(&image) {
                out.push(image);
            }
        }
        out
    }
}

/// The directory as it stands: what a process that stopped dead left, the kernel's cache
/// and all.
pub(crate) fn capture(dir: &Path) -> Image {
    let mut out = Image::new();
    for name in names_in(dir).into_keys() {
        if let Ok(bytes) = std::fs::read(dir.join(&name)) {
            out.insert(name, bytes);
        }
    }
    out
}

/// Make `dir` hold exactly `image`: every other regular file removed, every one of its
/// files written with its content.
pub(crate) fn apply(dir: &Path, image: &Image) {
    for name in names_in(dir).into_keys() {
        if !image.contains_key(&name) {
            std::fs::remove_file(dir.join(&name)).unwrap();
        }
    }
    for (name, bytes) in image {
        std::fs::write(dir.join(name), bytes).unwrap();
    }
}
