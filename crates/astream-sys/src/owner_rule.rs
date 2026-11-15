// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The owner-only rule's clauses, written once for every entry that judges an object:
//! [`crate::owner_private`] and [`crate::owner_private_dir`] over one `fstat` of a held
//! descriptor, [`crate::owner_private_dir_by_path`] over one `lstatx_np` of a path, and
//! [`crate::kind_and_owner_of`] over metadata a caller read itself. Safe code: it reads
//! numbers, never the OS.
//!
//! The clauses come in two steps, in order. [`kind_and_owner`] judges the kind asked
//! for and then the owner, and only it makes an [`Owned`]; [`Owned::list_and_mode`]
//! judges the access list and then the mode, and only an [`Owned`] has it. `Owned`'s
//! field is private to this module, so nothing outside it can make one, and no caller
//! can judge the list or the mode of an object whose kind and owner were not judged
//! first. A clause added to either step reaches every entry.

use crate::NotPrivate;

/// `<sys/stat.h>`'s file types: the same numbers on Darwin (SDK
/// `sys/_types/_s_ifmt.h:35-42`), Linux and the BSDs (the libc crate's `S_IF*`, which
/// std's `FileType` tests `st_mode & S_IFMT` against).
pub(crate) const S_IFMT: u32 = 0o170_000;
pub(crate) const S_IFIFO: u32 = 0o010_000;
pub(crate) const S_IFCHR: u32 = 0o020_000;
pub(crate) const S_IFDIR: u32 = 0o040_000;
pub(crate) const S_IFBLK: u32 = 0o060_000;
pub(crate) const S_IFREG: u32 = 0o100_000;
pub(crate) const S_IFLNK: u32 = 0o120_000;
pub(crate) const S_IFSOCK: u32 = 0o140_000;

/// What the owner-only rule reads of one state of one object: its `st_mode` (file type
/// and permission bits) and its owner's uid, from one `fstat` of a descriptor, one
/// `lstatx_np` of a path, or a caller's own metadata. A clause that needs another input
/// adds a field here, which breaks every constructor at compile time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Seen {
    pub(crate) st_mode: u32,
    pub(crate) uid: u32,
}

/// An object whose kind and owner held. Only [`kind_and_owner`] makes one (its field is
/// private to this module), so [`Owned::list_and_mode`] is never judged first.
#[must_use]
#[derive(Debug)]
pub(crate) struct Owned {
    mode: u32,
}

/// The clauses before the access list, in order: the kind asked for (a directory when
/// `dir`, else a regular file), then owned by `euid`. The first one broken is the
/// answer.
pub(crate) fn kind_and_owner(seen: Seen, dir: bool, euid: u32) -> Result<Owned, NotPrivate> {
    let kind = seen.st_mode & S_IFMT;
    let wanted = if dir { S_IFDIR } else { S_IFREG };
    if kind != wanted {
        return Err(NotPrivate::Kind(kind_word(kind)));
    }
    if seen.uid != euid {
        return Err(NotPrivate::Owner(seen.uid));
    }
    Ok(Owned {
        mode: seen.st_mode & 0o777,
    })
}

impl Owned {
    /// The clauses from the access list on, in order: no entry that allows anyone
    /// anything (`allows`, which a caller reads only once it holds an `Owned`; a missing
    /// list holds none), then no group or other permission bit.
    pub(crate) fn list_and_mode(self, allows: bool) -> Result<(), NotPrivate> {
        if allows {
            return Err(NotPrivate::Acl);
        }
        if self.mode & 0o077 != 0 {
            return Err(NotPrivate::Mode(self.mode));
        }
        Ok(())
    }
}

/// The word [`NotPrivate::Kind`] names a file type (`st_mode & S_IFMT`) by.
pub(crate) fn kind_word(kind: u32) -> &'static str {
    match kind {
        S_IFIFO => "a FIFO",
        S_IFSOCK => "a socket",
        S_IFCHR | S_IFBLK => "a device",
        S_IFDIR => "a directory",
        S_IFREG => "a regular file",
        S_IFLNK => "a symlink",
        _ => "not a regular file",
    }
}
