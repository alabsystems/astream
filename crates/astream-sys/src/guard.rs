// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! THE GUARD LOCK: the lock a file's one writer holds to keep a second one out, which
//! leaves every byte of the file readable beside it.
//!
//! On Unix it is `flock(2)` on the whole file, through `std` ([`File::try_lock`],
//! [`File::try_lock_shared`], [`File::unlock`]), and advisory: it refuses a second lock
//! and no read or write. On Windows a lock is a byte range's and MANDATORY: while one
//! handle holds a range, a read or write through any other handle that touches a byte of
//! it is refused (`ERROR_LOCK_VIOLATION`), this process's own other handles included. A
//! whole-file lock there (what [`File::try_lock`] takes: every byte from 0) refuses every
//! reader of the file for as long as the writer lives. So on Windows the guard is the one
//! byte at [`GUARD_BYTE`], which no file reaches (`LockFileEx` locks a range past the end
//! of a file without growing it): two guards still collide there exactly as two flocks
//! do, and a read or write of the file's bytes through another handle never touches it.
//!
//! A whole-file lock taken by anything else (an older build's, [`File::try_lock`])
//! covers the guard byte too, so it and a guard still keep each other out.
//!
//! A guard taken here is let go through [`unlock`]: on Windows an unlock names the
//! range it locked, and [`File::unlock`] names the whole file, which no guard locked.

use std::fs::{File, TryLockError};
use std::io;

/// The byte the guard locks on Windows: 2^62, past the longest file any Windows file
/// system holds (NTFS 2^48 bytes less a cluster, ReFS about 2^55) and inside the signed
/// 64-bit offsets a file server may map a lock to.
pub const GUARD_BYTE: u64 = 1 << 62;

/// Take the guard exclusively without waiting: `Err(TryLockError::WouldBlock)` while
/// another handle (in this process or any other) holds it, either way.
///
/// # Errors
/// [`TryLockError::WouldBlock`] when another handle holds the guard; any other refusal
/// as [`TryLockError::Error`], `Unsupported` where the file system takes no lock.
pub fn try_lock(file: &File) -> Result<(), TryLockError> {
    #[cfg(windows)]
    {
        guard_win::try_lock(file, true)
    }
    #[cfg(not(windows))]
    {
        file.try_lock()
    }
}

/// Take the guard shared without waiting: `Err(TryLockError::WouldBlock)` while another
/// handle holds it exclusively. A probe of whether a writer holds the file.
///
/// # Errors
/// As [`try_lock`].
pub fn try_lock_shared(file: &File) -> Result<(), TryLockError> {
    #[cfg(windows)]
    {
        guard_win::try_lock(file, false)
    }
    #[cfg(not(windows))]
    {
        file.try_lock_shared()
    }
}

/// Let the guard go. On Unix `flock(LOCK_UN)`, which releases it on the open file
/// description at once, however many references a `fork` in another thread holds; on
/// Windows the guard byte is unlocked twice, as [`File::unlock`] unlocks its range,
/// because a handle may hold it both exclusively and shared.
///
/// # Errors
/// The OS's refusal; on Windows `ERROR_NOT_LOCKED` where this handle holds no guard.
pub fn unlock(file: &File) -> io::Result<()> {
    #[cfg(windows)]
    {
        guard_win::unlock(file)
    }
    #[cfg(not(windows))]
    {
        file.unlock()
    }
}

#[cfg(windows)]
#[allow(unsafe_code)]
#[path = "guard_win.rs"]
mod guard_win;

#[cfg(test)]
#[path = "guard_tests.rs"]
mod tests;
