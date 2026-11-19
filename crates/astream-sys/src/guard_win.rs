// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The guard byte's lock on Windows: `LockFileEx` and `UnlockFileEx` on the one byte at
//! [`GUARD_BYTE`](super::GUARD_BYTE), through the file's own handle.

use std::fs::{File, TryLockError};
use std::io;
use std::os::windows::io::AsRawHandle;

use super::GUARD_BYTE;

/// `OVERLAPPED`: two `ULONG_PTR`s, the offset's low and high `DWORD`s (a union with a
/// pointer, which two `u32`s lay out the same at every width), and an event handle.
#[repr(C)]
struct Overlapped {
    internal: usize,
    internal_high: usize,
    offset: u32,
    offset_high: u32,
    event: *mut core::ffi::c_void,
}

impl Overlapped {
    /// No event, the offset the guard byte's.
    fn at_guard() -> Overlapped {
        Overlapped {
            internal: 0,
            internal_high: 0,
            offset: GUARD_BYTE as u32,
            offset_high: (GUARD_BYTE >> 32) as u32,
            event: core::ptr::null_mut(),
        }
    }
}

#[link(name = "kernel32")]
unsafe extern "system" {
    fn LockFileEx(
        file: *mut core::ffi::c_void,
        flags: u32,
        reserved: u32,
        bytes_low: u32,
        bytes_high: u32,
        overlapped: *mut Overlapped,
    ) -> i32;
    fn UnlockFileEx(
        file: *mut core::ffi::c_void,
        reserved: u32,
        bytes_low: u32,
        bytes_high: u32,
        overlapped: *mut Overlapped,
    ) -> i32;
    fn GetOverlappedResult(
        file: *mut core::ffi::c_void,
        overlapped: *mut Overlapped,
        transferred: *mut u32,
        wait: i32,
    ) -> i32;
}

const LOCKFILE_FAIL_IMMEDIATELY: u32 = 0x1;
const LOCKFILE_EXCLUSIVE_LOCK: u32 = 0x2;
const ERROR_LOCK_VIOLATION: i32 = 33;
const ERROR_NOT_LOCKED: i32 = 158;
const ERROR_IO_PENDING: i32 = 997;

/// Lock the guard byte without waiting, exclusively or shared. A refusal because another
/// handle holds it is `WouldBlock`, as [`File::try_lock`] reads it (`ERROR_LOCK_VIOLATION`).
pub(super) fn try_lock(file: &File, exclusive: bool) -> Result<(), TryLockError> {
    let flags = LOCKFILE_FAIL_IMMEDIATELY
        | if exclusive {
            LOCKFILE_EXCLUSIVE_LOCK
        } else {
            0
        };
    let mut overlapped = Overlapped::at_guard();
    // SAFETY: `file` keeps its handle open for the call; `overlapped` is a valid OVERLAPPED,
    // writable for the call, naming the guard byte and no event, and it outlives the
    // operation: `settled` waits out one a handle opened for overlapped I/O left pending.
    let locked = unsafe { LockFileEx(file.as_raw_handle(), flags, 0, 1, 0, &raw mut overlapped) };
    match settled(file, locked, &mut overlapped) {
        Ok(()) => Ok(()),
        Err(error) if error.raw_os_error() == Some(ERROR_LOCK_VIOLATION) => {
            Err(TryLockError::WouldBlock)
        }
        Err(error) => Err(TryLockError::Error(error)),
    }
}

/// Unlock the guard byte, twice: a handle that holds it both exclusively and shared needs
/// two unlocks, the first of which lets the exclusive lock go. The second finding nothing
/// locked is no error.
pub(super) fn unlock(file: &File) -> io::Result<()> {
    unlock_once(file)?;
    match unlock_once(file) {
        Err(error) if error.raw_os_error() == Some(ERROR_NOT_LOCKED) => Ok(()),
        other => other,
    }
}

fn unlock_once(file: &File) -> io::Result<()> {
    let mut overlapped = Overlapped::at_guard();
    // SAFETY: `file` keeps its handle open for the call; `overlapped` is a valid OVERLAPPED,
    // writable for the call, naming the guard byte and no event, and it outlives the
    // operation (`settled`).
    let unlocked = unsafe { UnlockFileEx(file.as_raw_handle(), 0, 1, 0, &raw mut overlapped) };
    settled(file, unlocked, &mut overlapped)
}

/// The outcome of a call on the guard byte that answered `answer`: its own where it
/// finished; where it was left pending (`ERROR_IO_PENDING`, on a handle opened for
/// overlapped I/O, which nothing here opens), the operation's, waited for, so the OS never
/// writes `overlapped` after it is gone. A lock that fails immediately and an unlock never
/// wait on another holder, so that wait is the call's own.
fn settled(file: &File, answer: i32, overlapped: &mut Overlapped) -> io::Result<()> {
    if answer != 0 {
        return Ok(());
    }
    let error = io::Error::last_os_error();
    if error.raw_os_error() != Some(ERROR_IO_PENDING) {
        return Err(error);
    }
    let mut transferred = 0u32;
    // SAFETY: `file` keeps its handle open, `overlapped` is the structure the pending
    // operation was started with and stays valid until this returns, `transferred` is
    // writable, and the call waits (TRUE) until the operation is done.
    let done =
        unsafe { GetOverlappedResult(file.as_raw_handle(), overlapped, &raw mut transferred, 1) };
    if done == 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}
