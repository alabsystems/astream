// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The cordoned Unix module: hand-declared FFI for the owner-only file rule (no libc
//! dependency). `geteuid` on every Unix; on Apple `fstatx_np`, the four filesec calls and
//! three `<sys/acl.h>` calls that read a descriptor's extended access list; and on macOS
//! arm64 `lstatx_np` with the same filesec calls, which read
//! a path's owner, mode and whether it carries an access list without opening it
//! (`lstatx_np`, `filesec_init`, `filesec_get_property`, `filesec_query_property`,
//! `filesec_free`, behind [`crate::owner_private_dir_by_path`]). The `open` flags the
//! rule opens with are plain per-OS numbers, kept here beside the calls they serve. Off
//! Apple it also holds the cordon's plain flush, `fsync` behind [`crate::plain_fsync`]
//! (Apple's is the `apple` module's). Raw pointers stay inside this module, and each
//! errno it reads is read straight after the failing call: every function returns an
//! owned value, `io::Result`, or plain integers (`Looked`, whose `errno` is that number).

use std::ffi::c_int;
#[cfg(target_vendor = "apple")]
use std::ffi::c_void;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
use std::ffi::{c_char, CStr};
use std::fs::File;
use std::io;

unsafe extern "C" {
    fn geteuid() -> u32;
}

#[cfg(not(target_vendor = "apple"))]
unsafe extern "C" {
    fn fsync(fd: c_int) -> c_int;
}

/// `fsync(fd)`, retried while it is interrupted (`EINTR`, [`crate::retried_on_eintr`]):
/// the open file's writes, or a directory's entries, handed to the drive.
/// [`crate::plain_fsync`] off Apple, the call `File::sync_all` makes there, on any
/// descriptor rather than only a `File`'s.
#[cfg(not(target_vendor = "apple"))]
pub(crate) fn plain_fsync(fd: std::os::fd::BorrowedFd<'_>) -> io::Result<()> {
    use std::os::fd::AsRawFd as _;
    let fd = fd.as_raw_fd();
    crate::retried_on_eintr!({
        // SAFETY: `fd` is a valid open descriptor, retained by a BorrowedFd for the call;
        // `fsync` takes it by value and touches no memory.
        if unsafe { fsync(fd) } == -1 {
            Err(io::Error::last_os_error())
        } else {
            Ok(())
        }
    })
}

#[cfg(target_vendor = "apple")]
unsafe extern "C" {
    fn acl_get_entry(acl: *mut c_void, entry_id: c_int, entry: *mut *mut c_void) -> c_int;
    fn acl_get_tag_type(entry: *mut c_void, tag: *mut c_int) -> c_int;
    fn acl_free(object: *mut c_void) -> c_int;
    // SDK sys/stat.h:422. The plain symbol on every Apple target: x86_64's is the
    // 32-bit-inode call beside `_fstatx_np$INODE64`, whose smaller `struct stat` the
    // buffer holds too, and nothing here reads the stat.
    fn fstatx_np(fd: c_int, sb: *mut c_void, fsec: *mut c_void) -> c_int;
    // SDK sys/fcntl.h:636, 638, 639 and 640.
    fn filesec_init() -> *mut c_void;
    fn filesec_free(fsec: *mut c_void);
    fn filesec_get_property(fsec: *mut c_void, property: c_int, propptr: *mut c_void) -> c_int;
    fn filesec_query_property(fsec: *mut c_void, property: c_int, validptr: *mut c_int) -> c_int;
}
/// `ACL_FIRST_ENTRY` and `ACL_NEXT_ENTRY`, `acl_get_entry`'s cursor.
#[cfg(target_vendor = "apple")]
const ACL_FIRST_ENTRY: c_int = 0;
#[cfg(target_vendor = "apple")]
const ACL_NEXT_ENTRY: c_int = -1;
/// `acl_tag_t`'s `ACL_EXTENDED_ALLOW`: an entry that grants (the other is a deny).
#[cfg(target_vendor = "apple")]
const ACL_EXTENDED_ALLOW: c_int = 1;
/// `ENOENT`, which `lstatx_np` answers for a path whose lookup found nothing.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) const ENOENT: i32 = 2;

/// `(O_NONBLOCK, O_NOFOLLOW)` for this target, or `None` where this crate declares
/// none. Darwin and the BSDs share `<sys/fcntl.h>`'s numbers; Linux's differ by
/// architecture (`asm-generic/fcntl.h`, and `arch/{arm,arm64,powerpc}`'s overrides of
/// `O_NOFOLLOW`).
pub(crate) const OPEN_FLAGS: Option<(c_int, c_int)> = open_flags();

const fn open_flags() -> Option<(c_int, c_int)> {
    if cfg!(any(
        target_vendor = "apple",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd",
        target_os = "dragonfly"
    )) {
        Some((0x0004, 0x0100))
    } else if cfg!(all(
        any(target_os = "linux", target_os = "android"),
        any(
            target_arch = "x86",
            target_arch = "x86_64",
            target_arch = "riscv32",
            target_arch = "riscv64",
            target_arch = "s390x",
            target_arch = "loongarch64"
        )
    )) {
        Some((0o4000, 0o400000))
    } else if cfg!(all(
        any(target_os = "linux", target_os = "android"),
        any(
            target_arch = "arm",
            target_arch = "aarch64",
            target_arch = "powerpc",
            target_arch = "powerpc64"
        )
    )) {
        Some((0o4000, 0o100000))
    } else {
        None
    }
}

/// This process's effective user id.
pub(crate) fn euid() -> u32 {
    // SAFETY: `geteuid` takes nothing, cannot fail, and touches no memory of ours.
    unsafe { geteuid() }
}

/// Whether `file`'s extended access list holds an entry that ALLOWS anyone anything.
/// A file with no list holds none; a deny entry is not counted.
///
/// One `fstatx_np` of the descriptor into a filesec of this function's, decided by return
/// codes and the filesec's validity bits alone ([`ListRead::allows`]), never by errno.
/// `acl_get_fd_np`, which this replaced, answers a file with no list NULL with errno
/// ENOENT, set by `filesec_get_property` before the `free()` in `filesec_free` (Libc
/// posix1e/acl_file.c:71-90, gen/filesec.c:94-99, 183-186). libmalloc's `free` keeps no
/// errno, and one that hands a chunk back with `madvise(MADV_FREE_REUSABLE)` leaves the
/// madvise's: EINVAL where XNU will not reuse the map entry (bsd/kern/kern_mman.c:1492-1495;
/// osfmk/vm/vm_map.c:16962-17004, 17165-17170: an entry in transition, wired, or copied
/// on write since a read of this process's memory). So a loaded process could read
/// "Invalid argument" for a plain private file with no list (aterm's ATERM-KI-1111-30).
#[cfg(target_vendor = "apple")]
pub(crate) fn acl_allows(file: &File) -> io::Result<bool> {
    use std::os::fd::AsRawFd as _;
    // SAFETY: `filesec_init` takes nothing; the filesec it returns (Libc gen/filesec.c:61-70)
    // is owned here and freed once below.
    let fsec = unsafe { filesec_init() };
    let read = if fsec.is_null() {
        ListRead::NoFilesec
    } else {
        // SAFETY: `fsec` is filesec_init's, non-null, and freed only below; the descriptor is
        // `file`'s, open for the whole call.
        let read = unsafe { read_list(file.as_raw_fd(), fsec) };
        // SAFETY: `fsec` is filesec_init's and freed exactly once, here, on the one path out
        // after it was made; `read_list` keeps no pointer into it.
        unsafe { filesec_free(fsec) };
        read
    };
    #[cfg(test)]
    errno_seam::after_free();
    read.allows()
}

/// What [`acl_allows`] read of a descriptor's access list, as plain values: no pointer, and
/// no errno but the one `filesec_get_property` set itself as it failed, read straight after.
#[cfg(target_vendor = "apple")]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ListRead {
    /// `filesec_init` could not allocate.
    NoFilesec,
    /// `fstatx_np` returned this instead of 0: -1 (the syscall failed; statx1 frees its
    /// buffer after it, so errno may be `free`'s, and is not read), or the ENOMEM statx1
    /// returns itself (Libc sys/statx_np.c:159-162).
    Failed(c_int),
    /// `fstatx_np` returned 0 with no mode in the filesec: statx1's realloc for a list
    /// longer than its first buffer failed, and it returns 0 having set nothing
    /// (statx_np.c:178-187), so no list bit says there is none.
    Unset,
    /// The stat was read and the filesec holds no access list.
    Unlisted,
    /// The filesec holds a list, which `filesec_get_property` could not copy out: its
    /// errno (`acl_copy_int_native`'s).
    Uncopied(Option<i32>),
    /// The filesec holds a list; whether one of its entries allows.
    Listed(bool),
}

#[cfg(target_vendor = "apple")]
impl ListRead {
    /// The verdict: `Ok(false)` with no list, the allow walk's answer with one, and `Err`
    /// for every read that left the list unjudged.
    pub(crate) fn allows(self) -> io::Result<bool> {
        let unjudged = |why: String| {
            Err(io::Error::other(format!(
                "the access list could not be read: {why}"
            )))
        };
        match self {
            ListRead::Unlisted => Ok(false),
            ListRead::Listed(allows) => Ok(allows),
            ListRead::NoFilesec => Err(io::Error::from(io::ErrorKind::OutOfMemory)),
            ListRead::Failed(rc) => unjudged(format!("fstatx_np returned {rc}")),
            ListRead::Unset => unjudged("fstatx_np set no mode".to_string()),
            ListRead::Uncopied(Some(errno)) => Err(io::Error::from_raw_os_error(errno)),
            ListRead::Uncopied(None) => unjudged("the list could not be copied".to_string()),
        }
    }
}

/// The words of the `struct stat` buffer `fstatx_np` fills in [`read_list`].
#[cfg(target_vendor = "apple")]
const LIST_STAT_WORDS: usize = 32;

#[cfg(target_vendor = "apple")]
const _: () = assert!(
    LIST_STAT_WORDS * 8 > 144,
    "the buffer holds the 144 bytes of a 64-bit-inode stat"
);

/// [`acl_allows`]'s `fstatx_np` and its reads of the filesec, which `acl_allows` makes and
/// frees.
///
/// # Safety
/// `fsec` is a live filesec from `filesec_init`, not yet freed, and is not freed during
/// the call; `fd` is open for the call.
#[cfg(target_vendor = "apple")]
unsafe fn read_list(fd: c_int, fsec: *mut c_void) -> ListRead {
    let mut sb = [0u64; LIST_STAT_WORDS];
    // SAFETY: `sb` is 256 writable, 8-aligned bytes, more than any `struct stat` the call
    // writes, and nothing here reads it; `fsec` is a live filesec, so the call goes to
    // statx1 (Libc sys/statx_np.c:141-219), which keeps its list buffer in `fsec` or frees it.
    let rc = unsafe { fstatx_np(fd, sb.as_mut_ptr().cast::<c_void>(), fsec) };
    if rc != 0 {
        return ListRead::Failed(rc);
    }
    let mut mode_set: c_int = 0;
    // SAFETY: `fsec` is live; the query writes one int and allocates nothing
    // (filesec.c:303-341).
    let mode_query = unsafe { filesec_query_property(fsec, FILESEC_MODE, &raw mut mode_set) };
    if mode_query != 0 || mode_set == 0 {
        return ListRead::Unset;
    }
    let mut listed: c_int = 0;
    // SAFETY: as above; `listed` is the bitmask `fs_valid & FS_VALID_ACL`, so "listed" is
    // `!= 0` (filesec.c:325-328, 339).
    let list_query = unsafe { filesec_query_property(fsec, FILESEC_ACL, &raw mut listed) };
    if list_query != 0 {
        return ListRead::Unset;
    }
    if listed == 0 {
        return ListRead::Unlisted;
    }
    let mut acl: *mut c_void = std::ptr::null_mut();
    // SAFETY: `fsec` is live and holds a list; FILESEC_ACL writes one `acl_t` through the
    // pointer, a copy (`acl_copy_int_native`) this function owns and frees below
    // (filesec.c:148-160).
    let got = unsafe { filesec_get_property(fsec, FILESEC_ACL, (&raw mut acl).cast::<c_void>()) };
    if got != 0 || acl.is_null() {
        let errno = if got != 0 {
            io::Error::last_os_error().raw_os_error()
        } else {
            None
        };
        return ListRead::Uncopied(errno);
    }
    let mut allows = false;
    let mut entry: *mut c_void = std::ptr::null_mut();
    let mut which = ACL_FIRST_ENTRY;
    // SAFETY: `acl` is the live list; `entry` is written by the call and read only
    // while `acl` lives.
    while unsafe { acl_get_entry(acl, which, &mut entry) } == 0 {
        which = ACL_NEXT_ENTRY;
        let mut tag: c_int = 0;
        // SAFETY: `entry` is an entry of the live `acl`; `tag` is this frame's.
        if unsafe { acl_get_tag_type(entry, &mut tag) } == 0 && tag == ACL_EXTENDED_ALLOW {
            allows = true;
            break;
        }
    }
    // SAFETY: `acl` came from `filesec_get_property` and is freed exactly once.
    unsafe { acl_free(acl) };
    ListRead::Listed(allows)
}

/// In a test, what libmalloc's `free` may do as `filesec_free` returns: leave errno
/// EINVAL (a refused `madvise`), on threads that ask for it.
#[cfg(all(test, target_vendor = "apple"))]
pub(crate) mod errno_seam {
    use std::cell::Cell;

    thread_local! {
        static CLOBBER: Cell<bool> = const { Cell::new(false) };
    }

    unsafe extern "C" {
        fn __error() -> *mut std::ffi::c_int;
    }

    /// EINVAL, which XNU's madvise answers for a map entry it will not reuse.
    pub(crate) const EINVAL: std::ffi::c_int = 22;

    /// Run `body` with errno set to EINVAL each time Libc's frees return.
    pub(crate) fn clobbered<R>(body: impl FnOnce() -> R) -> R {
        CLOBBER.set(true);
        let out = body();
        CLOBBER.set(false);
        out
    }

    pub(super) fn after_free() {
        if CLOBBER.get() {
            // SAFETY: `__error` returns this thread's errno slot, live for the thread.
            unsafe { *__error() = EINVAL };
        }
    }
}

// The path entry's calls, macOS arm64 only (Libc-1752.120.2, xnu-12377.121.6). On macOS
// every target but i386 and x86_64 has `__DARWIN_ONLY_64_BIT_INO_T` 1 (XNU
// bsd/sys/cdefs.h:757-771), so arm64's `_lstatx_np` (the SDK's libsystem_c.tbd exports it
// for arm64e) is the 64-bit-inode call, and `struct stat` is `struct stat64`. x86_64,
// where `_lstatx_np` is the 32-bit-inode call beside `_lstatx_np$INODE64`, takes no path
// entry here.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
unsafe extern "C" {
    // SDK sys/stat.h:425.
    fn lstatx_np(path: *const c_char, sb: *mut c_void, fsec: *mut c_void) -> c_int;
}

/// `filesec_property_t`'s `FILESEC_OWNER`, `FILESEC_MODE` and `FILESEC_ACL` (SDK
/// sys/fcntl.h:601-612), a C enum whose values all fit an `int`, passed as one.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const FILESEC_OWNER: c_int = 1;
#[cfg(target_vendor = "apple")]
const FILESEC_MODE: c_int = 4;
#[cfg(target_vendor = "apple")]
const FILESEC_ACL: c_int = 5;

/// The words of the `struct stat` buffer `lstatx_np` fills, which nothing here reads:
/// 256 bytes, 8-aligned, against the 144 the kernel copies out on arm64 (XNU
/// bsd/sys/stat.h:166-182, `struct stat64`; bsd/vfs/vfs_syscalls.c:7523, the copyout of
/// `sizeof(user64_stat64)`). Law A5 holds the bound on this Mac, and the assertion below
/// refuses to compile a buffer of 144 bytes or fewer.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) const STAT_WORDS: usize = 32;

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const _: () = assert!(
    STAT_WORDS * 8 > 144,
    "the buffer holds the 144 bytes the kernel copies out, and A5 a word past them"
);

/// What one `lstatx_np` of a path read, as plain integers: no pointer leaves this
/// module, and errno only as the number read straight after the call. Each `None` is a
/// value Libc did not give.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Looked {
    /// `lstatx_np`'s return: 0, -1 (the syscall failed, errno set), or the 12 (ENOMEM)
    /// statx1 returns itself when its first buffer cannot be allocated (Libc
    /// sys/statx_np.c:159-162).
    pub(crate) rc: c_int,
    /// errno, read straight after the call, and only when `rc` is -1.
    pub(crate) errno: Option<i32>,
    /// `FILESEC_OWNER`: the uid statx1 copied from the stat (statx_np.c:192). `None`
    /// where it never set it (a failed realloc, statx_np.c:181-187).
    pub(crate) uid: Option<u32>,
    /// `FILESEC_MODE`: the stat's `st_mode`, file type bits included (statx_np.c:194;
    /// XNU vfs_vnops.c:1595-1621). `None` where statx1 never set it.
    pub(crate) mode: Option<u16>,
    /// Whether the filesec holds an access list: `FILESEC_ACL`'s validity, tested
    /// `!= 0`. `None` if the query refused.
    pub(crate) listed: Option<bool>,
}

/// One `lstatx_np` of `path` into `sb`, its filesec read and freed: one lookup that
/// does not follow a link at its last component (unless the path ends in a slash, where
/// the read open follows it too) and one `vnode_getattr`, never an open. statx1 repeats
/// the pair, keeping the last reading, while the access list outgrows its buffer, first
/// sized for 16 entries (Libc sys/statx_np.c:34, 168-189): twice for a list of more than
/// 16 entries that does not change, which `by_path` reads as `Listed` and leaves to the
/// open. `None`: `filesec_init` failed, and nothing was called or allocated.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub(crate) fn look(path: &CStr, sb: &mut [u64; STAT_WORDS]) -> Option<Looked> {
    // SAFETY: `filesec_init` takes nothing; the filesec it returns (Libc gen/filesec.c:61-70,
    // a malloc with only `fs_valid` set, to 0) is owned here and freed once below.
    let fsec = unsafe { filesec_init() };
    if fsec.is_null() {
        return None;
    }
    // SAFETY: `fsec` is filesec_init's, non-null, and freed only below, after this call.
    let looked = unsafe { look_into(path, sb, fsec) };
    // SAFETY: `fsec` is filesec_init's, non-null, and freed exactly once, here, on the one
    // path out after it was made (`look_into` cannot fail early or panic). filesec_free
    // frees the list buffer statx1 handed it only when its list bit is set, and the filesec
    // itself (filesec.c:94-99, 343-353); nothing here obtained a pointer into either.
    unsafe { filesec_free(fsec) };
    Some(looked)
}

/// [`look`]'s `lstatx_np` and its reads of the filesec, which `look` makes and frees.
///
/// # Safety
/// `fsec` is a live filesec from `filesec_init`, not yet freed, and is not freed during
/// the call.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
unsafe fn look_into(path: &CStr, sb: &mut [u64; STAT_WORDS], fsec: *mut c_void) -> Looked {
    // SAFETY: `path` is NUL-terminated and outlives the call; `sb` is 256 writable,
    // 8-aligned bytes, more than the 144 the kernel copies out (STAT_WORDS), and nothing
    // here reads it; `fsec` is a live filesec, so the call goes to statx1 (Libc
    // sys/statx_np.c:63-69), which hands `sb` to the syscall, reads back only the owner,
    // group and mode the kernel wrote there (192-194), and keeps its own list buffer in
    // `fsec` or frees it (204-205, 216-218).
    let rc = unsafe { lstatx_np(path.as_ptr(), sb.as_mut_ptr().cast::<c_void>(), fsec) };
    let errno = if rc == -1 {
        io::Error::last_os_error().raw_os_error()
    } else {
        None
    };
    if rc != 0 {
        return Looked {
            rc,
            errno,
            uid: None,
            mode: None,
            listed: None,
        };
    }
    let mut owner: u32 = 0;
    // SAFETY: `fsec` is live; FILESEC_OWNER writes one uid_t (u32) through the pointer, and
    // only when the owner is set (filesec.c:108-115); `owner` is this frame's.
    let got_owner =
        unsafe { filesec_get_property(fsec, FILESEC_OWNER, (&raw mut owner).cast::<c_void>()) };
    let mut st_mode: u16 = 0;
    // SAFETY: `fsec` is live; FILESEC_MODE writes one mode_t (u16) through the pointer, and
    // only when the mode is set (filesec.c:140-147); `st_mode` is this frame's.
    let got_mode =
        unsafe { filesec_get_property(fsec, FILESEC_MODE, (&raw mut st_mode).cast::<c_void>()) };
    let mut valid: c_int = 0;
    // SAFETY: `fsec` is live; the query writes one int through `validptr` and allocates
    // nothing (filesec.c:303-341); `valid` is this frame's. It writes the bitmask
    // `fs_valid & FS_VALID_ACL` (filesec.c:45, 55, 325-328, 339), 32 when a list is held, so
    // "listed" is `!= 0`, never `== 1`.
    let got_list = unsafe { filesec_query_property(fsec, FILESEC_ACL, &raw mut valid) };
    Looked {
        rc,
        errno,
        uid: if got_owner == 0 { Some(owner) } else { None },
        mode: if got_mode == 0 { Some(st_mode) } else { None },
        listed: if got_list == 0 {
            Some(valid != 0)
        } else {
            None
        },
    }
}

/// No extended access list off Apple: a Linux POSIX ACL that grants anyone but the
/// owner shows in the group mode bits (its mask), which the mode clause already reads.
#[cfg(not(target_vendor = "apple"))]
pub(crate) fn acl_allows(_file: &File) -> io::Result<bool> {
    Ok(false)
}
