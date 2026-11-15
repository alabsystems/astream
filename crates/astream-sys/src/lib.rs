// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! # astream-sys
//!
//! The broker's OS cordon: kernel operations that safe `std` does not offer.
//!
//! - [`barrier_sync`]: an ORDERING-only flush of a file. On Apple it is
//!   `fcntl(fd, F_BARRIERFSYNC)`, which fcntl(2) defines device-wide: every write
//!   issued before it reaches stable media before any write issued after it, without
//!   waiting for the drive to empty its cache — the cost `F_FULLFSYNC` pays. Anywhere
//!   else it is `sync_data`, a FULL flush: Linux has no ordering-only primitive
//!   (`fdatasync` flushes the drive cache), so the fallback is never weaker than asked.
//!
//!   What the two cost was measured once, on ONE Mac (Apple SSD, APFS), a shared
//!   development machine under other agents' builds and Strict brokers (load averages
//!   2–48), by a scratch probe that is not in this repository — so these are that
//!   machine's numbers on those days, not a bound. A single writer, write + flush, in
//!   a tight loop: a 64-byte append took p50 0.14 ms, p95 1.1 ms, p99 5.1 ms with
//!   `F_BARRIERFSYNC`, and p50 7.3 ms, p95 17 ms, p99 21 ms with `F_FULLFSYNC` (n =
//!   6,000 each, three passes pooled); a 4 KiB append p50 0.49 / p99 2.3 ms against
//!   p50 4.3 / p99 8.6 ms (n = 6,000 each). The flush's own floor, every single-writer
//!   pass pooled: `F_BARRIERFSYNC` min 94 µs, p50 294 µs (n = 26,000); `F_FULLFSYNC` min
//!   1.8 ms, p50 4.3 ms (n = 42,000), in steps of about 4.2 ms when the device is
//!   already flushing for someone else. The tiers that use the barrier measure their
//!   own cost before they become a default.
//! - [`full_sync`] and [`full_sync_data`]: the FULL flush every durable write of the
//!   broker ends with, [`File::sync_all`] and [`File::sync_data`] (`F_FULLFSYNC` on
//!   Apple, `fsync(2)` / `fdatasync(2)` on Linux), in every build. Debug assertions do
//!   not weaken a full flush: Strict acknowledgements, durable heads and recovery
//!   identity rely on the same persistence contract in a debug application. Only a
//!   TEST's process tree, which a test binary marks with [`TEST_PLAIN_FSYNC_ENV`] before
//!   any test runs, takes a plain `fsync(2)` in a debug build on Apple: the same flush
//!   at the same point, without the drain of the drive's cache, which only a power loss
//!   shows and no test makes. No application sets the mark, and a release build never
//!   reads it.
//! - [`plain_fsync`] (Unix): a plain `fsync(2)` of any open descriptor (a `&File`, an
//!   `OwnedFd`, a `BorrowedFd`), retried on `EINTR`, in every build: the file's writes,
//!   or a directory's entries, handed to the drive without the drain of its cache, for a
//!   caller that asks for exactly that (aterm-durable's `ordered_or_fsync`, where a
//!   volume refuses both the barrier and the full flush, and the plain flushes aterm
//!   names, through aterm-durable's `primitive::fsync`). On Apple it is the `fsync`
//!   behind [`full_sync`] in a test's process tree; elsewhere the `owner` module's
//!   `fsync`, the call [`File::sync_all`] makes there.
//! - [`flush_tally`]: how many of those four calls this process has made, by kind, so
//!   a reading around a span of a process's work counts every flush it asked the OS
//!   for through this crate, whatever the broker's own counts say (astream-broker's
//!   benches gate it, and its `<log>.health` carries it).
//! - [`flush_times`]: how long those calls took, by kind, and the last
//!   [`SLOW_FLUSHES_KEPT`] slower than [`SLOW_FLUSH_NS`] (1 ms), each with its kind, start
//!   and end on [`clock_ns`], the clock a caller reads to line its own stalls up with a
//!   flush: on Apple the machine's `CLOCK_UPTIME_RAW` (the clock std's `Instant` reads
//!   there), so two processes' readings compare; elsewhere this process's own
//!   ([`FLUSH_CLOCK`]). Each flush is counted as it begins and timed as it returns, in one
//!   door every flush of the crate goes through, and astream-broker's `<log>.health`
//!   carries the totals and the ring.
//! - [`boot_session`]: THIS BOOT of the machine as the kernel names it, as 16 bytes.
//!   Two readings are equal exactly when no boot came between them, which is the
//!   question a log that trusts the page cache asks — "has the kernel holding my
//!   unflushed writes run throughout?". A process crash, a restart, a sleep or a clock
//!   step leave it as it was (the page cache outlives all of them); a reboot, a kernel
//!   panic or a power loss give a new one. Apple: `kern.bootsessionuuid`. Linux:
//!   `/proc/sys/kernel/random/boot_id` (safe `std`). Elsewhere `None`, which the
//!   broker reads as "a boot it cannot vouch for": the safe direction.
//!   [`parse_boot_id`] reads a boot id's text as its 16 bytes and [`boot_id_text`]
//!   writes them back in the kernel's form, so a caller that records a boot as text
//!   and compares it later holds no UUID writer of its own.
//! - `socket_hung_up` (Apple only): whether a zero-wait `poll` sees both directions
//!   of a socket hung up. astream-broker's client asks it only after setting a
//!   socket's read or write timeout was refused with `EINVAL`
//!   (`Subscription::set_read_timeout`, `Closer::set_read_timeout`,
//!   `Closer::set_write_timeout`), which XNU answers on a socket the peer already
//!   shut down: then there is nothing left to bound, and the refusal is no error. A
//!   refusal on a live socket is kept.
//! - [`close_on_fork`]: request `FD_CLOFORK` and report whether the kernel retained
//!   it. Some Apple kernels ignore this flag; success alone does not establish
//!   fork exclusion. The caller's close-on-exec and spawn policy still apply.
//! - [`install_sighup_handler`] and [`sighup_generation`]: a process-wide `SIGHUP`
//!   handler that only counts the signals (Apple; elsewhere `Unsupported` and a
//!   count of zero). Only the broker's revocation file installs it, so that a
//!   `SIGHUP` reloads the file (`Broker::load_revocation_file`, `asb serve
//!   --revocation-file`); a broker that loads none never changes the process's
//!   `SIGHUP` disposition.
//! - The owner-only file rule: [`open_nonblocking`] opens a path read-only and
//!   without waiting (`O_NONBLOCK`, so a FIFO opens at once), following or refusing a
//!   link at its last component (`O_NOFOLLOW`), and [`open_nonblocking_rw`] the same
//!   way for reading and writing, writing nothing, so a check is refused where a writer
//!   in place would be; [`owner_private`] and
//!   [`owner_private_dir`] judge the open descriptor: the kind asked for (a regular
//!   file, a directory), owned by [`euid`], no group or other permission bit, and on
//!   macOS no access-list entry that allows anyone anything (`fstatx_np` into a filesec,
//!   decided by return codes and validity bits, never errno), because
//!   macOS checks an extended ACL before the mode bits. astream-cap's `capfile` reads
//!   every secret file through it (claim `cap.secret-file-owner-only`).
//!   [`owner_private_dir_by_path`] (macOS arm64) gives `owner_private_dir`'s verdict on a
//!   path from one `lstatx_np` of it, never an open, where the path's attributes decide
//!   it (a [`DirByPath`]): a missing path, a link, a kind or owner refusal of an object
//!   with no access list, and this user's directory with no list and its owner read and
//!   search bits set; every other path is left to the open ([`PathUndecided`]). Both
//!   entries judge through one set of clauses, the private `owner_rule` module, which
//!   [`kind_and_owner_of`] also holds a caller's own metadata to.
//!
//! ## The cordon
//!
//! The crate root is `deny(unsafe_code)`, and its OS modules re-permit it, for
//! hand-declared FFI calls with a `// SAFETY:` note each. `apple`
//! (`cfg(target_vendor = "apple")`): `fcntl(F_BARRIERFSYNC)` behind [`barrier_sync`],
//! `fsync` behind [`plain_fsync`] and behind [`full_sync`] in a test's debug process,
//! `sysctlbyname("kern.bootsessionuuid")` behind [`boot_session`], `poll` behind
//! `socket_hung_up`, `fcntl(F_GETFD)` and `fcntl(F_SETFD)` behind [`close_on_fork`],
//! `clock_gettime_nsec_np(CLOCK_UPTIME_RAW)` behind [`clock_ns`], and `signal(SIGHUP)`
//! behind [`install_sighup_handler`]. `owner`
//! (`cfg(unix)`): `geteuid` behind [`euid`] and [`owner_private`], on Apple
//! `fstatx_np`, `filesec_init`, `filesec_query_property`, `filesec_get_property`,
//! `filesec_free`, `acl_get_entry`, `acl_get_tag_type` and `acl_free` behind
//! [`owner_private`] and [`owner_private_dir`], on macOS arm64 `lstatx_np` and the same
//! filesec calls behind [`owner_private_dir_by_path`], and off Apple `fsync` behind
//! [`plain_fsync`]; the per-OS `O_NONBLOCK` and `O_NOFOLLOW` numbers
//! [`open_nonblocking`] and [`open_nonblocking_rw`] pass to safe `std` live there too.
//! `file_identity` (`cfg(windows)`) reads the kernel's volume and file index for
//! [`file_matches_path`], so a path replacement is never judged by size or time.
//! Nothing else here may use `unsafe` — the compiler refuses it — and no errno or raw
//! pointer leaves those modules: every call returns `io::Result` or an owned value.
//! `astream-broker` stays `forbid(unsafe_code)` and reaches the OS through this
//! crate's safe functions (and reads a barrier's refusal through
//! [`barrier_refused`], and a directory flush's through [`dir_flush_unavailable`]:
//! plain errno numbers that need no `unsafe`).
//!
//! ## Who else calls it
//!
//! aterm depends on this crate directly (astream's `docs/ROADMAP.md`, "What aterm
//! uses beyond the fabric"). It reads the boot through [`boot_session`] and
//! [`parse_boot_id`] in aterm-link, aterm-agent, aterm-acaffeine, aterm-gui, aterm-uds,
//! aterm-release (its publisher fence's `fence-boot`, compared as 16 bytes), aterm-cli
//! (its setup ledger) and aterm-update (which reads Linux's `boot_id` file itself and
//! judges it with [`parse_boot_id`]), and writes the boot text it records (aterm-agent's ledger and
//! tapes, aterm-acaffeine's state file, aterm-release's fence, aterm-link's messages)
//! with [`boot_id_text`]. Outside tests (whose oracle is the kernel's own text), only
//! aterm-machines reads `kern.bootsessionuuid` otherwise, with a `sysctl -n`
//! subprocess, to read what its enrollment root script reads. On
//! Apple targets every ordered write it makes, to a file or a directory, is finished
//! with [`barrier_sync`], [`barrier_refused`] telling a volume that takes no barrier
//! from a failed flush; elsewhere aterm-durable's ordered write is [`full_sync`]. Every
//! durable write aterm-durable finishes ends with [`full_sync`] or [`full_sync_data`],
//! and the plain flush its ordered write falls back to where a volume refuses both is
//! [`plain_fsync`], as is every plain flush aterm names (aterm-durable's
//! `primitive::fsync`: the crash journal's folders, atpkg's stores and the handle-relative
//! directories of atpkg's build cache and aterm-gui's pinned folders), so [`flush_tally`]
//! counts every flush aterm-durable makes, and aterm-link's BROKER section quotes the
//! tally its broker's `<log>.health` carries.
//! aterm-durable's `Flush::dir_best_effort` and aterm-link's
//! tolerated state-dir flushes go on without a directory's flush exactly where
//! [`dir_flush_unavailable`] says so, the broker's own rule, and return any other
//! failure. [`file_flush_refused`] classifies refusals from a file's selected flush;
//! whether a writer accepts one is its own durability policy. aterm reaches `fcntl`, `fsync`
//! (through [`plain_fsync`], and [`full_sync`] in a marked test's process tree:
//! [`TEST_PLAIN_FSYNC_ENV`]), `sysctlbyname` and `poll` (the last through
//! astream-broker's client, whose `Closer` it bounds both ways on every dial), and
//! never installs the `SIGHUP` handler. Its private files are held to
//! the owner rule: aterm-uds's `private_file` judges each file it reads with
//! [`owner_private`] and each private directory with [`owner_private_dir_by_path`],
//! opening it and judging the descriptor with [`owner_private_dir`] where the path's
//! attributes cannot decide (its refused open judged with [`kind_and_owner_of`]), and
//! aterm-link reads the fabric's mint secret through capfile's `read_secret_at`, and
//! `fabric on --dry-run` through its `read_secret_at_narrowed`.

#![deny(unsafe_code)]

use std::fs::File;
use std::io;

mod flush_times;
pub use flush_times::{
    clock_ns, flush_times, slow_flushes_missed, FlushClock, FlushKind, FlushTimes, SlowFlush,
    FLUSH_CLOCK, SLOW_FLUSHES_KEPT, SLOW_FLUSH_NS,
};

#[cfg(target_vendor = "apple")]
macro_rules! apple_ffi {
    (socket_hangup($fds:expr)) => {
        // SAFETY: the caller provides two initialized pollfd entries, writable for
        // this call; each descriptor is retained by a BorrowedFd. Timeout zero does
        // not wait for readiness and the call does not read or change socket flags.
        unsafe { poll($fds, 2, 0) }
    };
    (barrier_fsync($fd:expr, $cmd:expr)) => {
        // SAFETY: `fd` is a valid open descriptor owned by `file` and `F_BARRIERFSYNC` takes no extra arguments.
        unsafe { fcntl($fd, $cmd) }
    };
    (fsync($fd:expr)) => {
        // SAFETY: `fd` is a valid open descriptor, retained by a BorrowedFd for the call;
        // `fsync` takes it by value and touches no memory.
        unsafe { fsync($fd) }
    };
    (sysctlbyname($name:expr, $oldp:expr, $oldlenp:expr, $newp:expr, $newlen:expr)) => {
        // SAFETY: NUL-terminated name, writable buffer, and length pointer are valid for the duration of the call.
        unsafe { sysctlbyname($name, $oldp, $oldlenp, $newp, $newlen) }
    };
    (fd_flags($fd:expr)) => {
        // SAFETY: `F_GETFD` reads one descriptor's flags and touches no memory; the
        // descriptor is retained by a BorrowedFd for the call.
        unsafe { fcntl($fd, F_GETFD) }
    };
    (set_fd_flags($fd:expr, $flags:expr)) => {
        // SAFETY: `F_SETFD` sets one descriptor's flags from an int and touches no memory;
        // the descriptor is retained by a BorrowedFd for the call.
        unsafe { fcntl($fd, F_SETFD, $flags) }
    };
    (uptime_raw_ns($clock:expr)) => {
        // SAFETY: `clock_gettime_nsec_np` takes a clock id by value, touches no memory and
        // returns the reading (0 for a clock id it does not know, which `CLOCK_UPTIME_RAW` is
        // not: Darwin has defined it since macOS 10.12).
        unsafe { clock_gettime_nsec_np($clock) }
    };
    (install_sighup($sig:expr, $handler:expr)) => {
        // SAFETY: `SIGHUP` is a valid standard POSIX signal number and `$handler` is an
        // async-signal-safe `extern "C" fn(c_int)` that only performs an atomic fetch_add.
        unsafe { signal($sig, $handler) }
    };
}

/// Evaluates `$call` until it answers anything but `EINTR`
/// ([`io::ErrorKind::Interrupted`]): the retry every flush of the cordon makes, so an
/// interrupted flush is never reported as a failed one.
#[cfg(any(test, unix))]
macro_rules! retried_on_eintr {
    ($call:expr) => {{
        loop {
            let step: ::std::io::Result<()> = $call;
            match step {
                Err(e) if crate::is_eintr(&e) => {}
                answer => break answer,
            }
        }
    }};
}

#[cfg(unix)]
pub(crate) use retried_on_eintr;

#[cfg(any(test, unix))]
pub(crate) fn is_eintr(err: &io::Error) -> bool {
    err.kind() == io::ErrorKind::Interrupted
}

#[cfg(target_vendor = "apple")]
#[allow(unsafe_code)]
mod apple;

#[cfg(unix)]
#[allow(unsafe_code)]
mod owner;

#[cfg(unix)]
mod owner_rule;

#[cfg(windows)]
#[allow(unsafe_code)]
mod file_identity;

/// Whether the open descriptor and the path currently name the same file.
/// Follows the path's final symlink, just as a normal file open does.
///
/// # Errors
/// Propagates metadata/open errors, or returns `Unsupported` on platforms without
/// a kernel file identity implementation.
pub fn file_matches_path(file: &File, path: &std::path::Path) -> io::Result<bool> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let opened = file.metadata()?;
        let named = std::fs::metadata(path)?;
        Ok((opened.dev(), opened.ino()) == (named.dev(), named.ino()))
    }
    #[cfg(windows)]
    {
        let named = File::open(path)?;
        Ok(file_identity::of(file)? == file_identity::of(&named)?)
    }
    #[cfg(not(any(unix, windows)))]
    {
        let _ = (file, path);
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "kernel file identity unavailable",
        ))
    }
}

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

#[cfg(any(test, not(clean_islands)))]
mod twins;

#[cfg(clean_islands)]
#[path = "boot_island.rs"]
mod boot_island;
#[cfg(clean_islands)]
pub use boot_island::boot_nibble_advance;
#[cfg(not(clean_islands))]
pub use twins::boot_nibble_advance;

contract_fn! {
    /// Verified check that a parsed boot session UUID has exactly 32 hex nibbles (`16` bytes),
    /// linked via `clean-kernel-defeq` to `boot_nibble_count_valid_isl`.
    #[must_use]
    pub const fn boot_nibble_count_valid(nibbles: usize) -> bool
    clauses [ensures result == (nibbles == 32)]
    {
        nibbles == 32
    }
}

#[must_use]
pub const fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0' => Some(0),
        b'1' => Some(1),
        b'2' => Some(2),
        b'3' => Some(3),
        b'4' => Some(4),
        b'5' => Some(5),
        b'6' => Some(6),
        b'7' => Some(7),
        b'8' => Some(8),
        b'9' => Some(9),
        b'a' | b'A' => Some(10),
        b'b' | b'B' => Some(11),
        b'c' | b'C' => Some(12),
        b'd' | b'D' => Some(13),
        b'e' | b'E' => Some(14),
        b'f' | b'F' => Some(15),
        _ => None,
    }
}

/// Pack a 16-byte boot session UUID into two big-endian `u64` words `(hi, lo)`
/// using fixed-width bitwise shifts.
#[must_use]
pub const fn encode_boot_id_u128_be(id: [u8; 16]) -> (u64, u64) {
    let hi = ((id[0] as u64) << 56)
        | ((id[1] as u64) << 48)
        | ((id[2] as u64) << 40)
        | ((id[3] as u64) << 32)
        | ((id[4] as u64) << 24)
        | ((id[5] as u64) << 16)
        | ((id[6] as u64) << 8)
        | (id[7] as u64);
    let lo = ((id[8] as u64) << 56)
        | ((id[9] as u64) << 48)
        | ((id[10] as u64) << 40)
        | ((id[11] as u64) << 32)
        | ((id[12] as u64) << 24)
        | ((id[13] as u64) << 16)
        | ((id[14] as u64) << 8)
        | (id[15] as u64);
    (hi, lo)
}

/// Unpack two big-endian `u64` words `(hi, lo)` into a 16-byte boot session UUID
/// using fixed-width bitwise shifts.
#[must_use]
pub const fn decode_boot_id_u128_be(hi: u64, lo: u64) -> [u8; 16] {
    [
        ((hi >> 56) & 0xFF) as u8,
        ((hi >> 48) & 0xFF) as u8,
        ((hi >> 40) & 0xFF) as u8,
        ((hi >> 32) & 0xFF) as u8,
        ((hi >> 24) & 0xFF) as u8,
        ((hi >> 16) & 0xFF) as u8,
        ((hi >> 8) & 0xFF) as u8,
        (hi & 0xFF) as u8,
        ((lo >> 56) & 0xFF) as u8,
        ((lo >> 48) & 0xFF) as u8,
        ((lo >> 40) & 0xFF) as u8,
        ((lo >> 32) & 0xFF) as u8,
        ((lo >> 24) & 0xFF) as u8,
        ((lo >> 16) & 0xFF) as u8,
        ((lo >> 8) & 0xFF) as u8,
        (lo & 0xFF) as u8,
    ]
}

/// Whether a zero-wait poll positively observes BOTH directions of this retained
/// socket hung up. A read-side EOF alone does not establish that writes cannot wait.
/// No bytes are consumed and descriptor flags/timeouts are unchanged. Any refusal
/// (including interruption), invalid descriptor or missing event returns `false`.
#[cfg(target_vendor = "apple")]
#[must_use]
pub fn socket_hung_up(socket: std::os::fd::BorrowedFd<'_>) -> bool {
    apple::socket_hung_up(socket)
}

/// Request `FD_CLOFORK` for `socket` and report whether the kernel retained the flag.
///
/// Apple kernels may accept `F_SETFD` while ignoring this flag. `Ok(false)` reports
/// that case, without claiming that a fork excludes the descriptor. The existing
/// close-on-exec flag is preserved. Other Unix targets return `Ok(false)` without
/// a call; callers still enforce their own descriptor policy when spawning.
///
/// # Errors
/// The `fcntl(2)` errno of reading or setting the descriptor's flags.
#[cfg(unix)]
pub fn close_on_fork(socket: std::os::fd::BorrowedFd<'_>) -> io::Result<bool> {
    #[cfg(target_vendor = "apple")]
    {
        apple::close_on_fork(socket)
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        let _ = socket;
        Ok(false)
    }
}

/// Install the process-wide Apple `SIGHUP` handler once. Success means installation
/// completed, so later `SIGHUP` signals advance [`sighup_generation`] rather than
/// terminating the process. Concurrent callers receive the same installation result.
/// This replaces any previous handler and does not restore it. Non-Apple targets
/// return [`io::ErrorKind::Unsupported`] without changing signal disposition.
pub fn install_sighup_handler() -> io::Result<()> {
    #[cfg(target_vendor = "apple")]
    {
        apple::install_sighup_handler()
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "SIGHUP reload is supported only on Apple targets",
        ))
    }
}

/// The current `SIGHUP` generation counter: increments on each `SIGHUP` delivered to
/// this process after a successful [`install_sighup_handler`] on Apple targets.
/// Other targets always return zero.
#[must_use]
pub fn sighup_generation() -> u64 {
    #[cfg(target_vendor = "apple")]
    {
        apple::sighup_generation()
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        0
    }
}

/// Whether a Darwin `errno` value (`ENODEV=19`, `EINVAL=22`, `ENOTTY=25`, `ENOTSUP=45`)
/// indicates that the filesystem or device refuses `F_BARRIERFSYNC`.
#[must_use]
pub const fn is_apple_barrier_refused_errno(errno: i32) -> bool {
    matches!(errno, 19 | 22 | 25 | 45)
}

/// The environment variable that marks a TEST's process tree: a test binary sets it to
/// `1` before any test runs, and every process it starts inherits it. Such a process,
/// built with debug assertions for an Apple target, takes a plain `fsync(2)` for
/// [`full_sync`] and [`full_sync_data`] ([`test_plain_fsync`]). No application sets it,
/// and a release build never reads it.
pub const TEST_PLAIN_FSYNC_ENV: &str = "ASTREAM_TEST_PLAIN_FSYNC";

/// Whether this process belongs to a test's process tree ([`TEST_PLAIN_FSYNC_ENV`] is
/// `1`), read once. Always `false` in a release build and off Apple targets.
#[must_use]
pub fn test_plain_fsync() -> bool {
    #[cfg(all(debug_assertions, target_vendor = "apple"))]
    {
        static MARKED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        *MARKED.get_or_init(|| std::env::var_os(TEST_PLAIN_FSYNC_ENV).is_some_and(|v| v == "1"))
    }
    #[cfg(not(all(debug_assertions, target_vendor = "apple")))]
    {
        false
    }
}

/// Make everything written to `file` durable, its data and metadata: [`File::sync_all`]
/// (`F_FULLFSYNC` on Apple), in every build, except a test's process tree in a debug
/// build on Apple, which takes a plain `fsync(2)` ([`TEST_PLAIN_FSYNC_ENV`]).
///
/// # Errors
/// The flush's own error.
pub fn full_sync(file: &File) -> io::Result<()> {
    // Counted and timed `full` whatever a test's process takes underneath: the call is a
    // full flush.
    flush_times::timed(FlushKind::Full, || {
        #[cfg(all(debug_assertions, target_vendor = "apple"))]
        if test_plain_fsync() {
            return apple::plain_fsync(std::os::fd::AsFd::as_fd(file));
        }
        file.sync_all()
    })
}

/// [`full_sync`] for `file`'s data and the metadata a read of it needs:
/// [`File::sync_data`] (`F_FULLFSYNC` on Apple, `fdatasync(2)` on Linux), in every build,
/// except a test's process tree as [`full_sync`] says.
///
/// # Errors
/// The flush's own error.
pub fn full_sync_data(file: &File) -> io::Result<()> {
    flush_times::timed(FlushKind::Full, || {
        #[cfg(all(debug_assertions, target_vendor = "apple"))]
        if test_plain_fsync() {
            return apple::plain_fsync(std::os::fd::AsFd::as_fd(file));
        }
        file.sync_data()
    })
}

/// Order every write to `file` issued before this call ahead of every write issued
/// after it, on stable media — without waiting for the media to hold either.
///
/// Apple: `fcntl(fd, F_BARRIERFSYNC)`, retried on `EINTR`. A filesystem or device
/// that cannot honour the barrier answers an error (`ENOTSUP`, `ENODEV`, `EINVAL` or
/// `ENOTTY`), which the caller must treat as "no ordering was promised" — the broker
/// then flushes in full instead. Elsewhere: [`File::sync_data`], a full flush, which
/// orders everything because it persists everything.
pub fn barrier_sync(file: &File) -> io::Result<()> {
    flush_times::timed(FlushKind::Barrier, || {
        #[cfg(target_vendor = "apple")]
        {
            apple::barrier_fsync(file)
        }
        #[cfg(not(target_vendor = "apple"))]
        {
            file.sync_data()
        }
    })
}

/// A plain `fsync(2)` of the open file or directory `fd` (a `&File`, an `OwnedFd`, a
/// `BorrowedFd`), retried while it is interrupted (`EINTR`), in every build: its writes,
/// or a directory's entries, handed to the drive, without the drain of the drive's cache
/// that [`full_sync`] waits for on Apple. For a caller that asks for exactly that flush —
/// a volume that refuses both [`barrier_sync`] and [`full_sync`] (a network home whose
/// server takes no `F_FULLFSYNC`) still takes it, as SQLite finds there — and for one
/// that holds a directory as a bare descriptor (aterm's handle-relative trees), which no
/// `File` method flushes. The cordon's `fsync`: the `apple` module's on Apple, the
/// `owner` module's elsewhere on Unix (where it is the call [`File::sync_all`] makes).
///
/// # Errors
/// The flush's own error.
#[cfg(unix)]
pub fn plain_fsync(fd: impl std::os::fd::AsFd) -> io::Result<()> {
    let fd = fd.as_fd();
    flush_times::timed(FlushKind::Plain, || {
        #[cfg(target_vendor = "apple")]
        {
            apple::plain_fsync(fd)
        }
        #[cfg(not(target_vendor = "apple"))]
        {
            owner::plain_fsync(fd)
        }
    })
}

/// How many flushes this process has asked this crate for since it started, by kind
/// ([`flush_tally`]).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FlushTally {
    /// [`full_sync`] and [`full_sync_data`] calls (a plain `fsync(2)` underneath in a
    /// test's process tree, counted here all the same).
    pub full: u64,
    /// [`barrier_sync`] calls (a full flush off Apple, counted here all the same).
    pub barrier: u64,
    /// [`plain_fsync`] calls.
    pub plain: u64,
}

/// The flushes this process has asked this crate for so far: every [`full_sync`] and
/// [`full_sync_data`] call is one `full`, every [`barrier_sync`] call one `barrier`,
/// every [`plain_fsync`] call one `plain`, counted as the call begins, whatever it then
/// returns (a barrier the device refuses is counted, and so is the full flush a caller
/// issues in its place).
///
/// It counts calls, not what any caller meant by them. `astream-broker` is
/// `forbid(unsafe_code)` and finishes every write it makes durable or ordered through
/// this crate, so two readings around a span of a broker's work count every flush that
/// work asked for, whether or not the broker's own bookkeeping (its `FlushCounts`)
/// counted it; a flush through [`File::sync_data`] or [`File::sync_all`] directly is no
/// call here and escapes the tally. The count is process-wide, so it reads one
/// caller's flushes alone only in a process where nothing else flushes through this
/// crate meanwhile: astream-broker's benches, which gate it, run one broker each.
/// [`flush_times`] is how long the same calls took.
#[must_use]
pub fn flush_tally() -> FlushTally {
    let ledger = &flush_times::LEDGER;
    FlushTally {
        full: ledger.count(FlushKind::Full),
        barrier: ledger.count(FlushKind::Barrier),
        plain: ledger.count(FlushKind::Plain),
    }
}

/// Whether `err`, from [`barrier_sync`], says the file or its device cannot take a
/// barrier at all — `ENOTSUP`, `ENODEV`, `EINVAL` or `ENOTTY` on Apple — rather than
/// that a flush failed. The caller then knows no ordering was promised and the bytes
/// are still only in the page cache: it flushes in full instead, and serves the
/// stronger tier from then on. Any other error is a failed flush, to be handled as a
/// failed `fsync` is.
///
/// Always `false` off Apple: there [`barrier_sync`] IS a full flush, so any error it
/// returns is a failed flush.
#[must_use]
pub fn barrier_refused(err: &io::Error) -> bool {
    // The errno values of <sys/errno.h> on Apple platforms (Darwin's own numbering:
    // ENOTSUP is 45 there, not Linux's 95). Plain numbers, not FFI: nothing here
    // crosses into the kernel, so the cordon's `unsafe` stays in `apple`.
    #[cfg(target_vendor = "apple")]
    {
        match err.raw_os_error() {
            Some(errno) => is_apple_barrier_refused_errno(errno),
            None => false,
        }
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        let _ = err;
        false
    }
}

/// Whether `err`, from a flush of an open handle ([`full_sync`], [`full_sync_data`], a
/// plain `fsync(2)`, or the full flush a caller issues where [`barrier_refused`] said
/// the barrier was refused), says the handle's file or volume cannot be flushed at all,
/// rather than that a flush failed: `Unsupported` or `InvalidInput` by kind everywhere,
/// and on Apple the errnos a volume answers a flush `fcntl` it cannot take with
/// ([`is_apple_barrier_refused_errno`]: `F_FULLFSYNC` is refused as `F_BARRIERFSYNC`
/// is). The kind alone misses some of them: no std names `ENODEV` (what a full flush of
/// `/dev/null` answers) or `ENOTTY` by kind, and a stock std reads only Darwin's
/// `EOPNOTSUPP` (102), not its `ENOTSUP` (45), as `Unsupported`, where the Trust std reads
/// both.
///
/// A refused flush leaves the bytes where they were, in the page cache: a crash of the
/// process loses none of them, a power loss may. Any other error (`EIO`, `ENOSPC`, ...)
/// is a failed flush, handled as a failed `fsync` is: a later flush that succeeds says
/// nothing about what the failed one was to cover.
///
/// This is the classification only. A writer whose promise rests on the flush refuses
/// either way; one that can go on where its volume takes no flush (a mark whose loss
/// costs a repeat) goes on exactly where this says so. [`dir_flush_unavailable`] is this
/// rule for a directory's handle, and more.
#[must_use]
pub fn file_flush_refused(err: &io::Error) -> bool {
    if matches!(
        err.kind(),
        io::ErrorKind::Unsupported | io::ErrorKind::InvalidInput
    ) {
        return true;
    }
    // Plain errno numbers, not FFI, as in `barrier_refused`.
    #[cfg(target_vendor = "apple")]
    {
        err.raw_os_error()
            .is_some_and(is_apple_barrier_refused_errno)
    }
    #[cfg(not(target_vendor = "apple"))]
    {
        false
    }
}

/// Whether `err`, from opening a directory or from a full flush of its handle
/// ([`full_sync`]), says the directory's entries simply cannot be flushed here, rather
/// than that a flush failed:
///
/// - a filesystem that refuses to flush a directory handle ([`file_flush_refused`]:
///   `Unsupported` or `InvalidInput`, and on Apple the refusal errnos, Darwin's `ENOTSUP`
///   among them);
/// - a directory this process may write but not OPEN (`PermissionDenied`): a
///   write-only `0300` directory, where opening a file inside it is allowed;
/// - a directory that is gone by the time it is opened (`NotFound`).
///
/// The file's own bytes are flushed on their own handle; there is nothing more a writer
/// can do about the entry, and failing here would refuse a write that landed. Any other
/// error (`EIO`, `ENOSPC`, ...) is a failed flush: the entry may not survive a power loss,
/// and the caller handles it as a failed `fsync`.
///
/// This is the classification only. Each caller decides what an unavailable flush means
/// for it: astream-broker's `sync_parent_dir` goes on without the entry's flush, and a
/// writer whose promise rests on that flush refuses instead.
#[must_use]
pub fn dir_flush_unavailable(err: &io::Error) -> bool {
    matches!(
        err.kind(),
        io::ErrorKind::PermissionDenied | io::ErrorKind::NotFound
    ) || file_flush_refused(err)
}

/// This boot's id as 16 bytes, or `None` where this host cannot read one (or reads
/// something that is not a boot id: see [`parse_boot_id`]).
#[must_use]
pub fn boot_session() -> Option<[u8; 16]> {
    #[cfg(target_vendor = "apple")]
    {
        match apple::boot_session_uuid() {
            Some(buf) => parse_boot_id(&buf),
            None => None,
        }
    }
    #[cfg(any(target_os = "linux", target_os = "android"))]
    {
        let raw = match std::fs::read("/proc/sys/kernel/random/boot_id") {
            Ok(b) => b,
            Err(_) => return None,
        };
        parse_boot_id(&raw)
    }
    #[cfg(not(any(target_vendor = "apple", target_os = "linux", target_os = "android")))]
    {
        None
    }
}

#[must_use]
pub const fn nul_offset(raw: &[u8]) -> usize {
    let mut i = 0usize;
    let mut scan = raw;
    while let &[b, ref tail @ ..] = scan {
        if b == 0 {
            return i;
        }
        i = i.saturating_add(1);
        scan = tail;
    }
    raw.len()
}

/// Call-free `const fn` scanner that parses a NUL-terminated or whitespace-framed
/// ASCII UUID into two non-zero big-endian `u64` words `(hi, lo)`.
#[must_use]
pub const fn scan_boot_id_words(raw: &[u8]) -> Option<(u64, u64)> {
    let mut scan = raw;
    let mut hi = 0u64;
    let mut lo = 0u64;
    let mut nibbles = 0usize;
    let mut phase = 0u8;
    let mut skip = 0u8;
    while let &[b, ref tail @ ..] = scan {
        if skip > 0 {
            skip = (skip & 3).wrapping_sub(1);
            scan = tail;
            continue;
        }
        if b == 0 {
            break;
        }
        if matches!(b, b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C) {
            if phase == 1 {
                phase = 2;
            }
            scan = tail;
            continue;
        }
        if b == 0xC2 {
            if matches!(tail, &[0x85 | 0xA0, ..]) {
                if phase == 1 {
                    phase = 2;
                }
                skip = 1;
                scan = tail;
                continue;
            }
            return None;
        }
        if matches!(b, 0xE1..=0xE3) {
            if let &[b2, b3, ..] = tail {
                let is_ws = (b == 0xE1 && b2 == 0x9A && b3 == 0x80)
                    || (b == 0xE2
                        && b2 == 0x80
                        && ((b3 >= 0x80 && b3 <= 0x8A) || b3 == 0xA8 || b3 == 0xA9 || b3 == 0xAF))
                    || (b == 0xE2 && b2 == 0x81 && b3 == 0x9F)
                    || (b == 0xE3 && b2 == 0x80 && b3 == 0x80);
                if is_ws {
                    if phase == 1 {
                        phase = 2;
                    }
                    skip = 2;
                    scan = tail;
                    continue;
                }
            }
            return None;
        }
        if phase == 2 {
            return None;
        }
        phase = 1;
        if b == b'-' {
            scan = tail;
            continue;
        }
        let v: u64 = match b {
            b'0' => 0,
            b'1' => 1,
            b'2' => 2,
            b'3' => 3,
            b'4' => 4,
            b'5' => 5,
            b'6' => 6,
            b'7' => 7,
            b'8' => 8,
            b'9' => 9,
            b'a' | b'A' => 10,
            b'b' | b'B' => 11,
            b'c' | b'C' => 12,
            b'd' | b'D' => 13,
            b'e' | b'E' => 14,
            b'f' | b'F' => 15,
            _ => return None,
        };
        if nibbles < 16 {
            hi = (hi << 4) | v;
        } else if nibbles < 32 {
            lo = (lo << 4) | v;
        } else {
            return None;
        }
        nibbles = nibbles.saturating_add(1);
        scan = tail;
    }
    if nibbles == 32 && (hi | lo) != 0 {
        Some((hi, lo))
    } else {
        None
    }
}

/// The kernel's boot id text as 16 bytes: the bytes up to a NUL, whitespace trimmed,
/// then exactly 32 hexadecimal digits (either case) once every hyphen is dropped,
/// wherever it falls: the UUID form's four, none, or any others between the digits.
/// Anything else — empty, too short or long, a stray character — is `None`, and so is
/// the all-zero id, which a log's identity sidecar reserves for "the boot is unknown":
/// a damaged answer must never pass as a boot, because two equal damaged answers would
/// read as "no reboot came between them". [`boot_id_text`] is its inverse.
#[must_use]
#[allow(clippy::question_mark)]
pub fn parse_boot_id(raw: &[u8]) -> Option<[u8; 16]> {
    let Some((hi, lo)) = scan_boot_id_words(raw) else {
        return None;
    };
    if boot_nibble_count_valid(32) {
        Some(decode_boot_id_u128_be(hi, lo))
    } else {
        None
    }
}

/// Whether this host's kernel spells its boot id in lower-case hex: Linux's and
/// Android's `/proc/sys/kernel/random/boot_id` do; Apple's `kern.bootsessionuuid`
/// does not.
pub const KERNEL_SPELLS_BOOT_ID_LOWER: bool = cfg!(any(target_os = "linux", target_os = "android"));

const fn nibble_hex_char(nibble: u8, lower: bool) -> char {
    match nibble & 0x0F {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        10 => {
            if lower {
                'a'
            } else {
                'A'
            }
        }
        11 => {
            if lower {
                'b'
            } else {
                'B'
            }
        }
        12 => {
            if lower {
                'c'
            } else {
                'C'
            }
        }
        13 => {
            if lower {
                'd'
            } else {
                'D'
            }
        }
        14 => {
            if lower {
                'e'
            } else {
                'E'
            }
        }
        _ => {
            if lower {
                'f'
            } else {
                'F'
            }
        }
    }
}

const fn byte_hex_pair(byte: u8, lower: bool) -> (char, char) {
    (
        nibble_hex_char(byte >> 4, lower),
        nibble_hex_char(byte & 0x0F, lower),
    )
}

const fn boot_id_chars(id: [u8; 16], lower: bool) -> [char; 36] {
    let [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] = id;
    let (h0, l0) = byte_hex_pair(b0, lower);
    let (h1, l1) = byte_hex_pair(b1, lower);
    let (h2, l2) = byte_hex_pair(b2, lower);
    let (h3, l3) = byte_hex_pair(b3, lower);
    let (h4, l4) = byte_hex_pair(b4, lower);
    let (h5, l5) = byte_hex_pair(b5, lower);
    let (h6, l6) = byte_hex_pair(b6, lower);
    let (h7, l7) = byte_hex_pair(b7, lower);
    let (h8, l8) = byte_hex_pair(b8, lower);
    let (h9, l9) = byte_hex_pair(b9, lower);
    let (h10, l10) = byte_hex_pair(b10, lower);
    let (h11, l11) = byte_hex_pair(b11, lower);
    let (h12, l12) = byte_hex_pair(b12, lower);
    let (h13, l13) = byte_hex_pair(b13, lower);
    let (h14, l14) = byte_hex_pair(b14, lower);
    let (h15, l15) = byte_hex_pair(b15, lower);
    [
        h0, l0, h1, l1, h2, l2, h3, l3, '-', h4, l4, h5, l5, '-', h6, l6, h7, l7, '-', h8, l8, h9,
        l9, '-', h10, l10, h11, l11, h12, l12, h13, l13, h14, l14, h15, l15,
    ]
}

/// A boot id as text, the inverse of [`parse_boot_id`]: its 32 hex digits hyphenated
/// 8-4-4-4-12, the kernel's own form, lower-case when `lower` and upper-case otherwise.
/// [`KERNEL_SPELLS_BOOT_ID_LOWER`] is the case this host's kernel answers in, so
/// `boot_id_text(id, KERNEL_SPELLS_BOOT_ID_LOWER)` is the text the kernel answered for
/// the [`boot_session`] that read `id`. For every id but the reserved all-zero one,
/// `parse_boot_id(boot_id_text(id, lower).as_bytes()) == Some(id)`, in either case.
#[must_use]
pub fn boot_id_text(id: [u8; 16], lower: bool) -> String {
    String::from_iter(boot_id_chars(id, lower))
}

/// This process's effective user id: the owner [`owner_private`] holds a file to.
#[cfg(unix)]
#[must_use]
pub fn euid() -> u32 {
    owner::euid()
}

/// Whether [`open_nonblocking`] may follow a symbolic link at the path's last
/// component.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Links {
    /// Follow it, as `open(2)` does by default.
    Follow,
    /// Refuse it (`O_NOFOLLOW`): a link there fails the open (`ELOOP`) and nothing
    /// is opened through it. Only the last component is judged.
    Refuse,
}

/// Open `path` read-only and NON-BLOCKING (`O_NONBLOCK`), following or refusing a
/// link at its last component as `links` says.
///
/// Non-blocking so that whatever sits at the path is opened at once, a FIFO
/// included: a plain open of a FIFO waits until something opens its other end, so a
/// reader that opened before it judged would hang on one anyone could make with
/// `mkfifo`. Reads of a regular file are not changed by the flag. The caller judges
/// what it opened ([`owner_private`], [`owner_private_dir`]) before it reads a byte.
///
/// # Errors
///
/// The open's own error (`NotFound`, `PermissionDenied`, and under
/// [`Links::Refuse`] the OS's `ELOOP` for a link). On a target whose flags this
/// crate does not declare (Unix other than Apple, the BSDs, and Linux/Android on
/// x86, x86-64, RISC-V, s390x, LoongArch, ARM and PowerPC), `Unsupported`: nothing is
/// opened without them. Off Unix, a plain read-only open: there is no FIFO to wait
/// on, and `links` is not judged.
pub fn open_nonblocking(path: &std::path::Path, links: Links) -> io::Result<File> {
    open_flagged(path, links, false)
}

/// [`open_nonblocking`] for READING AND WRITING (`O_RDWR | O_NONBLOCK`), which writes
/// nothing itself: the access an open that will write in place asks for, so a file
/// that open would be refused (its mode, its owner, an immutable flag, an access-list
/// entry that denies the write, a read-only volume) is refused here the same way,
/// while one it would take opens without a byte changed. A FIFO opens at once, as it
/// does read-only.
///
/// # Errors
///
/// As [`open_nonblocking`], the open's own error for the write access included
/// (`PermissionDenied` for the mode, `EPERM` for an immutable flag, `EROFS`,
/// `EISDIR` for a directory, which no read-write open takes). Off Unix, a plain
/// read-write open.
pub fn open_nonblocking_rw(path: &std::path::Path, links: Links) -> io::Result<File> {
    open_flagged(path, links, true)
}

fn open_flagged(path: &std::path::Path, links: Links, write: bool) -> io::Result<File> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        let Some((nonblock, nofollow)) = owner::OPEN_FLAGS else {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "astream-sys declares no O_NONBLOCK/O_NOFOLLOW for this target",
            ));
        };
        let flags = match links {
            Links::Follow => nonblock,
            Links::Refuse => nonblock | nofollow,
        };
        std::fs::OpenOptions::new()
            .read(true)
            .write(write)
            .custom_flags(flags)
            .open(path)
    }
    #[cfg(not(unix))]
    {
        let _ = links;
        std::fs::OpenOptions::new()
            .read(true)
            .write(write)
            .open(path)
    }
}

/// Why an open file is not its owner's alone ([`owner_private`],
/// [`owner_private_dir`]). Its `Display` names the clause without a path; a caller
/// leads with the path it opened.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NotPrivate {
    /// It is not the kind of file asked for: what it is instead (`"a FIFO"`, `"a
    /// directory"`, `"a regular file"`, `"a socket"`, `"a device"`, `"a symlink"`, or
    /// `"not a regular file"` for any other type).
    Kind(&'static str),
    /// It is another user's: its owner's uid (the reader's is [`euid`]).
    Owner(u32),
    /// A group or other permission bit is set: its permission bits (`& 0o777`).
    Mode(u32),
    /// An access-list entry allows someone something (macOS, `ACL_EXTENDED_ALLOW`).
    /// macOS checks an extended list before the mode bits, so a 0600 file carrying
    /// an `everyone allow read` entry (one a parent's `file_inherit` entry passed
    /// on, say) is open to every user.
    Acl,
}

impl core::fmt::Display for NotPrivate {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            NotPrivate::Kind(what) => write!(f, "is {what}"),
            NotPrivate::Owner(uid) => write!(f, "is owned by uid {uid}, not this user"),
            NotPrivate::Mode(mode) => write!(f, "is mode {mode:04o}"),
            NotPrivate::Acl => f.write_str("carries an access list (ACL) that lets other users in"),
        }
    }
}

/// The word [`NotPrivate::Kind`] names a file type by, off Unix (on Unix the owner
/// rule's `kind_word` names it from `st_mode`).
#[cfg(not(unix))]
fn kind_of(file_type: std::fs::FileType) -> &'static str {
    if file_type.is_dir() {
        "a directory"
    } else if file_type.is_file() {
        "a regular file"
    } else if file_type.is_symlink() {
        "a symlink"
    } else {
        "not a regular file"
    }
}

/// `file` held to the owner-only rule, read off the descriptor (`fstat`, and on
/// macOS `fstatx_np`'s filesec), never by path: a REGULAR file, owned by this process's
/// effective uid ([`euid`]), carrying no access-list entry that allows anyone anything
/// (macOS; a deny entry takes nothing away and passes), and with no group or other
/// permission bit. The clauses are judged in that order, and the first one broken is
/// the answer: [`NotPrivate::Mode`], the one clause a `chmod` of the mode closes, comes
/// last, so a caller that narrows a mode it was given knows every other clause held.
/// Off Unix only the kind is judged: there are no mode bits.
///
/// The outer `Err` is an OS error that left the file unjudged (the `fstat`, or an
/// access list that could not be read); `Ok(Err(..))` is the clause it breaks;
/// `Ok(Ok(meta))` passes, with the descriptor's metadata, so a caller adds its own
/// clauses (a link count, a length) without a second `fstat`.
///
/// # Errors
///
/// As above.
pub fn owner_private(file: &File) -> io::Result<Result<std::fs::Metadata, NotPrivate>> {
    owner_only(file, false)
}

/// [`owner_private`] for a DIRECTORY (opened as [`open_nonblocking`] opens one): the
/// same clauses, with a directory the kind asked for. A directory that holds a
/// secret bounds who may replace it, or put another name for it beside it.
///
/// # Errors
///
/// As [`owner_private`].
pub fn owner_private_dir(dir: &File) -> io::Result<Result<std::fs::Metadata, NotPrivate>> {
    owner_only(dir, true)
}

/// The descriptor entry: one `fstat` and the kind and owner clauses over it; only once
/// both held, the access list (`acl_allows`, read after `kind_and_owner` made the `Owned`
/// that `list_and_mode` needs) and then the mode.
fn owner_only(file: &File, dir: bool) -> io::Result<Result<std::fs::Metadata, NotPrivate>> {
    let meta = file.metadata()?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        let seen = owner_rule::Seen {
            st_mode: meta.mode(),
            uid: meta.uid(),
        };
        let owned = match owner_rule::kind_and_owner(seen, dir, owner::euid()) {
            Ok(owned) => owned,
            Err(broken) => return Ok(Err(broken)),
        };
        let allows = owner::acl_allows(file)?;
        match owned.list_and_mode(allows) {
            Ok(()) => Ok(Ok(meta)),
            Err(broken) => Ok(Err(broken)),
        }
    }
    #[cfg(not(unix))]
    {
        let file_type = meta.file_type();
        let kind_ok = if dir {
            file_type.is_dir()
        } else {
            file_type.is_file()
        };
        if !kind_ok {
            return Ok(Err(NotPrivate::Kind(kind_of(file_type))));
        }
        Ok(Ok(meta))
    }
}

/// The kind and owner clauses of [`owner_private`] and [`owner_private_dir`] (a regular
/// file, or a directory when `dir`; then owned by [`euid`]) over metadata a caller read
/// itself, in that order: the first one broken, or `Ok(())` when both hold, which says
/// nothing of the access list or the mode. For a caller that judges an object it could
/// not open, from its `symlink_metadata` (aterm-uds, where a directory's open is refused),
/// so it holds no kind or owner comparison of its own. A symlink's metadata is
/// `Kind("a symlink")`.
#[cfg(unix)]
pub fn kind_and_owner_of(meta: &std::fs::Metadata, dir: bool) -> Result<(), NotPrivate> {
    use std::os::unix::fs::MetadataExt as _;
    let seen = owner_rule::Seen {
        st_mode: meta.mode(),
        uid: meta.uid(),
    };
    match owner_rule::kind_and_owner(seen, dir, owner::euid()) {
        Ok(_owned) => Ok(()),
        Err(broken) => Err(broken),
    }
}

/// What [`owner_private_dir_by_path`] read of a path, without opening it.
#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DirByPath {
    /// The lookup found nothing (`ENOENT`, at the last component or on the way), where
    /// `open_nonblocking` fails `NotFound`.
    Missing,
    /// A symbolic link at the last component, which [`Links::Refuse`] refuses (`ELOOP`).
    Symlink,
    /// [`owner_private_dir`]'s verdict, given only for an object that carries no access
    /// list. `Err(Kind)` and `Err(Owner)` belong to the object and are given whatever an
    /// open would do. `Ok(())` and `Err(Mode)` are given only for this user's directory
    /// whose owner read and search bits are set: there the read open is authorized from
    /// exactly these attributes, so this is the verdict `owner_private_dir` gives on the
    /// descriptor `open_nonblocking(path, Links::Refuse)` opens, but for refusals only that
    /// open meets. The open needs only the read bit; the search bit is asked for because
    /// devfs's `/dev/fd/N` node of a held directory, whose open dups the held descriptor,
    /// shows every search bit clear ([`PathUndecided::NoOwnerRead`]), so no such node is
    /// judged by its own mode. Never `Err(Acl)`: a list sends the path to the open.
    Judged(Result<(), NotPrivate>),
    /// The attributes cannot stand for the opened verdict: open the path and judge the
    /// descriptor.
    Undecided(PathUndecided),
}

/// Why [`owner_private_dir_by_path`] left a path to the open.
#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PathUndecided {
    /// No path entry on this target (only macOS on arm64 has one).
    Unsupported,
    /// The lookup or the stat failed other than `ENOENT` (`ENOTDIR`, `EACCES`, `ELOOP`,
    /// `ENAMETOOLONG`, a refused READ_SECURITY or MAC stat), or the path holds a NUL.
    Lookup,
    /// Libc's answer is incomplete: `filesec_init` failed, statx1's first malloc failed
    /// (it returns 12), its realloc failed (0 with the owner and mode unset), or the list
    /// query refused.
    Unread,
    /// The object carries an extended access list.
    Listed,
    /// This user's directory without its owner read or search bit (devfs's `/dev/fd/N`
    /// node of a held directory clears every search bit and opens the held directory, a
    /// dup: XNU bsd/miscfs/devfs/devfs_fdesc_support.c:453-463, 497-505).
    NoOwnerRead,
}

/// [`owner_private_dir`]'s verdict on `path` where the path's attributes decide it, from
/// one `lstatx_np` of the path (one lookup that does not follow a link at its last
/// component, unless the path ends in a slash, where the lookup follows it as the read
/// open does too, and one `vnode_getattr`; statx1 repeats the pair, keeping the last
/// reading, while the access list outgrows its buffer, first sized for 16 entries, Libc
/// sys/statx_np.c:34, 168-189: twice for a list of more than 16 entries that does not
/// change, which is [`PathUndecided::Listed`] and goes to the open), never an open: the
/// owner, the mode and whether an access list is held, read through the filesec (no
/// `struct stat` field is read), and judged by the same clauses as the descriptor. The
/// only readings it decides from are the lookup's `ENOENT` ([`DirByPath::Missing`]) and
/// a complete stat of an object that carries no access list; everything else is
/// [`DirByPath::Undecided`], for the caller to open the path and judge the descriptor.
/// macOS arm64 only; elsewhere every path is `Undecided(Unsupported)`, with no call.
#[cfg(unix)]
#[must_use]
pub fn owner_private_dir_by_path(path: &std::path::Path) -> DirByPath {
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        use std::os::unix::ffi::OsStrExt as _;
        let Ok(named) = std::ffi::CString::new(path.as_os_str().as_bytes()) else {
            return DirByPath::Undecided(PathUndecided::Lookup);
        };
        by_path(
            owner::look(&named, &mut [0; owner::STAT_WORDS]),
            owner::euid(),
        )
    }
    #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
    {
        let _ = path;
        DirByPath::Undecided(PathUndecided::Unsupported)
    }
}

/// `<sys/stat.h>`'s owner read and search bits (SDK sys/_types/_s_ifmt.h:50, 52).
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const S_IRUSR: u32 = 0o400;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const S_IXUSR: u32 = 0o100;

/// The path entry's decision over what one look read. It is pure, so every Libc outcome,
/// reachable or not, is a row of law A4. Decided: `rc` -1 with `ENOENT`, and `rc` 0 with
/// the owner, the mode and a clear list bit; every other reading is `Undecided`.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
fn by_path(looked: Option<owner::Looked>, euid: u32) -> DirByPath {
    let Some(looked) = looked else {
        return DirByPath::Undecided(PathUndecided::Unread);
    };
    if looked.rc == -1 {
        return if looked.errno == Some(owner::ENOENT) {
            DirByPath::Missing
        } else {
            DirByPath::Undecided(PathUndecided::Lookup)
        };
    }
    if looked.rc != 0 {
        return DirByPath::Undecided(PathUndecided::Unread);
    }
    let (Some(uid), Some(mode)) = (looked.uid, looked.mode) else {
        return DirByPath::Undecided(PathUndecided::Unread);
    };
    match looked.listed {
        Some(false) => {}
        Some(true) => return DirByPath::Undecided(PathUndecided::Listed),
        None => return DirByPath::Undecided(PathUndecided::Unread),
    }
    let st_mode = u32::from(mode);
    if st_mode & owner_rule::S_IFMT == owner_rule::S_IFLNK {
        return DirByPath::Symlink;
    }
    let owned = match owner_rule::kind_and_owner(owner_rule::Seen { st_mode, uid }, true, euid) {
        Ok(owned) => owned,
        Err(broken) => return DirByPath::Judged(Err(broken)),
    };
    if st_mode & (S_IRUSR | S_IXUSR) != (S_IRUSR | S_IXUSR) {
        return DirByPath::Undecided(PathUndecided::NoOwnerRead);
    }
    DirByPath::Judged(owned.list_and_mode(false))
}

#[cfg(test)]
mod tests {
    #[test]
    #[cfg(any(unix, windows))]
    fn file_identity_survives_rename_and_distinguishes_replacement() {
        let dir = std::env::temp_dir().join(format!("astream-sys-identity-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("live");
        let held = dir.join("held");
        let hard = dir.join("hard");
        std::fs::write(&path, b"same contents").unwrap();
        let file = std::fs::File::open(&path).unwrap();
        assert!(super::file_matches_path(&file, &path).unwrap());
        std::fs::hard_link(&path, &hard).unwrap();
        assert!(super::file_matches_path(&file, &hard).unwrap());
        #[cfg(unix)]
        {
            let link = dir.join("symbolic");
            std::os::unix::fs::symlink(&path, &link).unwrap();
            assert!(super::file_matches_path(&file, &link).unwrap());
        }
        std::fs::rename(&path, &held).unwrap();
        assert!(super::file_matches_path(&file, &held).unwrap());
        assert!(super::file_matches_path(&file, &path).is_err());
        std::fs::write(&path, b"same contents").unwrap();
        assert!(!super::file_matches_path(&file, &path).unwrap());
        drop(file);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    use super::*;

    const ID: &str = "64C7D12D-5B0E-4F43-9A1C-2E7F00D1A9B3";

    #[test]
    fn a_uuid_parses_in_either_case_with_or_without_its_terminator() {
        let want = [
            0x64, 0xc7, 0xd1, 0x2d, 0x5b, 0x0e, 0x4f, 0x43, 0x9a, 0x1c, 0x2e, 0x7f, 0x00, 0xd1,
            0xa9, 0xb3,
        ];
        assert_eq!(parse_boot_id(ID.as_bytes()), Some(want));
        assert_eq!(parse_boot_id(format!("{ID}\0\0\0").as_bytes()), Some(want));
        assert_eq!(
            parse_boot_id(format!("{}\n", ID.to_lowercase()).as_bytes()),
            Some(want)
        );
        let (hi, lo) = encode_boot_id_u128_be(want);
        assert_eq!(decode_boot_id_u128_be(hi, lo), want);
        assert_eq!(scan_boot_id_words(ID.as_bytes()), Some((hi, lo)));
        assert_eq!(nul_offset(b"abc\0def"), 3);
        assert_eq!(hex_nibble(b'f'), Some(15));

        // The public reading keeps its UTF-8 whitespace contract. The kernel's
        // normal ASCII spelling and bytes beyond its first NUL remain ordinary.
        assert_eq!(
            parse_boot_id(format!(" \t\r\n{ID}\x0b\x0c ").as_bytes()),
            Some(want)
        );
        let mut invalid_prefix = vec![0xff];
        invalid_prefix.extend_from_slice(ID.as_bytes());
        assert_eq!(parse_boot_id(&invalid_prefix), None);
        let mut after_nul = format!("{ID}\0").into_bytes();
        after_nul.extend_from_slice(&[0xff, 0xfe]);
        assert_eq!(parse_boot_id(&after_nul), Some(want));
        let internal = format!("{}\u{a0}{}", &ID[..8], &ID[8..]);
        assert_eq!(parse_boot_id(internal.as_bytes()), None);
        for (left, right) in [
            ("\u{a0}", "\u{2003}"),
            ("\u{85}", "\u{3000}"),
            ("\u{202f}", "\u{205f}"),
            ("\u{2028}", "\u{2029}"),
        ] {
            let framed = format!("{left}{ID}{right}");
            assert_eq!(
                parse_boot_id(framed.as_bytes()),
                Some(want),
                "PUBLIC_BOOT_ID_TRIMS_VALID_UTF8_WHITESPACE: {framed:?}"
            );
        }
    }

    #[test]
    fn anything_but_a_boot_id_is_none() {
        for bad in [
            &b""[..],
            b"\0",
            b"   ",
            b"64C7D12D-5B0E-4F43-9A1C-2E7F00D1A9B", // one digit short
            b"64C7D12D-5B0E-4F43-9A1C-2E7F00D1A9B3A", // one digit long
            b"64C7D12D-5B0E-4F43-9A1C-2E7F00D1A9BZ", // not hex
            b"00000000-0000-0000-0000-000000000000", // the reserved unknown
            b"\xff\xfe",
        ] {
            assert_eq!(parse_boot_id(bad), None, "{bad:?}");
        }
    }

    /// The digits are the id: a hyphen is dropped wherever it falls, so the bare 32 digits
    /// and a misplaced hyphen read as the same boot as the 8-4-4-4-12 form.
    #[test]
    fn a_hyphen_is_dropped_wherever_it_falls() {
        let want = parse_boot_id(ID.as_bytes()).expect("the UUID form");
        let bare: String = ID.chars().filter(|c| *c != '-').collect();
        let misplaced = format!("-{}-{}-", &bare[..1], &bare[1..]);
        for spelled in [
            bare.as_str(),
            misplaced.as_str(),
            "64C7D12D5B0E4F439A1C2E7F00D1A9B3--",
        ] {
            assert_eq!(parse_boot_id(spelled.as_bytes()), Some(want), "{spelled:?}");
        }
    }

    /// The writer is the reader's inverse: the kernel's 8-4-4-4-12 form, in the case asked,
    /// read back as the same 16 bytes; and this host's own reading, written in the case its
    /// kernel spells it, is the text the kernel answers (compared, case and all, with the
    /// kernel's own text where this test can read it without FFI: Linux's `boot_id` file).
    #[test]
    fn the_written_boot_id_reads_back_as_the_same_bytes() {
        let id = parse_boot_id(ID.as_bytes()).expect("the UUID form");
        assert_eq!(boot_id_text(id, false), ID);
        assert_eq!(boot_id_text(id, true), ID.to_lowercase());
        let mut last = id;
        last[15] ^= 1;
        for one in [
            id,
            last,
            [0xFF; 16],
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        ] {
            for lower in [false, true] {
                let text = boot_id_text(one, lower);
                assert_eq!(text.len(), 36, "{text}");
                let hyphens: Vec<usize> = text.match_indices('-').map(|(at, _)| at).collect();
                assert_eq!(hyphens, [8, 13, 18, 23], "{text}");
                let letters_lower = text
                    .bytes()
                    .filter(u8::is_ascii_alphabetic)
                    .all(|b| b.is_ascii_lowercase());
                let letters_upper = text
                    .bytes()
                    .filter(u8::is_ascii_alphabetic)
                    .all(|b| b.is_ascii_uppercase());
                assert!(if lower { letters_lower } else { letters_upper }, "{text}");
                assert_eq!(parse_boot_id(text.as_bytes()), Some(one), "{text}");
            }
        }
        // The reserved all-zero id is written like any other and still reads as no boot.
        assert_eq!(parse_boot_id(boot_id_text([0; 16], false).as_bytes()), None);

        #[cfg(target_os = "linux")]
        if let (Some(live), Ok(kernel)) = (
            boot_session(),
            std::fs::read_to_string("/proc/sys/kernel/random/boot_id"),
        ) {
            assert_eq!(
                boot_id_text(live, KERNEL_SPELLS_BOOT_ID_LOWER),
                kernel.trim()
            );
        }
    }

    /// The live reading, where this host has one: stable within a process (no boot can
    /// come between two calls of one test), and never the reserved all-zero id.
    #[test]
    fn the_live_boot_session_is_stable_within_a_process() {
        let first = boot_session();
        assert_eq!(first, boot_session());
        assert_ne!(first, Some([0u8; 16]));
        #[cfg(any(target_vendor = "apple", target_os = "linux"))]
        assert!(first.is_some(), "this host's kernel names its boot");
    }

    /// The four errnos fcntl(2) answers for a file or device that cannot order its
    /// writes are a refusal on Apple; a real I/O failure, or any error off Apple (where
    /// the barrier is a full flush), is not.
    #[test]
    fn only_the_devices_refusal_reads_as_a_refused_barrier() {
        let refused = [19, 22, 25, 45].map(io::Error::from_raw_os_error);
        let failed = [5, 28].map(io::Error::from_raw_os_error); // EIO, ENOSPC
        for e in &refused {
            assert_eq!(barrier_refused(e), cfg!(target_vendor = "apple"), "{e}");
        }
        for e in &failed {
            assert!(!barrier_refused(e), "{e}");
        }
        assert!(!barrier_refused(&io::Error::other("not an errno")));
    }

    /// A directory that cannot be flushed or opened is unavailable, on every platform by
    /// its kind and on Apple by Darwin's own refusal errnos too (`ENOTSUP` is 45 there, and
    /// `ENODEV` and `ENOTTY` have no kind the rule reads); a real I/O failure never is.
    #[test]
    fn a_refused_or_unopenable_directory_flush_is_unavailable_and_eio_is_not() {
        for kind in [
            io::ErrorKind::Unsupported,
            io::ErrorKind::InvalidInput,
            io::ErrorKind::PermissionDenied,
            io::ErrorKind::NotFound,
        ] {
            assert!(dir_flush_unavailable(&io::Error::from(kind)), "{kind:?}");
        }
        // POSIX errno numbers are not Win32 error codes.
        #[cfg(unix)]
        {
            // EACCES, ENOENT, EINVAL.
            for errno in [13, 2, 22] {
                let e = io::Error::from_raw_os_error(errno);
                assert!(dir_flush_unavailable(&e), "{e}");
            }
            // EIO and ENOSPC are failed flushes.
            for errno in [5, 28] {
                let e = io::Error::from_raw_os_error(errno);
                assert!(!dir_flush_unavailable(&e), "{e}");
            }
        }
        // Darwin's ENOTSUP, EOPNOTSUPP, ENODEV and ENOTTY.
        #[cfg(target_vendor = "apple")]
        for errno in [45, 102, 19, 25] {
            let e = io::Error::from_raw_os_error(errno);
            assert!(dir_flush_unavailable(&e), "{e}");
        }
        assert!(!dir_flush_unavailable(&io::Error::from(
            io::ErrorKind::StorageFull
        )));
        assert!(!dir_flush_unavailable(&io::Error::other("not an errno")));
    }

    /// A file's flush that its volume refuses is refused, on every platform by its kind and
    /// on Apple by Darwin's own refusal errnos too; a real I/O failure never is, and
    /// neither is what only a directory's open answers (`PermissionDenied`, `NotFound`),
    /// which [`dir_flush_unavailable`] adds to it.
    #[test]
    fn a_refused_file_flush_is_its_kinds_and_apples_errnos_and_eio_is_not() {
        for kind in [io::ErrorKind::Unsupported, io::ErrorKind::InvalidInput] {
            assert!(file_flush_refused(&io::Error::from(kind)), "{kind:?}");
        }
        // POSIX errno numbers are not Win32 error codes.
        #[cfg(unix)]
        {
            // EINVAL is a refusal; EIO, ENOSPC, EACCES and ENOENT are not.
            assert!(file_flush_refused(&io::Error::from_raw_os_error(22)));
            for errno in [5, 28, 13, 2] {
                let e = io::Error::from_raw_os_error(errno);
                assert!(!file_flush_refused(&e), "{e}");
            }
        }
        // Darwin's ENOTSUP, EOPNOTSUPP, ENODEV and ENOTTY.
        #[cfg(target_vendor = "apple")]
        for errno in [45, 102, 19, 25] {
            let e = io::Error::from_raw_os_error(errno);
            assert!(file_flush_refused(&e), "{e}");
        }
        for kind in [io::ErrorKind::PermissionDenied, io::ErrorKind::NotFound] {
            assert!(!file_flush_refused(&io::Error::from(kind)), "{kind:?}");
            assert!(dir_flush_unavailable(&io::Error::from(kind)), "{kind:?}");
        }
        assert!(!file_flush_refused(&io::Error::from(
            io::ErrorKind::StorageFull
        )));
        assert!(!file_flush_refused(&io::Error::other("not an errno")));
    }

    /// On Apple a descriptor that is no file on a volume refuses the full flush with an
    /// errno std leaves uncategorized, and the predicate still reads it as a refusal.
    /// NEGATIVE CONTROL for the errno half: the error's kind alone would not.
    #[cfg(target_vendor = "apple")]
    #[test]
    fn apples_refusal_of_a_full_flush_reads_as_unavailable() {
        let null = File::open("/dev/null").unwrap();
        let refused = null.sync_all().expect_err("/dev/null takes no F_FULLFSYNC");
        assert!(file_flush_refused(&refused), "{refused:?}");
        assert!(dir_flush_unavailable(&refused), "{refused:?}");
        assert!(
            !matches!(
                refused.kind(),
                io::ErrorKind::Unsupported
                    | io::ErrorKind::InvalidInput
                    | io::ErrorKind::PermissionDenied
                    | io::ErrorKind::NotFound
            ),
            "CONTROL: the kind alone names this refusal ({refused:?}); the errno half is untested"
        );
    }

    /// Each flush call raises its own kind's count as it begins, whatever it returns. Other
    /// tests of this binary flush meanwhile, so a count only rises by at least what this
    /// test asked for; one that missed a call, or counted it as the other kind, falls short
    /// unless a test running beside it made up the difference.
    #[test]
    fn the_tally_counts_each_flush_call_by_its_kind() {
        let dir = std::env::temp_dir().join(format!("astream-sys-tally-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("tally");
        let mut f = File::create(&path).unwrap();
        std::io::Write::write_all(&mut f, b"counted").unwrap();
        let before = flush_tally();
        let full = full_sync(&f).and_then(|()| full_sync_data(&f));
        let after_full = flush_tally();
        let barrier = barrier_sync(&f);
        let after = flush_tally();
        let _ = std::fs::remove_dir_all(&dir);
        full.unwrap();
        barrier.unwrap();
        assert!(
            after_full.full >= before.full + 2,
            "{before:?} -> {after_full:?}"
        );
        assert!(
            after.barrier > after_full.barrier,
            "{after_full:?} -> {after:?}"
        );
        #[cfg(target_vendor = "apple")]
        {
            // A barrier the device refuses is a call all the same.
            let null = File::open("/dev/null").unwrap();
            let at = flush_tally();
            assert!(barrier_sync(&null).is_err_and(|e| barrier_refused(&e)));
            assert!(flush_tally().barrier > at.barrier);
        }
    }

    /// Each [`plain_fsync`] call raises `plain` by one, whatever descriptor it is handed: a
    /// regular file's `&File` twice, then a directory held as a bare `OwnedFd` and as a
    /// `BorrowedFd` of it (the handle-relative trees aterm flushes). No other test of this
    /// binary calls it, so that count is this test's alone, and a plain flush counted as
    /// `full` or `barrier` instead falls short here. That it raises NO other count cannot
    /// be read in this binary, whose other tests flush concurrently: `tests/flush_tally.rs`,
    /// a binary of one test, checks every kind exactly.
    #[cfg(unix)]
    #[test]
    fn each_plain_fsync_raises_plain_by_one() {
        use std::os::fd::{AsFd as _, OwnedFd};
        let dir = std::env::temp_dir().join(format!("astream-sys-plain-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let mut f = File::create(dir.join("plain")).unwrap();
        std::io::Write::write_all(&mut f, b"handed to the drive").unwrap();
        let folder = OwnedFd::from(File::open(&dir).unwrap());
        let before = flush_tally();
        let flushed = plain_fsync(&f).and_then(|()| plain_fsync(&f));
        let after = flush_tally();
        let entries = plain_fsync(&folder).and_then(|()| plain_fsync(folder.as_fd()));
        let after_dir = flush_tally();
        let _ = std::fs::remove_dir_all(&dir);
        flushed.expect("a regular file takes a plain fsync");
        entries.expect("a directory's descriptor takes a plain fsync");
        assert_eq!(after.plain, before.plain + 2, "{before:?} -> {after:?}");
        assert_eq!(
            after_dir.plain,
            after.plain + 2,
            "{after:?} -> {after_dir:?}"
        );
    }

    /// An interrupted flush is retried and never reported, and the first answer that is
    /// not `EINTR` is the flush's own: success, or another failure returned at once
    /// (`EIO` here). The cordon's `fsync` and `fcntl(F_BARRIERFSYNC)` both retry through
    /// it. NEGATIVE CONTROL: the `EINTR` the kernel answers reads as interrupted, so a
    /// retry that matched another kind would return it here.
    #[test]
    fn an_interrupted_flush_is_retried_and_another_failure_is_returned() {
        let interrupted = || {
            if cfg!(unix) {
                io::Error::from_raw_os_error(4)
            } else {
                io::Error::from(io::ErrorKind::Interrupted)
            }
        };
        assert_eq!(interrupted().kind(), io::ErrorKind::Interrupted);
        let mut calls = 0;
        retried_on_eintr!({
            calls += 1;
            if calls < 3 {
                Err(interrupted())
            } else {
                Ok(())
            }
        })
        .expect("the third call succeeded");
        assert_eq!(calls, 3, "each EINTR is retried");
        let mut calls = 0;
        let failed = retried_on_eintr!({
            calls += 1;
            if calls < 2 {
                Err(interrupted())
            } else {
                Err(io::Error::from_raw_os_error(5))
            }
        });
        assert_eq!(failed.unwrap_err().raw_os_error(), Some(5));
        assert_eq!(calls, 2, "a failure other than EINTR is not retried");
    }

    #[test]
    fn a_barrier_sync_of_a_regular_file_succeeds() {
        let dir = std::env::temp_dir().join(format!("astream-sys-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("barrier");
        let mut f = File::create(&path).unwrap();
        std::io::Write::write_all(&mut f, b"ordered").unwrap();
        let res = barrier_sync(&f);
        let _ = std::fs::remove_dir_all(&dir);
        res.expect("a regular file on the test volume takes a barrier");
    }

    /// A barrier on a DIRECTORY, opened read-only as `File::open` opens one, succeeds
    /// on the test volume: on Apple `F_BARRIERFSYNC` takes a directory descriptor, so
    /// a create, rename or unlink in it can be ordered without a full flush, and the
    /// answer is not one `barrier_refused` would read as the device's refusal (aterm's
    /// `aterm_durable::ordered_dir` relies on both). Elsewhere it is the full flush of
    /// the directory. NEGATIVE CONTROL: `/dev/null`, a descriptor that is no file on a
    /// volume, is refused on Apple, and read as refused there.
    #[cfg(unix)]
    #[test]
    fn a_barrier_sync_of_a_directory_succeeds_and_is_not_refused() {
        let dir = std::env::temp_dir().join(format!("astream-sys-dir-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("entry"), b"named").unwrap();
        let res = File::open(&dir).and_then(|handle| barrier_sync(&handle));
        let _ = std::fs::remove_dir_all(&dir);
        if let Err(e) = res {
            panic!(
                "a directory on the test volume refused or failed the barrier (refused: {}): {e}",
                barrier_refused(&e)
            );
        }
        #[cfg(target_vendor = "apple")]
        {
            let null = File::open("/dev/null").unwrap();
            let control = barrier_sync(&null);
            assert!(
                control.as_ref().is_err_and(barrier_refused),
                "CONTROL: /dev/null takes no barrier: {control:?}"
            );
        }
    }
}

#[cfg(all(test, unix))]
mod owner_tests;
