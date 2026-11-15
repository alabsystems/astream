//! The PTY `unsafe` module: thin libc wrappers for the pseudo-terminal syscalls.
//!
//! This is one of the **two** cordoned files in the astream workspace that contain
//! `unsafe` — this one (`cfg(unix)`, the PTY host) and `foreign` (`cfg(linux)`,
//! the ptrace tracer). Every function here returns [`io::Result`], so no errno and
//! no raw pointer escapes into safe code. A reviewer auditing the PTY OS surface
//! reads exactly this file: `posix_openpt`/`grantpt`/`unlockpt`/`ptsname_r`/`open`
//! (Linux) or `openpty` (other Unix), `fcntl(FD_CLOEXEC | O_NONBLOCK |
//! F_DUPFD_CLOEXEC)`,
//! `pipe2`/`pipe`, `fork`, `signal`, `sigprocmask`, `setsid`, `ioctl(TIOCSCTTY)`,
//! `dup2`, `execv`, `read`, `write`, `poll`, `ioctl(TIOCSWINSZ)`, `kill`,
//! `waitpid`, `close`.
//!
//! ## Close-on-exec and the fork window
//!
//! Every fd this module creates is close-on-exec, so a child we `fork`+`exec`
//! inherits only the three stdio fds it `dup2`s. On Linux the flag is set
//! **atomically** at creation (`O_CLOEXEC` on `posix_openpt`/`open`, `pipe2`).
//! `openpty(3)` and `pipe(2)` on other Unixes have no atomic form, so there the
//! flag is added by a second `fcntl` call, and a process-wide lock serializes
//! every fd creation in this module with every `fork` in this module — so two
//! threads spawning PTYs concurrently cannot leak one PTY into the other's child.
//! **Residual (non-Linux only):** a `fork`+`exec` performed by code *outside* this
//! module (e.g. `std::process::Command`) on another thread during that few-µs
//! window can still inherit a not-yet-CLOEXEC fd; the same window exists in
//! `std::process` itself on those platforms.

#![cfg(unix)]

use std::ffi::CString;
use std::io;
use std::os::raw::{c_char, c_int};
use std::sync::{Mutex, MutexGuard};

#[cfg(clean_islands)]
#[path = "sys_island.rs"]
mod sys_island;
#[cfg(not(clean_islands))]
pub use crate::twins::sys_stdio_fd_floor;
#[cfg(clean_islands)]
pub use sys_island::sys_stdio_fd_floor;

contract_fn! {
    /// Verified check that the exec-status pipe read a complete 4-byte `errno` word (`got == 4`),
    /// linked via `clean-kernel-defeq` to `sys_exec_status_complete_isl`.
    #[must_use]
    pub const fn sys_exec_status_complete(got: usize) -> bool
    clauses [ensures result == (got == 4)]
    {
        got == 4
    }
}

/// Encode a 32-bit `errno` status word in little-endian byte order.
#[must_use]
pub const fn encode_exec_errno_le(errno: i32) -> [u8; 4] {
    let u = errno as u32;
    [
        (u & 0xFF) as u8,
        ((u >> 8) & 0xFF) as u8,
        ((u >> 16) & 0xFF) as u8,
        ((u >> 24) & 0xFF) as u8,
    ]
}

/// Decode a 32-bit `errno` status word from little-endian byte order.
#[must_use]
pub const fn decode_exec_errno_le(bytes: &[u8; 4]) -> i32 {
    let u = (bytes[0] as u32)
        | ((bytes[1] as u32) << 8)
        | ((bytes[2] as u32) << 16)
        | ((bytes[3] as u32) << 24);
    u as i32
}

/// Encode an 8-byte terminal `winsize` tuple `(rows, cols, xpixel, ypixel)` in little-endian byte order.
#[must_use]
pub const fn encode_winsize_le(rows: u16, cols: u16, xpixel: u16, ypixel: u16) -> [u8; 8] {
    [
        (rows & 0xFF) as u8,
        ((rows >> 8) & 0xFF) as u8,
        (cols & 0xFF) as u8,
        ((cols >> 8) & 0xFF) as u8,
        (xpixel & 0xFF) as u8,
        ((xpixel >> 8) & 0xFF) as u8,
        (ypixel & 0xFF) as u8,
        ((ypixel >> 8) & 0xFF) as u8,
    ]
}

/// Decode an 8-byte terminal `winsize` tuple `(rows, cols, xpixel, ypixel)` from little-endian byte order.
#[must_use]
pub const fn decode_winsize_le(bytes: &[u8; 8]) -> (u16, u16, u16, u16) {
    let rows = (bytes[0] as u16) | ((bytes[1] as u16) << 8);
    let cols = (bytes[2] as u16) | ((bytes[3] as u16) << 8);
    let xpixel = (bytes[4] as u16) | ((bytes[5] as u16) << 8);
    let ypixel = (bytes[6] as u16) | ((bytes[7] as u16) << 8);
    (rows, cols, xpixel, ypixel)
}

fn last_err() -> io::Error {
    io::Error::last_os_error()
}

/// Serializes fd creation (where CLOEXEC is not atomic) with `fork` in this
/// module. See the module docs.
static FORK_LOCK: Mutex<()> = Mutex::new(());

fn fork_lock() -> MutexGuard<'static, ()> {
    match FORK_LOCK.lock() {
        Ok(g) => g,
        Err(p) => p.into_inner(),
    }
}

/// Open a pty pair sized `(cols, rows)`. Returns `(master, slave)` raw fds. Both
/// are close-on-exec; the master is non-blocking (its readers and writers
/// `poll` — see [`read_master`] / [`write_master`]).
pub fn open_pty(cols: u16, rows: u16) -> io::Result<(c_int, c_int)> {
    let (master, slave) = {
        let _g = fork_lock();
        open_pair()?
    };
    let setup = match set_nonblocking(master) {
        Ok(()) => set_winsize(master, cols, rows),
        Err(e) => Err(e),
    };
    if let Err(e) = setup {
        close(master);
        close(slave);
        return Err(e);
    }
    Ok((master, slave))
}

/// Linux: allocate the pair with `O_CLOEXEC` set atomically at creation.
#[cfg(target_os = "linux")]
fn open_pair() -> io::Result<(c_int, c_int)> {
    // SAFETY: posix_openpt takes only flags; returns a new fd or < 0.
    let master = sys_ffi!(
        libc::posix_openpt,
        libc::O_RDWR | libc::O_NOCTTY | libc::O_CLOEXEC
    );
    if master < 0 {
        return Err(last_err());
    }
    // SAFETY: grantpt/unlockpt/ptsname_r act on the valid master fd; `name` is a
    // live buffer of the stated length.
    let slave = {
        if sys_ffi!(libc::grantpt, master) < 0 || sys_ffi!(libc::unlockpt, master) < 0 {
            let e = last_err();
            sys_ffi!(libc::close, master);
            return Err(e);
        }
        let mut name = [0 as c_char; 128];
        // ptsname_r RETURNS the error number (POSIX); musl does not also set
        // errno, so errno here could be stale.
        let rc = sys_ffi!(libc::ptsname_r, master, name.as_mut_ptr(), name.len());
        if rc != 0 {
            sys_ffi!(libc::close, master);
            return Err(io::Error::from_raw_os_error(rc));
        }
        sys_ffi!(
            libc::open,
            name.as_ptr(),
            libc::O_RDWR | libc::O_NOCTTY | libc::O_CLOEXEC,
        )
    };
    if slave < 0 {
        let e = last_err();
        close(master);
        return Err(e);
    }
    Ok((master, slave))
}

/// Other Unix (macOS, BSDs): `openpty` has no CLOEXEC form, so the flag is added
/// afterwards — under the fork lock, see the module docs.
#[cfg(not(target_os = "linux"))]
fn open_pair() -> io::Result<(c_int, c_int)> {
    let mut master: c_int = -1;
    let mut slave: c_int = -1;
    let master_ptr = std::slice::from_mut(&mut master).as_mut_ptr();
    let slave_ptr = std::slice::from_mut(&mut slave).as_mut_ptr();
    // SAFETY: master/slave are valid out-params; name/termp/winp are NULL
    // (allowed). openpty writes the two fds or returns < 0.
    let rc = sys_ffi!(
        libc::openpty,
        master_ptr,
        slave_ptr,
        std::ptr::null_mut(),
        std::ptr::null_mut(),
        std::ptr::null_mut(),
    );
    if rc < 0 {
        return Err(last_err());
    }
    let cloexec_res = match set_cloexec(master) {
        Ok(()) => set_cloexec(slave),
        Err(e) => Err(e),
    };
    if let Err(e) = cloexec_res {
        close(master);
        close(slave);
        return Err(e);
    }
    Ok((master, slave))
}

/// Set the close-on-exec flag on a fd we own (non-Linux: no atomic form exists).
#[cfg(not(target_os = "linux"))]
fn set_cloexec(fd: c_int) -> io::Result<()> {
    // SAFETY: F_SETFD/FD_CLOEXEC on a valid fd; returns < 0 on error.
    if sys_ffi!(libc::fcntl, fd, libc::F_SETFD, libc::FD_CLOEXEC) < 0 {
        Err(last_err())
    } else {
        Ok(())
    }
}

/// Put a fd we own into non-blocking mode.
fn set_nonblocking(fd: c_int) -> io::Result<()> {
    // SAFETY: F_GETFL/F_SETFL on a valid fd; return < 0 on error.
    let flags = sys_ffi!(libc::fcntl, fd, libc::F_GETFL);
    if flags < 0 {
        return Err(last_err());
    }
    if sys_ffi!(libc::fcntl, fd, libc::F_SETFL, flags | libc::O_NONBLOCK) < 0 {
        return Err(last_err());
    }
    Ok(())
}

/// A close-on-exec pipe `(read, write)`. Atomic on Linux (`pipe2`); elsewhere the
/// flag is added afterwards, which is why callers hold the fork lock.
fn cloexec_pipe() -> io::Result<(c_int, c_int)> {
    let mut fds: [c_int; 2] = [-1, -1];
    #[cfg(target_os = "linux")]
    {
        // SAFETY: pipe2 writes two fds into a live 2-int array or returns < 0.
        if sys_ffi!(libc::pipe2, fds.as_mut_ptr(), libc::O_CLOEXEC) < 0 {
            return Err(last_err());
        }
    }
    #[cfg(not(target_os = "linux"))]
    {
        // SAFETY: pipe writes two fds into a live 2-int array or returns < 0.
        if sys_ffi!(libc::pipe, fds.as_mut_ptr()) < 0 {
            return Err(last_err());
        }
        let cloexec_res = match set_cloexec(fds[0]) {
            Ok(()) => set_cloexec(fds[1]),
            Err(e) => Err(e),
        };
        if let Err(e) = cloexec_res {
            close(fds[0]);
            close(fds[1]);
            return Err(e);
        }
    }
    Ok((fds[0], fds[1]))
}

/// Fork and exec `prog` (argv\[0\] = `prog`, then `args`) with `slave` as its
/// controlling terminal and stdio. Returns the child pid in the parent.
///
/// **Consumes `slave`:** it is closed in the parent on every return path (the
/// child keeps its own copy as fds 0/1/2), so the caller must not close it again.
///
/// A setup or exec failure is **reported, not hidden**: a close-on-exec status
/// pipe carries the first failed child syscall's `errno` back, including if
/// `execv` returns (ENOENT, EACCES, ENOEXEC, ...). The child is then reaped and
/// the error returned, so a program that never ran can never be mistaken for
/// one that ran and exited 127.
///
/// The child gets a real terminal's signal state before exec: `SIGPIPE` back to
/// `SIG_DFL` (the Rust runtime sets it to `SIG_IGN` in this process, and an
/// ignored disposition survives exec) and an empty signal mask — mirroring what
/// `std::process::Command` does, so pipelines in the child behave as under a tty.
///
/// All allocation happens in the parent **before** `fork`; the child path is
/// async-signal-safe and allocation-free, ending in `execv` or `_exit(127)`.
///
/// `prog` must be a path (contain `/`): we use `execv`, which does **not** search
/// `$PATH`, so the child path makes no `getenv`/`malloc` call — keeping the
/// post-`fork` window genuinely async-signal-safe even from a multithreaded
/// parent. A bare command name is rejected up front.
pub fn spawn_child(
    slave: c_int,
    master: c_int,
    prog: &str,
    args: &[&str],
) -> io::Result<libc::pid_t> {
    let r = spawn_child_inner(slave, master, prog, args);
    // Parent: the slave belongs to the child now (or the spawn failed) — either
    // way this process must not keep it open, or the master would never see EOF.
    close(slave);
    r
}

fn spawn_child_inner(
    slave: c_int,
    master: c_int,
    prog: &str,
    args: &[&str],
) -> io::Result<libc::pid_t> {
    if !prog.contains('/') {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "prog must be a path containing '/' (execv does not search $PATH)",
        ));
    }
    let c_prog = match CString::new(prog) {
        Ok(c) => c,
        Err(_) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "NUL byte in argument",
            ))
        }
    };
    let mut c_args: Vec<CString> = Vec::new();
    c_args.push(c_prog.clone());
    let mut arg_idx = 0usize;
    while arg_idx < args.len() {
        let Some(a) = args.get(arg_idx) else {
            break;
        };
        match CString::new(*a) {
            Ok(c) => c_args.push(c),
            Err(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "NUL byte in argument",
                ))
            }
        }
        arg_idx = arg_idx.saturating_add(1);
    }
    let mut argv: Vec<*const c_char> = Vec::new();
    let mut c_idx = 0usize;
    while c_idx < c_args.len() {
        let Some(c) = c_args.get(c_idx) else {
            break;
        };
        argv.push(c.as_ptr());
        c_idx = c_idx.saturating_add(1);
    }
    argv.push(std::ptr::null());
    // SAFETY: an all-zero sigset_t is a valid value; sigemptyset then
    // initializes it properly (done here, pre-fork, so the child only reads it).
    let mut empty_set: libc::sigset_t = sys_ffi!(std::mem::zeroed,);
    let empty_set_mut = std::slice::from_mut(&mut empty_set).as_mut_ptr();
    // SAFETY: sigemptyset on a live sigset_t.
    if sys_ffi!(libc::sigemptyset, empty_set_mut) < 0 {
        return Err(last_err());
    }
    let empty_set_ptr = std::slice::from_ref(&empty_set).as_ptr();

    let (status_r, pid) = {
        let _g = fork_lock();
        let (status_r, status_w) = cloexec_pipe()?;
        // SAFETY: fork() is a direct syscall. In the child we use only
        // async-signal-safe libc calls and pointers into parent-allocated memory
        // (valid via copy-on-write until execv replaces the image); we never
        // allocate or unwind. The child always terminates via execv or _exit.
        let pid = sys_ffi!(libc::fork,);
        if pid < 0 {
            let e = last_err();
            close(status_r);
            close(status_w);
            return Err(e);
        }
        if pid == 0 {
            // A host that closed one of its own stdio fds can allocate the
            // master, slave or status pipe in 0..=2. Preserve the status pipe
            // first: if duplication fails, its original fd can still report
            // that failure before any stdio slot is changed.
            let mut report_fd = status_w;
            let raw_errno = 'failed: {
                let moved_status = above_stdio(report_fd);
                if moved_status < 0 {
                    break 'failed child_errno();
                }
                report_fd = moved_status;
                let slave = above_stdio(slave);
                if slave < 0 {
                    break 'failed child_errno();
                }

                // Every required setup operation must succeed before exec.
                // Capture the first errno immediately; later cleanup or setup
                // must not replace it with a different failure.
                if sys_ffi!(libc::signal, libc::SIGPIPE, libc::SIG_DFL) == libc::SIG_ERR {
                    break 'failed child_errno();
                }
                if sys_ffi!(
                    libc::sigprocmask,
                    libc::SIG_SETMASK,
                    empty_set_ptr,
                    std::ptr::null_mut(),
                ) < 0
                {
                    break 'failed child_errno();
                }
                if sys_ffi!(libc::setsid,) < 0 {
                    break 'failed child_errno();
                }
                // Drop the master before dup2 can reuse its stdio slot. Do
                // not retry close after EINTR: the fd's state is unspecified.
                if sys_ffi!(libc::close, master) < 0 {
                    break 'failed child_errno();
                }
                if sys_ffi!(libc::ioctl, slave, libc::TIOCSCTTY as _, 0) < 0 {
                    break 'failed child_errno();
                }
                if sys_ffi!(libc::dup2, slave, 0) < 0 {
                    break 'failed child_errno();
                }
                if sys_ffi!(libc::dup2, slave, 1) < 0 {
                    break 'failed child_errno();
                }
                if sys_ffi!(libc::dup2, slave, 2) < 0 {
                    break 'failed child_errno();
                }
                if sys_ffi!(libc::close, slave) < 0 {
                    break 'failed child_errno();
                }
                // The status fds are CLOEXEC: only successful exec closes the
                // write end without an errno, so the parent then reads EOF.
                sys_ffi!(libc::execv, c_prog.as_ptr(), argv.as_ptr());
                child_errno()
            };
            let errno = encode_exec_errno_le(raw_errno);
            loop {
                let n = sys_ffi!(
                    libc::write,
                    report_fd,
                    errno.as_ptr() as *const _,
                    errno.len()
                );
                if n >= 0 || last_err().raw_os_error() != Some(libc::EINTR) {
                    break;
                }
            }
            extern "C" {
                #[link_name = "_exit"]
                fn posix_exit(status: c_int);
            }
            sys_ffi!(posix_exit, 127);
            return Err(io::Error::from_raw_os_error(raw_errno));
        }
        // Parent: drop the write end so the read below sees EOF once the child
        // execs (or reports). Outside the lock from here on.
        close(status_w);
        (status_r, pid)
    };
    let outcome = read_exec_status(status_r);
    close(status_r);
    let opt = match outcome {
        Ok(opt) => opt,
        Err(e) => {
            let _ = reap(pid);
            return Err(e);
        }
    };
    match opt {
        None => Ok(pid),
        Some(errno) => {
            let _ = reap(pid);
            Err(io::Error::from_raw_os_error(errno))
        }
    }
}

/// Capture a failed child syscall's errno before any other syscall runs. This
/// uses the same allocation-free OS-error representation as the exec path.
fn child_errno() -> c_int {
    last_err().raw_os_error().unwrap_or(libc::EIO)
}

/// `fd` itself if it is above the stdio range, else a close-on-exec duplicate at
/// the lowest free fd >= 3 (-1 if none). One `fcntl`: async-signal-safe, for the
/// post-`fork` child.
fn above_stdio(fd: c_int) -> c_int {
    if fd >= 0 && sys_stdio_fd_floor(3, fd as u64) > 3 || fd == 3 {
        return fd;
    }
    // SAFETY: F_DUPFD_CLOEXEC on a fd this process owns; returns a new fd or -1.
    sys_ffi!(libc::fcntl, fd, libc::F_DUPFD_CLOEXEC, 3)
}

/// Read the exec-status pipe: `Ok(None)` = EOF with nothing written (exec
/// succeeded), `Ok(Some(errno))` = the child reported an exec failure.
fn read_exec_status(fd: c_int) -> io::Result<Option<i32>> {
    let mut buf = [0u8; 4];
    let mut got = 0usize;
    while got < buf.len() {
        let Some(rem) = buf.get_mut(got..) else {
            break;
        };
        // SAFETY: read into the live remainder of `buf` on a valid fd.
        let n = sys_ffi!(libc::read, fd, rem.as_mut_ptr() as *mut _, rem.len());
        if n < 0 {
            let err = last_err();
            if err.raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            return Err(err);
        }
        if n == 0 {
            break;
        }
        got = got.saturating_add(n as usize);
    }
    if got == 0 {
        Ok(None)
    } else if sys_exec_status_complete(got) {
        Ok(Some(decode_exec_errno_le(&buf)))
    } else {
        Err(io::Error::other("short read on the exec-status pipe"))
    }
}

/// Wait (indefinitely, retrying `EINTR`) until the master is readable and/or (if
/// `want_write`) writable. Returns `(readable, writable)`; hang-up and error
/// conditions count as readable so the caller's `read` observes the end of
/// session.
pub fn wait_master(master: c_int, want_write: bool) -> io::Result<(bool, bool)> {
    let mut events = libc::POLLIN;
    if want_write {
        events |= libc::POLLOUT;
    }
    let mut pfd = libc::pollfd {
        fd: master,
        events,
        revents: 0,
    };
    loop {
        let pfd_ptr = std::slice::from_mut(&mut pfd).as_mut_ptr();
        // SAFETY: poll on one live pollfd.
        let rc = sys_ffi!(libc::poll, pfd_ptr, 1, -1);
        if rc >= 0 {
            break;
        }
        let err = last_err();
        if err.raw_os_error() != Some(libc::EINTR) {
            return Err(err);
        }
    }
    let r = pfd.revents;
    if r & libc::POLLNVAL != 0 {
        return Err(io::Error::other("poll rejected the pty master (POLLNVAL)"));
    }
    let hup = r & (libc::POLLHUP | libc::POLLERR) != 0;
    Ok((r & libc::POLLIN != 0 || hup, r & libc::POLLOUT != 0 || hup))
}

/// One non-blocking read of master output. `Ok(Some(0))` means end of session:
/// a clean EOF (macOS, after the child closes the slave) **or** `EIO` (Linux
/// delivers it on the master once the last slave fd closes). `Ok(None)` means
/// nothing is available right now. `EINTR` is retried.
pub fn try_read_master(master: c_int, buf: &mut [u8]) -> io::Result<Option<usize>> {
    loop {
        // SAFETY: read into a live buffer of the given length on a valid fd.
        let n = sys_ffi!(libc::read, master, buf.as_mut_ptr() as *mut _, buf.len());
        if n >= 0 {
            return Ok(Some(n as usize));
        }
        let err = last_err();
        match err.raw_os_error() {
            Some(libc::EINTR) => continue,
            Some(libc::EAGAIN) => return Ok(None),
            Some(libc::EIO) => return Ok(Some(0)),
            _ => return Err(err),
        }
    }
}

/// Read one chunk of master output, waiting for it. `Ok(0)` means end of
/// session (see [`try_read_master`]).
pub fn read_master(master: c_int, buf: &mut [u8]) -> io::Result<usize> {
    loop {
        if let Some(n) = try_read_master(master, buf)? {
            return Ok(n);
        }
        wait_master(master, false)?;
    }
}

/// One non-blocking write of input bytes to the master. `EINTR` is retried (like
/// [`read_master`]), so a signal that interrupts the write does not surface as a
/// spurious error; a full kernel input queue surfaces as `ErrorKind::WouldBlock`
/// so the caller can drain output (and [`wait_master`]) instead of deadlocking.
pub fn write_master(master: c_int, bytes: &[u8]) -> io::Result<usize> {
    loop {
        // SAFETY: write from a live buffer on a valid fd.
        let n = sys_ffi!(libc::write, master, bytes.as_ptr() as *const _, bytes.len());
        if n >= 0 {
            return Ok(n as usize);
        }
        let err = last_err();
        if err.raw_os_error() == Some(libc::EINTR) {
            continue;
        }
        return Err(err);
    }
}

/// Send signal `sig` to child `pid` (best-effort). Used by [`Pty`](crate::Pty)'s
/// `Drop` to terminate a still-running child before reaping, so the destructor
/// cannot block forever on a child that ignores `SIGHUP`.
pub fn kill(pid: libc::pid_t, sig: c_int) {
    // SAFETY: kill() on a pid of a child we own; errors are not actionable here.
    sys_ffi!(libc::kill, pid, sig);
}

/// Set the terminal window size on the master.
pub fn set_winsize(master: c_int, cols: u16, rows: u16) -> io::Result<()> {
    let ws = libc::winsize {
        ws_row: rows,
        ws_col: cols,
        ws_xpixel: 0,
        ws_ypixel: 0,
    };
    let ws_ptr = std::slice::from_ref(&ws).as_ptr();
    // SAFETY: TIOCSWINSZ reads a live winsize through a valid fd.
    let rc = sys_ffi!(libc::ioctl, master, libc::TIOCSWINSZ as _, ws_ptr);
    if rc < 0 {
        return Err(last_err());
    }
    Ok(())
}

/// Reap the child `pid`, returning its exit code (or `128 + signal` if killed).
/// `ECHILD` means the pid is no longer ours to wait for (already reaped, or the
/// process auto-reaps with `SIGCHLD=SIG_IGN`) — see [`reap_settles`].
pub fn reap(pid: libc::pid_t) -> io::Result<i32> {
    let mut status: c_int = 0;
    loop {
        let status_ptr = std::slice::from_mut(&mut status).as_mut_ptr();
        // SAFETY: waitpid writes status for a child we own.
        let rc = sys_ffi!(libc::waitpid, pid, status_ptr, 0);
        if rc < 0 {
            let err = last_err();
            if err.raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            return Err(err);
        }
        if libc::WIFEXITED(status) {
            return Ok(libc::WEXITSTATUS(status));
        }
        if libc::WIFSIGNALED(status) {
            return Ok(128i32.saturating_add(libc::WTERMSIG(status)));
        }
        return Ok(-1);
    }
}

/// Whether a [`reap`] outcome means the pid is settled — no longer ours to wait
/// for or signal. `Ok` is settled; so is `ECHILD` (the kernel has no such child
/// of ours: already reaped, or auto-reaped under `SIGCHLD=SIG_IGN`), after which
/// the pid may be recycled and must **never** be signalled again.
pub fn reap_settles(outcome: &io::Result<i32>) -> bool {
    match outcome {
        Ok(_) => true,
        Err(e) => e.raw_os_error() == Some(libc::ECHILD),
    }
}

/// Close a raw fd (best-effort).
pub fn close(fd: c_int) {
    // SAFETY: closing a fd we own; errors are not actionable here.
    sys_ffi!(libc::close, fd);
}

#[cfg(test)]
mod tests {
    use super::*;

    // The low-fd fixture temporarily removes/replaces this process's stdin.
    // Every fd-creating test here holds this lock for its complete lifetime,
    // including child cleanup and stdin restoration. This is not FORK_LOCK:
    // open_pty and spawn_child acquire that production lock themselves.
    static FD_TEST_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn exec_errno_and_winsize_roundtrip() {
        for errno in [libc::ENOENT, libc::EACCES, libc::ENOEXEC, -1] {
            let bytes = encode_exec_errno_le(errno);
            assert_eq!(decode_exec_errno_le(&bytes), errno);
        }
        let ws = encode_winsize_le(24, 80, 800, 600);
        assert_eq!(decode_winsize_le(&ws), (24, 80, 800, 600));
    }

    #[test]
    fn echild_settles_a_reap_but_other_errors_do_not() {
        assert!(reap_settles(&Ok(0)));
        assert!(reap_settles(&Ok(137)));
        assert!(
            reap_settles(&Err(io::Error::from_raw_os_error(libc::ECHILD))),
            "ECHILD: the pid is not ours to wait for, so it must count as settled (never SIGKILL it)"
        );
        assert!(!reap_settles(&Err(io::Error::from_raw_os_error(
            libc::EINVAL
        ))));
        assert!(!reap_settles(&Err(io::Error::from_raw_os_error(
            libc::EAGAIN
        ))));
    }

    #[test]
    fn child_setup_rejects_a_non_terminal_slave_before_exec() {
        let _fd_test = FD_TEST_LOCK.lock().expect("another fd fixture failed");
        // Use a real owned pipe, not an invalid fd: the terminal ioctl is the
        // failing operation. No PTY allocation or global directory is needed.
        let (master, slave) = {
            let _guard = fork_lock();
            cloexec_pipe().expect("allocate the non-terminal fixture")
        };
        let spawned = spawn_child(slave, master, "/bin/sh", &["-c", "exit 23"]);
        // spawn_child consumed the parent's slave and reaped an errored child.
        // A mutant that ignores the ioctl runs the program: reap that child too
        // before any assertion, so the negative control leaves no live child.
        let unexpected_exit = match &spawned {
            Ok(pid) => Some(reap(*pid)),
            Err(_) => None,
        };
        close(master);
        match spawned {
            Err(error) => assert_eq!(
                error.raw_os_error(),
                Some(libc::ENOTTY),
                "the child's non-terminal setup errno is reported: {error}"
            ),
            Ok(pid) => panic!(
                "a child with no controlling terminal executed: pid={pid}, exit={unexpected_exit:?}"
            ),
        }
    }

    /// Whether the child `spawn_child` runs has a terminal on stdin, when the
    /// pty fd `which` (the master or the slave) sits on fd 0 -- where the kernel
    /// puts it for a host that closed its own stdin. Swaps this test process's
    /// fd 0 for the duration (the harness never reads stdin) and restores it.
    fn child_stdin_is_a_tty_with_fd0_as(which: &str) -> String {
        const PROBE: &str = "if [ -t 0 ]; then echo STDIN-TTY; else echo STDIN-GONE; fi";
        // SAFETY: dup/dup2/fcntl on fds this test owns; fd 0 is restored below.
        let saved = unsafe { libc::dup(0) };
        assert!(saved >= 0);
        let (mut master, mut slave) = open_pty(80, 24).expect("open a pty");
        let moved = if which == "master" { master } else { slave };
        unsafe {
            assert_eq!(libc::dup2(moved, 0), 0);
            // Like the real fd, close-on-exec (dup2 cleared the flag).
            libc::fcntl(0, libc::F_SETFD, libc::FD_CLOEXEC);
        }
        close(moved);
        if which == "master" {
            master = 0;
        } else {
            slave = 0;
        }
        let spawned = spawn_child(slave, master, "/bin/sh", &["-c", PROBE]);
        let mut output = Vec::new();
        if let Ok(pid) = spawned {
            let mut buf = [0u8; 256];
            while let Ok(n) = read_master(master, &mut buf) {
                if n == 0 {
                    break;
                }
                output.extend_from_slice(&buf[..n]);
            }
            let _ = reap(pid);
        }
        if master != 0 {
            close(master);
        }
        // SAFETY: put the harness's stdin back.
        unsafe {
            libc::dup2(saved, 0);
            libc::close(saved);
        }
        spawned.expect("spawn the probe");
        String::from_utf8_lossy(&output).into_owned()
    }

    #[test]
    fn a_pty_fd_in_the_stdio_range_still_gives_the_child_its_terminal() {
        let _fd_test = FD_TEST_LOCK.lock().expect("another fd fixture failed");
        // Master on fd 0: the child's `close(master)` ran after the dup2s and
        // closed the stdin they had just installed.
        let out = child_stdin_is_a_tty_with_fd0_as("master");
        assert!(out.contains("STDIN-TTY"), "master on fd 0: {out:?}");
        // Slave on fd 0: `dup2(0, 0)` is a no-op that leaves close-on-exec set,
        // so exec closed the child's stdin.
        let out = child_stdin_is_a_tty_with_fd0_as("slave");
        assert!(out.contains("STDIN-TTY"), "slave on fd 0: {out:?}");
    }
}
