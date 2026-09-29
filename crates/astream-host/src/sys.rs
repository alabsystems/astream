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

fn last_err() -> io::Error {
    io::Error::last_os_error()
}

/// Serializes fd creation (where CLOEXEC is not atomic) with `fork` in this
/// module. See the module docs.
static FORK_LOCK: Mutex<()> = Mutex::new(());

fn fork_lock() -> MutexGuard<'static, ()> {
    FORK_LOCK.lock().unwrap_or_else(|p| p.into_inner())
}

/// Open a pty pair sized `(cols, rows)`. Returns `(master, slave)` raw fds. Both
/// are close-on-exec; the master is non-blocking (its readers and writers
/// `poll` — see [`read_master`] / [`write_master`]).
pub fn open_pty(cols: u16, rows: u16) -> io::Result<(c_int, c_int)> {
    let (master, slave) = {
        let _g = fork_lock();
        open_pair()?
    };
    let setup = set_nonblocking(master).and_then(|()| set_winsize(master, cols, rows));
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
    let master = unsafe { libc::posix_openpt(libc::O_RDWR | libc::O_NOCTTY | libc::O_CLOEXEC) };
    if master < 0 {
        return Err(last_err());
    }
    // SAFETY: grantpt/unlockpt/ptsname_r act on the valid master fd; `name` is a
    // live buffer of the stated length.
    let slave = unsafe {
        if libc::grantpt(master) < 0 || libc::unlockpt(master) < 0 {
            let e = last_err();
            libc::close(master);
            return Err(e);
        }
        let mut name = [0 as c_char; 128];
        // ptsname_r RETURNS the error number (POSIX); musl does not also set
        // errno, so errno here could be stale.
        let rc = libc::ptsname_r(master, name.as_mut_ptr(), name.len());
        if rc != 0 {
            libc::close(master);
            return Err(io::Error::from_raw_os_error(rc));
        }
        libc::open(
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
    // SAFETY: master/slave are valid out-params; name/termp/winp are NULL
    // (allowed). openpty writes the two fds or returns < 0.
    let rc = unsafe {
        libc::openpty(
            &mut master,
            &mut slave,
            std::ptr::null_mut(),
            std::ptr::null_mut(),
            std::ptr::null_mut(),
        )
    };
    if rc < 0 {
        return Err(last_err());
    }
    if let Err(e) = set_cloexec(master).and_then(|()| set_cloexec(slave)) {
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
    if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } < 0 {
        Err(last_err())
    } else {
        Ok(())
    }
}

/// Put a fd we own into non-blocking mode.
fn set_nonblocking(fd: c_int) -> io::Result<()> {
    // SAFETY: F_GETFL/F_SETFL on a valid fd; return < 0 on error.
    unsafe {
        let flags = libc::fcntl(fd, libc::F_GETFL);
        if flags < 0 {
            return Err(last_err());
        }
        if libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) < 0 {
            return Err(last_err());
        }
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
        if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } < 0 {
            return Err(last_err());
        }
    }
    #[cfg(not(target_os = "linux"))]
    {
        // SAFETY: pipe writes two fds into a live 2-int array or returns < 0.
        if unsafe { libc::pipe(fds.as_mut_ptr()) } < 0 {
            return Err(last_err());
        }
        if let Err(e) = set_cloexec(fds[0]).and_then(|()| set_cloexec(fds[1])) {
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
/// An exec failure is **reported, not hidden**: a close-on-exec status pipe
/// carries the child's `errno` back if `execv` returns (ENOENT, EACCES, ENOEXEC,
/// ...); the child is then reaped and the error returned, so a program that
/// never ran can never be mistaken for one that ran and exited 127.
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
    let nul = |_| io::Error::new(io::ErrorKind::InvalidInput, "NUL byte in argument");
    let c_prog = CString::new(prog).map_err(nul)?;
    let c_args: Vec<CString> = std::iter::once(prog)
        .chain(args.iter().copied())
        .map(|a| CString::new(a).map_err(nul))
        .collect::<io::Result<_>>()?;
    let mut argv: Vec<*const c_char> = c_args.iter().map(|c| c.as_ptr()).collect();
    argv.push(std::ptr::null());
    // SAFETY: an all-zero sigset_t is a valid value; sigemptyset then
    // initializes it properly (done here, pre-fork, so the child only reads it).
    let mut empty_set: libc::sigset_t = unsafe { std::mem::zeroed() };
    // SAFETY: sigemptyset on a live sigset_t.
    unsafe {
        libc::sigemptyset(&mut empty_set);
    }

    let (status_r, pid) = {
        let _g = fork_lock();
        let (status_r, status_w) = cloexec_pipe()?;
        // SAFETY: fork() is a direct syscall. In the child we use only
        // async-signal-safe libc calls and pointers into parent-allocated memory
        // (valid via copy-on-write until execv replaces the image); we never
        // allocate or unwind. The child always terminates via execv or _exit.
        let pid = unsafe { libc::fork() };
        if pid < 0 {
            let e = last_err();
            close(status_r);
            close(status_w);
            return Err(e);
        }
        if pid == 0 {
            unsafe {
                // A real terminal's signal state: default SIGPIPE, nothing masked.
                libc::signal(libc::SIGPIPE, libc::SIG_DFL);
                libc::sigprocmask(libc::SIG_SETMASK, &empty_set, std::ptr::null_mut());
                libc::setsid();
                // A host that closed one of its own stdio fds gets that slot back
                // for its next fd, so the master, the slave or the status pipe may
                // sit in 0..=2. Move the two the child keeps above 2 and drop the
                // master first, so the dup2s below cannot clobber them — and never
                // run as dup2(fd, fd), which would leave close-on-exec set.
                let status_w = above_stdio(status_w);
                let slave = above_stdio(slave);
                libc::close(master);
                if slave >= 0 {
                    libc::ioctl(slave, libc::TIOCSCTTY as _, 0);
                    libc::dup2(slave, 0);
                    libc::dup2(slave, 1);
                    libc::dup2(slave, 2);
                    libc::close(slave);
                    // status_r/status_w are CLOEXEC: on success they vanish here
                    // and the parent's read sees EOF.
                    libc::execv(c_prog.as_ptr(), argv.as_ptr());
                }
                // Only reached if exec (or moving the slave) failed: report errno
                // through the pipe.
                let errno = last_err().raw_os_error().unwrap_or(0).to_ne_bytes();
                loop {
                    let n = libc::write(status_w, errno.as_ptr() as *const _, errno.len());
                    if n >= 0 || last_err().raw_os_error() != Some(libc::EINTR) {
                        break;
                    }
                }
                libc::_exit(127)
            }
        }
        // Parent: drop the write end so the read below sees EOF once the child
        // execs (or reports). Outside the lock from here on.
        close(status_w);
        (status_r, pid)
    };
    let outcome = read_exec_status(status_r);
    close(status_r);
    match outcome {
        Ok(None) => Ok(pid),
        Ok(Some(errno)) => {
            let _ = reap(pid);
            Err(io::Error::from_raw_os_error(errno))
        }
        Err(e) => {
            let _ = reap(pid);
            Err(e)
        }
    }
}

/// `fd` itself if it is above the stdio range, else a close-on-exec duplicate at
/// the lowest free fd >= 3 (-1 if none). One `fcntl`: async-signal-safe, for the
/// post-`fork` child.
fn above_stdio(fd: c_int) -> c_int {
    if fd > 2 {
        return fd;
    }
    // SAFETY: F_DUPFD_CLOEXEC on a fd this process owns; returns a new fd or -1.
    unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3) }
}

/// Read the exec-status pipe: `Ok(None)` = EOF with nothing written (exec
/// succeeded), `Ok(Some(errno))` = the child reported an exec failure.
fn read_exec_status(fd: c_int) -> io::Result<Option<i32>> {
    let mut buf = [0u8; 4];
    let mut got = 0usize;
    while got < buf.len() {
        // SAFETY: read into the live remainder of `buf` on a valid fd.
        let n = unsafe { libc::read(fd, buf[got..].as_mut_ptr() as *mut _, buf.len() - got) };
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
        got += n as usize;
    }
    match got {
        0 => Ok(None),
        4 => Ok(Some(i32::from_ne_bytes(buf))),
        _ => Err(io::Error::other("short read on the exec-status pipe")),
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
        // SAFETY: poll on one live pollfd.
        let rc = unsafe { libc::poll(&mut pfd, 1, -1) };
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
        let n = unsafe { libc::read(master, buf.as_mut_ptr() as *mut _, buf.len()) };
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
        let n = unsafe { libc::write(master, bytes.as_ptr() as *const _, bytes.len()) };
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
    unsafe {
        libc::kill(pid, sig);
    }
}

/// Set the terminal window size on the master.
pub fn set_winsize(master: c_int, cols: u16, rows: u16) -> io::Result<()> {
    let ws = libc::winsize {
        ws_row: rows,
        ws_col: cols,
        ws_xpixel: 0,
        ws_ypixel: 0,
    };
    // SAFETY: TIOCSWINSZ reads a live winsize through a valid fd.
    let rc = unsafe { libc::ioctl(master, libc::TIOCSWINSZ as _, &ws) };
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
        // SAFETY: waitpid writes status for a child we own.
        let rc = unsafe { libc::waitpid(pid, &mut status, 0) };
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
            return Ok(128 + libc::WTERMSIG(status));
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
    unsafe {
        libc::close(fd);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
