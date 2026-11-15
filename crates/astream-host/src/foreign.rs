//! The Effects rung, **foreign-process form** (Linux, `ptrace`): record and replay
//! the effects of a child process that does NOT cooperate with the recorder.
//!
//! A forked child (not `exec`'d, so there is no dynamic-linker syscall noise) runs
//! a fixed effect program: it reads one wall clock, eight random bytes, and a file,
//! folding them NON-commutatively into a `u64` digest. It uses the raw `syscall`
//! path so the reads trap (defeating the vDSO). The tracer (parent) drives it via
//! `PTRACE_SYSCALL`:
//!
//! * **record** — tape each intercepted syscall's result into an
//!   [`EffectsLog`](astream_effects::EffectsLog) (the SAME tape the cooperative
//!   Effects rung uses, so the determinism/oracle discipline is shared).
//! * **replay** — OVERWRITE each result with the taped value (return register +
//!   output buffer), so the child is a pure function of the tape; a tape that runs
//!   short, yields the wrong kind, names a different file, or carries a `File`
//!   record longer than the tracee's read buffer ABORTS (fail-closed: a panic,
//!   with the tracee killed and reaped on unwind; the cooperative `ReplaySeam`
//!   refuses the same divergences with a typed `ReplayDivergence` instead).
//!
//! Failures of the *machinery* — `pipe`/`fork`/`waitpid` errors, `PTRACE_TRACEME`
//! denied (Yama `ptrace_scope`, seccomp, container profiles), a failed `ptrace`
//! register access or `process_vm_readv`/`writev`, the tracee dying by a signal —
//! are [`ForeignError`](crate::foreign::ForeignError)s, never a hang and never a
//! silent default.
//!
//! Honest scope: the child is a fork of this binary (a separate, non-cooperating
//! PROCESS, but not a separately-`exec`'d image — that is a trivial extension), and
//! replay drives the process from the tape by overwriting results (the kernel still
//! executes the now-ignored syscall; that injection is load-bearing is proven by a
//! NAIVE replay against a changed world diverging). aarch64 + x86_64 only.
//!
//! All `unsafe` here stays inside the `astream-host` cordon (the crate root denies
//! `unsafe_code`; this `cfg(linux)` module and `sys` are its only two re-permits).

#![cfg(target_os = "linux")]

use astream_effects::{EffectRecord, EffectsLog};
use libc::{c_int, c_long, c_void};
use std::ffi::CString;
use std::io;

pub use astream_effects::EffectRecord as Effect;

// Syscall numbers differ by arch.
#[cfg(target_arch = "aarch64")]
mod nr {
    use std::os::raw::c_long;
    pub const CLOCK_GETTIME: c_long = 113;
    pub const GETRANDOM: c_long = 278;
    pub const OPENAT: c_long = 56;
    pub const READ: c_long = 63;
    pub const CLOSE: c_long = 57;
    pub const GETPID: c_long = 172;
}
#[cfg(target_arch = "x86_64")]
mod nr {
    use std::os::raw::c_long;
    pub const CLOCK_GETTIME: c_long = 228;
    pub const GETRANDOM: c_long = 318;
    pub const OPENAT: c_long = 257;
    pub const READ: c_long = 0;
    pub const CLOSE: c_long = 3;
    pub const GETPID: c_long = 39;
}

/// A syscall stop under `TRACESYSGOOD`: `SIGTRAP | 0x80`.
const SYSCALL_STOP: c_int = libc::SIGTRAP | 0x80;
/// The child's exit code when `PTRACE_TRACEME` is refused (it never stops, so the
/// tracer sees an early exit with this code instead of waiting forever).
const TRACE_DENIED_EXIT: c_int = 126;
/// The tracee's read buffer (`child_body`); the `count` it passes to `read`.
const READ_BUF: usize = 256;

const K1: u64 = 0x9E37_79B9_7F4A_7C15;
const K2: u64 = 0xBF58_476D_1CE4_E5B9;

/// Why the tracer could not complete. Distinct from a fail-closed replay ABORT
/// (a panic on an inconsistent tape): these are failures of the machinery.
#[derive(Debug)]
pub enum ForeignError {
    /// `pipe`, `fork`, `waitpid`, `ptrace(SETOPTIONS)`, or the digest pipe failed.
    Io(io::Error),
    /// The child could not become a tracee: `PTRACE_TRACEME` was refused (Yama
    /// `ptrace_scope`, a seccomp profile, a container runtime), so it exited
    /// before its first stop.
    TraceDenied,
    /// The tracee exited (with this code) before its initial stop.
    ExitedEarly(i32),
    /// The tracee died by this signal instead of exiting.
    Signaled(i32),
    /// The tracee exited without writing its 8-byte digest.
    NoDigest,
}

impl std::fmt::Display for ForeignError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ForeignError::Io(e) => write!(f, "foreign tracer io error: {e}"),
            ForeignError::TraceDenied => {
                write!(
                    f,
                    "foreign tracer: PTRACE_TRACEME refused (ptrace denied on this host)"
                )
            }
            ForeignError::ExitedEarly(c) => {
                write!(
                    f,
                    "foreign tracer: tracee exited {c} before its initial stop"
                )
            }
            ForeignError::Signaled(s) => write!(f, "foreign tracer: tracee died by signal {s}"),
            ForeignError::NoDigest => write!(f, "foreign tracer: tracee wrote no digest"),
        }
    }
}

impl std::error::Error for ForeignError {}

impl From<io::Error> for ForeignError {
    fn from(e: io::Error) -> Self {
        ForeignError::Io(e)
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
#[cfg(target_arch = "aarch64")]
struct Regs {
    regs: [u64; 31],
    sp: u64,
    pc: u64,
    pstate: u64,
}
#[cfg(target_arch = "aarch64")]
impl Regs {
    fn zero() -> Regs {
        Regs {
            regs: [0; 31],
            sp: 0,
            pc: 0,
            pstate: 0,
        }
    }
    fn nr(&self) -> c_long {
        self.regs[8] as c_long
    }
    fn arg(&self, i: usize) -> u64 {
        self.regs[i]
    }
    fn ret(&self) -> u64 {
        self.regs[0]
    }
    fn set_ret(&mut self, v: u64) {
        self.regs[0] = v;
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
#[cfg(target_arch = "x86_64")]
struct Regs {
    r15: u64,
    r14: u64,
    r13: u64,
    r12: u64,
    rbp: u64,
    rbx: u64,
    r11: u64,
    r10: u64,
    r9: u64,
    r8: u64,
    rax: u64,
    rcx: u64,
    rdx: u64,
    rsi: u64,
    rdi: u64,
    orig_rax: u64,
    rip: u64,
    cs: u64,
    eflags: u64,
    rsp: u64,
    ss: u64,
    fs_base: u64,
    gs_base: u64,
    ds: u64,
    es: u64,
    fs: u64,
    gs: u64,
}
#[cfg(target_arch = "x86_64")]
impl Regs {
    fn zero() -> Regs {
        // SAFETY: Regs is a plain repr(C) struct of u64s; all-zero is a valid value.
        unsafe { std::mem::zeroed() }
    }
    fn nr(&self) -> c_long {
        self.orig_rax as c_long
    }
    fn arg(&self, i: usize) -> u64 {
        match i {
            0 => self.rdi,
            1 => self.rsi,
            2 => self.rdx,
            _ => self.r10,
        }
    }
    fn ret(&self) -> u64 {
        self.rax
    }
    fn set_ret(&mut self, v: u64) {
        self.rax = v;
    }
}

/// The kernel's 64-bit `struct timespec`, as `clock_gettime` fills it.
#[repr(C)]
struct Timespec {
    sec: i64,
    nsec: i64,
}

/// The foreign program's effect fold. Non-commutative in `(clock, rand)`. The
/// claim's test recomputes this over the taped values with its OWN spelling (an
/// oracle written without calling `fold`), so a shared fold bug cannot hide.
pub fn fold(clock: u64, rand: u64, bytes: &[u8]) -> u64 {
    let mut h = clock.rotate_left(7) ^ rand.wrapping_mul(K1);
    for &b in bytes {
        h = (h ^ b as u64).wrapping_mul(K2).rotate_left(11);
    }
    h
}

// The child: make the three effect syscalls via the raw path, fold, write digest.
// SAFETY: post-fork, async-signal-safe libc/syscall calls only; ends in _exit.
unsafe fn child_body(file: &CString, pipe_w: c_int) -> ! {
    let null = std::ptr::null_mut::<c_void>();
    if libc::ptrace(libc::PTRACE_TRACEME, 0, null, null) < 0 {
        // Not traceable here: exit distinctly rather than SIGSTOP as an untraced
        // child, which the tracer's `waitpid(.., 0)` would never observe.
        libc::_exit(TRACE_DENIED_EXIT)
    }
    // Stop so the tracer can set options before our syscalls run.
    let me = libc::syscall(nr::GETPID) as c_int;
    libc::kill(me, libc::SIGSTOP);

    let mut ts = Timespec { sec: 0, nsec: 0 };
    libc::syscall(
        nr::CLOCK_GETTIME,
        1 as c_long, /*MONOTONIC*/
        &mut ts as *mut _ as c_long,
    );
    let clock = (ts.nsec as u64) ^ (ts.sec as u64);

    let mut r: u64 = 0;
    libc::syscall(
        nr::GETRANDOM,
        &mut r as *mut _ as c_long,
        8 as c_long,
        0 as c_long,
    );

    let fd = libc::syscall(
        nr::OPENAT,
        -100 as c_long, /*AT_FDCWD*/
        file.as_ptr() as c_long,
        0 as c_long,
        0 as c_long,
    );
    let mut buf = [0u8; READ_BUF];
    let n = libc::syscall(
        nr::READ,
        fd,
        buf.as_mut_ptr() as c_long,
        buf.len() as c_long,
    );
    libc::syscall(nr::CLOSE, fd);
    // A failed read (negative) is an empty file; the tracer bounds an injected
    // length to the buffer, but clamp here too so the child never over-slices.
    let nb = if n < 0 {
        0
    } else {
        (n as usize).min(buf.len())
    };

    let digest = fold(clock, r, &buf[..nb]);
    let bytes = digest.to_le_bytes();
    libc::write(pipe_w, bytes.as_ptr() as *const c_void, bytes.len());
    libc::_exit(0)
}

/// A `ptrace`/`process_vm_*` return value checked for failure (`< 0`, with errno).
fn check(rc: c_long) -> io::Result<c_long> {
    if rc < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(rc)
    }
}

fn get_regs(pid: c_int) -> io::Result<Regs> {
    let mut regs = Regs::zero();
    let mut iov = libc::iovec {
        iov_base: &mut regs as *mut _ as *mut c_void,
        iov_len: std::mem::size_of::<Regs>(),
    };
    // SAFETY: GETREGSET fills `regs` (a live, correctly-sized buffer) for a stopped tracee.
    let rc = unsafe {
        libc::ptrace(
            libc::PTRACE_GETREGSET,
            pid,
            libc::NT_PRSTATUS as usize as *mut c_void,
            &mut iov as *mut _ as *mut c_void,
        )
    };
    check(rc)?;
    Ok(regs)
}
fn set_regs(pid: c_int, regs: &Regs) -> io::Result<()> {
    let mut r = *regs;
    let mut iov = libc::iovec {
        iov_base: &mut r as *mut _ as *mut c_void,
        iov_len: std::mem::size_of::<Regs>(),
    };
    // SAFETY: SETREGSET reads `r` (a live, correctly-sized buffer) into the tracee.
    let rc = unsafe {
        libc::ptrace(
            libc::PTRACE_SETREGSET,
            pid,
            libc::NT_PRSTATUS as usize as *mut c_void,
            &mut iov as *mut _ as *mut c_void,
        )
    };
    check(rc).map(drop)
}
/// Read exactly `len` bytes of the tracee's memory at `addr`.
fn peek(pid: c_int, addr: u64, len: usize) -> io::Result<Vec<u8>> {
    let mut local = vec![0u8; len];
    let liov = libc::iovec {
        iov_base: local.as_mut_ptr() as *mut c_void,
        iov_len: len,
    };
    let riov = libc::iovec {
        iov_base: addr as *mut c_void,
        iov_len: len,
    };
    // SAFETY: reads at most `len` bytes from the tracee into `local` (len bytes).
    let got = unsafe { libc::process_vm_readv(pid, &liov, 1, &riov, 1, 0) };
    if check(got as c_long)? as usize != len {
        return Err(io::Error::other("process_vm_readv: short read"));
    }
    Ok(local)
}
/// Write all of `bytes` into the tracee's memory at `addr`.
fn poke(pid: c_int, addr: u64, bytes: &[u8]) -> io::Result<()> {
    let liov = libc::iovec {
        iov_base: bytes.as_ptr() as *mut c_void,
        iov_len: bytes.len(),
    };
    let riov = libc::iovec {
        iov_base: addr as *mut c_void,
        iov_len: bytes.len(),
    };
    // SAFETY: writes `bytes` into the tracee's address space at `addr`; every
    // caller has bounded `bytes.len()` to the tracee's buffer at `addr`.
    let put = unsafe { libc::process_vm_writev(pid, &liov, 1, &riov, 1, 0) };
    if check(put as c_long)? as usize != bytes.len() {
        return Err(io::Error::other("process_vm_writev: short write"));
    }
    Ok(())
}

enum Mode<'a> {
    Record(&'a mut Vec<EffectRecord>),
    Replay(std::slice::Iter<'a, EffectRecord>),
    Naive,
}

/// The forked child plus its digest pipe. `Drop` kills + reaps a child that has
/// not been reaped (so an ABORT unwinding through the tracer leaves no stray
/// stopped tracee) and closes the pipe if it was not consumed — no fd leaks on
/// any path, and never a `kill` on a pid that waitpid already settled.
struct Tracee {
    pid: c_int,
    rfd: c_int,
    reaped: bool,
}

impl Drop for Tracee {
    fn drop(&mut self) {
        if !self.reaped {
            // SAFETY: SIGKILL + waitpid on our own un-reaped child (SIGKILL wakes
            // a ptrace-stopped tracee, so the wait returns).
            unsafe {
                libc::kill(self.pid, libc::SIGKILL);
                let mut s: c_int = 0;
                loop {
                    let rc = libc::waitpid(self.pid, &mut s, 0);
                    if rc == self.pid || (rc < 0 && errno() != libc::EINTR) {
                        break;
                    }
                }
            }
            self.reaped = true;
        }
        if self.rfd >= 0 {
            // SAFETY: closing a fd we own.
            unsafe { libc::close(self.rfd) };
            self.rfd = -1;
        }
    }
}

fn errno() -> c_int {
    io::Error::last_os_error().raw_os_error().unwrap_or(0)
}

/// `waitpid(pid)` retrying `EINTR`. `ECHILD` (the pid is not ours to wait for)
/// settles the tracee so `Drop` never signals a possibly-recycled pid.
fn wait_status(t: &mut Tracee) -> Result<c_int, ForeignError> {
    let mut status: c_int = 0;
    loop {
        // SAFETY: waitpid on our own child, writing a live status int.
        let rc = unsafe { libc::waitpid(t.pid, &mut status, 0) };
        if rc == t.pid {
            return Ok(status);
        }
        if rc < 0 {
            let e = io::Error::last_os_error();
            match e.raw_os_error() {
                Some(libc::EINTR) => continue,
                Some(libc::ECHILD) => {
                    t.reaped = true;
                    return Err(ForeignError::Io(e));
                }
                _ => return Err(ForeignError::Io(e)),
            }
        }
        return Err(ForeignError::Io(io::Error::other(format!(
            "waitpid({}) returned {rc}",
            t.pid
        ))));
    }
}

/// Classify a wait status that ended the tracee: `Some(Ok(code))` exited,
/// `Some(Err(sig))` killed by a signal, `None` still alive (a stop).
fn terminal(status: c_int) -> Option<Result<i32, i32>> {
    if libc::WIFEXITED(status) {
        Some(Ok(libc::WEXITSTATUS(status)))
    } else if libc::WIFSIGNALED(status) {
        Some(Err(libc::WTERMSIG(status)))
    } else {
        None
    }
}

/// Resume a stopped tracee to its next syscall stop, delivering `sig` (0 = none).
/// A failure would leave it stopped and the next `waitpid` blocked forever, so
/// it is an error rather than ignored.
fn ptrace_syscall(pid: c_int, sig: c_int) -> io::Result<()> {
    // SAFETY: PTRACE_SYSCALL on our tracee; addr is ignored, data the signal.
    let rc = unsafe {
        libc::ptrace(
            libc::PTRACE_SYSCALL,
            pid,
            std::ptr::null_mut::<c_void>(),
            sig as usize as *mut c_void,
        )
    };
    check(rc).map(drop)
}

/// Drive the stopped child to exit, applying `mode` at each intercepted syscall.
/// Returns once the tracee has exited (and is reaped); the child's digest is then
/// read from its pipe by the caller. Tape inconsistencies under `Replay` ABORT
/// (panic); machinery failures are `Err`.
fn trace(t: &mut Tracee, file: &str, mut mode: Mode) -> Result<(), ForeignError> {
    let pid = t.pid;
    // The initial stop: the child SIGSTOPs itself right after PTRACE_TRACEME. If
    // TRACEME was refused it exits TRACE_DENIED_EXIT instead, which is reported
    // here — never an untraced stop that `waitpid(.., 0)` would wait on forever.
    let status = wait_status(t)?;
    match terminal(status) {
        Some(Ok(code)) => {
            t.reaped = true;
            return Err(if code == TRACE_DENIED_EXIT {
                ForeignError::TraceDenied
            } else {
                ForeignError::ExitedEarly(code)
            });
        }
        Some(Err(sig)) => {
            t.reaped = true;
            return Err(ForeignError::Signaled(sig));
        }
        None => {}
    }
    if !libc::WIFSTOPPED(status) {
        return Err(ForeignError::Io(io::Error::other(format!(
            "unexpected initial wait status {status:#x}"
        ))));
    }
    // Options: syscall stops distinguishable from signal stops; and kill the tracee
    // if this tracer dies. EXITKILL needs Linux >= 3.8 — fall back without it.
    let opts = [
        libc::PTRACE_O_TRACESYSGOOD | libc::PTRACE_O_EXITKILL,
        libc::PTRACE_O_TRACESYSGOOD,
    ];
    let mut set = false;
    for o in opts {
        // SAFETY: SETOPTIONS on our stopped tracee; data is the option bitmask.
        let rc = unsafe {
            libc::ptrace(
                libc::PTRACE_SETOPTIONS,
                pid,
                std::ptr::null_mut::<c_void>(),
                o as usize as *mut c_void,
            )
        };
        if rc >= 0 {
            set = true;
            break;
        }
    }
    if !set {
        // ESRCH here means the child stopped but is NOT our tracee.
        return Err(ForeignError::Io(io::Error::last_os_error()));
    }
    ptrace_syscall(pid, 0)?;

    let mut at_enter = true;
    // (nr, arg0, arg1, arg2) captured at the syscall-enter stop.
    let mut pending: Option<(c_long, u64, u64, u64)> = None;
    loop {
        let status = wait_status(t)?;
        match terminal(status) {
            Some(Ok(_)) => {
                t.reaped = true;
                return Ok(());
            }
            Some(Err(sig)) => {
                t.reaped = true;
                return Err(ForeignError::Signaled(sig));
            }
            None => {}
        }
        if !libc::WIFSTOPPED(status) {
            continue;
        }
        let sig = libc::WSTOPSIG(status);
        if sig != SYSCALL_STOP {
            // Signal-delivery stop: re-inject (suppressing our own setup SIGSTOP);
            // does not toggle enter/exit.
            let s = if sig == libc::SIGSTOP { 0 } else { sig };
            ptrace_syscall(pid, s)?;
            continue;
        }
        let regs = get_regs(pid)?;
        if at_enter {
            let n = regs.nr();
            pending = Some((n, regs.arg(0), regs.arg(1), regs.arg(2)));
        } else if let Some((enr, a0, a1, a2)) = pending.take() {
            // The result buffer is in a different arg per syscall.
            let buf_addr = if enr == nr::GETRANDOM { a0 } else { a1 };
            let ret = regs.ret();
            match enr {
                n if n == nr::CLOCK_GETTIME => apply_clock(pid, buf_addr, &mut mode)?,
                n if n == nr::GETRANDOM => apply_rand(pid, buf_addr, &mut mode)?,
                n if n == nr::READ => apply_read(pid, buf_addr, a2, ret, regs, file, &mut mode)?,
                _ => {}
            }
        }
        at_enter = !at_enter;
        ptrace_syscall(pid, 0)?;
    }
}

/// Fail-closed replay abort: a panic that unwinds through the tracer, whose
/// [`Tracee`] guard kills + reaps the child and closes the digest pipe.
fn abort_replay(msg: &str) -> ! {
    panic!("foreign replay aborted: {msg}");
}

fn next_effect<'a>(it: &mut std::slice::Iter<'a, EffectRecord>) -> &'a EffectRecord {
    match it.next() {
        Some(e) => e,
        None => {
            abort_replay("effect tape exhausted — the process asked for more than was recorded")
        }
    }
}

/// Tape (record) or inject (replay) one effect at its syscall-exit stop. A
/// failed read or write of the tracee's memory or registers is a machinery
/// error: never a silently-taped zero, never a replay that quietly let the live
/// value through.
fn apply_clock(pid: c_int, buf: u64, mode: &mut Mode) -> io::Result<()> {
    match mode {
        Mode::Record(tape) => {
            let ts = peek(pid, buf, 16)?;
            let clock = u64::from_le_bytes(ts[8..16].try_into().unwrap())
                ^ u64::from_le_bytes(ts[0..8].try_into().unwrap());
            tape.push(EffectRecord::Clock(clock));
        }
        Mode::Replay(it) => match next_effect(it) {
            EffectRecord::Clock(v) => {
                let mut ts = [0u8; 16];
                ts[8..16].copy_from_slice(&v.to_le_bytes()); // sec=0, nsec=v -> child reads clock=v
                poke(pid, buf, &ts)?;
            }
            other => abort_replay(&format!("expected a Clock effect, got {other:?}")),
        },
        Mode::Naive => {}
    }
    Ok(())
}

fn apply_rand(pid: c_int, buf: u64, mode: &mut Mode) -> io::Result<()> {
    match mode {
        Mode::Record(tape) => {
            let b = peek(pid, buf, 8)?;
            tape.push(EffectRecord::Rand(u64::from_le_bytes(
                b[..8].try_into().unwrap(),
            )));
        }
        Mode::Replay(it) => match next_effect(it) {
            EffectRecord::Rand(v) => poke(pid, buf, &v.to_le_bytes())?,
            other => abort_replay(&format!("expected a Rand effect, got {other:?}")),
        },
        Mode::Naive => {}
    }
    Ok(())
}

/// `count` is the tracee's `read(2)` length argument — the size of the buffer at
/// `buf` — captured at the enter stop. It bounds both what record peeks and what
/// replay may poke.
fn apply_read(
    pid: c_int,
    buf: u64,
    count: u64,
    ret: u64,
    regs: Regs,
    file: &str,
    mode: &mut Mode,
) -> io::Result<()> {
    match mode {
        Mode::Record(tape) => {
            // The return register is a signed result: negative is -errno (an
            // unreadable/nonexistent file), an empty read — never a length.
            let n = ret as i64;
            let bytes = if n <= 0 {
                Vec::new()
            } else {
                peek(pid, buf, (n as u64).min(count) as usize)?
            };
            tape.push(EffectRecord::File {
                path: file.to_string(),
                bytes,
            });
        }
        Mode::Replay(it) => match next_effect(it) {
            EffectRecord::File { path, bytes } => {
                if path != file {
                    abort_replay(&format!(
                        "file path diverged — recorded {path:?}, replay read {file:?}"
                    ));
                }
                if bytes.len() as u64 > count {
                    abort_replay(&format!(
                        "taped File record is {} bytes but the tracee's read buffer holds {count}",
                        bytes.len()
                    ));
                }
                poke(pid, buf, bytes)?;
                let mut r2 = regs;
                r2.set_ret(bytes.len() as u64);
                set_regs(pid, &r2)?;
            }
            other => abort_replay(&format!("expected a File effect, got {other:?}")),
        },
        Mode::Naive => {}
    }
    Ok(())
}

// Fork the foreign child reading `file`; return it with the pipe read-fd the
// child writes its digest to. The child runs `child_body` and never returns.
fn spawn(file: &str) -> Result<Tracee, ForeignError> {
    let cfile = CString::new(file)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "file path has a NUL byte"))?;
    let mut fds: [c_int; 2] = [-1, -1];
    // SAFETY: pipe2 writes two fds into a live 2-int array (CLOEXEC so a
    // concurrent fork+exec elsewhere in the process cannot inherit them).
    if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } < 0 {
        return Err(ForeignError::Io(io::Error::last_os_error()));
    }
    // SAFETY: fork; the child uses only async-signal-safe libc/syscall calls and
    // ends in _exit. A failed fork (-1) is an error — never a pid to wait on
    // (waitpid(-1) would reap ANY child of this process).
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        let e = io::Error::last_os_error();
        unsafe {
            libc::close(fds[0]);
            libc::close(fds[1]);
        }
        return Err(ForeignError::Io(e));
    }
    if pid == 0 {
        unsafe {
            libc::close(fds[0]);
            child_body(&cfile, fds[1])
        }
    }
    // SAFETY: closing the write end we own; the child holds its own copy.
    unsafe { libc::close(fds[1]) };
    Ok(Tracee {
        pid,
        rfd: fds[0],
        reaped: false,
    })
}

impl Tracee {
    /// Read the 8-byte digest the exited child wrote, closing the pipe.
    fn read_digest(&mut self) -> Result<u64, ForeignError> {
        let mut buf = [0u8; 8];
        let mut got = 0usize;
        while got < buf.len() {
            // SAFETY: read into the live remainder of `buf` from a fd we own.
            let n = unsafe {
                libc::read(
                    self.rfd,
                    buf[got..].as_mut_ptr() as *mut c_void,
                    buf.len() - got,
                )
            };
            if n < 0 {
                if errno() == libc::EINTR {
                    continue;
                }
                return Err(ForeignError::Io(io::Error::last_os_error()));
            }
            if n == 0 {
                break;
            }
            got += n as usize;
        }
        // SAFETY: closing a fd we own (once; Drop then skips it).
        unsafe { libc::close(self.rfd) };
        self.rfd = -1;
        if got != buf.len() {
            return Err(ForeignError::NoDigest);
        }
        Ok(u64::from_le_bytes(buf))
    }
}

/// Record the fixed foreign child's effects while it reads `file`. Returns the tape
/// and the child's digest. An unreadable `file` records an empty `File` effect.
pub fn record(file: &str) -> Result<(EffectsLog, u64), ForeignError> {
    let mut t = spawn(file)?;
    let mut tape: Vec<EffectRecord> = Vec::new();
    trace(&mut t, file, Mode::Record(&mut tape))?;
    let digest = t.read_digest()?;
    Ok((EffectsLog(tape), digest))
}

/// Replay the fixed foreign child driven by `tape` (no recorded effect comes from
/// the live world). Returns the child's digest; ABORTS (panics, killing and
/// reaping the tracee) on a short, wrong-kind, path-divergent, or over-long tape.
pub fn replay(file: &str, tape: &EffectsLog) -> Result<u64, ForeignError> {
    let mut t = spawn(file)?;
    trace(&mut t, file, Mode::Replay(tape.0.iter()))?;
    t.read_digest()
}

/// A NAIVE replay that injects nothing — for a test to show injection is load-bearing.
pub fn run_naive(file: &str) -> Result<u64, ForeignError> {
    let mut t = spawn(file)?;
    trace(&mut t, file, Mode::Naive)?;
    t.read_digest()
}

// ============================================================================
// Seccomp-BPF pre-filter + full syscall neutralization + unmodified `execve`
// (`docs/ROADMAP.md` §4, `seccomp_record_replay`)
// ============================================================================

#[cfg(target_arch = "aarch64")]
const SYS_SECCOMP: c_long = 277;
#[cfg(target_arch = "x86_64")]
const SYS_SECCOMP: c_long = 317;

const SECCOMP_SET_MODE_FILTER: c_long = 1;
const PR_SET_NO_NEW_PRIVS: c_int = 38;
const PTRACE_O_TRACESECCOMP_BIT: c_int = 1 << 7;
const PTRACE_EVENT_SECCOMP_ID: c_int = 7;

#[cfg(target_arch = "aarch64")]
const NT_ARM_SYSTEM_CALL: usize = 0x404;

#[cfg(target_arch = "aarch64")]
const CURRENT_SECCOMP_ARCH: crate::seccomp::SeccompArch = crate::seccomp::SeccompArch::Aarch64;
#[cfg(target_arch = "x86_64")]
const CURRENT_SECCOMP_ARCH: crate::seccomp::SeccompArch = crate::seccomp::SeccompArch::X86_64;

#[repr(C)]
struct SockFprog {
    len: u16,
    filter: *const crate::seccomp::SockFilter,
}

/// Entry point invoked by the standalone unmodified `seccomp_child` binary (`#![forbid(unsafe_code)]`).
///
/// Makes zero `PTRACE_TRACEME` or `SIGSTOP` calls: reads one monotonic clock, 8 random bytes,
/// and `file` via `openat`/`read`/`close`, folds `(clock, rand, bytes)`, writes the 8-byte
/// little-endian digest to `STDOUT_FILENO`, and returns exit code `0` (`1` on short write).
#[must_use]
pub fn run_unmodified_probe(file: &str) -> i32 {
    let Ok(cfile) = CString::new(file) else {
        return 2;
    };
    // SAFETY: direct syscalls on valid stack buffers and NUL-terminated `cfile`.
    unsafe {
        let mut ts = Timespec { sec: 0, nsec: 0 };
        libc::syscall(nr::CLOCK_GETTIME, 1 as c_long, &mut ts as *mut _ as c_long);
        let clock = (ts.nsec as u64) ^ (ts.sec as u64);

        let mut r: u64 = 0;
        libc::syscall(
            nr::GETRANDOM,
            &mut r as *mut _ as c_long,
            8 as c_long,
            0 as c_long,
        );

        let fd = libc::syscall(
            nr::OPENAT,
            -100 as c_long,
            cfile.as_ptr() as c_long,
            0 as c_long,
            0 as c_long,
        );
        let mut buf = [0u8; READ_BUF];
        let n = libc::syscall(
            nr::READ,
            fd,
            buf.as_mut_ptr() as c_long,
            buf.len() as c_long,
        );
        libc::syscall(nr::CLOSE, fd);
        let nb = if n < 0 {
            0
        } else {
            (n as usize).min(buf.len())
        };
        let digest = fold(clock, r, &buf[..nb]);
        let bytes = digest.to_le_bytes();
        let wrote = libc::write(
            libc::STDOUT_FILENO,
            bytes.as_ptr() as *const c_void,
            bytes.len(),
        );
        if wrote == (bytes.len() as isize) {
            0
        } else {
            1
        }
    }
}

fn ptrace_cont(pid: c_int, sig: c_int) -> io::Result<()> {
    // SAFETY: PTRACE_CONT resumes our stopped tracee; `sig` is signal number or 0.
    let rc = unsafe {
        libc::ptrace(
            libc::PTRACE_CONT,
            pid,
            std::ptr::null_mut::<c_void>(),
            sig as usize as *mut c_void,
        )
    };
    check(rc).map(drop)
}

fn neutralize_syscall(pid: c_int, regs: &mut Regs) -> io::Result<()> {
    #[cfg(target_arch = "x86_64")]
    {
        regs.orig_rax = (-1i64) as u64;
        set_regs(pid, regs)
    }
    #[cfg(target_arch = "aarch64")]
    {
        let _ = regs;
        let mut sysno: c_int = -1;
        let mut iov = libc::iovec {
            iov_base: &mut sysno as *mut _ as *mut c_void,
            iov_len: std::mem::size_of::<c_int>(),
        };
        // SAFETY: NT_ARM_SYSTEM_CALL sets the active syscall number to -1 on stopped aarch64 tracee.
        let rc = unsafe {
            libc::ptrace(
                libc::PTRACE_SETREGSET,
                pid,
                NT_ARM_SYSTEM_CALL as *mut c_void,
                &mut iov as *mut _ as *mut c_void,
            )
        };
        check(rc).map(drop)
    }
}

fn peek_cstr(pid: c_int, addr: u64, max_len: usize) -> io::Result<String> {
    if addr == 0 {
        return Ok(String::new());
    }
    let cap = max_len.min(4096);
    let mut out = Vec::with_capacity(128);
    let mut cur = addr;
    while out.len() < cap {
        let b = peek(pid, cur, 1)?;
        if b[0] == 0 {
            break;
        }
        out.push(b[0]);
        cur = cur.saturating_add(1);
    }
    Ok(String::from_utf8_lossy(&out).into_owned())
}

/// Step a tracee currently stopped at `PTRACE_EVENT_SECCOMP` across its single syscall
/// (either real on `Record`/passthrough or neutralized `-1` on `Replay`) to the matching
/// syscall-exit stop (`SYSCALL_STOP`), returning the exit `Regs`.
fn step_to_syscall_exit(t: &mut Tracee) -> Result<Regs, ForeignError> {
    let pid = t.pid;
    ptrace_syscall(pid, 0)?;
    loop {
        let status = wait_status(t)?;
        match terminal(status) {
            Some(Ok(code)) => {
                t.reaped = true;
                return Err(ForeignError::ExitedEarly(code));
            }
            Some(Err(sig)) => {
                t.reaped = true;
                return Err(ForeignError::Signaled(sig));
            }
            None => {}
        }
        if !libc::WIFSTOPPED(status) {
            continue;
        }
        let sig = libc::WSTOPSIG(status);
        if sig == SYSCALL_STOP {
            return Ok(get_regs(pid)?);
        }
        let forward = if sig == libc::SIGTRAP || sig == libc::SIGSTOP {
            0
        } else {
            sig
        };
        ptrace_syscall(pid, forward)?;
    }
}

fn spawn_exec(bin_path: &str, file_path: &str) -> Result<Tracee, ForeignError> {
    let Ok(cbin) = CString::new(bin_path) else {
        return Err(ForeignError::Io(io::Error::new(
            io::ErrorKind::InvalidInput,
            "bin_path has a NUL byte",
        )));
    };
    let Ok(cfile) = CString::new(file_path) else {
        return Err(ForeignError::Io(io::Error::new(
            io::ErrorKind::InvalidInput,
            "file_path has a NUL byte",
        )));
    };
    let mut fds: [c_int; 2] = [-1, -1];
    // SAFETY: pipe2 initializes two valid CLOEXEC descriptors.
    if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } < 0 {
        return Err(ForeignError::Io(io::Error::last_os_error()));
    }
    let filter = crate::seccomp::compile_five_syscall_filter(CURRENT_SECCOMP_ARCH);
    // SAFETY: fork + async-signal-safe setup + seccomp filter install + execve in child.
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        let e = io::Error::last_os_error();
        unsafe {
            libc::close(fds[0]);
            libc::close(fds[1]);
        }
        return Err(ForeignError::Io(e));
    }
    if pid == 0 {
        unsafe {
            libc::close(fds[0]);
            if libc::dup2(fds[1], libc::STDOUT_FILENO) < 0 {
                libc::_exit(125);
            }
            libc::close(fds[1]);
            let null = std::ptr::null_mut::<c_void>();
            if libc::ptrace(libc::PTRACE_TRACEME, 0, null, null) < 0 {
                libc::_exit(TRACE_DENIED_EXIT);
            }
            let me = libc::syscall(nr::GETPID) as c_int;
            libc::kill(me, libc::SIGSTOP);
            if libc::prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) < 0 {
                libc::_exit(TRACE_DENIED_EXIT);
            }
            let prog = SockFprog {
                len: filter.len() as u16,
                filter: filter.as_ptr(),
            };
            if libc::syscall(
                SYS_SECCOMP,
                SECCOMP_SET_MODE_FILTER,
                0 as c_long,
                &prog as *const SockFprog as c_long,
            ) < 0
            {
                libc::_exit(TRACE_DENIED_EXIT);
            }
            let argv = [cbin.as_ptr(), cfile.as_ptr(), std::ptr::null()];
            let envp = [std::ptr::null()];
            libc::execve(cbin.as_ptr(), argv.as_ptr(), envp.as_ptr());
            libc::_exit(127);
        }
    }
    // SAFETY: close parent copy of write pipe end.
    unsafe { libc::close(fds[1]) };
    Ok(Tracee {
        pid,
        rfd: fds[0],
        reaped: false,
    })
}

fn attach_seccomp_tracer(t: &mut Tracee) -> Result<(), ForeignError> {
    let pid = t.pid;
    let status = wait_status(t)?;
    match terminal(status) {
        Some(Ok(code)) => {
            t.reaped = true;
            return Err(if code == TRACE_DENIED_EXIT {
                ForeignError::TraceDenied
            } else {
                ForeignError::ExitedEarly(code)
            });
        }
        Some(Err(sig)) => {
            t.reaped = true;
            return Err(ForeignError::Signaled(sig));
        }
        None => {}
    }
    let opts = [
        libc::PTRACE_O_TRACESYSGOOD | PTRACE_O_TRACESECCOMP_BIT | libc::PTRACE_O_EXITKILL,
        libc::PTRACE_O_TRACESYSGOOD | PTRACE_O_TRACESECCOMP_BIT,
    ];
    let mut set = false;
    for o in opts {
        // SAFETY: SETOPTIONS on our stopped tracee.
        let rc = unsafe {
            libc::ptrace(
                libc::PTRACE_SETOPTIONS,
                pid,
                std::ptr::null_mut::<c_void>(),
                o as usize as *mut c_void,
            )
        };
        if rc >= 0 {
            set = true;
            break;
        }
    }
    if !set {
        return Err(ForeignError::Io(io::Error::last_os_error()));
    }
    ptrace_cont(pid, 0)?;
    Ok(())
}

fn is_seccomp_event(status: c_int) -> bool {
    libc::WSTOPSIG(status) == libc::SIGTRAP && ((status >> 16) & 0xffff) == PTRACE_EVENT_SECCOMP_ID
}

/// Record an unmodified `execve`'d child binary `bin_path` reading `file` under the
/// 5-syscall `seccomp-bpf` pre-filter (`O(intercepted)` stops).
pub fn record_exec(bin_path: &str, file: &str) -> Result<(EffectsLog, u64), ForeignError> {
    let mut t = spawn_exec(bin_path, file)?;
    attach_seccomp_tracer(&mut t)?;
    let pid = t.pid;
    let mut tape = Vec::new();
    let mut target_fd: Option<i64> = None;

    loop {
        let status = wait_status(&mut t)?;
        match terminal(status) {
            Some(Ok(_)) => {
                t.reaped = true;
                break;
            }
            Some(Err(sig)) => {
                t.reaped = true;
                return Err(ForeignError::Signaled(sig));
            }
            None => {}
        }
        if !libc::WIFSTOPPED(status) {
            continue;
        }
        if !is_seccomp_event(status) {
            let sig = libc::WSTOPSIG(status);
            let forward = if sig == libc::SIGTRAP || sig == libc::SIGSTOP {
                0
            } else {
                sig
            };
            ptrace_cont(pid, forward)?;
            continue;
        }
        let regs = get_regs(pid)?;
        match CURRENT_SECCOMP_ARCH.classify_nr(regs.nr() as i64) {
            Some(crate::seccomp::InterceptedSyscall::ClockGettime) => {
                let buf_addr = regs.arg(1);
                let _exit = step_to_syscall_exit(&mut t)?;
                let ts = peek(pid, buf_addr, 16)?;
                let clock = u64::from_le_bytes(ts[8..16].try_into().unwrap())
                    ^ u64::from_le_bytes(ts[0..8].try_into().unwrap());
                tape.push(EffectRecord::Clock(clock));
            }
            Some(crate::seccomp::InterceptedSyscall::Getrandom) => {
                let buf_addr = regs.arg(0);
                let _exit = step_to_syscall_exit(&mut t)?;
                let b = peek(pid, buf_addr, 8)?;
                tape.push(EffectRecord::Rand(u64::from_le_bytes(
                    b[..8].try_into().unwrap(),
                )));
            }
            Some(crate::seccomp::InterceptedSyscall::Openat) => {
                let path_str = peek_cstr(pid, regs.arg(1), 4096)?;
                if path_str == file {
                    let exit = step_to_syscall_exit(&mut t)?;
                    target_fd = Some(exit.ret() as i64);
                }
            }
            Some(crate::seccomp::InterceptedSyscall::Read) => {
                let fd = regs.arg(0) as i64;
                if target_fd == Some(fd) {
                    let buf_addr = regs.arg(1);
                    let count = regs.arg(2);
                    let exit = step_to_syscall_exit(&mut t)?;
                    let n = exit.ret() as i64;
                    let bytes = if n <= 0 {
                        Vec::new()
                    } else {
                        peek(pid, buf_addr, (n as u64).min(count) as usize)?
                    };
                    tape.push(EffectRecord::File {
                        path: file.to_owned(),
                        bytes,
                    });
                }
            }
            Some(crate::seccomp::InterceptedSyscall::Close) => {
                let fd = regs.arg(0) as i64;
                if target_fd == Some(fd) {
                    target_fd = None;
                }
            }
            None => {}
        }
        ptrace_cont(pid, 0)?;
    }

    let digest = t.read_digest()?;
    Ok((EffectsLog(tape), digest))
}

/// Replay an unmodified `execve`'d child binary `bin_path` driven by `tape` with **full
/// syscall neutralization**: every intercepted target syscall is rewritten to `-1` at
/// `PTRACE_EVENT_SECCOMP` before reaching the kernel, then its taped return value and buffer
/// are injected at the `-ENOSYS` exit stop. Aborts (panics, killing + reaping the tracee) on
/// a short, wrong-kind, path-divergent, or over-buffer tape.
pub fn replay_exec(bin_path: &str, file: &str, tape: &EffectsLog) -> Result<u64, ForeignError> {
    let mut t = spawn_exec(bin_path, file)?;
    attach_seccomp_tracer(&mut t)?;
    let pid = t.pid;
    let mut drv = crate::seccomp::NeutralizedReplayDriver::new(file, tape);

    loop {
        let status = wait_status(&mut t)?;
        match terminal(status) {
            Some(Ok(_)) => {
                t.reaped = true;
                break;
            }
            Some(Err(sig)) => {
                t.reaped = true;
                return Err(ForeignError::Signaled(sig));
            }
            None => {}
        }
        if !libc::WIFSTOPPED(status) {
            continue;
        }
        if !is_seccomp_event(status) {
            let sig = libc::WSTOPSIG(status);
            let forward = if sig == libc::SIGTRAP || sig == libc::SIGSTOP {
                0
            } else {
                sig
            };
            ptrace_cont(pid, forward)?;
            continue;
        }
        let mut regs = get_regs(pid)?;
        let (decision, poke_addr) = match CURRENT_SECCOMP_ARCH.classify_nr(regs.nr() as i64) {
            Some(crate::seccomp::InterceptedSyscall::ClockGettime) => {
                let d = drv
                    .on_clock_gettime()
                    .unwrap_or_else(|e| abort_replay(&format!("{e:?}")));
                (d, regs.arg(1))
            }
            Some(crate::seccomp::InterceptedSyscall::Getrandom) => {
                let d = drv
                    .on_getrandom(regs.arg(1))
                    .unwrap_or_else(|e| abort_replay(&format!("{e:?}")));
                (d, regs.arg(0))
            }
            Some(crate::seccomp::InterceptedSyscall::Openat) => {
                let path_str = peek_cstr(pid, regs.arg(1), 4096)?;
                (drv.on_openat(&path_str), 0)
            }
            Some(crate::seccomp::InterceptedSyscall::Read) => {
                let d = drv
                    .on_read(regs.arg(0) as i64, regs.arg(2))
                    .unwrap_or_else(|e| abort_replay(&format!("{e:?}")));
                (d, regs.arg(1))
            }
            Some(crate::seccomp::InterceptedSyscall::Close) => {
                (drv.on_close(regs.arg(0) as i64), 0)
            }
            None => (
                crate::seccomp::SeccompReplayDecision::PassthroughRuntimeIo,
                0,
            ),
        };

        match decision {
            crate::seccomp::SeccompReplayDecision::PassthroughRuntimeIo => {
                ptrace_cont(pid, 0)?;
            }
            crate::seccomp::SeccompReplayDecision::NeutralizeAndInject {
                return_value,
                poke_bytes,
                ..
            } => {
                neutralize_syscall(pid, &mut regs)?;
                let mut exit_regs = step_to_syscall_exit(&mut t)?;
                if let Some(bytes) = poke_bytes {
                    poke(pid, poke_addr, &bytes)?;
                }
                exit_regs.set_ret(return_value as u64);
                set_regs(pid, &exit_regs)?;
                ptrace_cont(pid, 0)?;
            }
        }
    }

    t.read_digest()
}
