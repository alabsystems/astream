//! `verify_attach` runs on the grant string of an `Attach` frame, before the
//! peer has proved anything. Parsing that string builds a `Filter`, which costs
//! tens of bytes per `/x` segment, so a grant of 8M one-byte segments (16 MiB,
//! the frame cap) would take hundreds of MiB to parse. The proof must therefore
//! be checked BEFORE the grant is parsed: a bearer without a genuine proof gets
//! its grant hashed (linear, a copy at most), never parsed.
//!
//! Its own test binary, so no other test moves the process's peak RSS while
//! this one measures it. Linux-only: the measurement is `/proc/self/status`.
#![cfg(target_os = "linux")]

/// The process's peak resident set size so far, in KiB.
fn peak_rss_kib() -> u64 {
    let status = std::fs::read_to_string("/proc/self/status").expect("procfs");
    status
        .lines()
        .find_map(|l| l.strip_prefix("VmHWM:"))
        .and_then(|v| v.trim().trim_end_matches("kB").trim().parse().ok())
        .expect("VmHWM")
}

#[test]
fn a_hostile_grant_with_a_wrong_proof_is_refused_without_being_parsed() {
    let grant = "/a".repeat(8 * 1024 * 1024);
    let before = peak_rss_kib();
    assert!(!astream_cap::verify_attach(
        b"broker-secret",
        &grant,
        &[7u8; 32],
        &[0u8; 32]
    ));
    let grown_mib = (peak_rss_kib() - before) / 1024;
    // Hashing needs at most one copy of the grant (16 MiB); parsing it needed
    // ~36 times that.
    assert!(
        grown_mib < 128,
        "verify_attach grew peak RSS by {grown_mib} MiB for a 16 MiB grant it refused"
    );
}
