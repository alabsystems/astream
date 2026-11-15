// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `cfg(clean_islands)`, decided by the compiler: a crate's Clean islands (`*_island.rs`)
//! compile when the compiler is Trust, the one compiler that lexes them, and never under a
//! stock rustc (aterm's cross cells, its x86_64-apple-darwin slice, its Linux lane). Every
//! astream crate mounts this file into its build script, so the rule has one spelling and no
//! lane flag or RUSTFLAGS changes what compiles. aterm's crates decide it the same way.

/// Declare `cfg(clean_islands)` for the calling crate, and set it under a Trust compiler.
pub fn emit() {
    println!("cargo::rustc-check-cfg=cfg(clean_islands)");
    if trust_compiler() {
        println!("cargo::rustc-cfg=clean_islands");
    }
}

/// Does `RUSTC`, the compiler itself (a lint driver arrives as a separate wrapper), say it
/// is a Trust build: a `trust:` line in its `-vV`? Not `CARGO_CFG_TRUST_VERIFY`: Trust
/// prints that cfg only while it verifies, so a lint driver's target cfg lacks it.
fn trust_compiler() -> bool {
    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    std::process::Command::new(rustc)
        .arg("-vV")
        .output()
        .is_ok_and(|out| {
            out.stdout
                .split(|&byte| byte == b'\n')
                .any(|line| line.starts_with(b"trust:"))
        })
}
