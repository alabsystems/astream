// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Active `aterm` executable overwrite shield blocking `cp`, `install`, or `codesign` onto
//! `~/.local/bin/aterm` or `Contents/MacOS/aterm` (`aterm` primer: can kill every `aterm` window!;
//! `Astream.Abrew.TlaSelfBinaryShield`).

#[cfg(clean_islands)]
#[path = "self_binary_shield_island.rs"]
mod self_binary_shield_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_shield_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_blocked_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use self_binary_shield_island::{pkg_blocked_advance, pkg_shield_clamp};

/// Protected path patterns count ceiling.
pub const MAX_SHIELD_PATHS: u64 = 16;

contract_fn! {
    /// Verified safety check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `pkg_target_safe_isl`.
    #[must_use]
    pub const fn pkg_target_safe(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Guards the running `aterm` app executable from in-place overwrite/codesign SIGKILL (`CODE SIGNING` page invalidation!).
#[derive(Debug, Clone, Default)]
pub struct RunningExecutableShield {
    blocked_attempts: u64,
}

fn normalize_dest_tail(mut s: &str) -> &str {
    loop {
        if let Some(rest) = s.strip_suffix('/') {
            s = rest;
        } else if let Some(rest) = s.strip_suffix("/.") {
            s = rest;
        } else {
            break;
        }
    }
    s
}

impl RunningExecutableShield {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            blocked_attempts: 0,
        }
    }

    pub fn check_mutating_command(
        &mut self,
        prog: &str,
        dest_path: &str,
    ) -> Result<(), &'static str> {
        let _ = pkg_shield_clamp(2, MAX_SHIELD_PATHS);
        let base_prog = match prog.rsplit_once('/') {
            Some((_, base)) => base,
            None => prog,
        };
        let is_mutator = matches!(
            base_prog,
            "cp" | "install" | "codesign" | "mv" | "ln" | "rm" | "unlink" | "strip"
        );
        let clean_dest = normalize_dest_tail(dest_path.trim());
        let hits_installed_aterm = clean_dest.ends_with("/.local/bin/aterm")
            || clean_dest == "~/.local/bin/aterm"
            || clean_dest == "$HOME/.local/bin/aterm"
            || clean_dest == "${HOME}/.local/bin/aterm"
            || clean_dest.ends_with("/Contents/MacOS/aterm");
        if is_mutator && hits_installed_aterm && pkg_target_safe(1, 1) {
            self.blocked_attempts = pkg_blocked_advance(
                self.blocked_attempts,
                self.blocked_attempts.saturating_add(1),
            );
            return Err("refused: mutating installed aterm executable kills live aterm windows; run build from target/ path");
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shield_blocks_cp_install_and_codesign_onto_installed_aterm_binary() {
        let mut s = RunningExecutableShield::new();
        assert!(s
            .check_mutating_command("cp", "/Applications/aterm.app/Contents/MacOS/aterm")
            .is_err());
        assert!(s
            .check_mutating_command("codesign", "/fixture-home/.local/bin/aterm")
            .is_err());
        assert!(s
            .check_mutating_command("codesign", "/fixture-home/aterm/target/release/aterm")
            .is_ok());
    }
}
