// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm/vendor/README-astream.md` `[OB-1]` vendored-crate dependency-graph stability guard
//! ensuring the 7 `aterm`-vendored crates (`astream-wire`, `astream-digest`, `astream-cap`,
//! `astream-sys`, `astream-broker`, `astream-term`, `astream-effects`) never gain unexpected path
//! dependencies (`Astream.GitAlign.TlaVendorPinAuditor`).

#[cfg(clean_islands)]
#[path = "vendor_pin_auditor_island.rs"]
mod vendor_pin_auditor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_vendor_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn git_audit_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use vendor_pin_auditor_island::{git_audit_advance, git_vendor_clamp};

/// Exact count of `astream` crates vendored into `aterm/vendor/`.
pub const ATERM_VENDORED_CRATE_COUNT: u64 = 7;

contract_fn! {
    /// Verified zero-drift check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `git_vendor_clean_isl`.
    #[must_use]
    pub const fn git_vendor_clean(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn allowed_runtime_deps(crate_name: &str) -> Option<&'static [&'static str]> {
    match crate_name {
        "astream-wire" | "astream-digest" | "astream-sys" | "astream-term" | "astream-effects" => {
            Some(&[])
        }
        "astream-cap" => Some(&["astream-wire", "astream-digest"]),
        "astream-broker" => Some(&["astream-wire", "astream-sys", "astream-cap", "astream-aead"]),
        _ => None,
    }
}

/// Audits `[dependencies]` of the 7 `aterm`-vendored crates against `[OB-1]`.
#[derive(Debug, Clone, Default)]
pub struct VendorGraphAuditor {
    audits: u64,
}

impl VendorGraphAuditor {
    #[must_use]
    pub const fn new() -> Self {
        Self { audits: 0 }
    }

    pub fn verify_crate_deps(
        &mut self,
        crate_name: &str,
        runtime_deps: &[&str],
    ) -> Result<(), String> {
        let _ = git_vendor_clamp(ATERM_VENDORED_CRATE_COUNT, ATERM_VENDORED_CRATE_COUNT);
        self.audits = git_audit_advance(self.audits, self.audits.saturating_add(1));
        let Some(allowed) = allowed_runtime_deps(crate_name) else {
            return Ok(());
        };
        let mut violations = 0u64;
        let mut idx = 0usize;
        while idx < runtime_deps.len() {
            if let Some(&d) = runtime_deps.get(idx) {
                let mut is_allowed = false;
                let mut a_idx = 0usize;
                while a_idx < allowed.len() {
                    if let Some(&ok_dep) = allowed.get(a_idx) {
                        if ok_dep == d {
                            is_allowed = true;
                            break;
                        }
                    }
                    a_idx = a_idx.saturating_add(1);
                }
                if !is_allowed {
                    violations = violations.saturating_add(1);
                }
            }
            idx = idx.saturating_add(1);
        }
        if !git_vendor_clean(0, violations) {
            let mut msg = String::new();
            msg.push_str("vendored crate ");
            msg.push_str(crate_name);
            msg.push_str(" added unauthorized runtime dependency");
            return Err(msg);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vendor_auditor_enforces_exact_ob1_dependency_closure_for_vendored_crates() {
        let mut a = VendorGraphAuditor::new();
        assert!(a.verify_crate_deps("astream-wire", &[]).is_ok());
        assert!(a
            .verify_crate_deps("astream-cap", &["astream-wire", "astream-digest"])
            .is_ok());
        assert!(a
            .verify_crate_deps("astream-term", &["astream-wire"])
            .is_err());
    }
}
