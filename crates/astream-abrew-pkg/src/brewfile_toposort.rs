// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Cycle-checked Kahn topological installer plan for native `abrew bundle`
//! (`Astream.Abrew.TlaBrewfileToposort`).

use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[cfg(clean_islands)]
#[path = "brewfile_toposort_island.rs"]
mod brewfile_toposort_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_deps_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn pkg_installed_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use brewfile_toposort_island::{pkg_deps_clamp, pkg_installed_advance};

/// Maximum formulas in a single native `Brewfile`.
pub const MAX_BREWFILE_FORMULAS: u64 = 256;

contract_fn! {
    /// Verified acyclicity completion (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `pkg_acyclic_done_isl`.
    #[must_use]
    pub const fn pkg_acyclic_done(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

fn copy_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

/// Solves deterministic dependency-first install order for `abrew bundle`.
pub fn plan_brewfile_install_order(deps: &[(&str, &[&str])]) -> Result<Vec<String>, &'static str> {
    let max_formulas = pkg_deps_clamp(MAX_BREWFILE_FORMULAS, MAX_BREWFILE_FORMULAS) as usize;
    if deps.len() > max_formulas {
        return Err("Brewfile formula count exceeds MAX_BREWFILE_FORMULAS");
    }
    let lim = pkg_deps_clamp(deps.len() as u64, MAX_BREWFILE_FORMULAS) as usize;
    let mut indeg: BTreeMap<String, usize> = BTreeMap::new();
    let mut rdeps: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut idx = 0usize;
    while idx < lim {
        let Some(&(pkg, reqs)) = deps.get(idx) else {
            break;
        };
        if pkg.trim().is_empty() {
            return Err("empty formula name in Brewfile");
        }
        if !indeg.contains_key(pkg) {
            if indeg.len() >= max_formulas {
                return Err("total unique formulas exceed MAX_BREWFILE_FORMULAS");
            }
            indeg.insert(copy_str(pkg), 0);
        }
        let mut r_idx = 0usize;
        while r_idx < reqs.len() {
            let Some(&r) = reqs.get(r_idx) else {
                break;
            };
            if r.trim().is_empty() {
                return Err("empty dependency formula name in Brewfile");
            }
            if r == pkg {
                return Err("cycle detected in Brewfile dependency graph");
            }
            if !indeg.contains_key(r) {
                if indeg.len() >= max_formulas {
                    return Err("total unique formulas exceed MAX_BREWFILE_FORMULAS");
                }
                indeg.insert(copy_str(r), 0);
            }
            let inserted = rdeps.entry(copy_str(r)).or_default().insert(copy_str(pkg));
            if inserted {
                if let Some(d) = indeg.get_mut(pkg) {
                    *d = d.saturating_add(1);
                }
            }
            r_idx = r_idx.saturating_add(1);
        }
        idx = idx.saturating_add(1);
    }
    let mut ready: VecDeque<String> = VecDeque::new();
    for (k, &d) in &indeg {
        if d == 0 {
            ready.push_back(k.clone());
        }
    }
    let mut order = Vec::new();
    let mut done = 0u64;
    while let Some(n) = ready.pop_front() {
        if let Some(children) = rdeps.get(&n) {
            for ch in children {
                if let Some(d) = indeg.get_mut(ch) {
                    *d = d.saturating_sub(1);
                    if *d == 0 {
                        ready.push_back(ch.clone());
                    }
                }
            }
        }
        order.push(n);
        done = pkg_installed_advance(done, done.saturating_add(1));
    }
    if !pkg_acyclic_done(done, indeg.len() as u64) {
        return Err("cycle detected in Brewfile dependency graph");
    }
    Ok(order)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn brewfile_toposort_orders_dependencies_first_and_rejects_cycles() {
        let order = plan_brewfile_install_order(&[
            ("curl", &["openssl", "zlib"]),
            ("openssl", &["zlib"]),
            ("zlib", &[]),
        ])
        .unwrap();
        assert_eq!(order, vec!["zlib", "openssl", "curl"]);
        assert!(plan_brewfile_install_order(&[("a", &["b"]), ("b", &["a"])]).is_err());
    }
}
