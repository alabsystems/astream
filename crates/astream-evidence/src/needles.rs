//! Lint search strings ("needles") assembled from fragments.
//!
//! The merge gate scans source files for things like checkpoint markers and
//! cfg-feature references. If this crate's own source contained those exact
//! strings as literals, the gate would flag itself. So every needle is built
//! at runtime from pieces that, on disk, never form the contiguous trigger.
//! A meta-test (`gate_passes_on_the_real_repo`) proves this works by running
//! the gate against astream's own tree and asserting zero findings.

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "needles_island.rs"]
mod needles_island;
#[cfg(not(clean_islands))]
pub use crate::twins::needle_clamp_count;
#[cfg(clean_islands)]
pub use needles_island::needle_clamp_count;

contract_fn! {
    /// Verified check that a constructed lint needle is non-empty (`0 < len`),
    /// linked via `clean-kernel-defeq` to `needle_non_empty_isl`.
    #[must_use]
    pub const fn needle_non_empty(len: usize) -> bool
    clauses [ensures result == (0 < len)]
    {
        0 < len
    }
}

fn join_two(a: &str, b: &str) -> String {
    let mut out = String::new();
    out.push_str(a);
    out.push_str(b);
    out
}

/// Unlinked task marker (assembled so the literal never appears here).
pub fn task_marker() -> String {
    join_two("TO", "DO")
}

/// "Fix-me" marker, assembled from fragments.
pub fn fixme_marker() -> String {
    join_two("FIX", "ME")
}

/// Incomplete-checkpoint marker prefix: the bracketed tag agent swarms leave
/// on half-finished commits. A prefix (no closing bracket) so it also matches
/// suffixed variants (a trailing colon and number). Assembled from fragments
/// so the trigger never appears in this source file.
pub fn incomplete_marker() -> String {
    join_two("[", "INCOMPLETE")
}

/// Session-drift marker prefix: the other agent-swarm checkpoint tag. A prefix
/// so it matches both the bare tag and suffixed variants (a trailing colon and
/// number).
pub fn drift_marker() -> String {
    join_two("[", "SESSION-DRIFT")
}

/// Work-in-progress / draft / stub checkpoint tags agent swarms leave on
/// half-finished commits. Bracket prefixes (no closing `]`) so suffixed
/// variants also match. Assembled from fragments so the literal tag never
/// appears in this source file (which would trip the gate on itself).
pub fn extra_drift_markers() -> Vec<String> {
    vec![
        join_two("[", "WIP"),
        join_two("[", "DRAFT"),
        join_two("[", "STUB"),
    ]
}
