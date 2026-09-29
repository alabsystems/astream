//! Lint search strings ("needles") assembled from fragments.
//!
//! The merge gate scans source files for things like checkpoint markers and
//! cfg-feature references. If this crate's own source contained those exact
//! strings as literals, the gate would flag itself. So every needle is built
//! at runtime from pieces that, on disk, never form the contiguous trigger.
//! A meta-test (`gate_passes_on_the_real_repo`) proves this works by running
//! the gate against astream's own tree and asserting zero findings.

/// Unlinked task marker (assembled so the literal never appears here).
pub fn task_marker() -> String {
    format!("{}{}", "TO", "DO")
}

/// "Fix-me" marker, assembled from fragments.
pub fn fixme_marker() -> String {
    format!("{}{}", "FIX", "ME")
}

/// Incomplete-checkpoint marker prefix: the bracketed tag agent swarms leave
/// on half-finished commits. A prefix (no closing bracket) so it also matches
/// suffixed variants (a trailing colon and number). Assembled from fragments
/// so the trigger never appears in this source file.
pub fn incomplete_marker() -> String {
    format!("[{}", "INCOMPLETE")
}

/// Session-drift marker prefix: the other agent-swarm checkpoint tag. A prefix
/// so it matches both the bare tag and suffixed variants (a trailing colon and
/// number).
pub fn drift_marker() -> String {
    format!("[{}", "SESSION-DRIFT")
}

/// Work-in-progress / draft / stub checkpoint tags agent swarms leave on
/// half-finished commits. Bracket prefixes (no closing `]`) so suffixed
/// variants also match. Assembled from fragments so the literal tag never
/// appears in this source file (which would trip the gate on itself).
pub fn extra_drift_markers() -> Vec<String> {
    vec![
        format!("[{}", "WIP"),
        format!("[{}", "DRAFT"),
        format!("[{}", "STUB"),
    ]
}
