// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! aterm's retention rules as the tests that run them read them: from
//! `tests/fixtures/aterm-broker.retain` (`parse_rules`), the rules file aterm-link's
//! `astream_fixture_tests` holds equal to its `broker_rules::default_rules`, and from
//! `tests/fixtures/aterm-mesh-bus.retain`, the mesh bus log's (`broker_rules::mesh_rules`),
//! at byte bounds scaled down so a test's records reach them. `aterm_retention` and
//! `retention_planner` take them from here, so no test of this tree keeps a copy of aterm's
//! rules that could drift from what aterm runs. (aterm's escalation table and horizon are
//! `guarded_durability`'s `aterm_table` and `aterm_horizon`, from
//! `tests/fixtures/aterm-broker.escalate`.)

#![cfg(all(
    feature = "retention",
    any(debug_assertions, all(unix, feature = "cap"))
))]

use astream_broker::{parse_rules, Class, Retention, Rule};

/// aterm's four retention rules, as a rules file.
pub(super) const ATERM_RETAIN: &str = include_str!("../fixtures/aterm-broker.retain");

/// The five rules of the bus log aterm's node service hosts with the mesh on (aterm-link
/// `broker_rules::mesh_rules`), as a rules file: `ATERM_RETAIN`'s with one more before its
/// mail rule, the alab fleet's mail, which a second reader, the person carry's group,
/// holds too, and which forgets.
#[cfg(all(unix, feature = "cap"))]
pub(super) const MESH_RETAIN: &str = include_str!("../fixtures/aterm-mesh-bus.retain");

/// The rules of `text` (a rules file, `parse_rules`) with each byte bound scaled: the
/// prefix rule's to `ev`, a hold rule's that names a reader group (the mail lanes') to
/// `mail`, and the default rule's to `default`. Everything else is the file's: the order,
/// the filters, the classes, what each hold rule keeps, its readers and its age. A rule
/// with no byte bound keeps none.
///
/// # Panics
/// For a file that does not parse, and for a byte bound on a rule none of those three is
/// (a rule aterm added that no test has chosen a scale for), so a new rule of aterm's
/// is never run at its full bound by accident.
pub(super) fn scaled(text: &str, ev: u64, mail: u64, default: u64) -> Retention {
    let parsed = parse_rules(text).unwrap_or_else(|e| panic!("aterm's rules file: {e}"));
    let rules = parsed
        .rules()
        .iter()
        .map(|r| match (r.bytes(), r.class(), r.readers().is_empty()) {
            (None, _, _) => r.clone(),
            (Some(_), Class::Prefix, _) => r.clone().max_bytes(ev),
            (Some(_), Class::Hold, false) => r.clone().max_bytes(mail),
            (Some(_), Class::Hold, true) => panic!(
                "aterm's rule over {:?} has a byte bound no scale is chosen for",
                r.filter()
            ),
        })
        .collect::<Vec<Rule>>();
    let fallback = parsed.default_rule();
    let fallback = match fallback.bytes() {
        Some(_) => fallback.clone().max_bytes(default),
        None => fallback.clone(),
    };
    Retention::new(rules, fallback).unwrap_or_else(|e| panic!("aterm's rules, scaled: {e}"))
}
