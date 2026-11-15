// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The tier a broker bench measures, shared by `broker_durability_bench` and
//! `broker_pipeline_bench` (each mounts this file with `#[path]`, so the two cannot
//! parse the knobs or name the metric differently):
//!
//! - [`tier_of`] reads `DURABILITY` and `HORIZON_MS` with ONE match into the label and
//!   the [`Durability`] that runs, refusing what it does not know (the caller exits 2);
//! - [`served_label`] names the tier the broker SERVED, read after the run, so an
//!   Ordered request served Strict (off Apple, off the boot volume, a barrier refused at
//!   the open) or latched to Strict mid-run prints a `strict` metric and a claim that
//!   reads the `ordered` one fails on its missing metric;
//! - [`horizon_mismatch`] refuses a run whose broker reports another horizon than the
//!   one asked for, so a knob that stopped reaching the broker cannot measure astream's
//!   default horizon under aterm's;
//! - [`full_flushes_per_sec`] is the half of the cost neither the device nor the host's
//!   load can raise: how many full flushes the process asked the OS for per second of
//!   the run, from `astream_sys::flush_tally`, which an Ordered horizon bounds by time (a
//!   count per ack would rise as a busy host lowered the rate) and Relaxed holds at none;
//! - [`barriers_per_sec`] is the same count for ordering barriers, which Relaxed holds
//!   at none too. The tally counts every flush call the broker makes into astream-sys,
//!   whether or not its own `Broker::flush_counts` counts it, and the broker makes all of
//!   them there (it is `forbid(unsafe_code)`, so a barrier has no other way out), so a
//!   flush of either kind on the Relaxed path is seen at any load. One made through
//!   `std::fs::File` directly, which can only be a full flush, is not, and
//!   `broker_relaxed_ratio_bench` sees that one instead.

use astream_broker::{Durability, ServedInfo, Tier};
use astream_sys::FlushTally;
use std::time::Duration;

/// The canonical lowercase tier name and the [`Durability`] it selects, from the raw
/// `DURABILITY` value and the raw `HORIZON_MS` (`None` when unset; empty or blank is
/// unset too, as `HORIZON_MS= <command>` says in a shell, so a claim command can clear a
/// horizon it would inherit). Label and durability come from one match, so they cannot
/// disagree, and nothing is defaulted silently:
///
/// - a tier other than `strict`, `ordered` or `relaxed` (case-insensitive, surrounding
///   whitespace trimmed) is refused, so a mistyped tier can never measure Relaxed and
///   report it under the Strict label;
/// - `ordered` without `HORIZON_MS` is astream's default horizon
///   ([`Durability::ordered`], one second); with it, that many milliseconds (0 being a
///   full flush after every batch, as the broker defines it);
/// - `HORIZON_MS` for another tier, or one that is not a whole number of milliseconds,
///   is refused rather than ignored, as `asb serve --horizon-ms` refuses it.
pub fn tier_of(raw: &str, horizon_ms: Option<&str>) -> Result<(&'static str, Durability), String> {
    let horizon = match horizon_ms {
        None => None,
        Some(h) if h.trim().is_empty() => None,
        Some(h) => match h.trim().parse::<u64>() {
            Ok(ms) => Some(Duration::from_millis(ms)),
            Err(_) => {
                return Err(format!(
                    "HORIZON_MS must be a whole number of milliseconds, got {h:?}"
                ))
            }
        },
    };
    match (raw.trim().to_ascii_lowercase().as_str(), horizon) {
        ("strict", None) => Ok(("strict", Durability::Strict)),
        ("relaxed", None) => Ok(("relaxed", Durability::Relaxed)),
        ("ordered", None) => Ok(("ordered", Durability::ordered())),
        ("ordered", Some(h)) => Ok(("ordered", Durability::Ordered { horizon: Some(h) })),
        ("strict" | "relaxed", Some(_)) => Err(format!(
            "HORIZON_MS applies to DURABILITY=ordered alone, got DURABILITY={raw:?}"
        )),
        _ => Err(format!(
            "DURABILITY must be `strict`, `ordered` or `relaxed`, got {raw:?}"
        )),
    }
}

/// The METRIC label of the tier `served` reports as in force. A tier this build does
/// not know is `other`, never the tier asked for, so a claim reading the asked tier's
/// metric finds none.
pub fn served_label(served: &ServedInfo) -> &'static str {
    match served.served {
        Tier::Strict => "strict",
        Tier::Ordered => "ordered",
        Tier::Relaxed => "relaxed",
        _ => "other",
    }
}

/// Why a broker serving Ordered does not run at the horizon `asked` selected, or `None`
/// when it does (or serves another tier, which keeps no horizon to compare). The broker
/// reports its horizon in whole milliseconds rounded up ([`ServedInfo::horizon_ms_of`]).
pub fn horizon_mismatch(asked: Durability, served: &ServedInfo) -> Option<String> {
    if served.served != Tier::Ordered {
        return None;
    }
    let Durability::Ordered { horizon } = asked else {
        return Some(format!("asked {asked:?}, but the broker serves Ordered"));
    };
    let want = horizon.map(ServedInfo::horizon_ms_of);
    if served.horizon_ms == want {
        None
    } else {
        Some(format!(
            "asked a horizon of {want:?} ms, the broker reports {:?} ms",
            served.horizon_ms
        ))
    }
}

/// Full flushes this process asked the OS for between `before` and `after`
/// (`astream_sys::flush_tally`), per second of `run`, the time between the two reads.
/// Strict reads its batch rate (one flush per batch, so its ack rate for a single
/// producer). Ordered without escalations reads what its horizon
/// asks for alone: the writer flushes in full once the horizon has passed since the
/// first ack no full flush covers, so two of its full flushes begin at least a horizon
/// apart and the first a horizon into the run, at most one per horizon of `run` — ten a
/// second at 100 ms — whatever a full flush costs and however busy the host is (a
/// slower run is a longer one, which only lowers the count). Ordered at a zero horizon,
/// a full flush after every batch, reads its batch rate as Strict does. Relaxed without
/// escalations reads none: an ack follows the page-cache write alone and the tier keeps
/// no horizon, so nothing the bench does asks for a full flush.
pub fn full_flushes_per_sec(before: FlushTally, after: FlushTally, run: Duration) -> f64 {
    per_sec(after.full.saturating_sub(before.full), run)
}

/// Ordering barriers (`F_BARRIERFSYNC`) this process asked the OS for between `before`
/// and `after`, per second of `run`. Ordered reads its batch rate (one barrier per
/// batch). Strict reads none (each batch is flushed in full instead), and so does
/// Relaxed, whose ack follows the page-cache write alone, so a barrier on the Relaxed
/// path reads that path's batch rate, however busy the host is.
pub fn barriers_per_sec(before: FlushTally, after: FlushTally, run: Duration) -> f64 {
    per_sec(after.barrier.saturating_sub(before.barrier), run)
}

/// `count` per second of `run`. A run of no measurable length divides by a nanosecond
/// rather than by zero.
fn per_sec(count: u64, run: Duration) -> f64 {
    count as f64 / run.as_secs_f64().max(1e-9)
}

#[cfg(test)]
mod tests {
    use super::{barriers_per_sec, full_flushes_per_sec, horizon_mismatch, served_label, tier_of};
    use astream_broker::{Durability, ServedInfo, ServedReason, Tier};
    use astream_sys::FlushTally;
    use std::time::Duration;

    /// The METRIC label and the Durability that actually runs come from one match,
    /// so a Strict figure can never be published under the Relaxed label (or the
    /// reverse). Spelling is case-insensitive and surrounding whitespace is trimmed.
    #[test]
    fn the_label_and_the_durability_cannot_disagree() {
        assert_eq!(tier_of("strict", None), Ok(("strict", Durability::Strict)));
        assert_eq!(
            tier_of("  Strict\n", None),
            Ok(("strict", Durability::Strict))
        );
        assert_eq!(
            tier_of("RELAXED", None),
            Ok(("relaxed", Durability::Relaxed))
        );
        assert_eq!(
            tier_of(" ordered", None),
            Ok(("ordered", Durability::ordered()))
        );
    }

    /// HORIZON_MS sets the Ordered horizon, aterm's 100 ms among them, and zero is the
    /// broker's own "a full flush after every batch", not "no horizon".
    #[test]
    fn horizon_ms_sets_the_ordered_horizon() {
        assert_eq!(
            tier_of("ordered", Some("100")),
            Ok((
                "ordered",
                Durability::Ordered {
                    horizon: Some(Duration::from_millis(100))
                }
            ))
        );
        assert_eq!(
            tier_of("Ordered", Some(" 0 ")),
            Ok((
                "ordered",
                Durability::Ordered {
                    horizon: Some(Duration::ZERO)
                }
            ))
        );
    }

    /// An unrecognized DURABILITY is REJECTED (the caller exits 2), never silently
    /// measured as Relaxed and reported under whatever label was asked for; so is a
    /// horizon for a tier that keeps none, or one that is not a number.
    #[test]
    fn what_the_knobs_do_not_name_is_refused_not_defaulted() {
        for raw in ["bogus", "", "strictly"] {
            assert!(tier_of(raw, None).is_err(), "{raw:?}");
        }
        assert!(tier_of("strict", Some("100")).is_err());
        assert!(tier_of("relaxed", Some("100")).is_err());
        assert!(tier_of("bogus", Some("100")).is_err());
        for h in ["1s", "-1", "0.5", "100ms"] {
            assert!(tier_of("ordered", Some(h)).is_err(), "{h:?}");
        }
    }

    /// An empty HORIZON_MS is unset, as `HORIZON_MS= <command>` says in a shell, so a
    /// claim command can clear a horizon it would otherwise inherit: the Strict and
    /// Relaxed commands still measure their tier, and Ordered keeps astream's default.
    #[test]
    fn an_empty_horizon_is_unset() {
        for h in ["", "  "] {
            assert_eq!(
                tier_of("strict", Some(h)),
                Ok(("strict", Durability::Strict))
            );
            assert_eq!(
                tier_of("relaxed", Some(h)),
                Ok(("relaxed", Durability::Relaxed))
            );
            assert_eq!(
                tier_of("ordered", Some(h)),
                Ok(("ordered", Durability::ordered()))
            );
        }
    }

    fn served(tier: Tier, horizon_ms: Option<u32>) -> ServedInfo {
        ServedInfo {
            requested: Tier::Ordered,
            served: tier,
            reason: ServedReason::None,
            horizon_ms,
            rules: 0,
        }
    }

    /// The label is the tier served, so an Ordered request served Strict prints a
    /// strict metric, and a tier this build does not know names none of the three.
    #[test]
    fn the_label_is_the_tier_served() {
        assert_eq!(served_label(&served(Tier::Ordered, Some(100))), "ordered");
        assert_eq!(served_label(&served(Tier::Strict, None)), "strict");
        assert_eq!(served_label(&served(Tier::Relaxed, None)), "relaxed");
        assert_eq!(served_label(&served(Tier::Other(9), None)), "other");
    }

    /// A broker serving Ordered at another horizon than the one asked for is named, and
    /// so is one serving Ordered where no Ordered was asked; a broker serving another
    /// tier has no horizon to compare.
    #[test]
    fn a_horizon_the_broker_does_not_run_is_named() {
        let at_100 = Durability::Ordered {
            horizon: Some(Duration::from_millis(100)),
        };
        assert_eq!(
            horizon_mismatch(at_100, &served(Tier::Ordered, Some(100))),
            None
        );
        assert!(horizon_mismatch(at_100, &served(Tier::Ordered, Some(1000))).is_some());
        assert!(horizon_mismatch(at_100, &served(Tier::Ordered, None)).is_some());
        assert_eq!(
            horizon_mismatch(Durability::ordered(), &served(Tier::Ordered, Some(1000))),
            None
        );
        let none = Durability::Ordered { horizon: None };
        assert_eq!(horizon_mismatch(none, &served(Tier::Ordered, None)), None);
        assert_eq!(horizon_mismatch(at_100, &served(Tier::Strict, None)), None);
        assert!(horizon_mismatch(Durability::Strict, &served(Tier::Ordered, Some(100))).is_some());
    }

    /// The count takes only the full flushes between the two reads, per second of the
    /// run between them, so the same flushes over a longer run read lower: a host that
    /// slows the run lowers the count, where a count per ack would rise as the rate
    /// fell. A run of no measurable length divides by a nanosecond rather than by zero,
    /// so a flush in it reads far above any ceiling.
    #[test]
    fn the_flush_count_is_per_second_of_the_run() {
        let at = |full| FlushTally {
            full,
            ..FlushTally::default()
        };
        let secs = Duration::from_secs;
        assert_eq!(full_flushes_per_sec(at(1), at(11), secs(2)), 5.0);
        assert_eq!(full_flushes_per_sec(at(1), at(11), secs(4)), 2.5);
        assert_eq!(full_flushes_per_sec(at(3), at(3), secs(1)), 0.0);
        assert_eq!(full_flushes_per_sec(at(3), at(3), Duration::ZERO), 0.0);
        assert!(full_flushes_per_sec(at(3), at(4), Duration::ZERO) > 1e6);
    }

    /// Each count reads its own kind alone: barriers never raise the full-flush count and
    /// full flushes never raise the barrier count, so the Relaxed ceilings each see the
    /// flush they gate, and a run that issued neither reads zero on both.
    #[test]
    fn each_count_reads_its_own_kind() {
        let at = |barrier, full| FlushTally {
            full,
            barrier,
            plain: 0,
        };
        let secs = Duration::from_secs;
        assert_eq!(barriers_per_sec(at(2, 0), at(12, 0), secs(2)), 5.0);
        assert_eq!(full_flushes_per_sec(at(2, 0), at(12, 0), secs(2)), 0.0);
        assert_eq!(barriers_per_sec(at(0, 2), at(0, 12), secs(2)), 0.0);
        assert_eq!(full_flushes_per_sec(at(0, 2), at(0, 12), secs(2)), 5.0);
        assert_eq!(barriers_per_sec(at(4, 4), at(4, 4), secs(1)), 0.0);
        assert_eq!(full_flushes_per_sec(at(4, 4), at(4, 4), secs(1)), 0.0);
        assert!(barriers_per_sec(at(3, 0), at(4, 0), Duration::ZERO) > 1e6);
    }
}
