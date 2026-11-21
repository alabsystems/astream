// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Multi-step `LastStep::Pending` subject retirement history gated on `visible_head`
//! (`Astream.Retire.TlaPendingRetire`).
//!
//! Generalizes single-retirement `Last` gating to an arbitrary bounded chain of interleaved
//! `publish(off_1) -> retire(off_2) -> publish(off_3) -> retire(off_4)` transitions while
//! `visible_head` lags behind `log_head` (during an Ordered escalated flush or Replicated
//! quorum wait):
//! - Queries at any `visible_head` return the exact `Some((record_offset, producer_id))` or
//!   `None` that was authoritative strictly below `visible_head` (`offset < visible_head`).
//! - `gc_settled_below(visible_head)` compacts superseded historical transitions while
//!   bounding retained history per subject via Clean-origin `retire_steps_clamp`.

use std::collections::{BTreeMap, VecDeque};

#[cfg(clean_islands)]
#[path = "pending_retire_island.rs"]
mod pending_retire_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn retire_steps_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn retire_step_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use pending_retire_island::{retire_step_advance, retire_steps_clamp};

/// Maximum uncommitted transition steps retained per subject before backpressure refusal.
pub const MAX_PENDING_RETIRE_STEPS: u64 = 16;

contract_fn! {
    /// Verified check (`threshold <= observed`), linked via `clean-kernel-defeq` to
    /// `retire_visible_isl`. Used as `retire_visible(visible_head, step_offset + 1)`
    /// (`step_offset < visible_head`).
    #[must_use]
    pub const fn retire_visible(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// One transition along a subject's `Last` lifecycle spine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubjectStep {
    /// Subject published/updated at `offset` with `charged_producer` owning the slot.
    Published { offset: u64, charged_producer: u64 },
    /// Subject retired at `offset` (`COMMIT_TAG_RETIRE`), releasing the slot once visible.
    Retired { offset: u64 },
}

impl SubjectStep {
    /// Log offset at which this transition was staged/appended.
    #[must_use]
    pub const fn offset(self) -> u64 {
        match self {
            Self::Published { offset, .. } | Self::Retired { offset } => offset,
        }
    }

    #[must_use]
    const fn is_visible_under(self, visible_head: u64) -> bool {
        match self.offset().checked_add(1) {
            Some(need) => retire_visible(visible_head, need),
            None => false,
        }
    }
}

/// Multi-step `Last` visibility ledger across subjects.
#[derive(Debug, Clone)]
pub struct PendingRetireHistory {
    max_steps_per_subject: u64,
    highest_offset: u64,
    timelines: BTreeMap<String, VecDeque<SubjectStep>>,
}

impl Default for PendingRetireHistory {
    fn default() -> Self {
        Self::new()
    }
}

fn clone_str(s: &str) -> String {
    let mut out = String::new();
    out.push_str(s);
    out
}

impl PendingRetireHistory {
    /// Constructs a history ledger bounded by [`MAX_PENDING_RETIRE_STEPS`] per subject.
    #[must_use]
    pub fn new() -> Self {
        Self::with_step_bound(MAX_PENDING_RETIRE_STEPS)
    }

    /// Constructs a history ledger with explicit per-subject bound (clamped to [`MAX_PENDING_RETIRE_STEPS`]).
    #[must_use]
    pub fn with_step_bound(bound: u64) -> Self {
        let cap = retire_steps_clamp(bound, MAX_PENDING_RETIRE_STEPS);
        Self {
            max_steps_per_subject: if cap == 0 { 1 } else { cap },
            highest_offset: 0,
            timelines: BTreeMap::new(),
        }
    }

    /// Number of subjects currently tracked.
    #[must_use]
    pub fn len(&self) -> usize {
        self.timelines.len()
    }

    /// Returns `true` when no subjects are tracked.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.timelines.is_empty()
    }

    /// Records a publish on `subject` at strictly advancing `offset`.
    /// First publisher after absence (or after a retirement) becomes `charged_producer`;
    /// an update of an already-present subject keeps the introducing producer's charge!
    pub fn record_publish(
        &mut self,
        subject: &str,
        offset: u64,
        producer_id: u64,
    ) -> Result<u64, &'static str> {
        if subject.is_empty() {
            return Err("empty subject");
        }
        if !self.timelines.contains_key(subject) {
            self.timelines.insert(clone_str(subject), VecDeque::new());
        }
        let q = match self.timelines.get_mut(subject) {
            Some(deque) => deque,
            None => return Err("subject timeline missing"),
        };
        if let Some(last) = q.back() {
            if offset <= last.offset() {
                return Err("non-monotonic subject step offset");
            }
        }
        if (q.len() as u64) >= self.max_steps_per_subject {
            return Err("pending retire step history full; advance visible_head first");
        }
        let charged = match q.back() {
            Some(&SubjectStep::Published {
                charged_producer, ..
            }) => charged_producer,
            None | Some(&SubjectStep::Retired { .. }) => producer_id,
        };
        q.push_back(SubjectStep::Published {
            offset,
            charged_producer: charged,
        });
        self.highest_offset = retire_step_advance(self.highest_offset, offset);
        Ok(charged)
    }

    /// Records a retirement on `subject` at strictly advancing `offset`, requiring `producer_id`
    /// to match the currently charged owner at the log head.
    pub fn record_retire(
        &mut self,
        subject: &str,
        offset: u64,
        producer_id: u64,
    ) -> Result<(), &'static str> {
        let q = match self.timelines.get_mut(subject) {
            Some(deque) => deque,
            None => return Err("subject not present"),
        };
        let charged = match q.back() {
            Some(&SubjectStep::Published {
                offset: prev,
                charged_producer,
            }) => {
                if offset <= prev {
                    return Err("non-monotonic retire offset");
                }
                charged_producer
            }
            _ => return Err("subject already retired at head"),
        };
        if charged != producer_id {
            return Err("producer is not charged owner of subject");
        }
        if (q.len() as u64) >= self.max_steps_per_subject {
            return Err("pending retire step history full");
        }
        q.push_back(SubjectStep::Retired { offset });
        self.highest_offset = retire_step_advance(self.highest_offset, offset);
        Ok(())
    }

    /// Resolves `Last` state `(offset, charged_producer)` as of `visible_head`
    /// (considering only steps with `step.offset() < visible_head`).
    #[must_use]
    pub fn resolve_at(&self, subject: &str, visible_head: u64) -> Option<(u64, u64)> {
        let q = self.timelines.get(subject)?;
        let mut latest_vis: Option<SubjectStep> = None;
        for &step in q {
            if step.is_visible_under(visible_head) {
                latest_vis = Some(step);
            } else {
                break;
            }
        }
        match latest_vis {
            Some(SubjectStep::Published {
                offset,
                charged_producer,
            }) => Some((offset, charged_producer)),
            _ => None,
        }
    }

    /// Compacts settled historical steps once `visible_head` advances: keeps at most the
    /// newest visible step (dropping it entirely if it is `Retired` with nothing pending above!)
    /// plus any still-unvisible steps `>= visible_head`.
    pub fn gc_settled_below(&mut self, visible_head: u64) {
        let mut empty_keys: Vec<String> = Vec::new();
        for (subj, q) in &mut self.timelines {
            while let Some(&second) = q.get(1) {
                if second.is_visible_under(visible_head) {
                    q.pop_front();
                } else {
                    break;
                }
            }
            if q.len() == 1 {
                if let Some(&SubjectStep::Retired { .. }) = q.front() {
                    if let Some(&front) = q.front() {
                        if front.is_visible_under(visible_head) {
                            q.pop_front();
                        }
                    }
                }
            }
            if q.is_empty() {
                empty_keys.push(subj.clone());
            }
        }
        for key in empty_keys {
            self.timelines.remove(&key);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multi_step_pending_retire_gates_exact_visibility_at_every_watermark() {
        let mut h = PendingRetireHistory::new();
        // Interleaved chain while visible_head lags:
        // off 10: p1 introduces /f/a/s (charged=p1)
        // off 12: p2 updates /f/a/s (charged stays p1!)
        // off 14: p1 retires /f/a/s
        // off 17: p2 re-introduces /f/a/s (charged=p2!)
        // off 20: p2 retires /f/a/s
        assert_eq!(h.record_publish("/f/a/s", 10, 1).unwrap(), 1);
        assert_eq!(h.record_publish("/f/a/s", 12, 2).unwrap(), 1);
        assert!(h.record_retire("/f/a/s", 13, 2).is_err()); // p2 not charged!
        h.record_retire("/f/a/s", 14, 1).unwrap();
        assert_eq!(h.record_publish("/f/a/s", 17, 2).unwrap(), 2);
        h.record_retire("/f/a/s", 20, 2).unwrap();

        assert_eq!(h.resolve_at("/f/a/s", 10), None);
        assert_eq!(h.resolve_at("/f/a/s", 11), Some((10, 1)));
        assert_eq!(h.resolve_at("/f/a/s", 13), Some((12, 1)));
        assert_eq!(h.resolve_at("/f/a/s", 15), None); // retired at 14, 17 not yet visible!
        assert_eq!(h.resolve_at("/f/a/s", 18), Some((17, 2))); // re-introduced at 17, 20 not yet visible!
        assert_eq!(h.resolve_at("/f/a/s", 21), None); // retired at 20!

        h.gc_settled_below(18);
        assert_eq!(h.resolve_at("/f/a/s", 18), Some((17, 2)));
        assert_eq!(h.resolve_at("/f/a/s", 21), None);

        h.gc_settled_below(21);
        assert!(h.is_empty());
    }
}
