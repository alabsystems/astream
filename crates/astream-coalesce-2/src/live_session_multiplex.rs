// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Fair deficit-round-robin (`DRR`) multi-session live frame multiplexer (`astream-live`).
//!
//! Schedules outbound terminal/agent observation frames across up to [`MAX_MUX_TABS`]
//! concurrent `aterm` tabs over a shared remote `aterm-link` stream so a chatty compiler
//! build in one tab never starves interactive keystrokes, `NEEDS YOU:` notifications, or
//! `survey` snapshots in peer tabs!
//! Zero closures, backed by Clean TLA+ island `Astream.Live.TlaLiveSessionMux`.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

use std::collections::VecDeque;

#[cfg(clean_islands)]
#[path = "live_session_multiplex_island.rs"]
mod live_session_multiplex_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn mux_deficit_clamp(proposed_deficit: u64, max_credit: u64) -> u64 {
    if proposed_deficit < max_credit {
        proposed_deficit
    } else {
        max_credit
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn mux_tabs_clamp(proposed_tabs: u64, max_tabs: u64) -> u64 {
    if proposed_tabs < max_tabs {
        proposed_tabs
    } else {
        max_tabs
    }
}
#[cfg(clean_islands)]
pub use live_session_multiplex_island::{mux_deficit_clamp, mux_tabs_clamp};

contract_fn! {
    /// Kernel-certified check that `frame_bytes` fits within a tab's accumulated deficit
    /// credit (`frame_bytes <= credit`), linked via `clean-kernel-defeq` to
    /// `mux_frame_fits_credit_isl`.
    #[must_use]
    pub const fn mux_frame_fits_credit(frame_bytes: u64, credit: u64) -> bool
    clauses [ensures result == (frame_bytes <= credit)]
    {
        frame_bytes <= credit
    }
}

/// Maximum concurrent live tabs multiplexed on a single [`LiveSessionMux`].
pub const MAX_MUX_TABS: usize = 256;
/// Maximum queued frames retained per tab before rejecting bulk backlog.
pub const MAX_TAB_QUEUE_FRAMES: usize = 512;

/// Queued outbound frame belonging to `tab_id`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MuxFrame {
    /// Session / tab identifier (`@<sid>`).
    pub tab_id: u64,
    /// Priority control flag (`true` for `NEEDS YOU:`, resize, or interactive input ack).
    pub urgent: bool,
    /// Encoded frame bytes.
    pub payload: Vec<u8>,
}

#[derive(Debug, Clone)]
struct TabSlot {
    tab_id: u64,
    deficit: u64,
    queue: VecDeque<MuxFrame>,
}

/// Error returned when registering or enqueueing onto [`LiveSessionMux`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiveMuxError {
    /// `tab_id == 0` is reserved.
    ZeroTabId,
    /// Active tab count reached `max_tabs`.
    TooManyTabs,
    /// Frame exceeds `max_credit` (cannot ever be scheduled).
    FrameExceedsMaxCredit { frame_bytes: usize, max_credit: u64 },
    /// Tab queue reached [`MAX_TAB_QUEUE_FRAMES`].
    TabQueueFull { tab_id: u64 },
}

/// Deficit-round-robin fair scheduler with urgent-control bypass across live `aterm` tabs.
#[derive(Debug, Clone)]
pub struct LiveSessionMux {
    quantum_bytes: u64,
    max_credit: u64,
    max_tabs: usize,
    cursor: usize,
    tabs: Vec<TabSlot>,
}

impl LiveSessionMux {
    /// Construct a [`LiveSessionMux`] with per-round `quantum_bytes` and `max_credit` ceiling.
    #[must_use]
    pub fn new(quantum_bytes: u64, max_credit: u64, max_tabs: usize) -> Self {
        let cap_tabs = mux_tabs_clamp(max_tabs as u64, MAX_MUX_TABS as u64) as usize;
        let q = if quantum_bytes > 1 { quantum_bytes } else { 1 };
        let credit_cap = if max_credit > q { max_credit } else { q };
        Self {
            quantum_bytes: q,
            max_credit: credit_cap,
            max_tabs: if cap_tabs > 1 { cap_tabs } else { 1 },
            cursor: 0,
            tabs: Vec::new(),
        }
    }

    /// Number of active registered tabs (`<= max_tabs`).
    #[must_use]
    pub fn active_tabs(&self) -> usize {
        self.tabs.len()
    }

    /// Enqueue `frame` onto its `tab_id` (auto-registering `tab_id` if room permits).
    pub fn enqueue(&mut self, frame: MuxFrame) -> Result<(), LiveMuxError> {
        if frame.tab_id == 0 {
            return Err(LiveMuxError::ZeroTabId);
        }
        if (frame.payload.len() as u64) > self.max_credit {
            return Err(LiveMuxError::FrameExceedsMaxCredit {
                frame_bytes: frame.payload.len(),
                max_credit: self.max_credit,
            });
        }
        let mut idx = None;
        let mut i = 0usize;
        let mut cur: &[TabSlot] = &self.tabs;
        while let [slot, rest @ ..] = cur {
            if slot.tab_id == frame.tab_id {
                idx = Some(i);
                break;
            }
            i = i.saturating_add(1);
            cur = rest;
        }
        let slot_idx = match idx {
            Some(found) => found,
            None => {
                let proposed = self.tabs.len().saturating_add(1) as u64;
                if mux_tabs_clamp(proposed, self.max_tabs as u64) < proposed {
                    return Err(LiveMuxError::TooManyTabs);
                }
                self.tabs.push(TabSlot {
                    tab_id: frame.tab_id,
                    deficit: 0,
                    queue: VecDeque::new(),
                });
                self.tabs.len().saturating_sub(1)
            }
        };
        let tab_id = frame.tab_id;
        let Some(slot) = self.tabs.get_mut(slot_idx) else {
            return Err(LiveMuxError::TooManyTabs);
        };
        if slot.queue.len() >= MAX_TAB_QUEUE_FRAMES {
            return Err(LiveMuxError::TabQueueFull { tab_id });
        }
        if frame.urgent {
            // Insert after any existing urgent frames at the head of this tab's queue
            // without calling `VecDeque::insert` (which carries an unproved OD-1 panic surface).
            let old = core::mem::take(&mut slot.queue);
            let mut rebuilt = std::collections::VecDeque::new();
            let mut pending = Some(frame);
            for existing in old {
                if !existing.urgent {
                    if let Some(urg) = core::mem::take(&mut pending) {
                        rebuilt.push_back(urg);
                    }
                }
                rebuilt.push_back(existing);
            }
            if let Some(urg) = core::mem::take(&mut pending) {
                rebuilt.push_back(urg);
            }
            slot.queue = rebuilt;
        } else {
            slot.queue.push_back(frame);
        }
        Ok(())
    }

    /// Pop the next fairly-scheduled [`MuxFrame`], prioritizing urgent control frames
    /// round-robin first, then standard Deficit Round Robin (`quantum_bytes` per pass).
    pub fn pop_next(&mut self) -> Option<MuxFrame> {
        let n = self.tabs.len();
        if n == 0 {
            return None;
        }
        // Pass 1: round-robin urgent control frames (`NEEDS YOU:`, resize, input acks).
        let base_cursor = if self.cursor < n { self.cursor } else { 0 };
        let mut u_step = 0usize;
        while u_step < n {
            let sum = base_cursor.saturating_add(u_step);
            let idx = if sum < n { sum } else { sum.saturating_sub(n) };
            if let Some(slot) = self.tabs.get_mut(idx) {
                let is_urgent = match slot.queue.front() {
                    Some(front) => front.urgent,
                    None => false,
                };
                if is_urgent {
                    let next_cur = idx.saturating_add(1);
                    self.cursor = if next_cur < n { next_cur } else { 0 };
                    return slot.queue.pop_front();
                }
            }
            u_step = u_step.saturating_add(1);
        }

        // Check whether ANY non-empty queue exists before running DRR quantum refill loops.
        let mut has_any = false;
        let mut cur_mut = self.tabs.as_mut_slice();
        while let [slot, rest @ ..] = cur_mut {
            if !slot.queue.is_empty() {
                has_any = true;
                break;
            }
            slot.deficit = 0;
            cur_mut = rest;
        }
        if !has_any {
            return None;
        }

        // Bounded DRR rounds: since every queued frame has `len <= max_credit` and each
        // full revolution adds `quantum_bytes >= 1`, `max_credit / quantum_bytes + 2`
        // revolutions is guaranteed to emit a frame.
        let q = if self.quantum_bytes > 1 {
            self.quantum_bytes
        } else {
            1
        };
        let div_q = match self.max_credit.checked_div(q) {
            Some(v) => v,
            None => 0,
        };
        let max_rounds = (div_q as usize).saturating_add(2);
        let mut round = 0usize;
        while round < max_rounds {
            let cur_base = if self.cursor < n { self.cursor } else { 0 };
            let mut step = 0usize;
            while step < n {
                let sum = cur_base.saturating_add(step);
                let idx = if sum < n { sum } else { sum.saturating_sub(n) };
                if let Some(slot) = self.tabs.get_mut(idx) {
                    let front_len_opt = match slot.queue.front() {
                        Some(f) => Some(f.payload.len() as u64),
                        None => None,
                    };
                    if let Some(front_len) = front_len_opt {
                        if step == 0 || !mux_frame_fits_credit(front_len, slot.deficit) {
                            let topped = slot.deficit.saturating_add(q);
                            slot.deficit = mux_deficit_clamp(topped, self.max_credit);
                        }
                        if mux_frame_fits_credit(front_len, slot.deficit) {
                            slot.deficit = slot.deficit.saturating_sub(front_len);
                            if slot.queue.len() == 1 {
                                slot.deficit = 0;
                            }
                            let next_cur = idx.saturating_add(1);
                            self.cursor = if next_cur < n { next_cur } else { 0 };
                            return slot.queue.pop_front();
                        }
                    } else {
                        slot.deficit = 0;
                    }
                }
                step = step.saturating_add(1);
            }
            round = round.saturating_add(1);
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn drr_prevents_noisy_tab_starvation_and_prioritizes_urgent_alerts() {
        let mut mux = LiveSessionMux::new(100, 1_000, 8);
        // Tab 1 spams five 80-byte bulk frames; Tab 2 sends one 40-byte prompt + one urgent alert.
        for i in 0..5u8 {
            mux.enqueue(MuxFrame {
                tab_id: 1,
                urgent: false,
                payload: vec![i; 80],
            })
            .unwrap();
        }
        mux.enqueue(MuxFrame {
            tab_id: 2,
            urgent: false,
            payload: vec![0xAA; 40],
        })
        .unwrap();
        mux.enqueue(MuxFrame {
            tab_id: 3,
            urgent: true,
            payload: b"NEEDS YOU: token".to_vec(),
        })
        .unwrap();

        // Urgent frame on Tab 3 preempts immediately!
        let f0 = mux.pop_next().unwrap();
        assert_eq!(f0.tab_id, 3);
        assert!(f0.urgent);

        // Next two pops interleave Tab 1 and Tab 2 rather than draining all 5 frames of Tab 1!
        let f1 = mux.pop_next().unwrap();
        let f2 = mux.pop_next().unwrap();
        assert!(
            (f1.tab_id == 1 && f2.tab_id == 2) || (f1.tab_id == 2 && f2.tab_id == 1),
            "got tabs ({}, {})",
            f1.tab_id,
            f2.tab_id
        );
    }
}
