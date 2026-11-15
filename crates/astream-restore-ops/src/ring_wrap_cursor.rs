// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Physical zero-padded history-ring wrap cursor matching `aterm-restore` step-record ring layout
//! (`wire.steps.torn-vs-fault`, `Astream.Restore.TlaRingWrapCursor`).

use astream_wire::steps::{encode_step, scan_steps_from, StepEnd};

#[cfg(clean_islands)]
#[path = "ring_wrap_cursor_island.rs"]
mod ring_wrap_cursor_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ring_phys_len_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ring_gen_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use ring_wrap_cursor_island::{ring_gen_advance, ring_phys_len_clamp};

/// Maximum physical capacity for a single per-tab crash-restore history ring (`4` MiB).
pub const MAX_RING_CAPACITY_BYTES: u64 = 4 * 1024 * 1024;

contract_fn! {
    /// Verified fit check (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ring_slot_valid_isl`.
    #[must_use]
    pub const fn ring_slot_valid(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

/// Zero-padded physical step-record ring buffer matching `aterm-restore`'s wrap semantics.
#[derive(Debug, Clone)]
pub struct RestoreStepRing {
    buf: Vec<u8>,
    write_pos: usize,
    wrap_generation: u64,
    head_base_step: u64,
    next_step: u64,
}

impl RestoreStepRing {
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        let clamped = ring_phys_len_clamp(capacity as u64, MAX_RING_CAPACITY_BYTES) as usize;
        let cap = if clamped < 64 {
            64
        } else if clamped > (MAX_RING_CAPACITY_BYTES as usize) {
            MAX_RING_CAPACITY_BYTES as usize
        } else {
            clamped
        };
        let mut buf = Vec::new();
        let zeroes = [0u8; 64];
        while buf.len().saturating_add(64) <= cap {
            buf.extend_from_slice(&zeroes);
        }
        while buf.len() < cap {
            buf.push(0);
        }
        Self {
            buf,
            write_pos: 0,
            wrap_generation: 0,
            head_base_step: 0,
            next_step: 0,
        }
    }

    #[must_use]
    pub const fn wrap_generation(&self) -> u64 {
        self.wrap_generation
    }

    /// Appends one step record; if insufficient room remains at physical tail, zeroes the
    /// trailing gap (`Torn` + all-zero tail rule!) and wraps cleanly to physical offset `0`.
    pub fn append_body(&mut self, body: &[u8]) -> Result<u64, &'static str> {
        let step = self.next_step;
        let framed = match encode_step(step, body) {
            Ok(f) => f,
            Err(_) => return Err("step encode failed"),
        };
        if !ring_slot_valid(self.buf.len() as u64, framed.len() as u64) {
            return Err("step exceeds whole ring capacity");
        }
        let rem = self.buf.len().saturating_sub(self.write_pos);
        if framed.len() > rem {
            self.buf.fill(0);
            self.write_pos = 0;
            self.head_base_step = step;
            self.wrap_generation =
                ring_gen_advance(self.wrap_generation, self.wrap_generation.saturating_add(1));
        }
        let end = self.write_pos.saturating_add(framed.len());
        let dst = match self.buf.get_mut(self.write_pos..end) {
            Some(s) => s,
            None => return Err("ring slice out of bounds"),
        };
        dst.copy_from_slice(&framed);
        if let Some(after) = self.buf.get_mut(end..) {
            // Zero-fill next frame header window so scanner sees zero gap above latest step!
            let z = if after.len() < 16 { after.len() } else { 16 };
            if let Some(zslice) = after.get_mut(..z) {
                zslice.fill(0);
            }
        }
        self.write_pos = end;
        self.next_step = self.next_step.saturating_add(1);
        Ok(step)
    }

    /// Scans the active generation from physical `0` using `astream_wire::steps::scan_steps_from`.
    pub fn recover_active_run(&self) -> Result<Vec<Vec<u8>>, &'static str> {
        let scan = scan_steps_from(&self.buf, self.head_base_step);
        match scan.end {
            StepEnd::Clean => {}
            StepEnd::Torn => {
                let tail: &[u8] = match self.buf.get(scan.valid_len..) {
                    Some(t) => t,
                    None => &[],
                };
                for &b in tail {
                    if b != 0 {
                        return Err("non-zero bytes after torn ring end");
                    }
                }
            }
            StepEnd::Fault { .. } => return Err("corrupt step record in ring"),
        }
        let mut out = Vec::new();
        for s in scan.steps {
            let slice = match self.buf.get(s.1) {
                Some(sl) => sl,
                None => return Err("bad step range"),
            };
            let mut body_copy = Vec::new();
            body_copy.extend_from_slice(slice);
            out.push(body_copy);
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_ring_zero_pads_physical_tail_wraps_and_scans_back_cleanly() {
        let mut ring = RestoreStepRing::new(96);
        assert_eq!(ring.append_body(b"first-chunk").unwrap(), 0);
        assert_eq!(ring.append_body(b"second-chunk").unwrap(), 1);
        // Third chunk forces wrap to physical 0 with zeroed tail!
        assert_eq!(ring.append_body(b"third-chunk").unwrap(), 2);
        assert_eq!(ring.wrap_generation(), 1);
        assert_eq!(
            ring.recover_active_run().unwrap(),
            vec![b"third-chunk".to_vec()]
        );
    }
}
