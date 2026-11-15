//! Producer incarnation & reserved `will_seq` sequence allocator (`broker.will-fires-exactly-once`).

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

#[cfg(clean_islands)]
#[path = "will_incarnation_allocator_island.rs"]
mod will_incarnation_allocator_island;
#[cfg(clean_islands)]
pub use will_incarnation_allocator_island::{will_incarnation_advance, will_local_seq_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn will_incarnation_advance(prev_inc: u64, next_inc: u64) -> u64 {
    if prev_inc < next_inc {
        next_inc
    } else {
        prev_inc
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn will_local_seq_clamp(local_seq: u64) -> u64 {
    if local_seq < 4_294_967_294 {
        local_seq
    } else {
        4_294_967_294
    }
}

contract_fn! {
    #[must_use]
    pub const fn will_incarnation_valid(inc: u64) -> bool
    clauses [ensures result == ((inc < 2147483648))]
    {
        inc < 2_147_483_648
    }
}

pub const INCARNATION_MAX: u64 = 2_147_483_647;
pub const MAX_PUBLISH_WITHIN_INC: u64 = 0xFFFF_FFFE;
pub const WILL_LOW_WORD: u64 = 0xFFFF_FFFF;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WillIncarnationAllocator {
    incarnation: u64,
    next_local: u64,
}

impl WillIncarnationAllocator {
    #[must_use]
    pub const fn new(initial_incarnation: u64) -> Option<Self> {
        if !will_incarnation_valid(initial_incarnation) {
            return None;
        }
        Some(Self {
            incarnation: initial_incarnation,
            next_local: 1,
        })
    }

    #[must_use]
    pub const fn incarnation(&self) -> u64 {
        self.incarnation
    }

    #[must_use]
    pub const fn next_local(&self) -> u64 {
        self.next_local
    }

    /// Reserved sequence for this incarnation's `Will` (`(inc << 32) | 0xFFFF_FFFF`),
    /// guaranteed strictly above every ordinary publish in `self.incarnation` and strictly
    /// below every publish of `self.incarnation + 1`.
    #[must_use]
    pub const fn will_seq(&self) -> u64 {
        (self.incarnation << 32) | WILL_LOW_WORD
    }

    /// Advance to the next incarnation on reconnect, resetting `next_local = 1`.
    #[allow(clippy::question_mark)]
    pub fn advance_incarnation(&mut self) -> Option<u64> {
        let Some(candidate) = self.incarnation.checked_add(1) else {
            return None;
        };
        if !will_incarnation_valid(candidate) {
            return None;
        }
        self.incarnation = will_incarnation_advance(self.incarnation, candidate);
        self.next_local = 1;
        Some(self.incarnation)
    }

    /// Allocate the next ordinary publish sequence, rotating to `incarnation + 1`
    /// before touching `0xFFFF_FFFF` (`will_seq`).
    #[allow(clippy::question_mark)]
    pub fn next_publish_seq(&mut self) -> Option<u64> {
        if self.next_local > MAX_PUBLISH_WITHIN_INC && self.advance_incarnation().is_none() {
            return None;
        }
        let local = will_local_seq_clamp(self.next_local);
        let seq = (self.incarnation << 32) | local;
        self.next_local = self.next_local.saturating_add(1);
        Some(seq)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn newer_incarnation_publish_strictly_fences_prior_will_and_never_touches_ack_bit() {
        let mut a = WillIncarnationAllocator::new(0).unwrap();
        assert_eq!(a.incarnation(), 0);
        assert_eq!(a.next_local(), 1);
        let p0 = a.next_publish_seq().unwrap();
        let w0 = a.will_seq();
        assert!(p0 < w0);
        assert_eq!(a.advance_incarnation(), Some(1));
        let p1 = a.next_publish_seq().unwrap();
        assert!(
            w0 < p1,
            "new incarnation publish must fence prior incarnation will"
        );
        assert_eq!(
            p1 & (1u64 << 63),
            0,
            "ordinary publish never collides with ACK_SEQ_BASE"
        );
        assert!(WillIncarnationAllocator::new(INCARNATION_MAX + 1).is_none());
    }
}
