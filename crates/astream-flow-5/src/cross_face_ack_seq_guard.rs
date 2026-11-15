//! Cross-face `ACK_SEQ_BASE | offset` producer sequence guard (`broker.ack-key-is-one-wire-contract`).

#![allow(clippy::double_must_use)]

#[cfg(clean_islands)]
#[path = "cross_face_ack_seq_guard_island.rs"]
mod cross_face_ack_seq_guard_island;
#[cfg(clean_islands)]
pub use cross_face_ack_seq_guard_island::{ack_committed_cursor_advance, ack_input_offset_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn ack_input_offset_clamp(offset: u64) -> u64 {
    if offset < 9_223_372_036_854_775_807 {
        offset
    } else {
        9_223_372_036_854_775_807
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn ack_committed_cursor_advance(prev_cur: u64, next_cur: u64) -> u64 {
    if prev_cur < next_cur {
        next_cur
    } else {
        prev_cur
    }
}

contract_fn! {
    #[must_use]
    pub const fn ordinary_seq_below_ack_base(seq: u64) -> bool
    clauses [ensures result == ((seq < 9223372036854775808))]
    {
        seq < 9_223_372_036_854_775_808
    }
}

pub const ACK_SEQ_BASE: u64 = 1u64 << 63;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AckSeqError {
    OrdinarySeqInReservedAckSpace(u64),
    InputOffsetExceedsAckSpace(u64),
}

#[must_use]
pub const fn validate_ordinary_publish_seq(seq: u64) -> Result<u64, AckSeqError> {
    if ordinary_seq_below_ack_base(seq) {
        Ok(seq)
    } else {
        Err(AckSeqError::OrdinarySeqInReservedAckSpace(seq))
    }
}

#[must_use]
pub const fn derive_cross_face_ack_seq(input_offset: u64) -> Result<(u64, u64), AckSeqError> {
    if !ordinary_seq_below_ack_base(input_offset) || input_offset == (ACK_SEQ_BASE - 1) {
        return Err(AckSeqError::InputOffsetExceedsAckSpace(input_offset));
    }
    let clamped = ack_input_offset_clamp(input_offset);
    let ack_seq = ACK_SEQ_BASE | clamped;
    let next_group_cursor = ack_committed_cursor_advance(clamped, clamped.saturating_add(1));
    Ok((ack_seq, next_group_cursor))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn separates_ordinary_publish_and_ack_sequences_across_library_and_cli_faces() {
        assert_eq!(validate_ordinary_publish_seq(5), Ok(5));
        assert_eq!(
            validate_ordinary_publish_seq(ACK_SEQ_BASE | 5),
            Err(AckSeqError::OrdinarySeqInReservedAckSpace(ACK_SEQ_BASE | 5))
        );
        let (ack_seq, cursor) = derive_cross_face_ack_seq(5).unwrap();
        assert_eq!(ack_seq, ACK_SEQ_BASE | 5);
        assert_eq!(cursor, 6);
        assert_ne!(ack_seq, 5);
    }
}
