//! RFC 8878 Zstandard frame window & block-budget planner for `astream-kafka`.

#[cfg(clean_islands)]
#[path = "kafka_zstd_window_planner_island.rs"]
mod kafka_zstd_window_planner_island;
#[cfg(clean_islands)]
pub use kafka_zstd_window_planner_island::{zstd_block_len_clamp, zstd_decoded_total_advance};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn zstd_block_len_clamp(raw_len: u64) -> u64 {
    if raw_len < 131_072 {
        raw_len
    } else {
        131_072
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn zstd_decoded_total_advance(prev_total: u64, next_total: u64) -> u64 {
    if prev_total < next_total {
        next_total
    } else {
        prev_total
    }
}

contract_fn! {
    #[must_use]
    pub const fn zstd_window_admissible(window_bytes: u64, budget_bytes: u64) -> bool
    clauses [ensures result == (window_bytes <= budget_bytes)]
    {
        window_bytes <= budget_bytes
    }
}

pub const RFC8878_MAX_BLOCK_BYTES: u64 = 131_072;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ZstdBudgetError {
    WindowExceedsBudget {
        window_bytes: u64,
        budget_bytes: u64,
    },
    BlockExceedsRfc8878Max {
        raw_block_bytes: u64,
    },
    OutputExceedsCap {
        projected_bytes: u64,
        max_output_bytes: u64,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ZstdWindowPlanner {
    max_window_bytes: u64,
    max_output_bytes: u64,
    decoded_total: u64,
    last_block_len: u64,
}

impl ZstdWindowPlanner {
    #[must_use]
    pub const fn new(max_window_bytes: u64, max_output_bytes: u64) -> Self {
        Self {
            max_window_bytes,
            max_output_bytes,
            decoded_total: 0,
            last_block_len: 0,
        }
    }

    #[must_use]
    pub const fn max_window_bytes(&self) -> u64 {
        self.max_window_bytes
    }

    #[must_use]
    pub const fn max_output_bytes(&self) -> u64 {
        self.max_output_bytes
    }

    #[must_use]
    pub const fn decoded_total(&self) -> u64 {
        self.decoded_total
    }

    #[must_use]
    pub const fn last_block_len(&self) -> u64 {
        self.last_block_len
    }

    pub const fn check_window(&self, window_bytes: u64) -> Result<(), ZstdBudgetError> {
        if zstd_window_admissible(window_bytes, self.max_window_bytes) {
            Ok(())
        } else {
            Err(ZstdBudgetError::WindowExceedsBudget {
                window_bytes,
                budget_bytes: self.max_window_bytes,
            })
        }
    }

    pub fn admit_block(&mut self, raw_block_bytes: u64) -> Result<u64, ZstdBudgetError> {
        if raw_block_bytes > RFC8878_MAX_BLOCK_BYTES {
            return Err(ZstdBudgetError::BlockExceedsRfc8878Max { raw_block_bytes });
        }
        let clamped = zstd_block_len_clamp(raw_block_bytes);
        let projected = self.decoded_total.saturating_add(clamped);
        if !zstd_window_admissible(projected, self.max_output_bytes) {
            return Err(ZstdBudgetError::OutputExceedsCap {
                projected_bytes: projected,
                max_output_bytes: self.max_output_bytes,
            });
        }
        self.last_block_len = clamped;
        self.decoded_total = zstd_decoded_total_advance(self.decoded_total, projected);
        Ok(self.decoded_total)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_window_rfc8878_block_and_zip_bomb_output_caps() {
        let mut p = ZstdWindowPlanner::new(8 * 1024 * 1024, 256 * 1024);
        assert_eq!(p.max_window_bytes(), 8 * 1024 * 1024);
        assert_eq!(p.max_output_bytes(), 256 * 1024);
        assert_eq!(p.check_window(4 * 1024 * 1024), Ok(()));
        assert_eq!(
            p.check_window(16 * 1024 * 1024),
            Err(ZstdBudgetError::WindowExceedsBudget {
                window_bytes: 16 * 1024 * 1024,
                budget_bytes: 8 * 1024 * 1024,
            })
        );
        assert_eq!(
            p.admit_block(RFC8878_MAX_BLOCK_BYTES + 1),
            Err(ZstdBudgetError::BlockExceedsRfc8878Max {
                raw_block_bytes: RFC8878_MAX_BLOCK_BYTES + 1,
            })
        );
        assert_eq!(p.admit_block(131_072), Ok(131_072));
        assert_eq!(p.last_block_len(), 131_072);
        assert_eq!(p.admit_block(131_072), Ok(262_144));
        assert_eq!(p.decoded_total(), 262_144);
        assert_eq!(
            p.admit_block(1),
            Err(ZstdBudgetError::OutputExceedsCap {
                projected_bytes: 262_145,
                max_output_bytes: 262_144,
            })
        );
        assert_eq!(zstd_block_len_clamp(999_999), 131_072);
        assert_eq!(zstd_decoded_total_advance(10, 5), 10);
    }
}
