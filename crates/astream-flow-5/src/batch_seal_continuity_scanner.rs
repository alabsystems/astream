//! BREC v2 `0xB4` (`CONTINUES`) / `0xB5` (`SEAL(count)`) batch-tile continuity scanner.

#[cfg(clean_islands)]
#[path = "batch_seal_continuity_scanner_island.rs"]
mod batch_seal_continuity_scanner_island;
#[cfg(clean_islands)]
pub use batch_seal_continuity_scanner_island::{batch_seal_run_clamp, batch_sealed_head_advance};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn batch_seal_run_clamp(run_len: u64) -> u64 {
    if run_len < 65_536 {
        run_len
    } else {
        65_536
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn batch_sealed_head_advance(prev_head: u64, next_head: u64) -> u64 {
    if prev_head < next_head {
        next_head
    } else {
        prev_head
    }
}

contract_fn! {
    #[must_use]
    pub const fn batch_seal_matches_run(run_len: u64, declared_count: u64) -> bool
    clauses [ensures result == (run_len == declared_count)]
    {
        run_len == declared_count
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BatchMark {
    UnmarkedLegacy,
    Continues,
    Seal { count: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BatchScanError {
    SealCountMismatch { run_len: u64, declared_count: u32 },
    UnmarkedInsideOpenBatch,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BatchSealContinuityScanner {
    sealed_head: u64,
    batch_start_offset: u64,
    open_run_len: u64,
}

impl BatchSealContinuityScanner {
    #[must_use]
    pub const fn new(base_offset: u64) -> Self {
        Self {
            sealed_head: base_offset,
            batch_start_offset: base_offset,
            open_run_len: 0,
        }
    }

    /// Last fully sealed offset (`batch_start_offset` when an unsealed trailing batch is cut).
    #[must_use]
    pub const fn sealed_head(&self) -> u64 {
        self.sealed_head
    }

    #[must_use]
    pub const fn batch_start_offset(&self) -> u64 {
        self.batch_start_offset
    }

    #[must_use]
    pub const fn open_run_len(&self) -> u64 {
        self.open_run_len
    }

    #[must_use]
    pub const fn has_open_batch(&self) -> bool {
        self.open_run_len > 0
    }

    pub fn observe_record(&mut self, seq: u64, mark: BatchMark) -> Result<(), BatchScanError> {
        match mark {
            BatchMark::UnmarkedLegacy => {
                if self.open_run_len > 0 {
                    return Err(BatchScanError::UnmarkedInsideOpenBatch);
                }
                let next = seq.saturating_add(1);
                self.sealed_head = batch_sealed_head_advance(self.sealed_head, next);
                self.batch_start_offset = self.sealed_head;
                Ok(())
            }
            BatchMark::Continues => {
                if self.open_run_len == 0 {
                    self.batch_start_offset = seq;
                }
                self.open_run_len = batch_seal_run_clamp(self.open_run_len.saturating_add(1));
                Ok(())
            }
            BatchMark::Seal { count } => {
                let run = self.open_run_len.saturating_add(1);
                if count == 0 || !batch_seal_matches_run(run, count as u64) {
                    return Err(BatchScanError::SealCountMismatch {
                        run_len: run,
                        declared_count: count,
                    });
                }
                let next = seq.saturating_add(1);
                self.sealed_head = batch_sealed_head_advance(self.sealed_head, next);
                self.batch_start_offset = self.sealed_head;
                self.open_run_len = 0;
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tiles_sealed_batches_and_cuts_unsealed_trailing_continues_to_batch_start() {
        let mut s = BatchSealContinuityScanner::new(0);
        s.observe_record(0, BatchMark::Continues).unwrap();
        s.observe_record(1, BatchMark::Continues).unwrap();
        s.observe_record(2, BatchMark::Seal { count: 3 }).unwrap();
        assert_eq!(s.sealed_head(), 3);
        assert!(!s.has_open_batch());

        // Torn batch at offsets 3, 4 without final 0xB5 seal -> sealed_head stays at 3!
        s.observe_record(3, BatchMark::Continues).unwrap();
        s.observe_record(4, BatchMark::Continues).unwrap();
        assert!(s.has_open_batch());
        assert_eq!(s.sealed_head(), 3);
    }
}
