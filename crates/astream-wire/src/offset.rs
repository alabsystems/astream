//! Per-partition log offsets, with checked arithmetic (no silent wrap).

/// A monotonic position within a single partition's log.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Offset(pub u64);

impl Offset {
    /// The first offset in any partition.
    pub const ZERO: Offset = Offset(0);

    /// The next offset, or `None` on `u64` overflow (never wraps silently).
    pub fn checked_next(self) -> Option<Offset> {
        self.0.checked_add(1).map(Offset)
    }

    /// `self - earlier`, the number of records in between, or `None` if
    /// `earlier > self`.
    pub fn delta_from(self, earlier: Offset) -> Option<u64> {
        self.0.checked_sub(earlier.0)
    }
}

impl From<u64> for Offset {
    fn from(v: u64) -> Self {
        Offset(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next_is_monotonic_and_checked() {
        assert_eq!(Offset::ZERO.checked_next(), Some(Offset(1)));
        assert_eq!(Offset(u64::MAX).checked_next(), None);
    }

    #[test]
    fn delta_is_directional() {
        assert_eq!(Offset(10).delta_from(Offset(4)), Some(6));
        assert_eq!(Offset(4).delta_from(Offset(10)), None);
        assert!(Offset(1) > Offset::ZERO);
    }
}
