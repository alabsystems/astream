// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! How far a retention cut has taken an origin's records, kept after their dedup keys are gone.
//!
//! A relayed record is deduplicated on its origin's `(producer_id, producer_seq)`, and a signature
//! has no age: once a cut drops a record and its key, a carrier holding the old envelope could
//! have it appended again. So a cut raises, for each origin and subject it reached, the highest
//! sequence it dropped, and a relayed record at or below that floor answers as a duplicate.
//!
//! Floors are per subject because an origin's subjects travel different paths: a cut of its
//! metrics must not refuse its mail still on the way. The price is a record that arrives later
//! than a cut of a higher sequence of its own subject: it is not appended, since nothing here can
//! tell it from a replay.
//!
//! Only an origin has floors: a producer a signature has vouched for here (the log marks its first
//! relayed record, [`RELAY_MARK_SUBJECT`](crate::store::RELAY_MARK_SUBJECT)), or one whose key the
//! broker has held (a publish under it marks it the same way). So a log that never relays pays nothing, and a producer nothing can relay for
//! grows nothing. A floor is raised by whatever key an origin's id holds, signed or not, so a
//! relaying broker binds its grants (`p=`): a plain `Publish` under an origin's id, which an
//! unguarded broker or an unbound grant lets through, can raise a floor over that origin's own
//! records.
//!
//! A sequence names one record of one subject, the origin's own contract: the floor is per subject,
//! so the same sequence sealed on a second subject is another record to it.
//!
//! Subjects come and go, so each origin keeps at most [`SUBJECTS_PER_ORIGIN`] floors. Past that the
//! lowest floors, those of the subjects cut longest ago in the origin's order, fold into one
//! floor over all its subjects, and past [`MAX_ENCODED_BYTES`] altogether they fold sooner. Floors
//! live in the one frame of `<log>.state`, whose limit would otherwise stop the log's cuts.

use std::collections::HashMap;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "relay_island.rs"]
mod relay_island;
#[cfg(not(clean_islands))]
pub(crate) use crate::twins::relay_floor_admits;
#[cfg(all(
    not(clean_islands),
    any(test, all(feature = "retention", feature = "relay"))
))]
pub(crate) use crate::twins::relay_floor_raise;
#[cfg(clean_islands)]
pub(crate) use relay_island::relay_floor_admits;
#[cfg(all(
    clean_islands,
    any(test, all(feature = "retention", feature = "relay"))
))]
pub(crate) use relay_island::relay_floor_raise;

/// How many subjects' floors one origin keeps before the lowest fold together.
#[cfg(all(feature = "retention", feature = "relay"))]
pub(crate) const SUBJECTS_PER_ORIGIN: usize = 4096;

/// How many bytes every origin's floors may take in `<log>.state`.
#[cfg(all(feature = "retention", feature = "relay"))]
pub(crate) const MAX_ENCODED_BYTES: usize = 1 << 20;

/// One origin's floors.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct OriginFloor {
    /// The floor over every subject, once some have folded.
    wide: Option<u64>,
    subjects: HashMap<String, u64>,
}

/// Every origin's floors.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RelayFloors {
    origins: HashMap<u64, OriginFloor>,
}

impl RelayFloors {
    /// Whether this log knows no origin.
    #[cfg(feature = "retention")]
    pub(crate) fn is_empty(&self) -> bool {
        self.origins.is_empty()
    }

    /// Whether `producer_id` is an origin of this log.
    pub(crate) fn marked(&self, producer_id: u64) -> bool {
        self.origins.contains_key(&producer_id)
    }

    /// `producer_id` is an origin of this log.
    pub(crate) fn mark(&mut self, producer_id: u64) {
        self.origins.entry(producer_id).or_default();
    }

    /// Every origin of `other` is one of this log too.
    #[cfg(feature = "retention")]
    pub(crate) fn keep_origins_of(&mut self, other: &RelayFloors) {
        for &producer_id in other.origins.keys() {
            self.mark(producer_id);
        }
    }

    /// Whether a cut has passed `producer_seq` of `producer_id` on `subject`.
    pub(crate) fn passed(&self, producer_id: u64, subject: &str, producer_seq: u64) -> bool {
        let Some(origin) = self.origins.get(&producer_id) else {
            return false;
        };
        let floor = origin.subjects.get(subject).copied().max(origin.wide);
        floor.is_some_and(|f| relay_floor_admits(f, producer_seq) == 0)
    }

    /// A cut dropped `producer_seq` of `producer_id` on `subject`. A producer no signature or key
    /// has made an origin raises nothing.
    #[cfg(any(test, all(feature = "retention", feature = "relay")))]
    pub(crate) fn raise(&mut self, producer_id: u64, subject: &str, producer_seq: u64) {
        let Some(origin) = self.origins.get_mut(&producer_id) else {
            return;
        };
        match origin.subjects.get_mut(subject) {
            Some(floor) => *floor = relay_floor_raise(*floor, producer_seq),
            None => {
                origin.subjects.insert(subject.to_owned(), producer_seq);
            }
        }
    }

    /// Fold each origin's lowest floors down to `cap` subjects, and to half as many until all of
    /// them fit `max_bytes`. A cut calls this once, after its last [`raise`](Self::raise).
    #[cfg(any(test, all(feature = "retention", feature = "relay")))]
    pub(crate) fn bound(&mut self, cap: usize, max_bytes: usize) {
        let mut cap = cap;
        self.fold_to(cap);
        while cap > 0 && self.encoded_bytes() > max_bytes {
            cap /= 2;
            self.fold_to(cap);
        }
    }

    #[cfg(any(test, all(feature = "retention", feature = "relay")))]
    fn fold_to(&mut self, cap: usize) {
        for origin in self.origins.values_mut() {
            let Some(over) = origin.subjects.len().checked_sub(cap).filter(|n| *n > 0) else {
                continue;
            };
            let mut lowest: Vec<(u64, String)> = origin
                .subjects
                .iter()
                .map(|(subject, &floor)| (floor, subject.clone()))
                .collect();
            lowest.sort_unstable();
            for (floor, subject) in lowest.into_iter().take(over) {
                origin.subjects.remove(&subject);
                origin.wide = origin.wide.max(Some(floor));
            }
        }
    }

    /// The length of [`encode`](Self::encode)'s form.
    #[cfg(any(test, all(feature = "retention", feature = "relay")))]
    fn encoded_bytes(&self) -> usize {
        let mut bytes = 4usize;
        for origin in self.origins.values() {
            bytes = bytes.saturating_add(8 + 1 + 8 + 4);
            for subject in origin.subjects.keys() {
                bytes = bytes.saturating_add(4 + subject.len() + 8);
            }
        }
        bytes
    }

    /// The encoded form in `<log>.state`, each map's entries sorted so that equal floors encode
    /// equally.
    #[cfg(feature = "retention")]
    pub(crate) fn encode(&self, out: &mut Vec<u8>) -> Option<()> {
        out.extend_from_slice(&u32::try_from(self.origins.len()).ok()?.to_le_bytes());
        let mut origins: Vec<_> = self.origins.iter().collect();
        origins.sort_unstable_by_key(|(id, _)| **id);
        for (id, origin) in origins {
            out.extend_from_slice(&id.to_le_bytes());
            match origin.wide {
                Some(wide) => {
                    out.push(1);
                    out.extend_from_slice(&wide.to_le_bytes());
                }
                None => out.push(0),
            }
            out.extend_from_slice(&u32::try_from(origin.subjects.len()).ok()?.to_le_bytes());
            let mut subjects: Vec<_> = origin.subjects.iter().collect();
            subjects.sort_unstable();
            for (subject, floor) in subjects {
                out.extend_from_slice(&u32::try_from(subject.len()).ok()?.to_le_bytes());
                out.extend_from_slice(subject.as_bytes());
                out.extend_from_slice(&floor.to_le_bytes());
            }
        }
        Some(())
    }

    /// Read what [`encode`](Self::encode) wrote at `*pos`.
    #[cfg(feature = "retention")]
    pub(crate) fn decode(bytes: &[u8], pos: &mut usize) -> Option<RelayFloors> {
        fn take<'a>(bytes: &'a [u8], pos: &mut usize, n: usize) -> Option<&'a [u8]> {
            let end = pos.checked_add(n)?;
            let taken = bytes.get(*pos..end)?;
            *pos = end;
            Some(taken)
        }
        fn u32_at(bytes: &[u8], pos: &mut usize) -> Option<u32> {
            Some(u32::from_le_bytes(take(bytes, pos, 4)?.try_into().ok()?))
        }
        fn u64_at(bytes: &[u8], pos: &mut usize) -> Option<u64> {
            Some(u64::from_le_bytes(take(bytes, pos, 8)?.try_into().ok()?))
        }
        let mut floors = RelayFloors::default();
        for _ in 0..u32_at(bytes, pos)? {
            let id = u64_at(bytes, pos)?;
            let wide = match take(bytes, pos, 1)?.first()? {
                0 => None,
                1 => Some(u64_at(bytes, pos)?),
                _ => return None,
            };
            let mut subjects = HashMap::new();
            for _ in 0..u32_at(bytes, pos)? {
                let len = usize::try_from(u32_at(bytes, pos)?).ok()?;
                let subject = core::str::from_utf8(take(bytes, pos, len)?).ok()?;
                subjects.insert(subject.to_owned(), u64_at(bytes, pos)?);
            }
            floors.origins.insert(id, OriginFloor { wide, subjects });
        }
        Some(floors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_floor_covers_its_origin_and_subject_up_to_its_sequence() {
        let mut floors = RelayFloors::default();
        floors.raise(7, "/m/a", 1);
        assert!(!floors.passed(7, "/m/a", 1), "not an origin: nothing rises");
        floors.mark(7);
        floors.raise(7, "/m/a", 10);
        floors.raise(7, "/m/a", 4);
        assert!(floors.passed(7, "/m/a", 10), "a cut sequence stays passed");
        assert!(floors.passed(7, "/m/a", 3), "and everything below it");
        assert!(!floors.passed(7, "/m/a", 11), "a newer one is not");
        assert!(!floors.passed(7, "/m/b", 3), "another subject is not");
        assert!(!floors.passed(8, "/m/a", 3), "another origin is not");
    }

    #[test]
    fn the_lowest_floors_fold_and_the_newest_stay_exact() {
        let mut floors = RelayFloors::default();
        floors.mark(7);
        for (subject, seq) in [("/a", 1), ("/b", 2), ("/c", 30), ("/d", 40)] {
            floors.raise(7, subject, seq);
        }
        floors.bound(2, usize::MAX);
        let origin = floors.origins.get(&7).unwrap();
        assert_eq!(origin.subjects.len(), 2);
        assert_eq!(origin.wide, Some(2));
        assert!(floors.passed(7, "/a", 1), "a folded subject stays covered");
        assert!(
            floors.passed(7, "/never-cut", 2),
            "the fold covers them all"
        );
        assert!(
            !floors.passed(7, "/never-cut", 3),
            "only up to its own floor"
        );
        assert!(floors.passed(7, "/c", 30), "a kept floor stays exact");
        assert!(!floors.passed(7, "/c", 31));
    }

    #[test]
    fn within_the_bound_nothing_folds() {
        let mut floors = RelayFloors::default();
        floors.mark(7);
        floors.raise(7, "/a", 1);
        floors.raise(7, "/b", 2);
        floors.bound(2, usize::MAX);
        assert_eq!(floors.origins.get(&7).unwrap().wide, None);
    }

    #[test]
    fn many_origins_fold_to_the_byte_bound_and_stay_covered() {
        let mut floors = RelayFloors::default();
        for id in 0..8 {
            floors.mark(id);
            for seq in 0..64 {
                floors.raise(id, &format!("/subject/{seq:0>40}"), seq);
            }
        }
        floors.bound(4096, 2048);
        assert!(floors.encoded_bytes() <= 2048, "{}", floors.encoded_bytes());
        for id in 0..8 {
            for seq in 0..64 {
                assert!(floors.passed(id, &format!("/subject/{seq:0>40}"), seq));
            }
        }
    }

    #[cfg(feature = "retention")]
    #[test]
    fn the_counted_length_is_never_below_the_encoded_one() {
        let mut floors = RelayFloors::default();
        floors.mark(7);
        floors.mark(9);
        floors.raise(7, "/a", 1);
        floors.raise(7, "/b", 2);
        floors.bound(1, usize::MAX);
        let mut bytes = Vec::new();
        floors.encode(&mut bytes).unwrap();
        assert!(bytes.len() <= floors.encoded_bytes());
    }

    #[cfg(feature = "retention")]
    #[test]
    fn the_encoded_form_reads_back_and_a_cut_short_one_is_refused() {
        let mut floors = RelayFloors::default();
        floors.mark(7);
        floors.mark(9);
        for (subject, seq) in [("/a", 1), ("/b", 2), ("/c", 3)] {
            floors.raise(7, subject, seq);
        }
        floors.raise(9, "/x", 5);
        floors.bound(2, usize::MAX);
        let mut bytes = Vec::new();
        floors.encode(&mut bytes).unwrap();
        let mut pos = 0;
        assert_eq!(RelayFloors::decode(&bytes, &mut pos), Some(floors));
        assert_eq!(pos, bytes.len());
        for cut in 0..bytes.len() {
            let mut pos = 0;
            assert_eq!(RelayFloors::decode(&bytes[..cut], &mut pos), None, "{cut}");
        }
    }
}
