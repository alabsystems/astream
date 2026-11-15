// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Mergeable window summaries: the metric primitive for per-Mac statistics that a fleet
//! reads without polling anyone.
//!
//! Each Mac rolls its own raw events (the tokens one turn used, one stream's latency) into a
//! [`Summary`] per metric and aligned [`Window`], and writes it as its own row. Every
//! fleet-wide view (a total, a percentile, who is near a wall) is a merge computed locally,
//! from the replica, of each Mac's rows. Nothing polls and nothing is logged centrally.
//!
//! ## What a summary holds
//!
//! A [`Summary`] of a multiset of `u64` values (in the metric's unit: tokens, microseconds,
//! basis points) holds its count, its exact sum (`u128`), its exact minimum and maximum, and
//! a histogram over one fixed log-linear bucket layout:
//!
//! * values `0..=63` each have a bucket of their own;
//! * above that, each power-of-two range `[2^e, 2^(e+1))` (`e` from 6 to 63) is cut into
//!   `2^SUB_BUCKET_BITS` = 32 buckets of equal width `2^(e-5)`.
//!
//! That is [`BUCKET_COUNT`] = 1,920 buckets that tile `0..=u64::MAX` ([`bucket_index`],
//! [`bucket_bounds`]). The boundaries are the same in every build and on every Mac, so two
//! summaries' buckets line up one to one and merging adds counts: no re-binning, no
//! approximation beyond the bucket a value fell in.
//!
//! ### The quantile error bound
//!
//! Bucket counts are exact, so [`Summary::value_at_rank`] always finds the bucket that holds
//! the `r`-th smallest value `x`. It answers that bucket's integer midpoint clamped to the
//! summary's `[min, max]`. A bucket of width `w = 2^s` (`s ≥ 1`) starts at no less than
//! `32 · 2^s`, so the midpoint is at most `2^(s-1)` from any value in it:
//!
//! ```text
//! |estimate - x| ≤ x / 64        (relative error ≤ 2^-(SUB_BUCKET_BITS + 1) = 1.5625 %)
//! ```
//!
//! and the estimate is `x` itself when `x < 64` (unit-width buckets), when `r = 1` (the
//! exact minimum) and when `r = count` below a saturated count (the exact maximum). The
//! bound holds at every rank, saturated or not. [`QUANTILE_ERROR_DIVISOR`] names the 64. A
//! [`Quantile`] picks its rank by the nearest-rank rule, `max(1, ⌈q · count⌉)`, with `q` in
//! parts per million, so p50, p99 and p99.9 are integers and every Mac computes the same
//! rank. Merging never widens the bound: the merge of two summaries *is* the summary of the
//! union of their values.
//!
//! ## Merging: a commutative monoid, not a semilattice
//!
//! [`Summary::merge`] is associative and commutative, and [`Summary::new`] (the empty
//! summary) is its identity. Counts, sums and bucket counts add with saturation, which is
//! still associative and commutative on unsigned integers, so the laws hold exactly even at
//! the limits; no realistic metric reaches them (`u64::MAX` events, a `u128` sum).
//!
//! Merging is **not idempotent**: a summary merged with itself counts every value twice.
//! A replica that receives the same row twice, or receives a newer version of a row it
//! already holds, must not merge both. So every row has an identity, [`SummaryId`] (origin,
//! metric, window start, window length), and a revision its origin raises with each version
//! it writes. A reader keeps, per identity, only the version with the highest revision, and
//! merges across identities of one window length. [`Rollup`] is that reader. The origin is
//! the only writer of its rows and summarizes only its own events, so two identities of the
//! same window length never share an event, and a merge over one length counts each event
//! exactly once, whatever order, duplication or staleness the rows arrive with. An origin's
//! rows of different lengths (its minute rows and their hour roll-up) hold the same events,
//! so a reader never merges across lengths: [`Rollup::summarize`] reads exactly one.
//!
//! ## Windows
//!
//! A [`Window`] is aligned to Unix time (UTC): a [`WindowLen::Minute`], [`WindowLen::Hour`]
//! or [`WindowLen::Day`] starts at a multiple of its length, and a [`WindowLen::Week`] starts
//! on a Monday at 00:00 UTC (1970-01-05 was the first). Each length divides the next and the
//! week's offset is whole days, so every coarser window is the disjoint union of the finer
//! windows inside it, and rolling fine summaries up by merging ([`Window::coarsen`]) equals
//! summarizing the raw events in the coarse window directly. A span that no aligned window
//! names (a day in a local time zone, the last seven days) is the merge of the finer windows
//! that start inside it ([`Rollup::summarize`]). A reader bounds its memory per length
//! ([`Rollup::forget_before`]): minute rows for a day, hour rows for a week.
//!
//! ## Counters and gauges
//!
//! Two small companions cover what a window summary does not:
//!
//! * [`Counter`]: one origin's monotone total (tokens used since the store began). Versions
//!   of one origin's counter join by `max`, which *is* idempotent, so a duplicate or stale
//!   copy never inflates it; a fleet total is the sum of each origin's joined counter. An
//!   origin that lost its count resumes from its own replicated row; one that restarts at 0
//!   is hidden until it passes its old total (an undercount, never a double count).
//! * [`Gauge`]: one origin's latest reading and the time it was taken (quota percent now).
//!   Versions join by the later reading (`at_ms`, then `value`), also idempotent.
//!
//! ## The wire encoding
//!
//! Every encoding starts with a kind byte and a version byte, and every number after them is
//! an unsigned LEB128 varint. Decoding is strict: an unknown version, a different kind, a
//! truncation, trailing bytes, a non-minimal varint, or fields no multiset of values could
//! produce are refused ([`DecodeError`]), never misread, and every accepted byte string is
//! the one [`Summary::encode`] writes for its value (the encoding is canonical). The sum is
//! checked exactly while no bucket above 0 holds `u64::MAX` values; past that the true count
//! is unknown and only the least possible sum is enforced.
//!
//! ```text
//! Summary   'S' 1 | k | k × (index gap, count) | min | max | sum      (min.. only if k > 0)
//! Counter   'C' 1 | total
//! Gauge     'G' 1 | at_ms | value
//! SummaryId 'I' 1 | origin len (1) | origin | metric len (1) | metric | window tag (1) | index
//! ```
//!
//! A summary's `k` nonempty buckets are listed in ascending index order, each as the gap
//! from the previous bucket's index plus one (from 0 for the first) and its count; the count
//! itself is not stored, because it is the sum of the bucket counts. Sizes for the default
//! layout:
//!
//! * the empty summary is 3 bytes;
//! * each nonempty bucket costs 2 bytes while its count is below 128 and it lies within 128
//!   buckets of the previous one. Measured on the day of 96 agent turns in astream-wire's
//!   test suite (`tests/suite/summary.rs`): a one-turn minute row is at most 15 bytes, the
//!   day's output-token counts merge into 194 bytes (92 buckets) and its cache-read counts
//!   into 158 (72 buckets), and the day's [`SummaryId`] for a node-id origin and
//!   `tokens.output` is 39 bytes (the suite asserts each of these numbers);
//! * the largest possible encoding is [`MAX_SUMMARY_LEN`] = 21,154 bytes (every bucket
//!   nonempty with a count of `u64::MAX`), well under a frame's payload cap;
//! * in memory a summary is a fixed header plus 16 bytes per nonempty bucket on a 64-bit
//!   target.

use std::cmp::Ordering;
use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::Range;

// ---------------------------------------------------------------------------
// The bucket layout
// ---------------------------------------------------------------------------

/// Bits of linear subdivision per power of two: each range `[2^e, 2^(e+1))` above 63 is cut
/// into `2^SUB_BUCKET_BITS` buckets of equal width.
pub const SUB_BUCKET_BITS: u32 = 5;

/// Buckets per power-of-two range, and the number of unit-width buckets below them.
const SUB_BUCKETS: u64 = 1 << SUB_BUCKET_BITS;

/// The number of buckets in the layout: 32 unit buckets for `0..=31`, then 32 for each of
/// the 59 power-of-two ranges `[2^5, 2^6)` through `[2^63, 2^64)`.
pub const BUCKET_COUNT: u16 = ((64 - SUB_BUCKET_BITS + 1) as u16) << SUB_BUCKET_BITS;

/// A quantile read from a summary is within `x / QUANTILE_ERROR_DIVISOR` of the exact value
/// `x` at its rank: `2^(SUB_BUCKET_BITS + 1)`.
pub const QUANTILE_ERROR_DIVISOR: u64 = 1 << (SUB_BUCKET_BITS + 1);

/// The bucket a value falls in, `0..BUCKET_COUNT`.
#[must_use]
pub const fn bucket_index(value: u64) -> u16 {
    if value < SUB_BUCKETS {
        return value as u16;
    }
    // `value >= 32`, so its top set bit is at 5..=63 and `shift` is 0..=58.
    let top = 63u32.saturating_sub(value.leading_zeros());
    let shift = top.saturating_sub(SUB_BUCKET_BITS);
    // `value >> shift` keeps the top six bits: 32..=63.
    let sub = (value >> shift).saturating_sub(SUB_BUCKETS);
    let group = (shift as u64).saturating_add(1);
    (group.saturating_mul(SUB_BUCKETS).saturating_add(sub)) as u16
}

/// The inclusive value range `(low, high)` of a bucket, or `None` past the layout.
#[must_use]
pub const fn bucket_bounds(index: u16) -> Option<(u64, u64)> {
    if index >= BUCKET_COUNT {
        return None;
    }
    let index = index as u64;
    if index < SUB_BUCKETS {
        return Some((index, index));
    }
    // Group 1..=59 holds widths 2^0..=2^58.
    let shift = (index >> SUB_BUCKET_BITS).saturating_sub(1);
    let sub = index & (SUB_BUCKETS - 1);
    let low = (SUB_BUCKETS + sub) << shift;
    let width_less_one = (1u64 << shift).saturating_sub(1);
    Some((low, low.saturating_add(width_less_one)))
}

// ---------------------------------------------------------------------------
// Summary
// ---------------------------------------------------------------------------

/// One nonempty histogram bucket.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Bucket {
    index: u16,
    count: u64,
}

/// A mergeable summary of a multiset of `u64` values: count, exact sum, exact minimum and
/// maximum, and a fixed log-linear histogram (module docs).
///
/// Equal multisets give equal summaries. A summary has no public order: `Ord`'s by-value
/// `min` and `max` would shadow [`Summary::min`] and [`Summary::max`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Summary {
    /// `min(Σ bucket counts, u64::MAX)`.
    count: u64,
    /// The values' sum, saturating at `u128::MAX`.
    sum: u128,
    /// The smallest value; `u64::MAX` (the identity of `min`) when empty.
    min: u64,
    /// The largest value; `0` (the identity of `max`) when empty.
    max: u64,
    /// Nonempty buckets in strictly ascending index order.
    buckets: Vec<Bucket>,
}

impl Default for Summary {
    fn default() -> Self {
        Summary::new()
    }
}

impl Summary {
    /// The empty summary: the identity of [`Summary::merge`].
    #[must_use]
    pub const fn new() -> Summary {
        Summary {
            count: 0,
            sum: 0,
            min: u64::MAX,
            max: 0,
            buckets: Vec::new(),
        }
    }

    /// The summary of `values`.
    #[must_use]
    pub fn of(values: impl IntoIterator<Item = u64>) -> Summary {
        let mut summary = Summary::new();
        for value in values {
            summary.record(value);
        }
        summary
    }

    /// Add one occurrence of `value`.
    pub fn record(&mut self, value: u64) {
        self.record_n(value, 1);
    }

    /// Add `n` occurrences of `value`: the same summary as `n` calls to
    /// [`Summary::record`]. `n == 0` changes nothing.
    pub fn record_n(&mut self, value: u64, n: u64) {
        if n == 0 {
            return;
        }
        self.count = self.count.saturating_add(n);
        self.sum = self
            .sum
            .saturating_add(u128::from(value).saturating_mul(u128::from(n)));
        self.min = self.min.min(value);
        self.max = self.max.max(value);
        let index = bucket_index(value);
        match self
            .buckets
            .binary_search_by_key(&index, |bucket| bucket.index)
        {
            Ok(at) => {
                if let Some(bucket) = self.buckets.get_mut(at) {
                    bucket.count = bucket.count.saturating_add(n);
                }
            }
            Err(_) => {
                self.buckets = merge_buckets(&self.buckets, &[Bucket { index, count: n }]);
            }
        }
    }

    /// Merge `other` into `self`: afterwards `self` summarizes both multisets.
    ///
    /// Associative and commutative, with [`Summary::new`] as identity. **Not idempotent**:
    /// merging a summary with itself counts its values twice, so merge each event's row once:
    /// one version per identity, and rows of one window length only ([`Rollup`]).
    pub fn merge(&mut self, other: &Summary) {
        if other.count == 0 {
            return;
        }
        self.count = self.count.saturating_add(other.count);
        self.sum = self.sum.saturating_add(other.sum);
        self.min = self.min.min(other.min);
        self.max = self.max.max(other.max);
        self.buckets = merge_buckets(&self.buckets, &other.buckets);
    }

    /// `self` merged with `other`, by value.
    #[must_use]
    pub fn merged(mut self, other: &Summary) -> Summary {
        self.merge(other);
        self
    }

    /// How many values (saturating at `u64::MAX`).
    #[must_use]
    pub const fn count(&self) -> u64 {
        self.count
    }

    /// Whether the summary holds no value.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.count == 0
    }

    /// The exact sum of the values (saturating at `u128::MAX`).
    #[must_use]
    pub const fn sum(&self) -> u128 {
        self.sum
    }

    /// The exact smallest value, or `None` when empty.
    #[must_use]
    pub const fn min(&self) -> Option<u64> {
        if self.count == 0 {
            None
        } else {
            Some(self.min)
        }
    }

    /// The exact largest value, or `None` when empty.
    #[must_use]
    pub const fn max(&self) -> Option<u64> {
        if self.count == 0 {
            None
        } else {
            Some(self.max)
        }
    }

    /// The nonempty buckets as `(index, count)`, in ascending index order; see
    /// [`bucket_bounds`] for each one's value range.
    pub fn buckets(&self) -> impl Iterator<Item = (u16, u64)> + '_ {
        self.buckets
            .iter()
            .map(|bucket| (bucket.index, bucket.count))
    }

    /// An estimate of the `rank`-th smallest value (1-based), or `None` when `rank` is 0 or
    /// above the count. Within `x / 64` of the exact value `x` at every rank, saturated or
    /// not; exact for the first rank, for any `x < 64`, and for the last rank while the
    /// count is below `u64::MAX` (module docs). It never leaves `[min, max]`, and a higher
    /// rank never reads lower.
    #[must_use]
    pub fn value_at_rank(&self, rank: u64) -> Option<u64> {
        if rank == 0 || rank > self.count {
            return None;
        }
        if rank == 1 {
            return Some(self.min);
        }
        // A saturated count is not the true last rank, so the bucket walk answers it.
        if rank == self.count && self.count < u64::MAX {
            return Some(self.max);
        }
        let mut seen: u128 = 0;
        for bucket in &self.buckets {
            seen = seen.saturating_add(u128::from(bucket.count));
            if seen >= u128::from(rank) {
                let (low, high) = bucket_bounds(bucket.index)?;
                let middle = low.saturating_add(high.saturating_sub(low) / 2);
                return Some(middle.max(self.min).min(self.max));
            }
        }
        None
    }

    /// An estimate of quantile `q` by the nearest-rank rule, `max(1, ⌈q · count⌉)`; `None`
    /// when empty. [`Quantile::MIN`] is the exact minimum and [`Quantile::MAX`] the exact
    /// maximum; any other rank assumes the count has not saturated.
    #[must_use]
    pub fn quantile(&self, q: Quantile) -> Option<u64> {
        if q == Quantile::MAX {
            return self.max();
        }
        self.value_at_rank(q.rank(self.count))
    }

    /// The canonical encoding (module docs).
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.encoded_len().min(MAX_SUMMARY_LEN));
        self.encode_into(&mut out);
        out
    }

    /// Append the canonical encoding to `out`.
    pub fn encode_into(&self, out: &mut Vec<u8>) {
        out.push(KIND_SUMMARY);
        out.push(SUMMARY_VERSION);
        put_varint(out, self.buckets.len() as u128);
        let mut next: u64 = 0;
        for bucket in &self.buckets {
            let index = u64::from(bucket.index);
            put_varint(out, u128::from(index.saturating_sub(next)));
            put_varint(out, u128::from(bucket.count));
            next = index.saturating_add(1);
        }
        if !self.buckets.is_empty() {
            put_varint(out, u128::from(self.min));
            put_varint(out, u128::from(self.max));
            put_varint(out, self.sum);
        }
    }

    /// The length of [`Summary::encode`]'s output, at most [`MAX_SUMMARY_LEN`].
    #[must_use]
    pub fn encoded_len(&self) -> usize {
        let mut len = 2usize.saturating_add(varint_len(self.buckets.len() as u128));
        let mut next: u64 = 0;
        for bucket in &self.buckets {
            let index = u64::from(bucket.index);
            len = len
                .saturating_add(varint_len(u128::from(index.saturating_sub(next))))
                .saturating_add(varint_len(u128::from(bucket.count)));
            next = index.saturating_add(1);
        }
        if !self.buckets.is_empty() {
            len = len
                .saturating_add(varint_len(u128::from(self.min)))
                .saturating_add(varint_len(u128::from(self.max)))
                .saturating_add(varint_len(self.sum));
        }
        len
    }

    /// Decode a canonical encoding; anything else is refused.
    ///
    /// # Errors
    ///
    /// [`DecodeError`] for a different kind, an unknown version, a truncated or overlong
    /// input, a non-minimal or overflowing varint, a bucket list that is not strictly
    /// ascending within the layout or holds an empty bucket, or a minimum, maximum or sum no
    /// multiset of values in those buckets could have (for the sum, exactly while no bucket
    /// above 0 holds `u64::MAX` values; with one that does, a sum below the least possible).
    pub fn decode(bytes: &[u8]) -> Result<Summary, DecodeError> {
        let mut reader = Reader { rest: bytes };
        reader.header(KIND_SUMMARY, SUMMARY_VERSION)?;
        let listed = reader.varint_u64()?;
        if listed > u64::from(BUCKET_COUNT) {
            return Err(DecodeError::TooManyBuckets);
        }
        let mut buckets = Vec::with_capacity(listed as usize);
        let mut next: u64 = 0;
        let mut total: u128 = 0;
        for _ in 0..listed {
            let gap = reader.varint_u64()?;
            let index = match next.checked_add(gap) {
                Some(index) if index < u64::from(BUCKET_COUNT) => index,
                _ => return Err(DecodeError::BucketOutOfRange),
            };
            let count = reader.varint_u64()?;
            if count == 0 {
                return Err(DecodeError::EmptyBucket);
            }
            total = total.saturating_add(u128::from(count));
            buckets.push(Bucket {
                index: index as u16,
                count,
            });
            next = index.saturating_add(1);
        }
        if buckets.is_empty() {
            reader.finish()?;
            return Ok(Summary::new());
        }
        let min = reader.varint_u64()?;
        let max = reader.varint_u64()?;
        let sum = reader.varint_u128()?;
        reader.finish()?;
        let summary = Summary {
            count: u64::try_from(total).unwrap_or(u64::MAX),
            sum,
            min,
            max,
            buckets,
        };
        summary.check_fields()?;
        Ok(summary)
    }

    /// A total order consistent with `==`, for breaking a tie between two different
    /// summaries one writer published under one revision; it means nothing else.
    fn tie_order(&self, other: &Summary) -> Ordering {
        (self.count, self.sum, self.min, self.max, &self.buckets).cmp(&(
            other.count,
            other.sum,
            other.min,
            other.max,
            &other.buckets,
        ))
    }

    /// Refuse a nonempty summary whose extremes or sum no multiset of values in its buckets
    /// could have. While no bucket above 0 holds `u64::MAX` values the check is exact: it
    /// accepts precisely the summaries some multiset produces.
    fn check_fields(&self) -> Result<(), DecodeError> {
        let (Some(first), Some(last)) = (self.buckets.first(), self.buckets.last()) else {
            return Ok(());
        };
        let (first_low, first_high) =
            bucket_bounds(first.index).ok_or(DecodeError::BucketOutOfRange)?;
        let (last_low, last_high) =
            bucket_bounds(last.index).ok_or(DecodeError::BucketOutOfRange)?;
        if self.min < first_low || self.min > first_high {
            return Err(DecodeError::MinOutsideBucket);
        }
        if self.max < last_low || self.max > last_high {
            return Err(DecodeError::MaxOutsideBucket);
        }
        if self.min > self.max {
            return Err(DecodeError::MinAboveMax);
        }
        if self.count == 1 && self.min != self.max {
            return Err(DecodeError::ExtremesExceedCount);
        }
        let (low, high) = self.sum_bounds();
        if self.sum < low || high.is_some_and(|high| self.sum > high) {
            return Err(DecodeError::SumOutOfRange);
        }
        Ok(())
    }

    /// The least and greatest sum a multiset with these buckets, minimum and maximum can
    /// have. The minimum is one of the first bucket's values and the maximum one of the
    /// last's, and every other value lies anywhere in its bucket, so the sums form one
    /// integer interval. The upper end is `None` when a bucket other than 0 has saturated,
    /// because its true count, and so the most its values can add, is then unknown; the lower
    /// end stays a valid bound. Bucket 0 holds only zeros, so its count never moves the sum.
    fn sum_bounds(&self) -> (u128, Option<u128>) {
        let min = u128::from(self.min);
        let max = u128::from(self.max);
        let saturated = self
            .buckets
            .iter()
            .any(|bucket| bucket.count == u64::MAX && bucket.index != 0);
        let last_at = self.buckets.len().saturating_sub(1);
        let mut low: u128 = 0;
        let mut high: u128 = 0;
        if let [only] = self.buckets.as_slice() {
            let n = u128::from(only.count);
            if n == 1 {
                return (min, Some(min));
            }
            let others = n.saturating_sub(2);
            low = min
                .saturating_add(max)
                .saturating_add(others.saturating_mul(min));
            high = min
                .saturating_add(max)
                .saturating_add(others.saturating_mul(max));
        } else {
            for (at, bucket) in self.buckets.iter().enumerate() {
                let (bucket_low, bucket_high) = match bucket_bounds(bucket.index) {
                    Some((l, h)) => (u128::from(l), u128::from(h)),
                    None => continue,
                };
                let n = u128::from(bucket.count);
                let rest = n.saturating_sub(1);
                let (part_low, part_high) = if at == 0 {
                    (
                        n.saturating_mul(min),
                        min.saturating_add(rest.saturating_mul(bucket_high)),
                    )
                } else if at == last_at {
                    (
                        max.saturating_add(rest.saturating_mul(bucket_low)),
                        n.saturating_mul(max),
                    )
                } else {
                    (n.saturating_mul(bucket_low), n.saturating_mul(bucket_high))
                };
                low = low.saturating_add(part_low);
                high = high.saturating_add(part_high);
            }
        }
        (low, if saturated { None } else { Some(high) })
    }
}

/// The sorted union of two bucket lists, adding counts of shared indices.
fn merge_buckets(a: &[Bucket], b: &[Bucket]) -> Vec<Bucket> {
    let mut out = Vec::with_capacity(a.len().saturating_add(b.len()).min(BUCKET_COUNT as usize));
    let mut a = a.iter().peekable();
    let mut b = b.iter().peekable();
    loop {
        match (a.peek().copied(), b.peek().copied()) {
            (Some(x), Some(y)) => match x.index.cmp(&y.index) {
                Ordering::Less => {
                    out.push(*x);
                    a.next();
                }
                Ordering::Greater => {
                    out.push(*y);
                    b.next();
                }
                Ordering::Equal => {
                    out.push(Bucket {
                        index: x.index,
                        count: x.count.saturating_add(y.count),
                    });
                    a.next();
                    b.next();
                }
            },
            (Some(x), None) => {
                out.push(*x);
                a.next();
            }
            (None, Some(y)) => {
                out.push(*y);
                b.next();
            }
            (None, None) => return out,
        }
    }
}

/// The largest [`Summary::encode`] output: kind and version (2), the bucket count 1,920
/// (2), every bucket with a zero gap (1) and a count of `u64::MAX` (10), a minimum of 0 (1:
/// every bucket nonempty puts it in bucket 0), a maximum of `u64::MAX` (10) and a saturated
/// sum (19). Dropping a bucket to lengthen the minimum or a gap saves more than it costs.
pub const MAX_SUMMARY_LEN: usize = 2 + 2 + (BUCKET_COUNT as usize) * (1 + 10) + 1 + 10 + 19;

// ---------------------------------------------------------------------------
// Quantile
// ---------------------------------------------------------------------------

/// A quantile in parts per million, `0..=1_000_000`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Quantile(u32);

impl Quantile {
    /// The minimum (rank 1).
    pub const MIN: Quantile = Quantile(0);
    /// The median.
    pub const P50: Quantile = Quantile(500_000);
    /// The 90th percentile.
    pub const P90: Quantile = Quantile(900_000);
    /// The 95th percentile.
    pub const P95: Quantile = Quantile(950_000);
    /// The 99th percentile.
    pub const P99: Quantile = Quantile(990_000);
    /// The 99.9th percentile.
    pub const P999: Quantile = Quantile(999_000);
    /// The maximum (the last rank).
    pub const MAX: Quantile = Quantile(1_000_000);

    /// The quantile `ppm` parts per million, or `None` above one million.
    #[must_use]
    pub const fn per_million(ppm: u32) -> Option<Quantile> {
        if ppm > 1_000_000 {
            None
        } else {
            Some(Quantile(ppm))
        }
    }

    /// Parts per million.
    #[must_use]
    pub const fn as_per_million(self) -> u32 {
        self.0
    }

    /// The nearest rank of this quantile among `count` values, `max(1, ⌈ppm · count /
    /// 10^6⌉)`, or 0 when `count` is 0.
    #[must_use]
    pub const fn rank(self, count: u64) -> u64 {
        if count == 0 {
            return 0;
        }
        // At most 10^6 · (2^64 - 1) < 2^84, and the rank is at most `count`.
        let scaled = (self.0 as u128) * (count as u128);
        let rank = scaled.div_ceil(1_000_000) as u64;
        if rank == 0 {
            1
        } else {
            rank
        }
    }
}

// ---------------------------------------------------------------------------
// Windows
// ---------------------------------------------------------------------------

/// Monday 1970-01-05 00:00 UTC, in Unix milliseconds: where weeks are aligned.
const WEEK_OFFSET_MS: u64 = 4 * 86_400_000;

/// An aligned window's length. Each divides the next, finest first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WindowLen {
    /// 60 seconds, starting on a whole minute.
    Minute,
    /// 60 minutes, starting on a whole hour (UTC).
    Hour,
    /// 24 hours, starting at 00:00 UTC.
    Day,
    /// 7 days, starting on a Monday at 00:00 UTC.
    Week,
}

impl WindowLen {
    /// Every length, finest first.
    pub const ALL: [WindowLen; 4] = [
        WindowLen::Minute,
        WindowLen::Hour,
        WindowLen::Day,
        WindowLen::Week,
    ];

    /// The length in milliseconds.
    #[must_use]
    pub const fn millis(self) -> u64 {
        match self {
            WindowLen::Minute => 60_000,
            WindowLen::Hour => 3_600_000,
            WindowLen::Day => 86_400_000,
            WindowLen::Week => 604_800_000,
        }
    }

    /// Where this length's windows are aligned, in Unix milliseconds.
    const fn offset_ms(self) -> u64 {
        match self {
            WindowLen::Week => WEEK_OFFSET_MS,
            WindowLen::Minute | WindowLen::Hour | WindowLen::Day => 0,
        }
    }

    /// The wire tag, 1..=4, in the finest-first order.
    const fn tag(self) -> u8 {
        match self {
            WindowLen::Minute => 1,
            WindowLen::Hour => 2,
            WindowLen::Day => 3,
            WindowLen::Week => 4,
        }
    }

    const fn from_tag(tag: u8) -> Option<WindowLen> {
        match tag {
            1 => Some(WindowLen::Minute),
            2 => Some(WindowLen::Hour),
            3 => Some(WindowLen::Day),
            4 => Some(WindowLen::Week),
            _ => None,
        }
    }
}

/// An aligned window of Unix time `[start_ms, start_ms + len)`, UTC. Its end is always
/// representable; a window that would end past `u64::MAX` (or a week before the first
/// Monday of 1970) does not exist.
///
/// The derived order sorts by length first, then by start.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Window {
    len: WindowLen,
    start_ms: u64,
}

impl Window {
    /// The `index`-th window of length `len` since its alignment point.
    #[must_use]
    pub const fn from_index(len: WindowLen, index: u64) -> Option<Window> {
        let Some(from_offset) = index.checked_mul(len.millis()) else {
            return None;
        };
        let Some(start_ms) = from_offset.checked_add(len.offset_ms()) else {
            return None;
        };
        if start_ms.checked_add(len.millis()).is_none() {
            return None;
        }
        Some(Window { len, start_ms })
    }

    /// The window of length `len` that holds the instant `at_ms`.
    #[must_use]
    pub const fn containing(at_ms: u64, len: WindowLen) -> Option<Window> {
        let Some(from_offset) = at_ms.checked_sub(len.offset_ms()) else {
            return None;
        };
        Window::from_index(len, from_offset / len.millis())
    }

    /// The window of length `len` that starts at `start_ms`, if `start_ms` is aligned.
    #[must_use]
    pub const fn starting(start_ms: u64, len: WindowLen) -> Option<Window> {
        let Some(from_offset) = start_ms.checked_sub(len.offset_ms()) else {
            return None;
        };
        if from_offset % len.millis() != 0 {
            return None;
        }
        Window::from_index(len, from_offset / len.millis())
    }

    /// The window's length.
    #[must_use]
    pub const fn window_len(self) -> WindowLen {
        self.len
    }

    /// Its position since its alignment point: [`Window::from_index`]'s inverse.
    #[must_use]
    pub const fn index(self) -> u64 {
        self.start_ms.saturating_sub(self.len.offset_ms()) / self.len.millis()
    }

    /// The first instant in the window, Unix milliseconds.
    #[must_use]
    pub const fn start_ms(self) -> u64 {
        self.start_ms
    }

    /// The first instant after the window (exclusive end).
    #[must_use]
    pub const fn end_ms(self) -> u64 {
        self.start_ms.saturating_add(self.len.millis())
    }

    /// `start_ms..end_ms`.
    #[must_use]
    pub const fn span(self) -> Range<u64> {
        self.start_ms..self.end_ms()
    }

    /// Whether the instant `at_ms` lies in the window.
    #[must_use]
    pub const fn contains(self, at_ms: u64) -> bool {
        self.start_ms <= at_ms && at_ms < self.end_ms()
    }

    /// The window of length `len` that holds this one, or `None` when `len` is finer (or
    /// that window does not exist). Rolling summaries up along `coarsen` and merging equals
    /// summarizing the coarse window directly.
    #[must_use]
    pub const fn coarsen(self, len: WindowLen) -> Option<Window> {
        if len.tag() < self.len.tag() {
            return None;
        }
        Window::containing(self.start_ms, len)
    }

    /// The window after this one, if it exists.
    #[must_use]
    pub const fn next(self) -> Option<Window> {
        match self.index().checked_add(1) {
            Some(index) => Window::from_index(self.len, index),
            None => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Names and identity
// ---------------------------------------------------------------------------

/// The longest [`Origin`] or [`MetricName`], in bytes.
pub const MAX_NAME_LEN: usize = 64;

/// Why a string is not a valid [`Origin`] or [`MetricName`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NameError {
    /// No bytes.
    Empty,
    /// More than [`MAX_NAME_LEN`] bytes.
    TooLong,
    /// A byte outside printable ASCII, a space, or one of `/`, `*`, `>` (which astream
    /// subjects reserve).
    Byte(u8),
}

impl fmt::Display for NameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NameError::Empty => f.write_str("name is empty"),
            NameError::TooLong => write!(f, "name is longer than {MAX_NAME_LEN} bytes"),
            NameError::Byte(b) => write!(f, "name holds the byte 0x{b:02x}"),
        }
    }
}

impl std::error::Error for NameError {}

const fn name_byte_ok(b: u8) -> bool {
    b > b' ' && b < 0x7f && b != b'/' && b != b'*' && b != b'>'
}

fn check_name(name: &[u8]) -> Result<(), NameError> {
    if name.is_empty() {
        return Err(NameError::Empty);
    }
    if name.len() > MAX_NAME_LEN {
        return Err(NameError::TooLong);
    }
    match name.iter().find(|&&b| !name_byte_ok(b)) {
        Some(&b) => Err(NameError::Byte(b)),
        None => Ok(()),
    }
}

/// The Mac (or other writer) whose events a row summarizes and who alone writes it: a node
/// id such as `n-0123456789abcdef`, or a machine uuid. 1..=64 bytes of printable ASCII
/// other than space, `/`, `*` and `>`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Origin(Box<str>);

impl Origin {
    /// Validate `name` as an origin.
    ///
    /// # Errors
    ///
    /// [`NameError`] when `name` is empty, longer than [`MAX_NAME_LEN`] bytes, or holds a
    /// byte the grammar excludes.
    pub fn new(name: &str) -> Result<Origin, NameError> {
        check_name(name.as_bytes())?;
        Ok(Origin(name.into()))
    }

    /// The name.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Origin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// What a row measures, such as `tokens.output` or `stream.latency_us`; the same grammar
/// as [`Origin`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MetricName(Box<str>);

impl MetricName {
    /// Validate `name` as a metric name.
    ///
    /// # Errors
    ///
    /// [`NameError`] when `name` is empty, longer than [`MAX_NAME_LEN`] bytes, or holds a
    /// byte the grammar excludes.
    pub fn new(name: &str) -> Result<MetricName, NameError> {
        check_name(name.as_bytes())?;
        Ok(MetricName(name.into()))
    }

    /// The name.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for MetricName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// A summary row's identity: who wrote it, what it measures, and which window it covers.
/// One origin writes each identity, and identities of one window length never share an
/// event. Rows of different lengths for one origin and metric overlap by design (a roll-up),
/// so merge rows of one length only.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SummaryId {
    /// The writer, whose own events the row summarizes.
    pub origin: Origin,
    /// What the row measures.
    pub metric: MetricName,
    /// The window it covers.
    pub window: Window,
}

impl SummaryId {
    /// The canonical encoding (module docs).
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            5usize
                .saturating_add(self.origin.0.len())
                .saturating_add(self.metric.0.len())
                .saturating_add(varint_len(u128::from(self.window.index()))),
        );
        out.push(KIND_ID);
        out.push(SUMMARY_ID_VERSION);
        put_name(&mut out, &self.origin.0);
        put_name(&mut out, &self.metric.0);
        out.push(self.window.len.tag());
        put_varint(&mut out, u128::from(self.window.index()));
        out
    }

    /// Decode a canonical encoding; anything else is refused.
    ///
    /// # Errors
    ///
    /// [`DecodeError`] for a different kind, an unknown version, a truncated or overlong
    /// input, a non-minimal varint, an invalid name, or a window tag or index that names no
    /// window.
    pub fn decode(bytes: &[u8]) -> Result<SummaryId, DecodeError> {
        let mut reader = Reader { rest: bytes };
        reader.header(KIND_ID, SUMMARY_ID_VERSION)?;
        let origin = Origin(reader.name()?.into());
        let metric = MetricName(reader.name()?.into());
        let len = WindowLen::from_tag(reader.byte()?).ok_or(DecodeError::BadWindow)?;
        let index = reader.varint_u64()?;
        reader.finish()?;
        let window = Window::from_index(len, index).ok_or(DecodeError::BadWindow)?;
        Ok(SummaryId {
            origin,
            metric,
            window,
        })
    }
}

// ---------------------------------------------------------------------------
// Rollup: the reader that never double-counts
// ---------------------------------------------------------------------------

/// One version of a row: ordered by revision, then (to break a writer's tie) by
/// [`Summary::tie_order`].
#[derive(Clone, Debug, PartialEq, Eq)]
struct Version {
    revision: u64,
    summary: Summary,
}

impl Ord for Version {
    fn cmp(&self, other: &Version) -> Ordering {
        self.revision
            .cmp(&other.revision)
            .then_with(|| self.summary.tie_order(&other.summary))
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Version) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Rows by metric, then window length, then window start, then origin.
type Rows = BTreeMap<MetricName, BTreeMap<WindowLen, BTreeMap<u64, BTreeMap<Origin, Version>>>>;

/// What [`Rollup::offer`] did with a row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Offered {
    /// The first version of its identity this reader holds.
    Added,
    /// It replaced an older version of its identity.
    Replaced,
    /// The reader already holds this version or a newer one; nothing changed.
    Kept,
    /// Its window ended at or before the reader's horizon for its length
    /// ([`Rollup::forget_before`]); nothing changed.
    Expired,
}

/// A reader's replica of summary rows: per identity, the one version with the highest
/// revision (a tie broken by a fixed total order on summaries), merged across identities of
/// one window length on read.
///
/// Its state is a horizon per window length and, for each identity whose window ends after
/// its length's horizon, the newest version offered. Offering joins per identity,
/// forgetting raises a horizon (a `max`), and a window's end does not depend on its version,
/// so the state after any set of offers and forgets is the same in every order, and
/// repeating any of them changes nothing. A replica fed by any number of paths, with
/// duplicates and late stale copies, holds exactly each live identity's newest version.
#[derive(Clone, Debug, Default)]
pub struct Rollup {
    rows: Rows,
    len: usize,
    /// Per [`WindowLen`], finest first: rows ending at or before it are gone and refused.
    horizons: [u64; 4],
}

impl Rollup {
    /// An empty reader.
    #[must_use]
    pub const fn new() -> Rollup {
        Rollup {
            rows: BTreeMap::new(),
            len: 0,
            horizons: [0; 4],
        }
    }

    const fn slot(len: WindowLen) -> usize {
        match len {
            WindowLen::Minute => 0,
            WindowLen::Hour => 1,
            WindowLen::Day => 2,
            WindowLen::Week => 3,
        }
    }

    /// The instant at or before which rows of length `grain` have been forgotten and are
    /// refused; 0 until [`Rollup::forget_before`] raises it.
    #[must_use]
    pub fn horizon_ms(&self, grain: WindowLen) -> u64 {
        self.horizons.get(Rollup::slot(grain)).copied().unwrap_or(0)
    }

    /// Offer one version of a row. It is kept when its window ends after its length's
    /// horizon and its identity is new here, or when `(revision, summary)` is greater than
    /// the held version's; its origin raises `revision` with every version it writes (its
    /// own log offset will do).
    pub fn offer(&mut self, id: SummaryId, revision: u64, summary: Summary) -> Offered {
        if id.window.end_ms() <= self.horizon_ms(id.window.len) {
            return Offered::Expired;
        }
        let SummaryId {
            origin,
            metric,
            window,
        } = id;
        let by_origin = self
            .rows
            .entry(metric)
            .or_default()
            .entry(window.len)
            .or_default()
            .entry(window.start_ms)
            .or_default();
        let offered = Version { revision, summary };
        match by_origin.entry(origin) {
            Entry::Vacant(slot) => {
                slot.insert(offered);
                self.len = self.len.saturating_add(1);
                Offered::Added
            }
            Entry::Occupied(mut held) => {
                if offered > *held.get() {
                    held.insert(offered);
                    Offered::Replaced
                } else {
                    Offered::Kept
                }
            }
        }
    }

    /// The version held for `id`: its revision and summary.
    #[must_use]
    pub fn get(&self, id: &SummaryId) -> Option<(u64, &Summary)> {
        let version = self
            .rows
            .get(&id.metric)?
            .get(&id.window.len)?
            .get(&id.window.start_ms)?
            .get(&id.origin)?;
        Some((version.revision, &version.summary))
    }

    /// How many identities the reader holds.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether the reader holds no row.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn versions(
        &self,
        metric: &MetricName,
        grain: WindowLen,
        span: Range<u64>,
    ) -> impl Iterator<Item = (&Origin, &Version)> + '_ {
        let starts = match self.rows.get(metric).and_then(|by_len| by_len.get(&grain)) {
            // `BTreeMap::range` panics on a reversed range; an empty one selects nothing.
            Some(by_start) if span.start < span.end => Some(by_start.range(span)),
            _ => None,
        };
        starts
            .into_iter()
            .flatten()
            .flat_map(|(_, by_origin)| by_origin.iter())
    }

    /// The merge, over every origin, of the `grain` rows of `metric` whose window starts in
    /// `span`. For a span whose ends are boundaries of `grain`'s windows (as both ends of
    /// the [`Window::span`] of a window of `grain` or a coarser length are; for
    /// [`WindowLen::Week`] that means Mondays, not multiples of its length) that is exactly
    /// the rows inside it, and the result equals the summary of every origin's events in the
    /// span. Rows of other lengths are never mixed in.
    #[must_use]
    pub fn summarize(&self, metric: &MetricName, grain: WindowLen, span: Range<u64>) -> Summary {
        let mut out = Summary::new();
        for (_, version) in self.versions(metric, grain, span) {
            out.merge(&version.summary);
        }
        out
    }

    /// [`Rollup::summarize`], one summary per origin.
    #[must_use]
    pub fn per_origin(
        &self,
        metric: &MetricName,
        grain: WindowLen,
        span: Range<u64>,
    ) -> BTreeMap<Origin, Summary> {
        let mut out: BTreeMap<Origin, Summary> = BTreeMap::new();
        for (origin, version) in self.versions(metric, grain, span) {
            out.entry(origin.clone())
                .or_default()
                .merge(&version.summary);
        }
        out
    }

    /// Raise the horizon of length `grain` to `at_ms`: drop every `grain` row whose window
    /// ended at or before it, and refuse such rows from now on ([`Offered::Expired`]). A
    /// horizon only moves forward, so an earlier `at_ms` changes nothing. Returns how many
    /// rows went.
    pub fn forget_before(&mut self, grain: WindowLen, at_ms: u64) -> usize {
        let horizon = self.horizon_ms(grain).max(at_ms);
        if let Some(slot) = self.horizons.get_mut(Rollup::slot(grain)) {
            *slot = horizon;
        }
        // A window ends after the horizon exactly when it starts after `horizon - grain`.
        let Some(first_kept) = horizon
            .checked_sub(grain.millis())
            .and_then(|start| start.checked_add(1))
        else {
            return 0;
        };
        let mut removed = 0usize;
        for by_len in self.rows.values_mut() {
            if let Some(by_start) = by_len.get_mut(&grain) {
                by_start.retain(|&start, by_origin| {
                    if start >= first_kept {
                        true
                    } else {
                        removed = removed.saturating_add(by_origin.len());
                        false
                    }
                });
                if by_start.is_empty() {
                    by_len.remove(&grain);
                }
            }
        }
        self.rows.retain(|_, by_len| !by_len.is_empty());
        self.len = self.len.saturating_sub(removed);
        removed
    }
}

// ---------------------------------------------------------------------------
// Counter and gauge
// ---------------------------------------------------------------------------

/// One origin's monotone total. Versions join by `max` (idempotent), and a fleet total is
/// the sum of each origin's joined counter (module docs).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Counter {
    total: u64,
}

impl Counter {
    /// A counter that has counted nothing.
    pub const ZERO: Counter = Counter { total: 0 };

    /// A counter at `total`.
    #[must_use]
    pub const fn new(total: u64) -> Counter {
        Counter { total }
    }

    /// This counter after `n` more, saturating at `u64::MAX`.
    #[must_use]
    pub const fn add(self, n: u64) -> Counter {
        Counter {
            total: self.total.saturating_add(n),
        }
    }

    /// The total.
    #[must_use]
    pub const fn total(self) -> u64 {
        self.total
    }

    /// The join of two versions of one origin's counter: the larger.
    #[must_use]
    pub const fn join(self, other: Counter) -> Counter {
        if other.total > self.total {
            other
        } else {
            self
        }
    }

    /// The canonical encoding (module docs).
    #[must_use]
    pub fn encode(self) -> Vec<u8> {
        let mut out = Vec::with_capacity(2usize.saturating_add(varint_len(u128::from(self.total))));
        out.push(KIND_COUNTER);
        out.push(COUNTER_VERSION);
        put_varint(&mut out, u128::from(self.total));
        out
    }

    /// Decode a canonical encoding; anything else is refused.
    ///
    /// # Errors
    ///
    /// [`DecodeError`] for a different kind, an unknown version, a truncated or overlong
    /// input, or a non-minimal or overflowing varint.
    pub fn decode(bytes: &[u8]) -> Result<Counter, DecodeError> {
        let mut reader = Reader { rest: bytes };
        reader.header(KIND_COUNTER, COUNTER_VERSION)?;
        let total = reader.varint_u64()?;
        reader.finish()?;
        Ok(Counter { total })
    }
}

/// One origin's latest reading and when it was taken (Unix milliseconds). Versions join by
/// the later `(at_ms, value)` (idempotent).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Gauge {
    at_ms: u64,
    value: u64,
}

impl Gauge {
    /// A reading of `value` at `at_ms`.
    #[must_use]
    pub const fn new(at_ms: u64, value: u64) -> Gauge {
        Gauge { at_ms, value }
    }

    /// When the reading was taken.
    #[must_use]
    pub const fn at_ms(self) -> u64 {
        self.at_ms
    }

    /// The reading.
    #[must_use]
    pub const fn value(self) -> u64 {
        self.value
    }

    /// The join of two versions of one origin's gauge: the later reading, and of two taken
    /// at the same instant the larger, so every replica picks the same one.
    #[must_use]
    pub const fn join(self, other: Gauge) -> Gauge {
        if other.at_ms > self.at_ms || (other.at_ms == self.at_ms && other.value > self.value) {
            other
        } else {
            self
        }
    }

    /// The canonical encoding (module docs).
    #[must_use]
    pub fn encode(self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            2usize
                .saturating_add(varint_len(u128::from(self.at_ms)))
                .saturating_add(varint_len(u128::from(self.value))),
        );
        out.push(KIND_GAUGE);
        out.push(GAUGE_VERSION);
        put_varint(&mut out, u128::from(self.at_ms));
        put_varint(&mut out, u128::from(self.value));
        out
    }

    /// Decode a canonical encoding; anything else is refused.
    ///
    /// # Errors
    ///
    /// [`DecodeError`] for a different kind, an unknown version, a truncated or overlong
    /// input, or a non-minimal or overflowing varint.
    pub fn decode(bytes: &[u8]) -> Result<Gauge, DecodeError> {
        let mut reader = Reader { rest: bytes };
        reader.header(KIND_GAUGE, GAUGE_VERSION)?;
        let at_ms = reader.varint_u64()?;
        let value = reader.varint_u64()?;
        reader.finish()?;
        Ok(Gauge { at_ms, value })
    }
}

// ---------------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------------

/// The kind byte of an encoded [`Summary`].
pub const KIND_SUMMARY: u8 = b'S';
/// The kind byte of an encoded [`Counter`].
pub const KIND_COUNTER: u8 = b'C';
/// The kind byte of an encoded [`Gauge`].
pub const KIND_GAUGE: u8 = b'G';
/// The kind byte of an encoded [`SummaryId`].
pub const KIND_ID: u8 = b'I';

/// The version of the [`Summary`] encoding and its bucket layout. A new layout or field is a
/// new version, which older builds refuse.
pub const SUMMARY_VERSION: u8 = 1;
/// The version of the [`Counter`] encoding.
pub const COUNTER_VERSION: u8 = 1;
/// The version of the [`Gauge`] encoding.
pub const GAUGE_VERSION: u8 = 1;
/// The version of the [`SummaryId`] encoding.
pub const SUMMARY_ID_VERSION: u8 = 1;

/// Why bytes are not a canonical encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeError {
    /// The input ends before the encoding does.
    Truncated,
    /// Bytes follow a complete encoding.
    TrailingBytes,
    /// The kind byte names a different type.
    WrongKind {
        /// The kind the decoder reads.
        expected: u8,
        /// The kind the bytes carry.
        found: u8,
    },
    /// A version this build does not know.
    UnknownVersion {
        /// The kind whose version it is.
        kind: u8,
        /// The version the bytes carry.
        version: u8,
    },
    /// A varint with a redundant trailing zero group.
    NonMinimalVarint,
    /// A varint wider than its field.
    VarintOverflow,
    /// More buckets listed than the layout has.
    TooManyBuckets,
    /// A bucket index at or past [`BUCKET_COUNT`].
    BucketOutOfRange,
    /// A bucket listed with a count of zero.
    EmptyBucket,
    /// The minimum is not a value of the lowest nonempty bucket.
    MinOutsideBucket,
    /// The maximum is not a value of the highest nonempty bucket.
    MaxOutsideBucket,
    /// The minimum exceeds the maximum.
    MinAboveMax,
    /// One value, but a minimum and a maximum that differ.
    ExtremesExceedCount,
    /// A sum no multiset of values with these buckets and extremes has.
    SumOutOfRange,
    /// An origin or metric name outside the grammar.
    BadName(NameError),
    /// A window tag or index that names no window.
    BadWindow,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecodeError::Truncated => f.write_str("encoding is truncated"),
            DecodeError::TrailingBytes => f.write_str("bytes follow the encoding"),
            DecodeError::WrongKind { expected, found } => {
                write!(f, "kind 0x{found:02x} where 0x{expected:02x} was expected")
            }
            DecodeError::UnknownVersion { kind, version } => {
                write!(f, "unknown version {version} of kind 0x{kind:02x}")
            }
            DecodeError::NonMinimalVarint => f.write_str("varint is not minimal"),
            DecodeError::VarintOverflow => f.write_str("varint overflows its field"),
            DecodeError::TooManyBuckets => f.write_str("more buckets than the layout has"),
            DecodeError::BucketOutOfRange => f.write_str("bucket index past the layout"),
            DecodeError::EmptyBucket => f.write_str("bucket listed with count zero"),
            DecodeError::MinOutsideBucket => f.write_str("minimum outside the lowest bucket"),
            DecodeError::MaxOutsideBucket => f.write_str("maximum outside the highest bucket"),
            DecodeError::MinAboveMax => f.write_str("minimum above maximum"),
            DecodeError::ExtremesExceedCount => {
                f.write_str("one value with a distinct minimum and maximum")
            }
            DecodeError::SumOutOfRange => f.write_str("sum impossible for these buckets"),
            DecodeError::BadName(why) => write!(f, "bad name: {why}"),
            DecodeError::BadWindow => f.write_str("names no window"),
        }
    }
}

impl std::error::Error for DecodeError {}

/// Append `value` as an unsigned LEB128 varint.
fn put_varint(out: &mut Vec<u8>, mut value: u128) {
    loop {
        let group = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            out.push(group);
            return;
        }
        out.push(group | 0x80);
    }
}

/// The length of `value`'s varint.
const fn varint_len(value: u128) -> usize {
    let bits = 128u32.saturating_sub(value.leading_zeros());
    if bits == 0 {
        1
    } else {
        bits.div_ceil(7) as usize
    }
}

fn put_name(out: &mut Vec<u8>, name: &str) {
    // A valid name is 1..=64 bytes, so its length fits the byte.
    out.push(name.len() as u8);
    out.extend_from_slice(name.as_bytes());
}

/// A strict cursor over an encoding.
struct Reader<'a> {
    rest: &'a [u8],
}

impl<'a> Reader<'a> {
    fn byte(&mut self) -> Result<u8, DecodeError> {
        match self.rest {
            [b, tail @ ..] => {
                self.rest = tail;
                Ok(*b)
            }
            [] => Err(DecodeError::Truncated),
        }
    }

    fn header(&mut self, kind: u8, version: u8) -> Result<(), DecodeError> {
        let found = self.byte()?;
        if found != kind {
            return Err(DecodeError::WrongKind {
                expected: kind,
                found,
            });
        }
        let found_version = self.byte()?;
        if found_version != version {
            return Err(DecodeError::UnknownVersion {
                kind,
                version: found_version,
            });
        }
        Ok(())
    }

    /// A minimal varint of at most `bits` bits.
    fn varint(&mut self, bits: u32) -> Result<u128, DecodeError> {
        let mut value: u128 = 0;
        let mut shift: u32 = 0;
        loop {
            let b = self.byte()?;
            let group = u128::from(b & 0x7f);
            let room = bits.saturating_sub(shift);
            if room < 7 && group.checked_shr(room).unwrap_or(0) != 0 {
                return Err(DecodeError::VarintOverflow);
            }
            let Some(shifted) = group.checked_shl(shift) else {
                return Err(DecodeError::VarintOverflow);
            };
            value |= shifted;
            if b & 0x80 == 0 {
                if b == 0 && shift > 0 {
                    return Err(DecodeError::NonMinimalVarint);
                }
                return Ok(value);
            }
            shift = shift.saturating_add(7);
            if shift >= bits {
                return Err(DecodeError::VarintOverflow);
            }
        }
    }

    fn varint_u64(&mut self) -> Result<u64, DecodeError> {
        let value = self.varint(64)?;
        u64::try_from(value).map_err(|_| DecodeError::VarintOverflow)
    }

    fn varint_u128(&mut self) -> Result<u128, DecodeError> {
        self.varint(128)
    }

    fn name(&mut self) -> Result<&'a str, DecodeError> {
        let len = usize::from(self.byte()?);
        let Some((name, rest)) = self.rest.split_at_checked(len) else {
            return Err(DecodeError::Truncated);
        };
        self.rest = rest;
        check_name(name).map_err(DecodeError::BadName)?;
        // Every byte is printable ASCII, so the name is UTF-8.
        std::str::from_utf8(name).map_err(|_| DecodeError::BadName(NameError::Byte(0x80)))
    }

    fn finish(self) -> Result<(), DecodeError> {
        if self.rest.is_empty() {
            Ok(())
        } else {
            Err(DecodeError::TrailingBytes)
        }
    }
}
