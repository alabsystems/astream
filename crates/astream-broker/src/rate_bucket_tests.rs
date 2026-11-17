// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! [`RateBucket::step`] held to the limiter it was taken out of.

use super::*;
use crate::store::MAX_RATE_BUDGET;

// The broker's limiter as it stood before its arithmetic became `RateBucket::step`, kept
// here word for word but for its names and for taking the millisecond it used to read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct OldBucket {
    rec_milli: u64,
    byte_milli: u64,
    last_ms: u64,
}

struct Old {
    limit: Option<RateLimit>,
    buckets: BTreeMap<u64, OldBucket>,
}

impl Old {
    fn set_limit_at(&mut self, now_ms: u64, limit: Option<RateLimit>) {
        self.limit = limit;
        match limit {
            None => self.buckets.clear(),
            Some(lim) => {
                let burst_rec = lim.burst_records.saturating_mul(1_000);
                let burst_byte = lim.burst_bytes.saturating_mul(1_000);
                for bucket in self.buckets.values_mut() {
                    bucket.rec_milli = rate_tokens_clamp(bucket.rec_milli, burst_rec);
                    bucket.byte_milli = rate_tokens_clamp(bucket.byte_milli, burst_byte);
                    bucket.last_ms = rate_clock_advance(bucket.last_ms, now_ms);
                }
            }
        }
    }

    fn try_acquire_at(
        &mut self,
        now_ms: u64,
        producer_id: u64,
        wire_bytes: usize,
    ) -> Result<(), (u64, &'static str)> {
        let Some(lim) = self.limit else {
            return Ok(());
        };
        let burst_rec_milli = lim.burst_records.saturating_mul(1_000);
        let burst_byte_milli = lim.burst_bytes.saturating_mul(1_000);
        let wire_b = (wire_bytes.max(1)) as u64;
        if lim.bytes_per_sec > 0 && wire_b > lim.burst_bytes {
            let over = wire_b.saturating_sub(lim.burst_bytes).saturating_mul(1_000);
            let retry_ms = over
                .saturating_add(lim.bytes_per_sec.saturating_sub(1))
                .checked_div(lim.bytes_per_sec)
                .unwrap_or(1)
                .max(1);
            return Err((retry_ms, "record bytes exceed burst_bytes"));
        }

        if !self.buckets.contains_key(&producer_id) && self.buckets.len() >= MAX_RATE_BUCKETS {
            let mut full_pid: Option<u64> = None;
            for (&pid, b) in &self.buckets {
                let dt = now_ms.saturating_sub(b.last_ms);
                let r_now = rate_tokens_clamp(
                    b.rec_milli
                        .saturating_add(dt.saturating_mul(lim.records_per_sec)),
                    burst_rec_milli,
                );
                let b_full = if lim.bytes_per_sec > 0 {
                    let b_now = rate_tokens_clamp(
                        b.byte_milli
                            .saturating_add(dt.saturating_mul(lim.bytes_per_sec)),
                        burst_byte_milli,
                    );
                    b_now >= burst_byte_milli
                } else {
                    true
                };
                if r_now >= burst_rec_milli && b_full {
                    full_pid = Some(pid);
                    break;
                }
            }
            match full_pid {
                Some(evict) => {
                    self.buckets.remove(&evict);
                }
                None => {
                    return Err((50, "active rate buckets at capacity"));
                }
            }
        }

        let cur = match self.buckets.get(&producer_id) {
            Some(&b) => b,
            None => OldBucket {
                rec_milli: burst_rec_milli,
                byte_milli: burst_byte_milli,
                last_ms: now_ms,
            },
        };
        let elapsed_ms = now_ms.saturating_sub(cur.last_ms);
        let rec_refilled = rate_tokens_clamp(
            cur.rec_milli
                .saturating_add(elapsed_ms.saturating_mul(lim.records_per_sec)),
            burst_rec_milli,
        );
        let byte_refilled = if lim.bytes_per_sec > 0 {
            rate_tokens_clamp(
                cur.byte_milli
                    .saturating_add(elapsed_ms.saturating_mul(lim.bytes_per_sec)),
                burst_byte_milli,
            )
        } else {
            0
        };

        if !rate_tokens_sufficient(rec_refilled, 1_000) {
            self.buckets.insert(
                producer_id,
                OldBucket {
                    rec_milli: rec_refilled,
                    byte_milli: byte_refilled,
                    last_ms: now_ms,
                },
            );
            let deficit = 1_000u64.saturating_sub(rec_refilled);
            let retry_ms = deficit
                .saturating_add(lim.records_per_sec.saturating_sub(1))
                .checked_div(lim.records_per_sec)
                .unwrap_or(1)
                .max(1);
            return Err((retry_ms, "record rate exceeded"));
        }

        let cost_byte_milli = wire_b.saturating_mul(1_000);
        if lim.bytes_per_sec > 0 && !rate_tokens_sufficient(byte_refilled, cost_byte_milli) {
            self.buckets.insert(
                producer_id,
                OldBucket {
                    rec_milli: rec_refilled,
                    byte_milli: byte_refilled,
                    last_ms: now_ms,
                },
            );
            let deficit = cost_byte_milli.saturating_sub(byte_refilled);
            let retry_ms = deficit
                .saturating_add(lim.bytes_per_sec.saturating_sub(1))
                .checked_div(lim.bytes_per_sec)
                .unwrap_or(1)
                .max(1);
            return Err((retry_ms, "byte rate exceeded"));
        }

        self.buckets.insert(
            producer_id,
            OldBucket {
                rec_milli: rec_refilled.saturating_sub(1_000),
                byte_milli: if lim.bytes_per_sec > 0 {
                    byte_refilled.saturating_sub(cost_byte_milli)
                } else {
                    0
                },
                last_ms: now_ms,
            },
        );
        Ok(())
    }
}

/// SplitMix64: a schedule is a function of its seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn pick(&mut self, from: &[u64]) -> u64 {
        from[self.below(from.len() as u64) as usize]
    }

    fn limit(&mut self) -> RateLimit {
        let records_per_sec = self.pick(&[1, 2, 7, 50, 1_000, 999_983, MAX_RATE_BUDGET]);
        let burst_records = self.pick(&[1, 2, 5, 40, 1_000, MAX_RATE_BUDGET]);
        let (bytes_per_sec, burst_bytes) = if self.below(3) == 0 {
            (0, 0)
        } else {
            (
                self.pick(&[1, 64, 1_000, 65_536, MAX_RATE_BUDGET]),
                self.pick(&[1, 100, 4_096, 1 << 20, MAX_RATE_BUDGET]),
            )
        };
        let limit = RateLimit {
            records_per_sec,
            burst_records,
            bytes_per_sec,
            burst_bytes,
        };
        limit.validate().expect("a limit the broker accepts")
    }
}

const OVERSIZE: &str = "record bytes exceed burst_bytes";

fn refused(old: Result<(), (u64, &'static str)>) -> Result<(), RateRefusal> {
    old.map_err(|(retry_ms, why)| RateRefusal { retry_ms, why })
}

fn same_buckets(old: &BTreeMap<u64, OldBucket>, new: &BTreeMap<u64, RateBucket>) -> bool {
    old.len() == new.len()
        && old.iter().zip(new).all(|((old_pid, old), (pid, new))| {
            old_pid == pid
                && (old.rec_milli, old.byte_milli, old.last_ms)
                    == (new.rec_milli, new.byte_milli, new.last_ms)
        })
}

/// LT-E51. Over 3,000 random schedules of 300 publishes each, with limits that change and
/// lapse, clocks that stand still and leap, and records from empty to past the byte burst,
/// three judges give the same verdict and the same retry time at every publish and hold the
/// same buckets at the end: the limiter as it stood before, the broker's limiter now, and a
/// caller that keeps one [`RateBucket`] a producer in a map of its own and calls
/// [`RateBucket::step`]. Then 6,000 producers against the limiter's 4,096 buckets, where
/// the limiter before and the limiter now refuse and forget the same ones.
///
/// Negative control, run once: with a passing record drawing 999 thousandths in place of
/// 1,000, the test fails at its first schedule, "the broker's limiter now".
#[test]
fn a_public_bucket_step_refuses_exactly_what_the_broker_refuses_over_random_schedules() {
    let mut rng = Rng(0x00A5_7EA4_2026_1116);
    let mut seen: BTreeMap<&'static str, u64> = BTreeMap::new();
    for schedule in 0..3_000u64 {
        let mut old = Old {
            limit: None,
            buckets: BTreeMap::new(),
        };
        let mut new = RateLimiterState::new();
        let mut caller: BTreeMap<u64, RateBucket> = BTreeMap::new();
        let mut limit: Option<RateLimit> = None;
        let producers = 1 + rng.below(40);
        let mut now_ms = rng.below(1_000);
        for publish in 0..300u64 {
            let wait = match rng.below(20) {
                0..=7 => 0,
                8..=11 => rng.below(5),
                12..=15 => rng.below(200),
                16..=18 => rng.below(20_000),
                // Rarely far enough that four of them hold the clock at its last millisecond.
                _ if rng.below(40) == 0 => 1 << 62,
                _ => rng.pick(&[10_000_000, 1 << 40]),
            };
            now_ms = now_ms.saturating_add(wait);
            if publish == 0 || rng.below(60) == 0 {
                limit = (rng.below(6) != 0).then(|| rng.limit());
                old.set_limit_at(now_ms, limit);
                new.set_limit_at(now_ms, limit);
                match &limit {
                    None => caller.clear(),
                    Some(limit) => {
                        for bucket in caller.values_mut() {
                            *bucket = bucket.under(limit, now_ms);
                        }
                    }
                }
            }
            let producer = rng.below(producers);
            let burst = limit.map_or(64, |limit| limit.burst_bytes.max(1));
            let wire_bytes = match rng.below(12) {
                0 => 0,
                1..=4 => rng.below(8),
                5..=7 => rng.below(300),
                8..=9 => (burst - 1).saturating_add(rng.below(3)),
                10 => burst / (1 + rng.below(4)),
                _ => rng.pick(&[1 << 20, u64::MAX]),
            };
            let wire_bytes = usize::try_from(wire_bytes).unwrap_or(usize::MAX);

            let before = refused(old.try_acquire_at(now_ms, producer, wire_bytes));
            let broker = new.try_acquire_at(now_ms, producer, wire_bytes);
            let stepped = match &limit {
                None => Ok(()),
                Some(limit) => {
                    let held = caller.get(&producer).copied();
                    let (next, verdict) = held
                        .unwrap_or(RateBucket::full(limit, now_ms))
                        .step(limit, now_ms, wire_bytes);
                    // As the broker: a record that can never pass makes no bucket.
                    if !matches!(verdict, Err(refusal) if refusal.why == OVERSIZE) {
                        caller.insert(producer, next);
                    }
                    verdict
                }
            };
            let at = format!("schedule {schedule} publish {publish} at {now_ms} ms under {limit:?}, {wire_bytes} bytes");
            assert_eq!(broker, before, "the broker's limiter now: {at}");
            assert_eq!(stepped, before, "a caller's own buckets: {at}");
            *seen
                .entry(before.err().map_or("passed", |refusal| refusal.why))
                .or_default() += 1;
        }
        assert!(
            same_buckets(&old.buckets, &new.buckets),
            "schedule {schedule}: the limiter's buckets"
        );
        assert_eq!(
            caller, new.buckets,
            "schedule {schedule}: a caller's own buckets"
        );
    }
    for why in [
        "passed",
        "record rate exceeded",
        "byte rate exceeded",
        OVERSIZE,
    ] {
        let count = seen.get(why).copied().unwrap_or(0);
        assert!(count >= 10_000, "{why}: {count} of 900,000 publishes");
    }

    // More producers than the limiter keeps buckets for: one record a second, a burst of
    // one, so a producer's bucket is full again a second after it published.
    let one = RateLimit::records(1, 1).expect("a limit");
    let mut old = Old {
        limit: None,
        buckets: BTreeMap::new(),
    };
    let mut new = RateLimiterState::new();
    old.set_limit_at(0, Some(one));
    new.set_limit_at(0, Some(one));
    let mut now_ms = 0;
    let mut at_capacity = 0u64;
    for publish in 0..40_000u64 {
        // The clock stands still while the buckets fill, so none is full again.
        if publish >= 8_000 {
            now_ms += [0, 0, 0, 1, 300][rng.below(5) as usize];
        }
        let producer = rng.below(6_000);
        let before = refused(old.try_acquire_at(now_ms, producer, 1));
        let broker = new.try_acquire_at(now_ms, producer, 1);
        assert_eq!(
            broker, before,
            "publish {publish} of producer {producer} at {now_ms} ms"
        );
        at_capacity += u64::from(
            before.is_err_and(|refusal| refusal.why == "active rate buckets at capacity"),
        );
        assert!(new.buckets.len() <= MAX_RATE_BUCKETS);
    }
    assert!(same_buckets(&old.buckets, &new.buckets));
    assert_eq!(new.buckets.len(), MAX_RATE_BUCKETS, "the limiter filled");
    assert!(
        at_capacity >= 100,
        "{at_capacity} publishes found no bucket to forget"
    );

    // A clock that steps back refills nothing and moves no time back.
    let limit = RateLimit::records(10, 5).expect("a limit");
    let (drawn, verdict) = RateBucket::full(&limit, 1_000).step(&limit, 1_000, 1);
    assert_eq!(
        (drawn.rec_milli, drawn.last_ms, verdict),
        (4_000, 1_000, Ok(()))
    );
    let (back, verdict) = drawn.step(&limit, 400, 1);
    assert_eq!(
        (back.rec_milli, back.last_ms, verdict),
        (3_000, 1_000, Ok(()))
    );
    let (again, _) = back.step(&limit, 1_100, 1);
    assert_eq!(
        (again.rec_milli, again.last_ms),
        (3_000, 1_100),
        "100 ms refills one record"
    );
    assert!(RateBucket::full(&limit, 0).is_full_at(&limit, 0) && !drawn.is_full_at(&limit, 1_000));
    assert!(drawn.is_full_at(&limit, 1_100));
}
