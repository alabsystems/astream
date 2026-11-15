// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The suite's one way to record a session into log bytes: each record appended
//! under a seeded seam, every append checked, so a fixture that cannot be
//! recorded fails its test instead of quietly dropping a record and shifting
//! every offset after it.

use astream_engine::{Disk, Effects, Log, Seeded};
use astream_term::Record;

/// Record `records` under `Seeded::new(seed)` and return the stored log bytes.
pub fn record_session(seed: u64, records: &[Record]) -> Vec<u8> {
    let mut fx = Seeded::new(seed);
    let mut log = Log::new();
    for rec in records {
        log.append(&mut fx, rec.clone())
            .expect("a fixture record appends");
    }
    fx.disk().read_all().to_vec()
}
