// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure-Rust Slicing-by-8 CRC-32C (Castagnoli, reflected polynomial `0x82F6_3B78`)
//! required by Kafka RecordBatch v2 (`magic = 2`, KIP-98).
//!
//! Zero external dependencies, `#![forbid(unsafe_code)]`, compile-time `.rodata`
//! tables indexed exclusively by `u8` so Trust discharges every table load with
//! zero runtime bounds checks.

/// Reflected Castagnoli CRC-32C generator polynomial (`0x82F6_3B78`).
pub const CRC32C_POLY: u32 = 0x82F6_3B78;

#[inline(always)]
const fn crc32c_table_at(row: &[u32; 256], idx: u8) -> u32 {
    row[idx as usize]
}

const fn crc32c_entry(byte: u8) -> u32 {
    let mut crc = byte as u32;
    let mut step = 0usize;
    while step < 8 {
        if crc & 1 != 0 {
            crc = (crc >> 1) ^ CRC32C_POLY;
        } else {
            crc >>= 1;
        }
        step = step.saturating_add(1);
    }
    crc
}

const fn crc32c_row0() -> [u32; 256] {
    let mut row = [0u32; 256];
    let mut i = 0u8;
    loop {
        row[i as usize] = crc32c_entry(i);
        if i == u8::MAX {
            return row;
        }
        i = i.wrapping_add(1);
    }
}

const fn crc32c_next_row(prev: &[u32; 256], t0: &[u32; 256]) -> [u32; 256] {
    let mut row = [0u32; 256];
    let mut i = 0u8;
    loop {
        let c = prev[i as usize];
        row[i as usize] = (c >> 8) ^ crc32c_table_at(t0, c as u8);
        if i == u8::MAX {
            return row;
        }
        i = i.wrapping_add(1);
    }
}

const fn crc32c_tables() -> [[u32; 256]; 8] {
    let t0 = crc32c_row0();
    let t1 = crc32c_next_row(&t0, &t0);
    let t2 = crc32c_next_row(&t1, &t0);
    let t3 = crc32c_next_row(&t2, &t0);
    let t4 = crc32c_next_row(&t3, &t0);
    let t5 = crc32c_next_row(&t4, &t0);
    let t6 = crc32c_next_row(&t5, &t0);
    let t7 = crc32c_next_row(&t6, &t0);
    [t0, t1, t2, t3, t4, t5, t6, t7]
}

const CRC32C_TABLES: [[u32; 256]; 8] = crc32c_tables();

#[inline(always)]
const fn u32_le(b0: u8, b1: u8, b2: u8, b3: u8) -> u32 {
    (b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)
}

/// Feed `data` into an ongoing CRC-32C (Castagnoli) computation started at `0`
/// (`crc32c(b"") == 0`).
#[must_use]
pub const fn crc32c_update(crc: u32, data: &[u8]) -> u32 {
    let [t0, t1, t2, t3, t4, t5, t6, t7] = &CRC32C_TABLES;
    let mut state: u32 = !crc;
    let mut rest = data;
    while let &[c0, c1, c2, c3, c4, c5, c6, c7, ref tail @ ..] = rest {
        let lo = state ^ u32_le(c0, c1, c2, c3);
        let hi = u32_le(c4, c5, c6, c7);
        state = crc32c_table_at(t7, lo as u8)
            ^ crc32c_table_at(t6, (lo >> 8) as u8)
            ^ crc32c_table_at(t5, (lo >> 16) as u8)
            ^ crc32c_table_at(t4, (lo >> 24) as u8)
            ^ crc32c_table_at(t3, hi as u8)
            ^ crc32c_table_at(t2, (hi >> 8) as u8)
            ^ crc32c_table_at(t1, (hi >> 16) as u8)
            ^ crc32c_table_at(t0, (hi >> 24) as u8);
        rest = tail;
    }
    while let &[b, ref tail @ ..] = rest {
        state = (state >> 8) ^ crc32c_table_at(t0, (state as u8) ^ b);
        rest = tail;
    }
    !state
}

/// Compute the CRC-32C (Castagnoli) checksum of `data` (`crc32c(b"123456789") == 0xE306_9283`).
#[must_use]
pub const fn crc32c(data: &[u8]) -> u32 {
    crc32c_update(0, data)
}
