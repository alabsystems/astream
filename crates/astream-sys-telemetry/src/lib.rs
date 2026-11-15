// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! `aterm ctl @self sys` Apple Silicon cluster millicore aggregation, `sys jobs` zero-progress stall detection, `fp_bytes`/swap memory-pressure step-down, `await sys` quiet-machine predicates, Darwin QoS throttling diagnostics, and `gpu_ppm` budgets. forbid(unsafe_code).

#![forbid(unsafe_code)]

#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

pub mod cluster_busy_cores;
pub mod gpu_ppm_budget;
pub mod memory_swap_pressure;
pub mod qos_clamp_diagnose;
pub mod quiet_machine_await;
pub mod stalled_job_detector;

/// Four-byte magic prefix (`"ASYS"`) for a 16-byte `astream-sys-telemetry` wire snapshot header.
pub const SYS_TELEMETRY_WIRE_MAGIC: [u8; 4] = *b"ASYS";

/// Wire format version for `astream-sys-telemetry` snapshot headers.
pub const SYS_TELEMETRY_WIRE_VERSION: u8 = 1;

/// Encode a 16-byte `astream-sys-telemetry` wire snapshot header:
/// `[0..4] = b"ASYS"`, `[4] = version (1)`, `[5] = pressure_tag` (`0..=3`), `[6..8] = 0`,
/// `[8..12] = busy_millicores (BE)`, `[12..16] = gpu_ppm (BE)`.
#[must_use]
pub const fn encode_sys_telemetry_wire(
    pressure_tag: u8,
    busy_millicores: u32,
    gpu_ppm: u32,
) -> Option<[u8; 16]> {
    if pressure_tag > 3 || gpu_ppm > 1_000_000 {
        return None;
    }
    Some([
        SYS_TELEMETRY_WIRE_MAGIC[0],
        SYS_TELEMETRY_WIRE_MAGIC[1],
        SYS_TELEMETRY_WIRE_MAGIC[2],
        SYS_TELEMETRY_WIRE_MAGIC[3],
        SYS_TELEMETRY_WIRE_VERSION,
        pressure_tag,
        0,
        0,
        ((busy_millicores >> 24) & 0xFF) as u8,
        ((busy_millicores >> 16) & 0xFF) as u8,
        ((busy_millicores >> 8) & 0xFF) as u8,
        (busy_millicores & 0xFF) as u8,
        ((gpu_ppm >> 24) & 0xFF) as u8,
        ((gpu_ppm >> 16) & 0xFF) as u8,
        ((gpu_ppm >> 8) & 0xFF) as u8,
        (gpu_ppm & 0xFF) as u8,
    ])
}

/// Decode a 16-byte `astream-sys-telemetry` wire snapshot header into
/// `(pressure_tag, busy_millicores, gpu_ppm)`.
#[must_use]
pub const fn decode_sys_telemetry_wire(buf: &[u8]) -> Option<(u8, u32, u32)> {
    let [b'A', b'S', b'Y', b'S', SYS_TELEMETRY_WIRE_VERSION, pressure_tag, 0, 0, m0, m1, m2, m3, g0, g1, g2, g3, ..] =
        *buf
    else {
        return None;
    };
    let busy_millicores =
        ((m0 as u32) << 24) | ((m1 as u32) << 16) | ((m2 as u32) << 8) | (m3 as u32);
    let gpu_ppm = ((g0 as u32) << 24) | ((g1 as u32) << 16) | ((g2 as u32) << 8) | (g3 as u32);
    if pressure_tag > 3 || gpu_ppm > 1_000_000 {
        return None;
    }
    Some((pressure_tag, busy_millicores, gpu_ppm))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sys_telemetry_wire_roundtrips_and_rejects_malformed() {
        let Some(frame) = encode_sys_telemetry_wire(2, 8_500, 250_000) else {
            panic!("valid telemetry frame should encode");
        };
        assert_eq!(decode_sys_telemetry_wire(&frame), Some((2, 8_500, 250_000)));
        assert_eq!(encode_sys_telemetry_wire(4, 100, 100), None);
        assert_eq!(encode_sys_telemetry_wire(1, 100, 1_000_001), None);
        let mut bad = frame;
        bad[4] = 2;
        assert_eq!(decode_sys_telemetry_wire(&bad), None);
    }
}
