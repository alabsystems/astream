//! A driver over astream-wire's REAL public API — the stock-toolchain companion to the Trust
//! verification survey (`scripts/verify-trust.sh`, captured in evidence/verify/trust-wire.md).
//!
//! The obligations the Trust verifier discharges (or refuses) for astream-wire are generated
//! from the crate's own MIR when the LIBRARY is compiled under Trust — never from a hand-copied
//! mirror of it, which would stay "proved" whatever the real guard did. This example carries
//! no logic of its own. It exists so that the functions the survey is about — the real `Frame`,
//! `Offset`, `assign_partition`, `Subject` / `Filter` and the table-driven CRC — are exercised
//! end to end on the guarded paths the survey's obligations come from, under the stock
//! toolchain (`cargo run -p astream-wire --example verify_core`). A renamed or removed
//! function breaks this driver; a weakened guard shows up in its printed lines.
//!
//! What it prints is a small deterministic exercise of each guarded path; it is NOT the
//! verification evidence. That evidence is the per-function verdict table the compiler emits
//! while building the library — captured, with its honest boundaries, in
//! evidence/verify/trust-wire.md. (No `unwrap`/`expect` here: each would add a panic obligation
//! of the driver's own to any Trust build of it.)

use astream_wire::{
    assign_partition, crc32_ieee, fnv1a_64, time_bucket, Filter, Frame, Offset, PartitionKey,
    Subject,
};

fn consumed(decoded: Result<Option<astream_wire::Decoded>, astream_wire::FrameError>) -> String {
    match decoded {
        Ok(Some(d)) => format!("Ok(Some(consumed={}))", d.consumed),
        Ok(None) => "Ok(None): need more bytes".to_string(),
        Err(e) => format!("Err({e})"),
    }
}

fn main() {
    // Frame codec: round trip, truncation, an oversized length field, a corrupt payload.
    let frame = Frame::new(b"agent-7 wake".to_vec());
    let bytes = match frame.encode() {
        Ok(b) => b,
        Err(e) => {
            println!("Frame::encode: Err({e})");
            return;
        }
    };
    println!("Frame::encode: {} bytes", bytes.len());
    println!(
        "Frame::decode(complete): {}",
        consumed(Frame::decode(&bytes))
    );
    let short = bytes.len().saturating_sub(1);
    println!(
        "Frame::decode(truncated): {}",
        consumed(Frame::decode(&bytes[..short]))
    );
    let mut hostile = bytes.clone();
    if hostile.len() >= 8 {
        hostile[4..8].copy_from_slice(&u32::MAX.to_le_bytes());
    }
    println!(
        "Frame::decode(oversized length): {}",
        consumed(Frame::decode(&hostile))
    );
    let mut corrupt = bytes.clone();
    if let Some(last) = corrupt.last_mut() {
        *last ^= 0xFF;
    }
    println!(
        "Frame::decode(corrupt payload): {}",
        consumed(Frame::decode(&corrupt))
    );

    // Hashes: the table-driven CRC (its lookup index is the one bounds obligation on the
    // per-frame hot path) and FNV-1a.
    println!("crc32_ieee(123456789) = {:#010x}", crc32_ieee(b"123456789"));
    println!("fnv1a_64(agent-7)     = {:#018x}", fnv1a_64(b"agent-7"));

    // Offsets: the checked successor and the directional delta.
    println!(
        "Offset::checked_next(0)        = {:?}",
        Offset::ZERO.checked_next()
    );
    println!(
        "Offset::checked_next(u64::MAX) = {:?}",
        Offset(u64::MAX).checked_next()
    );
    println!(
        "Offset(10).delta_from(4)       = {:?}",
        Offset(10).delta_from(Offset(4))
    );
    println!(
        "Offset(4).delta_from(10)       = {:?}",
        Offset(4).delta_from(Offset(10))
    );

    // The one partitioner, over every key kind, including the zero-partition guard.
    println!(
        "assign_partition(keyed, 0 partitions)   = {}",
        assign_partition(PartitionKey::Keyed(b"order-42"), 0)
    );
    println!(
        "assign_partition(durable, 16)           = {}",
        assign_partition(
            PartitionKey::UnkeyedDurable {
                topic: "/a/stream/events",
                origin: "producer-1",
                time_bucket: time_bucket(4321),
            },
            16
        )
    );
    println!(
        "assign_partition(ephemeral, u32::MAX)   = {}",
        assign_partition(
            PartitionKey::UnkeyedEphemeral { msg_id: u128::MAX },
            u32::MAX
        )
    );

    // The address grammar: validation, matching, containment.
    println!("Subject::new(/a//b) = {:?}", Subject::new("/a//b"));
    println!("Filter::new(/a/>/b) = {:?}", Filter::new("/a/>/b"));
    match (Subject::new("/a/stream/events"), Filter::new("/a/*/>")) {
        (Ok(subject), Ok(filter)) => {
            println!(
                "Filter(/a/*/>).matches(/a/stream/events) = {}",
                filter.matches(&subject)
            );
        }
        (s, f) => println!("unexpected: {s:?} {f:?}"),
    }
    match (Filter::new("/a/>"), Filter::new("/a/b/*")) {
        (Ok(wide), Ok(narrow)) => {
            println!("Filter(/a/>).contains(/a/b/*) = {}", wide.contains(&narrow));
            println!("Filter(/a/b/*).contains(/a/>) = {}", narrow.contains(&wide));
        }
        (a, b) => println!("unexpected: {a:?} {b:?}"),
    }
}
