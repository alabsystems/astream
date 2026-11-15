// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Cryptographic Trust-On-First-Use (TOFU) peer public-key pin table & explicit key-rotation
//! store (`DESIGN-aterm-fabric.md` §8.6 / §11.2 / lines 4037 & 4046,
//! `Astream.Cap.TlaTofuPinStore`).
//!
//! Binds peer node principals (`n-<16 hex>`) to 32-byte Ed25519 verifying keys with
//! constant-time key comparison, refuses silent key substitution (`KeyMismatchRefused`),
//! records monotone operator-authorized rotations (`rotate_peer_key`), and serializes
//! deterministically to/from newline-separated `v=1` pin files with `0 mandated` obligations.

#![allow(
    clippy::manual_is_ascii_check,
    clippy::manual_range_contains,
    clippy::question_mark
)]

use std::collections::BTreeMap;

#[cfg(clean_islands)]
#[path = "tofu_island.rs"]
mod tofu_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tofu_entries_clamp(entries: u64, max_entries: u64) -> u64 {
    if entries < max_entries {
        entries
    } else {
        max_entries
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn tofu_epoch_advance(prev_epoch: u64, cand_epoch: u64) -> u64 {
    if prev_epoch < cand_epoch {
        cand_epoch
    } else {
        prev_epoch
    }
}
#[cfg(clean_islands)]
pub use tofu_island::{tofu_entries_clamp, tofu_epoch_advance};

/// Maximum number of pinned peer nodes in a single [`TofuPinStore`].
pub const MAX_TOFU_PINS: usize = 1024;

contract_fn! {
    /// Verified check that a TOFU pin table size is within `max_entries`
    /// (`entries <= max_entries`), linked via `clean-kernel-defeq` to `tofu_table_within_cap_isl`.
    #[must_use]
    pub const fn tofu_table_within_cap(entries: usize, max_entries: usize) -> bool
    clauses [ensures result == (entries <= max_entries)]
    {
        entries <= max_entries
    }
}

/// Outcome of verifying a peer's 32-byte Ed25519 public key against [`TofuPinStore`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PinVerdict {
    /// First connection from `node_id`; key is now durably pinned at `epoch = 0`.
    PinnedFirstUse { epoch: u64 },
    /// Presented key matches the pinned key for `node_id` in constant time.
    VerifiedMatch { epoch: u64 },
    /// Presented key differs from the pinned key — potential MITM / rogue node refused!
    KeyMismatchRefused { pinned_epoch: u64 },
    /// Store reached `max_entries` and cannot admit an unseen `node_id`.
    CapacityExhausted,
}

/// Pinned Ed25519 identity record for one fabric peer node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinnedPeer {
    /// Canonical node principal (e.g. `"n-0123456789abcdef"`).
    pub node_id: String,
    /// 32-byte Ed25519 public key.
    pub pubkey: [u8; 32],
    /// Monotone rotation epoch (`0` on first TOFU pin, incremented on explicit rotation).
    pub epoch: u64,
    /// Timestamp (ms) when this pin or rotation was recorded.
    pub pinned_at_ms: u64,
}

/// Bounded TOFU peer-identity pin table with monotone explicit key rotation.
#[derive(Debug, Clone)]
pub struct TofuPinStore {
    max_entries: usize,
    global_rotation_epoch: u64,
    peers: BTreeMap<String, PinnedPeer>,
}

impl TofuPinStore {
    /// Create an empty TOFU pin store bounded to `max_entries` (`1..=MAX_TOFU_PINS`).
    #[must_use]
    pub fn new(max_entries: usize) -> Self {
        let clamped = tofu_entries_clamp(max_entries as u64, MAX_TOFU_PINS as u64) as usize;
        let effective = if clamped == 0 { 1 } else { clamped };
        Self {
            max_entries: effective,
            global_rotation_epoch: 0,
            peers: BTreeMap::new(),
        }
    }

    /// Number of currently pinned peers (`<= max_entries`).
    #[must_use]
    pub fn len(&self) -> usize {
        self.peers.len()
    }

    /// True when no peers are pinned yet.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.peers.is_empty()
    }

    /// Highest rotation epoch recorded across this store.
    #[must_use]
    pub const fn global_rotation_epoch(&self) -> u64 {
        self.global_rotation_epoch
    }

    /// Look up the pinned entry for `node_id`.
    #[must_use]
    pub fn get(&self, node_id: &str) -> Option<&PinnedPeer> {
        self.peers.get(node_id)
    }

    /// Verify `pubkey` for `node_id` under Trust-On-First-Use rules:
    /// - If `node_id` is already pinned: constant-time compare against `pinned.pubkey`.
    /// - If `node_id` is unseen and capacity remains: pin `pubkey` at `epoch = 0`.
    pub fn verify_or_pin(
        &mut self,
        node_id: &str,
        pubkey: &[u8; 32],
        now_ms: u64,
    ) -> Result<PinVerdict, &'static str> {
        if let Err(e) = validate_node_id(node_id) {
            return Err(e);
        }
        if ct_eq_32(pubkey, &ZERO_PUBKEY) {
            return Err("all-zero pubkey refused");
        }
        if let Some(existing) = self.peers.get(node_id) {
            if ct_eq_32(&existing.pubkey, pubkey) {
                return Ok(PinVerdict::VerifiedMatch {
                    epoch: existing.epoch,
                });
            }
            return Ok(PinVerdict::KeyMismatchRefused {
                pinned_epoch: existing.epoch,
            });
        }
        if !tofu_table_within_cap(self.peers.len().saturating_add(1), self.max_entries) {
            return Ok(PinVerdict::CapacityExhausted);
        }
        self.peers.insert(
            node_id.to_string(),
            PinnedPeer {
                node_id: node_id.to_string(),
                pubkey: *pubkey,
                epoch: 0,
                pinned_at_ms: now_ms,
            },
        );
        Ok(PinVerdict::PinnedFirstUse { epoch: 0 })
    }

    /// Operator-authorized key rotation (`aterm-link pin`): replaces `node_id`'s pinned
    /// key with `new_pubkey` and strictly advances both the peer's `epoch` and
    /// `global_rotation_epoch` via Clean-origin [`tofu_epoch_advance`].
    pub fn rotate_peer_key(
        &mut self,
        node_id: &str,
        new_pubkey: &[u8; 32],
        now_ms: u64,
    ) -> Result<u64, &'static str> {
        if let Err(e) = validate_node_id(node_id) {
            return Err(e);
        }
        if ct_eq_32(new_pubkey, &ZERO_PUBKEY) {
            return Err("all-zero pubkey refused");
        }
        if let Some(existing) = self.peers.get_mut(node_id) {
            if ct_eq_32(&existing.pubkey, new_pubkey) {
                return Err("new pubkey matches pinned pubkey");
            }
            let Some(peer_cand) = existing.epoch.checked_add(1) else {
                return Err("peer rotation epoch overflow");
            };
            let Some(glob_cand) = self.global_rotation_epoch.checked_add(1) else {
                return Err("global rotation epoch overflow");
            };
            let target = if peer_cand >= glob_cand {
                peer_cand
            } else {
                glob_cand
            };
            let next_epoch = tofu_epoch_advance(existing.epoch, target);
            existing.pubkey = *new_pubkey;
            existing.epoch = next_epoch;
            existing.pinned_at_ms = now_ms;
            self.global_rotation_epoch = tofu_epoch_advance(self.global_rotation_epoch, next_epoch);
            return Ok(next_epoch);
        }
        if !tofu_table_within_cap(self.peers.len().saturating_add(1), self.max_entries) {
            return Err("pin table capacity exhausted");
        }
        let Some(glob_cand) = self.global_rotation_epoch.checked_add(1) else {
            return Err("global rotation epoch overflow");
        };
        let next_epoch = tofu_epoch_advance(self.global_rotation_epoch, glob_cand);
        self.global_rotation_epoch = next_epoch;
        self.peers.insert(
            node_id.to_string(),
            PinnedPeer {
                node_id: node_id.to_string(),
                pubkey: *new_pubkey,
                epoch: next_epoch,
                pinned_at_ms: now_ms,
            },
        );
        Ok(next_epoch)
    }

    /// Serialize the pin table into canonical `v=1` lines sorted by `node_id`:
    /// `v=1 node=<id> epoch=<u64> t=<ms> key=<64-hex>`
    #[must_use]
    pub fn encode_text(&self) -> String {
        let mut out = String::new();
        for peer in self.peers.values() {
            out.push_str("v=1 node=");
            out.push_str(&peer.node_id);
            out.push_str(" epoch=");
            push_dec_u64(&mut out, peer.epoch);
            out.push_str(" t=");
            push_dec_u64(&mut out, peer.pinned_at_ms);
            out.push_str(" key=");
            push_hex_32(&mut out, &peer.pubkey);
            out.push('\n');
        }
        out
    }

    /// Parse a serialized `v=1` pin table with `max_entries` cap.
    pub fn decode_text(text: &str, max_entries: usize) -> Result<Self, &'static str> {
        let mut store = Self::new(max_entries);
        for raw_line in text.lines() {
            let line = raw_line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if !tofu_table_within_cap(store.peers.len().saturating_add(1), store.max_entries) {
                return Err("decoded pin table exceeds max_entries");
            }
            let Some(rest) = line.strip_prefix("v=1 ") else {
                return Err("missing v=1 prefix in pin line");
            };
            let mut node_id: Option<&str> = None;
            let mut epoch: Option<u64> = None;
            let mut pinned_at_ms: Option<u64> = None;
            let mut pubkey: Option<[u8; 32]> = None;

            for tok in rest.split(' ') {
                if tok.is_empty() {
                    continue;
                }
                let Some((k, v)) = tok.split_once('=') else {
                    return Err("malformed token in pin line");
                };
                match k {
                    "node" => {
                        if node_id.is_some() {
                            return Err("duplicate node field");
                        }
                        if let Err(e) = validate_node_id(v) {
                            return Err(e);
                        }
                        node_id = Some(v);
                    }
                    "epoch" => {
                        if epoch.is_some() {
                            return Err("duplicate epoch field");
                        }
                        let Ok(n) = parse_u64_dec_str(v) else {
                            return Err("invalid epoch");
                        };
                        epoch = Some(n);
                    }
                    "t" => {
                        if pinned_at_ms.is_some() {
                            return Err("duplicate timestamp field");
                        }
                        let Ok(n) = parse_u64_dec_str(v) else {
                            return Err("invalid timestamp");
                        };
                        pinned_at_ms = Some(n);
                    }
                    "key" => {
                        if pubkey.is_some() {
                            return Err("duplicate key field");
                        }
                        let pk = match decode_hex_32(v) {
                            Ok(val) => val,
                            Err(e) => return Err(e),
                        };
                        if ct_eq_32(&pk, &ZERO_PUBKEY) {
                            return Err("all-zero pubkey refused");
                        }
                        pubkey = Some(pk);
                    }
                    _ => return Err("unknown field in pin line"),
                }
            }

            let (Some(nid), Some(ep), Some(ts), Some(pk)) = (node_id, epoch, pinned_at_ms, pubkey)
            else {
                return Err("incomplete pin line");
            };
            if store.peers.contains_key(nid) {
                return Err("duplicate node in pin table");
            }
            store.global_rotation_epoch = tofu_epoch_advance(store.global_rotation_epoch, ep);
            store.peers.insert(
                nid.to_string(),
                PinnedPeer {
                    node_id: nid.to_string(),
                    pubkey: pk,
                    epoch: ep,
                    pinned_at_ms: ts,
                },
            );
        }
        Ok(store)
    }
}

const ZERO_PUBKEY: [u8; 32] = [0u8; 32];

fn ct_eq_32(a: &[u8; 32], b: &[u8; 32]) -> bool {
    astream_digest::ct_eq(a, b)
}

const fn parse_u64_dec_str(s: &str) -> Result<u64, &'static str> {
    let bytes = s.as_bytes();
    if bytes.is_empty() {
        return Err("empty decimal string");
    }
    let mut acc = 0u64;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if !b.is_ascii_digit() {
            return Err("non-digit in decimal string");
        }
        let d = b.saturating_sub(b'0') as u64;
        let Some(mul) = acc.checked_mul(10) else {
            return Err("decimal u64 overflow");
        };
        let Some(next) = mul.checked_add(d) else {
            return Err("decimal u64 overflow");
        };
        acc = next;
        rest = tail;
    }
    Ok(acc)
}

fn push_dec_u64(out: &mut String, mut val: u64) {
    if val == 0 {
        out.push('0');
        return;
    }
    let mut digits = [b'0'; 20];
    let mut len = 0usize;
    while val > 0 && len < 20 {
        let d = (val % 10) as u8;
        if let Some(slot) = digits.get_mut(len) {
            *slot = b'0' + d;
        }
        val /= 10;
        len = len.saturating_add(1);
    }
    while len > 0 {
        len = len.saturating_sub(1);
        if let Some(&ch) = digits.get(len) {
            out.push(ch as char);
        }
    }
}

fn validate_node_id(s: &str) -> Result<(), &'static str> {
    if s.is_empty() || s.len() > 64 {
        return Err("invalid node_id length");
    }
    let mut rest = s.as_bytes();
    while let &[b, ref tail @ ..] = rest {
        let ok = b.is_ascii_alphanumeric() || b == b'-' || b == b'_' || b == b'.';
        if !ok {
            return Err("invalid character in node_id");
        }
        rest = tail;
    }
    Ok(())
}

const fn hex_char_lower(nib: u8) -> char {
    match nib & 0x0F {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        10 => 'a',
        11 => 'b',
        12 => 'c',
        13 => 'd',
        14 => 'e',
        _ => 'f',
    }
}

fn push_hex_32(out: &mut String, key: &[u8; 32]) {
    let mut rest: &[u8] = key;
    while let &[b, ref tail @ ..] = rest {
        out.push(hex_char_lower(b >> 4));
        out.push(hex_char_lower(b & 0x0F));
        rest = tail;
    }
}

fn decode_nibble(b: u8) -> Result<u8, &'static str> {
    if b >= b'0' && b <= b'9' {
        Ok(b.saturating_sub(b'0'))
    } else if b >= b'a' && b <= b'f' {
        Ok(b.saturating_sub(b'a').saturating_add(10))
    } else if b >= b'A' && b <= b'F' {
        Ok(b.saturating_sub(b'A').saturating_add(10))
    } else {
        Err("invalid hex digit")
    }
}

fn decode_hex_32(s: &str) -> Result<[u8; 32], &'static str> {
    let bytes = s.as_bytes();
    if bytes.len() != 64 {
        return Err("expected 64-char hex pubkey");
    }
    let mut out = [0u8; 32];
    let mut rest = bytes;
    let mut idx = 0usize;
    while let &[h, l, ref tail @ ..] = rest {
        let hi = match decode_nibble(h) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        let lo = match decode_nibble(l) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };
        if let Some(slot) = out.get_mut(idx) {
            *slot = (hi << 4) | lo;
        }
        idx = idx.saturating_add(1);
        rest = tail;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tofu_pins_first_use_refuses_rogue_key_rotates_monotonically_and_round_trips() {
        let mut store = TofuPinStore::new(8);
        let k1 = [0x11u8; 32];
        let k_rogue = [0x22u8; 32];
        let k2 = [0x33u8; 32];

        assert_eq!(
            store
                .verify_or_pin("n-0011223344556677", &k1, 1000)
                .unwrap(),
            PinVerdict::PinnedFirstUse { epoch: 0 }
        );
        assert_eq!(
            store
                .verify_or_pin("n-0011223344556677", &k1, 1005)
                .unwrap(),
            PinVerdict::VerifiedMatch { epoch: 0 }
        );
        assert_eq!(
            store
                .verify_or_pin("n-0011223344556677", &k_rogue, 1010)
                .unwrap(),
            PinVerdict::KeyMismatchRefused { pinned_epoch: 0 }
        );

        // Explicit rotation advances epoch to 1 and accepts k2 while refusing k1.
        let ep = store
            .rotate_peer_key("n-0011223344556677", &k2, 2000)
            .unwrap();
        assert_eq!(ep, 1);
        assert_eq!(
            store
                .verify_or_pin("n-0011223344556677", &k2, 2005)
                .unwrap(),
            PinVerdict::VerifiedMatch { epoch: 1 }
        );
        assert_eq!(
            store
                .verify_or_pin("n-0011223344556677", &k1, 2010)
                .unwrap(),
            PinVerdict::KeyMismatchRefused { pinned_epoch: 1 }
        );

        let text = store.encode_text();
        let decoded = TofuPinStore::decode_text(&text, 8).unwrap();
        assert_eq!(decoded.global_rotation_epoch(), 1);
        assert_eq!(decoded.get("n-0011223344556677").unwrap().pubkey, k2);
    }

    #[test]
    fn refuses_zero_pubkey_same_key_rotation_and_duplicate_pin_fields() {
        let mut store = TofuPinStore::new(8);
        assert!(store.verify_or_pin("n-peer1", &[0u8; 32], 100).is_err());
        assert!(store.rotate_peer_key("n-peer1", &[0u8; 32], 100).is_err());

        let k1 = [0x44u8; 32];
        let k2 = [0x55u8; 32];
        assert_eq!(store.rotate_peer_key("n-peer1", &k1, 100).unwrap(), 1);
        // Same-key rotation is refused.
        assert!(store.rotate_peer_key("n-peer1", &k1, 101).is_err());
        // Rotating a second unseen peer advances global_rotation_epoch strictly beyond 1 -> 2.
        assert_eq!(store.rotate_peer_key("n-peer2", &k2, 102).unwrap(), 2);
        assert_eq!(store.global_rotation_epoch(), 2);

        let dup_line = "v=1 node=n-peer1 node=n-peer2 epoch=1 t=100 key=4444444444444444444444444444444444444444444444444444444444444444\n";
        assert!(TofuPinStore::decode_text(dup_line, 8).is_err());
    }
}
