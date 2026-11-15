// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! SIGHUP-driven capability & principal (`n-<hash>`) revocation reload controller
//! (`Astream.Cap.TlaPrincipalRevocationSighup`, Island #285; REQUIREMENTS R6 & `os.cordon`).

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "principal_revocation_sighup_island.rs"]
mod principal_revocation_sighup_island;
#[cfg(clean_islands)]
pub use principal_revocation_sighup_island::{revoc_entry_count_clamp, revoc_sighup_gen_advance};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn revoc_sighup_gen_advance(cur_gen: u64, observed_gen: u64) -> u64 {
    if cur_gen < observed_gen {
        observed_gen
    } else {
        cur_gen
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn revoc_entry_count_clamp(entries: u64, max_entries: u64) -> u64 {
    if entries < max_entries {
        entries
    } else {
        max_entries
    }
}

/// Hard ceiling (`4096`) on entries held in a reloaded [`PrincipalRevocationTable`].
pub const MAX_REVOCATION_ENTRIES: usize = 4096;

contract_fn! {
    /// Verified check `loaded_gen < sighup_gen`, linked via `clean-kernel-defeq` to
    /// `revoc_reload_needed_isl`.
    #[must_use]
    pub const fn revoc_reload_needed(loaded_gen: u64, sighup_gen: u64) -> bool
    clauses [ensures result == (loaded_gen < sighup_gen)]
    {
        loaded_gen < sighup_gen
    }
}

/// One parsed revocation entry (`principal:<id>` or `tag:<hex>`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RevocationRule {
    /// Revoke every capability, open subscription, and pending will of `principal` (e.g. `n-abc123`).
    Principal(String),
    /// Revoke a specific capability HMAC tag hex prefix (at least 16 hex chars).
    TagHexPrefix(String),
}

/// Error returned when a revocation file contains malformed rules or exceeds capacity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RevocationParseError {
    TooManyEntries { max: usize },
    InvalidLine { line_no: usize },
}

#[inline]
const fn is_lower_hex(b: u8) -> bool {
    (b >= b'0' && b <= b'9') || (b >= b'a' && b <= b'f')
}

const fn is_ascii_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\r' | b'\n' | 0x0C)
}

const fn trim_ascii_ws(mut s: &[u8]) -> &[u8] {
    while let [head, rest @ ..] = s {
        if is_ascii_ws(*head) {
            s = rest;
        } else {
            break;
        }
    }
    while let [rest @ .., last] = s {
        if is_ascii_ws(*last) {
            s = rest;
        } else {
            break;
        }
    }
    s
}

const fn split_first_line(mut s: &[u8]) -> (&[u8], &[u8]) {
    let orig = s;
    let mut len = 0usize;
    while let [b, rest @ ..] = s {
        if *b == b'\n' {
            if len <= orig.len() {
                let (head, _) = orig.split_at(len);
                return (head, rest);
            }
            return (orig, &[]);
        }
        s = rest;
        len = len.saturating_add(1);
    }
    (orig, &[])
}

const fn all_lower_hex(mut s: &[u8]) -> bool {
    while let [b, rest @ ..] = s {
        if !is_lower_hex(*b) {
            return false;
        }
        s = rest;
    }
    true
}

const fn bytes_starts_with(mut hay: &[u8], mut prefix: &[u8]) -> bool {
    if hay.len() < prefix.len() {
        return false;
    }
    while let [p, pt @ ..] = prefix {
        let [h, ht @ ..] = hay else {
            return false;
        };
        if *h != *p {
            return false;
        }
        hay = ht;
        prefix = pt;
    }
    true
}

/// Parse a revocation file (`principal:<id>` or `tag:<lowercase_hex>` per non-comment line).
pub fn parse_revocation_rules(text: &str) -> Result<Vec<RevocationRule>, RevocationParseError> {
    let mut out = Vec::new();
    let mut rem = text.as_bytes();
    let mut line_no = 0usize;
    while !rem.is_empty() {
        let (raw_line, next_rem) = split_first_line(rem);
        rem = next_rem;
        line_no = line_no.saturating_add(1);
        let trimmed = trim_ascii_ws(raw_line);
        if trimmed.is_empty() || trimmed.starts_with(b"#") {
            continue;
        }
        if out.len() >= MAX_REVOCATION_ENTRIES {
            return Err(RevocationParseError::TooManyEntries {
                max: MAX_REVOCATION_ENTRIES,
            });
        }
        if let Some(p_rest) = trimmed.strip_prefix(b"principal:") {
            let name_bytes = trim_ascii_ws(p_rest);
            if name_bytes.is_empty() || name_bytes.len() > 128 || has_ws_or_ctrl(name_bytes) {
                return Err(RevocationParseError::InvalidLine { line_no });
            }
            let Ok(name_str) = core::str::from_utf8(name_bytes) else {
                return Err(RevocationParseError::InvalidLine { line_no });
            };
            out.push(RevocationRule::Principal(copy_str(name_str)));
        } else if let Some(t_rest) = trimmed.strip_prefix(b"tag:") {
            let hb = trim_ascii_ws(t_rest);
            if hb.len() < 16 || hb.len() > 64 || !all_lower_hex(hb) {
                return Err(RevocationParseError::InvalidLine { line_no });
            }
            let Ok(hex_str) = core::str::from_utf8(hb) else {
                return Err(RevocationParseError::InvalidLine { line_no });
            };
            out.push(RevocationRule::TagHexPrefix(copy_str(hex_str)));
        } else {
            return Err(RevocationParseError::InvalidLine { line_no });
        }
    }
    Ok(out)
}

/// SIGHUP-synchronized revocation table preserving the prior active rules on a bad reload.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PrincipalRevocationTable {
    loaded_gen: u64,
    rules: Vec<RevocationRule>,
}

impl PrincipalRevocationTable {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            loaded_gen: 0,
            rules: Vec::new(),
        }
    }

    #[must_use]
    pub const fn loaded_gen(&self) -> u64 {
        self.loaded_gen
    }

    #[must_use]
    pub fn entry_count(&self) -> usize {
        revoc_entry_count_clamp(self.rules.len() as u64, MAX_REVOCATION_ENTRIES as u64) as usize
    }

    #[must_use]
    pub const fn needs_reload(&self, sighup_gen: u64) -> bool {
        revoc_reload_needed(self.loaded_gen, sighup_gen)
    }

    /// Apply a reload for `sighup_gen`; on parse error, keeps existing `rules` fail-closed!
    #[allow(clippy::question_mark)]
    pub fn apply_reload(
        &mut self,
        sighup_gen: u64,
        file_text: &str,
    ) -> Result<usize, RevocationParseError> {
        let parsed = match parse_revocation_rules(file_text) {
            Ok(p) => p,
            Err(e) => return Err(e),
        };
        if sighup_gen >= self.loaded_gen {
            self.rules = parsed;
            self.loaded_gen = revoc_sighup_gen_advance(self.loaded_gen, sighup_gen);
        }
        Ok(self.entry_count())
    }

    /// Check whether `principal` or `tag_hex` is revoked under the active generation.
    #[must_use]
    pub fn is_revoked(&self, principal: &str, tag_hex: &str) -> bool {
        let mut rest = self.rules.as_slice();
        let tag_bytes = tag_hex.as_bytes();
        while let [rule, tail @ ..] = rest {
            match rule {
                RevocationRule::Principal(p) => {
                    if p.as_str() == principal {
                        return true;
                    }
                }
                RevocationRule::TagHexPrefix(prefix) => {
                    if bytes_starts_with(tag_bytes, prefix.as_bytes()) {
                        return true;
                    }
                }
            }
            rest = tail;
        }
        false
    }
}

fn copy_str(src: &str) -> String {
    let mut out = String::new();
    out.push_str(src);
    out
}

fn has_ws_or_ctrl(bytes: &[u8]) -> bool {
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if b <= 0x20 || b == 0x7f {
            return true;
        }
        rest = tail;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reloads_on_sighup_advance_and_keeps_active_set_on_malformed_file() {
        let mut tbl = PrincipalRevocationTable::new();
        assert!(tbl.needs_reload(1));
        assert_eq!(
            tbl.apply_reload(
                1,
                "# revoked worker\nprincipal:n-deadbeef\ntag:0123456789abcdef\n",
            ),
            Ok(2)
        );
        assert!(!tbl.needs_reload(1));
        assert!(tbl.is_revoked("n-deadbeef", "ffffffffffffffff"));
        assert!(tbl.is_revoked("n-good", "0123456789abcdef9999"));
        assert!(!tbl.is_revoked("n-good", "fedcba9876543210"));

        assert!(tbl.needs_reload(2));
        assert_eq!(
            tbl.apply_reload(2, "garbage-directive"),
            Err(RevocationParseError::InvalidLine { line_no: 1 })
        );
        assert_eq!(tbl.loaded_gen(), 1);
        assert!(tbl.is_revoked("n-deadbeef", "ffffffffffffffff"));
    }
}
