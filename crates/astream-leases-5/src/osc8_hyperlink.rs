// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Bounded, scheme-allowlisted `OSC 8` terminal hyperlink table
//! (`Astream.Term.TlaOsc8Hyperlink`; `OSC 8 ; params ; uri ST`).
//!
//! Supports clickable `file://`, `https://`, `http://`, and `conversation://` links in
//! `aterm` panes while rejecting dangerous URI schemes (`javascript:`, `data:`, `vbscript:`),
//! control characters, and oversize URIs (`> MAX_OSC8_URI_BYTES`, certified via
//! [`osc8_link_uri_within_cap`] and Clean-origin [`osc8_link_uri_clamp`]), and bounding active
//! interned hyperlink slots to [`MAX_OSC8_SLOTS`] via Clean-origin [`osc8_link_slot_clamp`].

#![allow(
    clippy::question_mark,
    clippy::manual_map,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "osc8_hyperlink_island.rs"]
mod osc8_hyperlink_island;
#[cfg(clean_islands)]
pub use osc8_hyperlink_island::{osc8_link_slot_clamp, osc8_link_uri_clamp};

/// Mirror of Clean's `osc8_link_uri_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc8_link_uri_clamp(uri_len: u64, max_uri_len: u64) -> u64 {
    if uri_len < max_uri_len {
        uri_len
    } else {
        max_uri_len
    }
}

/// Mirror of Clean's `osc8_link_slot_clamp` when compiled without `--cfg clean_islands`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc8_link_slot_clamp(slots: u64, max_slots: u64) -> u64 {
    if slots < max_slots {
        slots
    } else {
        max_slots
    }
}

contract_fn! {
    /// Kernel-certified check that an OSC 8 URI byte length fits within `max_len`
    /// (`uri_len <= max_len`), linked via `clean-kernel-defeq` to `osc8_link_uri_within_cap_isl`.
    #[must_use]
    pub const fn osc8_link_uri_within_cap(uri_len: usize, max_len: usize) -> bool
    clauses [ensures result == (uri_len <= max_len)]
    {
        uri_len <= max_len
    }
}

/// Maximum accepted `OSC 8` URI byte length (`2048` bytes).
pub const MAX_OSC8_URI_BYTES: usize = 2048;

/// Maximum `id=` parameter byte length (`128` bytes).
pub const MAX_OSC8_ID_BYTES: usize = 128;

/// Maximum interned hyperlinks retained in a single [`Osc8HyperlinkTable`] (`256`).
pub const MAX_OSC8_SLOTS: usize = 256;

/// Non-zero hyperlink handle stored on terminal cells (`1..=256`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HyperlinkId(pub u16);

/// Interned `OSC 8` hyperlink entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HyperlinkEntry {
    /// Optional explicit `id=<value>` grouping token from `OSC 8 ; id=... ; uri`.
    pub explicit_id: Option<String>,
    /// Validated allowlisted URI (`file://`, `https://`, `http://`, or `conversation://`).
    pub uri: String,
}

#[must_use]
const fn has_allowed_scheme_bytes(uri: &[u8]) -> bool {
    matches!(
        uri,
        [b'f', b'i', b'l', b'e', b':', b'/', b'/', ..]
            | [b'h', b't', b't', b'p', b's', b':', b'/', b'/', ..]
            | [b'h', b't', b't', b'p', b':', b'/', b'/', ..]
            | [
                b'c',
                b'o',
                b'n',
                b'v',
                b'e',
                b'r',
                b's',
                b'a',
                b't',
                b'i',
                b'o',
                b'n',
                b':',
                b'/',
                b'/',
                ..
            ]
    )
}

#[must_use]
const fn has_only_printable_uri_bytes(bytes: &[u8]) -> bool {
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if b <= 0x20 || b == 0x7f {
            return false;
        }
        rest = tail;
    }
    true
}

fn split_once_byte(bytes: &[u8], delim: u8) -> Option<(&[u8], &[u8])> {
    let mut i = 0usize;
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if b == delim {
            return Some((bytes.get(..i)?, tail));
        }
        i = i.saturating_add(1);
        rest = tail;
    }
    None
}

fn extract_explicit_id(params_bytes: &[u8]) -> Option<String> {
    let mut rest = params_bytes;
    loop {
        let (part, next) = match split_once_byte(rest, b':') {
            Some((p, n)) => (p, Some(n)),
            None => (rest, None),
        };
        if let Some(val) = part.strip_prefix(b"id=") {
            if !val.is_empty()
                && val.len() <= MAX_OSC8_ID_BYTES
                && has_only_printable_uri_bytes(val)
            {
                return match std::str::from_utf8(val) {
                    Ok(s) => Some(copy_str(s)),
                    Err(_) => None,
                };
            }
            return None;
        }
        match next {
            Some(n) => rest = n,
            None => return None,
        }
    }
}

/// Bounded interning table and active-brush tracker for `OSC 8` terminal hyperlinks.
#[derive(Debug, Clone, Default)]
pub struct Osc8HyperlinkTable {
    entries: Vec<HyperlinkEntry>,
    active: Option<HyperlinkId>,
    next_evict_idx: usize,
}

impl Osc8HyperlinkTable {
    /// Construct an empty hyperlink table.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
            active: None,
            next_evict_idx: 0,
        }
    }

    /// Currently active hyperlink applied to newly printed cells (`None` after `OSC 8 ;; ST`).
    #[must_use]
    pub const fn active_link(&self) -> Option<HyperlinkId> {
        self.active
    }

    /// Number of interned hyperlink entries (`<= MAX_OSC8_SLOTS`).
    #[must_use]
    pub fn len(&self) -> usize {
        osc8_link_slot_clamp(self.entries.len() as u64, MAX_OSC8_SLOTS as u64) as usize
    }

    /// Whether zero hyperlinks are interned.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Resolve a [`HyperlinkId`] back to its [`HyperlinkEntry`].
    #[must_use]
    pub fn resolve(&self, id: HyperlinkId) -> Option<&HyperlinkEntry> {
        if id.0 == 0 {
            return None;
        }
        self.entries.get(usize::from(id.0.saturating_sub(1)))
    }

    /// Process an `OSC 8` payload (`"<params>;<uri>"`, stripped of leading `8;`):
    /// - Empty `<uri>` closes the active hyperlink (`active = None`).
    /// - Valid allowlisted `<uri>` (`<= MAX_OSC8_URI_BYTES`) interns or deduplicates the
    ///   entry and sets `active = Some(id)`.
    /// - Disallowed scheme or oversize/control-tainted `<uri>` fails closed (`active = None`).
    pub fn apply_osc8_payload(&mut self, payload: &str) -> Option<HyperlinkId> {
        let Some((params_bytes, uri_bytes)) = split_once_byte(payload.as_bytes(), b';') else {
            self.active = None;
            return None;
        };
        if uri_bytes.is_empty() {
            self.active = None;
            return None;
        }
        let clamped_len =
            osc8_link_uri_clamp(uri_bytes.len() as u64, MAX_OSC8_URI_BYTES as u64) as usize;
        if uri_bytes.len() != clamped_len
            || !osc8_link_uri_within_cap(uri_bytes.len(), MAX_OSC8_URI_BYTES)
            || !has_allowed_scheme_bytes(uri_bytes)
            || !has_only_printable_uri_bytes(uri_bytes)
        {
            self.active = None;
            return None;
        }
        let Ok(uri) = std::str::from_utf8(uri_bytes) else {
            self.active = None;
            return None;
        };
        let explicit_id = extract_explicit_id(params_bytes);

        let mut i = 0usize;
        while i < self.entries.len() {
            if let Some(existing) = self.entries.get(i) {
                if existing.uri == uri && existing.explicit_id == explicit_id {
                    let hid = HyperlinkId(i.saturating_add(1) as u16);
                    self.active = Some(hid);
                    return Some(hid);
                }
            }
            i = i.saturating_add(1);
        }

        let entry = HyperlinkEntry {
            explicit_id,
            uri: copy_str(uri),
        };
        if self.entries.len() < MAX_OSC8_SLOTS {
            self.entries.push(entry);
            let capped =
                osc8_link_slot_clamp(self.entries.len() as u64, MAX_OSC8_SLOTS as u64) as u16;
            let hid = HyperlinkId(capped);
            self.active = Some(hid);
            Some(hid)
        } else {
            let slot = if self.next_evict_idx < MAX_OSC8_SLOTS {
                self.next_evict_idx
            } else {
                0
            };
            let next_idx = slot.saturating_add(1);
            self.next_evict_idx = if next_idx < MAX_OSC8_SLOTS {
                next_idx
            } else {
                0
            };
            if let Some(target) = self.entries.get_mut(slot) {
                *target = entry;
            }
            let hid = HyperlinkId((slot.saturating_add(1)) as u16);
            self.active = Some(hid);
            Some(hid)
        }
    }
}

fn copy_str(src: &str) -> String {
    let mut out = String::new();
    out.push_str(src);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn osc8_interns_file_and_conversation_links_and_rejects_javascript() {
        let mut tbl = Osc8HyperlinkTable::new();
        let id1 = tbl
            .apply_osc8_payload("id=err1;file:///fixture-home/astream/src/lib.rs#L10-L20")
            .expect("valid file link");
        assert_eq!(tbl.active_link(), Some(id1));
        assert_eq!(
            tbl.resolve(id1).unwrap().explicit_id.as_deref(),
            Some("err1")
        );

        let id1_dup = tbl
            .apply_osc8_payload("id=err1;file:///fixture-home/astream/src/lib.rs#L10-L20")
            .unwrap();
        assert_eq!(id1, id1_dup);
        assert_eq!(tbl.len(), 1);

        let id2 = tbl
            .apply_osc8_payload(";conversation://31bdcf2b-4697-4d9a-a7c4-dc9f84cbcdbc")
            .unwrap();
        assert_ne!(id1, id2);
        assert_eq!(tbl.apply_osc8_payload(";"), None);
        assert_eq!(tbl.active_link(), None);

        assert_eq!(tbl.apply_osc8_payload(";javascript:alert(1)"), None);
        assert_eq!(tbl.active_link(), None);
    }
}
