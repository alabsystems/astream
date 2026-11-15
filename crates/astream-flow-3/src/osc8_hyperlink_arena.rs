//! Bounded deduplicating OSC 8 terminal hyperlink arena (`file://`, `conversation://`, `https://`).

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
#[path = "osc8_hyperlink_arena_island.rs"]
mod osc8_hyperlink_arena_island;
#[cfg(clean_islands)]
pub use osc8_hyperlink_arena_island::{osc8_slot_index_clamp, osc8_uri_len_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc8_slot_index_clamp(slot: u64) -> u64 {
    if slot < 256 {
        slot
    } else {
        256
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn osc8_uri_len_clamp(raw_len: u64) -> u64 {
    if raw_len < 2048 {
        raw_len
    } else {
        2048
    }
}

contract_fn! {
    #[must_use]
    pub const fn osc8_uri_within_max(raw_len: u64) -> bool
    clauses [ensures result == (raw_len < 2049)]
    {
        raw_len < 2049
    }
}

#[inline]
#[must_use]
pub const fn osc8_uri_admissible(raw_len: u64) -> bool {
    raw_len >= 1 && osc8_uri_within_max(raw_len)
}

pub const MAX_OSC8_SLOTS: usize = 256;
pub const MAX_OSC8_URI_BYTES: usize = 2048;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Osc8Entry {
    pub id_param: String,
    pub uri: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Osc8HyperlinkArena {
    slots: Vec<Osc8Entry>,
    evict_cursor: usize,
    active_slot: u16,
}

impl Osc8HyperlinkArena {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: Vec::new(),
            evict_cursor: 0,
            active_slot: 0,
        }
    }

    /// Current active hyperlink slot (`0` = none, `1..=256` = slot index + 1).
    #[must_use]
    pub const fn active_slot(&self) -> u16 {
        self.active_slot
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.slots.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }

    pub fn close_hyperlink(&mut self) {
        self.active_slot = 0;
    }

    /// Handle an OSC 8 sequence: empty `uri` closes the active hyperlink (`0`),
    /// overlong URIs (`> 2048` bytes) fail closed to `0`, and valid URIs deduplicate
    /// or allocate a bounded `1..=256` handle.
    pub fn open_or_close(&mut self, id_param: &str, uri: &str) -> u16 {
        if uri.is_empty() {
            self.active_slot = 0;
            return 0;
        }
        if !osc8_uri_admissible(uri.len() as u64) || id_param.len() > 256 {
            self.active_slot = 0;
            return 0;
        }
        let _ = osc8_uri_len_clamp(uri.len() as u64);
        let mut rest = self.slots.as_slice();
        let mut i = 0usize;
        while let [item, tail @ ..] = rest {
            if i >= MAX_OSC8_SLOTS {
                break;
            }
            if item.id_param == id_param && item.uri == uri {
                let handle = osc8_slot_index_clamp((i.saturating_add(1)) as u64) as u16;
                self.active_slot = handle;
                return handle;
            }
            i = i.saturating_add(1);
            rest = tail;
        }
        let entry = Osc8Entry {
            id_param: copy_str(id_param),
            uri: copy_str(uri),
        };
        if self.slots.len() < MAX_OSC8_SLOTS {
            self.slots.push(entry);
            let handle = osc8_slot_index_clamp(self.slots.len() as u64) as u16;
            self.active_slot = handle;
            handle
        } else {
            let idx = if self.evict_cursor < MAX_OSC8_SLOTS {
                self.evict_cursor
            } else {
                0
            };
            if let Some(slot) = self.slots.get_mut(idx) {
                *slot = entry;
            }
            let next_cur = idx.saturating_add(1);
            self.evict_cursor = if next_cur < MAX_OSC8_SLOTS {
                next_cur
            } else {
                0
            };
            let handle = osc8_slot_index_clamp((idx.saturating_add(1)) as u64) as u16;
            self.active_slot = handle;
            handle
        }
    }

    #[must_use]
    pub fn get(&self, handle: u16) -> Option<&Osc8Entry> {
        if handle == 0 {
            return None;
        }
        self.slots.get((handle as usize).saturating_sub(1))
    }
}

impl Default for Osc8HyperlinkArena {
    fn default() -> Self {
        Self::new()
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
    fn deduplicates_identical_osc8_links_closes_on_empty_and_rejects_overlong() {
        let mut arena = Osc8HyperlinkArena::new();
        assert!(arena.is_empty());
        let h1 = arena.open_or_close("L1", "file:///fixture-home/astream/src/lib.rs#L10");
        let h2 = arena.open_or_close("L1", "file:///fixture-home/astream/src/lib.rs#L10");
        assert_eq!(h1, 1);
        assert_eq!(h2, 1);
        assert_eq!(arena.len(), 1);
        assert_eq!(
            arena.get(h1).unwrap().uri,
            "file:///fixture-home/astream/src/lib.rs#L10"
        );
        arena.close_hyperlink();
        assert_eq!(arena.active_slot(), 0);
        assert_eq!(arena.open_or_close("", ""), 0);
        assert_eq!(arena.active_slot(), 0);
        let huge = "x".repeat(MAX_OSC8_URI_BYTES + 1);
        assert_eq!(arena.open_or_close("", &huge), 0);
        assert_eq!(osc8_slot_index_clamp(999), 256);
    }
}
