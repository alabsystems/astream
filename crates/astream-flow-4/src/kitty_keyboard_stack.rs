//! Kitty progressive keyboard enhancement protocol stack (`CSI > u` / `CSI < u` / `CSI = u`).

#[cfg(clean_islands)]
#[path = "kitty_keyboard_stack_island.rs"]
mod kitty_keyboard_stack_island;
#[cfg(clean_islands)]
pub use kitty_keyboard_stack_island::{kitty_kbd_depth_clamp, kitty_kbd_flags_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kitty_kbd_depth_clamp(depth: u64) -> u64 {
    if depth < 16 {
        depth
    } else {
        16
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kitty_kbd_flags_clamp(flags: u64) -> u64 {
    if flags < 31 {
        flags
    } else {
        31
    }
}

contract_fn! {
    #[must_use]
    pub const fn kitty_kbd_pop_safe(pop_count: u64, cur_depth: u64) -> bool
    clauses [ensures result == (pop_count <= cur_depth)]
    {
        pop_count <= cur_depth
    }
}

pub const MAX_KITTY_KBD_DEPTH: usize = 16;
pub const KITTY_ALL_FLAGS_MASK: u8 = 0x1F;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KittySetMode {
    Assign,
    BitwiseOr,
    BitwiseAndNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KittyKeyboardStack {
    entries: [u8; MAX_KITTY_KBD_DEPTH],
    depth: usize,
    current_flags: u8,
}

impl KittyKeyboardStack {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            entries: [0; MAX_KITTY_KBD_DEPTH],
            depth: 0,
            current_flags: 0,
        }
    }

    #[must_use]
    pub const fn current_flags(&self) -> u8 {
        self.current_flags
    }

    #[must_use]
    pub const fn depth(&self) -> usize {
        self.depth
    }

    /// `CSI > flags u`: push `current_flags` (evicting oldest if full) and set `flags & 0x1F`.
    pub fn push(&mut self, raw_flags: u8) {
        if self.depth < MAX_KITTY_KBD_DEPTH {
            if let Some(slot) = self.entries.get_mut(self.depth) {
                *slot = self.current_flags;
            }
            self.depth = kitty_kbd_depth_clamp((self.depth.saturating_add(1)) as u64) as usize;
        } else {
            let mut i = 0usize;
            while i < MAX_KITTY_KBD_DEPTH - 1 {
                let next = match self.entries.get(i.saturating_add(1)) {
                    Some(&v) => v,
                    None => 0,
                };
                if let Some(slot) = self.entries.get_mut(i) {
                    *slot = next;
                }
                i = i.saturating_add(1);
            }
            if let Some(slot) = self.entries.last_mut() {
                *slot = self.current_flags;
            }
            self.depth = MAX_KITTY_KBD_DEPTH;
        }
        let masked = (raw_flags & KITTY_ALL_FLAGS_MASK) as u64;
        self.current_flags = kitty_kbd_flags_clamp(masked) as u8;
    }

    /// `CSI < count u`: pop `max(1, count)` entries; underflow resets `current_flags` to `0`.
    pub fn pop(&mut self, count: usize) {
        let n = if count == 0 { 1 } else { count };
        let cur_depth = if self.depth <= MAX_KITTY_KBD_DEPTH {
            self.depth
        } else {
            MAX_KITTY_KBD_DEPTH
        };
        if kitty_kbd_pop_safe(n as u64, cur_depth as u64) && n > 0 && n <= cur_depth {
            let new_depth = cur_depth.saturating_sub(n);
            self.current_flags = match self.entries.get(new_depth) {
                Some(&v) => v,
                None => 0,
            };
            self.depth = kitty_kbd_depth_clamp(new_depth as u64) as usize;
        } else {
            self.depth = 0;
            self.current_flags = 0;
        }
    }

    /// `CSI = flags ; mode u`: update `current_flags` in place without changing stack depth.
    pub fn set_mode(&mut self, raw_flags: u8, mode: KittySetMode) {
        let masked = kitty_kbd_flags_clamp((raw_flags & KITTY_ALL_FLAGS_MASK) as u64) as u8;
        self.current_flags = match mode {
            KittySetMode::Assign => masked,
            KittySetMode::BitwiseOr => self.current_flags | masked,
            KittySetMode::BitwiseAndNot => self.current_flags & !masked,
        };
    }
}

impl Default for KittyKeyboardStack {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_set_pop_and_eviction_follow_kitty_keyboard_spec() {
        let mut s = KittyKeyboardStack::new();
        s.push(0b00001);
        s.push(0b01011);
        assert_eq!(s.current_flags(), 0b01011);
        assert_eq!(s.depth(), 2);
        s.set_mode(0b10000, KittySetMode::BitwiseOr);
        assert_eq!(s.current_flags(), 0b11011);
        s.set_mode(0b00010, KittySetMode::BitwiseAndNot);
        assert_eq!(s.current_flags(), 0b11001);
        s.set_mode(0b00101, KittySetMode::Assign);
        assert_eq!(s.current_flags(), 0b00101);
        s.pop(1);
        assert_eq!(s.current_flags(), 0b00001);
        s.pop(5);
        assert_eq!(s.current_flags(), 0);
        assert_eq!(s.depth(), 0);
    }
}
