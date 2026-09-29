//! The visual perception modalities: **image** (a deterministic rasterization of
//! the screen) and **animation** (the image sequence over an offset range),
//! reconstructed from the recorded `Out` log at any offset.
//!
//! Because every frame is `fold(Out[0..=K])`, the animation is not a stored
//! video — it is **reconstructed on demand** from the log: scrub to any offset,
//! and (because each frame is content-addressed by a hash) identical frames dedup
//! and a *forked* timeline shares a bit-identical frame-hash prefix.
//!
//! Honest scope: [`rasterize`] is a deterministic **cell thumbnail** — one pixel
//! per cell, the resolved foreground if the cell is inked else the background.
//! It captures layout, colour, and activity-over-time exactly and reproducibly;
//! **glyph-accurate, pixel-exact rendering is the aterm rung** (out of tree, the
//! pixel oracle in `docs/DESIGN-astream-term.md` §6). It is zero-dependency.

use crate::screen::{attr, Cell, Color, Folder, Screen};

/// An RGB image, row-major, 3 bytes per pixel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Image {
    /// Width in pixels (= screen columns).
    pub width: u16,
    /// Height in pixels (= screen rows).
    pub height: u16,
    /// `width * height * 3` bytes, row-major RGB.
    pub rgb: Vec<u8>,
}

/// Rasterize a screen to a deterministic cell thumbnail (one pixel per cell:
/// the resolved foreground colour if the cell is inked, else the background).
/// Reverse video swaps the **resolved** colours, so a default-colour reverse
/// cell (a status bar, a selection) really inverts — black glyph on light grey
/// — rather than resolving each `Default` back to its own role's fallback.
pub fn rasterize(screen: &Screen) -> Image {
    let (cols, rows) = screen.dims();
    let mut rgb = Vec::with_capacity(cols as usize * rows as usize * 3);
    for r in 0..rows {
        for c in 0..cols {
            let cell = screen.cell(r, c).copied().unwrap_or(Cell::BLANK);
            let mut fg = color_rgb(cell.fg, [192, 192, 192]); // default fg: light grey
            let mut bg = color_rgb(cell.bg, [0, 0, 0]); // default bg: black
            if cell.attrs & attr::REVERSE != 0 {
                std::mem::swap(&mut fg, &mut bg);
            }
            let inked = cell.ch != ' ';
            let px = if inked { fg } else { bg };
            rgb.extend_from_slice(&px);
        }
    }
    Image {
        width: cols,
        height: rows,
        rgb,
    }
}

/// A content address for a screen (FNV-1a over its serialization). Identical
/// screens share a hash; the animation uses it to dedup and to detect forks.
pub fn frame_hash(screen: &Screen) -> u64 {
    let mut h = Fnv1a(0xcbf2_9ce4_8422_2325);
    screen.serialize_into(&mut h);
    h.0
}

/// FNV-1a over the bytes [`Screen::serialize_into`] streams, so hashing a frame
/// allocates nothing (it runs once per record on the pump's settle path).
struct Fnv1a(u64);

impl crate::screen::ByteSink for Fnv1a {
    fn extend_from_slice(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 ^= b as u64;
            self.0 = self.0.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
}

/// One entry in a reconstructed animation: the offset, its content hash, and
/// whether the screen *changed* from the previous offset (an `In`/`Exit` record
/// paints nothing, so consecutive frames are often identical — dedup on this).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnimFrame {
    /// The log offset this frame is `fold(Out[0..=offset])`.
    pub offset: usize,
    /// Content hash of the screen at this offset.
    pub hash: u64,
    /// `false` iff this frame is byte-identical to the previous one.
    pub changed: bool,
}

/// Reconstruct the animation timeline over offsets `[from, to]` (clamped) — the
/// content-addressed, dedup-flagged frame sequence. Materialize the pixels of a
/// frame on demand with `rasterize(frame(cols, rows, records, af.offset))`.
pub fn animation(
    cols: u16,
    rows: u16,
    records: &[crate::record::Record],
    from: usize,
    to: usize,
) -> Vec<AnimFrame> {
    let to = to.min(records.len().saturating_sub(1));
    if records.is_empty() || from > to {
        return Vec::new();
    }
    // One incremental fold: frame(k) is the fold of records[0..=k], so advancing
    // a single Folder yields every frame in turn instead of refolding the prefix
    // for each offset.
    let mut folder = Folder::new(cols, rows);
    for r in &records[..from] {
        folder.apply(r);
    }
    let mut out = Vec::with_capacity(to - from + 1);
    let mut prev: Option<u64> = None;
    for (k, r) in (from..=to).zip(&records[from..=to]) {
        folder.apply(r);
        let hash = frame_hash(folder.screen());
        out.push(AnimFrame {
            offset: k,
            hash,
            changed: prev != Some(hash),
        });
        prev = Some(hash);
    }
    out
}

/// The xterm-256 palette: 0–15 named, 16–231 the 6×6×6 colour cube, 232–255 the
/// grayscale ramp. A fixed, deterministic mapping.
fn palette(n: u8) -> [u8; 3] {
    const NAMED: [[u8; 3]; 16] = [
        [0, 0, 0],
        [128, 0, 0],
        [0, 128, 0],
        [128, 128, 0],
        [0, 0, 128],
        [128, 0, 128],
        [0, 128, 128],
        [192, 192, 192],
        [128, 128, 128],
        [255, 0, 0],
        [0, 255, 0],
        [255, 255, 0],
        [0, 0, 255],
        [255, 0, 255],
        [0, 255, 255],
        [255, 255, 255],
    ];
    match n {
        0..=15 => NAMED[n as usize],
        16..=231 => {
            let i = n - 16;
            let levels = [0u8, 95, 135, 175, 215, 255];
            [
                levels[(i / 36) as usize],
                levels[((i / 6) % 6) as usize],
                levels[(i % 6) as usize],
            ]
        }
        _ => {
            let v = 8 + (n - 232) * 10;
            [v, v, v]
        }
    }
}

fn color_rgb(color: Color, default: [u8; 3]) -> [u8; 3] {
    match color {
        Color::Default => default,
        Color::Indexed(n) => palette(n),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::perceive::frame;
    use crate::record::Record;

    /// The streamed hash is FNV-1a over exactly the bytes `serialize` returns,
    /// including the alternate-screen and saved-cursor tail.
    #[test]
    fn frame_hash_is_fnv_over_the_serialized_screen() {
        let fnv = |bytes: &[u8]| {
            bytes.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, &b| {
                (h ^ b as u64).wrapping_mul(0x0000_0100_0000_01b3)
            })
        };
        let recs = vec![
            Record::Out(b"\x1b[31mhello\x1b[0m\r\nworld\x1b7".to_vec()),
            Record::Out(b"\x1b[?1049h\x1b[2;3Halt\x1b[1;2r".to_vec()),
            Record::Resize { cols: 7, rows: 4 },
            Record::Out(b"\x1b[?1049l tail".to_vec()),
        ];
        for k in 0..recs.len() {
            let screen = frame(10, 5, &recs, k);
            assert_eq!(
                frame_hash(&screen),
                fnv(&screen.serialize()),
                "at record {k}"
            );
        }
    }

    #[test]
    fn rasterize_inks_glyphs_in_foreground_over_background() {
        // A red 'X' at (0,0); the rest blank.
        let recs = vec![Record::Out(b"\x1b[31mX".to_vec())];
        let img = rasterize(&frame(3, 1, &recs, 0));
        assert_eq!((img.width, img.height), (3, 1));
        assert_eq!(&img.rgb[0..3], &[128, 0, 0], "the inked cell is red (fg)");
        assert_eq!(&img.rgb[3..6], &[0, 0, 0], "the blank cell is black (bg)");
    }

    #[test]
    fn a_sub_range_animation_is_a_window_of_the_whole_one() {
        let recs: Vec<Record> = (0..6)
            .map(|i| Record::Out(format!("{i}\r\n").into_bytes()))
            .collect();
        let whole = animation(4, 3, &recs, 0, 99);
        assert_eq!(whole.len(), 6);
        let part = animation(4, 3, &recs, 2, 4);
        let hashes = |a: &[AnimFrame]| a.iter().map(|f| (f.offset, f.hash)).collect::<Vec<_>>();
        assert_eq!(hashes(&part), hashes(&whole[2..=4]));
        for af in &part {
            assert_eq!(af.hash, frame_hash(&frame(4, 3, &recs, af.offset)));
        }
        assert!(animation(4, 3, &recs, 5, 4).is_empty());
        assert!(animation(4, 3, &recs, 9, 12).is_empty());
        assert!(animation(4, 3, &[], 0, 0).is_empty());
    }

    #[test]
    fn reverse_video_inverts_default_colours_too() {
        // SGR 7 with the default pen: the glyph pixel takes the resolved default
        // bg (black) and a reversed blank takes the resolved default fg (grey).
        let recs = vec![Record::Out(b"\x1b[7mX ".to_vec())];
        let img = rasterize(&frame(3, 1, &recs, 0));
        assert_eq!(&img.rgb[0..3], &[0, 0, 0], "reversed glyph: black");
        assert_eq!(&img.rgb[3..6], &[192, 192, 192], "reversed blank: grey");
        assert_eq!(&img.rgb[6..9], &[0, 0, 0], "untouched blank: black");
    }
}
