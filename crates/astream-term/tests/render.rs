//! Evidence for `term.perceive.render-deterministic`: the image and animation
//! modalities, reconstructed from the recorded Out log at any offset.
//!
//! `rasterize` is a deterministic function of the screen; `frame(K)` is the
//! screen as of any offset; `animation` is the content-addressed, dedup-flagged
//! frame sequence; and a forked timeline shares a bit-identical frame-hash prefix
//! and diverges only after the fork — so the same recording is a scrubbable,
//! forkable movie, reconstructed (not stored) from the one log.

use astream_term::{animation, frame, frame_hash, rasterize, Record};
use proptest::prelude::*;

const COLS: u16 = 20;
const ROWS: u16 = 4;

fn out(s: &[u8]) -> Record {
    Record::Out(s.to_vec())
}

fn session() -> Vec<Record> {
    vec![
        out(b"\x1b[2Jline one\r\n"), // offset 0: paints
        out(b"line two\r\n"),        // offset 1: paints
        Record::In {
            // offset 2: paints NOTHING (unchanged frame)
            bytes: b"x".to_vec(),
            client_id: 1,
            client_seq: 1,
        },
        out(b"line three"),       // offset 3: paints
        Record::Exit { code: 0 }, // offset 4: paints NOTHING (unchanged frame)
    ]
}

#[test]
fn rasterize_resolves_fg_if_inked_else_bg_and_honours_reverse_video() {
    // A red glyph, a blank on a blue background, a reversed default-colour glyph
    // and a reversed default-colour blank — each pixel checked against the rule:
    // resolved fg if inked else bg, with reverse video swapping the RESOLVED
    // colours (so a default-colour reverse cell really inverts; resolving each
    // Default against its own role's fallback after the swap rendered it plain).
    let recs = vec![out(b"\x1b[31mX\x1b[0;44m \x1b[0;7mY \x1b[0m ")];
    let img = rasterize(&frame(6, 1, &recs, 0));
    assert_eq!((img.width, img.height), (6, 1));
    let px = |c: usize| &img.rgb[c * 3..c * 3 + 3];
    assert_eq!(px(0), &[128, 0, 0], "inked red: fg");
    assert_eq!(px(1), &[0, 0, 128], "blank on blue: bg");
    assert_eq!(
        px(2),
        &[0, 0, 0],
        "reversed default glyph: resolved bg (black)"
    );
    assert_eq!(
        px(3),
        &[192, 192, 192],
        "reversed default blank: resolved fg"
    );
    assert_eq!(px(4), &[0, 0, 0], "plain blank: default bg");
    assert_eq!(px(5), &[0, 0, 0], "never painted: default bg");
}

#[test]
fn image_is_deterministic_and_addresses_the_frame() {
    let recs = session();

    // Rasterize is a pure function of the screen.
    let s = frame(COLS, ROWS, &recs, recs.len() - 1);
    assert_eq!(rasterize(&s), rasterize(&s));
    assert_eq!(rasterize(&s).rgb.len(), COLS as usize * ROWS as usize * 3);

    // The content hash addresses the frame: equal screens hash equal, the image
    // tracks the hash.
    let s2 = frame(COLS, ROWS, &recs, recs.len() - 1);
    assert_eq!(frame_hash(&s), frame_hash(&s2));
    assert_eq!(rasterize(&s), rasterize(&s2));
}

#[test]
fn animation_reconstructs_every_offset_and_dedups_unchanged_frames() {
    let recs = session();
    let anim = animation(COLS, ROWS, &recs, 0, recs.len() - 1);
    assert_eq!(anim.len(), recs.len());

    // Each frame's hash is exactly the hash of the screen folded to that offset.
    for af in &anim {
        assert_eq!(af.hash, frame_hash(&frame(COLS, ROWS, &recs, af.offset)));
    }

    // Offset 2 is an `In` record and offset 4 an `Exit` — neither paints, so
    // their frames are unchanged.
    assert!(!anim[2].changed, "the In record produced no visual change");
    assert!(
        !anim[4].changed,
        "the Exit record produced no visual change"
    );
    // The painting records did change the screen.
    assert!(anim[0].changed && anim[1].changed && anim[3].changed);
}

#[test]
fn a_forked_timeline_shares_a_frame_hash_prefix() {
    let recs = session();
    let n = 1; // fork after offset 1
    let mut forked = recs.clone();
    forked[2] = out(b"DIVERGE\r\n"); // swap the (non-painting) In for painting output

    let a = animation(COLS, ROWS, &recs, 0, recs.len() - 1);
    let b = animation(COLS, ROWS, &forked, 0, forked.len() - 1);

    // Frames [0..=n] are bit-identical (shared Merkle prefix).
    for k in 0..=n {
        assert_eq!(a[k].hash, b[k].hash, "frame {k} is shared before the fork");
    }
    // The timelines diverge at/after the fork.
    assert_ne!(
        a[n + 1].hash,
        b[n + 1].hash,
        "the fork diverges after offset {n}"
    );
}

proptest! {
    /// Rasterize and animation never panic, are deterministic, and every frame
    /// hash matches an independent fold at that offset — for arbitrary bytes.
    #[test]
    fn render_is_deterministic_and_panic_free(
        chunks in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..10), 1..6),
        cols in 1u16..16,
        rows in 1u16..6,
    ) {
        let recs: Vec<Record> = chunks.iter().map(|c| Record::Out(c.clone())).collect();
        let anim = animation(cols, rows, &recs, 0, recs.len() - 1);
        prop_assert_eq!(anim.len(), recs.len());
        for af in &anim {
            let s = frame(cols, rows, &recs, af.offset);
            prop_assert_eq!(af.hash, frame_hash(&s));
            prop_assert_eq!(rasterize(&s), rasterize(&s)); // deterministic
            prop_assert_eq!(rasterize(&s).rgb.len(), cols as usize * rows as usize * 3);
        }
    }
}
