#![forbid(unsafe_code)]
//! # astream-term
//!
//! A deterministic record/replay PTY substrate (see
//! `docs/DESIGN-astream-term.md`). This crate is **rung 0.5** of that plan: the
//! pure primitive everything else is built on — the screen fold, with no I/O and
//! no dependencies — proving the whole replay thesis in miniature.
//!
//! ## The spine: the screen is a pure fold of recorded output
//!
//! A terminal session is two ordered byte streams (`In` keystrokes, `Out` PTY
//! bytes) plus a derived screen. The screen is a **pure function** of the
//! recorded `Out`/`Resize` records:
//!
//! ```text
//! screen_n = vt_apply(screen_{n-1}, record_n)
//! ```
//!
//! `vt_apply` ignores `In` (input does not paint — only the PTY's echoed `Out`
//! does) and `Exit`. Because the fold touches no clock, no randomness, and no
//! I/O, replaying the same records always yields a byte-identical screen. That
//! purity *is* the replay guarantee, and it is testable in isolation — which is
//! exactly what `tests/suite/screen_fold.rs` does, earning the manifest claim
//! `term.screen-fold.deterministic`.
//!
//! What deliberately does **not** live here: the wire envelope (records riding
//! inside an `astream_wire::Frame` payload), offsets, the recorded logical
//! clock, durable append and `/a/state` materialization are `astream-engine`;
//! the PTY driver is `astream-host`; the bus and its TCP transport are
//! `astream-broker`. This crate stays a pure, zero-dependency fold they all
//! share.

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this crate's Clean islands compile, for a compiler
// that cannot lex the islands.
#[cfg(any(test, not(clean_islands)))]
mod twins;

pub mod events;
pub mod ops;
pub mod overlap_echo;
pub mod perceive;
pub mod predict;
pub mod program_predict;
pub mod record;
pub mod render;
pub mod screen;

pub use events::{
    classify, event_advance_offset_monotone, event_carry_within_bound, quiesced_at,
    sync_bytes_clamp, sync_hold_ticks_clamp, sync_within_budget, EventClassifier, Profile,
    SessionEvent, MAX_SYNC_HOLD_TICKS, MAX_SYNC_OUTPUT_BYTES,
};
pub use ops::{
    decode_ops, encode_ops, op_clamp_scroll_top, op_scroll_region_nonempty, OpsWireError, ScreenOp,
    MAX_MODE_PARAMS, MAX_OPS_PER_BATCH, OPS_WIRE_MAGIC, OPS_WIRE_VERSION,
};
pub use overlap_echo::{
    echo_matched_advance, echo_queue_len_clamp, echo_queue_within_cap, AttributedEchoSpan,
    EchoAttribution, ExpectedEcho, InFlightEchoQueue, MAX_IN_FLIGHT_ECHO_BYTES,
};
pub use perceive::{
    blocks, frame, perceive_clamp_take_count, perceive_row_in_bounds, search, text, Block, Hit,
};
pub use predict::{
    echo_admit_causal_watermark, echo_causal_watermark_select, echo_watermark_monotone,
    watermark_advances, Predictor, Verdict,
};
pub use program_predict::{
    is_cursor_relative_ops, program_ops_within_cap, program_rule_cap_clamp, ProgramPredictor,
    ScreenContext, SpeculativeTerminal, MAX_OPS_PER_RULE, MAX_PROGRAM_RULES, MAX_RULE_INPUT_BYTES,
};
pub use record::{record_client_seq_advance, record_tag_paints_screen, Record};
pub use render::{
    animation, frame_hash, rasterize, render_clamp_end_offset, render_frame_changed, AnimFrame,
    Image,
};
pub use screen::{
    apply_ops, apply_ops_to, cell_width_is_valid, char_display_width, color_clamp_channel,
    combining_cap_clamp, combining_len_within_cap, dec_special_graphic, emit_ops, fold,
    is_combining_mark, is_vs16_emoji_capable, is_wide_char, screen_clamp_dim,
    screen_coord_in_bounds, vs_cursor_advance_clamp, vs_width_clamp, vs_width_valid,
    wide_cell_width_clamp, wide_spacer_col_clamp, Cell, Charset, Color, Folder, Screen, Underline,
    MAX_COMBINING, MAX_OSC_CWD_BYTES, MAX_OSC_TITLE_BYTES, WIRE_UNDERLINE,
};
