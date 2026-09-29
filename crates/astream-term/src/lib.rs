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
//! exactly what `tests/screen_fold.rs` does, earning the manifest claim
//! `term.screen-fold.deterministic`.
//!
//! What deliberately does **not** live here: the wire envelope (records riding
//! inside an `astream_wire::Frame` payload), offsets, the recorded logical
//! clock, durable append and `/a/state` materialization are `astream-engine`;
//! the PTY driver is `astream-host`; the bus and its TCP transport are
//! `astream-broker`. This crate stays a pure, zero-dependency fold they all
//! share.

pub mod events;
pub mod ops;
pub mod perceive;
pub mod predict;
pub mod record;
pub mod render;
pub mod screen;

pub use events::{classify, quiesced_at, EventClassifier, Profile, SessionEvent};
pub use ops::ScreenOp;
pub use perceive::{blocks, frame, search, text, Block, Hit};
pub use predict::{Predictor, Verdict};
pub use record::Record;
pub use render::{animation, frame_hash, rasterize, AnimFrame, Image};
pub use screen::{apply_ops, emit_ops, fold, Cell, Color, Folder, Screen};
