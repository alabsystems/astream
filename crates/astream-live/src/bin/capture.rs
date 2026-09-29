//! `capture` — the live-capture CLI: record ONE real Anthropic model completion
//! and replay the session assembled around it through the in-tree substrate.
//!
//! This is the master seed's **non-hermetic** step, so it is a runnable TOOL,
//! never a green evidence claim (the hermetic parse + replay + fork half is the
//! green claim `cognition.live-bridge.parse-and-replay`). It captures over one of
//! two real, `#[ignore]`-gated paths:
//!
//! * `ANTHROPIC_API_KEY` set → `capture_live`: a keyed `curl` to the Messages API
//!   (key via curl's stdin config, never argv);
//! * no key → `capture_via_cli`: the authenticated `claude` CLI (the local Claude
//!   Code session; the model is asked to WRITE a Messages-shaped JSON object, so
//!   its tool_use block is model-authored text in that shape, not an API block).
//!
//! It exits non-zero only when the chosen path fails (no key AND no working
//! `claude` CLI, network/API error, unparseable response) — a no-key run on a
//! machine with an authenticated CLI performs a real model call and exits 0.
//!
//! ### What is real and what is not
//!
//! Only the model's **completion** is captured live. This binary does NOT run the
//! tool the model called and records NO real effect: the tool output
//! (`"BUILD OK: 0 errors"`), its error flag (`false`), and the effect clock
//! (`1_700_000_000`) below are fixed PLACEHOLDERS handed to `unified_from_capture`,
//! whatever the task was. The replay it then proves deterministic is of the real
//! completion plus those placeholders. Running the captured tool call under a
//! recording seam (real stdout/exit, a taped clock) is a documented seed.
//!
//! ```text
//! ANTHROPIC_API_KEY=... cargo run -p astream-live --bin capture -- "<prompt>" [model]
//! cargo run -p astream-live --bin capture -- "<prompt>"       # via the claude CLI
//! ```

use astream_agent::replay_session;
use astream_live::{capture_live, capture_via_cli, unified_from_capture};
use std::process::ExitCode;

/// The placeholder tool result and clock (see the module doc): NOT a tool run.
const PLACEHOLDER_TOOL_OUTPUT: &str = "BUILD OK: 0 errors";
const PLACEHOLDER_IS_ERROR: bool = false;
const PLACEHOLDER_CLOCK: u64 = 1_700_000_000;

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let prompt = args
        .next()
        .unwrap_or_else(|| "Build the Rust project and report whether it compiles.".to_string());
    let model = args
        .next()
        .unwrap_or_else(|| "claude-sonnet-4-6".to_string());

    // Two real, non-hermetic capture paths: a raw keyed Messages call (curl) when
    // ANTHROPIC_API_KEY is set, else the authenticated `claude` CLI (no key needed —
    // it uses the local Claude Code session). Either way the model completion is real.
    let completion = if std::env::var("ANTHROPIC_API_KEY").is_ok() {
        capture_live(&prompt, &model)
    } else {
        eprintln!("(no ANTHROPIC_API_KEY — capturing via the authenticated `claude` CLI)");
        capture_via_cli(&prompt)
    };
    let completion = match completion {
        Ok(c) => c,
        Err(e) => {
            eprintln!("capture failed: {e}");
            eprintln!(
                "(the live capture is the master seed's non-hermetic step: it needs \
                 either ANTHROPIC_API_KEY or an authenticated `claude` CLI)"
            );
            return ExitCode::FAILURE;
        }
    };

    // Assemble the unified four-stream turn around the real completion and replay
    // it in-tree, deterministically. The tool result and clock are placeholders:
    // the tool is NOT run here (see the module doc).
    let events = unified_from_capture(
        completion,
        PLACEHOLDER_TOOL_OUTPUT,
        PLACEHOLDER_IS_ERROR,
        PLACEHOLDER_CLOCK,
    );
    let a = replay_session(&events, 80, 12);
    let b = replay_session(&events, 80, 12);
    let deterministic = a == b;
    println!(
        "captured a live completion + replayed it with a PLACEHOLDER tool result \
         ({PLACEHOLDER_TOOL_OUTPUT:?}, is_error={PLACEHOLDER_IS_ERROR}) and clock \
         ({PLACEHOLDER_CLOCK}; the tool was NOT run): {} decisions, {} inputs applied, \
         screen_hash={:016x}, deterministic={}",
        a.decisions.len(),
        a.inputs_applied,
        a.screen_hash,
        deterministic
    );
    if deterministic {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
