# Theory: deterministic sessions — one object at three layers

A cross-repo design record spanning **astream** (the deterministic replay
substrate / distributed log) and **aterm** (`~/aterm`, the headless,
introspectable, model-checked terminal kernel). It states the unifying theory and
the novel surface it opens, in both projects' honesty discipline: every bold
claim is tagged **BUILT** / **DESIGNED-FOR-VERIFICATION** / **SEED** (the
re-runnable command that would make it real). Ambition is bounded only by the
size of the seed we can attach — so here we attach the biggest seeds we honestly
can.

> **Status & home doc.** The BUILT-vs-DESIGNED account of the in-repo terminal
> substrate (the determinism dial, the verb/event model) lives in
> [`DESIGN-astream-term.md`](DESIGN-astream-term.md); the claim ledger of record is
> `evidence/manifest.toml`. This doc is the *theory*; the
> determinism dial of §2 is the canonical honesty frame adopted there. All four
> rungs carry green claims today: Render and Session; Effects in its cooperative
> form and its Linux `ptrace` foreign-process form; Cognition as hermetic
> replay + fork (a *live* model turn is captured but is non-hermetic, so it is
> never a green claim). The status notes below each section are updated to match.

## 0. The identity that makes this one project

aterm's kernel proves a gap-free event-log spine: **`seq == count`** (every
appended event advances the sequence by exactly one; no gaps, no dups —
`kernel_model`, `subscribe_model` in `aterm-spec`). astream's wire proves a
monotonic per-partition position: **`Offset`** with `checked_next` (no silent
wrap) and `delta_from` (exact gap, `None` if a reader is ahead of head).

These are **the same invariant at two scales.** A subscriber's cursor in aterm is
a consumer's `Offset` in astream. aterm's per-session event log *is* an astream
partition. Lifting a local aterm session onto the astream bus is therefore not an
adaptation — it is the same algebraic object (a single-writer deterministic
transducer over a gap-free offset spine) observed process-locally vs.
distributed. aterm verifies it small; astream carries it wide.

## 1. The session as a deterministic transducer over two causal logs

A session `S` is a pair of logs `(I, O)`:

- `I` — input log (keystrokes / uniform verbs), positions `i`.
- `O` — output log (VT bytes → normalized screen-ops), positions `o`.
- Each output record carries a causal watermark `w(o)` = the highest `I`-offset
  consumed before it was produced. `w` is the cross-log causal edge.

Two functions act on these logs:

- **`R` — render.** `R(O[0..o]) = ScreenState` (cells + scrollback + cursor +
  modes; and, via aterm's injected rasterizer, *pixels*). **`R` is pure** — no
  clock, rng, net, or disk. aterm **is** `R`, and model-checks that `R` is a
  deterministic single-writer fold. *Status: the engine is BUILT; the purity is
  DESIGNED-FOR-VERIFICATION at Tier-0/1 via `ty`.*
- **`P` — the program.** `O = P(I, E)` where `E` is the effect vector (clock,
  rng, filesystem, network, and — for an agent — LLM responses + tool results).
  **`P` is not pure.** `P` is the shell / Claude Code behind the PTY.

### The two-domain determinism theorem (informal)

> A session is replayable iff both `R` and `P` are replayable. `R` is *always*
> replayable (pure, verified). `P` is replayable iff its effect vector `E` was
> recorded. Therefore **session replayability reduces to a single question: how
> much of `E` did we record?**

This is the correction to the naive "you can't replay the program." Replay is not
binary; it is a function of the cut between recorded and live.

## 2. NOVEL: the determinism dial (the seam is a knob, parallel to durability)

astream already has a **durability dial** (`Strict`/`Replicated`/`Relaxed`) — a
labeled knob where each setting states its guarantee. The claim here is that
determinism has the *same shape*: a labeled knob set by **how far down the effect
seam `Σ` you record.**

| Determinism setting | Recorded | What replays | Cost / who pays |
|---|---|---|---|
| **`Render`** | `O` | the exact screen (text **and pixels**), scrollback, counterfactual re-geometry | ≈ free — you already ship `O` |
| **`Session`** | `O` + `I` | the screen *plus why it looked that way given inputs*; freeze any moment as a regression test | tiny |
| **`Effects`** | `O` + `I` + clock/rng/fs/net reads | a *sandboxed* program's full execution (the `rr` / TigerBeetle deterministic-sim model) | moderate; needs a **seam-completeness proof** |
| **`Cognition`** | `O` + `I` + effects + **LLM calls + tool results** | a full **agent** session — its reasoning, its actions, *and* its rendering | the astream thesis realized; needs agent cooperation at the seam |

The theorem behind the dial: **replay fidelity is monotone in the fraction of `E`
that crosses a recorded seam.** Pushing `Σ` down never decreases fidelity; it
trades recording overhead and a heavier honesty burden (you must *prove the seam
is complete* — no effect reaches the pure core un-recorded) for more replay.

This is where the two repos fuse: aterm already has the **seam machinery**
(dependency-injected effects, the provenance lattice, capability-gated effect
tiers, sandbox/containment); astream already has the **thesis** ("record the
recorded LLM calls"). The determinism dial is the missing concept that unifies
them — and crucially it is *honest by construction*: you may claim only the rung
whose seam-completeness has a green artifact. aterm's `ty`/Trust toolchain is
precisely the tool for that proof (the "no `Clock`/`Rng` reachable from the
reducer" property is a refinement check).

- **`Render`/`Session` — BUILT in-tree (`term.replay.byte-identical`,
  `term.resume.gapless-exactly-once`, …); the aterm pixel oracle of §6 is REALIZED
  out-of-tree** (the aterm repo's `astream-oracle`, off astream's manifest by
  doctrine — `DESIGN-astream-term.md` §13): record `(I, O)`; replay `O` through
  aterm headless from `Offset::ZERO`; `read_text` **and** `read_image` are
  bit-identical to the live session at every offset.
- **`Effects` — BUILT** in the cooperative form (`effects.cooperative.record-replay`:
  a program written against `EffectSeam`) and the Linux `ptrace` form
  (`effects.foreign-process.record-replay`: a forked, astream-authored effect
  program traced without cooperating on effect values). Still SEED: the original
  shape here — a sandboxed `sh -c` (an unmodified, exec'd binary) under a
  seccomp pre-filter.
- **`Cognition` — BUILT, hermetic half** (`term.cognition.replay-and-fork`,
  `term.session.unified-replay-and-fork`): a recorded agent turn's LLM/tool effects
  replay to a bit-identical decision trace + screen from seed+offset and fork on
  one swapped tool result. The live record pass (`astream-live` `capture`) runs but
  is non-hermetic, so it stays an `#[ignore]` test, never a green claim.

## 3. NOVEL: verified speculative execution (branch prediction for terminals)

mosh predicts only *local echo*, because it has no model of `P` and its
reconciliation is a corruption-prone heuristic — so it **fails closed inside
full-screen TUIs** (exactly where Claude Code lives). We can do strictly more,
*because* the substrate is deterministic and introspectable.

We hold something mosh structurally cannot: **a recorded corpus of
`(ScreenState, input) → output-ops` for this exact program**, since every session
is a logged `(I, O)` pair and aterm exposes `ScreenState` at every offset. So
build a client-side approximation **`P̂`** and run the CPU speculative-execution
loop:

- **Predict.** Client runs `P̂(confirmed_screen, input)` → predicted ops →
  renders immediately (zero-RTT). Unlike mosh this can predict *program
  responses* (prompt redraw after Enter, tab-completion menus, `hjkl` cursor
  moves), not just echo.
- **Execute.** Server runs the real `P`, appends authoritative `O`.
- **Retire.** When `O[o]` arrives with `w(o) ≥` the input's offset, compare
  predicted vs. actual: match → retire (free); mismatch → squash the speculative
  overlay, rebuild from confirmed.

Two properties make aggression *safe*:

1. **Safety/confluence theorem.** Committed `ScreenState = R(authoritative O
   prefix)` **regardless of `P̂`.** Prediction is a pure latency optimization with
   zero semantic effect: predicted rendering is observationally equivalent to
   authoritative rendering in steady state. `P̂` may be arbitrarily — even
   adversarially — wrong and can never corrupt the session.
2. Because misprediction is **free to detect** (deterministic replay catches it
   exactly) and **free to undo** (squash), you can predict *aggressively, into
   TUIs*, where mosh must abstain.

`P̂` is improvable and measurable: a deterministic memo-cache keyed on
`(screen-region-hash, input) → ops` seen before, or a learned model trained on
the session logs. The hit rate is a metric, hence a gate.

- *Status: the retire/squash reconciliation is BUILT for local echo
  (`term.echo.watermark-retire`, `term.echo.caused-by-retire`); `P̂`, the predictor of
  program responses, is DESIGNED and does not exist.*
- **SEED:** TLA+-verify the protocol — model `{confirmed cursor over O,
  speculative overlay}` as a `ty_model!`; invariants `committed == R(auth_prefix)`
  and `predicted ⊑ authoritative` (a refinement). Same class as aterm's
  `snapshot_model` / `transact_model`. A **formally verified speculative terminal
  protocol** is, as far as we know, new.
- **SEED:** `METRIC predict_hit_rate <v>` on a recorded corpus, with a floor —
  an astream `bench`-kind claim. Honest because it's measured, not asserted.

## 4. NOVEL: content-addressed session history ("git for cognition")

`ScreenState = R(O prefix)`, and aterm has hashing / RLE / LZ4. Content-address
every `O`-segment and materialized `ScreenState`: offsets + hashes form a
**Merkle DAG**. Consequences:

- **Sessions are versioned objects.** Scrollback is history; a session is a commit
  chain.
- **Counterfactual = branch.** Fork at offset `N`, inject a different input — or,
  at the `Cognition` rung, a different recorded LLM/tool result — replay forward:
  a new branch sharing a prefix. "What would the agent have done if the tool
  returned X" becomes `branch + replay`.
- **Diff two sessions = tree-diff** over the DAG; identical prompt-redraws
  hash-collide and dedup for free.
- **Honest bound:** *merge* is meaningful only on the **input** logs and only
  when deterministic (replay a concatenated `I`-log). "Merge two divergent screen
  histories" is otherwise ill-defined — state it, don't sell it.

- *Status: the prefix-stable branch is BUILT* — `term.fork.prefix-stable`
  (fork-at-`N` + replay reproduces a **byte-identical** shared prefix and diverges
  only after `N`), plus `term.fork.counterfactual-replay`. The content-addressing
  is what stays DESIGNED: the log is not hash-linked and carries no digest of its
  history, so the Merkle DAG (offsets + hashes as a commit chain; tree-diff;
  input-log merge) is a seed, not a built property.

## 5. NOVEL: the fleet as one materialized view (consistent-cut replay)

aterm has hierarchical-sessions and cross-session-input plans; astream has
multi-subscriber partitions. Compose: an agent fleet is a **forest of sessions,
each a partition, all on one log.** An orchestrator subscribes to N child
`out`-logs (multi-subscriber, free) and injects into any child's `in`-log
(cross-session input).

- **The fleet's collective screen is a single `state`-verb projection over a
  partitioned log** — aterm's "one introspectable buffer" thesis lifted from one
  terminal to the whole fleet.
- **Fleet-level counterfactual = consistent-cut replay.** A global checkpoint is a
  *vector of per-partition offsets* that respects the cross-log watermarks `w` —
  a causally consistent cut (Chandy–Lamport over astream offsets). Fork the whole
  forest at that cut and replay: the entire fleet's interaction re-runs
  deterministically in the render domain, and — at the `Cognition` rung — in the
  cognition domain too.

- *Status: BUILT* — `term.fleet.consistent-cut-replay` (two sessions with a
  cross-injection edge; a consistent cut as an offset-vector; both replay to their
  live screens, an effect-without-cause cut rejected), `term.fleet.durable-watermark`
  (the causal edge persisted on-log, `ENV_VERSION = 3`), `term.fleet.orchestrate-n`,
  `term.fleet.control-handoff`. The fleet-wide `state`-verb materialized view and a
  cognition-domain fleet replay stay DESIGNED.

## 6. NOVEL: self-proving transport (the introspection API is the oracle)

aterm proves itself with its **own** introspection API (golden text, pixel
regression, scripted flows — `aterm-conformance`, `tools/golden/vectors`).
astream requires every claim to carry a re-runnable command. Fuse them: **the
replay substrate is checked by the terminal's own eyes.**

Master seed (near-term, connects two *existing* test surfaces):

> Record a session as `(I, O)`. Replay `O` through aterm headless from
> `Offset::ZERO`. Assert the replayed buffer's `read_text` **and** `read_image`
> (pixels) are bit-identical to the live session at every offset.

This is strictly stronger than a grid-hash seed: aterm verifies replay at the
**pixel**, not just the cell, and the checker is the same API the intelligence
uses (self-proving, aterm pillar #8). It is the gate every other claim here
waits on, and it is runnable soon because both halves already exist (aterm's
conformance harness + astream's manifest).

Proposed manifest rows (existing kinds only) — of these only `term.fork.prefix-stable`
(`test`) exists and is green; `term.replay.pixel-exact` (`test`),
`term.replay.golden-pinned` (`selftest` + sha) and `term.predict.hit-floor` (`bench`)
are seed names, not claims (the pixel oracle runs out-of-tree, off the manifest).

## 7. The honest frontier

With aterm in the picture the position is no longer "a niche idea on an unborn
transport." It is:

- **Real today:** a verified-ish, introspectable, xterm-class terminal kernel
  (aterm) and a panic-free deterministic wire vocabulary (astream-wire). The
  render-domain floor (`R` pure; pixel-exact replay) is near-term checkable.
- **The new theory:** determinism is a *dial*, parallel to durability; on a
  deterministic+introspectable substrate, prediction becomes *verified
  speculative execution* (predict program responses, retire against the log,
  squash exactly) rather than mosh's fail-closed heuristic; session history
  becomes a *content-addressed Merkle DAG* with replay-defined branches; and an
  agent fleet becomes *one forkable materialized view* with consistent-cut replay.
- **The boldest still-falsifiable claim:** *replay an agent's mind and its screen
  together* — record `(I, O, E_cognition)` for one Claude Code session and
  re-derive both its actions and its exact pixels from seed+offset. That is the
  `Cognition` rung, and it is the union of astream's thesis and aterm's verified
  `R`.

What is **not** claimed: §3's verified speculation (`P̂`, squash of predicted
*program responses* — the retire/squash machinery exists for echo,
`term.echo.watermark-retire` / `term.echo.caused-by-retire`, the predictor of
program responses does not); §6's pixel-exact replay as an *in-tree* claim (it is
proven out-of-tree by the aterm oracle; in-tree the content hash is the proxy); the
full Merkle DAG/merge of §4; that an *uninstrumented* program replays (only its
render does, until its seam is recorded and proven complete); that prediction
beats the speed of light (it hides RTT exactly as mosh does — the win is
correctness and reach, not physics); that aterm is "fully proven" (Tier-0/1 `ty`
model-checking is real; MIR-refinement is designed-for-verification per aterm's
own ratchet).
