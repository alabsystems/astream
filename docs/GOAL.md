# Goal

## North star (one sentence)

Build the substrate on which an entire agent fleet — every terminal it drives,
every effect it touches, and ultimately its cognition — is a **pure, replayable,
forkable function of one durable log**, and climb the *determinism dial* from
**Render** to **Cognition** one falsifiable rung at a time, so that ambition
never outruns evidence.

## What "fully" means — the whole stack is one object

A single algebraic object — a single-writer deterministic transducer over a
gap-free offset spine — observed at every scale:

- **`astream-wire`** — the panic-free vocabulary: a CRC `Frame`, the
  `Subject`/`Filter` address grammar, the canonical partitioner, and `Offset`
  with checked arithmetic. Zero dependencies; the auditable bottom.
- **`astream-engine`** — the per-partition deterministic single-writer `Log` over
  an effect seam (`Clock`/`Rng`/`Disk`/`Net`): record → byte-identical replay →
  Strict fsync durability + crash recovery → snapshot+tail resume with
  exactly-once input → counterfactual fork → a byte-identical shared
  prefix (content-addressing itself is a seed: the log is not hash-linked) → fleet consistent-cut replay.
- **`astream-term`** — a terminal session as two ordered streams (`In`, `Out`)
  plus a pure screen fold; speculative echo that can never corrupt the screen;
  normalized typed screen-ops so two viewers can never disagree.
- **`astream-host`** — a *real* pseudo-terminal recorded and replayed: the
  substrate driving an actual OS process, with all unsafe cordoned to two
  cfg-gated OS modules (`sys`, and the Linux `foreign` ptrace tracer).
- **`astream-evidence`** — the honesty spine: every claim is a re-runnable
  command, the README is generated from the manifest, and the merge gate makes
  drift un-mergeable.

These are not separate products; they are the same object at the wire, the log,
the screen, the process, and the fleet.

## The spine — the determinism dial

Replay fidelity is a labeled knob, orthogonal to the durability dial
(`Strict`/`Replicated`/`Relaxed`), set by **how far down the effect seam you
record**:

| Rung | Records | What replays |
|---|---|---|
| **Render** | `Out` | the exact screen, scrollback, counterfactual re-geometry |
| **Session** | `Out` + `In` | the screen *and why it looked that way*; freeze any moment as a test |
| **Effects** | + clock/rng/fs/net | a sandboxed program's full execution |
| **Cognition** | + LLM calls + tool results | a full **agent** session — its reasoning, its actions, and its rendering |

The climb is the goal. Its summit is the **Cognition** rung: *replay an agent's
mind and its screen together* from seed + offset.

## The law (non-negotiable)

A rung may be **claimed** only when its seam-completeness has a green,
re-runnable artifact. Nothing is faked; the **absence** of a claim is itself
machine-checked evidence. Ambition is bounded only by the size of the seed we can
honestly attach.

## Where we are — and the master seed

**Built and green (all four dial levels; every claim, and the count, is in
`evidence/manifest.toml`, and hosted CI runs `make ci` on Linux on every push, so
the Linux-gated claim runs there too):** record a real
shell, replay it byte-identically, survive `kill -9`, resume exactly across a
drop, predict-and-reconcile by watermark, fork counterfactually, branch with a
byte-identical shared prefix, replay a fleet from a consistent cut, drive a real PTY,
project lossless screen-ops, fold the DECSTBM scroll region (cross-validated vs
real aterm), perceive in four modalities, orchestrate ≥3 children with a control
handoff — **and now climb to the top of the dial**: the **Effects** rung
(`effects.cooperative.record-replay` — a program's real clock/rng/file effects
replayed byte-identically from a tape) and the **Cognition** rung
(`term.cognition.replay-and-fork` — an agent turn's decisions + screen replayed
hermetically, and counterfactually forked on a tool result). **Durable execution**
is now built on the Strict log too (`engine.durable.exactly-once-resume` — a
workflow survives a crash and resumes exactly, each step run once), and the
regression-floor `bench` gate now covers the engine append/replay and the screen
fold, not just the wire layer. The Effects rung's foreign-process form — recording
and replaying, via Linux `ptrace`, the syscall effects of a **forked,
astream-authored effect program** that self-attaches with `PTRACE_TRACEME` and does
not cooperate on effect *values* — is now built too
(`effects.foreign-process.record-replay`, a Linux-gated claim that hosted CI runs on
Linux; a local macOS `make ci` skips it). Tracing an **unmodified, separately-exec'd
binary** remains a sub-seed.

**And astream is now a *servable* system, not just a library.** `astream-broker`
is a message bus you connect to over a Unix socket or TCP: exactly-once-ingest
durable pub/sub with `Filter` routing and resume-from-offset
(`broker.exactly-once-pubsub-resume`); the agent-native verbs no other bus has —
counterfactual fork-delivery and cognition routing (`broker.agent-native-*`); true
end-to-end exactly-once via durable group commits + an atomic read-process-write
transaction, no coordinator (`broker.true-exactly-once-e2e`); a throughput floor at
parity with Redis at equal durability (`broker.bench.publish-floor` +
`evidence/bench/broker-vs-redis.md`); **GROUP COMMIT** — a single writer thread folds
concurrent appends into one fsync, so durable throughput scales with concurrency
(~58× the single-producer rate at 128 producers on the dev box) while keeping the
identical Strict `ack ⟹ fsync'd` guarantee, proven correct under concurrency and
gated by a throughput floor (`broker.group-commit-durability` +
`broker.bench.groupcommit-floor`); **single-connection pipelining** so one agent's
connection keeps many publishes in flight (~180× the one-in-flight rate at window 512,
same Strict guarantee; `broker.pipelining` + `broker.bench.pipeline-floor`);
**share-nothing partition sharding** — N independent brokers, canonical routing,
per-partition order, fan-in subscribe, recovery (`broker.sharded-routing`), a
horizontal-scale architecture (honestly NOT a single-disk Strict throughput win —
that's group commit + pipelining); the **durability dial** — `Relaxed` (page-cache
ack, ~233× the Strict single-producer rate at the stated weaker guarantee: survives a
process crash, not power loss) and `Replicated` (leader ships each batch to a follower
quorum over TCP; an ack survives leader-node loss — `broker.replicated-tier`) alongside
the `Strict` default (`broker.relaxed-tier` + `broker.bench.relaxed-floor`); **zero-copy
egress** (Arc-shared read path,
`broker.bench.replay-egress-floor`); multi-machine TCP (`broker.tcp-transport`)
with an unforgeable HMAC capability mint (`cap.unforgeable-mint`,
`wire.filter.containment`) that the broker **enforces on its accept path** when built
with the opt-in `cap` feature (`broker.cap-enforced-on-attach`); an **AEAD wire** —
XChaCha20-Poly1305 sealing of the same TCP protocol under a pre-shared key, opt-in
`aead` feature (`aead.seal-open.authenticated`, `broker.sealed-tcp-roundtrip`), with
**forward secrecy** from an ephemeral X25519 agreement over it (opt-in `handshake`;
`aead.handshake.forward-secret-key-agreement`, `broker.handshake-tcp-roundtrip`) and
**mutual static public-key identity** that needs no shared secret at all — the client
pins the broker's host key, the broker allow-lists the client, and the identity keys
only sign the ephemeral transcript so forward secrecy survives their compromise
(opt-in `identity`; `aead.identity.mutual-signed-dh`, `broker.identity-tcp-roundtrip`);
capabilities that **expire**, checked per request (`cap.expiry-enforced`); the durable
log **sealed at rest** (opt-in `at-rest`; `broker.log-encrypted-at-rest`) with an
authenticated **anti-rollback** watermark (opt-in `anti-rollback`;
`broker.log-anti-rollback`) and **retention** that keeps absolute offsets (opt-in
`retention`; `broker.log-retention`); the
**drive-pipe pump** that turns the block-forever bus into semantic wake boundaries for
a turn-based agent, from any subject and off a broker-durable cursor
(`term.perceive.semantic-events`, `pump.wake-on-boundaries`,
`pump.attach-subject-and-group`); two
shell faces, `asb` and `aspump` (`broker.cli.pub-sub-roundtrip`,
`broker.cli.tcp-roundtrip`, `pump.cli.wake-lines`); and a std-only Kafka wire-protocol
handshake/Metadata **codec** (`kafka.handshake-and-metadata`) — proven at the wire
level but not wired into any accept path, so no Kafka client can connect today.

**And the wire core's guards are SURVEYED by the compiler — 61 of 98 obligations
proved, every gap named.**
[Trust](https://github.com/alabsystems/trust) is a `rust-lang/rust` fork whose
SMT-backed verifier runs as a MIR pass **during compilation** and **auto-generates +
discharges** the Level-0 safety obligations (integer overflow, array/slice bounds,
div/rem-by-zero, allocation bounds, panic-freedom) with **no proof harnesses** (it
discovers them from the MIR, unlike Kani). Honest scope: `scripts/verify-trust.sh`
builds the **real `astream-wire` library** under the pinned Trust (`4b3506be5`) and
records every verdict: **61 of 98** obligations proved (the decoder's header indexing,
the CRC-32 table lookup, the encoder's length add, `h % n`), 4 refuted (allocation
bounds), 7 unmodelled and 26 `std` calls left runtime-checked — so the crate does
**not** build under `-Z trust-policy=strict` or `certify`: proof-aware, not
proof-complete, with every gap named. Attached artifact `evidence/verify/trust-wire.md` (not a make-ci
claim — Trust is a separate toolchain). The
stateful durable log is additionally verified against an independent reference model
over random operation sequences incl. crash recovery (`broker.model-based-equivalence`).
With `forbid(unsafe)` making memory- and data-race-safety compiler-proved, the
*substrate's invariants* are verified — not the whole distributed system, and
emphatically not agent behaviour (the doctrine keeps "provably correct agents" out).
See [`DOCTRINE.md`](DOCTRINE.md) §7.

**The frontier that remains (seeded, not claimed):** the **live-API record pass**
for Cognition (one real Messages turn under a recording seam — non-hermetic by
nature, never a green claim); the Effects sub-seeds (a **seccomp-bpf pre-filter**,
full syscall neutralization, tracing a separately-exec'd unmodified binary);
graphemes and truecolour in the fold (DECSTBM and `bce` are folded); and, on the
transport + auth track, what still separates the built sealed/guarded bus from the
word "SSH" — now that the key agreement, static public-key identity, capability
expiry and encrypt-at-rest are BUILT: identity bound to an **external** authority
(an SSH agent, OIDC) rather than a locally pinned and allow-listed key, the
operational surface around keys and capabilities (distribution, rotation,
revocation), and QUIC connection migration. The open list is
[`ROADMAP.md`](ROADMAP.md); the seeds are in
[`DESIGN-astream-term.md`](DESIGN-astream-term.md) §13 and
[`DESIGN-drive-pipe.md`](DESIGN-drive-pipe.md) §8.

**The master seed — the one command whose green means the goal is reached:**

> Record one Claude Code session as `(Inputs, Outputs, Effects, Cognition)` — its
> keystrokes/tool calls, the world's responses, its effect vector, and its LLM
> completions. Replay it from `seed + offset` with no network and no live tools,
> and assert its **decision sequence** and its **exact pixels** are bit-identical
> to the live session at every offset — then `fork` it at any offset, swap one
> recorded tool result or completion, and replay a forward-divergent alternate
> history.

When that command is green, an agent's cognition and its screen are one
replayable, forkable, auditable object — the determinism thesis realized
end-to-end. Until then, we ship the rung below it, with the seed in hand.

**Progress toward the master seed — its hermetic form is now CLOSED.** The
capstone (`term.session.unified-replay-and-fork`) carries all four streams —
**Inputs, Outputs, Effects, Cognition** — on **one offset axis**, replays them
bit-identically, and forks on a single recorded tool result so **all four diverge
coherently** (a swapped result finishes the turn early, so the decision trace
shortens, the screen omits the unreached recovery and its content hash moves,
fewer inputs apply, the effect digest differs). The four streams are one
replayable, forkable, auditable object — exactly what the master seed asks for,
minus the one non-hermetic step.

**The live-capture bridge is now BUILT, in-tree.** `crates/astream-live`
(a workspace member with ZERO third-party deps — a real hand-rolled JSON parser
and a `std::process` shell-out, since an HTTP/serde tree is forbidden in the
substrate; claim `cognition.live-bridge.parse-and-replay`) turns a **real
Anthropic Messages response** into a unified four-stream session and replays it
through the in-tree substrate. Its green test verifies the real-response-format
**parse** + **deterministic replay + coherent fork**. The `capture` binary exercises that pipeline
over a **real model call** on either path: `capture_live` (a key-gated `curl` to the
Messages API) when `ANTHROPIC_API_KEY` is set, or `capture_via_cli` (the
authenticated `claude` CLI — **no key needed**) otherwise. Be precise about what is
captured: the model's **completion** is real and non-deterministic, and it replays
deterministically — but the binary does **not run the tool** the completion asks for,
and the tool result and the effect clock it assembles around that completion are
fixed placeholders (`crates/astream-live/src/bin/capture.rs`, the `PLACEHOLDER_*`
consts). `cargo run -p astream-live --bin capture` demonstrates the real-completion
path in this environment.

So every piece of the master seed exists and runs, with that one honest gap: the
capture bridge (over a real model completion, with a placeholder tool result), the
unified four-stream log, the deterministic replay, and the fork. The one irreducibly non-hermetic runtime step — a real, non-deterministic
model call — cannot be a *green* claim (its output differs every run, so it is
gated `#[ignore]`), but it is **no longer un-exercised**: the `claude` CLI path
runs it here without a key. Pixel-*exact* rendering remains the out-of-tree aterm
oracle (proven); the in-tree content hash is its deterministic proxy. The summit
is reached.

See [`DOCTRINE.md`](DOCTRINE.md) for the thesis and the performance model,
[`DESIGN-astream-term.md`](DESIGN-astream-term.md) for the status ledger and the
open seeds, and [`THEORY-deterministic-sessions.md`](THEORY-deterministic-sessions.md)
for the cross-repo theory the dial comes from.
