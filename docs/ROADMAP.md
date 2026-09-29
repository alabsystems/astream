# Roadmap: what is open

This file lists **open work only**. What is BUILT, and the re-runnable claim that
proves it, lives in [`evidence/manifest.toml`](../evidence/manifest.toml) and the
README's Evidence table generated from it; this file does not restate it and claims
nothing. The direction is [`GOAL.md`](GOAL.md). An item leaves this list only as a
green manifest claim under `make ci` ([`DOCTRINE.md`](DOCTRINE.md)); where a design
doc gives a precise seed command it is quoted here.

## Transport and identity (what still separates the sealed bus from "SSH")

- **Identity bound to an external authority** (an SSH agent, OIDC) rather than a
  locally pinned host key and allow-list, and the key operations around it:
  distribution and rotation. See [`DESIGN-astream-term.md`](DESIGN-astream-term.md) §11.
- **Capability revocation and attenuation.** Expiry exists; withdrawing one capability
  before its deadline still means rotating the mint secret. Open: revocation lists,
  attenuable (macaroon) caps, and caps bound to an identity key rather than a bearer tag.
- **QUIC transport / connection migration** — true zero-gap roaming (today a roam is a
  reconnect that resumes from its offsets).

## The durable log at rest

- **Bind at-rest records to their log.** The at-rest AAD is the record index alone, so
  two logs sealed under one key can have same-index records swapped undetected; a
  per-log identity in the AAD is an on-disk format change (today: one key per log).
- **Retention that carries state across compaction.** Producer bindings (`/a/bind`) and
  pending wills (`/a/will`) live in the log itself, so `retain_before` refuses to drop
  them; on a guarded broker the first binding sits near the start of the log, which
  keeps retention from making progress until a sidecar or format change carries them.
- **Torn-tail classification after power loss.** A partial frame followed by zeroed,
  never-written extents reads as corruption, so open refuses and needs `asb repair`
  even though only an unacked batch was torn.

## Replication and scale

- **Replicated tier follow-ons:** leader election / automatic failover; follower
  catch-up after a rejoin (a diverged follower is fenced today, never truncated); a
  backoff for re-dialing a down follower (today every batch re-dials it, so a
  blackholed one costs up to `REPLICA_IO_TIMEOUT` per batch);
  capability attachment on follower links; a multi-node failure-injection matrix.
- **Federation across brokers** (per-host brokers, cross-broker cuts).
- **Kafka Produce/Fetch data path** (record-batch v2 + CRC32C), flexible versions, and
  wiring the codec into an accept path — no Kafka client can connect today.
- **io_uring** egress/ingest — seed `broker.bench.iouring-floor` (`cfg(linux)`), gated on
  a decision: a new cordoned unsafe module or a vetted-dependency exception
  (`DESIGN-astream-term.md` §13).
- **Cross-system benchmark** vs Kafka/NATS at equal durability on disclosed hardware.
- **Durable execution**, distributed form and a step-DAG (today: in-process, linear).
- **WASM** and **file-sync** — named as not built; no design yet.

## Determinism-dial rungs

- **Effects, foreign-process sub-seeds.** The Linux `ptrace` rung records and replays a
  forked, astream-authored effect program. Three pieces remain, all against the same
  `EffectRecord`/`EffectsLog` tape and oracle discipline:
  1. a **seccomp-bpf pre-filter** that `SECCOMP_RET_TRACE`s only the intercepted set
     (`clock_gettime`, `getrandom`, `openat`, `read`, `close`), so the tracer costs
     O(intercepted) rather than O(all) syscalls;
  2. **full syscall neutralization** on replay: rewrite the syscall to a no-op at the
     seccomp stop, then inject the taped return value and buffer, so no real syscall
     reaches the kernel (today replay overwrites the result of a call that still ran);
  3. tracing a separately **exec'd, unmodified** binary (fork, `PTRACE_TRACEME`,
     `execve`), single-threaded first.

  Seed: `cargo test --locked -p astream-host --test seccomp_record_replay`
  (`cfg(target_os = "linux")`; the target does not exist yet) — an unmodified child
  whose output is a pure function of one `clock_gettime`, one `getrandom` and one `read`
  of a fixed file is recorded, then replayed with no real syscall reaching the kernel,
  to a byte-identical digest equal to an independent oracle over the taped values; a
  short, wrong-kind or diverged tape aborts the replay.
- **Cognition, live record pass.** `cargo run -p astream-live --bin capture` records a
  real model completion (the tool result and effect clock are placeholders). It is
  key-gated and non-hermetic, so it stays an `#[ignore]` test, never a green claim.
- **Render fidelity:** graphemes and truecolour in the in-tree fold; DECSC/DECRC
  saving the SGR pen as xterm and aterm do (a `Screen::serialize` and frame-hash change); pixel-exact image
  rendering via the external aterm oracle, which stays out of the manifest by design.
- **Verified speculation:** the `P̂` program-response predictor — seed
  `term.predict.watermark-squash` over a recorded corpus with a `METRIC predict_hit_rate`
  floor (`DESIGN-astream-term.md` §8, [`THEORY`](THEORY-deterministic-sessions.md) §3).
- **Session history and fleet views:** a content-addressed (Merkle-DAG) history (THEORY
  §4); the normalized screen-op cross-machine projection (`DESIGN-astream-term.md` §4); a
  fleet-wide `state`-verb materialized view and a cognition-domain fleet replay; a live
  PTY host stamping `caused_by` itself.
- Any future envelope change (`ENV_VERSION`) re-pins both selftest SHAs in one increment.

## Driving aterm over the bus, and the fabric

- **An in-tree end-to-end "aterm driven over the bus" claim.** Every constituent is
  green, but nothing re-runnable composes them. On the way: the lash's resume and
  exactly-once drive (`DESIGN-drive-pipe.md` §9, Rung 1), the agent-hook wake (§5), and
  a second program profile (Rung 3).
- **Fabric follow-ups:** the astream-side requirements R1–R8 in
  [`REQUIREMENTS-fabric-operations-2026-09-14.md`](REQUIREMENTS-fabric-operations-2026-09-14.md)
  (a guarded broker from the CLI, multiple listeners, broker-stamped time, a retention
  policy and oldest-offset query, `Stats`, identity-bound principals with revocation, a
  client-visible exactly-once key, the ack/`expired` record shapes), and the **DESIGNED**
  rows of [`DESIGN-aterm-fabric.md`](DESIGN-aterm-fabric.md) §15.
