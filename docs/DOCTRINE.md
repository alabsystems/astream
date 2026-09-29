# astream Doctrine

Thesis, architecture, and the performance + honesty model. This extends the
Phase-0 README with the direction set after the kafka2 audit. It is a design
record: it marks clearly what is **built** versus **designed**, because the one
rule astream never breaks is that ambition and evidence may not drift apart.

## 1. Thesis (v2): the deterministic replay substrate for agent fleets

astream is a small, reproducibly-buildable message bus whose reason to exist is
*honest semantics for the agent work loop*. Its headline bet is **determinism**:

> An agent is nondeterministic only because of its inputs — LLM outputs, tool
> results, the clock, randomness. Record those inputs as ordered events in one
> durable log and the agent becomes a pure function of the log.

When that holds, the log stops being mere transport and becomes the canonical,
replayable history of the fleet's cognition and action. Four verbs
(`/a/{stream|queue|inbox|state}`) are projections over that single log, and the
following capabilities — which no existing bus offers together — fall out:

- **Total replay**, including the recorded LLM calls, from a seed + offset.
- **Counterfactual debugging**: fork history at offset N, swap one tool result,
  replay forward.
- **Durable execution**: a workflow survives a crash and resumes exactly (no
  lost steps; no double side-effects beyond the stated idempotency caveat).
- **Audit and regression for free**: replay *why* an agent acted; freeze any
  incident as a deterministic test.

This collapses message bus + work queue + retained state + durable-execution
engine + audit trail + test harness into one substrate, and adds replay of
*cognition*, which none of them have.

### The ambition ceiling

Ambition is bounded by falsifiability: the most ambitious astream is the
largest capability we can attach a re-runnable seed to. The following are
deliberately **out** until each has a falsifiable milestone, because each is the
exact trap kafka2 fell into — whole-system machine-checked refinement, a BFT
"global consensus layer", a bare "beyond-SOTA throughput" claim, and any notion
of "provably correct agents" (we can prove the *substrate's* invariants, never
the model's behavior). Each may re-enter the roadmap the moment it has a seed.

Two of these have now re-entered *with their seed attached*, at exactly their
honest scope: "beyond-SOTA throughput" is no longer bare — group commit and
single-connection pipelining are **measured, floor-gated** wins at equal
durability (§6); and *formal verification of the substrate* has re-entered with its seed
attached — a re-runnable Trust survey of the **real** wire crate
(`evidence/verify/trust-wire.md`) that records, per obligation, what the pinned
compiler proves (61 of 98) and what it does not; the crate does not yet build
under Trust's strict policy, and the stateful log is model-checked against a
reference spec (§7). What stays out is
unchanged: whole-system refinement and "provably correct agents." Proving the
substrate's invariants is the seed we said we'd need; proving the model's
behaviour is not on the table.

## 2. The Pareto rule: never worse on a measured axis

astream must be **at least as good as the usual suspects (Kafka / NATS / Redis)
on every dimension people benchmark, and decisively better on the dimensions
agents need.** This is a Pareto rule, not a single posture, and it is enforced
by a gate (§5), not hoped for.

### The honest exception

There is one axis where a new system *is* worse and pretending otherwise would
be a lie: **ecosystem maturity** — clients, connectors, ops tooling,
battle-hardening. We do not out-engineer ten years of adoption. The mitigation
is a **Kafka wire-protocol compatibility mode** (§4.3): speak Kafka's protocol
and inherit its client/tooling ecosystem unchanged, while running the better
engine underneath. So even this axis has a real answer — it just is not "we are
more mature."

## 3. Performance is a durability dial, not a fixed posture

Throughput is not capped by astream; it is set by the durability guarantee you
choose. Kafka's default is fast because it acks *before* fsync ("durable" =
"in the page cache of N replicas"). astream exposes this as an explicit, labeled
knob where every setting is benchmarkable and its guarantee is stated:

| Mode | "ack" means | Comparable default | Survives |
|---|---|---|---|
| `Strict` (astream default) | fsync'd to disk | stricter than anyone's default | single-node power loss |
| `Replicated` | in memory on N nodes | Kafka default — parity target | node loss (not full power loss) |
| `Relaxed` | local memory only | NATS core / Redis — parity target | nothing; lowest latency |

At **equal** durability, astream targets parity-or-better; and it *additionally*
offers `Strict`, which the usual-suspects' defaults do not. The dishonest move
is hiding a durability difference inside a benchmark; astream surfaces it.

## 4. Architecture: determinism and speed are not in tension

### 4.1 Per-partition deterministic engine

Each partition has one deterministic single-writer engine over an effect seam
(`Clock` / `Rng` / `Net` / `Disk`). This is what makes replay, simulation, and
verification possible. The seam is pulled **forward into the core design** so
determinism is load-bearing from the start, not retrofitted (retrofitting it is
the failure mode to avoid).

### 4.2 Thread-per-core, share-nothing across partitions

Partitions are sharded across cores with no shared locks, so throughput scales
linearly with cores. This is how Redpanda (thread-per-core) and TigerBeetle
(deterministic + batched) are each built; astream does both at once. Mechanical
sympathy is table stakes: batched sequential append, zero-copy egress, io_uring.

> Existence proof: Redpanda (no JVM, thread-per-core, io_uring) already beats
> JVM Kafka on latency at equal-or-better durability. Rust gives astream the
> same ceiling. This is a credible, proven *target* — not a Phase-1 fact, and
> not claimed until the bench says so.

### 4.3 Kafka wire-protocol compatibility mode

A compatibility surface that speaks Kafka's protocol, so existing Kafka clients
and tooling would work unchanged against astream, with the agent-native verbs and
the replay substrate available to code that opts in. This is the adoption answer
to the ecosystem-maturity exception (§2) — and it is **Designed**, not built: what
exists today is the handshake/Metadata **codec**, proven at the wire level
(`kafka.handshake-and-metadata`) but wired into no accept path, so no Kafka client
can connect. The Produce/Fetch data path and the broker wiring are the increments
that would make this paragraph true.

## 5. The "never worse" gate (Trust makes the Pareto promise real)

The Pareto rule is enforced as a **benchmark-regression gate** in the evidence
harness, via `bench`-kind claims in `evidence/manifest.toml`:

- A bench command prints `METRIC <name> <value>` lines; a claim asserts a floor
  (or ceiling) on a named metric. A change that drops a metric below its floor
  **fails the gate**.
- Cross-system claims (vs Kafka / NATS / Redis) record the comparison run
  directory with disclosed hardware and the same workload at equal durability;
  the claim ships only with that artifact attached.

"We do not want to be worse in an important dimension" thereby becomes a
machine-checked invariant, not an aspiration.

## 6. Status: built vs designed

| Capability | Status |
|---|---|
| Reproducible build, evidence manifest, merge gate | **Built** (Phase 0) |
| `astream-wire`: frame, address grammar, partitioner, offset | **Built** (Phase 0) |
| `bench` claim-kind + regression floors (wire + engine append/replay + screen fold) | **Built** — `wire.bench.*`, `engine.bench.*`, `term.bench.fold-floor` |
| Durability dial: `Strict` (fsync) + `Relaxed` (page-cache) + `Replicated` (quorum) | **Built (all three)** — `term.strict.survives-kill`; `broker.relaxed-tier` + `broker.bench.relaxed-floor` (~233× Strict single-producer, stated weaker guarantee); `broker.replicated-tier` (leader ships each batch to a follower quorum over TCP, ack waits for quorum, survives leader-node loss). Leader election / follower catch-up-after-rejoin remain a later track |
| Group commit (batched fsync): one fsync amortized over a concurrent batch, same `ack ⟹ fsync'd` guarantee | **Built** — `broker.group-commit-durability` (correctness under concurrency + restart) + `broker.bench.groupcommit-floor` (throughput floor; ~58× single-producer at 128 producers on the dev box) |
| Single-connection pipelining: one connection keeps many publishes in flight (read half + ordered ack-writer), same Strict guarantee | **Built** — `broker.pipelining` (ordering + dedup-under-pipeline + restart) + `broker.bench.pipeline-floor` (~180× one-in-flight at window 512 on the dev box) |
| Formal verification of the substrate: a Trust SURVEY of the wire core; stateful log model-checked vs a reference spec | **Surveyed (attached artifact), not proved** — `evidence/verify/trust-wire.md`: `scripts/verify-trust.sh` builds the REAL `astream-wire` library under the Trust compiler (rust-lang/rust fork, SMT verifier as a MIR pass) at the pinned commit `4b3506be5` under the `advisory`/`strict`/`certify` policies. Auto-generated obligations, no harnesses: 69 functions, 98 obligations — 61 proved (`Frame::decode`'s header indexing, the CRC-32 table lookup, `h % n`, loop counters), 4 refuted (allocation bounds, one capacity add), 7 unmodelled, 26 calls into `std` left runtime-checked; the crate does NOT build under `-Z trust-policy=strict` (37 errors) or `certify` (58). Plus `broker.model-based-equivalence` (a make-ci claim). Whole-system/agent-behaviour correctness remains deliberately OUT (§1) |
| Per-partition deterministic engine + effect seam (`Clock`/`Rng`/`Disk`/`Net`) | **Built** — `astream-engine` |
| Deterministic replay (record → byte-identical replay → resume → counterfactual fork) | **Built** — `term.replay.byte-identical`, `term.resume.*`, `term.fork.*` |
| Effects + Cognition rungs of the determinism dial | **Built** — `effects.cooperative.record-replay`, `effects.foreign-process.record-replay` (Linux `ptrace` over a forked, astream-authored effect program that self-attaches with `PTRACE_TRACEME` and does not cooperate on effect *values*; tracing an unmodified, separately-exec'd binary remains a sub-seed; Linux-gated, and hosted CI runs it on Linux on every push), `term.cognition.replay-and-fork` |
| Durable-execution engine (a workflow survives a crash and resumes exactly) | **Built** (single-writer, in-process) — `engine.durable.exactly-once-resume`; distributed + step-DAG forms Designed |
| Share-nothing partition sharding (thread-per-core architecture) | **Built** (architecture) — `broker.sharded-routing`: N independent brokers, canonical routing, per-partition order, fan-in subscribe, recovery. HONEST: on a single disk at Strict durability throughput does NOT scale with shards (one batched log is already disk-bound) — it is a horizontal-scale / multi-disk / CPU-bound-regime mechanism, not a single-disk win |
| Zero-copy egress (Arc-shared read path) | **Built** — `broker.bench.replay-egress-floor`: `read_from` hands out shared `Arc` records (no deep copy out of the log) and delivery frames are assembled from borrowed fields; egress floor-gated. True writev (0 frame-assembly copies) is a further seed |
| io_uring (Linux) | Designed — Phase 2 (needs a cordoned `cfg(linux)` unsafe `sys` module, like `astream-host`, or a vetted-crate decision; out until that seed lands) |
| Cross-system bench vs Redis (equal durability) | **Built** (artifact) — `broker.bench.publish-floor` + `evidence/bench/broker-vs-redis.md`: at UDS + fsync-per-op astream-broker is at parity with Redis on disclosed hardware; Kafka/NATS + larger matrix Designed |
| Kafka wire-protocol compatibility (handshake + Metadata) | **Built** — `kafka.handshake-and-metadata` (ApiVersions + Metadata, spec-faithful v0); Produce/Fetch data path + flexible versions + broker wiring Designed |
| Servable broker: exactly-once pub/sub + resume over a Unix socket and TCP; agent-native fork-delivery + cognition routing; true end-to-end exactly-once | **Built** — `broker.exactly-once-pubsub-resume`, `broker.tcp-transport`, `broker.agent-native-fork-and-cognition`, `broker.true-exactly-once-e2e`; shell faces `asb` (`broker.cli.pub-sub-roundtrip`, `broker.cli.tcp-roundtrip`) |
| Capability mint (HMAC-SHA256 signed `Filter`) + enforcement on the broker accept path | **Built** — `cap.unforgeable-mint`, `wire.filter.containment`; enforcement is **opt-in** (`cap` feature, `Broker::open_guarded`) — `broker.cap-enforced-on-attach`. A default (unguarded) broker still equates reachability with access. A grant can carry an **expiry**, checked per request so a live connection loses authority at the deadline — `cap.expiry-enforced`; revoking one capability before its deadline (short of rotating the secret), revocation lists and attenuation stay Designed |
| AEAD wire (XChaCha20-Poly1305 `SealedStream`, pre-shared key) on the TCP transport | **Built (opt-in `aead` feature)** — `aead.seal-open.authenticated`, `broker.sealed-tcp-roundtrip`. A per-connection hello handshake; every record's AAD binds both hellos, the direction and the sequence, so a record replayed across connections or reflected back its own way fails its tag. Per-connection sequence as AAD. The two limits this row used to list are now the two rows below it: an online key agreement (forward secrecy) is **Built** under the `handshake` feature, and static public-key identity under `identity`. What stays Designed is identity bound to an EXTERNAL authority (SSH agent, OIDC) and any key distribution, rotation or revocation surface |
| Forward secrecy over the sealed wire (ephemeral X25519 agreement authenticated by the PSK) | **Built (opt-in `handshake` feature)** — `aead.handshake.forward-secret-key-agreement`, `broker.handshake-tcp-roundtrip`. Each session derives a fresh key (NNpsk: HKDF-SHA256 over the DH, salted by the PSK), so a later PSK compromise cannot decrypt a recorded session. astream owns the framing, transcript and HMAC/HKDF (RFC 4231/5869 vectors); only the raw X25519 scalar multiplication is delegated to the vetted `x25519-dalek` |
| Static public-key identity, NO shared secret (mutual signed-DH, SIGMA/Ed25519) | **Built (opt-in `identity` feature)** — `aead.identity.mutual-signed-dh`, `broker.identity-tcp-roundtrip`. The client PINS the broker's host key and the broker ALLOW-LISTS the client's identity; the identity keys only sign the ephemeral transcript, so forward secrecy survives an identity-key compromise. The record layer binds that same transcript into every record's AAD. Only Ed25519 sign/verify is delegated (`ed25519-dalek`). Honest boundary: identity is a LOCALLY pinned/allow-listed key, not one bound to an external authority (SSH agent, OIDC), and there is no key distribution, rotation or revocation surface |
| The durable log at rest: per-record encryption, an anti-rollback head watermark, retention | **Built (opt-in `at-rest` / `anti-rollback` / `retention`)** — `broker.log-encrypted-at-rest` (`Broker::open_encrypted`: XChaCha20-Poly1305 per record, the log index as AAD; hides content, not record count, sizes or timing), `broker.log-anti-rollback` (`Broker::open_encrypted_verified`: an authenticated head watermark in a `<log>.hw` sidecar refuses a log truncated below it; a key-less attacker is defeated, restoring an older snapshot of the log and its sidecar needs a hardware counter), `broker.log-retention` (`Broker::retain_before`: compaction below an offset floor keeping surviving offsets absolute; exactly-once holds within the retention window) |
| The drive-pipe pump: broker SUBSCRIBE -> fold -> semantic events -> agent wake | **Built** — `term.perceive.semantic-events`, `pump.wake-on-boundaries`, `pump.cli.wake-lines` (`aspump`). The pump tails from a client-held offset OR a **broker-committed durable-group cursor** — also **Built**: `pump.attach-subject-and-group` (`Pump::attach_group` resumes from the durable commit across a restart with no missed or doubled boundary) and `aspump --group`, pinned by `pump.cli.wake-lines`, so a killed run's replacement starts with no `--from` and replays nothing it had committed. The group form is at-least-once on wakes (the commit follows the acted-on wake). The agent-hook wake remains Designed (`DESIGN-drive-pipe.md` §5) |

Each "Built" row is backed by a re-runnable green claim in the evidence manifest;
nothing in the remaining "Designed" rows is claimed as working — each becomes a
manifest row with a re-runnable command the day it is real.

## 7. Verification posture: what "verified" means here, layer by layer

astream is verified in four layers, strongest-where-it-matters-most, and we are
precise about the scope of each — overclaiming verification is itself a kafka2 trap.

1. **By construction (the compiler, always on).** `forbid(unsafe_code)` in every
   substrate crate (all but two cordoned modules in `astream-host`, whose crate
   root is `deny(unsafe_code)` with a scoped `allow` on exactly `sys` (`cfg(unix)`,
   the PTY) and `foreign` (`cfg(target_os = "linux")`, the ptrace tracer)) makes
   memory-safety and **data-race freedom** *compiler-proved*,
   not conventional: the concurrent broker (writer thread, `Arc`/`Mutex`/`Condvar`,
   channels, atomics, the pipelining ack-writer) type-checks only because `Send`/`Sync`
   discharge. Newtypes (`Offset`), checked arithmetic, and consuming typestate
   (`Subscription`) push more invariants into the type system.
2. **Property-based testing (proptest, 4 crates: `astream-wire`, `astream-term`,
   `astream-engine`, `astream-live`).** Laws checked over thousands of generated
   inputs with shrinking (e.g. the router differential oracle). `astream-host`
   declares the dev-dependency but carries no property test yet.
3. **Model-based testing of the stateful log** (`broker.model-based-equivalence`). An
   independent reference *model* (spec) of the durable log is run in lock-step with the
   real file-backed group-commit implementation over random operation sequences,
   asserted equal at every flush and after crash recovery — two implementations of one
   spec that must not diverge.
4. **Compiler-enforced verification of the pure core's guards** (`evidence/verify/trust-wire.md`,
   Trust). [Trust](https://github.com/alabsystems/trust) is a `rust-lang/rust` fork
   whose SMT-backed verifier (`ay`) runs as a MIR pass **during compilation**. It
   **auto-generates** the Level-0 safety obligations from the MIR (overflow, bounds,
   div/rem-by-zero, allocation bounds, panic-freedom) — **no proof harnesses or
   annotations** — and `-Z trust-policy=strict|certify` are **fail-closed** (an unproved
   obligation is a build error; the older `-Z trust-verify-full` flag no longer exists).
   Honest scope: `scripts/verify-trust.sh` builds the **real `astream-wire` library**
   and records every verdict. It proves the decoder's header indexing, the CRC-32 table
   lookup, the encoder's length add and `h % n` (61 of 98 obligations);
   `Offset::checked_next`/`delta_from` use checked arithmetic and so carry no overflow
   obligation at all; it refutes four allocation-side obligations and leaves 26 calls
   into `std` runtime-checked. The crate does **not** build under the strict or certify
   policy: proof-aware, not proof-complete, and the survey names every gap.
   Not a make-ci claim (Trust is a separate toolchain); an attached, re-runnable artifact.

**The boundary (non-negotiable honesty).** This verifies the *substrate's invariants*.
It does **not** verify the whole distributed system, and it says nothing about agent
behaviour — "provably correct agents" remains deliberately out (§1). The true statement
is: *the pinned Trust compiler proves 61 of the 98 Level-0 obligations it generates from
the real wire crate's MIR and the attached survey names every one it does not; the crate
does not build under Trust's strict policy — proof-aware, not proof-complete; the stateful log is model-checked against a reference spec; safety and
data-race freedom are compiler-proved by `forbid(unsafe)` outside two cordoned OS
modules.* Not: "astream is provably correct."
