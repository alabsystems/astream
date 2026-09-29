# astream-term: a deterministic record/replay terminal substrate

The unified design + status record for carrying a terminal session over astream —
the honest successor to `ssh + mosh + tmux` for **auditable, replayable,
multi-subscriber agent sessions**. This is the home doc; it consolidates the
former SSH design record, this protocol record, and the cross-repo
[`THEORY-deterministic-sessions.md`](THEORY-deterministic-sessions.md).

The one rule it never breaks: **ambition and evidence may not drift.** Every
subsection is tagged **BUILT** (a green manifest claim runs it), **DESIGNED** (no
claim yet), or **SEED** (the re-runnable command that would make it real). The
honest name is a *deterministic record/replay PTY substrate*. The transport half of
"SSH" is now largely built and opt-in (§11): an XChaCha20-Poly1305 wire, an ephemeral
X25519 key agreement over it for forward secrecy, mutual static public-key identity
(the client pins the broker's host key, the broker allow-lists the client — no shared
secret at all), a capability mint the broker enforces on attach, capabilities that
expire, and the durable log sealed at rest. What is still missing for the word:
identity bound to an EXTERNAL authority (an SSH agent, OIDC) rather than a locally
allow-listed key, and the operational surface — key distribution, rotation,
revocation — that a real SSH deployment has.

## 1. Thesis

A terminal session is **two ordered streams plus a pure derived screen**:
keystrokes in (`In`), PTY bytes out (`Out`), and a screen that is a pure,
I/O-free fold of the output — `screen_n = vt_apply(screen_{n-1}, record_n)`. Once
those streams are one ordered log, the connection stops being where the session
lives: a client is two cursors into a log, and every event classic SSH dies from
(RST, wifi→cellular roam, sleep, even `kill -9`) collapses into one operation —
*reopen a byte path, resume from your offsets*. This is astream's
record-the-inputs thesis on the most universal tool there is, and it buys the one
thing no shell tool has: a live session that **is its own durable, replayable,
forkable audit log.**

## 2. Status ledger

The ledger of record is `evidence/manifest.toml`; the README's Evidence table is
generated from it and the gate rejects drift, so the manifest is the only place a
claim count lives. The table below maps the claims this document cites to their
determinism rung; it does not list every broker and fabric claim.

**All four levels of the determinism dial now have green claims** — Render,
Session, **Effects** (`effects.cooperative.record-replay`), and **Cognition**
(`term.cognition.replay-and-fork`, the summit, hermetic replay half). Rungs 0.5–3,
a live PTY host, the fleet layer (text+query, image+animation, interactive
driving, N-child orchestration, control handoff), the DECSTBM fold widening, and
the Effects + Cognition rungs are **BUILT and green** — plus **durable execution**
on the Strict log (`engine.durable.exactly-once-resume`) and **regression-floor
benches** for the engine append/replay and the screen fold (`engine.bench.*`,
`term.bench.fold-floor`), and the foreign-process Effects rung via Linux `ptrace`
(`effects.foreign-process.record-replay`, a Linux-gated claim). `make ci` runs every
claim, clippy, and the merge gate with 0 findings; hosted CI
(`.github/workflows/ci.yml`) runs it on Linux on every push, so the Linux-gated
claim runs there, and a local `make ci` on macOS skips it (there is no macOS
runner). The newest layer makes astream a **servable message bus**
(`astream-broker`): durable exactly-once pub/sub + resume, counterfactual
fork-delivery + cognition routing, true end-to-end exactly-once (durable group
commits + atomic read-process-write), a Redis-parity throughput floor, **group
commit** (a single writer thread amortizes one fsync over a concurrent batch —
durable throughput scales with concurrency at the same `ack ⟹ fsync'd` guarantee),
**single-connection pipelining** (one connection keeps many publishes in flight),
**share-nothing sharding** (N independent brokers, per-partition order — a
horizontal-scale architecture, honestly NOT a single-disk Strict throughput win),
multi-machine TCP, an unforgeable HMAC capability mint (`astream-cap`,
`wire.filter.containment`) **enforced on the broker's accept path** behind the opt-in
`cap` feature (`broker.cap-enforced-on-attach`), an **AEAD wire** — the same TCP
protocol sealed with XChaCha20-Poly1305 under a pre-shared key, opt-in `aead` feature
(`astream-aead`; `aead.seal-open.authenticated`, `broker.sealed-tcp-roundtrip`), with a
**forward-secret X25519 key agreement** over it (opt-in `handshake`;
`aead.handshake.forward-secret-key-agreement`, `broker.handshake-tcp-roundtrip`) and
**mutual static public-key identity** with no shared secret (opt-in `identity`;
`aead.identity.mutual-signed-dh`, `broker.identity-tcp-roundtrip`), capability
**expiry** (`cap.expiry-enforced`), the durable log **sealed at rest** with an
anti-rollback watermark and **retention** beside it (opt-in `at-rest`,
`anti-rollback`, `retention`; `broker.log-encrypted-at-rest`,
`broker.log-anti-rollback`, `broker.log-retention`), the
**drive-pipe pump** (`astream-pump`: `term.perceive.semantic-events`,
`pump.wake-on-boundaries`, `pump.attach-subject-and-group`), two shell faces `asb` / `aspump` (`broker.cli.*`,
`pump.cli.wake-lines`), a table-driven CRC-32 on the frame hot path
(`wire.hash.crc32-table-equiv`, `wire.bench.crc32-floor`), and a Kafka wire-protocol
handshake (`astream-kafka`). The pure wire core carries an attached **Trust verification survey** of the
real crate (`evidence/verify/trust-wire.md`): the pinned Trust compiler (a
`rust-lang/rust` fork, SMT verifier as a MIR pass) proves 61 of the 98 Level-0
obligations it generates from `astream-wire`'s own MIR and the survey names every one
it does not — the crate does not build under Trust's strict policy; the durable log is **model-checked** against a reference spec
(`broker.model-based-equivalence`); see [`DOCTRINE.md`](DOCTRINE.md) §7.

| Claim id | Kind | Determinism rung | Status |
|---|---|---|---|
| `build.reproducible` | test | — | BUILT |
| `wire.frame.panic-safe` | test | L0 | BUILT |
| `wire.address-grammar.validated` | test | L0 | BUILT |
| `wire.router.matches-independent-oracle` | test | L0 | BUILT |
| `wire.partition.deterministic-and-in-bounds` | test | L0 | BUILT |
| `wire.filter.containment` | test | L0 | BUILT |
| `wire.hash.crc32-table-equiv` | test | L0 | BUILT |
| `gate.rejects-known-failures` | test | — | BUILT |
| `gate.rejects-theater-evidence` | test | — | BUILT |
| `term.screen-fold.deterministic` | test | Render | BUILT |
| `term.replay.byte-identical` | selftest | Render | BUILT |
| `term.strict.survives-kill` | test | Session | BUILT |
| `term.resume.gapless-exactly-once` | test | Session | BUILT |
| `term.echo.predict-and-reconcile` | test | Session | BUILT |
| `term.fork.counterfactual-replay` | selftest | Session | BUILT |
| `term.fork.multi-client` | test | Session | BUILT |
| `term.pty.records-and-replays` | test | Session | BUILT |
| `term.fork.prefix-stable` | test | Session | BUILT |
| `term.fleet.consistent-cut-replay` | test | Session | BUILT |
| `term.echo.watermark-retire` | test | Session | BUILT |
| `term.screen-ops.lossless-projection` | test | Render | BUILT |
| `term.perceive.query` | test | Render | BUILT |
| `term.perceive.semantic-events` | test | Render (drive pipe) | BUILT |
| `pump.wake-on-boundaries` | test | Drive pipe | BUILT |
| `pump.cli.wake-lines` | test | Drive pipe | BUILT |
| `term.perceive.render-deterministic` | test | Render | BUILT |
| `term.drive.interactive-exactly-once` | test | Session | BUILT |
| `term.fleet.orchestrate-n` | test | Session | BUILT |
| `term.fleet.control-handoff` | test | Session | BUILT |
| `term.fold.scroll-region` | test | Render | BUILT |
| `term.fold.bce` | test | Render | BUILT |
| `term.fleet.durable-watermark` | test | Session | BUILT |
| `term.echo.caused-by-retire` | test | Session | BUILT |
| `effects.cooperative.record-replay` | test | **Effects** | BUILT |
| `effects.foreign-process.record-replay` | test (Linux-gated) | **Effects** | BUILT |
| `term.cognition.replay-and-fork` | selftest | **Cognition** | BUILT |
| `term.session.unified-replay-and-fork` | test | **All four** | BUILT |
| `cognition.live-bridge.parse-and-replay` | test | **Cognition** | BUILT |
| `engine.durable.exactly-once-resume` | test | Session (durable exec) | BUILT |
| `evidence.selftest.hash-pinned` | test | — | BUILT |
| `wire.bench.frame-roundtrip-floor` | bench | — | BUILT |
| `wire.bench.match-floor` | bench | — | BUILT |
| `wire.bench.crc32-floor` | bench | — | BUILT |
| `engine.bench.append-floor` | bench | — | BUILT |
| `engine.bench.replay-floor` | bench | — | BUILT |
| `term.bench.fold-floor` | bench | — | BUILT |
| `broker.exactly-once-pubsub-resume` | test | Servable bus | BUILT |
| `broker.agent-native-fork-and-cognition` | test | Servable bus | BUILT |
| `broker.true-exactly-once-e2e` | test | Servable bus | BUILT |
| `broker.bench.publish-floor` | bench | Servable bus | BUILT |
| `broker.group-commit-durability` | test | Performance | BUILT |
| `broker.bench.groupcommit-floor` | bench | Performance | BUILT |
| `broker.model-based-equivalence` | test | Verification | BUILT |
| `broker.pipelining` | test | Performance | BUILT |
| `broker.bench.pipeline-floor` | bench | Performance | BUILT |
| `broker.sharded-routing` | test | Performance | BUILT |
| `broker.relaxed-tier` | test | Durability dial | BUILT |
| `broker.bench.relaxed-floor` | bench | Durability dial | BUILT |
| `broker.replicated-tier` | test | Durability dial | BUILT |
| `broker.bench.replay-egress-floor` | bench | Performance | BUILT |
| `broker.tcp-transport` | test | Transport | BUILT |
| `broker.cli.pub-sub-roundtrip` | test | Servable bus (CLI) | BUILT |
| `broker.cli.tcp-roundtrip` | test | Transport (CLI) | BUILT |
| `cap.unforgeable-mint` | test | Security | BUILT |
| `broker.cap-enforced-on-attach` | test (`cap` feature) | Security | BUILT (opt-in) |
| `aead.seal-open.authenticated` | test | Security | BUILT |
| `broker.sealed-tcp-roundtrip` | test (`aead` feature) | Transport / Security | BUILT (opt-in) |
| `aead.handshake.forward-secret-key-agreement` | test (`handshake` feature) | Transport / Security | BUILT (opt-in) |
| `broker.handshake-tcp-roundtrip` | test (`handshake` feature) | Transport / Security | BUILT (opt-in) |
| `aead.identity.mutual-signed-dh` | test (`identity` feature) | Transport / Security | BUILT (opt-in) |
| `broker.identity-tcp-roundtrip` | test (`identity` feature) | Transport / Security | BUILT (opt-in) |
| `cap.expiry-enforced` | test (`cap` feature) | Security | BUILT (opt-in) |
| `broker.log-encrypted-at-rest` | test (`at-rest` feature) | Security (at rest) | BUILT (opt-in) |
| `broker.log-anti-rollback` | test (`anti-rollback` feature) | Security (at rest) | BUILT (opt-in) |
| `broker.log-retention` | test (`retention` feature) | Durable log | BUILT (opt-in) |
| `pump.attach-subject-and-group` | test | Drive pipe | BUILT |
| `kafka.handshake-and-metadata` | test | Kafka compat | BUILT |

**DESIGNED** (no manifest claim until a seed runs; their *absence* is the
machine-checked honesty): predicted *program responses* (§8 v1's `P̂`), the
normalized screen-op cross-machine projection (§4), graphemes and truecolour in the
fold (§6), EXTERNAL identity and the key operations around it (distribution,
rotation, capability revocation) on the transport/auth track (§11 — the key
agreement, static public-key identity, cap expiry and encrypt-at-rest are built),
and the Effects sub-seeds (seccomp pre-filter, syscall
neutralization, an exec'd unmodified binary — §13). **Realized since earlier
revisions of this ledger:** `caused_by`-exact echo retirement and the durable
cross-log watermark (`term.echo.caused-by-retire`, `term.fleet.durable-watermark`,
`ENV_VERSION = 3`), the DECSTBM scroll region and `bce` (`term.fold.scroll-region`,
`term.fold.bce`), the aterm oracle (§6, out-of-tree, proven), both forms of the
**Effects** rung (§3: cooperative, and Linux `ptrace` over a forked astream-authored
effect program), the **Cognition** rung (§3, hermetic replay+fork — only the live-API
record pass stays non-hermetic), the AEAD wire + enforced mint, and cap expiry,
encrypt-at-rest, the anti-rollback watermark and retention (§11, opt-in).
Each open seed has a precise falsifiable command in §13; the open list is
[`ROADMAP.md`](ROADMAP.md).

> Naming note: both doctrine-hygiene renames are complete — the terminal claim ids
> use the honest `term.*` namespace and the crate is `astream-term`. The two
> selftest SHAs hash example *stdout*, not the claim id, so the id rename re-pinned
> nothing; the README evidence block (generated from the manifest, with the gate
> rejecting any drift) regenerated to match. The legacy `ssh.*` names are gone.

## 3. The determinism dial (the unifying honesty frame)

Replay fidelity is a **labeled knob**, parallel to astream's durability dial
(`Strict`/`Replicated`/`Relaxed`) and orthogonal to it. It is set by **how far
down the effect seam you record** — and the doctrine rule is that a rung may be
*claimed* only when its seam-completeness has a green artifact.

| Rung | Records | What replays | Status |
|---|---|---|---|
| **Render** | `Out` | the exact screen, scrollback, counterfactual re-geometry | **BUILT** — `term.screen-fold.deterministic`, `term.replay.byte-identical` |
| **Session** | `Out` + `In` | the screen *plus why it looked that way*; freeze any moment as a regression | **BUILT** — `term.resume.*`, `term.fork.*`, `term.fork.prefix-stable`, `term.strict.survives-kill`, `term.pty.*` |
| **Effects** | + clock/rng/fs/net | a *seam-cooperative* program's full execution, or a traced process's syscall effects | **BUILT** (cooperative + foreign-process/`ptrace`, the latter Linux-gated) — `effects.cooperative.record-replay`, `effects.foreign-process.record-replay`; a seccomp pre-filter, full syscall neutralization and an exec'd unmodified binary remain sub-seeds |
| **Cognition** | + LLM calls + tool results | a full **agent** session | **BUILT** (hermetic replay+fork) — `term.cognition.replay-and-fork`; only the live-API record pass stays a seed |

This generalizes the old re-paint-vs-re-drive boundary: *render* is always
replayable (pure fold); the *program* is replayable only insofar as its effect
vector was recorded. Replay is not binary — it is the cut between recorded and
live. All four rungs now carry a green claim, each scoped to exactly what its
seam records: the **Effects** rung replays a *seam-cooperative* program and, on
Linux, the intercepted syscall effects of a forked astream-authored effect program
under `ptrace` (an exec'd *unmodified* binary and true syscall neutralization stay
sub-seeds), and the **Cognition** rung replays a recorded agent turn hermetically
and forks it (capturing a *live* turn is non-hermetic and never a green claim).
Those remaining seam-completeness gaps are the honest boundary, made
machine-checked by the *absence* of a claim for them.

## 4. Verb mapping & event model

One session `S` is one partition with one single writer (`sessiond`). Clients do
not write the log; they submit input as `/a/inbox` proposals that `sessiond`
orders, dedups, applies, and appends.

| Subject | Verb meaning | Carries |
|---|---|---|
| `/a/stream/term/S/in` | ordered log of nondeterministic **inputs** | keystrokes / paste / signals |
| `/a/stream/term/S/out` | ordered log of authoritative **outputs** | **BUILT:** raw VT `Out` bytes (the flight recorder). **DESIGNED:** a derived normalized screen-op view |
| `/a/state/term/S/screen` | materialized current projection | the folded screen + the `out` offset it reflects (`folded_through`) |
| `/a/inbox/term/S/ctl` | addressed control to one consumer | resize, bell, exit, attach-ack |

**BUILT event model** (`astream-engine::envelope`, `ENV_VERSION = 3`): each record
rides inside an `astream_wire::Frame` as a tagged envelope — `tag | seq:u64 | caused_by? |
ts_logical:u64 | body`, where `ts_logical` is read *through the seam Clock* (a
recorded input). Tags: `In{bytes, client_id, client_seq}`, `Out(bytes)`,
`Resize{cols,rows}`, `Exit{code}`. `In` and `Exit` never paint.

**Wire decision (consolidated):** raw `Out` bytes stay the **durable log of
record** — re-folding them in a separate read-by-offset pass is exactly what makes
`term.replay.byte-identical` *non-tautological*. Normalized server-side screen-ops
(`PrintRun`/`SetCursor`/`EraseLine`/`SetSGR`, one canonical parser, structurally
killing the two-party terminfo-disagreement class) are adopted as an **additive
derived projection** for cross-machine viewers — **DESIGNED**, never a replacement
for the byte log. The designed input fields `predicted_at` (the `out` offset the
client's screen reflected) and `in_watermark` (the highest **in-offset** an
output reflects) are the reconciliation signals for §8; note `in_watermark` is an
*engine in-offset*, a different numbering domain from the built per-client
`client_seq`.

## 5. Resume & roaming (BUILT)

A connection is a disposable cursor; a client holds `session_id`,
`last_rendered: Offset`, and its next `client_seq`. Reattach = read `/a/state`
(the snapshot at `folded_through = K`, painted in O(viewport)), then tail
`/a/stream` from `max(K, last_rendered)` — *snapshot + tail, never screen-diffing*.
Roaming is not a special case: an IP change is identical to a drop. Resume is
**exact even when an escape sequence straddles K**, because the snapshot carries
full parser state (the resumable `Folder`). `delta_from` returning `None` is the
gap-direction guard (a client ahead of head is detected, not mis-served).
Exactly-once input is keyed by `(client_id, client_seq)` and the dedup high-water
is rebuildable from the log, so it survives a reconnect. BUILT:
`term.resume.gapless-exactly-once`.

## 6. Render R and the aterm oracle

There are two fidelity rungs of the **same** render function `R`:

- **Embedded reference R (BUILT, fidelity rung 0):** `astream-term::screen` — a
  pure, zero-dependency, `forbid(unsafe)`, cell-exact VT fold over a deliberately
  bounded subset. DECSTBM and background-colour-erase are folded
  (`term.fold.scroll-region`, `term.fold.bce`); documented gaps: one `char` per
  cell not graphemes, no truecolour (`2;r;g;b` is parsed and skipped),
  reverse-video bce out of scope, resize clips wrapped lines. It ships today and
  is what the green claims exercise.
- **Canonical high-fidelity R + pixel oracle (DESIGNED):** the external
  [`aterm`](../../aterm) engine — headless, introspectable, model-checked
  (`ty`/Trust toolchain), xterm-class, grapheme/bidi/pixel-capable. It is the
  natural **replay oracle** (assert `read_text` *and* `read_image` are
  bit-identical to the live session). It is **EXTERNAL and never an in-repo
  dependency** — its large crate tree would break the substrate's
  reproducible-build + zero-dep doctrine. It plugs in only at a future
  verification seam (self-proving transport, THEORY §6), behind its own seed.

aterm and the in-repo fold are not rivals: aterm verifies `R` small and at the
pixel; astream carries `R` wide. They are the same algebraic object — aterm's
`seq == count` spine and astream's `Offset` are the same gap-free monotone
invariant at two scales.

## 7. Partitioning (the resolved non-conflict)

`assign_partition(Keyed(sid), n)` returns `fnv1a_64(sid) % n` — a colliding
partition **index**. Two facts, both true, no conflict:

- It is the correct **co-location routing primitive**: it puts a session's
  `in`/`out`/`state`/`ctl` subjects on the *same* engine instance (one ordering
  domain). Use it for that.
- It is **not** a per-session single-writer-*log* factory — colliding indices
  manufacture no private log.

Co-location *delivers* single-writer rather than contradicting it: once a
session's subjects land on one engine, `sessiond` is the sole writer of that
engine's one-`append`-path log. Use `Keyed(sid)` for co-location **and** an
explicit session→engine map for the one-writer guarantee.

## 8. Smoothness / prediction

- **v0 (BUILT):** `astream-term::Predictor` — speculative local echo painted faint
  before the round-trip, reconciled **positionally** against the authoritative
  `/out` fold; predicts printable echo only, abstains on control/escape. Its green
  claim `term.echo.predict-and-reconcile` proves the **safety theorem**: for *any*
  interleaving of predictions and output, the reconciled view equals the pure
  authoritative fold — a prediction can never corrupt the session.
- **v1 — retirement BUILT, program-response prediction DESIGNED.** The retire
  machinery is green: watermark-monotone retirement against the engine out-offset
  with squash-rebuild from confirmed state (`term.echo.watermark-retire`), and
  `caused_by`-exact retirement that survives reordered/batched echoes
  (`term.echo.caused-by-retire`, the `ENV_VERSION = 3` causal field). What stays
  DESIGNED is *verified speculation* proper: predicting *program responses* (prompt
  redraw, completion menus, cursor moves) with a `P̂` (THEORY §3) and retiring those
  through the same path — strictly stronger than mosh (which fails closed inside
  TUIs) and safe by the same theorem. SEED `term.predict.watermark-squash` over a
  recorded corpus (`METRIC predict_hit_rate` with a floor). `in_watermark` is an
  engine in-offset, a different numbering domain from `client_seq` — do not
  conflate them.

## 9. Counterfactual & history

**BUILT:** fork a recorded session at offset N, swap one `Out` record (the build
result the agent saw), re-derive a byte-exact, screen-exact alternate timeline
(`term.fork.counterfactual-replay`, `term.fork.multi-client`). The new
`term.fork.prefix-stable` claim proves the *branch* half of that framing: the
fork shares a **byte-identical** prefix with the original (asserted by byte
equality over the stored frames) and branches only forward — *counterfactual =
branch sharing a prefix*, proven over the built log. **DESIGNED:** the
content-addressing itself — nothing in the log is hash-linked, it carries no
digest of its history, so a Merkle-DAG session history (offsets + hashes as a
commit chain; diff = tree-diff; merge meaningful only on input logs) remains a
designed seed.

The honest bound (loud): a forked `Out` timeline re-renders deterministically; it
does **not** re-drive the program (the agent does not re-decide) unless every
effect is seam-mediated — which is sound only for a fully instrumented agent
(the Cognition rung), never a bare shell.

## 10. Fleet (BUILT)

An agent fleet is a forest of sessions, each a partition, all on one log. An
orchestrator subscribes to N child `out`-logs (multi-subscriber, free via the
`Filter` grammar — a capability IS a Filter over a session subtree) and injects
into any child's `in`-log. A fleet-level counterfactual is a **consistent-cut
replay** (a vector of per-partition offsets respecting cross-log watermarks).
**BUILT:** `term.fleet.consistent-cut-replay` (two sessions with a cross-injection
edge; a Chandy-Lamport cut as an offset-vector; each partition replays to its live
screen; an effect-without-cause cut is rejected), `term.fleet.durable-watermark`
(the causal edge persisted on-log as `caused_by:(Partition,Offset)`, `ENV_VERSION =
3`, so the cut predicate is reconstructible from recovered bytes alone),
`term.fleet.orchestrate-n` (one orchestrator, three real heterogeneous PTY
children), `term.fleet.control-handoff` (`ControlToken`: exactly one writer, an
auditable handoff). **DESIGNED:** the fleet's collective screen as one
`state`-verb materialized view, and a cognition-domain fleet replay.

## 11. Security & transport (the "term, not SSH" boundary — both blockers BUILT, opt-in)

`astream-broker` serves over **TCP as well as a Unix socket** (`serve_tcp`,
`broker.tcp-transport`). The *default* TCP wire is **plaintext frames** (`Frame`'s
CRC32 is integrity-against-corruption, **not** a MAC) with no authentication —
multi-machine on a TRUSTED network only. Both pieces the doctrine named as blocking
untrusted-network use are now built, each behind an off-by-default cargo feature so
the default broker stays zero-third-party:

1. **AEAD on the wire — BUILT (opt-in `aead` feature).** `astream-aead` seals with
   XChaCha20-Poly1305 (the vetted RustCrypto primitive, isolated in that one crate,
   never hand-rolled — the documented exception to zero-dep) under a 32-byte
   **pre-shared key**; `Broker::serve_tcp_sealed` / `Client::connect_tcp_sealed`
   (and `asb --key-env NAME` / `--key-file PATH`; a bare `--key HEX` on argv is
   refused) run the identical Frame protocol inside an ordered-record
   `SealedStream`. Each connection opens with a hello exchange — 32 CSPRNG bytes
   each way — and every record's AAD is
   `hello_client ‖ hello_server ‖ direction ‖ seq`, so a record is valid only for
   this connection, this direction and this position
   (`aead.seal-open.authenticated`, `broker.sealed-tcp-roundtrip`).
   **Forward secrecy — BUILT (opt-in `handshake`).** An ephemeral X25519 agreement
   authenticated by the PSK (the NNpsk pattern) derives a fresh per-session key, so a
   later PSK compromise cannot decrypt a recorded session
   (`aead.handshake.forward-secret-key-agreement`, `broker.handshake-tcp-roundtrip`).
   **Static public-key identity — BUILT (opt-in `identity`).** A mutual signed-DH
   (SIGMA / Ed25519) handshake replaces the shared secret entirely: the client pins
   the broker's host key, the broker allow-lists the client's identity, and because
   the identity keys only SIGN the ephemeral transcript, forward secrecy survives an
   identity-key compromise (`aead.identity.mutual-signed-dh`,
   `broker.identity-tcp-roundtrip`). All three share one record layer, whose AAD binds
   whatever the handshake above it agreed — the hellos for the PSK wire, the DH
   transcript for the other two. **At rest — BUILT (opt-in).** The same primitive
   seals the durable log itself: `Broker::open_encrypted` (`at-rest`) seals each
   record's payload on disk with its log index as AAD (`broker.log-encrypted-at-rest`);
   `Broker::open_encrypted_verified` (`anti-rollback`) adds an authenticated head
   watermark in a `<log>.hw` sidecar and refuses a log rolled back below it
   (`broker.log-anti-rollback`); and `Broker::retain_before` (`retention`) compacts
   the log while keeping surviving offsets absolute (`broker.log-retention`). Not
   built: identity bound to an external authority (SSH agent / OIDC) rather than a
   locally pinned and allow-listed key.
2. **A sound, unforgeable capability mint — BUILT, and enforced on attach (opt-in
   `cap` feature).** `astream-cap` signs a `Filter` with HMAC-SHA256 (RFC 2104 over
   the vetted `sha2`, checked against the RFC 4231 vector), verified in constant
   time; tampered/widened/forged/wrong-secret capabilities are rejected
   (`cap.unforgeable-mint`, `wire.filter.containment`). `Broker::open_guarded`
   refuses any publish/subscribe/commit outside the presented capability's grant
   (`broker.cap-enforced-on-attach`). A grant can carry an expiry (`exp=` in its
   prefix), checked per request, so even a live connection loses authority at the
   deadline (`cap.expiry-enforced`); revocation before the deadline (short of rotating
   the secret) and attenuation are not built. An unguarded broker still equates
   reachability with access.

Authorization is per-subject-prefix — the `Filter` grammar is the ACL surface, with
an unforgeable mint over it — but astream authenticates attachment to the log, it
does not replace the host OS's authentication of the shell's owning uid. The honest
status is **"multi-machine over a sealed, forward-secret, optionally
identity-authenticated, capability-scoped bus"** — the shared secret is no longer
required at all when the `identity` feature is used, and the log can be sealed at
rest. It earns **"SSH"** only with identity bound to an EXTERNAL credential (an SSH
agent, OIDC) plus the key operations around it (distribution, rotation, revocation)
— see `DESIGN-drive-pipe.md` §7 and `ROADMAP.md`.

## 12. The live PTY host (BUILT)

`astream-host` drives a **real** pseudo-terminal: `libc posix_openpt+grantpt+unlockpt`
with `O_CLOEXEC` on Linux, `libc openpty` on other Unix, then `fork + exec`
runs a child, its master output is drained into `Record::Out` on the engine log
through the seam, and the child's exit is reaped into `Record::Exit`. A separate
read-by-offset pass over the stored bytes — no OS — reconstructs the records and
folds a screen equal to both the live screen and the known output. All OS access
and the workspace's `unsafe` are confined to two cordoned modules of this crate —
`sys` (`#[cfg(unix)]`, the PTY) and `foreign` (`#[cfg(target_os = "linux")]`, the
ptrace tracer of §13) — under a crate-root `deny(unsafe_code)` with a scoped `allow`
on exactly those two; `wire`/`term`/`engine` keep `forbid(unsafe)` + zero
third-party deps. The dependency
is `libc` (already in the locked graph → zero new crates). Only the chunk-invariant
folded screen is asserted (chunk boundaries/timing are nondeterministic). BUILT:
`term.pty.records-and-replays`.

## 13. Honest scorecard & open seeds

**Genuine wins** (defensible on the built substrate): durable, replayable,
**auditable** session history — a capability no incumbent has; persistence +
roaming + scrollback + resume **unified into one offset-addressed log**;
multi-subscriber sessions for free (one agent observing another); counterfactual
fork with a byte-identical shared prefix; state-level prediction that rolls back
exactly. **Ties / losses (no hedging):** latency floor is RTT for everyone
(prediction is mosh's own trick — no physics win); far heavier than mosh's single
UDP datagram (the durable log is a hot-path liability, repaid only if you use
replay/audit); ecosystem maturity ≈ 0; larger attack surface + a durable store of
every keystroke (a forensic target). **For a single human on a single link,
mosh + tmux remains the right tool**, and this design says so. The decisive niche
is *auditable, replayable, multi-subscriber sessions for agent fleets* — exactly
astream's reason to exist.

**Open seeds (DESIGNED — no manifest claim until each runs; the absence is the
honesty).** Each is a precise, re-runnable command + assertion that *would* make
it real, with the honest reason it is not a green claim today:

| Seed | Falsifiable command + assertion | Why it stays DESIGNED |
|---|---|---|
| **Durable cross-log watermark** (the persisted half of fleet, §10) — **BUILT** | `cargo test -p astream-engine --test fleet_durable_watermark` (`term.fleet.durable-watermark`). **DONE:** `caused_by:(Partition,Offset)` rides the envelope (`ENV_VERSION = 3`); `cross_edges_from_logs` decodes a *recovered* child log alone (no in-memory `CrossEdge`) and reconstructs the consistent-cut predicate purely from on-log bytes. | **Remaining:** a fleet-wide `state`-verb materialized view over the cut; a cognition-domain fleet replay. |
| **`caused_by`-exact retirement** (the strongest form of §8) — **BUILT** | `cargo test -p astream-engine --test caused_by_retire` (`term.echo.caused-by-retire`). **DONE:** a prediction retires by `caused_by == its in-offset` even when its echo is reordered/batched with another keystroke's, where positional/watermark retirement mis-assigns it; the field is a real on-log envelope field, not synthesized. | **Remaining:** host-side PTY write→read correlation so a *live* PTY host stamps `caused_by` (today the engine stamps it on the recorded path); the `P̂` program-response predictor (§8 v1). |
| **Faithful-xterm op set** (the wider form of §4) — **DECSTBM and `bce` done** | `cargo test -p astream-term --test scroll_region` + `--test bce` (in-tree) + `cd the aterm repo's astream-oracle && cargo test --test scroll_region` (vs real aterm). **DONE:** the `DECSTBM` scrolling region is folded, projected losslessly as a `SetScrollRegion` op, and agrees with the production aterm engine over fixtures + 300 random region programs (`term.fold.scroll-region`); erase honours background-colour-erase (`term.fold.bce`, cross-validated structurally against aterm; reverse-video bce out of scope). **Remaining (still seeds):** graphemes and truecolour. | The widening proceeds one feature at a time, each cross-validated against the real aterm engine. Graphemes/truecolour need a richer (cluster / cell-colour) oracle than the text-level `visible_content` comparison. |
| **Effects rung** (§3) — **cooperative form BUILT; foreign-process form BUILT (Linux)** | `cargo test -p astream-effects --test cooperative_replay` (`effects.cooperative.record-replay`) + `cargo test -p astream-host --test effects_foreign_process` (`effects.foreign-process.record-replay`, Linux-gated). **DONE (cooperative):** a program written against `EffectSeam` records its real clock/rng/file reads and replays byte-identically; `ReplaySeam` makes no OS call. **DONE (foreign process):** `astream-host::foreign` uses `ptrace(PTRACE_SYSCALL)` to record + replay the syscall effects of a NON-cooperating forked child into the SAME `EffectsLog`; injected replay reproduces the digest against a deliberately-changed world while a naive replay diverges; independent oracle + order-sensitivity + fail-closed abort. Platform-gated to Linux: hosted CI runs it on every push, and a local macOS `make ci` skips it. | **Remaining sub-seeds (smaller now):** a **seccomp-bpf** pre-filter (a perf optimization so the tracer is O(intercepted) not O(all) syscalls — the `ptrace`-only form already proves the capability); **full syscall neutralization** (replay overwrites the result but the kernel still runs the now-ignored call — true no-kernel-effect is stronger); a separately-**exec'd** image (vs the forked child). The seed command and design notes are in [`ROADMAP.md`](ROADMAP.md). |
| **Cognition rung** (§3) — **replay + unified capstone BUILT (the summit); live bridge BUILT in-tree (zero-dep); capture CLI BUILT** | `cargo run -p astream-agent --example agent_replay` (`term.cognition.replay-and-fork`) + `cargo test -p astream-agent --test unified` (`term.session.unified-replay-and-fork`). **DONE:** a bounded agent turn replayed hermetically + forked; all four streams unified on one offset axis; in-tree `crates/astream-live` (zero third-party dep -- a hand-rolled JSON parser; `cognition.live-bridge.parse-and-replay`) parses a **real Anthropic Messages response** into that unified log and replays it; and the `astream-live` **`capture` binary** (`cargo run -p astream-live --bin capture`) is the operator-facing tool that records one real model COMPLETION (key via curl stdin, never argv) and replays the session assembled around it -- the tool the completion asks for is NOT run, and that tool result and the effect clock are fixed placeholders. | **Remaining (one runtime step):** a real, non-deterministic live model call — non-hermetic by nature, so never a *green* (SHA-pinned) claim. But it is now **runnable here without a key**: `capture_via_cli` shells the authenticated `claude` CLI (the `capture` bin uses it when `ANTHROPIC_API_KEY` is absent), and `cargo run -p astream-live --bin capture` captures a genuine, non-deterministic model COMPLETION and replays the assembled session deterministically (the placeholder tool result and clock are the honest gap, stated in the binary's own doc). The key-gated `curl` path (`capture_live`) and both `--ignored` live tests cover it too. The irreducible non-determinism of a live call — not the lack of a key — is why it stays gated, and that is the honest boundary. |
| **Durable execution** (§ doctrine 3) — **BUILT** | `cargo test -p astream-engine --test durable` (`engine.durable.exactly-once-resume`). **DONE:** a workflow's steps are journaled to the Strict log; a crash at any inter-step boundary — and arbitrary repeated crashes (proptest) — resumes with each step run exactly once. | **Remaining seeds:** a *distributed* durable engine and a step-DAG (vs the in-process single-writer linear workflow); the mid-step crash is at-least-once (idempotency caveat), witnessed by a test. |
| **Cross-system throughput** (doctrine §5) — **in-tree regression floors BUILT** | `cargo run --release -p astream-{wire,engine,term} --example microbench` (`wire.bench.*`, `engine.bench.*`, `term.bench.fold-floor`) hold throughput floors that fail the gate on a catastrophic slowdown. | **Remaining seed:** a *cross-system* comparison vs Kafka/NATS/Redis at equal durability needs disclosed hardware + those systems installed + the broker — Phase 2; an in-tree floor is a regression gate, not a comparison, and the docs say so. |
| **aterm pixel oracle** (§6) — **REALIZED out-of-tree** | `cargo test --manifest-path astream-oracle/Cargo.toml` (in the aterm repo) (a **separate repo** path-depping astream-term + the real production aterm `aterm-core`/`aterm-render`). Proven green: astream-term's fold text equals aterm's `visible_content` at **every prefix offset** of 8 fixtures **and 500 random subset programs**, and aterm's CPU rasterizer renders **bit-identical pixels** across replays. | Built against the real aterm engine and passing — but it stays **off astream's manifest by design**: aterm's ~40-crate tree can never be an astream dependency (it would break reproducible-build + zero-dep — in-tree trips `no-git-deps`/`verify-isolation`, cited-but-absent trips `manifest-integrity`). Its **absence from the manifest is the doctrine; its green out-of-tree test is the proof.** This is the strongest cross-validation astream-term has: two independently-built engines agreeing byte-for-byte on the supported subset. |
| **io_uring egress/ingest** (doctrine §4.2 mechanical sympathy) — **SEED** | A `cfg(linux)` claim `broker.bench.iouring-floor` whose example drives the broker's socket I/O through an `io_uring` submission/completion ring and beats the current `read`/`write_all` syscall-per-op path on a batched-egress workload (assert ops/s above a floor), verified on Linux, where hosted CI runs `make ci` (the `effects.foreign-process` pattern). | std has no `io_uring`; a real ring needs raw `io_uring_setup`/`enter` **unsafe** FFI. The doctrine forbids `unsafe` outside the two cordoned modules in `astream-host` (`sys`, and the `cfg(linux)` `foreign` tracer), and forbids third-party deps (so the `io-uring`/`tokio-uring` crates are out). So this needs an explicit decision: a NEW cordoned `cfg(linux)` unsafe module (crate-root `deny(unsafe_code)` + a scoped `allow`, exactly the `foreign` pattern), or a vetted-dependency exception. Until that decision lands it stays a seed — the portable `read`/`write_all` path (with group commit + pipelining + Arc egress) is already measured, so this is a Linux-specific optimization, not a missing capability. |
| **Replicated durability tier** (doctrine §3 dial) — **BUILT** | `broker.replicated-tier`: `Broker::open_replicated` makes a leader (local Relaxed) ship each committed batch to follower brokers over TCP; an ack waits for a follower QUORUM, so an acked record survives leader-node loss (proven: a follower serves all acked records, at matching offsets, after the leader is shut down). | **Remaining (a later track):** leader election / automatic failover, follower catch-up/truncation after rejoin (a diverged follower is fenced today, never overwritten), capability attachment on follower links, and a multi-node failure-injection matrix. Commit records and read-process-write annotations already replicate at matching offsets. |

The doctrine-hygiene renames (claim ids to `term.*`, crate to `astream-term`) are
complete.
