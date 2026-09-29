# DESIGN: the drive pipe — one agent driving another terminal as a user, over astream

**The pipe** is the channel by which a **driving agent** (Window B — a Claude Code)
operates a **target** (Window A — an aterm session running *any* program: Claude
Code, Codex, emacs, a REPL) **as if it were the user** — keystrokes in, screen out
— efficiently, exactly-once, replayably, and **across machines**.

This is the concrete, buildable form of the conversation that produced it, grounded
against two real codebases: **aterm** (`~/aterm`, the headless introspectable
terminal engine) and **astream** (`~/astream`, the offset-addressed deterministic
message bus). It extends `DESIGN-aterm-lash.md` ("lashing aterms over
astream") with the one thing that design does not have and the pattern most needs:
**the pump** — the bridge from a block-forever bus to a turn-based agent.

Where the pipe carries ONE driver's keystrokes and screen for ONE target,
[`DESIGN-aterm-fabric.md`](DESIGN-aterm-fabric.md) carries the fleet's
*conversation* on the same bus — broadcast (halts, presence, acknowledged
barriers) and addressed messaging (ask/answer, task/report, handoff) between many
aterm instances, on one machine and across them.

Status discipline follows astream's doctrine: every capability is tagged
**BUILT** (a green re-runnable claim runs it today) / **DESIGNED** (specified, no
claim yet) / **SEED** (a precise command would make it real) / **RED** (a blocker).
One more tag is needed for the aterm-side tools and is deliberately weaker than
BUILT: **HAND-RUN** (an out-of-tree script in `~/aterm/tools/` that has been
exercised by hand against the built bus; **no test in either repo runs it**, so
nothing it does is a claim). Claim ids and `file:line` are cited so nothing here
is theater.

---

## 1. The problem, stated precisely

A human driving a terminal has two powers an AI driver does not:

1. **Continuous, free perception.** A human watches the screen the whole time. An
   AI cannot: reading the screen on a timer is wasteful, laggy, and polling-shaped.
   The driver needs **block-until-something-happens**, then a wake — a *push*
   channel, not a poll loop.
2. **A body that persists.** A human sits there. A **Claude Code agent is
   turn-based** — it thinks, calls tools, and *stops*. It cannot hold a socket
   open across turns. So a raw pipe (a fd you block-read forever) is unusable by
   the very consumer we are building for.

Two more requirements came out of the conversation:

3. **Any program in A.** The target is not necessarily an agent. You cannot
   `--resume` emacs; you drive it by *being a user at its terminal*. So the channel
   must be the universal terminal shape (keystrokes/screen), not an agent RPC.
4. **Cross-machine.** The powerful version is one orchestrator on a laptop driving
   and watching a fleet of workers — claude, codex, emacs — on remote machines.

The honest failure mode of the naive approach (an agent issuing `aterm-ctl
status`/`text`/`await` in a loop) is: it is one fork+connect+auth+one-verb per
observation, it is polling-shaped, it loses its place on a disconnect, and it has
no notion of "wake me." **The pipe fixes all four by making the session a durable
offset log and putting a pump between the log and the agent.**

---

## 2. Why astream is the right substrate

astream's thesis (`DESIGN-astream-term.md §1`) is exactly the shape we
need: **a terminal session is two ordered streams plus a pure derived screen** —
`In` (keystrokes), `Out` (PTY bytes), and `screen_n = vt_apply(screen_{n-1},
record_n)`. Once those streams are one ordered log, *the connection stops being
where the session lives* — a client is just two cursors into a log, and every event
that kills SSH (RST, wifi→cellular roam, sleep, `kill -9`) collapses into one
operation: **reopen a byte path, resume from your offsets.**

That single property — the **gap-free Offset spine** — is what raw `aterm-ctl
subscribe` cannot give, and it is what makes the pipe *reasonable* rather than a
polling hack. Concretely, astream already ships as green claims:

| Property the pipe needs | astream, today | Status |
|---|---|---|
| Push, not poll (block until the next event) | broker SUBSCRIBE parks on a `Condvar` tail (`shared.tail.wait_timeout_while(.., LIVENESS_POLL, ..)` in the subscriber tail loop, `astream-broker/src/broker.rs:1780`); a commit `notify_all`s it (`:1732`). Delivery is Condvar-woken — no delivery polling, no sleeps on the data path; the tail thread wakes every 200 ms (`LIVENESS_POLL`, `:229`) only to detect a vanished peer | **BUILT** `broker.exactly-once-pubsub-resume` |
| Resume exactly where you left off | reconnect `from_offset = last+1`, or a broker-durable consumer **group** whose commit survives a broker restart | **BUILT** `broker.true-exactly-once-e2e` |
| Never double-drive a keystroke | exactly-once *ingest*: `Publish{producer_id,producer_seq}` deduped to its original offset; drive deduped by `(client_id,client_seq)` at one point | **BUILT** `term.drive.interactive-exactly-once` |
| Replay / scrub back the whole session | `frame(K) == fold(Out[0..=K])`, byte-identical replay from offset 0 | **BUILT** `term.replay.byte-identical` |
| Coalesced "what changed" signal | `frame_hash` (FNV-1a over the folded screen) — moves iff the screen changed | **BUILT** `term.perceive.render-deterministic` |
| Perceive at any offset: text / blocks / search / image / animation | `astream-term::perceive` + `::render` | **BUILT** `term.perceive.query`, `.render-deterministic` |
| Many watchers, none disagreeing | one canonical server-side fold; N clients are cursors into the same Out-log | **BUILT** `term.fleet.orchestrate-n` |
| One writer at a time + human handoff | `astream-engine::ControlToken` — only the holder drives; transfer is auditable. HONEST: enforcement is at the engine's token-taking ingest (`Session::apply_input_as`); the plain `apply_input` takes no token and the `astream-host` `Driver` still calls that one, so routing the live PTY path through the token is a host-crate follow-up | **BUILT** `term.fleet.control-handoff` |
| Cross-machine transport | the *same* protocol over `serve_tcp` (generic `Stream`) | **BUILT** `broker.tcp-transport` |
| Cross-machine durability | leader→follower quorum ack over TCP | **BUILT** `broker.replicated-tier` |
| Scoped authorization | an unforgeable capability = a signed `Filter` subtree (HMAC-SHA256) | **BUILT** `cap.unforgeable-mint` |
| A real PTY host for the target | `posix_openpt`(Linux)/`openpty`+fork+exec, drains master → `Record::Out`, unsafe cordoned | **BUILT** `term.pty.records-and-replays` |
| N children driven by one orchestrator | 3 heterogeneous children, each its own partition, independently resumable | **BUILT** `term.fleet.orchestrate-n` |

That is most of the pipe, already green. What is **not** there is discussed in §5.

---

## 3. Architecture

The pipe is **one astream session log per target**, three subject subtrees, and
three actors. It never invents a remote protocol — it gives an existing local one
(aterm-ctl's four-verb shape) a durable, cursored, cross-machine transport.

### 3.1 Subject taxonomy (adopted verbatim from the lash design)

Per `DESIGN-aterm-lash.md §1` and `DESIGN-astream-term.md §4`, using
whole-segment subjects only (astream forbids partial-segment wildcards):

| Subject | Direction | Carries | aterm-ctl equivalent |
|---|---|---|---|
| `/a/stream/term/<sid>/in` | driver → target | keystrokes as `In{bytes,client_id,client_seq}` | `key` `send` `paste` `resize` `mouse` |
| `/a/stream/term/<sid>/out` | target → driver | PTY bytes as `Out(..)` — the flight recorder | engine change-stream + `text`/`screen`/`cell` |
| `/a/state/term/<sid>/screen` | snapshot | a materialized fold carrying `folded_through` offset | `screen` / `image` |
| `/a/inbox/term/<sid>/ctl` | driver → target | out-of-band control (`resize`, `tab`, detach) | `modes` `resize` `tab` `off` |

A driver **observes** with `SUBSCRIBE(Filter = /a/stream/term/<sid>/>, from_offset)`
and **drives** by publishing `In` records to `…/in`. A fresh or reattaching client
paints `…/state/screen` (O(viewport)) then folds only the tail after `folded_through`
— an agent reconstructs the current screen in **O(tail)**, not O(full history).

### 3.2 The three actors and the data flow

```
   TARGET (machine 1)                 astream broker              DRIVER (machine 2)
 ┌────────────────────┐            ┌──────────────────┐        ┌─────────────────────┐
 │ aterm + <program>  │  Out recs  │  one offset log  │  tail  │  ▟ PUMP (resident)   │
 │  claude/codex/…    │──lash────▶ │  /…/out  ───────────────▶ │  fold→frame_hash→    │
 │  a real PTY        │            │  (gap-free Offset,│ (push, │  semantic events     │
 │                    │ ◀──lash────│   durable, EOS)   │  no    │        │ wake        │
 │                    │  In recs   │  /…/in   ◀───────────poll) │        ▼             │
 └────────────────────┘            │  /…/state         │  drive │  Claude Code agent   │
        ▲  human can seize         └──────────────────┘  (EOS)  │  (turn-based)        │
        │  the keyboard (ControlToken)                          └─────────────────────┘
```

- **The target + the lash (a frontend/embedder — §4).** aterm runs `<program>` on
  a real PTY. The lash drains the engine's change-stream into `Out` records on the
  log and applies inbound `In` records to the PTY. *Design target:* exactly-once
  by `(client_id, client_seq)`. *Built today (HAND-RUN, aterm
  `tools/aterm-astream-bridge`):* a live-only mirror — `/out` is published from
  aterm's live byte stream (`asb pub`, dedup by producer seq) and `/in` is fed
  at-most-once per delivery (`feed-bin`, no retry) with no `(client_id,
  client_seq)` on the record.
- **The broker.** One single-writer partition per session. It is the pipe: durable,
  gap-free, exactly-once, resumable, forkable, servable over TCP.
- **The pump (resident, non-turn-based — §5).** Holds a broker SUBSCRIBE on
  `…/out` (from a client-held offset, or off a broker-durable consumer-group
  cursor — `Pump::attach_group`; and on any subject, not only the built face),
  folds each record, debounces on `frame_hash`, classifies **semantic events**
  (prompt-ready / command-start / command-end / quiesced) per program profile, and
  surfaces a **wake** only on a meaningful boundary (as returned events / printed
  wake lines; the hook that re-enters the agent is DESIGNED).
- **The driver (turn-based).** On wake, reads `…/state` + tail, decides, and drives
  `…/in` with a stable `(client_id, client_seq)`. Reviews against ground truth. A
  human can seize control at any time via `ControlToken` (enforced at the engine's
  token-taking ingest; the `astream-host` `Driver` is not yet routed through it).

---

## 4. Component 1 — the lash (`aterm-link`, a frontend crate) — **DESIGNED** (the crate now exists aterm-side as the fabric bridge, `DESIGN-aterm-fabric.md` §11.2, but its `lash` verb is refused by name); **HAND-RUN** as two aterm-side scripts (`tools/aterm-link`, `tools/aterm-astream-bridge`; no claim in either repo)

`DESIGN-aterm-lash.md`'s core claim, which the grounding confirmed against the real
verb table (`aterm-types/src/control_verbs.rs`): **aterm-ctl is already the lash
protocol.** The drive verbs (`key`/`send`/`turn`/`resize`/…, `OpClass::Write`), the
observe verbs (`text`/`screen`/`cell`/`subscribe`, `Read`), and the block-until
verbs (`await`/`turn`/`wait`) already exist locally. Lashing = **routing those verbs
between engines over astream's wire, cursored by Offset.**

**Where it must live (a hard constraint).** aterm's canonical rule
(`ATERM_DESIGN.md §2`, grep-enforced): the engine owns **zero** I/O. A network link
is I/O. And astream's doctrine forbids a ~40-crate dependency entering its
zero-dep/reproducible-build tree. Therefore the lash is a **third crate, a
frontend/embedder** — not aterm-core, not the astream substrate. It:

1. embeds/connects an aterm engine over the existing control socket,
2. frames aterm-ctl messages as `astream_wire::Frame`s,
3. addresses them with `Subject`, and
4. cursors them with `Offset` — mapping aterm's ty-model-checked `seq==count` spine
   (`aterm-spec/src/derive/models_session.rs`) onto astream's checked `Offset`
   (`astream-wire/src/offset.rs`), which is the *same invariant* on both sides.

**Cheapest first proof — MVP-0 (HAND-RUN — aterm `tools/aterm-link`; the plan is
`DESIGN-aterm-lash.md` §6):** a local `aterm-link` relay mirroring one aterm into
another over the existing ctl sockets (host PTY→viewer render; viewer keys→host).
Same machine, same uid, **no security needed** — the falsifiable seed that the
four-verb routing works before any Offset/broker/cross-machine layer is added. It
has been run by hand; no test asserts it.

**Output representation — a real choice.** Three options, honestly:
- Raw VT `Out` bytes (**BUILT** flight recorder) — correct, but a cross-machine
  viewer must re-fold with a *matching* terminfo or it diverges.
- aterm's lossless styled **`cells`** JSON DELTA (**BUILT**, `subscribe.rs:93-96`) —
  styled, unambiguous, heavier.
- astream-term's **normalized screen-ops** (**DESIGNED**) — a derived view that
  *structurally* kills two-party terminfo disagreement.

Recommendation: carry raw `Out` as the durable truth (cheap, replayable) and derive
`cells`/screen-ops for cross-machine viewers so no one re-parses VT against the wrong
terminfo.

---

## 5. Component 2 — the pump — **the net-new, load-bearing piece** — **BUILT** (`astream-pump`: `Pump::next_wake` / `quiesce`, `aspump`; `term.perceive.semantic-events`, `pump.wake-on-boundaries`, `pump.cli.wake-lines`, `pump.attach-subject-and-group`) with one part still **DESIGNED** (agent-hook wake)

Every grounding area converged on the same conclusion: **astream deliberately stops
at a socket that blocks until an event; the entity that blocks is a *thread*, not an
agent turn.** There is no webhook, no exec-on-record, no notification egress —
"emphatically not agent behaviour" is astream's own framing. So the pump was ours to
build, and it was the highest-risk, highest-value component. The loop below is the
design; each step is tagged with what `crates/astream-pump` does today.

The pump is a **small resident process** (co-located with the target, or anywhere it
can reach the broker) that owns the block-forever end of the pipe so the agent
doesn't have to. Its loop:

1. **Hold the pipe open.** *Built:* `Pump::attach` / `Pump::attach_subject` do
   `client.subscribe(from_offset, subject)` — the built face
   `/a/stream/term/<sid>/out` or **any** subject, so a fabric node's
   `/f/<F>/term/<node>/<sid>/out` pumps through the same code — and `aspump` the
   same with `--subject` and `--from N` (default 0): a **client-held cursor**, so
   the read position lives in the pump process and dies with it (a restarted
   `aspump` from 0 replays the whole session and re-prints every historical wake).
   `recv()` blocks on the Condvar tail — the no-poll push wait (Constraint 1
   solved). *Also built:* `Pump::attach_group(client, commits, group, subject, …)`
   does `client.subscribe_group(group, subject)` and `Pump::commit()` after each
   acted-on wake — a **durable consumer group** so the read position lives on the
   broker and survives a pump restart, with the replacement pump handed no offset
   at all (`aspump --group G`; `pump.attach-subject-and-group`). It takes a second
   connection, because a group subscription's own connection is one-way. The
   commit is *after* the wake is acted on, so the guarantee is at-least-once: a
   pump killed between a delivery and its commit re-delivers that record.
2. **Fold + coalesce.** Keep an `astream-term::Folder`; apply each `Out` record;
   compute `frame_hash(folder.screen())`. Emit nothing while the hash churns; a
   burst of byte-deltas collapses to *one* "screen settled at offset K" — the
   frame_hash-unchanged flag is astream's built quiescence primitive.
3. **Classify semantic events.** *Built:* `astream-term::events`
   (`term.perceive.semantic-events`) emits prompt-ready / command-start /
   command-end(+exit) from OSC-133/633 marks, and `Quiesced` at the `frame_hash`
   settle point. A glyph `Profile` is the fallback for a target with no shell
   integration, and it is consulted **only while the session has shown no OSC mark
   at all** — once any mark arrives, the marks own prompt-ready, so a glyph can never
   contradict a command that is still running:
   - Claude Code → the `❯` idle box (`Profile::common()`); a spinner keeps
     `frame_hash` churning, so the glyph is only read once the screen has settled —
     there is no separate spinner predicate;
   - Codex → `»` composer (visible even while working, so its wake is `Quiesced`;
     `»` is deliberately **not** a marker);
   - a REPL → `>>>` at the end of the last non-empty line (no column-0 check); a
     shell → the OSC-133 `A` mark, or `$`/`%`/`#` when it emits no marks. Honest
     residual: on a non-integrated target those three characters also end many
     ordinary output lines, so a settled progress line can read as a prompt.
4. **Wake the driver** (Constraint 2 — the "update hooks and such"). *Built:* the
   pump returns the wake events (`Pump::next_wake` / `quiesce`) and `aspump` prints
   them as `PROMPT_READY boffset=K` lines, each tagged with the broker `/out` offset
   the woken agent resumes its fold from. *Designed (none of these exist):* on a
   qualifying event, convert bus activity into an agent turn by one of:
   - a **Claude Code hook** (a `Notification`/`Stop`-class hook the pump fires), so
     the driver re-enters its loop on an A-side event instead of spinning;
   - **relaunch/`--resume`** a `claude -p` turn with the event + the `…/state` offset;
   - **post to a task queue** the driver drains at the top of each turn.
   The wake payload is small: `{event, offset K, sid}` — the driver pulls the screen
   at K on wake, so the pump never ships full frames into the agent's context.

**Why durable-group, not client cursor (BUILT — `pump.attach-subject-and-group`):**
a turn-based driver restarts constantly. A broker-committed offset means a
freshly-woken turn resumes from `commit+1` — gapless, and never re-delivered
anything the previous pump committed — even though the pump itself bounced.
(Constraint 2, made robust.) The client-cursor form remains, and with it the
old hazard: a restarted pump must be given `--from` explicitly, and getting it
wrong misses or duplicates boundaries. The honest residual on the group form is
that it is at-least-once, not exactly-once: the delivery whose commit was still
in flight when the pump died comes back.

**Design question, resolved by the build:** the pump is a broker **consumer**
(durable, replayable, cross-machine — `astream-pump` consumes the bus through the
ordinary `Client`), not an in-`aterm-link` embedder thread. That is the form that
makes the wake survive everything, and with the durable-group cursor now built it
survives the pump's own death too.

---

## 6. Component 3 — the driver, and the properties you buy

The driver is an ordinary Claude Code agent that, on wake:

1. reads `…/state/screen` at offset K plus the tail fold — **O(tail)** to current
   screen (`term.resume.gapless-exactly-once`);
2. reviews against **ground truth**, not the screen's self-report (the lesson from
   the live runs: a worker's "all tests pass" is not evidence);
3. drives `…/in` with a stable `(client_id, client_seq)` — a keystroke re-sent after
   a drop is applied **at most once** (`term.drive.interactive-exactly-once`);
4. yields to a human instantly: `ControlToken` makes exactly one writer authoritative
   at the engine's token-taking ingest (`Session::apply_input_as`; the host `Driver`
   still calls the untokened `apply_input` — a host-crate follow-up)
   and the handoff auditable (`term.fleet.control-handoff`) — the "human always wins"
   rule, now a first-class, replayable property instead of a convention.

Properties the pipe has that raw `aterm-ctl subscribe` does **not**:

- **Exactly-once drive** — no double-typed command across a flaky link.
- **Resume after disconnect / sleep / roam** — reopen, resume from offset; an IP
  change is identical to a drop.
- **Replay & scrub-back** — re-derive any past screen byte-identically; freeze any
  moment as a regression test (Session rung, In+Out).
- **Counterfactual fork** — `ForkSubscribe` previews an alternate timeline in a
  sandbox while the live session is provably untouched (offline "what did the screen
  do if…", *not* a live re-drive — see risks).
- **Multi-subscriber** — many agents/humans watch one target, none disagreeing.
- **A durable audit log** — every keystroke and screen the agent drove, replayable.
- **Cross-machine** — the same, over TCP.

---

## 7. Cross-machine — the powerful part, honestly bounded

The same exactly-once pub/sub + resume protocol rides `serve_tcp` **today**
(`broker.tcp-transport`), and durable replication (leader→follower quorum) rides TCP
too (`broker.replicated-tier`). One orchestrator driving N remote terminals — each a
real PTY running claude/codex/emacs, each its own partition, each independently
resumable and perceivable — is the fleet vision of astream's own `GOAL.md`,
and its constituent claims (`term.fleet.orchestrate-n`, `.control-handoff`,
`term.drive.interactive-exactly-once`) are **BUILT** at N=3.

**But the wire is the boundary, and the doc must say so plainly:**

- **BUILT (opt-in) — an AEAD wire now exists.** Frame CRC32 is
  integrity-against-corruption, **not a MAC** — so plaintext `--tcp` still lets an
  active MITM **inject keystrokes** or tamper with output, and remains the default.
  But the sealed transport (`broker.serve_tcp_sealed` / `Client::connect_tcp_sealed`,
  the `aead` feature) wraps the SAME Frame protocol in an **XChaCha20-Poly1305**
  `SealedStream` under a pre-shared key: confidential and authenticated, each
  record's AAD `hello_client ‖ hello_server ‖ direction ‖ seq` — the two 32-byte
  CSPRNG hellos the connection opens with — so an injected, reordered, dropped or
  replayed record fails its tag, and a record captured from ANOTHER connection (or
  reflected back down the other direction) fails it too
  (`aead.seal-open.authenticated`, `broker.sealed-tcp-roundtrip`). The primitive is
  the vetted RustCrypto AEAD, never hand-rolled. The CLI face is
  `asb --key-env NAME` / `--key-file PATH` (a bare `--key HEX` on argv is refused
  so the PSK never shows in `ps`), exercised by `broker.cli.tcp-roundtrip`.
  The hellos give freshness and key confirmation over a bare PSK; the key agreement
  that adds forward secrecy is the next bullet.
- **BUILT (opt-in) — forward secrecy via an online handshake.** On top of the PSK
  wire, the `handshake` feature (`broker.serve_tcp_handshake` /
  `Client::connect_tcp_handshake`; `asb --key … --handshake`) runs an ephemeral
  **X25519** key agreement authenticated by the PSK (the NNpsk pattern), deriving a
  FRESH per-session key so a later PSK compromise cannot decrypt past traffic
  (`aead.handshake.forward-secret-key-agreement`, `broker.handshake-tcp-roundtrip`).
  It reuses the record layer above: instead of the hello exchange, the AAD binds the
  handshake's own TRANSCRIPT (`ec_pub ‖ es_pub ‖ direction ‖ seq`), which is what the
  session key already derives from — so cross-session and cross-direction replay fail
  with no extra round trip.
  We own the protocol + HMAC/HKDF-SHA256 (RFC 4231/5869 vectors); only the raw
  curve scalar-mult is the vetted `x25519-dalek`.
- **BUILT (opt-in) — static public-key identity, NO shared secret.** The `identity`
  feature (`serve_tcp_identity` / `connect_tcp_identity`) runs a mutual signed-DH
  (SIGMA / Ed25519) handshake: the client pins the broker's host key and the broker
  allow-lists the client's identity, authenticating with long-term keypairs instead
  of any shared secret (`aead.identity.mutual-signed-dh`,
  `broker.identity-tcp-roundtrip`). The identity keys ONLY sign the ephemeral
  transcript, so forward secrecy survives even an identity-key compromise. We own the
  SIGMA protocol; only the raw Ed25519 sign/verify is the vetted `ed25519-dalek`.
  Because both peers SIGN that transcript and the record layer BINDS it, an
  authenticated session's records cannot be lifted into any other session.
  Encrypt-at-rest is **BUILT** too (below).
- **BUILT (opt-in) — the mint is enforced on attach.** The unforgeable capability
  mint is **BUILT** (`cap.unforgeable-mint`, `wire.filter.containment`) — a signed
  `Filter` scopes a bearer to exactly `/a/stream/term/<sid>/>` and `…/inbox/<sid>`
  and nothing else — and a broker opened with `Broker::open_guarded` (the `cap`
  feature) refuses any publish, subscribe or group commit outside the presented
  capability's grant (`broker.cap-enforced-on-attach`). Without the feature (the
  default build, and plain `asb serve`), *reachability equals access*. Scope of the
  shell faces under enforcement: `asb` can present one, but only out of a FILE
  (`--cap-file PATH`, repeatable, `<grant> <tag-hex>` lines -> `Client::attach`,
  covered by `broker.cli.pub-sub-roundtrip` and `broker.cli.fleet-verbs`;
  `--cap-filter`/`--cap-tag` on argv are refused with exit 2, because a tag is a
  secret and argv is world-readable), so a bridge patch must pass a cap FILE
  through, not those flags; `aspump` cannot — against a guarded broker its
  subscription is refused and it exits 1 with the broker's reason. A grant can also
  carry an expiry, checked per request (`cap.expiry-enforced`); revoking one before
  its deadline, short of rotating the secret, is not built.
- **BUILT (opt-in) — encrypt-at-rest.** The durable log records every keystroke and
  screen, forever unless compacted: a forensic target. `Broker::open_encrypted` (the
  `at-rest` feature) seals each record's payload on disk with XChaCha20-Poly1305
  (random nonce, log-index AAD), so a disk reader recovers nothing without the key,
  and a wrong key or a tampered/corrupt record is refused (a Corrupt tail), never
  silently discarded (`broker.log-encrypted-at-rest`). Honest boundary: it hides
  content, not structure (sizes/counts), and on its own a write-capable attacker
  could still tail-truncate the log undetectably;
  the optional `anti-rollback` feature (`Broker::open_encrypted_verified`) closes that
  with an authenticated monotonic head watermark in a `<log>.hw` sidecar, refusing a
  log rolled back below it (`broker.log-anti-rollback`) — defeating a key-less
  attacker, though not one who can restore an older on-disk snapshot (that needs a
  hardware-monotonic counter). Retention (`Broker::retain_before`, the `retention`
  feature, `broker.log-retention`) compacts the log below an offset floor, keeping
  surviving offsets absolute.

**Therefore cross-machine drive over an untrusted network is now possible** with the
sealed transport plus mint enforcement, on a pre-shared key: the wire is confidential
and authenticated (with forward secrecy when the handshake is used), and the mint
scopes each bearer to its own subtree. Authentication now spans the full range: a
pre-shared key (Rungs 6/7) OR static public-key identities with no shared secret at
all (Rung 8, SSH-like — the client pins the host key, the broker allow-lists the
client). The in-flight and at-rest ladder is BUILT — including an optional
anti-rollback watermark (`broker.log-anti-rollback`) and log retention
(`broker.log-retention`) — so it is no longer the hard blocker; what it still lacks
is identity bound to an external authority and the key operations around it. A
trusted link (localhost, LAN/VPN, WireGuard, `ssh -L`) is still the simplest
deployment, but no longer the *only* safe one.

---

## 8. Status ledger (respecting astream's honesty gate)

| Capability | Status | Evidence |
|---|---|---|
| Session-as-offset-log; byte-identical replay | **BUILT** | `term.replay.byte-identical` |
| Perceive (text/blocks/search) + render (image/animation) at any offset | **BUILT** | `term.perceive.query`, `.render-deterministic` |
| Exactly-once drive `(client_id,client_seq)` | **BUILT** | `term.drive.interactive-exactly-once` |
| Durable exactly-once pub/sub + offset resume; Condvar push | **BUILT** | `broker.exactly-once-pubsub-resume`, `.true-exactly-once-e2e` |
| Real PTY host (`posix_openpt` on Linux / `openpty` elsewhere, + fork + exec), unsafe cordoned | **BUILT** | `term.pty.records-and-replays` |
| N-child orchestration + single-writer control handoff | **BUILT** | `term.fleet.orchestrate-n`, `.control-handoff` |
| Cross-machine transport (TCP) + durable replication | **BUILT** | `broker.tcp-transport`, `broker.replicated-tier` |
| Unforgeable capability mint (signed Filter) | **BUILT** | `cap.unforgeable-mint` |
| Bus + pump **shell faces** (`asb` serve/pub/sub, `aspump` wake lines) | **BUILT** | `broker.cli.pub-sub-roundtrip`, `pump.cli.wake-lines` |
| Cross-machine bus over **TCP** (CLI) | **BUILT** | `broker.cli.tcp-roundtrip` (trusted network) |
| Counterfactual fork-delivery (offline sandbox) | **BUILT** | `broker.agent-native-fork-and-cognition` |
| **The lash** (`tools/aterm-link` mirror + `tools/aterm-astream-bridge`, aterm-side) | **HAND-RUN** (no claim) | aterm `tools/aterm-link`, `tools/aterm-astream-bridge`: a live-only mirror onto the bus over `aterm-ctl` + `asb` on a Unix socket (`/out` from aterm's live bytes, so output emitted while the bridge is down never reaches the bus and each incarnation is a fresh producer; `/in` fed at-most-once per delivery, no `(client_id, client_seq)`). Run by hand; no test in either repo runs it |
| Normalized screen-op cross-machine projection | **DESIGNED** | `DESIGN-astream-term.md §4` |
| **The pump** (fold→frame_hash→semantic events→agent wake) | **BUILT** (client-cursor *or* broker-durable-group subscribe, on any subject; wake = returned events / `aspump` lines) | `pump.wake-on-boundaries`, `pump.attach-subject-and-group` (crate `astream-pump`); agent-hook wake **DESIGNED** (§5) |
| Per-program semantic-event profiles (prompt-ready / command-start / command-end / quiesced; the glyph profile is off once a session shows any OSC mark) | **BUILT** | `term.perceive.semantic-events` (OSC-133/633 + glyph profile + frame_hash quiescence; batch == streaming over fixtures, an ST session split at every byte boundary, and proptest sessions) |
| Mint **enforced on broker accept path** | **BUILT (opt-in)** | `broker.cap-enforced-on-attach` (`cap` feature) |
| Capability expiry (not revocation) | **BUILT (opt-in)** | `cap.expiry-enforced` (`cap` feature) |
| Filter-containment ACL primitive (`Filter::contains`, `grants_filter`) | **BUILT** | `wire.filter.containment` |
| **AEAD on the wire** (untrusted-network safety) | **BUILT (opt-in)** | `aead.seal-open.authenticated`, `broker.sealed-tcp-roundtrip` (`aead` feature) |
| Online key-agreement handshake (forward secrecy) | **BUILT (opt-in)** | `aead.handshake.forward-secret-key-agreement`, `broker.handshake-tcp-roundtrip` (`handshake` feature) |
| Static public-key identity (auth without a shared secret) | **BUILT (opt-in)** | `aead.identity.mutual-signed-dh`, `broker.identity-tcp-roundtrip` (`identity` feature) |
| Encrypt-at-rest for the durable log | **BUILT (opt-in)** | `broker.log-encrypted-at-rest` (`at-rest` feature) |
| Log-level anti-rollback (authenticated head watermark) | **BUILT (opt-in)** | `broker.log-anti-rollback` (`anti-rollback` feature) |
| Retention (bounded log, absolute offsets) | **BUILT (opt-in)** | `broker.log-retention` (`retention` feature) |
| End-to-end "aterm-over-broker driven by a remote agent" | **BUILT (astream half) + HAND-RUN (aterm half); no single claim** | `pump.wake-on-boundaries` proves broker→classify→wake over a scripted session; the aterm bridge has been run by hand against the bus. Nothing re-runnable asserts the composition (§10) |

---

## 9. Build ladder — each rung a falsifiable increment

Following astream's rule (nothing claimed without a green re-runnable command):

1. **MVP-0 — local mirror (HAND-RUN — aterm `tools/aterm-link`; no test).** `aterm-link` relays one aterm into another
   over existing ctl sockets, same machine/uid, no security. *Claim (untested):* keystrokes in
   viewer reach host PTY; host render appears in viewer. Proves the four-verb routing.
2. **Rung 1 — onto the bus (PARTIAL, HAND-RUN — aterm `tools/aterm-astream-bridge`; no test).** Put `Out`/`In` on one astream partition;
   drive exactly-once by `(client_id,client_seq)`; resume `…/out` from offset after a
   forced disconnect with no gap/dup. *Target claim:* kill the client mid-session,
   reattach, miss nothing. *What the bridge does today:* a **live-only mirror** — `/out`
   is `asb pub` of aterm's live `subscribe bytes` (output emitted while the bridge is
   down is never on the bus; each incarnation is a fresh random producer id, so
   there is no `/out` resume), and `/in` is raw bytes fed **at-most-once** per delivery
   (`feed-bin`, no retry) with no `(client_id, client_seq)`; it speaks only a Unix
   socket broker endpoint. The exactly-once/resume properties are BUILT in the
   substrate (`term.drive.interactive-exactly-once`, `broker.exactly-once-pubsub-resume`)
   but the bridge does not yet use them, and no test runs the bridge. *Two hazards
   an audit of the bridge found, both still open in `~/aterm`:* its `/in` subscribe
   passes no `--from` and no group, so the broker replays the **whole** keystroke
   history into the PTY on every restart; and an aterm `GAP` frame (PTY bytes
   dropped because the bridge fell behind) is silently discarded, so `/out` loses
   bytes with no marker on the bus. astream now ships the faces that fix both —
   `asb sub --group` + `asb commit` for a durable, per-record-committed `/in`, and a
   `/gap` discontinuity record — and a proposed bridge patch using them is written
   but unapplied (this repo does not edit `~/aterm`).
3. **Rung 2 — the pump + program profiles (BUILT: the classifier + pump + CLI + the durable-group cursor — `astream-pump`, `term.perceive.semantic-events`, `pump.wake-on-boundaries`, `pump.cli.wake-lines`, `pump.attach-subject-and-group`; DESIGNED: agent-hook wake, nested-Claude-Code end-to-end).** Resident pump: a plain offset
   `subscribe` or a broker-durable group cursor, frame_hash debounce, OSC-133/glyph
   prompt-ready classifier (Claude Code / Codex / REPL / shell profiles), wake as
   returned events or `aspump` wake lines (a Claude Code hook DESIGNED). *Claim
   (green, scoped):* over a scripted session on a live in-process broker the pump wakes
   only on the semantic boundaries. *Target claim (no green command):* drive a real
   nested Claude Code end-to-end, the agent waking only on turn boundaries, zero polling.
4. **Rung 3 — a second program (DESIGNED).** Add a REPL or emacs profile. *Claim:*
   the same pump drives a non-agent program; proves "any program."
5. **Rung 4 — cross-machine on a trusted link (BUILT via CLI — `broker.cli.tcp-roundtrip`; `asb --tcp`).** `serve_tcp` over
   localhost/VPN; scope the driver with a `cap` Filter. *Claim:* orchestrator on box A
   drives a worker on box B over the tunnel, exactly-once, resuming across a link drop.
6. **Rung 5 — enforce the mint on attach (BUILT — `broker.cap-enforced-on-attach`).** Broker checks the signed
   Filter on the accept path. *Claim:* an unscoped attach is refused.
7. **Rung 6 — AEAD wire (BUILT — `aead.seal-open.authenticated`, `broker.sealed-tcp-roundtrip`).**
   XChaCha20-Poly1305 `SealedStream` over a pre-shared key, wired into the broker's
   TCP transport (`serve_tcp_sealed` / `connect_tcp_sealed`,
   `asb --key-env`/`--key-file`); a tampered/injected/reordered record fails its
   tag, a record replayed from another connection or direction fails it too, and a
   wrong-key peer is refused inside the handshake.
8. **Rung 7 — forward-secret handshake (BUILT — `aead.handshake.forward-secret-key-agreement`, `broker.handshake-tcp-roundtrip`).**
   An ephemeral-X25519 key agreement authenticated by the PSK (NNpsk), wired in as
   `serve_tcp_handshake` / `connect_tcp_handshake` (`asb --key … --handshake`); each
   session gets a fresh key, so a later PSK compromise cannot decrypt past traffic. We
   own the protocol + HMAC/HKDF (RFC vectors); only the curve is delegated. The record
   layer binds the handshake transcript rather than a hello exchange, so the freshness
   the sealed wire gets from its hellos comes here from the agreement itself.
9. **Rung 8 — static public-key identity (BUILT — `aead.identity.mutual-signed-dh`, `broker.identity-tcp-roundtrip`).**
   Mutual signed-DH (SIGMA / Ed25519): the client pins the broker's host key, the
   broker allow-lists the client's identity — authentication with NO shared secret
   (`serve_tcp_identity` / `connect_tcp_identity`). Identity keys only sign, so forward
   secrecy survives their compromise. We own the SIGMA protocol; only Ed25519
   sign/verify is delegated. Encrypt-at-rest for the durable log is BUILT too (`broker.log-encrypted-at-rest`).
10. **Fleet — N remote workers (BUILT substrate).** One orchestrator, many remote
    PTYs, consistent-cut checkpoint. The vision.

---

## 10. Risks & open questions

- **The pump's semantic profiles are the accuracy bottleneck.** Idle-waiting and
  mid-compute both hold a stable `frame_hash`; without a per-program prompt marker the
  pump can't tell "ready for me" from "still thinking." Getting a profile wrong wakes
  the driver early (waste) or never (stall). This is the same trap the live drive runs
  hit; it is real work, not a footnote.
- **Fork is offline, not a live what-if.** `ForkSubscribe` replays *recorded*
  divergence in a sandbox; it does **not** re-run claude/emacs against swapped input.
  Do not sell it as live speculative driving.
- **Composition is unproven.** Every constituent claim is green; "aterm-over-broker
  driven by a remote agent" as one green claim does not exist yet — the aterm bridge
  is a hand-run script with no test, and its `/out` is live-only. Rung 1's target
  properties (resume, exactly-once drive) and a nested-Claude-Code end-to-end are
  where it becomes real.
- **seq domains don't interchange.** aterm's `subscribe seq=` is a per-session
  content_seq (no bump on pure scroll/cursor moves); astream's `Offset` is a
  per-partition log position; astream-term's `in_watermark` is another axis. The lash
  must pick one authoritative axis (the astream `Offset`) and derive the rest.
- **Fold fidelity is a bounded xterm subset** (DECSTBM and bce are folded —
  `term.fold.scroll-region`, `term.fold.bce`; no graphemes/truecolour in the in-tree
  fold). Match on text/blocks/search, not exact cell colour; pixel-true perception
  needs the external aterm engine (out-of-tree, by doctrine).
- **The durable log is a secrets store.** Every keystroke typed into A lives on it.
  Scope capabilities tightly; **encrypt-at-rest is BUILT**, opt-in (`Broker::open_encrypted`).
- **Wake latency/cost.** Relaunching an agent turn per event is expensive; the pump
  must debounce aggressively (frame_hash + prompt boundary), or the driver thrashes.

---

## 11. The one-paragraph version

Make each target session **one astream offset log** (`In`/`Out`/`state`), lashed from
aterm through a frontend `aterm-link` crate (the crate exists aterm-side as the fabric
bridge; the lash itself is today a hand-run live-only bridge script). A resident **pump** holds the broker's no-poll SUBSCRIBE on `…/out`
(client-held cursor, or a broker-durable group cursor, on any subject), folds it, debounces on
`frame_hash`, classifies per-program semantic events, and **wakes** the turn-based
driver only on a real boundary — the missing bridge from a block-forever bus to an
agent that stops between turns. The driver reads the screen at an offset, reviews
ground truth, and drives `…/in` exactly-once, yielding to a human via the control
token. The substrate below the pump and the lash is **BUILT** in astream today, and
so are the pump's classifier and CLI; with the **AEAD wire** and **mint enforcement**
both **BUILT (opt-in)**, cross-machine drive over an untrusted network on a
pre-shared key is now a library-level capability — and above it a forward-secret
X25519 agreement and mutual static public-key identity that needs no shared secret
at all. The fleet is unlocked in the substrate; encrypt-at-rest for the durable log is BUILT
too (`broker.log-encrypted-at-rest`), and so is the pump's durable-group cursor
(`pump.attach-subject-and-group`); the remaining increments are the lash's
resume/exactly-once and the hook wake.
