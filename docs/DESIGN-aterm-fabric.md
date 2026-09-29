# DESIGN: the aterm fabric — cross-aterm broadcast and messaging on astream

**The fabric** is how many **aterm** instances — on one machine and across machines,
each hosting sessions that may be a human, a Claude Code or Codex agent, a shell, or
a TUI — talk to each other over **astream**: **broadcast** (fleet-wide halts and
notices, presence, attention fan-out, acknowledged barriers) and **messaging**
(agent↔agent ask/answer, orchestrator↔worker task/report, a human answering from
another host, handoff and drive-with-consent), *managed*: discoverable, permissioned,
auditable, replayable, resumable, exactly-once where it matters, and
human-always-wins. astream is the transport and the log; aterm is the endpoint and
the UX.

This is the synthesis of five judged proposals, revised once after adversarial review
(doctrine, security, agent-UX). Its skeleton is the top-ranked "Fleet Faces"
(protocol-minimal) design; the best ideas the judges named in the other four are
grafted in, and every contradiction is resolved in the open (§0.1). Both repos'
disciplines are kept whole: substrate crates stay zero-third-party — the two vetted
crypto dependencies live only behind `astream-cap`/`astream-aead` — and
`forbid(unsafe)`; aterm's engine owns zero I/O (a link is a frontend/embedder crate);
authority is exercised one hop at a time and never borrowed transitively; screen
content is data, never instructions.

Status discipline follows `docs/DESIGN-drive-pipe.md`: every capability is tagged
**BUILT** (a green re-runnable claim runs it today — cited by claim id and
`file:line`) / **DESIGNED** (specified, no claim yet) / **SEED** (a precise falsifiable
command would make it real) / **HAND-RUN** (an out-of-tree script exercised by hand
against the built bus, with *no test in either repo* running it — the tag
`DESIGN-drive-pipe.md:24-28` defines) / **RED** (a blocker). astream citations are against
`fabric/integration` commit `d2b70ef` (the round-3 fix pass); aterm citations are against
aterm branch `fabric/a1-a2` commit `a3936e5f2`, which carries rungs A1–A10 and the two
adversarial audit rounds after them. Every astream `BUILT` cites a manifest claim; aterm
has **no claim ledger** (no `evidence/` directory), so **BUILT (aterm)** means *test-cited,
not manifest-cited*: each such row names the test and the command that runs it.

> **Citations are pinned, not maintained.** Every `file.rs:NNN` and bare `:NNN` citation
> below refers to the commits just named — astream `d2b70ef`, aterm `a3936e5f2` — and is
> kept there. They were not re-resolved when this document was last revised (astream
> `d61e73e`, by which time `store.rs` and `broker.rs` had already moved), and they will
> not be updated as the code changes. Status lives in `evidence/manifest.toml`; a
> citation is a snapshot, re-found by the symbol named beside it.

**Every citation below — astream and aterm, file-qualified and bare `:<line>` alike — was
re-resolved on 2026-08-31 by printing the cited line and comparing it against the symbol
or claim named beside it.** All 467 that this document carried were checked; 298 were
renumbered — 239 of the 358 astream ones (the round-3 pass moved `store.rs` by ~350 lines
and `asb.rs` by ~240) and 59 of the 109 aterm ones. The document now carries 481, and every
one of them resolves inside its file at the commit named above. The two targets are COMMITS
and not "the working tree" on purpose: astream's tree above `d2b70ef`
carries an unrelated in-progress feature, and the aterm worktree moved twice while this was
written, so a number resolved against an unnameable tree is not a citation. The check is
mechanical and anyone can re-run it:
`git show d2b70ef:crates/astream-broker/src/store.rs | sed -n '939p'`, and
`git -C <aterm> show a3936e5f2:aterm-link/src/bridge.rs | sed -n '2605p'`.

**A line number here is a snapshot; the symbol name beside it is the identity.** Where a
line moves easily the symbol is named (`store.rs:939 stage_publish`), and a `grep -n` for
that name is the repair once the number has drifted — which it will, at the next commit
that touches the file. Three earlier passes asserted a line-by-line re-resolution without
doing one, so: a citation that does not land **against the commit named above** is a defect
to fix; one that does not land against a later HEAD is drift, and the symbol name is how you
re-find it.

**What this pass could NOT check.** Two citations name a range whose interior was rewritten
between the commit the number was taken from and the commit it now names
(`crates/aterm-types/src/env_sanitize.rs:127-186`,
`crates/aterm-ctl/src/lib.rs:2771-2777`); both endpoints land on the
construct the text names, but the range is wider than the construct was. Nothing else is
approximate.

---

## 0. The one-paragraph version

Give the fleet a subject tree whose layout is *face first, owner second* —
`/f/<F>/{fleet,pub,in,term,cur}/<owner>/…` — so a capability is one prefix per face
and a message's sender is the subject segment (and the producer id) the capability
forced. Add four request tags and two response tags to the broker — `Last{filter,
after, max}` (the last record per matching subject, paged, then `Mark`), `Fetch{from,
filter, max}` (a bounded, non-terminal read), `Will{…}` (a record the broker appends
when your connection dies, fenced by your own later records and deduped against your
own goodbye), and `Hello` → `Nonce` (so `Attach` is a proof of possession, never a
bearer tag on the wire) — and one change to the capability string (a mode/principal
prefix: read-only grants, and a principal whose producer id the broker derives and
binds, which closes a real dedup-poisoning hole in the built broker). Everything else
is derivation over what astream already has: broadcast is a read-only subtree; a
fleet halt is a retained flag only a human's read-write cap can write, with the human
in the address; presence is `Last` plus a will; a barrier count is `Last` over
`ack/<offset>`; a message is a record on the addressee's lane; a reply cites the
request's offset; an inbox is a durable consumer group drained by one resident bridge
per aterm instance (`aterm-link serve`, a child the instance launches over an
inherited socketpair, so its authority is a connection no token unlocks) into four new
aterm verbs (`inbox`, `post`, `deliver`, `hold`) and one `await` predicate, so a
turn-based Claude Code agent reads its mail with one call at turn start, is woken
through the hooks it already has (metadata only, never a body), and never touches the
bus socket. Every astream rung is a manifest claim with a command; every aterm rung is a
named test with a command, because aterm keeps no claim ledger.

### 0.1 How this document was assembled — grafts and resolved contradictions

| Idea | Source | Verdict | Why |
|---|---|---|---|
| Subject tree with the writer as a fixed segment; `Last`+`Mark`; `Will`; read-only cap mode; keyring; `inbox`/`post`/`deliver`/`hold`; correlation id = offset; one bridge per instance | protocol-minimal | **base** | Ranked first by all three judges |
| **Producer-id binding on the capability** (closes dedup-key poisoning, `store.rs:902 staged_or_durable_dup`, which `stage_publish` (`:939`) reaches through `stage_publish_bounded` at `:953`) | capability-security | **grafted**, revised | The id is now **derived by the broker from a principal named in the grant** (SHA-256, §3.2); the draft's `fnv1a_64` is invertible per byte (`crates/astream-wire/src/hash.rs:7-8`: "not cryptographic") and reopened the hole |
| Read-only mode by HMAC domain separation vs a **grant-string prefix** | protocol-minimal vs agent-ergonomics | **prefix won** | The binding must be visible at attach; `Filter::new` rejects any string not starting with `/` (`subject.rs:150-152`), so a grant can never be mistaken for a filter |
| `Fetch{from, filter, max}`, non-terminal | agent-ergonomics | **grafted** | Every streaming verb ended the connection (`broker.rs:1780,1893` — the `Subscribe` and `SubscribeGroup` arms still `return tail_loop(…)`; `ForkSubscribe` now writes a closing `Mark` and returns, `:1863-1870`) |
| `Last{filter, tail}` | protocol-minimal | **`tail` dropped**; **paging added** | A tail is `Subscribe{from: next}` on the same connection; paging bounds one query (review) |
| Wake through the agent's own hooks | agent-ergonomics | **grafted** (vendor-pinned, §9.1) | Hooks now carry **metadata only**; the `Stop` hook is monotone and budgeted; `PreToolUse` is the real stop |
| Agent speaks to the bus vs only to its aterm socket | agent-ergonomics vs protocol-minimal | **aterm socket won** | Keeps every cap off the agent and astream free of aterm's grammar (`DESIGN-drive-pipe.md:166-171`). Codex's sandbox reaches *neither* socket (T13); its path is the file mirror, A9 |
| Ack = one `ProcessAndProduce` | agent-ergonomics | **grafted** for direct consumers | Sessions behind a bridge use the endpoint watermark |
| Deterministic deadlines as beacon records | determinism-replay | **rejected**; verdicts recorded | A recorded `expired` verdict replays identically with no clock and no steady-state writer |
| Late-joiner equivalence, versioned folds, acknowledged `Attach` | determinism-replay | **grafted** | A rejected `Attach` was invisible until the next request; `Client::attach` now runs the whole `Hello`→`Nonce`→`Attach`→`Mark` round trip and reads the answer (`client.rs:238 attach`) |
| Cross-broker relay + content-addressed cut | determinism-replay | **out of scope** | One broker per fleet is *this design's* decision (§3.3); leader election / follower catch-up-after-rejoin are astream's later track (`docs/DOCTRINE.md:146`) — the replicated (quorum) tier itself is now **BUILT** (`broker.replicated-tier`, §11.1) |
| Epoch in presence rows | capability-security | **grafted**, simplified | The epoch *is* the public launch nonce (`id.rs:49-55`): a freshness fence, not a secret (§7) |
| Macaroon warrants; HELLO/K_conn handshake; broker-stamped principal | capability-security | **deferred**, one piece taken | The **nonce handshake** is taken (`Hello`/`Nonce`, §8.2): a bearer tag inside a stream every host can open is the wrong shape for the halt authority |
| Fabric-as-a-session, `lease holder=fabric:<p>` mirror, misbehaviour table, `glance.json` | human-operator | **grafted** | Engine-free UX; its "downgrade-only" trust label is replaced by a receiver-computed one (§4.3) |
| Central router; PTY-typed wake line; human class = GUI gesture only | human-operator / capability-security | **rejected** | A wide-cap single point of failure; typing into a composer is what the house rule forbids (`OPERATOR.md:221-224`); the core stories need a human away from a GUI |
| A will firing on a transient blip publishes a spurious `gone` | judge finding | **fixed at the broker** | The draft's reader-side fold was unimplementable (`Last` returns one record per subject); the broker fences a will on the producer's high-water sequence (§7) |
| `deliver`/`hold` behind aterm Owner scope | review (all three) | **fixed** | Owner is what an in-session `aterm-ctl` already holds (`crates/aterm-gui/src/control.rs:3975-3977`); the bridge gets a **connection-scoped** authority (`Scope::Bridge`, §11.2) |

---

## 1. The problem, stated precisely

A fleet is many aterm instances, on one machine and across machines, each hosting
sessions that may be a human, a Claude Code or Codex agent, a shell, or a TUI. Today
they cannot talk:

1. **There is no message.** A session can receive only keystrokes on its PTY
   (`turn`/`send`/`feed-bin`, `crates/aterm-types/tests/fixtures/help_catalog_full.txt:37,39,45`)
   or a 256-byte `attention` string on its own record (`:33`). Agent→agent "ask" is
   typing into another agent's composer — what the house rule forbids without the
   human naming session and message (`docs/AGENT-EXPERIENCE-2026-08-26.md:470-472`).
2. **Events are ephemeral, per-connection and lane-bounded.** `subscribe` is push-only
   on one connection (`docs/INTROSPECTION.md:121-124`); the `sessions` roster is a
   512-record in-memory journal (`crates/aterm-gui/src/session_store.rs:406,890`) whose
   push seeds at the journal's high-water mark, so nothing before the subscribe replays
   (`AGENT-EXPERIENCE…md:258-262`); the `exits` ledger dies with the process
   (`help_catalog_full.txt:83`); an instance has 8 control lanes and 4 subscription
   lanes (`crates/aterm-gui/src/control.rs:2195-2196`), answering `ERR control server
   busy; retry` (`:2749`) past them.
3. **Turn-based agents cannot receive.** Claude Code and Codex "think, call tools, and
   stop"; they cannot hold a socket open across turns (`docs/DESIGN-drive-pipe.md:40-43`).
   Their only wait is one parked `await` per instance (`docs/OPERATOR.md:87-90`).
4. **Cross-host is a relay, not a bus.** `dial <name>` relays one connection to a saved
   peer and runs the subsequent verbs there, Owner-only (`help_catalog_full.txt:94`;
   `crates/aterm-gui/src/control.rs:3030-3032`); session connections are explicitly not cross-process or
   cross-machine (`docs/design/SESSION_CONNECTIONS.md:115-119`); the L2.5 fleet fabric
   emits NDJSON addressed by astream subjects but publishes to no broker
   (`crates/aterm-agent/src/fleet_cli.rs:20-32`; `docs/INTROSPECTION.md:730-736`).
5. **astream had the log but no envelope, no last-value, no presence, no bounded read,
   and a capability that authorized both directions at once.** *(This section states the
   problem as it stood before the fabric rungs; `proto.rs` now holds twelve request tags
   (`:14-25`) and five response tags (`:26-30`) — R1, R2, R4, R5 and R11 below.)* The
   broker spoke eight request tags and three responses (the eighth, `TAG_REPLICATE =
   0x08`, `crates/astream-broker/src/proto.rs:21`, is the audit pass's leader→follower
   verb); a `Delivery` is `{offset, subject, body}` (`proto.rs:161-165`); every streaming
   verb returned `tail_loop` and ended the connection (the two arms that still do are
   `Subscribe` and `SubscribeGroup`, `broker.rs:1780,1893`); one connection held one
   capability, replaced on each `Attach` (it is now the append-only keyring,
   `broker.rs:1523`); the same filter authorized publish and subscribe (the split matrix
   is `cap_authorized`, `broker.rs:2217-2292`). And — verified at the time — the dedup map
   is keyed on the client-chosen `(producer_id, producer_seq)` with no binding to the
   capability (`store.rs:175`, the `dedup` map; `stage_publish` (`:939`) consults
   `staged_or_durable_dup` (`:902`) through `stage_publish_bounded` at `:953`), so any
   co-permitted publisher could pre-publish a peer's next key and the peer's genuine
   record dedups to the attacker's offset — a silent-drop attack on exactly the acks and
   inbox records a fleet depends on. **That hole is closed now**, by the producer binding
   on `Publish`/`ProcessAndProduce`/`Will` and by the unbound-link-grant rule on
   `Replicate` (`broker.rs:2241-2246`, §8.2). The capability tag was also a bearer secret
   sent inside the stream (`proto.rs:81`, the `Attach` request); it no longer crosses the
   wire at all (§8.2).

**The thesis.** The doctrine's four verbs (`/a/{stream|queue|inbox|state}` as
projections over one log, `docs/DOCTRINE.md:18-21`) are enough. Broadcast is a subject
subtree everyone may read and one principal may write. A message is a record on the
recipient's lane whose sender the capability forced. A reply's correlation id is the
request's offset. Presence is a last-value record plus a will. What is missing is not
machinery: four request tags, two response tags, a prefix on the capability string,
and one frontend crate.

---

## 2. Why astream + aterm — the built primitives

| Property the fabric needs | Built today | Status |
|---|---|---|
| Subject/Filter addressing, whole-segment `*`/`>`, control bytes rejected | `crates/astream-wire/src/subject.rs:56-80,138-180` | **BUILT** `wire.address-grammar.validated` |
| Sound containment for a subscribe ACL (never a false positive) | `Filter::contains`, `subject.rs:217-248` | **BUILT** `wire.filter.containment` |
| Exactly-once ingest by `(producer_id, producer_seq)`, rebuilt on restart | `store.rs:175` (the `dedup` map), `:575-603` (rebuilt in `open_inner`), `:902 staged_or_durable_dup` | **BUILT** `broker.exactly-once-pubsub-resume` |
| Replay from any offset, then a no-poll Condvar tail, to N subscribers | `broker.rs` `tail_loop` | **BUILT** (same claim); N-subscriber fan-out is now green too — 16 concurrent subscribers, every record exactly once — in `broker.last-value` (R1), and its rate FLOOR is green too — `broker.bench.fanout-floor` (R12) |
| Retained last-value as a paged query (`Last` + `Mark`), consistent with the subscriber-visible head | `crates/astream-broker/src/store.rs` `last_matching` over the ordered `last` index; `broker.rs` the `Request::Last` arm | **BUILT** `broker.last-value` (R1) |
| Bounded, NON-TERMINAL read (`Fetch`), scan-capped so one request is bounded in work | `store.rs` `fetch`; `broker.rs` `FETCH_SCAN_MAX`, the `Request::Fetch` arm | **BUILT** `broker.fetch-bounded` (R2) |
| Proof-of-possession `Attach` over a per-connection nonce, acknowledged, over a bounded keyring; the §8.2 matrix incl. the producer binding; the `/a/bind` table | `broker.rs` `attach_grant`, `cap_authorized`; `store.rs` `stage_bind` | **BUILT (opt-in `cap`)** `broker.cap-keyring-enforced` (R4) |
| A persisted `Will`, deduped and fenced on the producer's high water, re-fired on broker open | `store.rs` `WillRecord`, `stage_will_fire`, `pending_wills`; `broker.rs` `fire_will` | **BUILT** `broker.will-fires-exactly-once` (R5) |
| The inbox loop as library helpers: the two-connection drain and the read-process-write ack | `crates/astream-broker/src/client.rs` `take`, `drain`, `ack` | **BUILT** `broker.inbox-drain-ack-exactly-once` (R6) |
| Broker-durable consumer-group cursor; commits are hidden `/a/commit` records | `store.rs:39 COMMIT_SUBJECT`, `:800-832` (`group_start` / `commit`); `broker.rs:1873-1894` (the `SubscribeGroup` arm), `:2779` (`tail_loop`'s explicit hidden-subject skip) | **BUILT** `broker.true-exactly-once-e2e` |
| Atomic read-process-write, deduped | `store.rs:833-867 process_and_produce` | **BUILT** (same claim) |
| Counterfactual fork-delivery (offline snapshot, live log untouched, closed by an explicit `Mark`) | `store.rs:1748 fork_shared`; `broker.rs:1782-1872` (the `ForkSubscribe` arm, its closing `Mark` at `:1863-1870`) | **BUILT** `broker.agent-native-fork-and-cognition` |
| Unforgeable capability = HMAC-SHA256-signed Filter; verify folds all 32 tag bytes with no early exit on the first differing byte | `crates/astream-cap/src/lib.rs:270 mint`, `:291 verify`, `:257 ct_diff` (the fold, split out so a rewrite to `==` is detectable by a test) | **BUILT** `cap.unforgeable-mint` (the mint); the fold is guarded by `ct_diff_folds_every_byte_whatever_the_mismatch` under `cap.grant-mode-and-producer` |
| Capability enforced on the accept path, incl. group-as-subject for commits | `broker.rs:843 open_guarded`, `:1567-1603` (the per-request gate), `:2217-2292 cap_authorized` | **BUILT (opt-in `cap`)** `broker.cap-enforced-on-attach` |
| Confidential, authenticated wire (XChaCha20-Poly1305, PSK; AAD = `hello_client‖hello_server‖direction‖seq` from a key-confirming per-connection handshake, bounded pre-auth accept) | `crates/astream-aead/src/lib.rs:14-24`; `stream.rs:5-26,64-67`; `broker.rs:1121 serve_tcp_sealed`; `client.rs:85-97 connect_tcp_sealed` | **BUILT (opt-in `aead`)** `broker.sealed-tcp-roundtrip` |
| Single-writer keyboard with an auditable handoff, **enforced at ingest** | `crates/astream-engine/src/control.rs:38-49` (the non-`Copy`, non-`Clone` `ControlToken`), `:6-8` (enforcement is `Session::apply_input_as`), `:25-29` (the honest boundary: the plain `apply_input` takes no token) | **BUILT** `term.fleet.control-handoff` |
| Exactly-once drive into a real PTY at the astream-host seam | `crates/astream-host/src/driver.rs:53-69` (`drive_input` refuses a duplicate before any write) over `crates/astream-engine/src/session.rs:258-273 precheck_input`, which wraps `:246-250 is_duplicate` | **BUILT** `term.drive.interactive-exactly-once` |
| Durable causal pointer message→keystroke on the engine envelope | `crates/astream-engine/src/envelope.rs:36` (`ENV_VERSION = 3`), `:69` (`caused_by`); `session.rs:325-333 apply_input_caused` and its token-gated twin `:337-347 apply_input_caused_as` | **BUILT** `term.fleet.durable-watermark` |
| Consistent-cut replay across session logs (`replay_to_cut` now returns `Result<CutReplay, ReadError>`, whose `folded_through` is an `Option<Offset>`) | `crates/astream-engine/src/fleet.rs:42-47 Cut`, `:69-76 is_consistent`, `:110-117 CutReplay`, `:126-153 replay_to_cut` | **BUILT** `term.fleet.consistent-cut-replay` |
| A resident pump that turns bus records into semantic wakes | `crates/astream-pump/src/lib.rs` `Pump::attach` → `Pump::next_wake`; `wake_line` (the wake-line formatter, now in the library so the CLI and an embedder render identically), printed through `aspump.rs`'s `emit` | **BUILT** `pump.wake-on-boundaries`, `pump.cli.wake-lines` |
| The pump on an ARBITRARY subject, and off a broker-durable cursor | `crates/astream-pump/src/lib.rs` `Pump::attach_subject`, `Pump::attach_group` + `Pump::commit`; `aspump --subject/--group/--tcp/--key-file` | **BUILT** `pump.attach-subject-and-group` (R10) — at-least-once on wakes, not exactly-once |
| Shell faces: `asb serve|pub|sub|commit` byte-exact framing (`sub --group G`; the sealed key only via `--key-env`/`--key-file`, never argv; a capability only from a FILE — `--cap-file PATH` (repeatable, `<grant> <tag-hex>` lines, each split at its LAST whitespace so a filter holding a space still reads back), with `--cap-filter`/`--cap-tag` on argv REFUSED for the same reason a bare `--key HEX` is; every flag strict, exit 2) | `crates/astream-broker/src/bin/asb.rs:7-17` (the verb block), `:127-131` (the key rule), `:133-145` (the capability rule), `:376-408 load_caps` (the `--cap-file` parser, its last-whitespace split at `:362-375`, `:389`) + `:717-730` (the flag itself, repeatable), `:602-616` (`ARGV_SECRETS`, the argv refusal table) and `:712-716` (the refusal, exit 2), `:159-166` (strict flags) | **BUILT** `broker.cli.pub-sub-roundtrip`, `broker.cli.tcp-roundtrip` |
| aterm: stable sid, per-instance socket + token, discovery graph | `crates/aterm-types/src/control_socket.rs` `token_choice_follows_symlink_target`, `stale_sweep_removes_only_dead_instances` (`:384,493`); `crates/aterm-gui/src/proxy.rs` `graph_entry_roundtrips_through_disk` (`:674`) — `cargo test -p aterm-types control_socket && cargo test -p aterm-gui proxy::` | **BUILT (aterm)** test-cited |
| aterm: Owner vs Edge scope, per-op edge tokens bound to the launch nonce | `control.rs` `op_scope_gate_owner_full_power_edge_read_only`, `edge_cross_session_is_fail_closed_without_edge_and_allowed_with_one` (`:12913,13912`); `crates/aterm-session/src/edge.rs` `decide_edge_permits_only_exact_match`, `authority_does_not_flow_along_a_cycle_or_self_loop` (`:470,599`) — `cargo test -p aterm-gui op_scope_gate && cargo test -p aterm-session edge::` | **BUILT (aterm)** test-cited |
| aterm: `subscribe @* events,sessions` push digest with honest `GAP` frames and a roster journal | `subscribe.rs` `bytes_gap_emitted_when_queue_overflowed`, `a_sub_tick_spawn_and_exit_both_surface`, `only_owner_is_granted_the_instance_sessions_stream` (`:3754,3923,2876`) — `cargo test -p aterm-gui subscribe::` | **BUILT (aterm)** test-cited |
| aterm: `meta set role|attention`, `status revision= detail=`, `who`, `lease`, `turn` | the catalog golden `full_catalog_matches_the_generated_golden` (`crates/aterm-types/src/control_verbs.rs:2403`) pins every verb's contract; `access_exceptions_are_exactly_the_declared_sets` (`:2106-2196`) pins `who`/`sessions` Owner-only; `drain_turn_events_emits_once_per_new_record` (`subscribe.rs:4046`) — `cargo test -p aterm-types control_verbs` | **BUILT (aterm)** test-cited |
| aterm: nested authority one hop at a time | `proxy.rs` `one_proxy_hop_preserves_guard_until_original_client_ack` (`:879`); `control.rs` `proxy_forward_plan_owner_only_op_scoped_and_nonce_guarded` (`:10367`); `crates/aterm-nest/src/main.rs:7-11` is a demonstration binary, not a test | **BUILT (aterm)** test-cited |

**One drift note the design stands on.** The two astream ones this design was drafted
against are now closed by the audit pass's doc re-sync: `docs/DESIGN-astream-term.md:343-363`
records the AEAD wire and the enforced mint as **BUILT (opt-in `aead` / `cap`)**
(`evidence/manifest.toml:472 aead.seal-open.authenticated`, `:478
broker.sealed-tcp-roundtrip`, `:430 broker.cap-enforced-on-attach`), and
`crates/astream-engine/src/fleet.rs:10-16` now names the durable source as "the envelope's
`caused_by` pointer (`ENV_VERSION` 3)" with claim `term.fleet.durable-watermark`
(`manifest.toml:224`, `envelope.rs:36`) — the words
"SEED, still blocking", "the next increment" and "a later rung" are gone from both files.
What remains is aterm's: `subscribe.rs:150-160`'s doc comment still says the roster "keeps
no monotonic lifecycle log"; the journal fast path at `:1125-1146` and the test
`a_sub_tick_spawn_and_exit_both_surface` (`:3923`) say otherwise.

---

## 3. Architecture and subject taxonomy

### 3.1 Three actors, one log

```
 aterm instance (node n-A, host 1)            astream broker (fleet F)            aterm instance (node n-B, host 2)
┌───────────────────────────────┐        ┌────────────────────────────┐        ┌───────────────────────────────┐
│ sessions: s-1 human, s-2 cc   │        │  ONE offset log            │        │ sessions: s-7 codex, s-8 zsh  │
│   inbox/post/await inbox      │        │  /f/F/{fleet,pub,in,term,  │        │                               │
│         ▲ ctl socket │ Owner  │        │         cur}/…             │        │                               │
│  aterm-link serve (child,     │──pub──▶│  Last · Fetch · Will       │◀──sub──┼──────── aterm-link serve      │
│   Scope::Bridge over two      │        │  Hello/Nonce → PoP Attach  │        │                               │
│   inherited socketpair fds;   │        │  caps: mode + principal    │        │                               │
│   N broker connections)       │        │  sealed TCP across hosts   │        │                               │
└───────────────────────────────┘        └────────────────────────────┘        └───────────────────────────────┘
   hooks (metadata only) ─▶ Claude Code turn      human's tools: rw on /f/F/fleet/h-<name>/> — the only halt authority
```

- **The bridge — `aterm-link serve`, one per aterm instance (§11.2).** A
  frontend/embedder process, never engine code (`docs/DESIGN-aterm-lash.md:50-62`;
  `docs/DESIGN-drive-pipe.md:166-171`). It is the *node*: the bus principal under which
  every session it hosts is addressed and attested. The instance launches it as a child
  holding two `socketpair` ends (a verb connection and a `subscribe @* events,sessions`
  push connection, both `Scope::Bridge`) — not control-pool lanes. It publishes the
  events digest, presence rows and outbound posts; drains the node's inbox lanes into
  aterm's inbox rings with `deliver`; mirrors the fleet halt into `hold` and the control
  row into `lease`. **Lane cost, precisely:** the bridge costs zero pool lanes; each
  locally parked `await inbox` (a script's wait) costs one, as any `await` does today
  (`docs/OPERATOR.md:87-90`); the hook path parks none (§9.1).
- **The broker.** Unchanged in shape: thread-per-connection, single writer, group
  commit, exactly-once ingest, Condvar tail, sealed TCP, capability enforcement. It
  gains `Last`, `Fetch`, `Will`, `Hello`, the `Mark`/`Nonce` responses, a
  proof-of-possession `Attach` with a keyring, a grant string with a mode and a
  principal binding, and two hidden record kinds (`/a/will`, `/a/bind`) of the same kind
  as `/a/commit` (§11.1).
- **The endpoint (aterm).** Gains an inbox ring, a post queue and a hold gate per
  session — *state*, not I/O — the verbs that read and write them, one `await`
  predicate, and one connection scope (§11.2). An agent inside aterm talks only to its
  own control socket, exactly as today.

### 3.2 Principals and producer ids

A principal is one subject segment, class-prefixed so reserved literals can never
collide with an id: `s-<20 hex>` an aterm session (its stable sid,
`crates/aterm-session/src/id.rs:10-14`); `n-<16 hex>` a node (minted once by the bridge,
persisted in its state dir); `h-<name>` a human; `a-<name>` a headless service. A name
is `[a-z0-9-]{1,32}` — too short to carry a sentence into an agent's context.

Every bound principal has a **producer id** the *broker* derives from the principal
named in its grant: `pid = u64::from_le_bytes(SHA-256("astream-pid\0" ‖ principal)[..8])`,
computed in `astream-cap` over the `sha2` it already has. Nothing a bearer types is ever
a producer id: `Publish{producer_id}` must equal the derived id of a principal its ring
names (§8.2). A targeted collision is a 2^64 second-preimage search; as belt-and-braces
the broker keeps a **binding table** `pid → principal` (a hidden `/a/bind` record
appended when a bound grant first attaches, rebuilt on open like `/a/commit`) and
refuses an `Attach` whose derived id is already bound to a different principal
(`Error 5, "producer id collision"`). Unbound grants (the fleet root) remain the god cap.

### 3.3 Subject taxonomy — face first, owner second

All fleet subjects live under `/f/<F>/`, `<F>` a fleet name. **One broker per fleet is
this design's deployment decision** (federation is the named seed, §14). `/a/` stays
astream's own (`/a/commit`, `store.rs:39`, which the broker now also refuses to a client
publish by name — `publish_subject_error`, `broker.rs:2096-2104`; the built PTY faces
`/a/stream/term/<sid>/{in,out}`, `crates/astream-pump/src/lib.rs:35`). The segment after
`<F>` is the **face**; the segment(s) after the face are the **owner** — the only
principal whose read-write capability covers that subtree (for `fleet` and `in`, the
*writer* is the pinned segment instead). Every face has one read policy and one write
policy, each a prefix. An owner path is `<node>/<sid>` (a session), `<node>/node` (the
node itself), or `p/<principal>` (a human or service that is not an aterm session).

| Subject | Face kind | Writer (rw cap) | Readers | Semantics |
|---|---|---|---|---|
| `/f/<F>/fleet/<src>/<kind>` | last-value or stream | the human `<src>` (`rw,p=<h>:/f/<F>/fleet/<h>/>`) | every member (`ro:/f/<F>/fleet/>`) | `halt` (retained, per human), `barrier`, `notice` — **the writer is the address** |
| `/f/<F>/pub/<owner>/presence` | last-value | the owner | every member (`ro:/f/<F>/pub/>`) | roster row; `state=gone` written by a `Will` |
| `/f/<F>/pub/<owner>/ev` | stream | the owner | every member | the aterm `events` digest, one record per `EVENT` line, `GAP` included |
| `/f/<F>/pub/<owner>/say/<kind>` | stream | the owner | every member | the owner's announcements (`notice`, `report`, `barrier`) |
| `/f/<F>/pub/<owner>/ack/<offset>` | last-value | the owner | every member | the owner's answer to the barrier (or halt) at `<offset>` |
| `/f/<F>/pub/<owner>/control` | last-value | the owner's node | every member | who holds the keyboard (§6.6) |
| `/f/<F>/in/<node>/<sid>/<src>/<kind>` (**exactly 7 segments**) | stream | **`<src>`** (`rw,p=<src>:/f/<F>/in/*/*/<src>/*`) | the owner (`ro:/f/<F>/in/<node>/>`) | addressed messages to the owner from `<src>` |
| `/f/<F>/term/<node>/<sid>/out` | stream | the node (`rw,p=<n>:/f/<F>/term/<n>/*/out`) | drivers, pumps (scoped) | PTY bytes — the flight recorder, opt-in per session |
| `/f/<F>/term/<node>/<sid>/in/<src>` | stream | `<src>` (`rw,p=<src>:/f/<F>/term/*/*/in/<src>`) | the node (`ro:/f/<F>/term/<n>/>`) | the drive face, per driver; applied only if `<src>` holds `control` (§6.6) |
| `/f/<F>/term/<node>/<sid>/screen` | last-value | the node | late joiners (scoped) | a full `DELTA screen` snapshot, opt-in, ≤ 4/s |
| `/f/<F>/cur/<owner>/<name>` | group name | the owner | — | consumer-group names are subjects the cap must grant (`broker.rs:2282,2288` — the `SubscribeGroup` and `Commit` arms of `cap_authorized`); never delivered |

Reserved literal segments can never collide with a class-prefixed id. A subject never
contains `*`, `>` or a control byte (`subject.rs:34-45`), so every field above is a
literal segment and every query below is a valid `Filter` (`*` = exactly one segment,
`>` = one-or-more trailing, `subject.rs:160-167,200`).

**The `in` shape is pinned, not implied.** Because `>` is one-*or-more* segments, a
sender under a `>` grant could publish an 8-segment subject whose last two segments
read as a forged `<src>/<kind>`. So the `in` write grant ends in `*` (exactly one kind
segment); an `in` subject is exactly seven segments, parsed **by position from the
left**; a receiving bridge refuses — never delivers, records `ev undeliverable off=<n>
reason=malformed` — any `in` record with ≠ 7 segments, a `<src>` without an
`s-|n-|h-|a-` prefix, or a `<sid>` it does not host.

Why the node is nested into the owner path: a bridge is pre-authorized for every
session it will ever host by **one** grant per face, so a `spawn` never round-trips to
the secret holder. Sids are globally unique, but nothing on the bus *binds* a sid to a
node — any node can publish a presence row for any sid under its own subtree — so a
sender's bridge **pins** a sid to the first node seen advertising it (TOFU, persisted in
its state dir) and treats a second node claiming a pinned sid as a conflict, never a
route (§6.1).

### 3.4 The four doctrine verbs, realized

| Doctrine verb | Realization | Status |
|---|---|---|
| `stream` | `Subscribe`/`SubscribeGroup` + `Commit`; `Fetch` for a bounded read | **BUILT**; `Fetch` **BUILT** `broker.fetch-bounded` (R2) |
| `state` | `Last{filter, after, max}` — last record per matching subject, paged, then `Mark` | **BUILT** `broker.last-value` (R1) |
| `inbox` | a lane only the owner reads, drained as a durable group; correlation by offset | **BUILT** (the transport half) `broker.inbox-drain-ack-exactly-once` (R6); the endpoint ring is **BUILT (aterm)** — A2, test-cited (§11.2) |
| `queue` | competing consumers with claims — deliberately out (§14); aterm's embedded operator keeps that shape (`docs/OPERATOR-EMBEDDED.md:185-203`) | out of scope |

---

## 4. Message model and envelope

### 4.1 Byte layout, outermost to innermost

```
astream_wire::Frame     | A5 71 | ver=1 | flags=0 | payload_len u32 LE | crc32 u32 LE | payload |    (frame.rs; 16 MiB cap)
  BrokerRecord v2       | 02 | seq u64 | producer_id u64 | producer_seq u64 | subject u32-len ‖ bytes |
                        | body u32-len ‖ bytes | commit u8 [‖ group u32-len ‖ bytes ‖ upto u64] |         (brecord.rs:13,24-40 — UNCHANGED;
                                                                                                           payload capped at MAX_RECORD_PAYLOAD
                                                                                                           = 16 MiB − 16, brecord.rs:20, enforced :77)
    fabric body         v=1 t=<ms> [re=<offset>] [dl=<ms>] [epoch=<hex32>] [gen=<seq>:<fp16>]
                        [via=<p>[,<p>…]] [text=<pct>] [len=<n>]                                            (one ASCII line)
                        [ "\n" ‖ <n> raw bytes ]                                                           (only when len= is present)
```

The broker's on-disk RECORD is **unchanged** (`BREC_VERSION` stays 2 — nothing on this
ladder is an on-disk format change, so no existing log is affected), but the WIRE is not:
`PROTO_VERSION` moved 1 → 2 (`proto.rs:12`), because `Attach` kept its tag `0x07` and its
wire shape — a string then a byte string — while its MEANING changed, from
`{cap_filter, cap_tag}` to `{grant, proof}` (§8.2). Same bytes, different meaning: under an
unchanged version byte a v1 client's `Attach` would have decoded CLEANLY into the new
variant and then desynchronised on a `Mark` it never expected, so the byte moved. A
pre-bump peer is now REFUSED at the codec, in both directions, rather than misread
(`broker.proto.tag-budget`). `Response::Mark` also grew an additive third field, and a
durable `<log>.replica` sidecar now sits beside the log, so "no on-disk change" is not the
whole truth either (§11.1, deviations 5 and 7). The fabric body is one line in the control-protocol
grammar every aterm client already parses — space-separated `key=value` tokens, values
pct-encoded, `-` for unset (`help_catalog_full.txt:33,34`) — optionally followed by
`len=` raw bytes. Zero-dep on both sides; the broker never looks inside a body.

There is deliberately **no `from=`, `to=`, `kind=`, `id=`, `trust=` or `by=` in the
body**: they are the subject's segments, the record's offset, and a label the
*receiver* computes (§4.3). A field a sender could lie about is not in the body; a field
the broker enforced is in the address or in the producer key. Two attested exceptions:
a node writing on behalf of one of its sessions adds `from=<sid>` (the node is that
instance's Owner and could type as the session anyway — §8.3), and a relayer appends
`via=` (a demotion at the receiver, never authority — §6.7).

`t=` is the publisher's wall clock, informational — records carry no timestamp
(`brecord.rs:24-40`); a broker-stamped time is DESIGNED (§14). `v=` versions the fold
rules a reader applies (§10). `epoch=` is **mandatory** on every `term/in` and `control`
record and is the target session's public launch nonce (§7); `gen=` is an optional
freshness fence on `term/in` only.

### 4.2 Kinds, per face

| Face | `<kind>` | Body fields | Ordering / delivery / durability |
|---|---|---|---|
| `pub/…/ev` | — (payload is the aterm `EVENT` line) | `v=1 t= ev=<pct(EVENT payload)>` e.g. `turn 12 submitted=1 status=settled`, `closing reason=ctl-close by=…`, `gap bytes-dropped=…`, `undeliverable off= reason=` | total order per owner; a `GAP` frame is **published, not dropped** (fixes `fleet_cli.rs:549`) |
| `pub/…/presence` | — | `v=1 t= inc=<n> epoch=<hex32> state=live|exited|gone role= detail= phase= driving=<turn:<id>|lease:<h>|-> holder=<p|-> watchers= hold=<0|1> fabric=<connected|disconnected> attention= [title=] host= pid= parent=` | last-value; written on every change of `sessions`/`who`/`status revision=`/`meta`; `gone` by a `Will`. `detail=` is aterm's already-sanitized running command — first word's basename plus an allow-listed subcommand, never an argument (`help_catalog_full.txt:34`) — so it carries no secret; `title=` (an OSC title can carry a cwd or command) is **opt-in** (`--presence-title`); `attention=` keeps aterm's 256 B cap |
| `fleet/<h>` | `halt` | `v=1 t= state=on|off reason=` | last-value per human; in force iff **any** `Last{/f/<F>/fleet/*/halt}` row says `on`; each human lifts their own |
| `fleet/<h>` | `barrier` | `v=1 t= expect=<n|-> dl=<ms> text=` | stream; its **offset** is the barrier id |
| `fleet/<h>`, `pub/…/say` | `notice`, `report`, `barrier` | `v=1 t= text=` | stream; a `say/barrier` is answered only from `--accept-from` principals (§5.4) |
| `pub/…/ack/<B>` | — | `v=1 t= state=ready|busy|refused|absent|held reason=` | last-value per (member, barrier); exactly-once by producer dedup; readers ignore an `ack/<B>` whose own offset is < B |
| `in/…` | `ask` `answer` `task` `report` `note` `control` `ack` `expired` `undeliverable` | `v=1 t= [from=<sid>] [re=] [dl=] [epoch=] [via=] text= [len=]` | per-`<src>` order; exactly-once ingest; delivered at-least-once by group cursor, deduped by offset at the endpoint (§6.2). **Every `in` kind is an inbox row; none is ever applied to a PTY** (§6.6) |
| `pub/…/control` | — | `v=1 t= holder=<p|-> by=<p> reason= evidence=claim|grant|release|request|unaccounted-change` | last-value; the intent ledger of the keyboard |
| `term/…/in/<src>` | — | `v=1 t= epoch=<hex32> [gen=<seq>:<fp16>] [re=<offset>] len=<n>` + raw bytes | applied iff `<src>` == the `control` holder ∧ `hold=0` ∧ `epoch` matches ∧ (`gen` absent or current) — the **only** bus→PTY path (§6.6) |

### 4.3 Provenance and trust — two orthogonal labels, both receiver-computed

- **Provenance** is *who* published: the cap-forced `<src>` segment and the cap-bound
  producer id. A row's `from=` in aterm's `inbox` is filled by the bridge from the
  delivered subject (`Delivery` carries the subject, `proto.rs:161-165`) and the body's
  node-attested `from=<sid>`, rendered `s-…@n-…` — never from a sender's claim.
- **Trust** is *what the content is*, a **pure function the receiving bridge computes**
  from `(face, <src> class, via= present)` — never read from a body: `h-*` →
  `trust=human`; `n-*`/`s-*`/`a-*` → `trust=agent`; any `via=` → `trust=relayed`; the
  `ev`/`term` faces and anything the bridge itself quotes from a screen → `trust=screen`.
  There is no `attested` token (identity attestation is `from=`, not trust) and no
  "downgrade only" rule to police, because no sender ever writes the label. "Screen
  content is data, not instructions" (`docs/OPERATOR.md:221-224`) becomes a label the
  agent sees *first* in every inbox row (§9.2).

---

## 5. Broadcast

### 5.1 Fan-out

A broadcast is a publish under a subtree many principals may read. The broker fans out
to N subscribers as N independent `tail_loop`s over `Arc`-shared records
(`broker.rs:2721 tail_loop`, whose catch-up copy at `:2736-2742` hands out shared `Arc`
records from `store.rs:1735 read_from`) — the *broker* absorbs the observers. Delivery to a
single subscriber is **BUILT** (`broker.exactly-once-pubsub-resume`;
`broker.bench.replay-egress-floor` is a one-subscriber backlog replay), and
**N-subscriber fan-out is now BUILT** too — `broker.last-value` (R1) asserts sixteen
concurrent subscribers each receive every one of 1 000 records exactly once, in order.
A RATE floor for it is **BUILT** too — `broker.bench.fanout-floor` (R12): 64 live
subscribers on one filter, every record at its exact offset, ~399 000 deliveries/s on the
disclosed box. That bench also makes the honest correction to *"the broker absorbs the
observers"*: what it gates is that delivery is **off the commit path** (durable ingest with
four live subscribers holds ~0.88 of its no-subscriber rate), not that observers are free —
at 64 co-hosted subscribers the producer's durable rate falls ~7x on an 18-core box (§13).

Three broadcast faces with three authority shapes: `/f/<F>/fleet/<h>/<kind>` (a human
writes, all read — needs the read-only mode, §8.2); `/f/<F>/pub/<owner>/say/<kind>` (an
owner announces under its own authority); `/f/<F>/pub/<owner>/{ev,presence}` (the
node's authority, the fleet's eyes).

**`say` is publish-only in the built fabric.** `post to=say` is routed —
`/f/<F>/pub/<node>/<sid>/say/<kind>`, with the session as the owner segment — and the tui
renders it out of the whole-fleet transcript. But a bridge subscribes to three faces only,
`fleet/>`, `in/<node>/>` and `term/<node>/>`, so **no bridge ever turns a `say` record into
an inbox row**: a broadcast reaches a human reading the transcript, not an agent's `inbox`.
A bare `say` with no session behind it (a bridge-internal notice) has no owner face to speak
under at all and is unroutable. Fan-out into endpoints is **DESIGNED**.

### 5.2 Retained / last-value: `Last`

`Last{filter, after, max}` delivers the most recent record of every subject matching
`filter` whose subject sorts after `after` (`""` for the first page), in ascending
**subject** order, then `Mark{next: head, head, resume}`; the connection stays usable.

**`max` is the client's ask, not the bound.** The broker clamps it to `LAST_PAGE_MAX =
4096` rows (`broker.rs:256`, applied at `:1931`) and cuts each index scan after
`LAST_SCAN_MAX = 65536` entries VISITED — matched or not (`broker.rs:250`, passed at
`:2690`). So **a page shorter than `max`, an EMPTY one included, is not the end of the
answer.** `Mark` carries a third field, `resume` (`proto.rs:172-190`), the subject cursor
that continues the page; a correct reader pages on it until it comes back empty, which is
the broker saying its scan reached the end of the filter's range. `Client::last_page`
(`client.rs:457`) is the shape that surfaces it; `Client::last` (`:445`) drops it and is
only safe where the caller knows the filter is dense.

The broker keeps `last: BTreeMap<String, Offset>` beside `dedup` (`store.rs:182`),
updated as a batch is promoted (`store.rs:1408-1447 index_last`, driven from
`commit_batch` at `:1457`) and rebuilt on open exactly like `dedup` (`:575-603`, inside
`open_inner`); `/a/commit`, `/a/will` and `/a/bind` are excluded like everywhere else
(`store.rs:59 is_hidden_subject`).

**The cost model, corrected.** This section used to say a page "costs O(log n + page)"
because it is a range scan from the filter's literal prefix (`/f/F/pub/` for
`/f/F/pub/*/*/presence`). That was false for a SPARSE filter, and `LAST_SCAN_MAX` exists
because it was false: `/f/F/pub/*/*/ack/<B>` (§5.4's own barrier query) seeks to
`/f/F/pub/` and then pays a `Subject::new` + `Filter::matches` for every entry it skips,
so an unbounded scan costs O(entries under the literal prefix), not O(page) — with the
log lock held for all of it, which a read-only holder could loop to stall ingest. What is
built is bounded in WORK, not only in output: an O(log n) seek, then at most
`LAST_SCAN_MAX` index visits per acquisition of the log lock, at most `LAST_PAGE_MAX`
rows delivered, and a resume cursor to continue from. `last_matching` takes `scan_max`
for exactly that reason (`store.rs:1616-1664 last_matching`).

**The resume cursor never names a subject the filter does not match.** A page cut by the
scan bound stops on whatever index entry the walk reached, which under a prefix as broad
as `/f/F/in/` is routinely another node's, another session's, another human's inbox lane
— a name a scoped reader is not entitled to, and in this fabric provenance is the address,
so names are the roster. So `last_page` (`broker.rs:2667-2718`) takes and RELEASES the log
lock per round and CONTINUES the walk from such a cursor instead of putting it on the
wire. What reaches `Mark.resume` is therefore always either absent (the answer is
complete), a subject cut off by `max` (which matched by construction), or a subject the
requested filter matches — and any capability that contained the filter contains that
subject. `LAST_RESUME_ROUNDS = 64` (`broker.rs:263`) bounds one request's total CPU, never
a single lock hold; a request that cannot reach such a position within it is answered with
an `Error`, not with a blanked cursor — an empty `resume` means "complete", so blanking
would turn a name leak into a silent truncation.

**Consistency.** A page is read together with the **subscriber-visible** head under the
log lock — and when the walk takes SEVERAL scan rounds, that head is PINNED on the first
round and every later round reads against it (`last_page`'s `pinned`, `broker.rs:2679`,
read at `:2688`), so the whole
answer is a snapshot as of the one head its `Mark` reports, not a splice of rounds each
read at its own. (It was the latter until the fix: rows collected in an early round went
out paired with a LATER round's head, so a subject the log had already superseded below
that head came back at its old value — a last-value verb returning a non-last value.) The
head itself is an atomic beside the log, not a field of it — `shared.head`
(`broker.rs:359-364`; `Broker::visible_head`, `:971`), which the writer stores under that
same lock at `:2562` (Strict/Relaxed) or publishes as the quorum watermark with
`fetch_max` at `:2574` (Replicated), and which the tail loop reads at `:2738,2757`. It
can never run *ahead* of promoted records: in Strict/Relaxed it **is** the durable head, and in the Replicated tier
it **lags** it, because `tail_loop` deliberately withholds records above the watermark
(`:2736-2742`). So a `Last` page must be paired with `shared.head`, never with
`log.head()` — pairing it with the durable head would expose, on the Replicated tier,
exactly the records the tail path refuses to deliver. Paired correctly,
`Subscribe{from_offset: next, filter}` on the same connection afterwards is gap-free and
dup-free. A multi-page `Last` is consistent per page; a record landing between pages
may appear both in a later page and in the tail from the first page's `next`, so a
paged reader folds newest-wins and dedups on offset — the endpoint ring does anyway.

**Cost model, honestly.** Distinct subjects grow with history, not just with
principals × faces: one `presence` per session ever spawned (kept as `state=exited`),
one `ack/<B>` per (member, barrier) ever issued, one `in/…/<kind>` per (owner, src,
kind). Four bounds: the two broker-side bounds above (`LAST_PAGE_MAX` rows delivered,
`LAST_SCAN_MAX` index entries visited per lock hold); a per-producer cap on distinct
subjects (`MAX_SUBJECTS_PER_PRODUCER = 4096`, `store.rs:142`, counted in the `last` index;
the publish that would exceed it is `Error 5`, and a `Will` whose SUBJECT would exceed it
is refused at REGISTRATION rather than lost at firing — `store.rs:1146-1203
stage_will_register`) — per-principal because producer ids are cap-bound; and
the bridge collapses a session's `exited` presence row into an `ev` record after
`--exited-keep <n>` (default 64) sessions. "Distinct subjects" joins the retention risk
(§14).

This is MQTT 5 retained messages (OASIS MQTT v5.0 §3.3.1.3) / JetStream
`DeliverPolicy: last_per_subject` / Kafka compaction as a *query over the same log*:
the retained value is also an offset you can replay to, and the late-joiner equivalence
assertion (R1) pins that `Last` equals the last-per-subject of a from-0 replay **at the
visible head**, not at the durable one. **BUILT** `broker.last-value`
(R1); floor **BUILT** `broker.bench.last-floor` (R12) — 4 096-row pages over 10 000
subjects behind 200 000 records at ~180 queries/s, with durable ingest under a concurrent
query loop holding ~0.97 of its idle rate, which is the measured form of "the lock is held
for the page, not for the scan". One refinement the code makes explicit: a
subject whose newest record is at or above the head the page is read against is OMITTED
from the page rather than answered with an older record — fail-closed, the same direction
as `tail_loop`. That is what the visible head lagging the durable head means on the
Replicated tier; it is ALSO, on every tier, the deliberate price of pinning the head
across scan rounds. A subject superseded to or above the pinned head while a multi-round
walk is between rounds is left out rather than returned stale, and reaches the reader on
the `Subscribe{from: next}` that pairs with the snapshot — because `next` IS that pinned
head. An omission the reader will be told about beats a stale row it will not. A late joiner paints the fleet in O(members):
`Last{/f/<F>/pub/*/*/presence}` is the roster; `Last{/f/<F>/fleet/*/halt}` is the halt flag.

### 5.3 The fleet halt (story A1) — a drive hold, and a hook stop

A human publishes `/f/<F>/fleet/h-<name>/halt` with `state=on reason=…`. Every bridge
tails `/f/<F>/fleet/>` and flips `hold <sid> on reason=… origin=fleet` on every session
it hosts (§11.2); a worker spawned after the halt sees it at its first `Last`. Two
things then happen, and they differ in kind:

- **The drive hold (every agent, structural at the socket).** Under hold, every
  PTY-reaching socket verb against that session — `send key ctrl feed feed-bin paste
  paste-bin mouse resize signal turn close operator-propose-bin` — from **any** socket
  scope answers `ERR halted <reason>`, a transient class beside `ERR busy`
  (`docs/INTROSPECTION.md:157-166`) so existing back-off code already does the right
  thing; the physical keyboard keeps working. `post`, `inbox seen`, `meta set` and
  `lease` are **exempt** — they touch no PTY, and a halted agent must still be able to
  `post kind=ask "why am I halted?"`, mark the notice seen and escalate with `meta set
  attention`. A halt stops *drivers*; it does not stop an agent's own tool calls, which
  never cross the aterm socket.
- **The hook stop (Claude Code, structural at the tool call).** `aterm-link hook install
  claude` installs a `PreToolUse` hook that reads `status hold=` and, when held, **exits
  2** with the reason on stderr — documented by the vendor as "Blocks the tool call"
  with stderr shown to Claude (§9.1). `UserPromptSubmit` adds the hold banner as context
  (exit 0) rather than exit 2, which would erase the human's prompt. Hookless agents
  (Codex today, a bare shell) are **drive-held only**; §13 says so.

Only a `/f/<F>/fleet/<h>/>`-rw cap can write the flag (§8.2); an agent may *propose* a
halt only as an `ask` to a human. Lifting is the same human's subject flipping to `off`.
Every bridge acknowledges a halt it applied, and **the built ack is one retained subject
per node, not one per halt**: `pub/<node>/node/ack` carrying `v=1 t= re=<halt-offset>
state=held|ready` (`aterm-link/src/bridge.rs`'s `on_fleet_record`). The design asked for
`pub/<node>/node/ack/<halt-offset>`, a fresh subject per halt record — and the broker
bounds a producer at `MAX_SUBJECTS_PER_PRODUCER = 4096`, rebuilt from the log at every
open, against a node id its state dir mints once and keeps forever. So a fleet whose humans
toggled the halt two thousand times, or one cap-holding human publishing 4096 halt records
in a burst, permanently spent that node's whole subject budget: past the bound EVERY publish
from the node fails, including the `live` presence row the bridge refuses to attach without,
so no bridge on that node can ever attach again and every session it hosts stays held
`fabric-lost`. T9's "log flooding" residual became permanent damage. One subject carrying
`re=` costs the node one subject for its whole life. **The price is a narrower answer, and
a counter must read it as one:** the single row answers only the NEWEST halt that node saw,
so a node whose `re=` names a LATER halt is UNKNOWN for an earlier one, not absent —
"who is missing = roster minus acked" is exactly the reading that turns this into a false
report. The ack is also written at most once per halt offset, behind a durable watermark,
because the fleet face resubscribes from offset 0 on every reconnect. **And the per-barrier
`pub/<owner>/ack/<B>` face of §5.4 has no writer at all**: a session's own `post kind=ack
re=<B>` is routed to the ADDRESSEE's inbox lane like every other kind, so an issuer reads
its answers with `inbox`, not with `Last`. The only `ack` subject anything publishes is the
node's. **Fail closed:** a fleet-origin hold is sticky while the
bridge is disconnected from the broker; if the bridge itself dies, the instance applies
`hold on reason=fabric-lost` to every fabric-managed session until a bridge reconnects
(§11.2). All three halves are now **BUILT (aterm)**, test-cited: the endpoint enforcement —
the scope-blind gate at three seams and the fail-closed drop guard — is A2; the bridge that
tails `/f/<F>/fleet/>`, folds "in force iff any human says on", mirrors it into `hold` and
acks it is A3, and **the human's own `reason=` is carried through** by a later fix (A3
hard-coded `reason=fleet-halt` and dropped the halt record's words on the floor, which made
§5.3's whole point — that `PreToolUse` shows the model *why* — vacuous); the hook stop is
A4. The
verb list the gate refuses is derived, not enumerated: `fabric::is_pty_reaching`, and it is
wider than the sentence above — `focus` (it writes DEC 1004 reports to the PTY), `invoke`
(`invoke Paste` writes the clipboard into the front tab's PTY) and `tab` (`tab close [N]`
retires a session exactly as `close` does) are in it, and because `invoke`/`tab` resolve no
session they are refused while ANY session on the instance is held.

### 5.4 Acknowledged broadcast (barrier — story A5)

The issuer publishes `/f/<F>/fleet/h-<name>/barrier` (or `pub/<owner>/say/barrier`) and
gets offset `B` in its `PublishAck` (`proto.rs:159`). A member's answer is
`/f/<F>/pub/<owner>/ack/<B>`, deduped by its `(producer_id, producer_seq)` so a retried
ack lands once. **Who answers what:** the bridge auto-answers only `busy` (mid-`turn`)
and `absent` (exited) — a liveness echo, never consent; `ready` and `refused` come from
the session itself, `post kind=ack re=<B> ready|refused`, which a turn-based member
sends on its next turn. The count is one query: `Last{/f/<F>/pub/*/*/ack/<B>}`, ignoring
any `ack/<B>` whose own offset is below `B` (pre-published for a barrier that did not
exist yet); "who is missing" is the presence roster minus the acked set. A human's
`refused` is a decision the issuer must show, not a timeout. A `say/barrier` from a
principal not on the member's `--accept-from` list yields no answer at all — otherwise
one rogue publish costs N records and N new subjects fleet-wide. The count is **BUILT** —
`broker.barrier-count-by-last` (R7): five members present, a stale `ack/<B>` published below
`B` and discarded, a retry under the same producer key deduped to its original offset with
the head unmoved, four distinct members counted (one `refused`), the fifth found by
presence-minus-acked. What is built is exactly a **count over a log**: nothing blocks, the
rule (discard rows below `B`, count distinct owners) is the issuer's and lives in the
caller, and a member that never acks is simply absent — `busy`, `crashed` and `never
existed` are indistinguishable from the page. **Nothing in the built fabric writes
`pub/<owner>/ack/<B>`, so `Last{/f/F/pub/*/*/ack/<B>}` counts nothing today.** Three
separate gaps, all named rather than one blurred: the bridge-side `busy`/`absent`
auto-answers are not built and were on no rung's acceptance list — `on_fleet_record` handles
`halt` and nothing else, so a `barrier` or a `notice` on the fleet face is read and dropped;
a session's own `post kind=ack re=<B>` IS built (A2) but routes to the ADDRESSEE's inbox
lane like every other kind, so the issuer reads it with `inbox` rather than with a query
over a retained face; and the only `ack` subject anything publishes is the bridge's halt ack
(A3), one retained row per node carrying `re=<halt-offset>` (§5.3). R7 proves the COUNT over
a log, and the count is correct; what has no writer is the face it counts. The `--accept-from`
gate on a `say/barrier` likewise gates nothing yet, since there are no answers to gate.
**DESIGNED**, all three.

### 5.5 Late-join catch-up and the digest (story A6)

"What happened while I was away" is `Fetch{from: K, /f/<F>/…, max}` from the offset the
reader last committed (a durable group under its own `cur/` subtree), paged by
`Mark{next}` — the same replay the broker already proves (`broker.rs:2721 tail_loop`). Wall-clock
windows use `t=` in bodies until the broker stamps time (§14). Every record the reader
is allowed to see is inside its cap, evaluated at read time by `grants_filter`
(`cap/lib.rs:402`).

### 5.6 Rate and attention budget (story A7)

The bus never wakes an agent; the bridge does (§9). What was designed here was one budget
in the bridge, governing every egress: at most one `EVENT <local> inbox` per session per
pending batch; kinds ordered `control > ask > task > answer > report > ack > note`; a
per-session `serve --wake-budget <n>/<min>` bounding hook wakes and `await inbox` latches
alike, with `h-*` and `--accept-from` principals exempt.

**What is built is narrower, lives somewhere else, and drops the exemption.** The budget is
the STOP HOOK's own, not the bridge's: a per-session ledger of epoch-ms stamps under
`<state>/wake/<sid>`, trimmed to the window on every read and written temp+rename, read and
charged by the hook process itself (`aterm-link hook run stop --wake-budget <n>/<min>`,
default 6/min). It has to live outside the process that reads it, because a hook starts,
wakes or does not, and exits; and it cannot live in the bridge because there is no wake
socket for the bridge to be asked through (§9.1). `serve` has no `--wake-budget` flag.
**Every exit-2 is charged, `h-*` included** — the design's two clauses defeat each other,
since the exempt set is exactly the set that can wake a `Stop` hook at all, so a budget with
that exemption bounds nothing. It costs the human nothing structural: a halt reaches a
hooked agent through `PreToolUse` and the drive hold at the socket, neither of which is on
this path, and an un-woken row is still read at the next turn's `UserPromptSubmit` and by
the next explicit drain. Honest bound: the ledger is best-effort — a state dir that cannot
be written costs the budget, not the wake, so a read-only state dir silently disables it.

**"Unlisted principals never wake an agent" holds; "never surface" does not** (§8.4). The
`Stop` hook requires an accepted sender AND `kind != note`, so an unlisted principal's row
never reaches exit 2. Its row still appears in the `SessionStart`/`UserPromptSubmit`
metadata block, as numbers and a CLASS (`s-?`, `n-?`, `h-?`, `a-?`) rather than a name —
deliberately, because an agent never told it has mail cannot go and read it.

**The built `pending=` is not the design's count.** A2 defines it as "delivered rows past
the LISTED watermark that this reply did not carry", because an allowlist is the BRIDGE's
and the endpoint has no access to one — §11.2 deviation 7. A per-principal count would have
to be reported by the bridge, and no verb carries it. Coalescing and the kind ordering are
still **DESIGNED**: nothing implements either, and the bridge has no rate budget of its own
— it buffers records as fast as the broker delivers them. Delivery into the ring is bounded
per sender (§6.2), and that bound is what is actually load-bearing today.

---

## 6. Messaging

### 6.1 Addressing

To message an owner `O` as principal `me`, publish to `/f/<F>/in/O/me/<kind>` (seven
segments, §3.3). You need a cap whose filter matches that subject and whose principal
binding is yours: `rw,p=me:/f/<F>/in/*/*/me/*` ("I may talk to anyone, as me, any kind")
or narrower — the `<kind>` segment is the send ACL (`…/in/*/*/h-andrew/answer` grants
`answer` only). **The sender's identity is the one segment you cannot choose.** The
owner's bridge reads all lanes with one filter, `/f/<F>/in/<node>/>`, contained in its
own grant (`Filter::contains`, `subject.rs:226-248`).

A session behind a bridge holds no cap: its bridge publishes under the node's `<src>`
(`/f/<F>/in/O/<node>/<kind>`) with `from=<sid>` attested in the body (§4.3). The full
address of a session is `@s-<sid>@n-<node>`; a bare `@s-<sid>` is accepted only when
exactly one node advertises that sid **and** the sender's bridge has pinned that
(sid → node) pair on first sight. A second node advertising a pinned sid is a conflict and
is never routed — a node's cap covers its whole `pub/<n>/` subtree, so a rogue node *can*
publish a presence row for a sid it does not host; pinning stops that from becoming a route
into the rogue's own read lane. **Only `post --wait` answers `ERR ambiguous`.** Routing is
the bridge's knowledge and `post` is answered by the ENDPOINT before the bridge has seen
the message at all, so a bare `post` still answers `OK <id>` and learns the verdict later,
from `outbox sent … off=- reason=ambiguous` — which reaches a PARKED sender as
`ERR ambiguous` and reaches a non-waiting one only as a bare `off=-` on the `inbox` post
row. A sender that posted without `--wait` therefore learns the message died and not that
the fleet has a contested sid; surfacing `reason=` on that row is **DESIGNED**. A row
published in OBSERVER mode carries `observer=1` and is excluded from the advertiser set, so
opening a read-only observer cannot make every session it can see ambiguous — a grammar
element the design did not name, additive, and one that can only ever REMOVE a node from
the candidate set. Role addressing ("whoever runs codex on host 2") is **DESIGNED**: the
bridge publishes no `role=` or `detail=` on a session presence row at all
(`publish_session_presence` writes `inc epoch gen state hold holder attention [observer]`),
so `aterm-link ls` prints `-` for both and there is nothing to resolve a role against
(`role=` would be spoofable and `detail=` would not,
`docs/AGENT-EXPERIENCE-2026-08-26.md:667-668`).

### 6.2 Inbox and drain — the bridge path

The node's bridge runs one durable group
`SubscribeGroup{group=/f/<F>/cur/<node>/node/inbox, filter=/f/<F>/in/<node>/>}`
(`broker.rs:1873-1894` — the `SubscribeGroup` arm resumes from `log.group_start(&group)`
at `:1889-1892`, then runs one `tail_loop`). For each delivery it validates the subject shape (§3.3), computes
`from=`/`trust=` (§4.3), calls aterm `deliver <sid> off=<offset> from=<src> kind=<kind> …
text=<pct>` on its verb connection, and only after `OK <id>` does it `Commit{group,
upto=offset}` (`store.rs:810-823 BrokerLog::commit`) on its commit connection — `subscribe(self, …)`
consumes the client (`client.rs:540 subscribe`, `:627 subscribe_group`), so two
connections are the price and the client library hides it (§11.1) — and the broker now
caps simultaneously-open connections at `MAX_CONNS` (default 1024, `broker.rs:270`,
enforced on accept at `:1457-1475`, over it answering `Error 6 too many connections`), so
two-per-node is also a ceiling of roughly 512 bridges per broker. A post-restart
thundering herd is therefore a real reconnect concern, not only a presence one (§7, §14). A crash between `deliver` and `Commit` redelivers the
record; aterm's inbox ring dedups on `off=`, so the agent sees it once: exactly-once
*delivery into the endpoint* from exactly-once ingest + at-least-once cursor + an
idempotent sink — the broker's own stated boundary (`crates/astream-broker/src/lib.rs:37-39`).

**The ring.** 512 rows per session, drop-oldest, with a **per-sender quota** of 64
unread rows per `<src>`: the 65th is refused at `deliver` and the bridge records
`undeliverable re=<off> reason=quota` on the sender's lane, so one peer cannot evict the
human's unread `task` with a burst of `note`s; eviction is by (class, age) and never
evicts an `h-*` or allowlisted row ahead of anyone else's. Evictions of unread rows are
reported in the header (`dropped=<n>`), never silently.

**The watermark survives the endpoint.** `inbox seen <id>` advances the endpoint
watermark and pushes `EVENT <local> inbox-seen <id> off=<n>`; the bridge persists
`seen_off[sid]` in its state dir on every such event. On an instance relaunch or a
`session-created` with a known sid, the bridge refills the ring with `Fetch{from:
seen_off+1, /f/<F>/in/<node>/<sid>/>}` before the first `inbox` — the group cursor is per
node and already past those rows, so without this a SIGKILLed `aterm-gui` would lose
every delivered-but-unseen row. **The self-lane check:** a record on the node's own
lanes whose `<src>` is this node and whose offset the bridge never received in a
`PublishAck` is a forgery by a co-holder of the node cap; it is recorded `ev
undeliverable reason=forged-self`, never delivered, and the bridge raises `attention`.
Likewise a `PublishAck{deduped: true}` on a sequence the bridge has never sent is proof
of a co-holder: the bridge records `ev cap-compromised`, escalates, and rolls its
incarnation.

A turn-based agent drains with one verb at turn start: `aterm-ctl @self inbox` → rows;
`inbox get <id>` for a full body; `inbox seen <id> [handled|refused|deferred]` when
handled. The bus keeps the durable copy.

### 6.3 Inbox and drain — the direct path (humans' tools, services)

A principal that speaks to the bus itself (a phone tool, a headless service) drains
with `client::drain(sub, committer, group, max)` (`client.rs:721-726`) — the filter is
named one call earlier, on `Client::subscribe_group(group, filter)` (`client.rs:627`),
and the idle window with `Subscription::set_read_timeout` (§11.1, deviation 4) — and
acknowledges
with **one `ProcessAndProduce`**: `out_subject=/f/<F>/in/<sender-owner>/<me>/ack`,
`out_body="v=1 t= re=<off> state=handled|refused|deferred"`, `group=/f/<F>/cur/p/<me>/inbox`,
`upto=<off>`, `producer_seq` derived from `<off>`. The ack record and the cursor advance
land in one durable append; a retry after a killed turn returns `deduped=true` and
appends nothing (`store.rs:833-867 process_and_produce`; `broker.true-exactly-once-e2e`). The CLI prints the
broker's own `PublishAck{deduped}` back as `dup=1`, so the agent *sees* that
exactly-once held. **BUILT** primitive; helpers **BUILT** too —
`client::drain` (with `client::take` for a caller that must process before committing) and
`client::ack` — `broker.inbox-drain-ack-exactly-once` (R6).

**Where the idle window actually exists, and what a timeout mid-record does.**
`Subscription::set_read_timeout` is implemented per CONCRETE stream, not on the generic
`impl<S: Read + Write>`: `Subscription<UnixStream>` on Unix builds (`client.rs:993-1005`),
`Subscription<TcpStream>` (`:1007-1012`), and — behind the `aead` feature —
`Subscription<SealedStream<TcpStream>>` (`:1015-1030`), which is what
`connect_tcp_sealed`, `connect_tcp_handshake` and `connect_tcp_identity` all hand back,
so the §8.6 transports the fabric is told to deploy on are covered. On any OTHER stream
type (a boxed `dyn` stream, say) there is no idle window and the consumer bounds its own
socket through `Subscription::get_ref` (`client.rs:916`); before that helper existed a
sealed direct consumer had no way to bound the read and parked forever on an empty turn.
The stop is also **frame-atomic**: a timeout landing part-way through a record keeps that
record's consumed bytes on the subscription and finishes it on the next call, so the same
`sub` is safe to drain from again rather than desynchronised (the round-2 claim
`broker.drain-idle-window-frame-atomic`, §12). One consequence worth writing down: `asb drain
--tcp --key-file` no longer has to clone the raw `TcpStream` out of the sealed wrapper to
bound a read — the library expresses it (asb's own `SetTimeout`/`connect_sealed` fd-dup at
`asb.rs:465-512` still works and is not wrong, it is simply no longer the only way).

### 6.4 Request / reply and deadlines (stories B1, B5)

An `ask` published at offset `R` is answered by a record on the asker's inbox with
`re=R`. The offset is dense, unique, durable and broker-assigned — a correlation id
nobody can collide or forge. A turn-based asker does not hold the push digest, so it
must learn `R` synchronously: `post … --wait[=<ms>]` (default on for `ask` and `task`)
blocks until the bridge's `deliver <sid> landed=<post-id> off=<R>` and answers `OK <id>
off=<R>`; the endpoint keeps the (post id ↔ offset) table, every inbox row carries
`re=<off> re-id=<post id>` resolved through it, and `inbox` lists the session's own
un-landed posts as `post <id> to= kind= off=-` so an agent sees at turn start what is
still in flight. All of that is **BUILT (aterm)**, A2 (the endpoint's post/landed table and
`--wait`) and A3 (the bridge that publishes and reports the landing), with two answers the
design did not spell: with no bridge attached `post --wait` answers `ERR fabric
absent|disconnected id=<id>` at once rather than parking to a certain timeout (the post is
still queued and `inbox` lists it), and a post the bridge retires as permanently
undeliverable wakes the parked caller with `ERR undeliverable`.

A deadline `dl=` is advisory. The design has the asker's bridge **record** the verdict as
`kind=expired re=R` on the asker's own lane when it sees the deadline pass with no answer
(a nondeterministic input made a record, so replay reaches the same verdict without a
clock), and mark a late answer `late=1`. **Neither is built.** `dl=` is carried end to end
— accepted on `post`, encoded in the body, forwarded on the `deliver` line, printed on the
`msg` row — and nothing anywhere watches it expire: no bridge holds a deadline timer, no
`expired` record has ever been published, and no `late=1` has ever been set. `expired` is a
`deliver`-accepted kind and one of the two `VERDICT_KINDS` a verdict may not itself earn,
which is the whole of its implementation. **DESIGNED.**

`undeliverable` IS a recorded verdict and is **BUILT (aterm)**, A3: the receiving bridge
refuses a malformed subject, a `<sid>` it does not host, or a forged self-lane record,
publishes `ev undeliverable off=<n> reason=<token>`, and — where there is a lane to answer
on — appends a `kind=undeliverable` row for the sender. What it does NOT do is the
presence-consulting half the design describes: there is no `state=exited|offline` token and
no sender-side "not delivered yet" verdict, because an undelivered message simply stays on
the log for a node that reconnects, which "fails the old wiring closed" only for local edges
(`docs/OPERATOR.md:191-193`), never for its mail. One honest bound the design did not carry:
A3's sender notice assumes an `s-*` sender is hosted by THIS node, so an undeliverable
notice aimed at a session behind another bridge lands on the local lane and is recorded
`not-hosted`. `ForkSubscribe{fork_at=R}` replays the exchange with the ask record
swapped — recorded divergence only; the recorded answer is unchanged (`broker.rs:1782-1872`).
The snapshot now ends with an explicit `Mark` before the EOF (`:1863-1870`), so a caller
using `Subscription::recv_event` can tell "snapshot complete" from "the connection dropped
mid-history" — a bare EOF could not. `Subscription::recv` still SKIPS the mark, so the
shipped shape is unchanged.

### 6.5 Exactly-once where it matters (story B6)

| Hop | Mechanism | Status |
|---|---|---|
| sender → log | `(producer_id, producer_seq)` dedup, rebuilt on restart (`store.rs:575-603`); the producer id is cap-bound (§8.2); the bridge persists `producer_seq` **before** publishing and derives its incarnation from local state and its own last presence row (§7) | **BUILT** ingest; the bridge discipline is **BUILT (aterm)** A3 — the sequence is reserved durably before the publish and reused verbatim on every retry, because `outbox` is a peek and a fresh sequence would put a second copy on the bus |
| log → node | durable group cursor, commit after `deliver OK`; per-session `seen_off` persisted for refill | **BUILT** cursor and drain/ack helpers (`broker.inbox-drain-ack-exactly-once`, R6); the bridge that uses them is **BUILT (aterm)** A3 (`bridge_e2e`) |
| node → agent | aterm inbox ring dedups on `off=`; `seen` watermark | **BUILT (aterm)** A2 — test-cited (`deliver` idempotent on `off=`, the two watermarks) |
| log → direct consumer | PnP ack: record + cursor, deduped | **BUILT** primitive (`store.rs:833-867`) |
| bus → PTY (`term/in`) | aterm now accepts `send\|key\|feed-bin\|turn … id=<epoch>:<producer>:<seq>` and keeps a per-session, per-producer high water: at or below it writes nothing and answers `OK dup=1` in the verb's own framing; an attempt whose reply was not `OK` leaves the mark UNKNOWN and a retry gets `ERR in-doubt seq=<n>`, terminal for that sequence and never replayed; a key from a dead incarnation is `ERR epoch`. The bridge brackets the feed — journal the offset, session and key BEFORE the verb, publish the outcome as an `ev` after it, clear the journal only then — so a `SIGKILL` inside the window is resolved on restart by re-asking with the SAME key. `ERR busy` and `ERR denied` release the mark; nothing else does, `ERR usage` included, because `cmd_turn_guarded` can answer USAGE *after* the text was typed. The old stand-in `tools/aterm-astream-bridge:172-175` remains **HAND-RUN** and is evidence for nothing (`DESIGN-drive-pipe.md:416`). | **BUILT (aterm)** A6 (`cargo test -p aterm-gui feed_idempotent`) + A7 (the bridge journal, `fleet_comms_e2e`) |
| bus → PTY at the astream-host seam | `Driver::drive_input` refuses a duplicate before any write (`driver.rs:53-69`, whose guard is `Session::precheck_input`, `session.rs:258-273`, over `is_duplicate`, `:246-250`) then commits with `Session::apply_input` (`session.rs:279-286`) — the *untokened* one, at `driver.rs:67`, the boundary `control.rs:25-29` states | **BUILT** `term.drive.interactive-exactly-once` |

### 6.6 Handoff and drive-with-consent (stories B3, B4, B11)

The keyboard has one holder. On the bus that is the last-value
`/f/<F>/pub/<node>/<sid>/control` (`holder=`), written only by the session's node — the
wire twin of `ControlToken` (`crates/astream-engine/src/control.rs:38-49` — a token that
is deliberately neither `Copy` nor `Clone`, and that the engine now **enforces at ingest**:
`Session::apply_input_as` / `apply_input_caused_as` refuse a non-holder with
`EngineError::NotHolder` before the log is touched, `control.rs:6-8`, `session.rs:292,337`.
The honest boundary is stated in the same file, `:25-29`: the plain `Session::apply_input`
takes no token and the astream-host `Driver` still calls that one). On aterm it is
`lease` (`help_catalog_full.txt:38`) and `turn`'s hard arbitration (`:37`). The bridge
keeps them equal with one pure policy, `decide_control(state, event)`:

| Event | Rule |
|---|---|
| `claim` by an `h-*` principal (an inbox `control` message carrying the session's `epoch=`, or a local human gesture) | granted unconditionally; the previous holder gets `control lost` in its inbox |
| `request` by an agent | granted iff `holder ∈ {none, expired}` and no halt; else a pending row the holder's next wake shows. **`expired` is OBSERVED, not timed** (A5): a SESSION holder is expired once no node's roster row says `state=live` for it — the same `Last` read routing uses — and a human or a service never expires on its own. A TTL on the retained `control` row would mean republishing it per held session per renewal period, forever. The bridge acts on a pending row by publishing it and telling the holder and nothing else: no timeout, no automatic promotion, no verb for a human to read the queue |
| `release` by the holder; `grant <p>` by the holder or an `h-*` | holder = none / `<p>` |
| local: an unaccounted `status revision=` advance with no bus `term/in` in flight | `holder=human? evidence=unaccounted-change` — the conservative pause (`docs/RFC-operator-2026-08-15.md:297-301`), labelled inferred. **Two honest bounds, both measured.** It OVER-fires: `status revision=` is the session-status CLASSIFIER's revision and moves on ordinary program lifecycle, not only on somebody typing. And it is a SAMPLER of an EDGE, so it can miss entirely rather than late — the classifier publishes a phase only while the thing that caused it is still true, so a command shorter than the sampling period is never seen at all. The window was narrowed to aterm's own 250 ms classification interval, on its own deadline and over HELD sessions only (`aterm-link/src/bridge.rs` `LOCAL_OBSERVE`), which is as fast as `status` can produce a new verdict; sharing the 2 s roster deadline had also phase-locked the sample to the lease renewal, making a person who typed just after one invisible for two seconds reproducibly. **Narrowed, not closed** |
| local: `lease acquire` by a socket driver | mirrored as `holder=owner-cli:<h>` |

**The one rule, stated once and obeyed everywhere:** the *only* records the bridge ever
converts to PTY input are `/f/<F>/term/<node>/<sid>/in/<src>` records, applied iff
`<src>` equals the `control` holder **at apply time** ∧ `hold=0` ∧ the body's `epoch=`
equals the live session's launch nonce ∧ (`gen=` absent or equal to the live
`content_seq:fp16`). `answer`, `task`, `control` and every other `in/` kind are inbox
rows, full stop — a `re=` is dense and guessable and a `gen=` is observable from
presence, so a body that could *trigger* keystrokes on their strength would let any
lane-writer drive a worker. A keystroke replayed after a human claim is refused (the
check is at apply, not send; rejected attempts leave no `In`, exactly as
`term.fleet.control-handoff` proves) and recorded `ev refused reason=holder|hold|epoch|gen`.
The bridge mirrors the row into aterm's own lease — `lease acquire
holder=fabric:<principal> ttl=30000`, renewed at TTL/3 while the row stands
(`LEASE_RENEW`) — so every local driver sees `driving=lease:fabric:h-andrew` in `who`
(`control_session.rs:245`) and a competing `turn` gets `ERR busy`
(`help_catalog_full.txt:38`). §11.2 calls `lease … holder=fabric:*` a `BridgeOnly` verb;
**no such gate exists** — `cmd_lease` accepts any printable holder from any scope, so an
Owner-token client can set `holder=fabric:h-andrew` itself. That is not an escalation
(Owner scope can already type arbitrary bytes into the PTY) but it does mean the
`fabric:` prefix is a convention, not an authority. **DESIGNED.** The `gen=` fingerprint
the design leaves undefined is, in the built code, `fp16` = FNV-1a-64 over the `rows`
array of one `text --json` frame rendered as 16 hex chars, compared as an opaque string
and read in one round trip with the `content_seq` it is joined to; it is deliberately NOT
byte-identical to aterm's own `turn` `hash=`, which hashes the plain screen text, so the
two must never be compared. Honest bound, unchanged:
raw `send`/`key`/`feed` are advisory against a lease (`:38`), and a human at the physical
keyboard is indistinguishable at the byte level (`tools/aterm-manager.sh:27-29`); exact
attribution is aterm's Phase-2 input provenance, **SEED**, not claimed here.

A human's answer from a phone (B4) is therefore **two typed, cap-gated steps or none**:
a `control claim` (an `in/…/h-andrew/control` record; `<src>` is cap-forced) followed by
a `term/<n>/<sid>/in/h-andrew` record carrying `epoch=` (and, for an approval prompt,
`gen=` so a stale screen cannot be answered — `docs/OPERATOR-EMBEDDED.md:253-256`), or an
`answer` inbox row the agent reads as text. The bridge never applies approval
keystrokes on a message's behalf (`:295-302`).

### 6.7 Nested aterm relays up without borrowing (story B9)

An inner aterm's bridge is its own node only when the human mints it a cap — HMAC caps
cannot be attenuated by a bearer, so a spawner cannot mint for its child; the consent
moment is explicit (the spawner `post`s `kind=ask text=cap for n-… over /f/<F>/…`, the
human runs `asb mint` and places the cap as a 0600 file inside the child's sandbox root
— out of band, never a message, never env) — and only when the inner can reach the
broker. Otherwise the inner is **relayed**, over one of two channels: (a) the inner's
bridge speaks to the *outer* aterm's `post` as the outer session that hosts it
(`aterm-ctl @self post … via=<inner sid>` from inside that session, Owner-scoped as any
in-session client is), or (b) when the sandbox reaches no socket at all, the file
mirror (A9): the inner writes `<root>/.aterm/<sid>/outbox.ndjson` — **the sid is in the
path**, matching §11.2's A9 row, because a bare `<root>/.aterm/outbox.ndjson` is ambiguous
the moment an instance hosts more than one session, and because `mirror --session <sid>`
is what confines a root to one agent. The relay is expressed by the LINE's `"via"` field,
never by the file's location. The outer bridge posts each line with `via=`, and the plane
also carries `<root>/.aterm/<sid>/sent.ndjson` (one receipt per outbox line — aterm's own
reply header, or the reason the line was refused) and `.cursor` (consumed bytes), neither
of which the design named: without a receipt a confined agent cannot learn its post id or
the `off=` it needs to recognise the answer that comes back as `re=`, and `inbox`'s `post`
rows disappear once the post lands. Either way the outer publishes under its own cap with
`<src>` = its session and `via=` appended. **A relayed message is always delivered as
`kind=note demoted=<k> trust=relayed`, whatever the recipient's allowlist says** — `via=`
is a claim on the relayer's word, never authority, so it can never bypass a budget or an
allowlist or become a `task`/`control`/`answer` (`aterm-nest`'s rule, `main.rs:7-11`,
applied to messages). The mirror does not implement that rule a second time: the `via=`
claim rides the ordinary `post` verb and the demotion is computed where it already is, in
the RECEIVING bridge's `classify_kind`, which demotes on `via.is_some()` before it consults
`--accept-from` at all. Two consequences of the built shape that the design did not state:
with no `--session` **every** session the instance hosts is mirrored into the root, so an
agent that owns the root reads its neighbours' inboxes, and the mirror runs `inbox seen` on
their behalf; and the inbound side reads `inbox --peek`, so a row evicted from the 512-row
ring between two polls (default 250 ms) never reaches the file and nothing in the file says
so. The inner's sessions share one fleet identity (the hosting session).
Attenuable (macaroon) caps stay a named seed (§14).

---

## 7. Presence and liveness

Presence is three derived facts, none of them a heartbeat storm:

1. **Roster rows** — `/f/<F>/pub/<owner>/presence`, republished by the bridge only when
   `status revision=`, `who`, `sessions` or `meta` change (the revision gate the operator
   brief uses, `docs/OPERATOR.md:91-92`), read in O(members) via `Last`. A row survives
   the session's exit as `state=exited` with its last `attention=`, which is how an
   escalation outlives the worker (story A2 — today the ledger dies with the session,
   `docs/AGENT-EXPERIENCE-2026-08-26.md:250-262`). The row carries `epoch=` — the
   session's launch nonce as hex, verbatim. The nonce is **public** anti-spoof state,
   "published as `meta.nonce`" (`crates/aterm-session/src/id.rs:49-55`), so the epoch is a
   freshness fence, not a secret, and needs no hash: a relaunch is visible on the bus, and a
   `term/in` or `control` record minted against the old epoch is refused (§6.6). **The
   bridge reads it off the Owner-only `sessions` roster row's `nonce=<hex32>` field, not via
   `whoami`** (`control_session.rs:176`, the row; A3 added the field). `whoami` reports the
   CONNECTION's own session and refuses a selector — the Owner-only arm answers `ERR denied`
   for `@<sid> whoami` — and the bridge's connection is not a session's, so the design's
   original reading was not implementable as written.

   **What the built row actually carries**, against §4.2's list: `v= t= inc= epoch= gen=
   state= hold= holder= attention=` and, in observer mode, `observer=1`
   (`publish_session_presence`). **Ten of §4.2's fields have no writer**: `role`, `detail`,
   `phase`, `driving`, `watchers`, `title`, `host`, `pid`, `parent` and — on a SESSION row —
   `fabric`. `host=`, `pid=` and `fabric=` are on the NODE's own presence row instead
   (`bring_presence_up`), deliberately, since `fabric=` on a session row was a constant
   nothing could falsify. `aterm-link ls` prints `-` for the rest rather than dropping the
   column, and adds three §7 does not name because each has a writer and a reader: `gen=`,
   `observer=` and `epoch=`. `serve` has no `--presence-title` and no `--exited-keep`, so
   `title=` is unreachable and an `exited` row is never collapsed into an `ev`; `state=exited`
   itself IS published. Those ten fields are **DESIGNED**.
2. **Node liveness** — `/f/<F>/pub/<node>/node/presence` with `state=live inc=<n>`, and a
   **`Will`** registered on the bridge's publisher connection and re-registered on every
   reconnect: `Will{producer_id, producer_seq=(inc<<32)|0xFFFF_FFFF, subject=…/node/presence,
   body="v=1 … state=gone inc=<n>"}`. The will's sequence is the **reserved top** of the
   incarnation's sequence space, so no ordinary publish of that incarnation can collide
   with it. When the connection ends for any reason — a clean EOF or a SIGKILLed
   bridge, both of which the connection thread observes (`broker.rs:1529-1536`, where a
   clean EOF and an I/O error are distinguished inside `serve_conn`, under `handle_conn`
   at `:1400`) — the
   broker enqueues the will as an ordinary publish, **fenced**: it fires only if no
   record from that producer with a *higher* sequence has landed (a per-producer
   high-water map beside `dedup`, rebuilt on open). A graceful shutdown publishes the
   reserved key itself first, so the will dedups to a no-op: **exactly-once goodbye**.
   **The incarnation rule, at the broker:** a bridge that reconnects after a transient
   drop publishes `state=live inc=n+1` first — every sequence of incarnation n+1 is
   above incarnation n's reserved top — so when the half-open old connection finally
   dies its will is *suppressed structurally* and appends nothing. No reader fold is
   needed, which matters because `Last` returns one record per subject and a reader
   could never see a `live` hidden behind a later `gone`. `inc` is persisted locally; on
   start the bridge uses `max(local, Last-of-own-row) + 1` and queues its publishes until
   that first `Last` succeeds, so a wiped state dir or a broker outage never forces a
   guess. Wills are persisted as hidden `/a/will` records (`store.rs:45 WILL_SUBJECT`,
   excluded from `dedup`, `last` and delivery like `/a/commit`) and rebuilt on open
   (`store.rs:1294-1307 pending_wills`). **BUILT** `broker.will-fires-exactly-once` (R5).
   **Seven things the code pins that the prose above leaves open:**

   a. The firing on connection end is **fire-and-forget** — the connection thread does not
      wait for the ack (`broker.rs:1439-1445 fire_will`) — so what makes the goodbye
      exactly-once is the durable `/a/will` record plus the next open's firing, not the
      connection thread.
   b. On open at most **ONE will per producer id** — the most recently registered — is
      re-fired.
   c. **One producer id per connection.** "One per connection, a second replaces" is
      enforced in memory, but the durable record of the will it replaces stays on the log
      and the re-firing at the next open keys by PRODUCER. So a second `Will` naming a
      DIFFERENT producer id is refused by name (`broker.rs:1981-1994`) rather than leaving
      two live entries, one of which the connection had explicitly taken back.
   d. **The distinct-subject bound is applied at REGISTRATION, against the subject the
      will would publish to** — not against the hidden `/a/will`, which is outside the
      bound (`store.rs:1146-1203 stage_will_register`). A will whose subject would be its
      producer's 4097th distinct one can never be delivered, and registration is the one
      moment a client is still listening. The FIRING is correspondingly **exempt**
      (`store.rs:1222-1250 stage_will_fire`, through `stage_publish_bounded`): its ack is
      discarded, so a bound applied there would lose the goodbye silently and re-fail it at
      every later open. **And a registration that PASSES reserves that subject against the
      same budget** — the round-3 addition, without which the firing's exemption was a
      hole: checking without reserving read the same count for every live connection, so N
      connections registering wills for N distinct new subjects all passed and their
      firings took the producer N subjects past the cap. The reservation is durable and is
      rebuilt at open from the log's own `/a/will` records. Honest boundary: it is
      conservative in the direction that keeps the cap — released when a record on that
      subject lands under that producer, and NOT when a will is superseded for a different
      subject, fenced by a later record, or beaten to the subject by another producer — so
      such a producer reaches its cap sooner than its landed subjects alone would say. The
      over-count is never more than the budget itself, since a registration that would
      exceed it is refused.
   f. **A sequence at or above `ACK_SEQ_BASE` is refused at registration**
      (`StageErr::SeqReserved`, `store.rs:1156`), and acks are excluded from the
      per-producer high water the fence reads (`store.rs:594`, `:1268`, `:1420`). Both
      halves are needed: without the second, one ack fences the will forever; without the
      first, a will parked in the reserved half would be permanently *unfenceable*. §11.1
      boundary 3 states the failure this replaced.
   g. **A registration is acked on the leader's own LOCAL commit, not on the quorum
      watermark** (`broker.rs:2469-2477,2585-2611`, the `local_only` flag on
      `WriteKind::WillRegister`). The `/a/will` record is broker-internal bookkeeping no
      subscriber ever sees, and its acknowledgement decides whether the connection keeps
      the will IN MEMORY — so it must answer for the record's own fate, not for a
      follower's. That is what keeps the connection's in-memory will and the log's
      `/a/will` record from ever disagreeing about whether the will exists. **The cost,
      written down:** on the Replicated tier the goodbye is only as durable as the leader's
      own log — lose the leader before a follower takes the `/a/will` record and the will
      is lost with it. The alternative, gating the ack on the quorum, is what produced a
      forged death notice for a live node: a will the log held while the client was told it
      did not, fired at the next open for a producer that believed it had registered
      nothing.
3. **Session lifecycle** — `EVENT * session-created/session-exited` from the Owner-only
   `sessions` stream (`subscribe.rs:1127-1144`, journal-backed, so a sub-tick
   spawn-and-exit surfaces, `:3923`) becomes the node's `ev`, with `closing reason= by=`.

`aterm-link ls` is the cross-host `ls`: `Last{/f/<F>/pub/*/*/presence}` →
`<node> <host> <sid> state= inc= role= detail= driving= holder= hold= fabric= attention=`.
No filesystem scan, no `dial`, no saved peer names.

**Honest bounds.** Liveness of a *session* behind a live bridge comes from aterm's
`sessions`/`exited` events, not the will. A half-open TCP connection is noticed only when
the broker next writes or probes it (`broker.rs:2761` — the park-branch probe, `:2795` —
the zero-write probe, `:2807 peer_gone`, under the 50 ms read / `STREAM_WRITE_TIMEOUT`
30 s write timeouts set at `:2730-2731`), so a `gone` can lag a
cable pull by the OS's TCP timeout — the fence keeps that lag harmless, it does not
shorten it. **A broker restart is a presence epoch — on a broker that OWNS its log:**
every connection dies with no connection thread running, so on open a broker that owns its
log fires every persisted will that is neither deduped, nor fenced, nor held on a log this
broker is a REPLICATION TARGET for — a bridge that reconnects publishes `live inc+1` within
one round trip, a bridge that died during the outage is marked `gone` exactly once, and in
between every node reads `gone` (a sender in that window records `undeliverable
state=offline`, which delivery on reconnect supersedes). The alternative — never firing
— would leave a node that died while the broker was down `live` forever.

**The replica exception, which is durable and irreversible.** A follower fires NOTHING on
open: `let pending = { let log = shared.log.lock().unwrap(); if log.is_replica() {
Vec::new() } else { log.pending_wills() } }` (`broker.rs:820-827`), and `stage_will_fire`
refuses on a replica independently (`store.rs:1224-1232`, `StageErr::Replica`). The wills a
follower's log holds are the LEADER's; they fire there. Firing one on the follower would
append a record the leader does not have — a forged death notice for a live node, a log
that is no longer a prefix of the leader's, and a `Diverged` refusal that fences the link
for good. "Whose log this is" is therefore a durable property of the log itself, a
`<log>.replica` sidecar beside it (`store.rs:423-427 replica_marker_path`, written and
fsynced by `:721-744 mark_replica`, read before a single record is decoded at `:528-537`),
so a follower restarted through plain `Broker::open` is still a follower. **What sets it:**
a log that takes its first replicated record while it is STILL EMPTY declares itself (the
shipped follower bring-up, `store.rs:1036-1125 stage_replica`), or an operator declares it explicitly with
`Broker::open_replica` / `BrokerLog::declare_replica`. **Where that is decided moved in the
round-3 pass, and it had to.** The rule admitting a replicated hidden record only onto a
log that is a replica or still empty used to live on the CONNECTION thread, which reads the
PROMOTED head and then drops the lock while the append happens later in the writer — so a
record pipelined on the same connection was staged but not promoted in between, the guard
read "still empty" about a log that already held a record of its own, and a hidden `/a/will`
landed on a log the broker OWNS, to be fired at its next open under an arbitrary producer
id, outside the capability matrix entirely. It is now one predicate, `declares`, computed
ONCE inside `stage_replica` under the lock that appends, and it is both what admits the
hidden record and what marks the log, so the two can no longer disagree. The
connection-thread check survives as a cheap early refusal that says the same sentence. Two
more orderings came with it: a `Replicate` refused for SIZE stages first and marks second,
so it leaves an ordinary log ordinary, and pure commits stay exempt so leader replication is
unchanged. A log that ALREADY HOLDS RECORDS is
**not** converted by a replicated record accepted beside them: accepting one says nothing
about whose log it is and any reader can construct the frame — a byte-identical echo of a
record already on the log used to flip the bit while appending nothing at all, silently
disabling will-firing for every producer on that broker. So a follower seeded from a COPY
of the leader's log must be DECLARED. **The marker must travel with the log**: back a
follower up with `cp broker.log …` and leave `broker.log.replica` behind, and the restored
broker believes it owns the log and fires every will the leader's spine holds. **What
`open_replica` does and does not enforce:** it blocks will-firing, and that is the whole of
it (`broker.rs:758-770 open_replica`). A replica's listener still accepts client writes — a
`Publish`/`Commit`/`ProcessAndProduce` that reaches it lands at the FOLLOWER's own next
offset and permanently diverges it from the leader, so the leader's next ship to that
offset is refused `Diverged`, the link is fenced, and with quorum == follower count the
cluster goes write-unavailable. **Do not expose a replica's listener to publishers.**
**The undo is the file**, by design — there is no undeclare verb, because the declaration IS the file:
`rm <log>.replica`. The first write says so on stderr, naming the log and the marker.
Operationally the trap runs the other way too: resetting a follower with `: > broker.log`
leaves the marker in place (`open_inner` clears it only when it CREATED the file,
`store.rs:528-537`), so the node restarts as a standalone broker whose wills silently never
fire.

**The reconnect is not free:** `MAX_CONNS` is enforced on accept (`broker.rs:1457-1475`), so a herd of
two-connections-per-node bridges racing back after a restart can be refused with
`Error 6`, delaying the `live inc+1` that suppresses a fenced will; a bridge therefore
reconnects with jittered back-off and opens its publisher connection *before* its drain
connection (§14).

---

## 8. Security

### 8.1 Threat model

Assets: the fleet's keyboards (write-input), its screens (every keystroke ever typed —
a secrets store, `docs/DESIGN-drive-pipe.md:458-459`), presence rows, the humans'
attention, and the audit log. The stated adversary, as in both repos, is a
prompt-injected cooperating agent **with a shell**, same uid as its aterm — not a
hostile same-uid *user* (`docs/RFC-operator-2026-08-15.md:284-287`). That adversary
already holds aterm's Owner token: an in-session `aterm-ctl` reads the instance's 0600
token file (`crates/aterm-ctl/src/lib.rs:46-48,2771-2777`; `docs/INTROSPECTION.md:144-148`),
so nothing on this instance may rest on Owner scope.

| # | Threat | Today | Fabric mitigation | Residual |
|---|---|---|---|---|
| T1 | Prompt-injected worker with a shell tries to halt the fleet, lift a halt, task peers, or drive a peer | prompt-enforced only (`OPERATOR.md:221-224`) | no fleet cap; `hold`/`deliver` are `Scope::Bridge`, a connection no token unlocks (§11.2); an unlisted `task` is demoted; `term/in` needs `control` = an `h-*`; killing the bridge fails **closed**; its own tool calls are stopped by `PreToolUse` | it can read the node's cap in the bridge's state dir (same uid) and speak **as the node** to other nodes — `from=s-…@n-…` is trusted exactly as far as node `n`'s uid; it can `send` into siblings as Owner can today (aterm's boundary); Codex-sandboxed workers reach neither (T13) |
| T2 | Spoofed provenance (`from=h-andrew`) | nothing stops it | `from` is the cap-forced `<src>`; body `from=<sid>` is honoured only under a node's lane; `deliver` is Bridge-only, so no Owner client can forge a row; the self-lane check refuses records under the node's own id it did not publish | a node can attribute a post to any of its own sessions, and a same-uid shell can be the node (T1) |
| T3 | **Dedup-key poisoning** | possible (`store.rs:902 staged_or_durable_dup`; `producer_id` is still client-chosen on `Publish`, `proto.rs:36-42`) | producer id broker-derived from the grant's principal (SHA-256), enforced before staging; a collision with another principal is refused at attach; a bridge detects a co-holder by a `deduped=true` on a fresh sequence | unbound caps (the fleet root) publish under any key — the god cap |
| T4 | Capture and replay of a cap | bearer tag inside the stream | `Attach` is a proof of possession over a per-connection nonce (§8.2); the tag never leaves the client; a captured proof is refused on any other connection, sealed or UDS | none for the attach; the PSK is shared by every host (T10) |
| T5 | Confused deputy through a relay | messaging does not exist | relayers publish under their own cap; `via=` is untrusted and always demotes; a node's lane cap cannot reach another node's `pub`/`term` | hop-trusted; hash-checkable only if `term/out` is on the log |
| T6 | Stale principal after relaunch | nonce fail-closed for edges (`edge.rs:432`); nothing on the bus | `epoch=` mandatory on `term/in`/`control`; mismatch refused and recorded | — |
| T7 | Agent impersonates its human | `role=` is spoofable | human authority is a cap the agent's process does not hold — passed to tools by `--cap-file` (0600) or keychain, **never argv**; `post` refuses `Scope::Edge` | a same-uid process on the *human's* machine can read the human's 0600 file — aterm's boundary |
| T8 | Offset forcing | closed (`broker.rs:2288` — `cap_authorized`'s `Commit` arm is scoped to the group as a subject the cap must grant) | groups live under the owner's `cur/` subtree; a read-only cap cannot commit | — |
| T9 | Wake thrash / attention DoS / eviction of the human's own rows | script counters (`aterm-manager.sh:227-228`) | per-recipient budget on every egress; unlisted principals never wake; per-sender ring quota (64) with class-ordered eviction; barrier acks only to accepted issuers | log flooding by a cap holder (a per-cap rate limit is DESIGNED) |
| T10 | MITM / eavesdrop on TCP | sealed PSK wire | strengthened since the sealed rung: XChaCha20-Poly1305 with a per-connection handshake — each side sends a random hello in the clear and every record's AAD is `hello_client ‖ hello_server ‖ direction ‖ seq`, so a record opens only on the connection, direction and position it was sealed for, and a peer without the key is refused inside the handshake; the cap no longer rides inside it | on the PSK transport, **one key per broker is a boundary shared by all members, not a per-peer identity**. Both gaps are now closable in astream and a fabric deployment SHOULD close them: the `handshake` feature adds a forward-secret X25519 agreement, and the `identity` feature replaces the shared secret with mutual static public-key identity (pinned host key, allow-listed client). Binding a node's fabric principal to its identity key is DESIGNED (§8.6) |
| T11 | Broker compromise | total | none structurally — HMAC means verify = mint | total; asymmetric caps are a vetted-dep decision |
| T12 | At-rest exfil of the log, now holding messages **and presence** | mitigable, opt-in: the `at-rest` feature (`Broker::open_encrypted`) seals each record's payload and subject on disk (`broker.log-encrypted-at-rest`); `anti-rollback` refuses a log truncated below its authenticated watermark (`broker.log-anti-rollback`); `retention` compacts old records (`broker.log-retention`). A default broker writes plaintext | `detail=` is aterm-sanitized; `title=` opt-in; `attention=` capped | total on a plaintext broker; with `at-rest`, record count, sizes and timing stay visible, and the key-holder reads everything |
| T13 | Sandboxed agent cannot reach a socket outside writable roots (Codex, `AGENT-EXPERIENCE…md:305-320`) | `ls` lies | the agent never needs the *broker* socket; the aterm socket is unreachable too, so Codex is **RED** on the socket path and its path is the file mirror (A9) | — |
| T14 | Hostile same-uid *user* | out of scope (both repos) | out of scope | total |
| T15 | Sid hijack (a rogue node advertises a victim's sid) | — | TOFU pin per sender; conflict → `ERR ambiguous`, never a route | a sid first seen from the rogue is pinned to the rogue — the human sees `✗ conflict` when the real node appears |
| T16 | Injection through the wake path (hooks) | — | hooks carry **metadata only**, rebuilt field by field from a closed vocabulary rather than forwarded from the endpoint's reply — `holder=` becomes a class, `via=` a hop count (§8.4); bodies are read only by an explicit call the agent makes; an unlisted principal can never WAKE an agent | its row still surfaces in the metadata block, as numbers and a class rather than a name (§8.4); natural-language injection inside an accepted principal's text is not neutralized |
| T17 | Unauthenticated flood on the broker's accept path (idle half-open connections, a trickled length prefix, thread + buffer exhaustion) | **closed by the audit pass**: a first-frame timeout closes a connection that never completes one frame while leaving an established quiet producer alone, and simultaneous connections are capped (`MAX_CONNS = 1024`, `broker.rs:270,1457-1475`; `Error 6`), proven in `broker.tcp-transport`; the sealed acceptor adds a pre-authentication deadline and a concurrent-handshake cap (`broker.rs:1197-1277 serve_tcp_with` — the in-wrap counter at `:1234`, the deadline at `:1240`) | unchanged — the fabric adds connections (two per bridge) but no new accept path; the cap is the reconnect ceiling §6.2 and §7 name | a cap holder can still flood the *log* (a per-cap rate limit is DESIGNED, T9) |

### 8.2 Capabilities: the grant string, a proof-of-possession attach, and a keyring

Three changes to the built model; the `Attach` wire body is reused unchanged
(`proto.rs:81`: a string and a byte vector) and its meaning changes.

**The grant string.** `mint(secret, filter)` validates the filter and tags the raw
string bytes (`cap/lib.rs:270`). A *grant* is a filter with an optional prefix before
the leading slash:

```
grant := [ ("rw" | "ro") [ "," "p=" <principal> ] ":" ] <filter>
   e.g.  /f/F/pub/>                                  = rw, unbound   (every existing cap, unchanged)
         ro:/f/F/fleet/>                             = read-only
         rw,p=n-a1b2c3d4e5f60718:/f/F/in/*/*/n-a1b2c3d4e5f60718/*
                                                     = read-write, only as producer_id_of("n-a1b2…")
```

`mint` validates the `<filter>` half with `Filter::new` and tags the **whole** grant
string with the same HMAC — the construction and the RFC 4231 vector are untouched.
Because `Filter::new` rejects any string not starting with `/` (`subject.rs:150-152`), a
prefixed grant can never parse as a filter and a filter can never carry a prefix; `:`
cannot occur in a principal, so `split_once(':')` is unambiguous. A bare filter means
`rw`, unbound, so every cap minted today verifies unchanged — but **`asb mint` requires
an explicit mode** and mints the UNBOUND read-write grant only under `--legacy-unbound`
in EITHER spelling (`/f/F/>` and `rw:/f/F/>` parse to the same authority, so the gate
reads the parsed grant, not the leading character), and a guarded
broker logs every attach of an unbound rw grant at warn level: the footgun stays out of
the common path. `Grant::parse`, `mode_of` and `producer_id_of` are the only new
parsers, in `astream-cap`, still `sha2`-only.

**Proof-of-possession attach.** A bearer tag sent inside the stream is the wrong shape
for the halt authority: every fleet host holds the PSK, so any host can open any other
host's stream and lift the tag out of it. So the tag **never leaves the client**: the
connection first sends `Hello` and receives `Nonce{32 random bytes}`; `Attach{grant,
proof}` then carries `proof = HMAC-SHA256(tag, nonce ‖ grant)`; the broker recomputes
`tag = HMAC(secret, grant)` and verifies the proof with a compare that folds all 32 bytes,
with no early exit on the first differing byte (`cap/lib.rs:257 ct_diff`, `:335
verify_attach`) — a structural property asserted in `astream-cap`, not a timing
measurement; a wrong-length proof is decided on the length alone, which the wire has
already revealed. Zero new
dependencies (the same `sha2`), the attach is channel-bound to the connection for free,
and a captured `Attach` frame replayed on a second connection is refused. A guarded
broker refuses an `Attach` with no preceding `Hello`; an unguarded broker answers both
anyway so one client works against either. `Client::attach` does the round trip, so
every in-tree caller is unchanged.

**Keyring.** `Attach` *appends* to the connection's grants (a duplicate grant string
replaces; at most 16 — `MAX_KEYRING`, `broker.rs:198`) instead of replacing
(`broker.rs:1523` the ring itself, `:1567-1591` the guarded attach and `:1592-1603` the
gate it feeds, `:1605-1622` the unguarded acknowledge-and-enforce-nothing path), and is
**acknowledged**: `Mark{next: head, head}` on success (the client learns `head` for
free), `Error{5, …}` when the proof does not verify or the principal's derived id
collides in the binding table — closing the silent-rejection gap where a refused cap
surfaces only on the next request (`client.rs:238 attach` now reads the answer). This and `Hello` are the
behaviour changes to existing verbs, and the reason `broker.cap-enforced-on-attach`'s
test is touched in the same commit.

Authorization is per request, existential over the ring:

| Request | Requires |
|---|---|
| `Publish{subject, producer_id}`, `Will{…}` | ∃ **rw** grant: filter matches `subject` ∧ (unbound ∨ `producer_id_of(principal) == producer_id`) |
| `Commit{group}` | ∃ **rw** grant: filter matches `group` |
| `ProcessAndProduce{out_subject, producer_id, group}` | the `Publish` rule on `out_subject` ∧ the `Commit` rule on `group` |
| `Replicate{seq, producer_id, subject, body, commit?}` (leader → follower, proto tag `0x08`) | ∃ **rw**, **UNBOUND** grant (no `,p=`): filter matches `subject` ∧, when it carries a commit, the `Commit` rule on that group. The producer-id binding is not merely skipped — a **bound grant cannot reach this verb at all** (`broker.rs:2241-2246 replicate`, applied at `:2273-2275`; `proto.rs:21,82-96`). A leader ships the ORIGINAL producer's id, which no bound principal could ever derive, so the link grant is deliberately a distinct, unbound authority. Plus the **hidden-subject rule** (`broker.rs:1716-1747`): a replicated `/a/will` or `/a/bind` is accepted only on a log that is a replication target or is still EMPTY — on a broker that OWNS its log they are an injection, not a replication (an injected `/a/will` is an arbitrary publish under an arbitrary producer id that the broker itself executes at its next open, outside this matrix; an injected `/a/bind` locks a victim principal out of attaching for good), and `/a/commit` may carry only the pure-commit shape |
| `Subscribe`, `ForkSubscribe`, `Last{filter}`, `Fetch{filter}` | ∃ any grant: `contains(filter)` |
| `SubscribeGroup{group, filter}` | ∃ any: `contains(filter)` ∧ ∃ **rw**: matches `group` |
| `Hello`, `Attach` | always (they only add) |

What this buys, structurally: a member reads `/f/<F>/fleet/>` (ro) while committing its
cursor under `/f/<F>/cur/<owner>/…` (rw) on one connection; only a
`/f/<F>/fleet/<h>/>`-rw holder can write a halt, and the address says which human;
nobody can publish under a producer id their grant's principal does not derive, so a
peer's dedup key cannot be poisoned; the tag never crosses the wire; and
`Filter::contains` is sound — never a false positive (`subject.rs:217-224`) — so the ACL
can only ever be too strict. **A scoped agent gets exactly its subtree, nothing else** —
including the one place that used not to hold, the read CURSOR: a `Last` page's
`Mark.resume` is now always a subject the requested filter matches, never the raw index
entry the `LAST_SCAN_MAX` bound happened to stop on, because the broker pays extra scan
rounds (releasing the log lock between them) rather than name a subject outside the filter,
and a request that cannot reach such a position within `LAST_RESUME_ROUNDS` is answered
with an error rather than a blanked cursor — an empty `resume` means "complete", so
blanking would be a silent truncation (§5.2). **BUILT** `cap.grant-mode-and-producer` (R3),
`broker.cap-keyring-enforced` (R4). The nonce is unique per connection and built from std
alone (`RandomState` + a counter + the clock), because the default broker has no dependency
exposing an OS CSPRNG: the protocol needs FRESHNESS, and the nonce is not claimed to be
cryptographically random. Only a read-WRITE grant that names a principal binds it — a
read-only grant publishes nothing, so binding it would let a read-only holder append.

A node's ring: `rw,p=<n>:/f/<F>/pub/<n>/>` · `rw,p=<n>:/f/<F>/in/*/*/<n>/*` ·
`ro:/f/<F>/in/<n>/>` · `rw,p=<n>:/f/<F>/cur/<n>/>` · `rw,p=<n>:/f/<F>/term/<n>/*/out` ·
`rw,p=<n>:/f/<F>/term/<n>/*/screen` · `ro:/f/<F>/term/<n>/>` · `ro:/f/<F>/pub/>` ·
`ro:/f/<F>/fleet/>` — the `term` grants are split so the node **cannot** write its own
`in/<src>` drive lanes and forge a driver. A human's: `rw,p=<h>:/f/<F>/fleet/<h>/>` ·
`rw,p=<h>:/f/<F>/in/*/*/<h>/*` · `rw,p=<h>:/f/<F>/term/*/*/in/<h>` ·
`rw,p=<h>:/f/<F>/pub/p/<h>/>` · `ro:/f/<F>/in/p/<h>/>` · `rw,p=<h>:/f/<F>/cur/p/<h>/>` ·
`ro:/f/<F>/pub/>`. A viewer of one screen: `ro:/f/<F>/term/<n>/<sid>/out` — observe-only
by construction, the twin of aterm's `read-screen` edge (`edge.rs:22-25`). Caps reach a
tool only by `--cap-file <path>` (0600), an env var the bridge unsets after reading, or
the keychain; `--cap <grant>=<tag>` on argv refuses with a pointer to `--cap-file`,
because argv is visible to every same-uid process, the agents' shells included.

### 8.3 Provenance = address; the god caps

Because a sender's segment and producer id are fixed by its cap, `from=` needs no
signature and no PKI — and after this revision that holds for the halt too
(`fleet/<h>/halt`), the one flagship record the draft had left with a body-asserted
`by=`. The principals that can forge beneath themselves are exactly the holders of a
wide unbound grant (`/f/<F>/>`, the fleet root) and, for its own sessions, a node (its
lanes carry `from=<sid>` on the node's word). Both are the analogue of aterm's Owner
token. Do not hand the fleet root to an agent; document that trusting `from=s-…@n-…`
is trusting node `n-…`'s bridge **and its uid**: the node cap lives in the bridge's
state dir, and a same-uid shell can read it. The co-holder checks (§6.2) make that
*visible*; they do not make it impossible.

### 8.4 Prompt-injection defense — structural where it can be, labelled where it cannot

- `trust=` is computed by the receiving bridge from the face, the `<src>` class and
  `via=` (§4.3), never from the sender; `inbox` prints it first.
- **Kind is authority.** For principals with their own caps, the `<kind>` segment is the
  send ACL (§6.1). For sessions behind a bridge, the bridge honours `kind ∈ {task,
  control}` only from an allowlist (`--accept-from h-*,<orchestrator>`); an
  instruction-shaped message from anyone else is delivered as `kind=note` with a
  `demoted=task` marker, so the agent sees a report, not an order; a relayed message is
  always demoted (§6.7).
- **The wake path carries no bodies, and the hook REBUILDS every field rather than
  forwarding one.** Hooks and the events digest carry `OK <n> hold= holder=` plus per-row
  `id from= kind= trust= off= len=` — the fields `EVENT inbox` limits itself to (the
  drive-pipe rule, `docs/DESIGN-drive-pipe.md:252-253`). A body enters the agent's context
  only through an `inbox get <id>` call the agent chooses to make. **The design's reason —
  "the endpoint computes every field it prints" — was false of the shipped endpoint on
  three counts**, and A4 fixed it by not trusting the reply at all: `holder=` is up to 64
  bytes of a lease-taker's own text on the HEADER (the hook reduces it to a class); `via=`
  is the SENDER's declared relay chain and `deliver` accepts any number of comma-separated
  principals (the hook reduces it to a hop COUNT); and `from=`'s `s-<sid>@` prefix is read
  off the record BODY by the bridge, so it is the sending NODE's word, trustworthy exactly
  as far as that node's uid (T1). What survives into the model's context is a principal
  NAME on an ACCEPTED sender's row and nothing else any caller chose — every other field is
  a number, a bit, or a lowercase token bounded at a fixed length, and the block carries an
  explicit open banner. **T16's "never surface in context or wake" is exact for the wake
  half and narrowed for the other:** an unlisted sender's row still appears, as numbers and
  a CLASS (`s-?`, `n-?`, `h-?`, `a-?`) rather than a name, because an agent that is never
  told it has mail cannot go and read it. Nothing from such a row can reach exit 2
  (`may_wake`), and `pending=` counts un-carried rows, not unlisted senders (§11.2
  deviation 7).
- **Nothing in the fabric turns a delivered body into keystrokes.** The one bus→PTY path
  is `term/in` under the holder/hold/epoch/gen check (§6.6); `DeriveLoop` stays an aterm
  op no connection can mint (`edge.rs:43-45,86-110`).
- None of this neutralizes natural-language injection inside an accepted principal's
  text. The RFC's `OutputSanitizer` caveat stands (`docs/RFC-operator-2026-08-15.md:330-333`;
  `crates/aterm-containment/src/output_filter.rs:105`): it strips terminal-control
  hazards and is worth wiring; it does not make text safe.

### 8.5 Nested aterm and the confused deputy

Hop-by-hop, never transitive (§6.7): each level's bridge is a principal; a relayed
message keeps the inner as `via=` and the outer as `<src>` and lands demoted; the inner
never holds the outer's cap, and the deny-list strips the fabric selectors that would
let an inherited copy of one aim a child at the outer's fabric — `ATERM_LINK_BROKER`,
`ATERM_LINK_CAP_FILE` and `ATERM_LINK_FLEET` — exactly as the edge-token and net-listen
selectors are stripped today (`crates/aterm-types/src/env_sanitize.rs:127-186,291-298`).

NOT A GLOB, AND THE DIFFERENCE IS LOAD-BEARING. This paragraph used to claim the
deny-list kept *every* `ATERM_LINK_*` variable from surviving a hop. It does not, and it
is not meant to: `ENV_DENY_VARS` names three, and two more under that prefix —
`ATERM_LINK_FAULT` and `ATERM_LINK_NOTIFY_FAULT` — are inherited ON PURPOSE, because the
e2e harness arms a fault in a child it launches through a real `aterm-gui`
(`crates/aterm-gui/src/fabric_launch.rs:38-39`). A reader who believed the glob would
conclude that adding an `ATERM_LINK_*` variable is automatically safe across a hop; the
truth is that each new one is a decision, and the two exceptions are the reason the rule
cannot simply be widened to the prefix. (`ATERM_LINK_ALLOW_STRAYS`, `ATERM_LINK_KEEP` and
`ATERM_LINK_CLAUDE` also escape the list, but they are read only under
`aterm-link/tests/` and reach no shipped binary.)

The fault pair is contained, but NOT by the env fence — by a second mechanism, and the
distinction is the whole reason this paragraph is worth reading. Both arming sites open
with `if !cfg!(debug_assertions) { return Fault::None; }`
(`aterm-link/src/bridge.rs:485-487`, `aterm-link/src/notify.rs:500-502`), so a released
binary ignores the variable however it arrived. The env fence lets the selector through;
the build profile is what makes it inert. Two consequences follow, and neither is
obvious from the deny-list alone: a DEBUG build of `aterm-link serve` — which is what
every developer and every test harness runs — does honour an inherited fault selector
across a hop; and the release safety rests on a `cfg!` in two functions rather than on
the sanitizer, so anyone adding a third fault knob must remember the gate, because
nothing in the env layer will remind them.

### 8.6 Cross-host and key agreement

The same protocol over `serve_tcp_sealed`/`connect_tcp_sealed` (`broker.rs:1121-1138`;
`client.rs:85-97`): confidential and authenticated under a pre-shared 32-byte key, with
records bound to the connection, the direction and their position by a
`hello_client ‖ hello_server ‖ direction ‖ seq` AAD established in a per-connection
handshake (two 36-byte hellos in the clear, then a key-confirming empty record 0 each
way, so a peer without the key is refused *inside* the handshake), chunked at a 64 KiB
plaintext record ceiling, with the accept path bounded by a pre-authentication deadline
and a concurrent-handshake cap (`stream.rs:5-26,64-67`; `broker.rs:1197-1277`). Plaintext `--tcp` remains a
trusted-network-only setting (`asb.rs:127`). The PSK is a **transport** boundary against
outsiders, shared by every member; it is not a per-peer identity, and after this
revision no cap depends on it staying secret from a member (§8.2). Honest limit carried
forward: no revocation of one cap before its deadline short of rotating the broker
secret (which revokes every cap at once). A grant can now carry an expiry, checked per
request (`exp=` in its prefix, `cap.expiry-enforced`), and a log that now holds messages
as well as keystrokes can be sealed at rest (opt-in `at-rest`,
`broker.log-encrypted-at-rest`).
**Two limits of the bare PSK are closed in astream**, and the fabric should be
deployed on them rather than on it: an ephemeral
X25519 key agreement gives every session a fresh key (**BUILT**, opt-in `handshake`
— `aead.handshake.forward-secret-key-agreement`), and a mutual signed-DH handshake
gives per-peer static public-key identity with no shared secret, the client pinning
the broker's host key and the broker allow-listing the client (**BUILT**, opt-in
`identity` — `aead.identity.mutual-signed-dh`). A fabric node SHOULD use the
`identity` transport: it makes the node's bus principal (§3.2) an actual keypair
rather than a name asserted under a fleet-wide secret. Binding the two — deriving a
node's principal from its identity public key — is the natural next increment and is
**DESIGNED**, not on this ladder.

---

## 9. The turn-based agent, and the human

### 9.1 Wake, drain, ack — the front door is the aterm socket

```
# turn start — one verb, no socket held open, no cap in the agent's hands
$ aterm-ctl @self inbox
OK 3 hold=0 holder=- seen=40 bus_head=90340 dropped=0 pending=1   # <n> counts EVERY row below, post rows included
msg 41 off=90312 t=1756389000123 from=s-7c1e…@n-b2f0… kind=ask trust=agent dl=240000 len=34 text=which%20branch%20has%20the%20fixture%3F
msg 42 off=90340 t=1756389003001 from=h-andrew kind=task trust=human len=21 text=stop%20after%20tests%20pass
post 7 to=@s-9a01…@n-b2f0… kind=ask off=-                       # my own un-landed ask

$ aterm-ctl @self post to=@s-7c1e…@n-b2f0… kind=answer re=90312 'fixtures/ on branch audit-2'
OK 8 off=90355                          # --wait is the default for ask/task; answers land as re=… re-id=8
$ aterm-ctl @self inbox seen 42 handled
OK seen=42
```

One header (`OK <n> hold= holder= seen= bus_head= dropped= pending=`) whose `<n>` is the
count of ROWS that follow — `msg` and `post` alike, because the `Lines` framing the verb
declares is what a client reads, and a header that counted only messages would have it
truncate the reply (§11.2 deviation 6; this example said `OK 2` over three rows until the
built code settled it) — then one `msg` line
per message with every field on the line, `text=` pct-encoded (`help_catalog_full.txt:33`'s
rule) and truncated at 512 B with `more=1`, one `post` line per un-landed post, `inbox
--peek` to read without moving the watermark. `inbox get <id>` returns the full body **as
the endpoint holds it**, which is not always the body the sender wrote: the endpoint accepts
a 256 KiB `post`, but a delivered body rides the bridge's `deliver` REQUEST LINE, which
aterm's control server refuses past `REQUEST_LINE_MAX = 64 KiB − 1`, so a larger body is
delivered TRUNCATED with `len=` naming its true size. `inbox get` also returns the body
pct-DECODED, which is lossy for invalid UTF-8, and `post` is lossy the same way on the way
out (`ControlReply` is `String`-typed end to end), so **a genuinely binary body is not
byte-exact in either direction**. Every kind §4.2 lists is text, so nothing today is
affected; the `--bytes` shape a binary body would need is not built. The agent never types anything anywhere; the drain is data. `inbox seen <id>
[handled|refused|deferred]` advances the endpoint watermark (persisted by the bridge,
§6.2); the bus cursor already advanced at `deliver OK`. A sender-visible receipt is an
explicit `post to=<sender> kind=ack re=<off>`.

**Wake — three egresses, cheapest first.** The bridge pushes `EVENT <local> inbox <id>
from=<p> kind=<k> off=<n>` on the events digest (through the one `timeline_wire_kind`
table, `subscribe.rs:1029-1045`) — a count and an offset, never the body. What turns
that into a turn:

1. **Hooks (zero residency, Claude Code).** The vendor contract, verified against the
   Claude Code hooks reference (`https://code.claude.com/docs/en/hooks`) and hooks guide
   (`https://code.claude.com/docs/en/hooks-guide`), both fetched 2026-08-28 (the
   reference dates its notes by Claude Code versions v2.1.191–v2.1.218; no page date):
   the events `SessionStart`, `UserPromptSubmit`, `PreToolUse` and `Stop` exist; per the
   reference's "Exit code 2 behavior per event" table, exit 2 on `PreToolUse` "Blocks
   the tool call", on `Stop` "Prevents Claude from stopping, continues the
   conversation", on `UserPromptSubmit` "Blocks prompt processing and erases the
   prompt", stderr shown to Claude in all three; per the guide, for `SessionStart`
   "Claude Code adds stdout it treats as plain text to Claude's context" and for
   `UserPromptSubmit` one must "use `hookSpecificOutput.additionalContext` … if you place
   it at the top level of the JSON, Claude Code silently ignores it"; the guide states
   "Claude Code overrides a Stop hook after it blocks eight times in a row without
   progress. Your hook script needs to check whether it already triggered a
   continuation. Parse the `stop_hook_active` field from the JSON input and exit early
   if it's `true`" (cap adjustable by `CLAUDE_CODE_STOP_HOOK_BLOCK_CAP`); the reference's
   command-hook fields include `async` and `asyncRewake` ("runs in the background and
   wakes Claude on exit code 2. The hook's stderr, or stdout if stderr is empty, is
   shown to Claude as a system reminder"), and `timeout` "Defaults: 600 for `command`",
   with `UserPromptSubmit` lowered to 30 s.
   `aterm-link hook install claude` writes four command hooks into `.claude/settings.json`:
   `SessionStart` and `UserPromptSubmit` run `aterm-link hook run <event>`, which prints
   `aterm-ctl @self inbox --peek --meta` — the header and per-row metadata, **no bodies**
   — as plain stdout / `hookSpecificOutput.additionalContext` respectively; `PreToolUse`
   runs `aterm-link hook run pre-tool-use`, which exits 2 with the reason while `status
   hold=1` (§5.3); `Stop` runs `aterm-link hook run stop --timeout 15`, which exits 0 at
   once if the input's `stop_hook_active` is `true` or the session's wake budget is
   spent, otherwise captures the current `seen` watermark and blocks for the timeout, then
   exits 2 with the metadata digest on stderr **only for a row newer than the watermark
   from an `h-*` or `--accept-from` principal** — a deferred row can never re-fire it, and
   a `hold` transition wakes via the events digest, never via `Stop`; on timeout it exits 0
   and the agent stops. **The wait is aterm's own `await inbox since=<id> timeout=<ms>`
   (egress 2), not a wake socket.** §9.1 was drafted around `aterm-link wake @self
   since=<seen> --timeout 15` over a per-instance `<state>/wake.sock` served from the
   bridge's push lane, so that zero control lanes are held however many agents wait.
   **No such socket exists** — A3 built none and A4 could not add one — so the built hook
   parks on the same monotone predicate over the same endpoint state, on the inbox condvar,
   event-driven and without polling. The cost is exactly the one the socket existed to
   avoid: **one aterm control lane per parked `Stop` hook**, so `docs/OPERATOR.md`'s "park
   at most one" rule binds the hook path too until the socket lands. A `note` never wakes,
   whoever sent it, because `await inbox` skips `note` by default and a hook with a
   different rule would wake on a note already in the ring while never waking on an
   identical one that arrived a millisecond later. `pre-tool-use` FAILS OPEN when aterm
   cannot be reached at all (exit 0, a line on stderr), so that an agent outside an aterm
   session is not wedged; the structural half of the halt is the drive hold at the socket,
   which such an agent is not behind either. The `--rewake` install form sets
   `asyncRewake: true` with a long timeout so the wait runs in the background and
   re-wakes the stopped agent on exit 2; whether the `Stop` event honours `asyncRewake`
   is **pinned by A4's non-hermetic case, not verified here**. Everything about the JSON
   shapes is the vendor's; the installer emits what the installed version documents and
   A4 pins the behaviour. The hook command speaks only to aterm — the Phase-1 shape
   aterm's own RFC already plans (`docs/RFC-agent-cli-hosting-2026-07-26.md:492-495`,
   which names `SessionStart`, `Notification`, `PostToolUse`, `Stop`).
2. **`await inbox since=<id> [kinds=<k,…>] [timeout=<ms>]`** — a server-side predicate
   beside `await idle|seq|match|block` (`help_catalog_full.txt:68`) for scripts: latches
   only on a row with id > `since` (monotone — an ignored row cannot latch it twice) of an
   accepted kind, or on a `hold` change iff `hold` is listed in `kinds=`; exit 124 on
   timeout. One control lane per parked wait, so the operator brief's rule holds: park
   at most one (`docs/OPERATOR.md:87-90`) — and, with no wake socket, that now includes the
   hook path. **BUILT (aterm)**, A2; the catalog carries the fifth predicate
   (`help_catalog_full.txt:68`).
3. **Resident waker (hookless agents) — NOT BUILT.** The design has `aterm-link wake @<sid>
   --exec '<cmd>'` block on the wake socket and convert a coalesced batch into one
   non-interactive turn (`claude -p --resume … "<metadata digest>"`); a killed turn would be
   harmless because the inbox is durable and the next drain is idempotent — a duplicate wake
   costs a turn, never an action. `aterm-link wake` is **refused by name with its reason**
   (`main.rs`, beside `pin` and `lash`), and the `<state>/wake.sock` push lane it would
   block on does not exist. **DESIGNED**, both halves. **Codex** has no hook path here (its
   `notify` hook is unverified, SEED) and no socket path (T13, RED): its path is the file
   mirror, A9, which is built.

### 9.2 The misbehaviour table (what the human sees, and the one-key remedy)

| Misbehaviour | The record the human sees | Mechanism | Remedy |
|---|---|---|---|
| agent floods a peer | `⏸ s-… → s-…: 41 msgs/min, budget 6 — coalesced; 3 refused (quota)` | bridge budget + ring quota (§5.6, §6.2) | `aterm-link budget @s-… 0` |
| agent claims `from=h-andrew` | `✗ refused: n-… posted as h-andrew` (never lands: no cap) | cap-forced `<src>` (§8.2) | none needed |
| something posts as this node with a sequence the bridge never sent | `✗ cap-compromised: n-… — incarnation rolled` | `deduped`-on-fresh-sequence / self-lane check (§6.2) | rotate the node cap |
| agent tries to halt | `✗ refused: /f/F/fleet/h-…/halt needs rw as h-…` | `Error 5` at the broker | none needed |
| agent keeps typing during a halt | `⛔ s-…: 3 inputs refused (halted); 2 tool calls blocked` | `hold` gate; `PreToolUse`; each refusal is an `ev` record | `/where` → `raise <sid>` |
| two nodes advertise one sid | `✗ conflict: s-… claimed by n-A (pinned) and n-B — not routed` | TOFU pin (§6.1) | `aterm-link pin @s-… n-A` |
| screen text carries instructions | `✉ note [trust=screen demoted=task] …` in a delimited block | trust label + demotion (§8.4) | read, decide |
| human typed at a worker while an agent drove | `⋯ s-…: unaccounted change — holder=human? agent drive paused` | `decide_control` (§6.6) | `/take` to lock it, or let the agent `request` |

**Four of those remedies do not exist.** `aterm-link budget` and `aterm-link pin` are not
subcommands (`pin` is refused by name; there is no `budget` at all); `/where` and `raise`
are not tui verbs (the eight that are, and the two refused by name, are in §9.3); and the
flood row's `budget`/`coalesced` are the bridge egress budget of §5.6, which is DESIGNED —
the built budget is the `Stop` hook's own and bounds hook wakes, not messages. `/take` is
real. The ring quota and the `✗ refused`, `✗ cap-compromised`, `⛔ halted`, `✗ conflict`
and `⋯ unaccounted change` records are real; the TOFU pin is real and first-wins, but
overriding it by hand is not.

### 9.3 The human — where "human always wins" is structural, and where it is not

- **Halt the fleet from anywhere:** `asb pub <ep> /f/F/fleet/h-andrew/halt --cap-file
  ~/.astream/h-andrew.cap <<< 'v=1 t=… state=on reason=main%20broken'`. The `--cap-file`
  form is now the **BUILT** §8.2 face (R8 `broker.cli.fleet-verbs`): `asb` reads
  `<grant> <tag-hex>` lines out of the file — the flag is repeatable, and each line is
  split at its LAST whitespace, so a grant whose filter legally holds a space
  (`ro:/f/F/pub a/>`) reads back as the grant `mint` sealed instead of taking the whole
  ring down with a parse error — and attaches each before the verb runs (`asb.rs:133-140`
  the rule, `:376-408 load_caps` the parser, `:717-730` the flag). Presenting the same
  capability as `--cap-filter F --cap-tag HEX` on argv is REFUSED with exit 2
  (`ARGV_SECRETS`, `asb.rs:602-616`, enforced at `:712-716`), for exactly the reason a bare
  `--key HEX` already is: argv is readable by every same-uid process through `ps` for the
  command's whole lifetime. Every bridge's
  tail flips `hold on` within one delivery and acks it (`ack/<halt-offset> state=held`),
  so the issuer's tool prints *who held* rather than assuming; the physical keyboard is
  untouched.
- **See every escalation on every host:** `aterm-link ls --attention` — one `Last`.
  **BUILT (aterm)**, A3/A5, with the honest columns §7 now lists. `glance.json` is **half
  built**: the WRITER and the format are real, as their own subcommand — `aterm-link
  glance` does one `Last` round trip and writes `<state>/fabric/glance.json` atomically,
  every `key=value` of the presence body carried through verbatim under its own name with
  the subject and offset it was read at, bounded by a row cap that says `"truncated": true`
  in the file when it bites, and `attention=`/`fabric=` guaranteed present as `-` when the
  publisher omitted them. What is NOT built is `serve --glance` (the bridge rewriting the
  file as presence changes — one line in the run loop) and, more importantly, **any reader
  at all**: `crates/aterm-gui/src/status_item.rs:179-212` still holds only `FleetGlance`,
  with no `FabricGlance`, no mention of `glance.json` and no read of any fabric state (the
  registry-is-the-filesystem idiom it would follow is
  `docs/design/HIERARCHICAL_SESSIONS.md:317-325`). The menu-bar half is **DESIGNED**.
- **Be reached when you are not looking (the Slack axis):** `aterm-link notify --on
  attention,ask:h-andrew --exec <cmd>` runs a user-supplied command (ntfy, mail, a
  webhook) once per matching record, deduped by offset and rate-limited — the outbound
  path headless boxes lack today (`docs/RFC-operator-2026-08-15.md:302-304`). **BUILT
  (aterm)**, A10 (`--test notify`). Four things the synopsis above does not carry, each
  because the built verb had to answer a question the design left open: it takes the same
  transport, capability and state flags `serve` does (a bus reader cannot reach a record
  without a broker, a fleet and a cap, and two grammars for one crate would be worse); it
  takes `--since head|start|<offset>`, defaulting to `head`, so a notifier installed today
  does not page a human through every escalation the fleet has ever had; **the journal is
  written BEFORE the command runs, so the failure it chooses is a command that runs TWICE**
  rather than one that silently never runs — an in-doubt entry re-fires, marked
  `ATERM_NOTIFY_DUP=1`; and dedup is **by offset only**, so a presence row republished with
  an UNCHANGED `attention=` at a new offset is a new notification, because collapsing on the
  value would be the silent drop the rung forbids. Two consequences: the budget is per
  NOTIFIER and not per recipient, so a chatty session can crowd out a quiet one; and a
  dropped offset is terminal — it is never re-offered when the window rolls.
- **Answer from a phone or an ssh session:** a tool holding `rw,p=h-andrew:…` either
  posts an `answer` the agent reads as text, or — to actually approve a prompt — takes
  the keyboard (`control claim`) and types through `term/<n>/<sid>/in/h-andrew` with
  `epoch=` and `gen=` (§6.6). The row the agent sees is `from=h-andrew trust=human`.
- **Take and give back the keyboard:** `kind=control` `claim`/`grant`; the bridge mirrors
  it into `lease holder=fabric:h-andrew`. The log is the control history.
- **The fabric as a session — BUILT (aterm), A8, with two verbs missing:** `aterm-link
  tui` is an ordinary program in an ordinary aterm PTY — the fleet transcript (`Fetch` then
  `Subscribe` over `/f/<F>/>`, `--from <offset>`, rendered by kind with trust labels first
  and `@<offset>` on every row) with the slash verbs `/tell`, `/ask`, `/answer`, `/all`,
  `/halt`, `/take`, `/give`, `/since` (plus `/help` and `/quit`), which are `post`s and
  publishes. **`/barrier` and `/fork` are refused by name with their reason**: a barrier is
  a publish plus a quorum fold over `pub/*/*/ack/<B>` with its own rule (§5.4) and a fork is
  a replay of the conversation into a new subtree (§10); neither is a line of that file, and
  a verb that parsed and did nothing would be worse than one that says it does not exist.
  Every rendered row is escaped before it reaches the PTY — no C0, C1, DEL or bidi override
  survives — because a body carrying a newline and a `trust=` token would otherwise print a
  label the receiver never computed, which is the same bug as feeding a body to a PTY, one
  layer up. Of "`text`, `search`, `subscribe`, `cast` and `image` apply to the fleet
  conversation with zero engine code", only `text` and `search` are asserted; the other
  three follow from the tui being an ordinary scrolling program but were not run.
- **Where it is structural:** the `/f/<F>/fleet/<h>/>` write cap (bus); the `hold` gate
  and `deliver` behind `Scope::Bridge`, which no token — Owner included — unlocks
  (endpoint); the `control`-holder check at apply time; `PreToolUse` for hooked agents;
  fail-closed on a dead bridge. **Where it is not:** an agent whose shell shares the
  bridge's uid can read the node cap and *be the node* on the bus (T1) and can kill the
  bridge (which only halts); hookless agents are drive-held only; keyboard provenance is
  inferred (§6.6).

---

## 10. Replay, audit and fork of the whole conversation

One log carries the messages, the acks, the presence and control rows, the events
digests, and — where a session opted in — its `term/out` bytes. So one audit:

- **Replay** is `Subscribe{0, /f/<F>/>}` (or `Fetch` paged), the deterministic
  time-travel `broker.exactly-once-pubsub-resume` proves; the folds a reader applies
  (halt, presence, control, barrier) are versioned by the body's `v=` so two readers
  with different fold versions disagree loudly, never silently.
- **"Who was present when message M arrived"** is presence folded to M's offset —
  replayable presence no gossip or last-will system offers.
- **Causality.** A `term/in` record at offset `M` that the bridge applied leaves an `ev`
  record `applied re=M seq=<n>` on the session's `ev` face,
  `/f/<F>/pub/<node>/<sid>/ev` — with `re=` as a first-class body token rather than a
  substring inside the pct-encoded `ev=` payload, so a reader rebuilds the causal edge from
  the stored bytes alone. **`seq=` is NOT aterm's `send` reply.** `feed-bin` — the verb the
  bridge actually drives with — carries no `seq=`: only the line-dispatched input verbs are
  stamped (`control.rs` `stamp_input_seq`, over `send|feed|key|ctrl|mouse|paste`) and the
  framed path never reaches it. So `seq=` is the session's `content_seq` BASELINE, read by
  the bridge immediately before the write on the same round trip the `gen=` fence already
  pays for, and `-` when the screen could not be read — an unknown baseline is not a zero.
  Adding `seq=` to `feed-bin`'s own reply would change a shape ~10 aterm-gui tests assert
  byte-exactly, inside A6's pinned call-site counts, for a value the bridge can read itself;
  that stays **DESIGNED**. The screen that followed is `term/out` after seq `n` —
  **watermark-grade** at the aterm seam, the same honest grade as
  `term.echo.watermark-retire`. An inbox record is never "applied"; what the agent does
  after reading it is its own. At the astream-host seam the pointer is exact: an
  injected `In` carries `caused_by=(partition, offset)` durably (`envelope.rs:69`;
  `session.rs:325-347`, where `apply_input_caused_as` is the ControlToken-gated ingest),
  and `cross_edges_from_logs` rebuilds the edges from bytes alone (`fleet.rs:88-106`,
  `term.fleet.durable-watermark`).
- **Consistent cuts.** With one broker per fleet the bus has a single offset spine, so a
  fleet cut *on the bus* is one offset. astream's own Chandy-Lamport machinery —
  `Cut`/`is_consistent`/`CutReplay`/`replay_to_cut`, with `replay_to_cut` returning
  `Result<CutReplay, ReadError>` whose `folded_through` is an `Option<Offset>`
  (`fleet.rs:42-47,69-76,110-117,126-153`) — runs over astream-host ENVELOPE logs, and
  **the fabric has none of those: its sessions are PTYs.** A7 therefore does not compose
  those functions; `aterm-link/src/replay.rs` REIMPLEMENTS `Cut` / `cut_includes` /
  `is_consistent` / `cross_edges_from_bus` / `replay_to_cut` in the same shape over BUS
  records, because §11.2 pins this crate's dependency set and `astream-engine` is not in it
  — importing it to reuse four small pure functions would widen the set for a rung whose
  point is composition without new authority. What A7 re-folds is the opt-in `screen`
  snapshot face (§3.3) as a last-value fold, not a byte-exact `term/out` stream, and the
  replay reads the bus with a separate `Auditor` holding `ro:/f/<F>/>` — a human's ring
  (§8.2) deliberately cannot read another session's mail or any screen, and the broker
  refuses it. So `term.fleet.consistent-cut-replay` and `term.fleet.durable-watermark`
  remain astream's claims about astream's logs and are **not** re-proved by A7; A7's own
  claim is the fabric's, `fleet.comms.e2e-exactly-once-across-nodes`. Cross-broker cuts are
  the federation seed (§14).
- **Fork.** `ForkSubscribe{fork_at=R, replacement}` replays the exchange with the ask at
  `R` swapped, live log untouched (`store.rs:1748 fork_shared`; `broker.agent-native-fork-and-cognition`)
  — offline, recorded divergence only, closed by an explicit `Mark` before the EOF so a
  truncated snapshot is distinguishable from a complete one (§6.4); the recorded answer
  does not change, and it is
  never a live re-drive of claude or codex (`docs/DESIGN-drive-pipe.md:292-294`).
- **Retention.** The log is file-backed under an exclusive file lock
  (`store.rs:389 lock_exclusive`, taken at `:524`) with every record also held in RAM
  (`:170` the byte mirror, `:173` the `Arc` record vector), and append-forever unless
  compacted: `Broker::retain_before` (opt-in `retention`, `broker.log-retention`) drops
  records below an offset floor, keeping surviving offsets absolute. The
  fabric writes `ev`, presence-on-change and messages; `term/out`/`screen` are opt-in.
  A retention policy that drives it (TTL, size) is DESIGNED and the largest operational
  risk (§14).

---

## 11. Exact changes

### 11.1 astream

**`crates/astream-broker/src/proto.rs`** — four request tags, two response tags. The tag
block (`:14-25`) holds **twelve** request tags, `0x01`–`0x0C` — the audit pass added
`TAG_REPLICATE = 0x08` (`:21`) for the replicated tier, and the four below start at `0x09`
— and five response tags (`:26-30`). Bodies use the existing `u32 LE length ‖ bytes`
strings/bytes, integers LE:

```
TAG_LAST  = 0x09   Last  { filter: str, after: str, max: u32 }
                   → Delivery* (last record per matching subject with subject > after, ascending subject),
                     Mark{next: head, head, resume: str}
                     max is CLAMPED to LAST_PAGE_MAX = 4096 rows, and each index scan is cut after
                     LAST_SCAN_MAX = 65536 entries VISITED (matched or not), so a page shorter than max —
                     an EMPTY one included — is NOT the end of the answer. `resume` is the SUBJECT cursor:
                     pass it back as `after`; an empty `resume` means the scan reached the end of the
                     filter's range. It is always a subject THIS filter matches (§5.2, §8.2).
TAG_FETCH = 0x0A   Fetch { from_offset: u64, filter: str, max: u32 }
                   → Delivery* (≤ max matching records with offset ≥ from_offset, scanning ≤ FETCH_SCAN_MAX = 65536),
                     Mark{next, head, resume: ""}
                                        next = offset after the last SCANNED record (a sparse filter still advances);
                                        max = 0 delivers nothing (the head query); Fetch pages by OFFSET, so its
                                        Mark.resume is always empty
TAG_WILL  = 0x0B   Will  { producer_id: u64, producer_seq: u64, subject: str, body: bytes }
                   → Mark{next: head, head, resume: ""}
                                              (persisted as a hidden /a/will record; one per connection AND one
                                               producer id per connection — a second Will under the SAME producer id
                                               replaces, a second under a DIFFERENT one is refused Error 5, because
                                               the durable record keys by producer and two live entries would fire a
                                               goodbye the client had taken back; the subject's DISTINCT-SUBJECT bound
                                               is checked here, at registration, and the firing is exempt from it;
                                               acked on this broker's LOCAL commit, not on the quorum watermark;
                                               fires as an ordinary Publish when this connection ends, unless deduped,
                                               fenced by a higher producer_seq from the same producer, or held on a log
                                               that is a replication target)
TAG_HELLO = 0x0C   Hello {}
                   → Nonce{nonce: [u8; 32]}   (fresh per connection; Attach's proof is HMAC-SHA256(tag, nonce ‖ grant))
TAG_MARK  = 0x84   Mark  { next: u64, head: u64, resume: str }     (also the reply to Attach)
TAG_NONCE = 0x85   Nonce { nonce: bytes }
```

`resume` is the one wire change this branch made to an existing type
(`proto.rs:172-191`), written with the same trailing `put_str` every other string uses
(`:498-502`). It was **not** made optional at the decoder: `Mark` reads it with
`r.string()?` (`:545-552`), so a `Mark` frame that ends after `head` is malformed and the
whole response is refused. The round-2 draft of this section said the decoder used
`unwrap_or_default()`; the round-3 pass took that away on purpose, because an older broker
is already refused at the version byte (`proto.rs:528`) — so a short `Mark` can only be a
CURRENT peer's truncated frame, and an empty `resume` means something specific ("the scan
reached the end of the filter's range") that a truncation must not be readable as
(`proto.rs a_mark_truncated_after_head_is_malformed`). The field therefore costs nothing on
a v2-to-v2 wire and is not compatible in either direction with a v1 peer. A second-language v2 client that
decodes `Mark` as exactly sixteen bytes and then reads the next frame WILL desynchronize on
the four-byte length prefix that now follows on every `Last`, `Fetch`, `Will` and `Attach`
reply.

`Last`, `Fetch`, `Will`, `Hello` and `Attach` are answered **in the request loop** — the
connection stays usable — after `finish_pipe` (flush pending acks, reclaim the socket,
the discipline every streaming verb already follows, `broker.rs:1766,1788,1874`). Unknown
tags still decode to `None` (`proto.rs:470,555`), so a broker that does not know a tag
answers `Error{5,"malformed request"}` (`broker.rs:1544`) rather than guessing. Across the
version bump that error is not reachable in either direction: a v2 client cannot decode a
v1 broker's `Error` response either, because `decode_response` gates on the version byte
first (`proto.rs:528`), so a version-mismatched exchange ends in a refusal at the codec on
both sides and not in a readable error. A `proto` unit test pins the tag set at **twelve** requests
(the built eight plus these four) and five responses, and pins that the version byte gates
all seventeen (`proto.rs the_tag_budget_is_twelve_requests_and_five_responses`).

**`crates/astream-broker/src/store.rs`** — `last: BTreeMap<String, Offset>` beside `dedup`
(`:175`, `:182`), maintained by `index_last` (`:1408-1447`) as `commit_batch` (`:1457`)
promotes a batch, and rebuilt in `open_with`/`open_inner` (`:489`, `:505`, the index
rebuild at `:575-603`); `high_water: HashMap<u64, u64>` (per producer, `:219`);
`bind: HashMap<u64, (String, Offset)>` (`:235` — the offset came with the audit pass, so
the rebuild can keep the FIRST binding);
the hidden subjects `/a/will` and `/a/bind` excluded from `dedup`, `last` and delivery
exactly like `COMMIT_SUBJECT` (`:59 is_hidden_subject`);
`last_matching(&Filter, after, max, scan_max, visible) -> (Vec<Arc<BrokerRecord>>, Option<String>)`
(`:1616-1664`) as a bounded prefix range scan returning its resume cursor;
`fetch(from, &Filter, max, scan_max, visible)` (`:1680-1713`); `subjects_per_producer`
counted in the `last` index.

**The on-disk record format is unchanged (`BREC_VERSION` stays 2), but this branch DID add
a durable on-disk artifact beside the log**: the `<log>.replica` marker
(`store.rs:423-427 replica_marker_path`, written and fsynced by `:721-744 mark_replica`,
read on every open at `:528-537`, cleared only on a log this open CREATED). It is
load-bearing for whether the broker fires the wills the log holds, it is what
`Broker::open_replica` / `BrokerLog::declare_replica` (`store.rs:708-710`) write, and
**it must travel with the log** — a backup or a relocation that copies `<log>` alone
restores a broker that believes it owns the log and fires the leader's wills (§7). Every
record body stays inside `MAX_RECORD_PAYLOAD = MAX_PAYLOAD_LEN − 16` (`brecord.rs:20`,
enforced at `:77`), the cap the audit pass added so a stored record always also fits inside
a `Replicate` request. `BrokerLog` also takes an **exclusive file lock** and a corrupt
(non-torn) log refuses to open unless the operator calls `open_repair` (`store.rs:389
lock_exclusive`, taken at `:524`; `:498 open_repair`, whose shell face is the `asb repair`
verb, `asb.rs:1346-1365`), so a fabric deployment must surface that refusal rather than
retry it.

**`crates/astream-broker/src/broker.rs`** — `Request::Last` (`:1895-1955`, through the
lock-releasing, cursor-continuing `last_page` helper at `:2667-2718`), `Fetch` (`:2040`)
and `Hello` (`:1554`) arms; `Request::Will` (`:1956-2039`) persists first and then stores
`Option<WillRecord>` on the connection, and `handle_conn` (`:1400`) is wrapped so that on
*any* return the will is sent to the writer as a fenced `WriteKind::WillFire` with a
discarded ack (`:1439-1445 fire_will`); on open every persisted will is fired through the
same fence, **unless the log is a replication target** (`:820-827`); the connection's
capability is now the append-only keyring `Vec<astream_cap::Capability>` (`:1523`, at most
`MAX_KEYRING = 16`, `:198`) with `Attach` verifying the proof against the connection's
nonce, appending, consulting the binding table and answering `Mark`/`Error`
(`:2120-2187 attach_grant`); `cap_authorized` (`:2217-2292`) applies the §8.2 matrix, including
the principal-derived producer binding on `Publish`/`ProcessAndProduce`/`Will`. Its
`Replicate` arm (`:2241-2246`, applied at `:2273-2275`) requires a genuine, read-write,
filter-matching **and UNBOUND** grant: the binding is not merely skipped, a BOUND grant
cannot reach the verb, because a leader ships the ORIGINAL producer's id and no bound
principal could derive it (§8.2). Two more per-connection rules landed here: the ack-writer
thread now takes the connection's RESOLVED write timeout rather than overriding it with
`ACK_WRITE_TIMEOUT` (`:2314 Pipeline::start`, `:2403 ack_writer_loop`), because
`SO_SNDTIMEO` belongs to the socket and the ack-writer runs on a `try_clone` of the same
one; and both streaming paths raise the socket to `STREAM_WRITE_TIMEOUT = 30s` (`:174`,
used at `:1826` and `:2731`), so a fork reader slower than the writer is not torn down at
the 10 s ack bound mid-snapshot.

**`crates/astream-broker/src/client.rs`** — `attach` does `Hello`→`Nonce`→`Attach` and
reads the `Mark` (`:238`); `last(filter, after, max)` (`:445`) and the resume-carrying
`last_page(filter, after, max) -> (Vec<Record>, (next, head), resume)` (`:457`), which is
the one a correct paged reader calls; `fetch(from, filter, max)` (`:482`);
`will(…) -> Mark` (`:394`); `Subscription::recv_event() -> Option<Event::{Delivery, Mark}>`
(`:948`; `recv` at `:923` keeps its signature and skips `Mark`); `Subscription::get_ref`
(`:916`), the escape hatch for a stream type with no `set_read_timeout` of its own; and
`client::drain(…)` (`:721`) / `client::ack(…)` (`:778`) — the two-connection drain and the
PnP ack as library helpers. `Subscription` also carries a `carry: Vec<u8>` resume buffer so
a read timeout landing part-way through a record does not desynchronise the stream (§6.3).

**`crates/astream-cap/src/lib.rs`** — `Grant{mode, principal: Option<String>, filter}`,
`Grant::parse`, `mint` over the grant string, `mode_of`, `producer_id_of(principal)`
(SHA-256 with the `"astream-pid\0"` domain), `attach_proof(tag, nonce, grant)` /
`verify_attach(secret, grant, nonce, proof)`, `grants_publish(secret, grant, subject,
producer_id)`, `grants_commit` (both NEW — `grants` at `lib.rs:367` is the plain filter-matches-subject
check, and is what the `Replicate` arm calls before it also demands an unbound grant),
`grants_publish` at `:377`, `grants_commit` at `:392`, `grants_filter` at `:402`
unchanged in meaning; the tag compare is `ct_diff` at `:257`, split out so the
all-32-bytes fold is observable to a test rather than only to a reader. Still `sha2` only.

**`crates/astream-broker/src/bin/asb.rs`** — `asb last <ep> <filter> [--after S] [--max N]`
(`:1491-1508`) and `asb fetch <ep> <filter> [--from N] [--max M]` (`:1509-1523`) print
`<offset> <nbytes> <subject>\n<body>\n` per record then `MARK next=<n> head=<h>` (subjects
are printed — `sub` omits them, which a wildcard drain cannot afford). **`next` means a
different thing in each.** For `fetch` it is the PAGE CURSOR — the offset after the last
record SCANNED, so a page that matched nothing still advances it — `--from <next>` reaches
the rest, and `next < head` means there is more. For `last` it is the HEAD to `sub --from`
from this snapshot, and NOT a page cursor: `last` pages by SUBJECT, `--max` is its only
bound (asb follows the broker's own resume cursor across as many round trips as it takes,
past `LAST_PAGE_MAX`/`LAST_SCAN_MAX` — `last_all`, `:1015-1086`), a page shorter than `--max`
(an empty one included) IS the end, and a full page resumes with
`--after <the last subject printed>`. Because asb may make several requests, the `MARK` it
prints is the FIRST one's — the lowest head it saw — since that is the only offset a paired
`sub --from <next>` can resume from without a gap. **`--max` alone is therefore not the
whole answer, and the round-3 pass made asb's own module doc say so**: §5.2's omission rule
means a subject whose newest record is at or above that pinned head is left OUT of the page
and arrives on the reader's `sub --from <next>` instead. The omission is real and invisible
from the page — the row count is one lower, `--max` was not reached, and nothing says why —
so a fleet roster read out of `asb last` ALONE can be short a session that just changed.
The whole answer is `--max` plus that paired subscribe. Round 3 also made `commit`'s `<upto>`
and `ack`'s `<offset>` check against the broker's visible head first: an operand at or past
it is a usage error (exit 2) with nothing written, because a group's committed offset is
monotone and an over-large one can never be lowered again.

`asb drain <ep> <group> <filter> [--max N] [--idle MS] [--peek]` (`:1524-1583`), where `--idle`
is a POSITIVE number of milliseconds and `0` is a parse-time usage error (exit 2, `:1539-1543`)
raised BEFORE either connection is opened rather than an opaque OS error after the group
subscription is already registered; `asb ack <ep> <group> <offset> <to-subject>
handled|refused|deferred` (`:1584-1660`) — `drain`/`ack` refine the already-built
`asb sub --group G` (`asb.rs:1472-1490`) and `asb commit <ep> <group> <upto>` (`:1661-1687`),
they are not first arrivals;
`asb mint --secret-env NAME | --secret-file PATH <ro:|rw,p=<principal>:><filter>`
(`:1366-1391`) → `<grant> <tag-hex>` (the mint secret never on argv — the rule
`asb.rs:602-616` already enforces for `--key`), the unbound read-write grant only under
`--legacy-unbound` — both of its spellings, `/f/F/>` and `rw:/f/F/>`, since they parse to
one authority; a repeatable global `--cap-file <path>` attaching before the verb
(`:376-408 load_caps`, attached by `connect_attached` at `:892-900`), each line split at its LAST whitespace — not its first
— because a filter may legally contain a space (`Filter::new` rejects only bytes below
0x20 and 0x7f) and the tag is the fixed-width whitespace-free tail, so a grant like
`ro:/f/F/pub a/>` that `asb mint` will seal and print reads back instead of exiting 2
(`--cap-filter F --cap-tag HEX` on argv is refused instead — `ARGV_SECRETS`,
`asb.rs:602-616`); `asb pub --seq-file <path>` (write-ahead persisted sequence,
`:1129-1184 advance_seq_file`, serialized by `:1205-1227 lock_seq_file`) so a bridge in any language gets safe producer sequencing.

**What landed, and the nine places the built code differs from the sketch above.**
R1, R2, R4, R5, R6 and R11 are **BUILT** (`broker.last-value`, `broker.fetch-bounded`,
`broker.cap-keyring-enforced`, `broker.will-fires-exactly-once`,
`broker.inbox-drain-ack-exactly-once`, `broker.proto.tag-budget`). The deviations, each
forced by the built code:

1. **`last_matching` and `fetch` take the visible head, and a scan bound, as arguments**
   (`last_matching(&Filter, after, max, scan_max, visible)`,
   `fetch(from, &Filter, max, scan_max, visible)` — `store.rs:1616-1664`, `:1680-1713`).
   The store cannot read `shared.head`, and pairing a page with the DURABLE head would
   expose, on the Replicated tier, exactly the records `tail_loop` withholds — so the
   broker reads the visible head under the same lock and hands it down. `scan_max` is the
   argument that makes `Last` bounded in WORK and not only in output (deviation 6).
2. **The keyring holds `astream_cap::Capability`, not `Grant`.** The tag never crosses the
   wire, so the broker re-derives it with `astream_cap::mint(secret, grant)` after
   `verify_attach` and then calls the vetted `grants_publish`/`grants_commit`/`grants_filter`
   unchanged, rather than re-implementing the ACL over a parsed `Grant`.
3. **`Client::attach` needs the `cap` feature.** The attach carries an HMAC proof, so a
   client that cannot compute that MAC cannot attach; without the feature `attach` returns
   `Unsupported` naming it, and `hello` + `attach_with_proof` stay available for a caller
   whose tag lives elsewhere. `asb --cap-file` therefore needs `--features cap` too;
   `--cap-filter`/`--cap-tag` are refused on argv whatever the features are (deviation 5
   of the next block), so no build of `asb` accepts them.
4. **`client::drain` takes neither `filter` nor `idle`: it is `drain(sub, committer,
   group, max)`** (`client.rs:721-726`). The idle window is set on the subscription.
   `Subscription::set_read_timeout` is implemented PER CONCRETE STREAM — `UnixStream`
   (`client.rs:993-1005`), `TcpStream` (`:1007-1012`), and (feature `aead`)
   `SealedStream<TcpStream>` (`:1015-1030`), which the sealed, handshake and identity
   transports all hand back — because a stream generic over `Read + Write` has no timeout
   to set. (The earlier text here said `set_read_timeout` was "the only shape a stream
   generic over `Read + Write` can express"; that was FALSE as written — the method was
   never on the generic impl, only on concrete types.) A stream type outside that list
   reaches its own socket through `Subscription::get_ref` (`:916`) and bounds it there.
   `take`/`drain` stop on a timed-out read, and that stop is **frame-atomic**: a timeout
   landing part-way through a record keeps that record's bytes on the subscription and
   finishes it on the next call, so the same `sub` is safe to drain from again
   (the round-2 claim `broker.drain-idle-window-frame-atomic`, §12). The filter belongs to
   `Client::subscribe_group(self, group, filter)` (`client.rs:627`), which CONSUMES its
   client, so the caller names it one call and one connection earlier and `drain` never
   sees it. §6.3 states the built four-argument shape.
5. **`Mark` grew a third field, `resume: String`, and the version byte moved anyway**
   (`proto.rs:172-191`, `PROTO_VERSION` at `:12`). The sketch's two-field `Mark` could not
   express "this page was cut short", which is the only honest answer a bounded `Last` can
   give. The field costs nothing on a v2-to-v2 wire, but it is NOT decoded optionally: the
   round-3 pass made it `r.string()?`, so a `Mark` truncated after `head` is malformed
   rather than silently read as "complete". `PROTO_VERSION` went 1 → 2 in this branch
   anyway, for `Attach`'s redefinition (§4.1, §8.2). **So do not read
   "additive" as "your v1 clients keep working": they do not.** Both `decode_request` and
   `decode_response` gate on the version byte, so a pre-bump peer is refused at the codec
   on the first frame, in either direction. Upgrade brokers and clients together; the
   compatibility this deviation once promised is not on offer.
6. **`Last` is bounded in WORK, not only in output, and its cursor is filter-safe.**
   `LAST_PAGE_MAX = 4096` rows, `LAST_SCAN_MAX = 65536` index entries per lock hold,
   `LAST_RESUME_ROUNDS = 64` rounds per request (`broker.rs:250-263`). The sketch's
   "O(log n + page)" cost model was wrong for a sparse filter, and a page cut by the scan
   bound must not hand back the subject it stopped on, so the broker continues the walk
   itself (`broker.rs:2667-2718 last_page`) rather than name a subject outside the caller's
   filter (§5.2, §8.2).
7. **"No on-disk change" was wrong.** The record format is unchanged (`BREC_VERSION` stays
   2), but a durable sidecar `<log>.replica` now sits beside the log and decides whether
   this broker fires the wills the log holds (`store.rs:423-427`, `:721-744`, `:528-537`).
   It must travel with the log, and `Broker::open_replica` / `BrokerLog::declare_replica`
   is how a copied log is re-declared. There is no undeclare verb: the declaration IS the
   file (§7).
8. **A `Will` REGISTRATION is acked on the leader's LOCAL commit, not the quorum
   watermark**, and a second `Will` under a DIFFERENT producer id is refused rather than
   accepted (`broker.rs:1981-1994`, `:2469-2477`, `:2585-2611`). The sketch said only "one
   per connection, a second replaces". Both changes exist to keep the connection's
   in-memory will and the log's `/a/will` record from disagreeing; the cost is that on the
   Replicated tier the goodbye is only as durable as the leader's own log (§7e).
9. **A `ForkSubscribe` snapshot ends with an explicit `Mark` before the EOF**
   (`broker.rs:1863-1870`). A bare EOF was the same answer a connection torn down
   mid-snapshot gives, so a truncated counterfactual was indistinguishable from a complete
   one. `Subscription::recv` still skips the mark, so the shipped shape is unchanged; a
   caller that cares uses `recv_event`.

**The `asb` verbs are BUILT** (R8 `broker.cli.fleet-verbs`, R9 `broker.cli.fleet-sealed`).
Every new verb goes through the existing `Transport` dispatch and the existing strict
parser, so it inherits the sealed/handshake transports and the flag discipline unchanged.
Six places the built CLI differs from the sketch above, each with its reason:

1. **R8's command carries `--features cap`.** `mint` computes an HMAC and `--cap-file`
   attaches a proof of possession; both need the same vetted MAC the broker verifies with,
   which is exactly deviation 3 of the previous block reaching the shell.
2. **`drain` prints the subject too, and a summary line.** The sketch pins the
   `<offset> <nbytes> <subject>` framing (the count first, the subject to end of line, so a subject holding a space cannot fake a header) for `last`/`fetch` only; a drain over
   `/f/<F>/in/<n>/>` spans senders and kinds for the same reason, and it closes with
   `DRAIN n=<n> upto=<offset|-> committed=<yes|no>` — a group read has no `Mark`, and a
   caller that must know whether the cursor moved cannot infer it from an empty batch.
3. **`pub` and `ack` DERIVE the producer id from a bound grant.** A bound grant may
   publish under exactly one id, so asb computes it (`astream_cap::producer_id_of`) from
   the single principal its WRITABLE grants name — a `ro,p=` grant binds nothing, so it
   never votes — and asks for an explicit `--id` only when two writable grants name two
   principals. Nothing about the id is typed, which is the §3.2 property.
4. **`ack` and `--seq-file` REFUSE the per-invocation producer id.** `asb pub`'s default id
   is the pid — fine for a one-shot publish, silently fatal for the two verbs whose whole
   point is a dedup key that survives a restart, so those demand `--id` or a bound grant
   instead of defaulting.
5. **`--secret`, `--cap-tag` and `--cap-filter` join `--key` in one refusal table.** The
   rule is the same rule — argv is world-readable through `ps` — so it is stated once, and
   each refusal names the file or environment flag that replaces it.
6. **R9's broker is opened in-process.** `asb serve` has and gains no way to set a mint
   secret: a guarded broker is opened by an embedder (`Broker::open_guarded`), never by the
   generic CLI, so the sealed+guarded test serves from the test process and every client is
   a real `asb` subprocess. *(Superseded 2026-09-24: `asb serve --secret-file | --secret-env`
   now opens that guarded broker from the CLI — REQUIREMENTS-fabric-operations R1, ported from
   aterm's `aterm link broker`, claim `broker.cli.serve-guarded`. The R9 test still serves
   in-process, which is now a choice rather than a limit.)*

Four honest boundaries the claims state. (1) `pub --seq-file` advances and fsyncs the file
BEFORE the publish, so a crash in between burns that sequence number — a record never
published, never a duplicated one (and a file that does not hold an unsigned integer —
an EMPTY or whitespace-only one included — is an error, never a restart at 1: only an
absent file starts a sequence). (2) `asb drain` commits before it prints (the order
`client::drain` fixes), so a crash between the two loses the batch, which is why `--peek`
plus an explicit `asb commit` is the at-least-once shape. (3) Because one bound
grant forces `pub` and `ack` to share a producer id, `asb ack` publishes under producer
sequence `2^63 | <input offset>` — the reserved TOP HALF of the sequence space, with
`--seq`/`--seq-file` held below it — so a seq-file counter and an early input offset can
never be the same `(producer_id, producer_seq)` dedup key. **The reservation is not the
CLI's: it is one wire contract, and both faces derive it from one exported constant.**
`ACK_SEQ_BASE` is defined by the LOG (`store.rs:85`, where the will fence can also read
it) and re-exported by the client (`client.rs:742`) and the crate root (`lib.rs:67`),
`astream_broker::ack` publishes under `ACK_SEQ_BASE | offset` (`client.rs:792`) and `asb`
imports that constant rather than defining its own, so an ack retried through the OTHER
face — a bridge that shells out to `asb` on one path and links the crate on another — is
recognised as the retry it is and dedups. Pinned by
`broker.ack-key-is-one-wire-contract`; `asb.rs:110-114` states the same rule in the binary's
own module doc. **The alignment is not backward compatible, and nothing on the wire can
catch it** (`client.rs:752-777`, `asb.rs:116-125`): an ack a PRE-alignment library caller
already put on a log sits under `(producer_id, offset)`, so the post-upgrade retry of that
same logical ack is keyed `(producer_id, 2^63 | offset)` — a different key, and a second
answer record rather than a dedup. The dedup map is durable, so no `PROTO_VERSION` reaches
it: the frames are well formed, it is the STORED key that moved (§14).

**The reservation and the WILL FENCE share a number line, and the round-3 pass is what
keeps them apart.** The fence is a per-producer high-water comparison — a registered will
fires only if no record from the SAME producer with a higher `producer_seq` has landed
(`store.rs:1222-1250 stage_will_fire`, against `producer_high_water` at `:1260`). A node's
presence will is registered at `producer_seq = (inc<<32)|0xFFFF_FFFF` (§7), twelve orders
of magnitude below an ack's `2^63 | offset`. Round 2 folded acks into that high water, so
**one ack permanently fenced its producer's goodbye**: `stage_will_fire` refused with
`Fenced`, the refusal reached nobody (a firing is fire-and-forget), every later open
re-attempted and re-failed it, and a dead node read `live` forever. Under a bound cap grant
the pairing is unavoidable — one principal binds one producer id — so this was the DEFAULT
shape of a §6.3 direct consumer that drains with `client::ack` and announces itself with a
`Will`, not a mistake someone had to make. **It is closed in both directions now.** The
reserved half is excluded from `producer_high_water` on all three paths that feed or read
it — the rebuild at open, the durable fold in `index_last`, and the in-flight staged scan
(`store.rs:594`, `:1268`, `:1420`) — and a `Will` offered a sequence at or above
`ACK_SEQ_BASE` is REFUSED at registration with `StageErr::SeqReserved` (`store.rs:1156`),
where the client is still listening, rather than accepted and left permanently unfenceable.
So a single producer id may hold both a presence will and its acks, and **a second
principal for acking is no longer required** — which matters precisely because a bound
grant permits exactly one id. What a caller must still observe itself is the other half of
the reservation: ordinary publishes stay BELOW `2^63` (`asb` enforces it on
`--seq`/`--seq-file`; a library caller does not have it enforced). Pinned by
`broker.will-fires-exactly-once` (a node that registers a will, publishes `live`, acks one
inbox message under the same id and then dies still gets its goodbye) and by the two
registration cases, `ACK_SEQ_BASE | 4` refused and `ACK_SEQ_BASE - 1` fired.

(4) Concurrent `asb pub --seq-file`
invocations on ONE file are serialized by an **exclusive ADVISORY lock** on a sibling
`<path>.lock` (`asb.rs:1205-1227 lock_seq_file`), held across the whole read-modify-write
— read, `+1`, staging write, both fsyncs, rename — with the update staged through a
per-process `<path>.<pid>.new`. The lock cannot live on the sequence file itself, because
the update replaces that file by rename and a second process would hold a lock on an
already-unlinked inode. Being advisory, on a filesystem that answers `Unsupported` (which
is tolerated, mirroring `store::lock_exclusive`) concurrent invocations are back to
racing, and only the per-process staging name protects them. Operationally: `--seq-file`
now creates a `<path>.lock` sidecar beside the counter, which an operator will see in the
directory and should not delete while a publisher is running.

**`crates/astream-pump/src/lib.rs`** — **BUILT** (R10, `pump.attach-subject-and-group`):
`Pump::attach_subject(client, subject, from, cols, rows, profile)` and
`Pump::attach_group(client, commits, group, subject, cols, rows, profile)` +
`Pump::commit()` — the durable cursor `DESIGN-drive-pipe.md §5` requires. Two deviations
from the sketch above, both forced by the built code: `attach_group` takes a **second
connection** for its commits, because `Client::subscribe_group` consumes its connection
into a one-way delivery stream the broker never reads again; and it commits *through*
`Pump::offset()` (the broker's `upto` is inclusive), which makes the group's next start
exactly `Pump::next_offset()` — the same value the client-cursor form must be handed
explicitly. `out_subject` stays the default so `pump.wake-on-boundaries` is untouched, and
the wake-line formatter moved into the library (`wake_line`) so the CLI and an embedder
render a wake identically. `aspump` gained `--group`, `--subject`, `--tcp`, `--key-file`
(the last behind the pump's new `aead` feature, which only forwards to
`astream-broker/aead` — no new third-party dependency). Honest residual: the group form is
at-least-once on wakes, since the commit follows the acted-on wake.

No new crate in astream. The default broker stays zero-third-party and every substrate
crate `forbid(unsafe)`; the `cap`/`aead` features pull exactly the vetted dependencies
they already isolate (`sha2`; `chacha20poly1305` + `getrandom`, `astream-broker/Cargo.toml:14-25`,
`astream-cap/Cargo.toml`, `astream-aead/Cargo.toml`); nothing here needs aterm's tree
(`docs/DESIGN-astream-term.md:441`). No astream doc drift is left for this change to fix:
the two notes this design was drafted against (`DESIGN-astream-term.md` on the AEAD wire
and the enforced mint, `fleet.rs` on the durable causal field) were both closed by the
audit pass's re-sync; only aterm's `subscribe.rs:150-160` roster comment remains (§2).

### 11.2 aterm

**Verb table** (`crates/aterm-types/src/control_verbs.rs`, the single source of truth the
catalog and dispatch are pinned to — the `VERBS` table at `:280`, pinned by
`access_exceptions_are_exactly_the_declared_sets` at `:2106`; these three numbers are
against aterm `fabric/a1-a2` `b1b94e63`, the branch that BUILT A1 and A2, not against
`fe8d4d81` like the rest of this document's aterm citations). `OpClass` is
`Read | Write | Signal | ConfigWrite | ClipboardWrite | Owner` (`:24`) and `Access` is
`Scoped | AnyScopeMeta | OwnerOnly` (`:51`); the fabric adds **one `Access` value,
`BridgeOnly`** (`:83`), and no op-class — the built rows are `Read` for
`inbox`/`inbox get`/`outbox` and `Write` for `inbox seen`/`post`/`deliver`/`hold`/`outbox
sent`, because none of the eight reaches a PTY:

| Verb | `OpClass` / `Framing` / `Target` / `Access` | Grammar and reply |
|---|---|---|
| `inbox` | `Read` / `Lines` / `Session` / `Scoped` | `inbox [<n>] [since=<id>] [--peek] [--meta]` → `OK <n> hold=<0|1> holder=<p|-> seen=<id> bus_head=<off> dropped=<n> pending=<n>` + `msg <id> off=<n> t=<ms> from=<p> kind=<k> trust=<human|agent|relayed|screen> [re=<n> re-id=<id>] [dl=<ms>] [late=1] [demoted=<k>] [via=<p,…>] len=<n> [more=1] text=<pct>` + `post <id> to=<> kind=<> off=<n|->` rows; `--meta` omits `text=` |
| `inbox get` | `Read` / `Bytes` / `Session` / `Scoped` | `inbox get <id>` → the full body, length-prefixed |
| `inbox seen` | `Write` / `Status` / `Session` / `Scoped` (write-gated like `meta set`) | `inbox seen <id> [handled|refused|deferred]` → `OK seen=<id>`; pushes `EVENT <local> inbox-seen <id> off=<n>` |
| `post` | `Write` / `Status` / `Session` / `Scoped` — **refuses `Scope::Edge` in the handler** | `post to=<@<sid>[@<node>]|<principal>|say> kind=<ask|answer|task|report|note|ack|control> [re=<n>] [dl=<ms>] [via=<p>] [--wait[=<ms>]] (<text ≤ 4 KiB> | len=<n> + raw bytes ≤ 256 KiB)` → `OK <id> [off=<n>]`; `--wait` defaults on for `ask`/`task`; no `to=fleet` (a node holds no fleet rw grant); recorded in `timeline` as `post`, later `post-landed id= off=` |
| `deliver` | `Write` / `Status` / `Meta` / **`BridgeOnly`** | `deliver <sid> off=<n> from=<p> kind=<k> [re=<n>] [dl=<ms>] trust=<…> [via=…] [demoted=<k>] [len=<n>] [text=<pct>]` → `OK <id>` (idempotent on `off=`; `ERR quota` past 64 unread rows from that `from=`); `deliver <sid> landed=<post-id> off=<n>` → `OK` |
| `hold` | `Write` / `Status` / `Meta` / **`BridgeOnly`** | `hold <sid> on|off [reason=<pct>] [origin=fleet|local]` → `OK hold=<0|1>`; while on, the PTY-reaching verbs (§5.3) resolving to that session, from **any** socket scope, answer `ERR halted <reason>` at dispatch — the same seam as the self-feed floor (`crates/aterm-gui/src/control.rs:5512-5523`); `post`, `inbox seen`, `meta set`, `lease` and every `Read` verb are exempt; PTY keyboard input is unaffected |
| `outbox` | `Read` / `Bytes` / `Meta` / **`BridgeOnly`** | `outbox [<max>]` → `OK <nbytes>` then that many raw bytes: one `post sid=<s> id=<n> to=<pct> kind=<k> [re=<n>] [dl=<ms>] [via=<p,…>] len=<n>` line per queued post, each followed by its `len` body bytes. A **peek** — it moves no watermark and drops nothing, so a bridge that dies mid-publish re-reads the same posts and republishes them under the same producer sequence, which the broker's `(producer_id, producer_seq)` dedup then collapses |
| `outbox sent` | `Write` / `Status` / `Meta` / **`BridgeOnly`** | `outbox sent <sid> <id> off=<n\|->` → `OK`; fills the `post` row's `off=`, releases a `post --wait` parked on it, and is what lets the endpoint drop the retained body. `off=-` retires it as permanently undeliverable (`post --wait` then wakes with `ERR undeliverable`). Idempotent: retiring twice is `OK`, not a second event |
| `await inbox` | (an `await` predicate) | `await inbox since=<id> [kinds=<k,…>] [timeout=<ms>]` → latches on a row with id > `since` of a listed kind (default: all but `note`), or on a `hold` change iff `hold` is listed; exit 124 on timeout like every `await` (`docs/INTROSPECTION.md:615-617`) |

**A1 through A10 are BUILT (aterm) — test-cited, not manifest-cited** (aterm has no claim
ledger), on branch `fabric/a1-a2` at `a3936e5f2`: `f08b9bcb` (the verb rows and
`BridgeOnly`), `466b2da4` (the endpoint: ring, hold gate, `Scope::Bridge`), `2c016005`
(the outbound plane and `aterm_uds::spawnfd`), `a0970345` (the launcher), `5320c6c3`
(the bridge), then A4–A10 and two adversarial audit rounds on top. `cargo test -p
aterm-types control_verbs`, `cargo test -p aterm-gui inbox_hold`, `cargo test -p aterm-gui
feed_idempotent` and `cargo test --manifest-path aterm-link/Cargo.toml` run them; §12
names each rung's own test. **What is still not built is named in place throughout this
section and in §15** — chiefly `serve`'s `--wake-budget`/`--exited-keep`/`--presence-title`/
`--receipts`/`--lash`/`--glance`/`--mirror` flags, the `<state>/wake.sock` push lane and
`aterm-link wake`, `lash`, `pin`, the `expired` deadline verdict, the barrier
`busy`/`absent` auto-answers, and ten of §4.2's presence fields. **The register after the
`serve` spec lists every place the built code decided something this document left open or
contradicted it** — an entry there is the record catching up with the code, not a
failure.

Why `post` refuses `Scope::Edge`: a write-input edge holder over session S would
otherwise speak *as* S; the sender of a `post` must be attested by the instance Owner
(an in-session `aterm-ctl @self` is Owner scope, `crates/aterm-gui/src/control.rs:3975-3977`) — a documented
per-handler check of the same kind as `family`'s explicit-sid form
(`docs/INTROSPECTION.md:737-742`).

**`Scope::Bridge` — an authority that is a connection, not a token.** Owner scope is
what every in-session client already holds, so `deliver` (which stamps `from=` and
`trust=`) and `hold` (which lifts a fleet halt) cannot be Owner verbs: a prompt-injected
agent could forge an attested human order into a sibling's inbox or lift the halt
locally. Instead the instance **launches the bridge itself** — `[fabric] command =
"aterm-link serve …"` in `aterm.toml`, default off exactly like the embedded operator
(`ATERM_OPERATOR=1`, `crates/aterm-gui/src/operator_host.rs:4,66-67`) — as a child
process holding fds 3 and 4, the far ends of two `socketpair(AF_UNIX)`s; the control
server serves the near ends through its ordinary request loop with `Scope::Bridge`
pre-resolved instead of an `AUTH` line (the pre-resolved bridge lane at
`crates/aterm-gui/src/control.rs:3915-3944`, reached through `serve_bridge` at
`:2283-2299` and `attach_fabric_bridge` at `:2370`; `Scope` at `:522-558`, its `Bridge`
variant and the reason for it at `:543-557`; the Owner tier the bridge does NOT take is
`:3975-3977`). `Bridge` has Owner's power plus the `BridgeOnly` verbs (`deliver`, `hold`,
`lease … holder=fabric:*`), which **no other scope may call, Owner included**. No token
file exists to steal; the only way to be the bridge is to be the process aterm spawned.
When either fd closes (the bridge exited or was killed) the instance applies `hold on
reason=fabric-lost origin=fleet` to every session the bridge ever `deliver`ed to or held
— the halt **must not depend on a killable process staying alive** — until a bridge
reconnects (the instance relaunches the child with back-off) or a human lifts it at
the GUI. `status` gains `hold=<0|1>` and `fabric=<connected|disconnected|absent>`
(additive fields, `help_catalog_full.txt:34`). A bridge started by hand with the Owner
token (`aterm-link serve --sock`) runs in **observer mode** — presence and `ev` only, no
delivery, no hold — and says so.

`EVENT <local> inbox <id> from=<p> kind=<k> off=<n>`, `EVENT <local> inbox-seen <id> off=<n>`,
`EVENT <local> post <id> to=<> kind=<> [re=] [dl=]`, `EVENT <local> post-landed <id> off=<n>`
and `EVENT <local> hold <0|1> reason=<pct> origin=<>` join the digest through the one
`timeline_wire_kind` table (`crates/aterm-gui/src/subscribe.rs:1029-1045`); none carries a
body. `deliver`, `hold`, `outbox` and `outbox sent` are the pinned `BridgeOnly` set in
`access_exceptions_are_exactly_the_declared_sets` (`control_verbs.rs:2106` on
`fabric/a1-a2`), which also asserts the three access sets are pairwise disjoint and pins
`inbox`/`inbox get`/`inbox seen`/`post` as ordinary `Scoped` rows, so neither plane can
drift into the other unargued; the catalog fixture regenerates. Optional: `EVENT <local> turn
<id> … by=<sid|owner|->` (the `closing by=` precedent, `subscribe.rs:91-92`, delivered from the events pass at
`:2109-2110`) —
**DESIGNED**, low priority.

**The idempotency key at the PTY seam — BUILT (aterm), A6** (`crates/aterm-gui/src/pty_idem.rs`;
`cargo test -p aterm-gui feed_idempotent`): `send|key|feed-bin|turn … id=<epoch>:<producer>:<seq>`
keeps a per-session, per-producer high-water mark beside the turn lease, in the caller's own
authority realm, and answers an already-consumed sequence **`OK dup=1`** — `OK 0 dup=1` for a
`Lines`/`Bytes`-framed verb, since a bare `OK dup=1` would make a `Lines` client read `dup=1`
as a row count — without writing. Control-plane bookkeeping, no engine change, the
exactly-once-at-the-sink half of B6. Four answers, not two: above the mark is the verb's own
reply, at or below it and applied is `OK dup=1`, at the mark and still running is `ERR busy
idem=<seq>`, and at the mark with the outcome UNKNOWN is `ERR in-doubt seq=<seq>` — the row
the rung exists for, because `cmd_turn` can type its text and then fail to submit, so the
mark is kept and the session's `timeline` carries an `in-doubt` row a human can read. §11.2
register entries 16 and 17 carry the deviations and the bounds. The four verbs are exactly
§11.2's set: `feed`, `paste`, `ctrl` and `paste-bin` take no key, so a driver on
`tools/aterm-astream-bridge`'s `feed` (hex) path gets no exactly-once until it moves to
`feed-bin`; and `aterm-ctl feed-bin` cannot pass one either (its client path refuses any
inline token after the verb), so the key is reachable only by a direct socket client — which
is exactly what the bridge is.

**Env hygiene:** `ATERM_LINK_BROKER`, `ATERM_LINK_CAP_FILE`, `ATERM_LINK_FLEET` join
`ENV_DENY_VARS` (`crates/aterm-types/src/env_sanitize.rs:127-186`) so a nested aterm
inherits no fabric credential.

**The one aterm-side crate: `aterm-link`.** The crate `docs/DESIGN-aterm-lash.md:57-59`
(astream's docs tree) and `docs/DESIGN-drive-pipe.md:157` already name, realized as a
resident bridge rather than a python demo. Both documents now tag the stand-in scripts
**HAND-RUN**, not BUILT: `tools/aterm-link` and `tools/aterm-astream-bridge` are run by
hand and **no test in either repo runs them** (`DESIGN-drive-pipe.md:157,416,434,437`), so
nothing they do is evidence for anything below. Its dependencies, precisely: `astream-broker` (client + proto, features
`cap`, `aead`) and hence `astream-wire`, `astream-cap` and `astream-aead`; `aterm-uds` (no
dependencies); `aterm-types` with default features (its `serde` feature stays off; it
brings the in-tree `aterm-alloc`, `aterm-error`, `aterm-log`, `aterm-time`). The
third-party set is therefore **exactly the two vetted crypto dependencies the
`cap`/`aead` features already isolate — `sha2`, and `chacha20poly1305` + `getrandom` —
plus whatever those four small aterm crates pull**, which A1 pins with a `cargo tree`
check; none of aterm's ~40-crate engine tree. The crate needs no hash of its own: the
epoch is the nonce verbatim (§7) and producer ids come from `astream-cap`. It lives in
the aterm repo **in its own workspace** (`aterm/aterm-link/`), exactly like
`aterm/astream-oracle/Cargo.toml:20-30` (its own `[workspace]`, a path-dep on a sibling
checkout: a dormant forward reference, in no gate), until astream is packaged.

The built command line, and the design's own that is not (a flag or verb absent below is
absent from the binary — `main.rs`'s `USAGE` is the source of this block):

```
aterm-link serve  --fleet <F> --broker <ep> [--tcp] [--key-file PATH] --cap-file <path> [--cap-file …]
                  [--state DIR] [--accept-from <p>,…] [--screen <sid|all>,…]
                  [--sock <path> --token-file <path>]   # hand-started observer mode: presence + ev only
aterm-link ls     [--attention]                   # Last{/f/<F>/pub/*/*/presence}, across hosts
aterm-link hook   install claude [--rewake] | run <session-start|user-prompt-submit|pre-tool-use|stop>
                  [--timeout <s>] [--accept-from <p>,…] [--wake-budget <n>/<min>] [--state DIR]
aterm-link notify --on <attention|ask:<p>|halt>,… --exec <cmd> [--rate <n>/<w>] [--since head|start|<off>]
                  [--once] [--exec-timeout <ms>]  + serve's transport/cap/state flags
aterm-link mirror <root> --sock <path> [--session <sid>…] [--interval <ms>]   # `--mirror <root>` also accepted
aterm-link glance --fleet <F> --broker <ep> --cap-file <path>… [--state DIR]  # writes <state>/fabric/glance.json
aterm-link tui    [--from <offset>]               # the fabric as a session

# refused BY NAME, with the reason, rather than silently absent:
aterm-link wake | pin | lash
serve --wake-budget | --exited-keep | --presence-title | --receipts | --lash | --glance | --mirror
serve --handshake | --identity | --identity-file | --host-key-file
```

**Three of the design's `serve` flags became their own subcommands, and one moved.**
`--mirror`, `--glance` and the hook/notify egresses are separate processes because none of
them needs bridge authority — the mirror speaks only `sessions`, `inbox` and `post`, all
ordinary `Scoped` verbs, so keeping it out of the bridge keeps the plane a sandboxed agent
writes from ever reaching the bridge plane — and because wiring each into `serve` is a line
in `bridge.rs`'s run loop that its rung did not own. `--wake-budget` moved to `hook run
stop` for the reason §5.6 gives. `--exited-keep`, `--presence-title`, `--receipts` and
`--lash` are unimplemented. The §8.6 transports are refused by NAME with the reason
printed, not silently absent: `--handshake` would add x25519-dalek and `--identity`
ed25519-dalek on top, and §11.2 pins this crate's third-party surface to exactly `sha2`,
`chacha20poly1305` and `getrandom` — §8.6 and §11.2 contradict each other here and only one
can hold; the pin won, and `asb` serves no `identity` listener to reach anyway.

`serve` per instance: publishes `ev`, `presence`, `say` and outbound `post`s under the
node's bound cap (persisted `producer_seq` written before each publish; `inc` from local
state and its own last presence row); registers the `Will` on every connect; drains
`/f/<F>/in/<node>/>` as group `/f/<F>/cur/<node>/node/inbox` into `deliver`, committing
after `OK`, and drains the `fleet/>` tail **ahead of** the inbox group on every
scheduling round so a halt never queues behind a redelivery backlog; mirrors `control`
↔ `lease`; records `undeliverable` verdicts; publishes `GAP` frames as `ev`
records instead of dropping them; persists `seen_off` and refills rings; keeps
fleet-origin holds sticky; acks halts. Three corrections to that list. Outbound posts queue
in the ENDPOINT's outbox — bounded, refused at the door — and the bridge simply does not
drain while disconnected, rather than there being a second queue in the state dir that could
disagree with the first about what is still in flight. `expired` verdicts are **not**
recorded (§6.4). And `glance.json` is written by `aterm-link glance`, not by `serve`. The
bridge is also only lightly bounded against a hostile broker: bodies are capped by the
endpoint (256 KiB) and by the ring quota, but the bridge itself buffers records as fast as
the broker delivers them — no rate budget, no `--wake-budget`. On a reconnect it tears down
and re-opens ALL subscriptions (closing the old ones first, so nothing double-delivers), so
a transient loss of one connection costs four; a per-source reconnect is the obvious later
refinement. `aterm-fleet events`' NDJSON record keeps its
shape as a *presentation* of the same `ev` body (`fleet_cli.rs:639-647`), so nothing
above the transport changes, as its header promised (`:26-28`).

**Where the built code decided something this sketch left open, or contradicted it.** Each
is named in the code it landed in; this register is the design catching up, in the same
shape as §11.1's. Entries 1–11 are A1/A2's; 12–21 are A3–A10's.

1. **The bridge plane is four verbs, not two.** §11.2 named no verb by which a bridge
   READS a queued outbound post's body, so the `serve` spec above ("publishes … outbound
   `post`s under the node's bound cap") was unimplementable. The built answer mirrors the
   inbound plane — `deliver`/`inbox seen` in, `outbox`/`outbox sent` out — and both new
   verbs are `BridgeOnly` for the reason `deliver` is: an Owner-token connection reading
   `outbox` would read every session's outbound traffic, and one forging `outbox sent`
   would release a `post --wait` for a message that never left the machine. The pinned set
   is now `{deliver, hold, outbox, outbox sent}`, widened by argument rather than by count.
2. **`outbox` is `Bytes`-framed, and it is a PEEK.** A body may contain newlines, so it
   cannot ride a `Lines` row; and retirement is a separate act, so a bridge that dies
   mid-publish re-reads the same posts and republishes them under the same producer
   sequence, which the broker's own dedup collapses. That is what makes the pair
   exactly-once at both ends.
3. **`deliver <sid> landed=` and `outbox sent` are ONE implementation.** Two names for one
   transition would be two chances to disagree about the watermark. `outbox sent … off=-`
   adds the case §11.2's form could not express — permanently undeliverable — and a
   `post --wait` parked on such a post wakes with `ERR undeliverable` instead of sitting
   out its timeout.
4. **The outbound queue is bounded twice and REFUSES at the door** (128 rows AND 4 MiB;
   `ERR outbox full`). Two bounds because 128 four-byte messages and 16 quarter-megabyte
   ones are the same hazard from opposite directions. Unlike the inbox ring it never
   evicts: an inbox row that is dropped is still on the log and the loss is reported, but a
   dropped OUTBOUND message has no sender-side record anywhere — the sender was told `OK`
   and the bus never saw it.
5. **Byte-exactness is NOT claimed end to end.** `outbox`'s length prefix buys framing, not
   byte-exactness: `ControlReply` is `String`-typed, so a non-UTF-8 body is lossy-converted
   at `post` exactly as `inbox get`'s is on the way in. A byte-exact outbound path needs a
   bytes-carrying reply, which is a wider change than one verb pair should smuggle in.
6. **`inbox`'s `OK <n>` counts EVERY row that follows**, `post` rows included — the
   `Lines` framing the row declares wins, or a client truncates the reply. §9.1's
   illustration showed `OK 2` over three rows and has been corrected here.
7. **`pending=` means "delivered rows past the LISTED watermark this reply did not
   carry"** — §5.6's reading needs the bridge's allowlist, which the endpoint does not
   have. Two watermarks, and the difference is the ergonomics: a bare `inbox` moves LISTED,
   `inbox seen` moves SEEN (the durable one), `--peek` moves neither.
8. **A `post` row carries `len=` and the endpoint RETAINS the outbound body** until
   `outbox sent` — which is what bounds the queue's memory, and what deviation 1 exists to
   consume.
9. **`post --wait` with no bridge answers `ERR fabric absent id=<n>` at once** rather than
   parking to a certain timeout. The post is queued and `inbox` lists it.
10. **`await inbox`'s hold arm latches on a transition observed AFTER the wait armed** — a
    halt already in force is not news.
11. **The fail-closed halt is a DROP GUARD, and the bridge is served inline.** A halt
    reachable only on the happy path is not fail-closed, so `BridgeLostGuard` fires on any
    end of the connection (child exited, SIGKILLed, fd closed, thread unwound) and holds
    every session that bridge delivered to or held. Its push half (`subscribe @*
    events,sessions`) is therefore served on the bridge's own thread rather than handed to
    the subscription pool: handing the connection away would fire the guard the moment the
    bridge flipped to push mode, with the bridge alive and watching. (It also keeps this
    design's lane accounting honest — a resident child costs none of the `CONTROL_WORKERS`
    lanes §14 counts.)
12. **The launcher is BOTH a config key and an env var, and the env wins.** §11.2 named
    only `[fabric] command` in `aterm.toml`; A3 added `$ATERM_FABRIC_COMMAND` beside it,
    because the design's own parenthetical cites `ATERM_OPERATOR=1` as the precedent, env >
    config is the precedence every other launch knob in this process follows, and it is what
    makes the end-to-end test hermetic. `ATERM_FABRIC_COMMAND` joined `ENV_DENY_VARS` in the
    same change, so a nested aterm cannot inherit it and start a second bridge under the
    outer node's identity.
13. **The fd-3/4 inheritance is `aterm_uds::spawnfd`, not new unsafe.** std can place an
    inherited descriptor at 0, 1 or 2 and nowhere else, so fd 3 needs `dup2` between fork
    and exec. It landed in `aterm-uds`, which is ALREADY aterm's cordoned raw-descriptor
    module (`fdpass`'s `sendmsg`/`recvmsg`, `process`'s `kill`); the `pre_exec` closure calls
    `dup`/`dup2` and nothing else — both on POSIX's async-signal-safe list — allocates
    nothing, locks nothing and formats no error, so the obligation is met by construction.
    astream's `forbid(unsafe_code)` is untouched by any of it.
14. **The bridge reads the session's epoch off the `sessions` roster row, and A3 added the
    field to do it.** §7 said "read by the bridge via `whoami`"; `whoami` reports the
    CONNECTION's own session and refuses a selector, and the bridge's connection is not a
    session's, so the statement was not implementable. `nonce=<hex32>` is now an
    Owner-only column on the roster row, immediately after `meta=` (§7).
15. **The halt ack is one retained subject per NODE carrying `re=<offset>`, not one subject
    per halt.** The per-halt shape §5.3 asked for spends a node's
    `MAX_SUBJECTS_PER_PRODUCER` budget permanently and unrecoverably; §5.3 states the
    trade, the narrower answer it gives a counter, and the durable watermark that keeps a
    reconnect from re-acking every historical halt.
16. **A6's idempotency key is three fields, `<epoch>:<producer>:<seq>`, and the duplicate
    answers `OK dup=1` — not `OK seq=<n> dup=1`.** §11.2 spelled the reply with a `seq=`
    token; that token is already taken on that exact line with a different meaning (R13's
    `stamp_input_seq` appends the grid content baseline `await seq <n+1>` reads, and it runs
    AFTER this gate returns), so emitting both would put two `seq=` with two meanings on one
    line. The caller's own sequence is echoed only where it disambiguates: `ERR in-doubt
    seq=<n>` and `ERR busy idem=<n>`. Carrying the epoch IN the key makes "a relaunched
    session starts a fresh high-water" a checked rule (`ERR epoch`) rather than an accident
    of allocation. The marks are bounded — `PRODUCER_CAP` is 64 producers per session,
    LRU-evicted, and an evicted producer's replay is applied again rather than recognised;
    a still-running producer is never evicted. A sequence strictly BELOW the mark answers
    `OK dup=1` even if its own attempt was the in-doubt one, because only the TIP's outcome
    is remembered. And an Owner-scope connection can burn another driver's sequence by
    guessing — not an escalation, since Owner scope can already type arbitrary bytes, but a
    way to make a legitimate driver's key look consumed.
17. **`ERR in-doubt` is TERMINAL for that sequence, not a transient class.** A driver that
    blindly retries the same id on any error loops against it. The help text says so;
    nothing enforces it.
18. **`--wait` grew two failure replies the design did not spell**, and `outbox sent … off=-`
    grew `reason=<word>`. §6.1 states what the non-waiting sender can and cannot see.
19. **A session presence row published in observer mode carries `observer=1`**, and such
    rows are excluded from §6.1's advertiser set and from the holder-liveness check.
    Unmarked, §11.2 and §6.1 combine into a live bug: an observer advertises sessions it
    does not host under its own node id, so opening a read-only observer would make every
    session it can see `ERR ambiguous` fleet-wide. Faking the flag can only REMOVE a node
    from the candidate set, never add one, so it fails safe.
20. **`ev` records go on the SESSION's `ev` face when a session is known** —
    `/f/<F>/pub/<node>/<sid>/ev` — and on the node's otherwise. A3 published every one on
    the node face with the session named only inside the pct-encoded payload, so §10's
    causal pointer belonged to no partition in the crate's own consistent-cut machinery and
    a reader scoped to `ro:/f/<F>/pub/<n>/<sid>/>` could not see its own session's `ev`.
21. **`inbox get` is not byte-exact, and neither is `post`.** Both go through a pct-decode
    / `String`-typed `ControlReply`, which is lossy for invalid UTF-8, and a delivered body
    is truncated at the bridge's `deliver` request line (§9.1). The `outbox` length prefix
    buys FRAMING — a body may contain newlines — not byte-exactness. `inbox get --bytes` is
    **DESIGNED**.

Two consequences worth carrying forward. `SHORT_CATALOG_MAX_BYTES` moved 8192 → 9216 to
fit the two new rows: the budget bounds the SHAPE (one row per verb, first sentence, capped
at `SUMMARY_MAX_CHARS`) and rewording an unrelated verb's help to make room is exactly the
drift a generated golden exists to catch. And the fd-3/4 inheritance the launch above
specifies landed as `aterm_uds::spawnfd`, in aterm-uds because that crate is ALREADY the
cordoned raw-descriptor module (`fdpass`'s `sendmsg`/`recvmsg`, `process`'s `kill`); its
`pre_exec` closure calls `dup`/`dup2` and nothing else — both on POSIX's async-signal-safe
list — so the obligation is met by construction rather than by review. **astream's
`forbid(unsafe_code)` is untouched by any of this**: the unsafe is aterm's, in aterm's
existing cordon.

---

## 12. Build ladder

Each rung is a falsifiable `[[claim]]` in `evidence/manifest.toml` with the exact
command; every test is in-process, std-only, no sleeps — synchronize on acks and known
delivery counts (`crates/astream-broker/tests/exactly_once_pubsub_resume.rs:1-6`) — and
lands with `make render && make ci` (`Makefile`). The gate lints apply
(`lint_tautological_tests`, `lint_verify_isolation`, `lint_doc_tamper`,
`lint_manifest_integrity`, `crates/astream-evidence/src/gate.rs:714,748,822,953` — the
gate also now skips hidden directories, tool state never source; a `test` claim — or any
`cargo test` command, whatever kind it is labelled — that runs zero tests fails,
`runner.rs:262-273`). No effort estimates sit
beside claim ids.

| Rung | Claim id | Command | Asserts |
|---|---|---|---|
| **R1** last-value + fan-out | `broker.last-value` | `cargo test --locked -p astream-broker --test last_value` | publish A@0, B@1, A@2, C@3 (C outside the filter); `Last{/x/>, "", 64}` delivers exactly {A@2, B@1} in subject order then `Mark{next=4, head=4}`; the connection then publishes D@4 and `Subscribe{from=4}` on the same connection delivers D with no gap and no dup; **consistency under pipelining**: while a second connection holds a staged, unpromoted window of 512 publishes (`broker.pipelining`'s shape), each of 64 snapshots pairs its page with a `head` that no record in that page reaches (`next == head`, every page offset `< head`), and a from-0 subscribe then yields the whole burst exactly once, dense, ending one below that mark (`head` read under the log lock, not the atomic; the test never learns the first staged offset, so it asserts the page-vs-head invariant, not a head-vs-staged-offset one); **paging**: `max=1` over 8 subjects, each page consistent, the union equal to the single-page snapshot; a REAL `/a/commit` record at a real offset is in neither a `Last{/a/>}` page nor a wildcard `Subscribe{/a/>}`, and a client publish to `/a/commit`, `/a/will` or `/a/bind` is refused as a `reserved subject`, appending nothing and burning no idempotency key (a real `/a/bind` record's exclusion from a page, a fetch and a delivery is R4's `broker.cap-keyring-enforced`); after `Broker::open` the snapshot is byte-identical (index rebuilt); **late-joiner equivalence**: the snapshot equals the last-per-subject of a from-0 subscribe; **subject bound**: the 4097th distinct subject under one producer is `Error 5`; **fan-out**: 16 concurrent subscribers on one filter each receive every one of 1 000 records exactly once, synchronized on delivery counts |
| **R2** bounded read | `broker.fetch-bounded` | `cargo test --locked -p astream-broker --test fetch` | `fetch(from, &Filter, max, scan_max, visible)`: with `scan_max=64` a page with zero matches returns no `Delivery` and `Mark{next = from + 64}`, and repeated paging over a 10 k-record log with a 1-in-1 000 filter reaches every match exactly once; with the default `FETCH_SCAN_MAX` a 70 k-record log pages past the cap gapless and dup-free; `max=0` is the head query; the connection publishes again afterwards (non-terminal); pending pipelined acks are flushed before the reply; `/a/commit` never delivered |
| **R3** grant string | `cap.grant-mode-and-producer` | `cargo test --locked -p astream-cap` | a bare filter mints and verifies as `rw` unbound (every existing test unchanged; RFC 4231 vector pinned); `ro:` verifies as read-only; `rw,p=<principal>:` binds `producer_id_of(principal)`, and two distinct principals derive distinct ids on a fixed vector; a widened filter, a flipped mode, or a changed principal with the old tag, and the wrong secret, are all rejected; `Grant::parse` refuses an invalid filter half, a principal outside the class-prefixed `[a-z0-9-]{1,32}` grammar, or one containing `:`; `attach_proof`/`verify_attach` round-trip and reject a wrong nonce, tag or grant |
| **R4** keyring + PoP + enforcement | `broker.cap-keyring-enforced` | `cargo test --locked -p astream-broker --features cap --test cap_keyring` | `Attach` without `Hello` → `Error 5`; a genuine proof → `Mark` **before** any other request; a forged proof → `Error 5`; **a captured `Attach` frame replayed on a second connection is refused**; ro `/f/F/>`: `Subscribe`/`Last`/`Fetch` ok, `Publish`/`Commit` → `Error 5` (a `Will` under a read-only grant is R5's command, not this one); ro `/f/F/fleet/>` + rw `/f/F/cur/n1/>` on one connection: `SubscribeGroup{group=/f/F/cur/n1/node/x, filter=/f/F/fleet/>}` ok; ro alone → refused; 17th attach → refused; **dedup-key poisoning closed**: under `rw,p=A:…` a publish with `producer_id ≠ producer_id_of(A)` is `Error 5` and B's later genuine publish is **not** deduped; **binding table**: a grant whose derived id is already bound to a different principal is refused at attach (unit-tested on the table with a forced collision, since a real SHA-256/64 collision is a 2^64 search) and the refusal survives a broker restart (`/a/bind` rebuilt); an UNBOUND rw grant still publishes under any producer id — the god cap, kept deliberately (the warn the broker logs at such an attach is a code path no test here captures); **`Replicate` needs an UNBOUND link grant**: `replicate_needs_an_unbound_link_grant_and_a_bound_one_cannot_reach_it` (`cap_keyring.rs:401`) asserts that an unbound `rw` grant authorizes a replicated record on subject + carried group while a BOUND `rw` grant is refused — under a foreign producer id and under its own derived one alike. The producer binding is not "skipped": a leader ships the ORIGINAL producer's id, which no bound principal could ever derive, so the link grant is a distinct, deliberately unbound authority (§8.2). Beside it, `a_bound_grant_cannot_burn_a_peers_dedup_key_through_replicate` (`:497`) is the dedup-poisoning attack this rule closes, and `a_hidden_subject_cannot_be_injected_by_replicate_into_a_log_this_broker_owns` (`:560`) is the `/a/will`//`a/bind` guard; a forged `<src>` (`/f/F/in/n2/s2/s9/ask` under `…/in/*/*/s1/*`) → `Error 5`, an 8-segment `/f/F/in/n2/s2/s1/h-andrew/answer` → `Error 5` (the `*` grant), while `/f/F/in/n2/s2/s1/ask` lands and is delivered with that subject |
| **R5** will | `broker.will-fires-exactly-once` | `cargo test --locked -p astream-broker --test will` | a subscriber on S is opened first; a connection registers `Will{7, (1<<32)|0xFFFF_FFFF, S, "… inc=1 gone"}` and gets `Mark`; dropping it without goodbye delivers the will as delivery k, and a sentinel published by a third connection is delivery k+1 (no intervening record); a second scenario publishes the reserved key itself then drops → the sentinel is the very next record after the goodbye; **fence**: `live inc=2` published from a new connection with seq `(2<<32)|1`, then the old connection drops → zero records appended, `Last` returns `live inc=2`; with `cap`, a will outside the rw grant or under a foreign producer is `Error 5`; **restart**: a registered will and a client killed while the broker is closed → reopen fires exactly one `gone`; a client that reconnects and publishes `live inc+1` supersedes it; a will already fired never fires twice; **one producer id per connection** — a second `Will` under a DIFFERENT producer id is `Error 5` (`a_second_will_under_a_different_producer_id_is_refused`) while a second under the SAME one replaces (`a_second_will_replaces_the_first`); a hidden subject is refused (`a_will_on_a_hidden_subject_is_refused`); **the replica rule** — a follower's restart fires none of the leader's wills (`a_follower_restart_does_not_fire_the_leaders_wills`); and the store's own two rules, the producer high-water fence and the open-time pending set, asserted against a log that really holds two wills under one producer (`the_fence_and_the_pending_set_are_the_stores_own_rules`) |
| **R6** inbox drain + ack | `broker.inbox-drain-ack-exactly-once` | `cargo test --locked -p astream-broker --test inbox_drain` | `client::drain` over two connections: crash-before-commit redelivers, crash-after-commit does not; `client::ack` is one PnP: a retried ack is `deduped=true`, appends nothing, and the cursor moved exactly once; `ask` at `R`, `answer re=R` on the asker's lane is found by its drain; `ForkSubscribe{fork_at=R}` replays the exchange with a swapped ask, live log untouched |
| **R7** barrier | `broker.barrier-count-by-last` | `cargo test --locked -p astream-broker --test barrier` | barrier at `B`; 4 members ack, one twice with the same producer key; an `ack/<B>` pre-published at an offset below `B` is ignored; `Last{/f/F/pub/*/*/ack/B}` = 4 counted records; missing = presence − acked = the fifth; a `refused` ack counts as answered |
| **R8** CLI | `broker.cli.fleet-verbs` | `cargo test --locked -p astream-broker --features cap --test cli_fleet` | `asb mint` (explicit mode; the unbound read-write grant refused without `--legacy-unbound`, in both spellings — `/f/F/>` and `rw:/f/F/>`), `--cap-file` (and yesterday's `--cap-filter`/`--cap-tag` on argv refused), `last`/`fetch`/`drain`/`ack`/`pub --seq-file` byte-exact framings; `drain --peek` commits nothing; a second `drain` resumes past the committed batch without dup. The command carries `--features cap` because minting and attaching need the same vetted MAC the broker verifies with; and the no-dup half is proved by the *resume*, not by a kill mid-print — `drain` commits before it prints (the library helper's order), so a crash there loses the batch and `--peek` + `asb commit` is the at-least-once shape. **Three behaviours `cli_fleet` does NOT exercise** — concurrent `--seq-file` invocations, `last` paging past the broker's own row/scan bounds, and a cap-file grant containing a space — are covered by `cli_defects.rs`, which the manifest carries as `broker.cli.defect-regressions` (§12). `cli_fleet`'s byte-exact `MARK next=… head=…` assertions (`:373,379,383,404,745`) still hold: the round-2 fix paged `last` internally rather than adding a `resume=` field to the MARK line |
| **R9** sealed | `broker.cli.fleet-sealed` | `cargo test --locked -p astream-broker --features "aead cap" --test cli_fleet_sealed` | R8's flow over `--tcp --key-file` on loopback with two nodes' caps; a wrong key never attaches; an `Attach` frame recorded from one sealed connection is refused on another |
| **R10** pump | `pump.attach-subject-and-group` | `cargo test --locked -p astream-pump --test pump` | `attach_subject(/f/F/term/n1/s1/out)` yields the same wake lines as `attach(sid)` on `/a/stream/term/s1/out`; `attach_group` resumes from the durable commit across a pump restart with no missed or doubled boundary |
| **R11** budget | `broker.proto.tag-budget` | `cargo test --locked -p astream-broker --lib proto` | exactly twelve request tags and five response tags decode — including `0x08`, which still decodes as `Replicate`; every other byte → `None`; and the version byte gates ALL SEVENTEEN, requests and responses alike — each declared tag is re-decoded under `PROTO_VERSION + 1` over the same 64-zero-byte body the sweep above just proved its parser accepts, so the only thing refusing the frame is the version (the earlier loop covered the twelve requests only) |
| **R12** bench floors | `broker.bench.last-floor`, `broker.bench.fanout-floor` | `SUBJECTS=10000 HISTORY=200000 cargo run --quiet --release --locked -p astream-broker --example broker_last_bench`; `SUBS=64 BENCH_N=20000 … --example broker_fanout_bench` | `kind = "bench"` claims in the manifest's shape (`command`/`metric`/`min_value`, cf. `broker.bench.replay-egress-floor`, `manifest.toml:332-338`): `Last` over 10 k subjects with 200 k history answers a 4 k-row page within a stated floor (queries/s) with the writer lock held only for the page; 64 live subscribers on one filter sustain a deliveries/s floor; both floors set far below observed, gating structure not hardware |

**Where the round-2 regression tests sit on the manifest.** The round-2 fix pass added six
test files. An earlier draft of this section said they had no manifest row and named the
ids a later pass "should" give them; that is no longer true, and naming ids the manifest
does not use would have had the next pass duplicate three claims that already exist. Each
file is now run by a green claim's own command, so a regression in it fails the gate:

| Test | Runs under | Claim |
|---|---|---|
| `crates/astream-broker/tests/broker_core_regressions.rs` (8 tests) | folded into five existing commands rather than given a row of its own — each property is asserted in the TEXT of the claim that runs it | `broker.last-value` (the resume cursor never names a subject outside the filter), `broker.replicated-tier`, `broker.cap-enforced-on-attach`, `broker.will-fires-exactly-once` (one producer id per connection; the distinct-subject bound at REGISTRATION; the registration acked on the LOCAL commit; an echoed `Replicate` does not convert an owned log), `broker.inbox-drain-ack-exactly-once` (a fork snapshot ends with a `Mark`, not a bare EOF) |
| `crates/astream-broker/tests/cli_defects.rs` (5 tests) | its own row | `broker.cli.defect-regressions` |
| `client_idle_frame_atomic.rs`, `client_sealed_idle.rs`, `client_sealed_resume.rs` | its own row | `broker.drain-idle-window-frame-atomic` |
| `crates/astream-pump/tests/aspump_argv.rs` (2 tests) | its own row | `pump.cli.argv-not-utf8` |

So where this document names `broker.drain-idle-window-frame-atomic` (§6.3, §11.1
deviation 4) it is naming an existing green claim, not a pending row. Note the two ids that
are NOT what an earlier draft guessed: the CLI row is `broker.cli.defect-regressions` (not
`broker.cli.r2-defects`) and the pump row is `pump.cli.argv-not-utf8` (not
`pump.cli.argv-utf8`); there is no `broker.core-invariants`.

aterm-side rungs (the aterm repo; never on astream's manifest — the oracle precedent,
`docs/DESIGN-astream-term.md:441`; their absence from the manifest is the doctrine, their
green out-of-tree tests the proof):

| Rung | Command | Asserts |
|---|---|---|
| **A1** verb table + deps — **BUILT (aterm)**, test-cited (`fabric/a1-a2` `f08b9bcb`, extended by `2c016005`) | `cargo test -p aterm-types control_verbs` | the rows of §11.2 with their classes; `access_exceptions_are_exactly_the_declared_sets` pins `BridgeOnly` = {`deliver`, `hold`, `outbox`, `outbox sent`} (two more than this document first drafted — §11.2 deviation 1), pins the four `Scoped` fabric rows, asserts the three access sets are pairwise disjoint, and leaves the OwnerOnly set unchanged; `framing_of` flips `inbox get` to `Bytes` and `inbox seen`/`outbox sent` to `Status` on the sub-verb, since `spec()` keys on the keyword; `help_catalog_full.txt`/`ctl_help_full.txt` regenerated (`SHORT_CATALOG_MAX_BYTES` 8192 → 9216); summaries ≤ the cap. the `cargo tree -p aterm-link` dependency pin landed with A3 and holds: the crate's third-party set is exactly `sha2`, `chacha20poly1305` and `getrandom` |
| **A2** rings + gate + scope — **BUILT (aterm)**, test-cited (`fabric/a1-a2` `466b2da4`, `2c016005`) | `cargo test -p aterm-gui inbox_hold` | `deliver` idempotent on `off=`; `inbox`/`inbox seen` watermark; `--peek` moves nothing; 513th unread row → `dropped=1`; **quota**: 600 `note`s from one principal then one `task` from `h-andrew` → the task is readable and the 65th note was `ERR quota`; eviction never removes an `h-*` row ahead of an agent's; `post` from an Edge-scoped connection → `ERR denied`; **`deliver` and `hold` from an Owner-token connection and from an Edge connection → `ERR denied`**, from the inherited `Scope::Bridge` fd → `OK`; `hold on` makes `send`/`key`/`turn`/`close` from Owner and Edge scope answer `ERR halted`, while `post`, `inbox seen`, `meta set attention`, `lease` and `text` still succeed and PTY bytes still flow; closing the bridge fd under a fleet hold leaves `turn` answering `ERR halted reason=fabric-lost` and `status fabric=disconnected`; `await inbox since=` does not latch on an older deferred row, latches on a newer one, ignores `note` by default, exit 124 on timeout; `EVENT inbox/inbox-seen/post/post-landed/hold` pushed on `events` with no body; **the outbound plane**: `outbox` hands the bridge each queued post's body and `outbox sent` retires it, an outbound body containing newlines survives the `Bytes` framing (`an_outbound_body_may_contain_newlines`), a full outbox REFUSES the `post` rather than dropping one (`a_full_outbox_refuses_the_post_instead_of_dropping_one`), and `outbox` drains every session with `<max>` bounding the batch. The ring bound is bound to the ty-proven `ring_model()` rather than to a hard-coded 512 |
| **A3** bridge e2e, one node — **BUILT (aterm)**, test-cited | `cargo test --manifest-path aterm-link/Cargo.toml --test bridge_e2e` | headless `aterm-gui` launching the bridge over the socketpair + in-process guarded broker; `post to=@s-B kind=ask --wait` in A answers `OK <id> off=<R>` and lands in B's `inbox` with `from=<A sid>@<node> trust=agent off=<R>`; B's `answer re=R` is drained by A with `re-id=<id>`; SIGKILL the bridge between `deliver` and `Commit` → after restart B's inbox has one row; **SIGKILL `aterm-gui` after `deliver`, before `seen` → after relaunch `inbox` shows the row once**; a `task` from an unlisted principal arrives `demoted=task`; an 8-segment subject and a `<sid>` the node does not host are never shown in any inbox and appear as `ev undeliverable`; a record on the node's own lane under the node's id at an offset the bridge never acked is `undeliverable reason=forged-self`; `/f/F/fleet/h-x/halt state=on` → B's `turn` answers `ERR halted` and `Last{…/node/ack}` with `re=<halt-offset>` counts the node as `held` (the one-subject-per-node shape, §5.3); with the broker unreachable the hold stays and posts queue, then land on reconnect; an `answer`/`task` from any principal with any `re=`/`gen=` produces **zero PTY bytes**; a `term/in` with a stale `epoch=` is refused and recorded; SIGKILL the bridge → `Last{…/node/presence}` reads `gone`, restart reads `live inc+1`; the producer sequence resumes with no dup after a wiped state dir. **Two assertions were split rather than weakened.** aterm mints a fresh sid at every launch and has no flag to ask for one, so §6.2's "a `session-created` with a KNOWN sid" cannot arise across a real relaunch: `the_persisted_watermark_refills_a_ring_without_duplicating_a_row` proves the mechanism (persisted watermark, `Fetch` from `seen_off + 1`, idempotency) across a BRIDGE restart, and `killing_aterm_gui_loses_no_row_and_duplicates_none` proves the aterm-gui restart loses nothing and duplicates nothing. **Two crash windows are timed from INSIDE the bridge** (`$ATERM_LINK_FAULT` makes it SIGKILL itself after `deliver` before `Commit`, and after `Publish` before `outbox sent`, one-shot across restarts via a marker in the state dir): the windows are microseconds wide and racing them from outside would be the flake this codebase refuses — the signal and the crash are real, only the timing is chosen, by the process whose progress defines the window. The harness PANICS with the build command when `aterm-gui`/`aterm-ctl` are absent rather than skipping |
| **A4** hooks (vendor pin) — **BUILT (aterm)**, test-cited, except the vendor case | `cargo test --manifest-path aterm-link/Cargo.toml --test hooks` | `hook run user-prompt-submit` prints `hookSpecificOutput.additionalContext` carrying the header and per-row metadata and **no byte of any body** (a 4 KiB `note` from an unlisted principal included); `hook run pre-tool-use` exits 2 with the reason under `hold=1` and 0 otherwise; `hook run stop` exits 0 on an empty inbox, 0 when the input JSON has `stop_hook_active: true`, 0 on the second invocation with one deferred row, **exits 2** with the metadata digest on stderr when a newer row from an accepted principal arrives before the timeout, and at most `budget` times for 100 rows in a minute; a real `claude` under a fixture settings file continues instead of stopping and — with `--rewake` — is re-woken after stopping (a non-hermetic, key-gated `#[ignore]` case — **written and never executed**: it needs a real `claude` binary, an API key and the network, so the vendor's half of §9.1 is pinned by a test that has not run, and the `asyncRewake`-on-`Stop` question is still open. The JSON shapes `hook install claude` writes come from §9.1's quotations of the reference, not from a fetch in that session). The budget the `at most budget times` assertion exercises is the HOOK's own ledger, not `serve --wake-budget` (§5.6) |
| **A5** two nodes, sealed — **BUILT (aterm)**, test-cited | `… --test two_nodes_sealed` | A3 across two bridges on loopback `--tcp --key-file`; `aterm-link ls` lists both nodes' sessions; a contested sid makes `post --wait` answer `ERR ambiguous` and never deliver; a human's `control claim` followed by a `term/in/h-andrew` record with the live `epoch=` and `gen=` is applied once, refused when the generation moved, and refused when replayed onto a RELAUNCHED session. Three narrowings the row has to carry. **Loopback, not two machines**: the sealed transport is a property of the connection, so the handshake claim is unweakened, but nothing here is a network that reorders, drops or delays. **The conflict is staged with a third node id**, not a third running bridge — sids are minted by the instance that hosts them, so no second aterm can honestly host B's sid; the rogue's cap and record are real and only the publisher is a test. And **"a new epoch" is the successor session**, because aterm mints a fresh sid at every launch, so "the same sid with a new nonce" cannot be constructed |
| **A6** PTY exactly-once — **BUILT (aterm)**, test-cited | `cargo test -p aterm-gui feed_idempotent` | `feed-bin id=k` twice types once (`dup=1`); `turn id=k` twice submits once; a key from a dead incarnation is `ERR epoch`; an attempt that failed after the write could have happened settles the mark UNKNOWN and its retry is `ERR in-doubt seq=<n>`. The bridge's half of that window is A7's, not this rung's: A6 built the SEAM (the endpoint), and the `feed-bin` test plays the bridge's part explicitly — write, discard the reply as a crashed bridge would, replay the same key. The endpoint's own `ERR in-doubt seq=<n>` is reached inside aterm-gui and **not end to end from the bridge by any test** |
| **A7** composition — **BUILT (aterm)**, test-cited | `… --test fleet_comms_e2e` (`fleet.comms.e2e-exactly-once-across-nodes`) | an agent on node 1 asks, a human answers from a third client as `h-…`, takes control and drives a worker on node 2 through one `term/in` applied once, and the exchange replays from a consistent cut with both screens re-folded. **The two claim ids this row used to name are astream's and are NOT re-proved here** (§10): `term.fleet.consistent-cut-replay` and `term.fleet.durable-watermark` are green over astream-host ENVELOPE logs, and the fabric's sessions are PTYs — `replay.rs` reimplements the cut machinery over BUS records, and what is re-folded is the opt-in `screen` snapshot face as a last-value fold, not a byte-exact `term/out` stream. The replay reads with a separate `Auditor` holding `ro:/f/<F>/>`, because §8.2's human ring deliberately cannot. the retry budget is `FEED_BUDGET = 45 s` of WALL CLOCK, measured from a durable `FeedIntent::first_at` so a bridge restart cannot buy a fresh one; `FEED_TRIES_MAX = 512` survives only as the backstop for the case a clock cannot bound (a bridge that dies inside the feed and relaunches into it). It was `FEED_TRIES_MAX = 8` counted in scheduler rounds, and this row said "~2 s ... more than ~16 s" — but round 2 moved that period to 250 ms without moving the count, so the promised 16 s had silently become 1.75 s. A count of someone else's ticks is not a duration; that is why it is one now. What exhaustion PUBLISHES is no longer a single verdict either: a budget spent entirely on clean pre-write refusals is `refused` (a definite non-delivery), and `in-doubt reason=unresolved` is reserved for a key that was ever genuinely in doubt — recorded by a sticky durable bit that defaults to TRUE for a journal line written before it existed. `ERR busy idem=<seq>` counts as doubt, not refusal: it is the endpoint saying an attempt under this very key is inside the seam with bytes possibly already on the PTY. Safe in the duplicate direction, because every retry rides the same key |
| **A8** glance + tui — **BUILT (aterm)**, test-cited, minus the reader | `… --test glance_and_tui` | `glance.json` rows equal `Last` presence with `attention=` and `fabric=` guaranteed present; `aterm-link tui` in a headless PTY renders published records with trust labels first and `aterm-ctl @<sid> search halt` finds the halt. Three corrections. **`@fabric` is not a selector aterm has** — `Selector::parse` is total over `@.`, `@<local u64>` and `@<sid>`, and a session cannot be NAMED `fabric` either (`is_valid_session_id` requires `s-` plus 20 hex), so the test drives the session the tui runs in. **The writer is `aterm-link glance`, a subcommand, not `serve --glance`**, and nothing on the aterm side READS the file: `status_item.rs` has no `FabricGlance` (§9.3) — that half stays **DESIGNED**. And the tui is proved against ONE node: the face table and the roster fold are unit-tested across all eight faces and for one, two and observer advertisers, but no test drives `/tell` across two |
| **A9** file mirror (sandboxed agents) — **BUILT (aterm)**, test-cited | `… --test mirror` | with `aterm-link mirror <root>` (a subcommand, not `serve --mirror`; `--mirror <root>` is accepted as the design's spelling of the root), a process confined to `<root>` (the Codex seatbelt shape, `AGENT-EXPERIENCE…md:305-320`) reads its rows from `<root>/.aterm/<sid>/inbox.ndjson` (`off=`-idempotent) and a line appended to `outbox.ndjson` lands on a peer's inbox as an ordinary `post`; a relayed inner line arrives `via=<inner> kind=note demoted=task trust=relayed`, proved END TO END against a control that keeps its kind, so the assertion cannot pass vacuously. The plane also carries `sent.ndjson` and `.cursor` (§6.7). **The mirror POLLS** (no inotify, no dependency that would bring one), so a message costs up to one `--interval`, 250 ms by default, in each direction |
| **A10** notify — **BUILT (aterm)**, test-cited | `… --test notify` | `notify --on attention --exec` runs the command once per matching offset across a bridge restart and never more than the rate limit. **"Exactly once" is not what was built and not what the rung chose**: the journal is written BEFORE the exec and an in-doubt entry re-fires, so the failure mode is a command that runs TWICE (marked `ATERM_NOTIFY_DUP=1`), never one that silently never runs — a notifier whose failure is silence fails at its purpose. Dedup is by OFFSET only. Not covered by any test: the `--exec-timeout` kill path, `--since <offset>` end to end, and follow mode's reconnect loop |

Ladder order: R1→R2→R3→R4 give a guarded single-machine bus with retained state,
bounded reads and a proof-of-possession attach; R5→R6→R7 finish presence and messaging;
R8→R9 are the shell faces; R12 measures; A1→A3 are the first cross-aterm message; A4 the
zero-residency wake; A5 crosses hosts; A6→A7 close the PTY seam and the composition; A9
gives Codex a path; A10 gives the human one. **All twenty-two rungs are now built** — R1–R12
manifest-cited on `fabric/integration`, A1–A10 test-cited on aterm's `fabric/a1-a2`, each
with the command in its own row. What that does NOT mean is that §11.2's `serve` spec is
finished: the rungs' acceptance lists were narrower than the spec, and the flags, verbs and
faces no rung asserted are named as unbuilt in §11.2 and §15 rather than carried along by the
word BUILT.

---

## 13. Beyond-SOTA claims — a design comparison, with R12's two measured axes

R12 is green, so the Pareto rule ("never worse than tmux/NATS/Kafka/Slack on a measured
axis") now has **two** measured axes and only two: `broker.bench.last-floor` gates the
retained-state query (10 000 subjects, 200 000 records, 4 096-row pages) and
`broker.bench.fanout-floor` gates live fan-out (64 subscribers on one filter). Every row
in the table below is still a *design* comparison — a mechanism argument with an honest
boundary, not a number — as are the two acknowledged losses at the bottom. Competitor
statements are attributed where I checked a document on 2026-08-28 and marked
*(unverified)* where I did not.

**What the two floors gate, and what they cannot.** An absolute floor set far below
observed catches a catastrophic or structural collapse and nothing finer — the audit's
standing complaint about bench claims. So each command also carries a **same-run ratio**
that exits 2, failing the claim outright rather than only missing a metric: a 64-row
`Last` page must cost at least 8x less than a 4 096-row page over the same index
(observed ~60x; a per-query walk of the history, or of the whole subject index, would
flatten it toward 1); durable ingest under a concurrent query loop must hold at least a
quarter of its un-queried rate (observed ~0.97; a query that parked the writer would
not); and durable ingest with four live subscribers must hold at least half of its
no-subscriber rate (observed ~0.88; a fan-out paid for on the commit path would land
near a quarter). A ratio taken inside one run needs no hardware assumption; the absolute
floors do, and their claim texts say so.

**The disclosure R12 forces on §5.1.** "The broker absorbs the observers" is true in the
sense the gated ratio proves — delivery is off the commit path — and **not** in the
sense that observers are free. On the disclosed dev box (Apple M5 Max, 18 cores, macOS
26.6.2) the producer's durable rate falls from ~46 000 to ~6 200 ops/s once 64
subscribers tail the subject: a ratio of ~0.14, which the bench reports and deliberately
does **not** gate, because broker, writer and all 64 subscribers are threads of one
process there. Separating the broker's own cost from its co-hosted subscribers' would
need the subscribers in their own processes, or a box with more cores than observers;
neither is done here, so nothing is claimed about it.

| Claim | SOTA system | How | Honest boundary |
|---|---|---|---|
| **Provenance is the address, and the producer key is bound to it.** `from=` needs no signature, no PKI, no header map | NATS JetStream: `Nats-Msg-Id` is client-chosen and deduped per stream for "two minutes after a message is stored" (docs.nats.io, JetStream streams, v2.14 docs) — so a co-permitted publisher can poison a peer's dedup; MQTT 5 (OASIS v5.0, 2019): no sender authentication in a message; Kafka: the idempotent producer id is **broker-assigned** (KIP-98), so Kafka lacks this hole — what it cannot express is "sender = subject segment" | the cap-forced `<src>` segment + the broker-derived, cap-bound `producer_id`, enforced on the accept path (R4) | the fleet root and a node can forge beneath themselves; HMAC means the secret holder forges anything |
| **Correlation id = log offset** | NATS `_INBOX` (ephemeral); MQTT 5 Correlation Data (§3.3.2.3.6) / AMQP 0-9-1 `correlation_id` (opaque, client-chosen, unverifiable) | `re=<offset>`, dense and broker-assigned; the exchange can be re-read with the ask swapped (R6) | replay with recorded divergence only — the recorded answer does not change |
| **Presence you can replay, with an exactly-once goodbye fenced at the broker** | MQTT retained + Will (v5.0 §3.3.1.3, §3.1.2.5: unlogged, not replayable); SWIM / phi-accrual / Erlang monitors (no history) *(unverified)* | `Last` + a persisted `Will`, deduped against the goodbye and suppressed by any later record of the same producer (R1, R5) | session liveness behind a live bridge comes from aterm's events; half-open TCP lags; a broker restart is a presence epoch (§7) |
| **Acked broadcast as a query over the same log** | MPI barrier (volatile, static membership); JetStream filtered consumers *can* count acks per subject *(unverified)* — what they cannot do is make the ack the same replayable, producer-deduped record as the broadcast | `Last` over `ack/<offset>` with producer-dedup acks; `ready`/`refused` are the session's, not the bridge's (R7) | absent members are reported by their bridge, never inferred |
| **Human-always-wins at three enforcement points that agree** | LangGraph `interrupt`, MCP elicitation, A2A `input-required` (in-process states) *(unverified)*; GNU screen `writelock` (advisory) | only a `/f/<F>/fleet/<h>/>`-rw cap halts (bus); `hold` refuses every socket driver and `deliver`/`hold` need `Scope::Bridge` (endpoint); `PreToolUse` exit 2 stops a hooked agent's tools (A2, A3, A4) | hookless agents are **drive-held only**; a same-uid shell can be the node on the bus; physical-keyboard provenance is inferred; `lease … holder=fabric:*` is a naming convention, not a gate (§6.6) |
| **Exactly-once into a turn-based agent's turn, across a bridge or endpoint crash, and exactly-once "handled" with an atomic cursor** | Claude Code agent-teams mailbox (single process, no offsets); A2A push notifications (at-most-once webhooks); JetStream/Redis/Pulsar/AMQP (at-least-once acks, not atomic with the record) *(unverified)* | ingest dedup + durable cursor + `deliver` idempotent on offset + persisted `seen` watermark; direct consumers ack with one PnP, `dup=1` visible (R6, A3) | the PTY hop is now decisive — a crash inside the window is resolved on restart by re-asking with the same key (A6, A7) — but an unresolvable one is REPORTED `in-doubt`, not repaired; the agent's own side effects are not covered |
| **Zero-residency wake through the agent's own hooks, metadata in context at turn start** | every bus (wakes a thread, not a turn); LangGraph interrupt (in-process) | `Stop` exits 2 with a metadata digest, monotone and budgeted; `UserPromptSubmit`/`SessionStart` add the metadata as context; the command speaks only to aterm (A4) | the hook contract is the vendor's, pinned by a test; `asyncRewake` on `Stop` unverified; Codex has no hook path |
| **One log for messages, presence, control, keystrokes and screens, hence one audit** | Matrix (history without screens); Kafka (replays data, never the consumer's view); LangGraph checkpoints (state, not an ordered input log) *(unverified)* | one offset spine; `applied re=` on the bus, `caused_by` at the host seam; consistent-cut replay of both screens (A7) | message→screen is watermark-grade at the aterm seam, exact only at the astream-host seam |
| **Protocol economy as a gate** | — (a discipline claim) | retained values, bounded reads, last will, proof-of-possession attach, exactly-once inbox, request/reply, barrier and presence on twelve request tags and five response tags, zero third-party deps in the default broker, `forbid(unsafe)`, pinned by R11 | not a "beats" claim |
| **Acknowledged loss: message size** | Slack (~40 000 characters per message), NATS and Kafka (1 MiB default payload) *(unverified defaults)* | `post` carries 4 KiB on the line and 256 KiB by `len=`; the broker frame allows 16 MiB (`frame.rs:34`), of which a stored record may carry `MAX_RECORD_PAYLOAD` = 16 MiB − 16 (`brecord.rs:20`, the bytes a `Replicate` envelope adds) | a diff or test log over 256 KiB goes by reference (a path, an offset), not by value — a deliberate cap on a RAM-resident log |
| **Acknowledged loss: push to a human** | Slack notifications | `aterm-link notify --on … --exec <cmd>` is green (A10); the human also pulls (`ls --attention`, and `glance.json` for a reader that does not exist yet) | the push exists but nothing on the aterm side reads `glance.json`, and `notify`'s chosen failure is a duplicate push rather than a missed one |

---

## 14. Risks, non-goals, open questions

**Risks.**

- **Retention.** The log is RAM-resident (`store.rs:170,173`) and append-forever unless
  compacted, and the
  fabric now writes `ev`, presence (one row per session ever spawned) and messages to
  it, and the `last` index grows with distinct subjects (§5.2). Mitigations: presence
  republishes only on revision change (no heartbeats, no beacons); the per-producer
  subject bound; `--exited-keep`; `ev` is the digest, not screens; `term/out` and
  `screen` are opt-in. Compaction below an offset floor is **BUILT** in astream (opt-in
  `retention`, `Broker::retain_before`, `broker.log-retention` — a cold, explicit call);
  a policy that drives it (TTL, size) stays **DESIGNED**
  (`REQUIREMENTS-fabric-operations-2026-09-14.md` R4), and this is the largest
  operational risk.
- **Control lanes.** `CONTROL_WORKERS = 8` per instance (`crates/aterm-gui/src/control.rs:2195`). The bridge
  costs none (inherited fds); a script that parks `await inbox` costs one, and seven such
  scripts leave the human one lane. The brief's rule — park at most one — stands. A2's
  bridge costs none of them (its push half is served on the bridge's own inherited-fd
  thread, deliberately, §11.2 deviation 11). **The hook path costs one lane per parked
  `Stop`, not none**, because the wake socket that would have cost none is not built (§9.1):
  with the design's `--timeout 15` and several hooked agents on one instance, several of
  `CONTROL_WORKERS` are held at once, and nothing checks the count.
- **The node is an Owner, and its cap is a file.** A bridge can attribute a post to any
  session it hosts and can read every lane addressed to them; a same-uid shell can read
  the node cap and be the node on the bus. This is aterm's same-uid boundary, not a new
  one, but "trust `from=s-…@n-…`" is "trust that instance's uid". The co-holder checks
  (§6.2) make it visible.
- **Broker restart is a presence epoch.** Every node reads `gone` for one round trip
  after a restart; senders in that window record `undeliverable state=offline`, which
  delivery on reconnect supersedes.
- **Reconnect herd against the connection cap.** A broker restart makes every bridge
  reconnect at once, two connections apiece, against `MAX_CONNS = 1024`
  (`broker.rs:270,1457-1475`); a refused accept (`Error 6`) delays the `live inc+1` that
  suppresses a fenced will, so a bridge back-offs with jitter and opens its publisher
  connection first (§7). Roughly 512 bridges per broker is the structural ceiling.
- **Vendor hook drift.** If the hook shapes move, the wake degrades to `await inbox` or
  the resident waker with no design change; A4 is the tripwire.
- **`Attach` changes shape.** An out-of-tree client that attaches without `Hello` or does
  not read the `Mark` desyncs; **two** callers attach — `Client::attach` (which now does
  the whole `Hello`→`Nonce`→`Attach`→`Mark` round trip) and the `asb` CLI, whose argv
  capability flags were replaced by the repeatable `--cap-file` in the same commit as R8.
- **The ack key moved, and the dedup map is durable.** Both faces now derive an ack's
  `producer_seq` as `ACK_SEQ_BASE | offset` (§11.1 boundary 3, `broker.ack-key-is-one-wire-contract`).
  An ack a PRE-alignment `astream_broker::ack` caller already put on a log is keyed on the
  BARE offset, so its post-upgrade retry is a NEW key and appends a second answer record.
  No protocol version reaches this — the frames are well formed and the incompatibility
  lives in the stored dedup map — so the remedy is procedural: drain a producer's in-flight
  acks before upgrading it, or accept one duplicated answer per ack that was in doubt
  across the upgrade. The group commit is monotone, so the cursor is unaffected either way.
- **An ack must never be read as an incarnation.** An ack sits at `2^63 | offset`; a
  presence will sits at `(inc<<32)|0xFFFF_FFFF`, below it. Round 2 folded acks into the
  per-producer high water the will fence reads, so one ack silently disabled that
  producer's goodbye for good; round 3 excluded the reserved half from the high water on
  every path and made a will in that half a registration-time refusal (§11.1 boundary 3,
  `broker.will-fires-exactly-once`). What remains is a caller obligation with no
  enforcement in the library: an ORDINARY publish must stay below `2^63`. `asb` refuses a
  `--seq`/`--seq-file` value there; a `Client::publish` caller is on its own.
- **Wall clock.** `t=` and `dl=` are publisher-asserted; skew shows as a wrong relative
  deadline, never as a lost message; a broker-stamped time needs `BREC_VERSION` 3 — an
  on-disk format change every existing log would have to be read through — and is deferred
  for that reason. (It is not deferred to hold the wire still: `PROTO_VERSION` is already
  2, §4.1.)
- **Keyboard provenance** stays inferred; `holder=human?` says so.
- **The inbox ring is bounded** (512 rows, 64 per sender, `dropped=<n>` reported); the bus
  is the durable copy and the persisted `seen` watermark refills a relaunched endpoint.
- **Composition is proved by A7** (`fleet_comms_e2e`, one node pair on loopback), and every astream rung is still green-able alone. What A7 does not prove: a network that reorders, drops or delays; a fleet of more than two nodes; a `/tell` across two nodes from the tui.

**Non-goals (deliberately out).**

- A work-sharing queue with claims and visibility timeouts (`/a/queue`, competing
  consumers): `SubscribeGroup` is one cursor, not N workers (`broker.rs:1873-1894`); an
  inbox has one owner; the embedded operator keeps its per-instance claim queue
  (`docs/OPERATOR-EMBEDDED.md:185-203`).
- Revocation lists, identity-bound (non-bearer) caps, attenuable (macaroon) caps, and an
  asymmetric mint — each a named seed with the one it would close in §8; none on this
  ladder. (Channel-bound attach *is* on the ladder now, R4.)
  Four items this list used to carry have since been BUILT in astream and left it:
  **forward secrecy** (`aead.handshake.forward-secret-key-agreement`, opt-in `handshake`),
  **per-peer static-key identity** (`aead.identity.mutual-signed-dh`, opt-in
  `identity`), **cap expiry** (`cap.expiry-enforced` — expiry only, not revocation), and
  **encrypt-at-rest** (`broker.log-encrypted-at-rest`, opt-in `at-rest`). The first two
  are transport, not capability: a fabric node should use them (§8.6), and BINDING a
  node's bus principal to its identity key is the increment that stays designed.
- Federation across brokers (per-host brokers, relay-stamped causes, cross-broker
  cuts): this design's one-broker-per-fleet decision; astream's own leader election /
  follower catch-up-after-rejoin remain a later track (`docs/DOCTRINE.md:146`; the
  replicated quorum tier itself is BUILT — `broker.replicated-tier`, `Replicate` at proto
  tag `0x08`).
- An MCP server (aterm policy, `AGENTS.md:603-618`; `docs/INTROSPECTION.md:743-745`); a
  central router; priority queues beyond bridge coalescing; any claim about the model's
  behaviour.
- Defeating natural-language prompt injection: authority is made visible and
  unforgeable, bodies stay out of the wake path; text is not made safe.

**Open questions.**

1. Should `inbox seen` publish a sender-visible receipt by default (`--receipts` on the
   bridge), or stay local until asked? Still open, and still local: `serve` has no
   `--receipts` flag, so the only sender-visible receipt is an explicit
   `post to=<sender> kind=ack re=<off>`.
2. `term/screen` cadence and who may hold `ro:…/screen` — the log is a secrets store.
3. Whether `<F>` belongs in the subject at all if one broker per fleet is the only
   supported deployment; it is cheap and it keeps caps readable, so it stays for now.
4. Whether `EVENT turn … by=` should land with A1 (it makes the control mirror exact for
   local drivers) or wait.
5. Whether a bridge should refuse to *start* with a `--cap-file` more permissive than
   the node ring of §8.2 (a fleet-root cap on a node is the god cap on the wrong box).
   It does not today, and A7's own harness still reaches for an unbound `rw /f/f1/>` for
   its polling assertions — fine in a test, and exactly the cap §8.2 warns about.
6. Whether the conservative pause should key on something other than `status revision=`.
   At the 250 ms sampling period it both over-fires (the classifier moves on ordinary
   program lifecycle) and can miss entirely (a command shorter than the period publishes no
   phase anyone can observe). §6.6 states both, measured.

---

## 15. Status ledger

| Capability | Status | Evidence |
|---|---|---|
| Subject/Filter grammar; sound containment ACL | **BUILT** | `wire.address-grammar.validated`, `wire.filter.containment` |
| Exactly-once ingest, replay-subscribe to one subscriber, Condvar tail, restart durability | **BUILT** | `broker.exactly-once-pubsub-resume` |
| Durable consumer-group cursor; atomic `ProcessAndProduce` | **BUILT** | `broker.true-exactly-once-e2e` |
| Counterfactual fork-delivery | **BUILT** | `broker.agent-native-fork-and-cognition` |
| A fork snapshot ends with an explicit `Mark` before the EOF, so "complete" is readable rather than inferred (`recv` still skips it) | **BUILT** | R6 `broker.inbox-drain-ack-exactly-once` (its command runs `broker_core_regressions.rs a_fork_snapshot_ends_with_a_mark_not_a_bare_eof`, and its text asserts the property) |
| Capability mint + enforcement on attach (group-as-subject) | **BUILT (opt-in)** | `cap.unforgeable-mint`, `broker.cap-enforced-on-attach` |
| Sealed cross-host wire (PSK) | **BUILT (opt-in)** | `aead.seal-open.authenticated`, `broker.sealed-tcp-roundtrip` |
| Single-writer control with auditable handoff (engine) | **BUILT** | `term.fleet.control-handoff` |
| Durable `caused_by`; consistent-cut replay | **BUILT** | `term.fleet.durable-watermark`, `term.fleet.consistent-cut-replay` |
| The pump and its wake lines | **BUILT** | `pump.wake-on-boundaries`, `pump.cli.wake-lines` |
| aterm: discovery, Owner/Edge scope, edge tokens, push digest with GAP and roster journal, `meta`/`status`/`who`/`lease`/`turn`, one-hop relay | **BUILT (aterm)** — test-cited; aterm has no claim ledger | the tests and commands named in §2 |
| N-subscriber fan-out | **BUILT** (exactly-once, 16 subscribers; rate floor at 64) | R1 `broker.last-value`, R12 `broker.bench.fanout-floor` |
| `Last{filter, after, max}` + `Mark{next, head, resume}` (retained last-value as a paged query, clamped to `LAST_PAGE_MAX` rows and `LAST_SCAN_MAX` index visits, paged on `resume` — a short page is not the end) | **BUILT** | R1 `broker.last-value` |
| `Mark.resume` is always a subject the caller's own filter matches (the broker pays extra scan rounds rather than name one outside it; past `LAST_RESUME_ROUNDS` it errors instead of blanking the cursor) | **BUILT** | R1 `broker.last-value` (its command runs `broker_core_regressions.rs lasts_resume_cursor_never_names_a_subject_outside_the_filter`, and its text asserts the property at the wire and at the store) |
| `Fetch{from, filter, max}` (bounded, non-terminal read) | **BUILT** | R2 `broker.fetch-bounded` |
| Grant string: read-only mode + broker-derived principal binding (dedup-poisoning closed); binding table | **BUILT** | R3 `cap.grant-mode-and-producer`, R4 `broker.cap-keyring-enforced` |
| `Hello`/`Nonce` proof-of-possession `Attach` + keyring (cap never on the wire; replay refused) | **BUILT** (opt-in `cap`) | R4 `broker.cap-keyring-enforced`; over the sealed wire, R9 |
| `Will` persisted, fenced on the producer's high-water, exactly-once goodbye, re-fired on broker open **by a broker that owns its log** — a replication target fires none | **BUILT** | R5 `broker.will-fires-exactly-once` |
| One producer id per connection for `Will`; the distinct-subject bound applied at REGISTRATION and the firing exempt from it; the registration acked on the LOCAL commit (so on the Replicated tier the goodbye is only as durable as the leader's own log) | **BUILT** | R5 `broker.will-fires-exactly-once` (its command runs `broker_core_regressions.rs` — `a_will_registered_without_a_quorum_is_the_will_the_connection_fires`, `a_will_whose_subject_is_over_the_bound_is_refused_when_it_is_registered` — and its text asserts all three) |
| The durable replica declaration: `<log>.replica` beside the log, set by a STILL-EMPTY log's first replicated record or by `Broker::open_replica`/`declare_replica`, never by a record accepted beside existing ones; `rm <log>.replica` is the only undo, and the marker must travel with the log | **BUILT** | R5 `broker.will-fires-exactly-once` — the non-conversion rule included: its command runs `broker_core_regressions.rs an_echoed_replicate_does_not_convert_an_owned_log_into_a_replica` and its text states the narrow declaration rule |
| Inbox drain helper; PnP ack | **BUILT** | R6 `broker.inbox-drain-ack-exactly-once` |
| Barrier count by `Last` — the astream half | **BUILT** (a count over the log — nothing blocks; an absent member is only absent) | R7 `broker.barrier-count-by-last` |
| A writer for `pub/<owner>/ack/<B>`, so the count has something to count: the bridge's `busy`/`absent` auto-answers, and a route that puts a session's `post kind=ack re=<B>` on that retained face rather than on the addressee's inbox lane | **DESIGNED** | §5.4 |
| Halt acks written by the bridge | **BUILT (aterm)** — in a NARROWER shape than §5.4's: one retained `pub/<node>/node/ack` per node carrying `re=<halt-offset> state=held\|ready`, not `ack/<B>` per (member, barrier), because the per-barrier shape spends a node's `MAX_SUBJECTS_PER_PRODUCER` budget permanently (§5.3) | A3 |
| `asb` fleet verbs (`--cap-file`, explicit-mode mint, `last`/`fetch`/`drain`/`ack`/`pub --seq-file`); sealed CLI flow with two nodes' rings | **BUILT** (opt-in `cap`; R9 also `aead`) | R8 `broker.cli.fleet-verbs`, R9 `broker.cli.fleet-sealed` |
| Pump on any subject; durable pump cursor | **BUILT** | R10 `pump.attach-subject-and-group` |
| Verb-count gate | **BUILT** | R11 `broker.proto.tag-budget` |
| `Last` and fan-out floors (the Pareto axis), each with a same-run ratio gate beside the absolute floor | **BUILT** | R12 `broker.bench.last-floor`, `broker.bench.fanout-floor` |
| aterm `inbox`/`inbox get`/`inbox seen`/`post --wait`/`deliver`/`hold`/`await inbox since=`; `Scope::Bridge` over inherited fds; hold gate with exemptions (scope-blind, at three seams); ring quota and drop-oldest with `dropped=` reported; fail-closed on bridge loss (a DROP guard); `status hold= fabric=`; the five fabric events, bodiless | **BUILT (aterm)** — test-cited, no claim ledger | A1, A2 — `fabric/a1-a2` `f08b9bcb`/`466b2da4`; `cargo test -p aterm-types control_verbs`, `cargo test -p aterm-gui inbox_hold` |
| The OUTBOUND plane the `serve` spec needed and §11.2 had not named: `outbox` (a `Bytes`-framed peek that moves no watermark) + `outbox sent <sid> <id> off=<n\|->`, both `BridgeOnly`; the queue bounded at 128 rows AND 4 MiB and REFUSING at the door | **BUILT (aterm)** — test-cited | A2 — `fabric/a1-a2` `b1b94e63`; `cargo test -p aterm-gui inbox_hold` (§11.2 deviations 1–5) |
| `aterm_uds::spawnfd` — two descriptors inherited at fds 3 and 4, the launch §11.2 specifies (`dup`/`dup2` in `pre_exec`, inside aterm-uds' existing raw-descriptor cordon; astream's `forbid(unsafe_code)` untouched) | **BUILT (aterm)** — test-cited | `fabric/a1-a2` `b1b94e63`, proved through a real fork+exec against `/bin/sh` reading `<&3` and writing `>&4` |
| `aterm-link serve` — the bridge: node id and incarnation, `Will`, presence and `ev`, the inbox group drained into `deliver` with the commit after `OK`, `seen_off` refill, the self-lane / forged-self check, the fleet-halt tail ahead of the inbox group, `hold` mirroring, the `control` ↔ `lease` mirror (renewed at TTL/3), `undeliverable` verdicts, `GAP` as `ev`, sticky holds under a dead broker, the outbound `outbox`/`outbox sent` plane, the `say` face, TOFU pinning, observer mode, and the §6.5 feed journal | **BUILT (aterm)** — test-cited, no claim ledger | A3, A5, A7 — `cargo test --manifest-path aterm-link/Cargo.toml` |
| `serve` flags the spec names and the binary does not have: `--wake-budget`, `--exited-keep`, `--presence-title`, `--receipts`, `--lash`, `--glance`, `--mirror` (the last two exist as their own subcommands, §11.2); and the §8.6 `--handshake`/`--identity` transports, refused by name because §11.2's dependency pin and §8.6 contradict each other | **DESIGNED** (each refused by name or simply absent) | §11.2 |
| Ten of §4.2's presence fields — `role`, `detail`, `phase`, `driving`, `watchers`, `title`, `host`, `pid`, `parent` on a session row — have no writer; `aterm-link ls` prints `-` for them. Role addressing (§6.1) rests on two of them | **DESIGNED** | §7 |
| The `expired` deadline verdict (§6.4): `dl=` is carried end to end and nothing watches it pass; no `expired` record is ever published and `late=1` is never set | **DESIGNED** | §6.4 |
| The bridge's barrier `busy`/`absent` auto-answers (§5.4): `on_fleet_record` handles `halt` only, so a `barrier` or `notice` on the fleet face is read and dropped | **DESIGNED** | §5.4 |
| `aterm-link wake` and the bridge's `<state>/wake.sock` push lane (§9.1 egress 3, and the reason the `Stop` hook parks no control lane) — refused by name | **DESIGNED**; the cost is one lane per parked `Stop` | §9.1, §14 |
| `aterm-link lash` (`term/out`, §3.3's flight recorder) and `aterm-link pin` — both refused by name | **DESIGNED** | §11.2 |
| `inbox get --bytes`: a binary body is lossy through pct-decode in, `String`-typed `ControlReply` out, and truncated at the bridge's `deliver` request line | **DESIGNED** | §9.1, §11.2 register 21 |
| Zero-residency wake through Claude Code hooks: four hooks installed into `.claude/settings.json`; every field REBUILT from a closed vocabulary rather than forwarded (§8.4); `PreToolUse` exit 2 under a hold with the human's reason; monotone `Stop` over `await inbox`, budgeted by the hook's own per-session ledger | **BUILT (aterm)** — test-cited, EXCEPT the vendor case | A4 — `--test hooks`; the real-`claude` case is `#[ignore]`d and **has never been run**, so `asyncRewake`-on-`Stop` is unverified |
| Two nodes over the sealed wire; `aterm-link ls`; sid pinning and the `observer=1` exclusion; `term/in` under `control claim` with `epoch`/`gen`; `expired` holders observed, not timed | **BUILT (aterm)** — test-cited | A5 — `--test two_nodes_sealed`; loopback, and the sid conflict is staged with a rogue cap rather than a third bridge |
| `id=<epoch>:<producer>:<seq>` idempotency key at the PTY seam, with four outcomes and a terminal `ERR in-doubt` | **BUILT (aterm)** — test-cited | A6 — `cargo test -p aterm-gui feed_idempotent` |
| Composition: cross-node exactly-once exchange replayed to a consistent cut, plus the bridge half of §6.5's feed journal and the `screen` snapshot face | **BUILT (aterm)** — test-cited | A7 `fleet.comms.e2e-exactly-once-across-nodes`; the cut machinery is REIMPLEMENTED over bus records, and astream's two `term.fleet.*` claims are not re-proved by it (§10) |
| `aterm-link glance` (the writer and the file format) and `aterm-link tui` (the fabric as a session, 8 of 10 slash verbs) | **BUILT (aterm)** — test-cited | A8 — `--test glance_and_tui` |
| `serve --glance`, and a `FabricGlance` reader beside `FleetGlance` in `status_item.rs` — nothing on the aterm side reads `glance.json`; `/barrier` and `/fork` in the tui, refused by name | **DESIGNED** | A8, §9.3 |
| Per-project file mirror for sandboxed agents (Codex's only path): `<root>/.aterm/<sid>/{inbox,outbox,sent}.ndjson` + `.cursor`, `off=`-idempotent, relay demotion computed at the receiver | **BUILT (aterm)** — test-cited | A9 — `--test mirror`; a subcommand, not `serve --mirror`; it POLLS at `--interval` (250 ms) |
| Push to a human (`aterm-link notify --on … --exec`), journalled BEFORE the exec so its chosen failure is a duplicate push, deduped by offset, rate-limited per notifier | **BUILT (aterm)** — test-cited | A10 — `--test notify` |
| Per-recipient wake budget and coalescing in the BRIDGE (`serve --wake-budget`), and the `control > ask > task > … > note` ordering | **DESIGNED** | §5.6; the built budget is the `Stop` hook's own per-session ledger, charging every exit-2 with no exemption |
| `EVENT turn … by=` (driver identity on the digest) | **DESIGNED** | — |
| Codex wake through its `notify` hook; Codex over the aterm socket | **DESIGNED** (unverified); **RED** (T13) | A9 is the path, and it is built |
| Retention/compaction keeping absolute offsets (`Broker::retain_before`); encrypt-at-rest for the log (`Broker::open_encrypted`) and its anti-rollback watermark (`Broker::open_encrypted_verified`, `<log>.hw`) | **BUILT (opt-in `retention` / `at-rest` / `anti-rollback`)** — astream broker, not a fabric rung | `broker.log-retention`, `broker.log-encrypted-at-rest`, `broker.log-anti-rollback` (§8.1 T12, §14) |
| Cap expiry (`exp=` in the grant prefix, checked per request) | **BUILT** — astream, not a fabric rung | `cap.expiry-enforced` (§8.6) |
| Broker-stamped time (`BREC_VERSION` 3); a retention policy (TTL, size) | **DESIGNED** | §14 |
| Cap revocation/attenuation; a node's bus principal DERIVED from its identity key | **DESIGNED** | §8.6, §14 |
| Forward secrecy on the wire (ephemeral X25519 under the PSK); per-peer static public-key identity (mutual signed-DH), which a fabric node should prefer to the bare PSK | **BUILT (opt-in `handshake` / `identity`)** — astream transport, not a fabric rung | `aead.handshake.forward-secret-key-agreement`, `broker.handshake-tcp-roundtrip`; `aead.identity.mutual-signed-dh`, `broker.identity-tcp-roundtrip` (§8.6) |
| Federation across brokers; leader election | **DESIGNED** (later track; the replicated quorum tier is BUILT — `broker.replicated-tier`) | §3.3 decision; `docs/DOCTRINE.md:146` |
| Physical-keyboard input provenance | **SEED** (aterm Phase 2) | `docs/RFC-operator-2026-08-15.md:297-301` |

**Read again in one breath.** Face-first subjects make every capability a prefix and
every sender — the halting human included — an address; `Last`, `Fetch` and `Will` make
retained state, bounded reads and presence queries over the one log, with the will
fenced where only the broker can see; a mode-and-principal prefix on the capability
string makes read-only grants expressible and closes a real dedup-poisoning hole, and a
nonce handshake keeps the cap off the wire; one bridge per aterm instance, holding an
authority that is a connection rather than a token, turns all of it into four aterm
verbs and four hooks that carry metadata and never a body, so a turn-based agent reads
its mail with one call and a human halts, takes and answers from anywhere with a cap
nobody else can hold — and where a same-uid shell could still be the node, the document
says so. Four request tags, two response tags, one prefix, one crate; every rung a
command.
