# Design record: lashing aterms over astream

How multiple **aterm** instances (`~/aterm` — the headless, introspectable,
model-checked terminal engine) are connected ("lashed") across processes and
machines using **astream** as the deterministic transport. This is the concrete,
buildable form of the theory in [`THEORY-deterministic-sessions.md`](THEORY-deterministic-sessions.md)
and the protocol in [`DESIGN-astream-term.md`](DESIGN-astream-term.md). Lashing
carries one session's `in`/`out`; the fleet's *messages between* sessions and
instances are [`DESIGN-aterm-fabric.md`](DESIGN-aterm-fabric.md).

> **Scope.** This doc is the *optional external* aterm integration: aterm is the
> high-fidelity, pixel-exact canonical render `R` and replay oracle, kept **out of
> the astream tree** (its crate tree would break the substrate's zero-dep +
> reproducible-build doctrine). The in-repo terminal substrate — what is BUILT and
> green today, with its own zero-dep reference render — is the home doc,
> [`DESIGN-astream-term.md`](DESIGN-astream-term.md) §6. The `aterm-link` crate now
> exists aterm-side (it vendors astream's wire/cap/broker/aead crates) as the fabric
> bridge; the lash itself is still **DESIGNED** there (its `lash` verb is refused by
> name) and stood in for by hand-run scripts. The security primitives this doc once
> marked RED — an AEAD wire and a sound mint — are **BUILT** in astream, opt-in (§4).

Status discipline (per astream's gate and aterm's honesty ratchet): every claim
is **BUILT** / **DESIGNED** / **SEED**. BUILT today: `astream-wire`, the aterm
engine, the astream broker (UDS + TCP; its claims are in `evidence/manifest.toml`), the
capability mint with opt-in enforcement and expiry (`astream-cap`), the opt-in AEAD wire
(`astream-aead`), and aterm's `aterm-link` fabric bridge (test-cited in aterm). DESIGNED:
the lash (L1) and L3 speculation; the aterm-side `tools/aterm-link` and `tools/aterm-astream-bridge`
scripts are **hand-run, untested** stand-ins for MVP-0 and half of L2 (`DESIGN-drive-pipe.md` §4, §9).

## 1. The core insight: aterm-ctl is already the lash protocol

aterm's control socket already exposes the four-verb shape locally. Verified
present (`crates/aterm-ctl`): read side `text`/`screen`/`cell`/`cursor`/`image`/
`blocks`/`search`/`selection`/`modes`; drive side `key`/`send`/`select`/`copy`/
`resize`. The kernel proves a gap-free spine (`seq == count`,
`aterm-spec/src/derive.rs:986`) — the same invariant as astream's `Offset`.

| astream verb | aterm-ctl today |
|---|---|
| `/a/stream/term/<sid>/in` (drive) | `key`, `send`, `select`, `copy`, `resize` |
| `/a/stream/term/<sid>/out` (observe) | engine change-stream + `text`/`screen`/`cell` |
| `/a/state/term/<sid>/screen` (snapshot) | `read` / `screen` / `image` |
| `/a/inbox/term/<sid>/ctl` | `modes`, `resize`, `tab`, `off` |

**Lashing = routing those verbs between aterm engines over astream's wire,
cursored by `Offset`.** The local socket already does this for one machine;
astream carries it between machines and (optionally) fans it out. We are not
inventing a remote protocol — we are giving an existing local one a transport.

## 2. Where it lives — respect the headless boundary

aterm's canonical rule (`ATERM_DESIGN.md` §2): the engine owns **zero** I/O. A
network link is I/O, so the lash is a **frontend/embedder, not engine code** —
same tier as the PTY fd or the macOS app. This keeps aterm's grep-enforced
no-platform invariant green.

- **New crate `aterm-link`** (a frontend embedder). It (a) embeds or connects to
  an aterm engine, (b) frames aterm-ctl messages as astream `Frame`s, (c)
  addresses them with `Subject`, (d) cursors with `Offset`.
- **Two roles, one binary.** *Host* owns the PTY + authoritative engine. *Viewer*
  runs a local aterm engine as renderer/predictor. Lashing = two engines sharing
  one log; one authoritative, one speculative.

## 3. Layering — point-to-point first, broker only for fleets

Honors aterm's "no daemon, no broker" minimalism: the default lash is direct,
like mosh's datagram. The broker is an *upgrade* for fleet scale.

- **L0 (BUILT):** aterm-ctl verbs + `seq==count` spine; `astream-wire`
  `Frame`/`Subject`/`Offset`; and, since this doc was written, the astream
  **broker** the L2 fleet layer needs (`broker.exactly-once-pubsub-resume`,
  `broker.tcp-transport`, `asb`).
- **L1 — the lash (small, new, no broker):** `aterm-link`, point-to-point. Host
  streams `out` as normalized screen-ops (the formatting fix — the viewer never
  re-parses VT against a wrong terminfo); viewer forwards `in`; reattach/roam =
  "I'm at `Offset K`," host replays the gap via `delta_from`. This unifies
  mosh-roaming + tmux-persistence on real types.
- **L2 — fleet (optional, astream broker):** route the same frames through a
  partitioned durable log for N-subscriber fan-out, replay/audit, and **nested
  aterms** (a tab/pane in aterm A *is* a remote lashed aterm B → the fleet as one
  introspectable surface).
- **L3 — speculative (research):** the viewer's local engine speculatively
  executes and retires against the host's authoritative `out` (verified-prediction
  protocol, `THEORY` §3).

## 4. Security — the model is strong; the two primitives that blocked real use are now BUILT (opt-in)

The *model* (capabilities, deny-and-log never prompt, provenance lattice,
sandbox, per-instance token + same-uid peer check) is more principled than
ssh/mosh. Security is implementation + audit; the two pieces this doc marked RED
have since landed in astream, each behind an off-by-default feature so the default
broker stays zero-third-party:

1. **The wire — AEAD BUILT (opt-in `aead`).** `Frame`'s CRC32 is
   integrity-against-corruption, **not** a MAC, so the *default* plaintext TCP wire
   still lets an active MITM tamper/inject. `astream-aead` +
   `Broker::serve_tcp_sealed` seal the same protocol with XChaCha20-Poly1305 under a
   32-byte pre-shared key (`aead.seal-open.authenticated`,
   `broker.sealed-tcp-roundtrip`; `asb --key-env`/`--key-file`), session-bound: a
   per-connection hello exchange makes every record's AAD name its connection and
   direction, so a captured record cannot be replayed into another connection or
   reflected back. Above it, both BUILT and opt-in: an ephemeral **X25519 key
   agreement** authenticated by that PSK, so each session's key is fresh and a later
   PSK compromise cannot decrypt a recorded one (`handshake` feature); and **mutual
   static public-key identity** with no shared secret at all — the client pins the
   broker's host key, the broker allow-lists the client's (`identity` feature). Both
   bind their DH transcript into the same record layer's AAD. The durable log can be
   sealed at rest too (opt-in `at-rest`, `broker.log-encrypted-at-rest`). Still SEED
   above them: identity bound to an external authority.
2. **The capability mint — BUILT and enforced (opt-in `cap`).** astream's mint is
   HMAC-SHA256 over a `Filter`, tamper/widen/forge-rejected, and verified with a compare
   that folds all 32 tag bytes with no early exit on the first differing byte — a
   structural property asserted in `astream-cap`, not a timing measurement
   (`cap.unforgeable-mint`, `wire.filter.containment`; the fold is guarded by
   `ct_diff_folds_every_byte_whatever_the_mismatch` under `cap.grant-mode-and-producer`),
   and `Broker::open_guarded` refuses any publish/subscribe/commit outside the grant
   (`broker.cap-enforced-on-attach`); a grant can carry an expiry, checked per request
   (`cap.expiry-enforced`), though not yet a revocation. (aterm's own instance token remains what
   `ATERM_DESIGN.md` §0.1 says of it; the lash should carry astream's mint.)

### Attack surface (enumerated, weighted)

Surface scales with capability; several entries are intrinsic to features mosh
refuses to offer (remote drive, durable replay, fan-out) — the feature *is* the
surface. Program: minimize + verify + capability-gate each, do not deny it.

| Entry point | New vs mosh | Blast radius | Mitigation |
|---|---|---|---|
| Network link (frame parser) | category-same | inject/tamper | panic-free bounds-checked decode (BUILT); AEAD wire (BUILT, opt-in PSK) |
| VT/escape parser | not new (every terminal) | escape-injection | aterm engine panic-free-targeted → smaller than typical |
| Control-verb API (`key`/`send`) | **new** | session takeover via keystroke injection | sound cap gate (mint + accept-path enforcement BUILT, opt-in) |
| Durable log (secret store) | **new** | exfil of every keystroke/screen | encrypt-at-rest (BUILT, opt-in `at-rest`) + retention (BUILT, opt-in `retention`) + provenance redaction |
| Broker + sub authz (L2) | **new** | fleet-wide | optional; not in MVP-0/1 |
| Viewer speculative engine | **new** | host corrupts viewer? | safety theorem: committed = `R(authoritative)` regardless of prediction |

## 5. Cost — interactive path ≈ mosh; only durable replay costs more (a dial)

- **Input wire:** negligible (~30–40 B/keystroke incl. future AEAD tag; hundreds
  of B/s for human typing).
- **Output wire:** ≈ mosh **if coalesced** — aterm already has damage tracking
  (`take_damage` epoch, dirty-row runs, `ATERM_DESIGN.md` §2.2); ship damage
  deltas at a frame rate, bounded by screen×framerate, not output volume.
- **CPU:** two emulator engines vs mosh's one + thin predictor; milliseconds/
  frame, GPU-accelerated — small in absolute terms.
- **Memory/disk:** the *only* structurally higher cost, and it is the **durability
  dial** — off by default. At `Relaxed`/no-retention you pay ≈ mosh; you pay
  storage only when you turn replay on. The extra cost is exactly the replay
  feature.

## 6. Build path — cheapest proof first

1. **MVP-0 (no security needed — same machine, same uid):** a local `aterm-link`
   relay mirroring one aterm into another over the existing ctl sockets (host
   PTY → viewer render; viewer keys → host). Proves "lashed aterms" end-to-end on
   only BUILT pieces.
2. **MVP-1:** swap the relay for astream `Frame`s + `Offset` cursoring →
   reattach/resync across a real socket. The tmux+mosh-roaming unification.
3. **MVP-2:** viewer engine as predictor; speculative echo, exact retire; verify
   the protocol with aterm's `ty` (same class as `snapshot_model`).
4. **MVP-3:** broker fan-out + nested aterms = the fleet.

**The seed that gates everything:** record a session `(I, O)`; replay `O` through
aterm headless from `Offset::ZERO`; assert `read_text` *and* `read_image` (pixels)
are bit-identical to the live session at every offset.

## 7. Honest verdict

Good — **for agent fleets and auditable multi-agent sessions**, which is exactly
what astream and aterm are built for. Not a better daily-driver shell for a solo
human (mosh+tmux wins there). It is a good *design* becoming a *system*: the
substrate, the broker, the AEAD wire, the forward-secret key agreement, static
public-key identity, the enforced mint and encrypt-at-rest are BUILT (the crypto ones
opt-in); the `aterm-link` crate exists aterm-side as the fabric bridge, while the lash
in it is DESIGNED and stood in for by hand-run scripts. It ties mosh on latency (prediction is mosh's own trick — no
physics win), is heavier only in proportion to the replay feature, and has a larger
but irreducible-and-gateable attack surface. The two non-negotiables for
untrusted-network use — **AEAD on the wire** and a **sound capability mint** — now
exist, with forward secrecy, static public-key identity and encrypt-at-rest beside
them; what remains for the word "SSH" is identity bound to an external authority and
the key operations around it.
