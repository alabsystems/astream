# REQUIREMENTS: fabric operations — what a manager driving a worker over the fabric needs from astream

Status: requirements, written 2026-09-14 by the aterm manager session that turned the fabric on for real on
m100 and drove a Claude Code worker through it for a day. Every item cites the section of
`DESIGN-aterm-fabric.md` it touches, the evidence that made it a requirement, and one falsifiable
acceptance check, in the spirit of `DOCTRINE.md` (nothing claimed without a green check). Items marked
**aterm** are listed for the boundary only: aterm-link (the bridge, the endpoint, `aterm drive`) builds
them against the broker as it is; the other system owns the items marked **astream**.

## 0. Evidence, measured on 2026-09-14 (m100, aterm 0.85.0, one broker under launchd, one node, two sessions)

| what | measured |
|---|---|
| turning the fabric on | six paths, a launchd label, a hand `fabric attach` of the live instance; the first `post` sat until the bridge's first attach (~1 s) |
| `fabric=connected` | asserted by the bridge PROCESS being attached (§11.2); a config pointing at a dead socket still reads `connected` and a `post --wait` burns its full timeout |
| a manager reading one worker turn from the screen | 689 rows (631 scrolled off) to find a 70-row summary |
| the same turn by mail | one `kind=report` row, 2,009 B, one `inbox get` |
| a task by mail | landed in the worker's inbox in < 2 s; nothing woke the worker (no wake path installed) |
| the Claude Code wake hooks | `aterm link hook install claude` printed commands of the form `aterm hook run …`; the installed multiplexed `aterm` has no top-level `hook`, so each hook exited non-zero and Claude Code BLOCKED the worker's prompts and tool calls until the settings were restored |
| `aterm link hook run pre-tool-use` from inside an aterm child | "no aterm control socket; the tool call is not gated" — the hook looks only at `$ATERM_CONTROL_SOCK` and `$XDG_RUNTIME_DIR`, neither set in an aterm child on macOS |
| presence roster (`aterm link ls`) | `role= detail= driving=` read `-` for every session (§7: ten designed fields have no writer) |
| record time | `t=` is the sender's monotonic milliseconds (`t=38510592`), not wall time; a cross-host timeline cannot be ordered from it |
| re-posting after a timeout | duplicates the task (§6.4: no client-facing key on `post`; the broker dedups by `(producer_id, producer_seq)` only) |
| receipts | none: a sender cannot tell that `inbox seen <id> handled` happened (§9.1: a receipt is an explicit `post kind=ack`; `serve --receipts` is refused by name) |
| the local broker | `aterm link broker` is UNGUARDED (no capability check on attach); the 0700 directory is the whole boundary |
| the m7 case | the campaign's evidence lives on a second machine this fabric cannot reach; the sealed transport is BUILT opt-in (§8.6), the fabric-side `serve --handshake|--identity` is refused by name |

## 1. Requirements for astream (the other system)

### R1 — a guarded broker from the CLI  (§8.2, §11.1 deviation 6)
**Why.** `Broker::open_guarded` exists, but only an embedder can open it; `asb serve` and `aterm link broker` have no way to take a
mint secret, so every real single-machine fabric runs unguarded and relies on directory permissions.
**Requirement.** The generic broker CLI accepts `--secret-file <path>` (32 raw bytes, 0600; never on argv) and opens a guarded
broker that refuses an attach whose capability does not verify. A guarded broker logs the refused principal, never the secret.
**Acceptance.** Start the CLI broker guarded; attach with a cap minted under the secret → accepted; attach with a cap minted under
a different secret, and with no cap → `refused` inside the attach, the connection closed, no record published. The same test
against the unguarded mode shows the difference, so the guard is proven present rather than assumed.

**Status (2026-09-24): BUILT, except the log line.** `asb serve --secret-file PATH | --secret-env NAME` opens `Broker::open_guarded`
(asb built with `cap`), ported from `aterm link broker`, which had built it against the broker as it was. Beyond the
requirement, and also from aterm: the secret file (and `serve`'s `--key-file`) must be 0600, a secret under 32 bytes is
refused by `serve` and `mint` alike, and a refusal happens before the log is opened. The acceptance check above is claim
`broker.cli.serve-guarded`. NOT built: the broker does not log the refused principal (a refused attach is reported to
the client only, and `asb serve` prints nothing per connection).

### R2 — the broker listens on more than one transport at once  (§8.6)
**Why.** A second host needs sealed TCP while the first host's sessions keep using the Unix socket. Today a broker binds one endpoint.
**Requirement.** `--listen unix:<path>` and `--listen sealed:<host:port> --key-file <k>` (and `identity:` once R6 lands) are
repeatable on one broker process, sharing one log, one will table and one producer-sequence dedup table. Plaintext `tcp:` stays
trusted-network-only and is refused unless `--allow-plaintext` is given.
**Acceptance.** One broker with a Unix listener and a sealed loopback listener; a record published on the Unix side is fetched on the
sealed side at the same offset; a will registered over sealed fires on the Unix side's `Last`. A peer without the key is refused in the
handshake, not after it.

**Status (2026-09-24): PARTLY BUILT.** `asb serve <tcp-endpoint> … --unix SOCKET` serves a Unix socket beside the TCP
(plain, sealed or handshake) listener from ONE broker process — one log, one guard, one will table, one dedup table —
ported from `aterm link broker --tcp … --unix`. A TCP endpoint that is not loopback is refused without
`--allow-remote`. NOT built: the repeatable `--listen <scheme>:<addr>` grammar (so two TCP listeners, or `identity:`),
and the `--allow-plaintext` gate on plain `tcp:`. Claim `broker.cli.serve-guarded` covers the socket-beside-sealed case.

### R3 — broker-stamped wall time on every record  (§11.1: "broker-stamped time" is DESIGNED)
**Why.** `t=` is the sender's monotonic clock. A manager's ledger (turns, events, mail) and any cross-host timeline need one clock.
**Requirement.** The broker stamps `bt=<unix ms>` at append, exposes it in `Fetch`, `Last` and the `Will`-fired goodbye, and it is
monotone per broker (a clock step backwards never produces a smaller `bt=` than the previous record). The sender's `t=` is kept.
**Acceptance.** Two records appended 1 s apart from two producers whose own clocks differ by an hour carry `bt=` 1 s apart in append
order. A replica opened from the log shows the same `bt=` values (they are in the record, not recomputed).

### R4 — retention and the oldest offset  (§11.1: "retention" is DESIGNED)
**Why.** The endpoint ring evicts unread rows (`dropped=`) and cuts long bodies; the durable log is the place to fetch them from, but
nothing says how long the log keeps a record or where it starts.
**Requirement.** Per-fleet retention by age and by size, configured on the broker, applied at segment boundaries; a `Head`-style query
that also answers `oldest=<off>` for a filter; a `Fetch` at an offset below `oldest` answers `ERR retained-from=<off>` rather than an
empty page. Retention never removes the last-value (`Last`) row of a subject or an unfired will.
**Acceptance.** With retention set to 100 records, publish 250; `oldest` reads 151 (or the segment boundary at or below it, stated);
`Fetch{from: 5}` answers `retained-from=`; `Last` of a presence subject published at offset 3 still answers.

### R5 — a `Stats` request for operators  (§11.2 `aterm fabric`, new)
**Why.** `aterm fabric` (the operator's status command, built 2026-09-14) can only ask `Head`. It cannot say how many producers are
attached, how much of the log is on disk, or whether a will is pending — the facts an operator needs before trusting `connected`.
**Requirement.** A read-only `Stats` request answering: broker start time, listeners, attached producers (principal, transport,
attach time, last publish `bt=`), record and byte counts per face prefix, `oldest`/`head`, pending wills, dedup-table size, log
segments and bytes on disk. Requires a read grant on `/f/<F>/>`; never returns bodies.
**Acceptance.** Two attached producers and one published record → `Stats` lists both principals and `records=1` under the right face;
kill one producer → its will fires and `Stats` shows one producer and the goodbye record.

### R6 — identity-bound principals and revocation  (§8.6 "DESIGNED, not on this ladder"; cap expiry landed in 4a70622)
**Why.** Joining a second host today means copying a cap minted by the first host's secret; the node id is provisioned text. The design
already says a node SHOULD use the `identity` transport and that deriving the principal from the identity key is designed.
**Requirement.** With `identity:`, the broker derives the connection's principal from the presented key (`n-<hash>`), refuses a cap
whose baked principal differs, and reads a revocation list (a file of key fingerprints, reloaded on SIGHUP) so a lost host can be cut off
without rotating the mint secret. Cap expiry (4a70622) and revocation compose: either refuses.
**Acceptance.** A node with key K and a cap for `n-<hash(K)>` attaches; the same cap over key K' is refused; adding K's fingerprint to
the revocation list and reloading refuses K's next attach and closes its current connection within one poll.

### R7 — exactly-once for a client-visible key  (§6.5; no broker change expected)
**Why.** Re-posting after `ERR timeout` duplicates. The design's answer is bridge-side: reserve `producer_seq` durably, reuse it on retry.
**Requirement (astream, a guarantee to document and test, not new code).** The `(producer_id, producer_seq)` dedup window is at least
4,096 sequences per producer, survives a broker restart ("rebuilt on restart"), and a duplicate answers `PublishAck{deduped: true}`
with the ORIGINAL offset. aterm-link builds `post key=<token>` on that guarantee.
**Acceptance.** Publish seq 10, restart the broker, publish seq 10 again → `deduped=true`, same offset; publish seq 10 after 5,000
newer sequences → still deduped (or the window is stated and pinned by the test).

### R8 — the ack record shape, and deadlines  (§4.2 `ack`, §6.4 `dl=`, the `expired` verdict is DESIGNED)
**Why.** Receipts and deadline expiry are both "explicit posts" in the design with no fixed body, so two bridges would disagree.
**Requirement.** Publish in §4.2 the exact bodies: `ack re=<off> verdict=handled|refused|deferred bt=` (from the recipient's bridge on
`inbox seen`, when `serve --receipts` is on) and `expired re=<off> dl=<ms> bt=` (from the ASKER's own bridge when its deadline passes
with no `answer|report|ack` carrying `re=<off>`; the broker holds no timers). The broker treats both as ordinary `in` records.
**Acceptance.** A conformance test in astream decodes both bodies from the documented grammar; aterm-link's tests are pinned to it.

## 2. What aterm builds against the broker as it is (the boundary, so nobody builds it twice)
- **Turning it on is one command** (`aterm fabric on|off|doctor`), with a self-proving round trip and a rendezvous file every client
  reads instead of six arguments. The broker stays an external, supervised service (launchd / systemd --user), never an in-process
  sidecar of a window: the design's "the only way to be the bridge is to be the process aterm spawned" stands for the bridge, and a
  broker must outlive any one instance.
- **`fabric=` tells the truth without heartbeats** (the design forbids a heartbeat storm, §7): the bridge reports its broker LINK state
  to the endpoint over the inherited fds — dial failed, connection lost, last ack round trip — and the endpoint reads `connected` only
  while the link is up, `stalled` (new) while a bridge is attached but its link is down. `post --wait` on a stalled fabric fails fast.
- **Presence with meaning**: the bridge writes the designed `role= detail= phase= context= title=` fields on change (never text).
- **Mail is the manager's channel**: `aterm drive watch --mail` (one wake per worker turn), `aterm drive task` (the body by mail, a
  one-line nudge only for a worker with no wake hook), and a Stop hook that posts the worker's last message as `kind=report` itself.
- **Hooks that cannot block by accident**: the installer emits the command form that runs, self-tests it, merges into existing settings
  with a backup, finds the control socket through aterm's rendezvous directory, and exits 0 on every internal failure.
- **`post key=`, `--receipts`, `inbox get @<off>`, `expired`** on R7/R8 and the existing `Fetch`.
- **A second host** over the sealed transport with `aterm fabric join`, proven on loopback first, then m7.

## 3. Order the other system should take
R1 and R2 first (they gate the guarded single-host fabric and the m7 join); R3 and R5 next (the operator's view and the ledger depend
on them); R4, R6, R7, R8 as they fit. Each with its acceptance check green in `make ci` before it is called built, per `DOCTRINE.md`.
