# Compiler-enforced verification survey of astream-wire (Trust)

**What this is.** [Trust](https://github.com/alabsystems/trust) is a fork of
`rust-lang/rust` whose SMT-backed verifier runs as a **MIR pass during compilation**. It
**auto-generates** the Level-0 safety obligations of every function it compiles — integer
overflow, array/slice bounds, div/rem-by-zero, shift overflow, allocation bounds,
panic-freedom — from the crate's real MIR, with **no proof harnesses and no annotations**, and
discharges what it can. `scripts/verify-trust.sh` builds the **real `astream-wire` library**
under Trust (`cargo build -p astream-wire --lib`; the crate has no dependencies, so nothing but
astream's code is verified) three times — under the `advisory`, `strict` and `certify`
enforcement policies — and prints the per-function verdict table below. Every row is about a
function in `crates/astream-wire/src/`, never a copy of it.

**What this is not.** It is an **attached, re-runnable artifact, not a `make ci` claim**:
Trust is a separately built toolchain and never a workspace dependency, so its state can never
break the substrate build (the predecessor's failure the gate's `verify-isolation` lint forbids). No
manifest claim asserts anything in this file; `wire.frame.panic-safe` points here and says so.

**Re-run.** `scripts/verify-trust.sh` — exit code **is** the verdict: `0` the crate builds under
both the strict and the certify policy (every obligation proved); `1` verification ran and the
crate does not fully verify (this file's state); `2` the toolchain or its CLI failed (an unknown
flag, a missing toolchain, an ordinary compile error — **not** a verdict about astream's code,
and never printed as one); `3` the installed Trust is not the pinned commit (the survey is only
comparable to this file under the pin; `TRUST_ALLOW_UNPINNED=1` surveys anyway and says so).

## Captured under the pinned toolchain

> **Stale for the CRC and `Filter` functions until the next re-run.** Since this capture,
> `crc32_ieee` computes slicing-by-8 over eight const tables (built by `crc32_tables`, which
> replaced `crc32_table`), and a `Filter` stores only its validated pattern: `Filter::new`
> validates segment by segment without collecting them, and `matches`/`contains` walk both
> strings' segments in lockstep. Those rows and notes below describe the code at `223a935`;
> the other surveyed functions are unchanged. `scripts/verify-trust.sh` needs the pinned Trust
> toolchain, which is not available in CI.

```
Trust toolchain: rustc 1.99.0-dev (4b3506be5 2026-08-20)      (TRUST_PINNED_COMMIT=4b3506be5)
tree:            astream 223a935 (astream-wire/src unchanged from then to c4b8ac8)
$ scripts/verify-trust.sh   ->  exit 1: NOT FULLY VERIFIED (strict=fail 37 errors, certify=fail 58 errors)
```

Crate totals, from the compiler's own `crate_summary` row (advisory policy — every obligation
reported, none fatal): **69 functions analyzed, 38 fully verified; 98 obligations: 61 proved
(35 of them functions with no panic obligation at all), 4 failed, 7 unknown, 26
runtime-checked, 0 timed out, 0 skipped.**

### Per-function survey (`-Z trust-policy=advisory`), as printed by the script

Functions with at least one obligation. `runtime_checked` = Trust could not prove the row
statically and rustc's runtime check stays (no proof credit); `failed` = the verifier reports a
refutation; `unknown` = an obligation it could not model.

| function | obligations | proved | failed | unknown | runtime-checked | not proved: kind -> outcome (file:line) |
|---|---|---|---|---|---|---|
| `astream_wire::frame::Frame::decode` | 16 | 14 | 0 | 0 | 2 | slice -> runtime_checked (frame.rs:145); assert -> runtime_checked (frame.rs:116) |
| `astream_wire::frame::Frame::encode` | 3 | 1 | 1 | 0 | 1 | unbounded_allocation -> failed (frame.rs:100); assert -> runtime_checked (frame.rs:93) |
| `astream_wire::hash::crc32_ieee` | 2 | 2 | 0 | 0 | 0 | - |
| `astream_wire::hash::crc32_table` | 4 | 4 | 0 | 0 | 0 | - |
| `astream_wire::offset::Offset::checked_next` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (offset.rs:12) |
| `astream_wire::partition::assign_partition` | 6 | 3 | 2 | 0 | 1 | unbounded_allocation -> failed (partition.rs:58); overflow:add -> failed (partition.rs:58); assert -> runtime_checked (partition.rs:45) |
| `astream_wire::subject::Filter::contains` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::subject::Filter::matches` | 2 | 1 | 0 | 1 | 0 | unknown -> unknown (subject.rs:192) |
| `astream_wire::subject::Filter::new` | 3 | 0 | 1 | 1 | 1 | unbounded_allocation -> failed (subject.rs:154); unknown -> unknown (subject.rs:153); assert -> runtime_checked (subject.rs:145) |
| `astream_wire::subject::Subject::new` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:60) |
| `<astream_wire::frame::Decoded as core::clone::Clone>::clone` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (frame.rs:76) |
| `<astream_wire::frame::Decoded as core::cmp::PartialEq>::eq` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (frame.rs:76) |
| `<astream_wire::frame::Decoded as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (frame.rs:76) |
| `<astream_wire::frame::Frame as core::clone::Clone>::clone` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (frame.rs:69) |
| `<astream_wire::frame::Frame as core::cmp::PartialEq>::eq` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (frame.rs:69) |
| `<astream_wire::frame::Frame as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (frame.rs:69) |
| `<astream_wire::frame::FrameError as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (frame.rs:37) |
| `<astream_wire::frame::FrameError as core::fmt::Display>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (frame.rs:54) |
| `<astream_wire::offset::Offset as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (offset.rs:4) |
| `<astream_wire::offset::Offset as core::hash::Hash>::hash` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (offset.rs:4) |
| `<astream_wire::partition::PartitionKey<'a> as core::cmp::PartialEq>::eq` | 1 | 0 | 0 | 1 | 0 | native-verification-gap -> unknown |
| `<astream_wire::partition::PartitionKey<'a> as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | native-verification-gap -> unknown |
| `<astream_wire::subject::Filter as core::clone::Clone>::clone` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:137) |
| `<astream_wire::subject::Filter as core::cmp::PartialEq>::eq` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:137) |
| `<astream_wire::subject::Filter as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:137) |
| `<astream_wire::subject::FilterError as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:98) |
| `<astream_wire::subject::FilterError as core::fmt::Display>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:112) |
| `<astream_wire::subject::Seg as core::clone::Clone>::clone` | 1 | 0 | 0 | 1 | 0 | native-verification-gap -> unknown |
| `<astream_wire::subject::Seg as core::cmp::PartialEq>::eq` | 1 | 0 | 0 | 1 | 0 | native-verification-gap -> unknown |
| `<astream_wire::subject::Seg as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | native-verification-gap -> unknown |
| `<astream_wire::subject::Subject as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:55) |
| `<astream_wire::subject::Subject as core::hash::Hash>::hash` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:55) |
| `<astream_wire::subject::SubjectError as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:28) |
| `<astream_wire::subject::SubjectError as core::fmt::Display>::fmt` | 1 | 0 | 0 | 0 | 1 | assert -> runtime_checked (subject.rs:39) |

Functions with no panic obligation at all (trivially panic-free; the compiler counts each as one
proved obligation): **35** — among them `Offset::delta_from` (`checked_sub`), `fnv1a_64`
(wrapping arithmetic), `time_bucket`, `Frame::new`, `segments`, and the derived `Clone` /
`PartialEq` / `Ord` impls of `Offset`, `FrameError`, `SubjectError`, `FilterError`,
`PartitionKey::clone`, `Subject::clone` / `eq`.

### Enforcement policies: does the crate build?

(Abridged: where the script prints the full sorted list of failing function names under
each policy, this transcript substitutes the summary line that follows. Everything else is
verbatim; the raw logs are the ones the script writes under `$TRUST_OUT_DIR`.)

```
== 2. Strict policy (-Z trust-policy=strict, Trust's default): does the crate build? ==
  -> DOES NOT BUILD (cargo exit 101): 37 error(s)
     error: could not compile `astream-wire` (lib) due to 37 previous errors; 21 warnings emitted
     functions failing strict verification: 32. The 37 errors are 25 "Trust strict
     verification failed", 7 "Trust full verification failed ... native typed-TrustIr
     lowering did not complete" and 5 "Trust Level 0 safety verification incomplete".
     31 of the 32 have an unproved row in the table above; the 32nd is `Filter::contains`,
     whose single obligation the advisory run PROVES (interval solver, kernel-certified)
     but whose native full verification cannot lower an "address walk into variant-bearing
     ADT interior" — so it is all-proved in the advisory table and still fails the strict
     build.

== 3. Certify policy (-Z trust-policy=certify): is every obligation statically proved? ==
  -> DOES NOT BUILD (cargo exit 101): 58 error(s)
     error: could not compile `astream-wire` (lib) due to 58 previous errors
     (the same 32 functions: 25 strict + 7 full as above, but 26 "Level 0 safety
     verification incomplete" instead of 5 — certify additionally fails every
     runtime-checked obligation)

== 4. Whole-crate report via targo (Trust's cargo frontend; informational, not the verdict) ==
   targo trust check -p astream-wire (exit 1):
     Level: L2 | Solver timeout: 5000ms | Function budget: 120000ms
     Summary: 42 proved, 4 failed, 0 runtime-checked, 0 assumed, 0 mandated, 0 contract-panic, 36 inconclusive (82 total)
     Coverage: 69/69 eligible function bodies verified (complete)
     Result: FAIL
     proved by kind: arithmetic_overflow_add=5, hardened_panic_boundary=17, index_out_of_bounds=4, remainder_by_zero=2, shift_overflow_shr=2, slice_bounds_check=12
     failed by kind: arithmetic_overflow_add=1, unbounded_allocation=3
     unknown by kind: arithmetic_overflow_add=1, assertion=30, hardened_panic_boundary=2, slice_bounds_check=1, unsupported_mir=2
     Gate: FAIL [strict lane, exit 1]
   (targo applies its default `unix_hardened` profile, which adds boundary VCs and counts
    trivially-panic-free functions differently, hence 82 obligations rather than 98.)

== VERDICT ==
  toolchain: rustc 1.99.0-dev (4b3506be5 2026-08-20)
  NOT FULLY VERIFIED (exit 1): strict=fail (37 error(s)), certify=fail (58 error(s)).
  The crate does NOT build drop-in under Trust's default policy at this commit.
```

## Reading the table: what is proved, what is not, and why

**Proved (statically, from the real MIR, with no annotation):**

- `Frame::decode` — all twelve fixed-offset header reads `buf[0]`..`buf[11]` (frame.rs:121–133;
  12 slice/bounds obligations) are proved in bounds from the `buf.len() < HEADER_SIZE` guard
  alone; the two `u32::from_le_bytes` array constructions likewise. The `len > MAX_PAYLOAD_LEN`
  cap and the `HEADER_SIZE.checked_add(len)` total generate no arithmetic obligation at all: the
  real code is already checked arithmetic.
- `crc32_ieee` — the table lookup `CRC32_TABLE[idx]` (hash.rs:57) is proved in bounds (the one
  bounds obligation on the per-frame hot path: `idx = ((crc ^ b) & 0xFF) as usize`) and the
  `crc >> 8` shift is proved in range. `crc32_table` (the `const fn` that builds the table): all
  four obligations proved. `fnv1a_64`: wrapping arithmetic, no obligation.
- `Frame::encode` — the length add `HEADER_SIZE + self.payload.len()` (frame.rs:100) cannot
  overflow (proved from the `len > MAX_PAYLOAD_LEN` guard).
- `assign_partition` — `h % n` cannot divide by zero (proved twice, once per reaching branch:
  `n = num_partitions.max(1) as u64 >= 1`), and `topic.len() + origin.len()` cannot overflow
  (slice lengths are `<= isize::MAX`).
- `Filter::matches` / `Filter::contains` — the `i += 1` loop counters (subject.rs:210, :243)
  cannot overflow. (Note the policy split: `Filter::contains`'s single obligation is proved
  here under `advisory`, yet the function still fails the `strict` build — its native full
  verification cannot lower the address walk into the `Seg` enum's interior, and strict
  requires complete native evidence. An all-proved advisory row is not a strict pass.)

**Failed (the verifier reports a refutation) — all four are allocation-side:**

- `assign_partition`, partition.rs:58: `(topic.len() + origin.len()) + 24` — the genuine,
  astronomically unlikely `usize` overflow (`2·isize::MAX + 24 > usize::MAX`) that no sound fact
  can discharge. Trust is correctly refusing it; it was the honest boundary under the previous
  toolchain too.
- `Frame::encode` frame.rs:100, `assign_partition` partition.rs:58, `Filter::new` subject.rs:154:
  `Vec::with_capacity(n)` with a non-constant `n` — Trust's allocation-bound rule ("bulk
  allocation may reach or exceed 2^28 elements: bound the size"). For `encode` the count is
  bounded by the guard two lines above (`<= MAX_PAYLOAD_LEN + 12 = 16 MiB + 12`), for
  `Filter::new` by the input's segment count; the verifier does not carry those bounds into the
  allocation obligation. They are recorded as the compiler reports them, not argued away.

**Unknown (an obligation Trust cannot yet model):**

- `Filter::new` (subject.rs:153) and `Filter::matches` (subject.rs:192): `segments(..).collect()`
  — "bulk allocation recognized (collect/from_iter) but element count not derivable".
- `PartitionKey::{eq, fmt}` and `Seg::{clone, eq, fmt}`: the native typed verification
  "did not produce a complete obligation inventory" (enums carrying `&str` / `String`).

**Runtime-checked (26 rows; every one is the same construct):** a call into `core`/`alloc`
whose body is not in the lowered bundle — `Vec::<u8>::push`, `u32::from_le_bytes`,
`Option::map` (in `Offset::checked_next`), `Into::<String>::into`, `<Vec<u8> as PartialEq>::eq`
(the derived `Frame::eq` / `Decoded::eq`), the `Formatter` calls behind every derived `Debug`
and `Display`, `Hasher` calls, and the drop glue of a `Vec` — is an
`[trust-absent-callee-assumption]`: Trust assumes it may panic, proves nothing about it, and
rustc's runtime behaviour stands. This is the modern form of the previous artifact's
"derived `eq` over `Vec` stays inconclusive" boundary, now applied uniformly to every std call.
The named function's own arithmetic and indexing can be fully proved while one such call keeps
the function out of the strict build: `Frame::decode` is 14/16 for exactly this reason;
`Offset::checked_next` is `checked_add(1).map(Offset)` — no arithmetic obligation exists to
prove, and the `map` call is the unproved row.

**Consequence.** Under Trust's default `strict` policy every runtime-checked, failed or unknown
row is a build error, so **astream-wire does not build drop-in under Trust** at this commit
(37 errors), and not under `certify` either (58). The honest statement is: *the pinned Trust
proves 61 of the 98 Level-0 obligations it generates from astream-wire's real MIR — the header
indexing of the decoder, the CRC table lookup and shift, the encoder's length add, the
partitioner's remainder-by-zero and its first length add, and the matcher's loop counters —
refutes 4 (three allocation bounds and the partitioner's `+ 24`), cannot model 7, and leaves 26
calls into the standard library as runtime-checked assumptions.* Not "the crate is verified".

## Honest boundaries (tracked, never faked — proof-aware, not proof-complete)

- **Proof-grade evidence depends on the pinned toolchain.** The verdicts above are only claimed
  for `4b3506be5`; the script refuses (exit 3) to present a survey under another commit as a
  re-run of this file. Trust moves quickly (the previous pin, `181db695c`, was ~5,200 commits
  earlier, and the `-Z trust-verify-full` flag the previous survey relied on no longer exists):
  re-pin and re-capture together, never one without the other
  (`crates/astream-evidence/tests/trust_pin.rs` holds the script and this file to the same pin).
- **Standard-library calls are assumed, not proved** (the 26 runtime-checked rows), and
  `core`/`alloc`/`std` themselves are "hard-skipped by the verifier; all proofs are conditional on
  their correctness" (targo's own dependency-trust-base note).
- **The example driver is not evidence.** `crates/astream-wire/examples/verify_core.rs` exercises
  the real API on the guarded paths under the stock toolchain; it carries no logic of its own and
  nothing in this file is derived from it.
- **A refuted allocation bound is not a proved bug**, and a proved obligation is not a proved
  function: read the per-obligation column, not the per-function count.

## History: the previous survey (superseded, not re-runnable)

Between 2026-06-23 and 2026-06-24 this file reported a survey under Trust `181db695c` that
compiled `crates/astream-wire/examples/verify_core.rs` **standalone with bare `rustc` under
`-Z trust-verify-full`** and listed as PROVED: `Frame::decode` length add `HEADER_SIZE + len`,
`Offset::checked_next` `n + 1`, `Offset::delta_from` `a - b`, `assign_partition` `h % n`,
`buf[11]` after the header guard, byte-slice `==`, and a length add `s.len() + s.len()`. That
example was a **hand-reduced re-encoding of those guards, not the crate**: it had no `use
astream_wire`, redefined `HEADER_SIZE` / `MAX_PAYLOAD_LEN` locally, saturated where the real
`Offset::checked_next` returns `None`, returned `0` where `delta_from` returns `None`, took the
hash as an input where `assign_partition` computes it, and contained no CRC, no `Frame::decode`
and no `Filter::matches`. Deleting a guard from the real crate left it "proved". Its
`-Z trust-verify-full` flag has since been removed from Trust (`-Z trust-policy=...` replaced
it), so the previous `scripts/verify-trust.sh` could not run at all and, because it discarded the
compiler's stderr, printed the unknown-flag error as "REFUTED". Both defects are what this
revision fixes: the survey is now of the real library, the flag error is a loud exit 2, and the
table above is what re-runs today. Several of the old rows have real-crate counterparts in the
table (the header indexing, `h % n`, the encoder's length add); others were never obligations of
the real code (`checked_next` and `delta_from` use checked arithmetic), and the previously
reported `Filter::matches` loop-counter gap is now proved.
