# Compiler-enforced verification survey of astream-wire (Trust)

**What this is.** [Trust](https://github.com/alabsystems/trust) is a fork of
`rust-lang/rust` whose SMT-backed verifier and Clean CIC kernel run as **MIR passes during compilation**. It:
1. **Auto-generates** the Level-0 safety obligations of every function it compiles — integer
   overflow, array/slice bounds, div/rem-by-zero, shift overflow, allocation bounds,
   panic-freedom — from the crate's real MIR, with **no proof harnesses**, and discharges what it can.
2. **Type-checks embedded Clean CIC / TLA+ islands (`clean { ... }`)**, compiles top-level Clean-origin (`I5`) transition functions directly into Rust `pub const fn`s (`clean_origin_mir.rs`), verifies their lowered Rust MIR against the Clean kernel definition via `is_def_eq` (`trust_clean_origin::check_faithful`), and discharges `#[ensures(...)]` postconditions via `clean-kernel-defeq`.

`scripts/verify-trust.sh` and `scripts/verify-ready.sh` check the **real `astream-wire` library**
with `targo trust check -p astream-wire` (the crate has no dependencies, so nothing but
astream's code is verified) and print the per-function verdict table below,
read from the survey run's `report.json`. Every row is about a function in
`crates/astream-wire/src/`, never a copy of it. targo applies its default `unix_hardened`
profile, which adds `hardened_panic_boundary` obligations beside the plain Level-0 ones.

**What this is not.** While `scripts/verify-ready.sh` gates `astream-wire` (along with all 20 other
workspace library and binary targets across all 15 crates) at **0 failed obligations (`exit 0`)**, `make ci` runs the fast unverified lane
(`targo --unverified`) — under Trust's strictest `--certify` policy, calls into `core`/`alloc`/`std`
whose bodies are outside the crate remain `unknown` (`[trust-absent-callee-assumption]`), and the
three full policy runs in `scripts/verify-trust.sh` take several minutes. Verification tooling is
never a workspace dependency (enforced by the gate's `verify-isolation` lint).

**Re-run.**
- `scripts/verify-ready.sh` — runs `targo trust check --allow-l0-gaps` across all 21 workspace targets
  (`astream-wire`, `astream-effects`, `astream-pump`, `astream-pump-bin`, `astream-kafka`,
  `astream-cap`, `astream-evidence-bin`, `astream-evidence`, `astream-agent`, `astream-aead`,
  `astream-live`, `astream-live-bin`, `astream-digest`, `astream-engine`, `astream-engine-bin`,
  `astream-sys`, `astream-host`, `astream-host-bin`, `astream-term`, `astream-broker-bin`, `astream-broker`) and exits `0` iff every
  target has `0 failed` obligations and meets its proved floor (**11,887 proved, 0 failed, 0 runtime-checked** across all 21 workspace targets, measured on e467a1d with Trust `321aaeda7`, with **0 mandated** across 10 of 15 library crates and 29 hardened OS-boundary `mandated` rows workspace-wide: raw path calls, process and stdio semantics, FFI and discarded OS errors, all in the binaries and the five I/O crates `astream-live`, `astream-engine`, `astream-sys`, `astream-host` and `astream-broker`).
- `scripts/verify-trust.sh` — exit code **is** the 3-policy verdict: `0` the crate verifies
  under both the strict and the certify policy (every obligation proved, 0 unknown); `1` verification ran
  and `unknown` absent-callee rows remain under strict/certify; `2` the toolchain or its CLI failed;
  `3` the installed Trust is not the pinned commit (`TRUST_ALLOW_UNPINNED=1` surveys anyway).
  Keep `TRUST_OUT_DIR` inside the repository: the verified lane refuses a world-writable path such as `/tmp`.

## Captured under the pinned toolchain

```
Trust toolchain: rustc 1.99.0-dev (321aaeda7 2026-09-17) (trustc 0.1.0)   (TRUST_PINNED_COMMIT=321aaeda7)
                 targo 1.99.0-dev (321aaeda7 2026-09-17) (targo 0.1.0)
tree:            astream-wire/src (0 failed Level-0 obligations across all 8 modules: cut.rs, frame.rs, hash.rs, offset.rs, partition.rs, receipt.rs, steps.rs, and subject.rs; 8/8 modules embed Clean TLA+ islands & Clean-Origin I5 functions; gated in scripts/verify-ready.sh)
$ targo trust check --allow-l0-gaps --locked -p astream-wire --lib   ->  exit 0: CONDITIONAL-PASS (440 proved, 0 failed, 70 unknown / 510 total)
```

**Summary of current capture (`321aaeda7`):**
- **193 functions analyzed** (65 fully verified with 0 unknown, **0 with violations (`0 failed`)**, 60 inconclusive due to `core`/`std` absent-callee boundaries; **68 functions carry no panic obligation at all**).
- **510 obligations: 440 proved, 0 failed, 70 unknown, 0 timed out, 0 runtime-checked, 0 mandated.** Every single arithmetic, shift, index, slice-bounds, allocation, panic-boundary, loop-termination, and postcondition obligation in `astream-wire` is **100% statically proved** (`unknown` holds only `core`/`alloc`/`std` absent-callee `assertion` rows; `non_termination=0`).
- **8 embedded Clean CIC / TLA+ islands kernel-checked (`100%` of modules in `astream-wire`, `293 declarations` total)**:
  - `cut.rs` (`39 declarations`): Top-level Clean-origin (`I5`) functions `heal_frontier_monotone`, `meet_frontier_monotone`, and `causal_gate_frontier` compiled directly from Clean to Rust MIR + `#[ensures]` guard `frontier_includes_raw` proved by `clean-kernel-defeq` + TLA+ state machine `Astream.Wire.TlaCausalCut` (`spec_satisfies_chandy_lamport : Spec ⊨ □ (Lift ChandyLamportInv)`).
  - `frame.rs` (`35 declarations`): Top-level Clean-origin (`I5`) function `frame_clamp_payload_len` compiled directly from Clean to Rust MIR + `#[ensures]` guard `payload_within_cap` proved by `clean-kernel-defeq` + TLA+ state machine `Astream.Wire.TlaFrameCodec` (`spec_satisfies_frame_codec_safety : (Spec cap) ⊨ □ (Lift FrameCodecSafetyInv)`).
  - `hash.rs` (`65 declarations`): Top-level Clean-origin (`I5`) functions `crc_table_index_clamp`, `crc32_poly_select`, and `fnv1a_64_mul_prime` compiled directly from Clean to Rust MIR + `#[ensures]` guards `crc_table_index_in_bounds` and `fnv1a_64_state_matches` proved by `clean-kernel-defeq` + functional CRC-32/IEEE slicing-by-8 recurrence, bitwise refinement, split-invariance (`crc32_update_ref_append`), and FNV-1a/64 left-fold (`fnv1a_64_fold_append`) theorems + TLA+ state machine `Astream.Wire.TlaSlicingCrc32` (`spec_satisfies_always_crc_safety : Spec ⊨ □ (Lift SlicingCrcSafetyInv)`).
  - `offset.rs` (`28 declarations`): Top-level Clean-origin (`I5`) function `offset_advance_monotone` compiled directly from Clean to Rust MIR + `#[ensures]` guard `offset_precedes_or_eq` proved by `clean-kernel-defeq` + TLA+ state machine `Astream.Wire.TlaLogOffset` (`spec_satisfies_always_offset_safety : Spec ⊨ □ (Lift LogOffsetSafetyInv)`).
  - `partition.rs` (`27 declarations`): Top-level Clean-origin (`I5`) function `partition_modulus_clamp` compiled directly from Clean to Rust MIR + `#[ensures]` guard `partition_in_bounds` proved by `clean-kernel-defeq` + TLA+ state machine `Astream.Wire.TlaPartitionRouter` (`spec_satisfies_always_router_safety : Spec ⊨ □ (Lift RouterSafetyInv)`).
  - `receipt.rs` (`33 declarations`): Top-level Clean-origin (`I5`) function `monotone_clock_tick` compiled directly from Clean to Rust MIR + `#[ensures]` guard `deadline_elapsed` proved by `clean-kernel-defeq` + TLA+ state machine `Astream.Wire.TlaFabricReceipts` (`spec_satisfies_receipt_safety : (Spec dl t0) ⊨ □ (Lift ReceiptSafetyInv)`).
  - `steps.rs` (`33 declarations`): Top-level Clean-origin (`I5`) function `step_prefix_advance` compiled directly from Clean to Rust MIR + `#[ensures]` guard `step_within_bounds` proved by `clean-kernel-defeq` + TLA+ state machine `Astream.Wire.TlaStepScan` (`spec_satisfies_step_scan_safety : Spec ⊨ □ (Lift StepScanSafetyInv)`).
  - `subject.rs` (`33 declarations`): Top-level Clean-origin (`I5`) function `segment_depth_advance` compiled directly from Clean to Rust MIR + `#[ensures]` guard `filter_depth_contains` proved by `clean-kernel-defeq` + TLA+ state machine `Astream.Wire.TlaSubjectFilter` (`spec_satisfies_always_filter_match_safety : Spec ⊨ □ (Lift FilterMatchSafetyInv)`).

```
note: Clean island kernel-checked: 39 declaration(s) registered (Trust.Temporal.*, heal_frontier_monotone, meet_frontier_monotone, causal_gate_frontier, Astream.Wire.TlaCausalCut.*)
note: Clean island kernel-checked: 35 declaration(s) registered (Astream.Wire.TlaFrameCodec.*, frame_clamp_payload_len)
note: Clean island kernel-checked: 65 declaration(s) registered (Astream.Wire.TlaSlicingCrc32.*, crc_table_index_clamp, crc32_poly_select, fnv1a_64_mul_prime)
note: Clean island kernel-checked: 28 declaration(s) registered (Astream.Wire.TlaLogOffset.*, offset_advance_monotone)
note: Clean island kernel-checked: 27 declaration(s) registered (Astream.Wire.TlaPartitionRouter.*, partition_modulus_clamp)
note: Clean island kernel-checked: 33 declaration(s) registered (Astream.Wire.TlaFabricReceipts.*, monotone_clock_tick)
note: Clean island kernel-checked: 33 declaration(s) registered (Astream.Wire.TlaStepScan.*, step_prefix_advance)
note: Clean island kernel-checked: 33 declaration(s) registered (Astream.Wire.TlaSubjectFilter.*, segment_depth_advance)
Level: L2 | Solver timeout: 5000ms | Function budget: 120000ms | Duration: 351136ms
Summary: 440 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 mandated, 0 contract-panic, 70 inconclusive (510 total)
Coverage: 193/193 eligible function bodies verified (complete)
Result: PASS (conditional: 70 unproved, 0 assumptions, 0 design mandates, 0 runtime-checked, 0 contract-panics; see the Gate line and the Assumptions ledger)
  proved by kind: arithmetic_overflow_add=2, arithmetic_overflow_shl=19, arithmetic_overflow_shr=33, arithmetic_overflow_sub=2, assertion=1, hardened_panic_boundary=91, index_out_of_bounds=49, postcondition=9, remainder_by_zero=1, shift_overflow_shl=19, shift_overflow_shr=33, slice_bounds_check=120, unbounded_allocation=2, unreachable=59
  unknown by kind: assertion=70
  Gate: CONDITIONAL-PASS [advisory lane, exit 0] (440 proved, 0 failed, 0 runtime-checked, 0 assumed, 0 mandated, 0 contract-panic, 70 unknown / 510 total)
```

### Per-function survey (`targo trust check --allow-l0-gaps`), as printed by the script

Functions with at least one obligation. `failed` = the verifier reports a refutation (with a
counterexample — **0 across the entire crate**); `unknown` = an obligation it could not decide or
model (exclusively `[trust-absent-callee-assumption]` on `core`/`alloc`/`std` calls); `runtime-checked` =
unproved but still checked at run time (none in this lane).

| function | obligations | proved | failed | unknown | runtime-checked | not proved: kind -> outcome (file:line) |
|---|---|---|---|---|---|---|
| `astream_wire::cut::CausalCut::<K>::advance_and_heal_edge` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (cut.rs:322) |
| `astream_wire::cut::CausalCut::<K>::advance_effect_if_causal` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (cut.rs:295) |
| `astream_wire::cut::CausalCut::<K>::advance` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (cut.rs:137) |
| `astream_wire::cut::CausalCut::<K>::dominates` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (cut.rs:191) |
| `astream_wire::cut::CausalCut::<K>::first_violation` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (cut.rs:206) |
| `astream_wire::cut::CausalCut::<K>::from_first_wins` | 3 | 1 | 0 | 2 | 0 | assertion -> unknown (cut.rs:122); assertion -> unknown (cut.rs:122) |
| `astream_wire::cut::CausalCut::<K>::heal` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (cut.rs:239) |
| `astream_wire::cut::CausalCut::<K>::includes` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (cut.rs:164) |
| `astream_wire::cut::CausalCut::<K>::is_consistent` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:226) |
| `astream_wire::cut::CausalCut::<K>::iter` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown |
| `astream_wire::cut::CausalCut::<K>::join` | 3 | 1 | 0 | 2 | 0 | assertion -> unknown (cut.rs:265); assertion -> unknown (cut.rs:265) |
| `astream_wire::cut::CausalCut::<K>::meet` | 3 | 1 | 0 | 2 | 0 | assertion -> unknown (cut.rs:280); assertion -> unknown (cut.rs:280) |
| `astream_wire::cut::CausalCut::<K>::offset_of` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:157) |
| `astream_wire::cut::CausalCut::<K>::set` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:131) |
| `astream_wire::cut::causal_step_frontier` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:55) |
| `astream_wire::cut::frontier_includes_raw` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::frame::Frame::decode` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (frame.rs:240) |
| `astream_wire::frame::Frame::encode` | 5 | 3 | 0 | 2 | 0 | assertion -> unknown (frame.rs:118); assertion -> unknown (frame.rs:118) |
| `astream_wire::frame::decode_frame_slice` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::frame::payload_within_cap` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::hash::crc32_entry` | 6 | 6 | 0 | 0 | 0 | - |
| `astream_wire::hash::crc32_ieee_prefix` | 40 | 40 | 0 | 0 | 0 | - |
| `astream_wire::hash::crc32_ieee_update` | 40 | 40 | 0 | 0 | 0 | - |
| `astream_wire::hash::crc32_next_row` | 7 | 7 | 0 | 0 | 0 | - |
| `astream_wire::hash::crc32_row0` | 2 | 2 | 0 | 0 | 0 | - |
| `astream_wire::hash::crc_table_at` | 2 | 2 | 0 | 0 | 0 | - |
| `astream_wire::hash::crc_table_index_in_bounds` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::hash::fnv1a_64_state_matches` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::hash::fnv1a_64_update` | 2 | 2 | 0 | 0 | 0 | - |
| `astream_wire::hash::u32_le` | 9 | 9 | 0 | 0 | 0 | - |
| `astream_wire::offset::Offset::checked_next` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::offset::offset_precedes_or_eq` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::partition::assign_partition` | 3 | 3 | 0 | 0 | 0 | - |
| `astream_wire::partition::partition_in_bounds` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::partition::time_bucket` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::receipt::FabricReceipt::bt_ms` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::receipt::FabricReceipt::decode` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (receipt.rs:270) |
| `astream_wire::receipt::FabricReceipt::encode` | 2 | 2 | 0 | 0 | 0 | - |
| `astream_wire::receipt::FabricReceipt::re` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::receipt::FabricReceipt::tick_clock` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (receipt.rs:226) |
| `astream_wire::receipt::ReceiptVerdict::as_str` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::receipt::deadline_elapsed` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::receipt::parse_u64_ascii` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::steps::decode_step` | 15 | 15 | 0 | 0 | 0 | - |
| `astream_wire::steps::encode_step` | 5 | 3 | 0 | 2 | 0 | assertion -> unknown (steps.rs:122); assertion -> unknown (steps.rs:122) |
| `astream_wire::steps::end_at_corrupt_frame` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (steps.rs:378) |
| `astream_wire::steps::end_without_frame` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (steps.rs:360) |
| `astream_wire::steps::frame_decodes_after` | 3 | 1 | 0 | 2 | 0 | assertion -> unknown (steps.rs:393); assertion -> unknown (steps.rs:393) |
| `astream_wire::steps::scan_steps_from` | 3 | 1 | 0 | 2 | 0 | assertion -> unknown (steps.rs:287); assertion -> unknown (steps.rs:287) |
| `astream_wire::steps::step_within_bounds` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::subject::Filter::contains` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (subject.rs:315) |
| `astream_wire::subject::Filter::matches_segments` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (subject.rs:285) |
| `astream_wire::subject::Filter::matches_str` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (subject.rs:279) |
| `astream_wire::subject::Filter::matches` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (subject.rs:269) |
| `astream_wire::subject::Filter::new` | 3 | 1 | 0 | 2 | 0 | assertion -> unknown (subject.rs:244); assertion -> unknown (subject.rs:244) |
| `astream_wire::subject::Subject::new` | 3 | 1 | 0 | 2 | 0 | assertion -> unknown (subject.rs:112); assertion -> unknown (subject.rs:112) |
| `astream_wire::subject::Subject::segments` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (subject.rs:124) |
| `astream_wire::subject::filter_depth_contains` | 1 | 1 | 0 | 0 | 0 | - |
| `astream_wire::subject::segments::{closure#1}` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (subject.rs:47) |
| `astream_wire::subject::segments` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (subject.rs:42) |
| `astream_wire::subject::validate_filter_segments` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (subject.rs:194) |
| `astream_wire::subject::validate_subject` | 4 | 4 | 0 | 0 | 0 | - |
| `<astream_wire::cut::CausalCut<K> as core::clone::Clone>::clone` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:98) |
| `<astream_wire::cut::CausalCut<K> as core::cmp::PartialEq>::eq` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:98) |
| `<astream_wire::cut::CausalCut<K> as core::default::Default>::default` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:104) |
| `<astream_wire::cut::CausalCut<K> as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:98) |
| `<astream_wire::cut::CausalEdge<K> as core::clone::Clone>::clone` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:72) |
| `<astream_wire::cut::CausalEdge<K> as core::cmp::PartialEq>::eq` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:72) |
| `<astream_wire::cut::CausalEdge<K> as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:72) |
| `<astream_wire::cut::CutViolation<K> as core::clone::Clone>::clone` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:83) |
| `<astream_wire::cut::CutViolation<K> as core::cmp::PartialEq>::eq` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:83) |
| `<astream_wire::cut::CutViolation<K> as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (cut.rs:83) |
| `<astream_wire::frame::Decoded as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (frame.rs:101) |
| `<astream_wire::frame::Frame as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (frame.rs:94) |
| `<astream_wire::frame::FrameError as core::clone::Clone>::clone` | 1 | 1 | 0 | 0 | 0 | - |
| `<astream_wire::frame::FrameError as core::fmt::Debug>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (frame.rs:59) |
| `<astream_wire::frame::FrameError as core::fmt::Display>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (frame.rs:76) |
| `<astream_wire::offset::Offset as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (offset.rs:27) |
| `<astream_wire::offset::Offset as core::hash::Hash>::hash` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (offset.rs:27) |
| `<astream_wire::partition::PartitionKey<'_> as core::cmp::PartialEq>::eq` | 1 | 1 | 0 | 0 | 0 | - |
| `<astream_wire::partition::PartitionKey<'_> as core::fmt::Debug>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (partition.rs:51) |
| `<astream_wire::receipt::FabricReceipt as core::clone::Clone>::clone` | 1 | 1 | 0 | 0 | 0 | - |
| `<astream_wire::receipt::FabricReceipt as core::cmp::PartialEq>::eq` | 1 | 1 | 0 | 0 | 0 | - |
| `<astream_wire::receipt::FabricReceipt as core::fmt::Debug>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (receipt.rs:142) |
| `<astream_wire::receipt::FabricReceipt as core::fmt::Display>::fmt` | 2 | 0 | 0 | 2 | 0 | assertion -> unknown (receipt.rs:372); assertion -> unknown (receipt.rs:372) |
| `<astream_wire::receipt::ReceiptError as core::clone::Clone>::clone` | 1 | 1 | 0 | 0 | 0 | - |
| `<astream_wire::receipt::ReceiptError as core::fmt::Debug>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (receipt.rs:100) |
| `<astream_wire::receipt::ReceiptError as core::fmt::Display>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (receipt.rs:117) |
| `<astream_wire::receipt::ReceiptVerdict as core::fmt::Debug>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (receipt.rs:61) |
| `<astream_wire::receipt::ReceiptVerdict as core::fmt::Display>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (receipt.rs:94) |
| `<astream_wire::receipt::ReceiptVerdict as core::hash::Hash>::hash` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (receipt.rs:61) |
| `<astream_wire::steps::StepEnd as core::clone::Clone>::clone` | 1 | 1 | 0 | 0 | 0 | - |
| `<astream_wire::steps::StepEnd as core::fmt::Debug>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (steps.rs:190) |
| `<astream_wire::steps::StepFault as core::clone::Clone>::clone` | 1 | 1 | 0 | 0 | 0 | - |
| `<astream_wire::steps::StepFault as core::fmt::Debug>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (steps.rs:210) |
| `<astream_wire::steps::StepFault as core::fmt::Display>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (steps.rs:239) |
| `<astream_wire::steps::StepScan as core::clone::Clone>::clone` | 2 | 0 | 0 | 2 | 0 | assertion -> unknown (steps.rs:173); assertion -> unknown (steps.rs:173) |
| `<astream_wire::steps::StepScan as core::cmp::PartialEq>::eq` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (steps.rs:173) |
| `<astream_wire::steps::StepScan as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (steps.rs:173) |
| `<astream_wire::subject::Filter as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (subject.rs:234) |
| `<astream_wire::subject::FilterError as core::clone::Clone>::clone` | 1 | 1 | 0 | 0 | 0 | - |
| `<astream_wire::subject::FilterError as core::fmt::Debug>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (subject.rs:134) |
| `<astream_wire::subject::FilterError as core::fmt::Display>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (subject.rs:148) |
| `<astream_wire::subject::Segments<'_> as core::iter::traits::iterator::Iterator>::next::{closure#1}` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (subject.rs:64) |
| `<astream_wire::subject::Segments<'_> as core::iter::traits::iterator::Iterator>::next` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (subject.rs:59) |
| `<astream_wire::subject::Subject as core::fmt::Debug>::fmt` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (subject.rs:107) |
| `<astream_wire::subject::Subject as core::hash::Hash>::hash` | 1 | 0 | 0 | 1 | 0 | assertion -> unknown (subject.rs:107) |
| `<astream_wire::subject::SubjectError as core::clone::Clone>::clone` | 1 | 1 | 0 | 0 | 0 | - |
| `<astream_wire::subject::SubjectError as core::fmt::Debug>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (subject.rs:80) |
| `<astream_wire::subject::SubjectError as core::fmt::Display>::fmt` | 2 | 1 | 0 | 1 | 0 | assertion -> unknown (subject.rs:91) |

Functions with no panic obligation at all (trivially panic-free): **68** — among them
`heal_frontier_monotone`, `meet_frontier_monotone`, `causal_gate_frontier`,
`frame_clamp_payload_len`, `crc_table_index_clamp`, `crc32_poly_select`, `fnv1a_64_mul_prime`,
`offset_advance_monotone`, `partition_modulus_clamp`, `monotone_clock_tick`, `step_prefix_advance`,
`segment_depth_advance` (all 12 Clean-origin `I5` functions), `crc32_ieee`, `crc32_tables`, `fnv1a_64`,
`fnv1a_64_mix_u64`, `crc32_is_ieee_poly`, `fnv1a_64_is_init`, `fnv1a_64_is_prime`,
`Offset::delta_from` (`checked_sub`), `Frame::new`, `Subject::as_str`, and derived `Clone` /
`PartialEq` / `Eq` / `Ord` impls.

## Reading the table: what is proved, what is not, and why

**Proved (440 obligations statically discharged, 0 failed):**

- **Clean-Origin (`I5`) Protocol Functions & `clean-kernel-defeq` Postconditions (`postcondition=9`)**:
  `heal_frontier_monotone`, `meet_frontier_monotone`, `causal_gate_frontier`, `frame_clamp_payload_len`,
  `crc_table_index_clamp`, `crc32_poly_select`, `fnv1a_64_mul_prime`, `offset_advance_monotone`,
  `partition_modulus_clamp`, `monotone_clock_tick`, `step_prefix_advance`, and `segment_depth_advance`
  are compiled directly from top-level Clean CIC definitions into Rust MIR (`clean_origin_mir.rs`) and
  checked for definitional equality (`is_def_eq`) against the Clean kernel; `frontier_includes_raw`,
  `payload_within_cap`, `crc_table_index_in_bounds`, `fnv1a_64_state_matches`, `offset_precedes_or_eq`,
  `partition_in_bounds`, `deadline_elapsed`, `step_within_bounds`, and `filter_depth_contains` have
  their `ensures` contracts discharged by `clean-kernel-defeq` with **0 unproved obligations**.
- **`decode_frame_slice`, `Frame::decode`, `Frame::encode`, `encode_step`, `decode_step` (`frame.rs`, `steps.rs`)**:
  `decode_frame_slice`, `decode_frame_header`, `decode_frame_header_bytes`, `decode_step`, `decode_step_header`,
  and `decode_step_header_bytes` are **100% `[VERIFIED]` (`0 unknown`)**, and all allocation and arithmetic
  obligations in `Frame::encode` and `encode_step` are 100% statically proved (`0 failed`,
  `0 slice_bounds_check unknown`, `0 non_termination unknown`, `0 mandated`).
- **`crc32_ieee_update`, `crc32_ieee_prefix`, `crc32_entry`, the table builders `crc32_row0` / `crc32_next_row`,
  `crc_table_at`, `u32_le`, and `fnv1a_64_update` (`hash.rs`)**: All 40 arithmetic, shift, and slicing-by-8
  array/slice index obligations in `crc32_ieee_update` (and 40 in `crc32_ieee_prefix`), all 6 in `crc32_entry`,
  all 11 in the table builders and `crc_table_at`, all 9 in `u32_le`, and both slice bounds checks in
  `fnv1a_64_update` are **100% statically proved (`0 failed`, `0 unknown` across the entire `hash.rs` module)**. The
  tables are a `const` and b10ea2f left `crc32_ieee_update` alone, so its **2.59 GiB/s** (**14.04x**
  bitwise), measured before b10ea2f, stands.
- **`assign_partition`, `time_bucket`, `PartitionKey::eq`, `Offset::checked_next` (`partition.rs`, `offset.rs`)**:
  All 3 obligations in `assign_partition` (streaming `fnv1a_64_update` with zero heap allocation and
  non-zero modulo), `time_bucket`, `PartitionKey::eq`, and `Offset::checked_next` are 100% proved
  (`0 failed`, `0 unknown`).
- **`FabricReceipt::encode`, `FabricReceipt::eq`, `parse_u64_ascii`, `bt_ms`, `re`, `ReceiptVerdict::as_str` (`receipt.rs`)**:
  100% of generated obligations proved (`0 failed`, `0 unknown`).

**Failed (0):** Every previously refuted obligation (`39 failed -> 0 failed`) across `hash.rs`,
`partition.rs`, `subject.rs`, and `frame.rs` has been eliminated at the source level and is gated by
`scripts/verify-ready.sh`.

**Unknown (70):** Exclusively `[trust-absent-callee-assumption]` rows (`assertion=70`)
— calls into `core`/`std`/`alloc` (`Formatter` in derived `Debug`/`Display`, `BTreeMap` in `CausalCut`,
`str`/`slice` methods) whose bodies are outside the crate. Zero arithmetic, shift, index, slice-bounds,
allocation, loop-termination, or panic-boundary obligations remain `unknown`.

## Honest boundaries (tracked, never faked — proof-aware, not proof-complete)

- **Proof-grade evidence depends on the pinned toolchain.** The verdicts above are claimed
  for `321aaeda7` (`crates/astream-evidence/tests/suite/trust_pin.rs` holds `scripts/verify-trust.sh` and
  this file to the same pin).
- **Standard-library calls are assumed, not proved** (the absent-callee rows), and
  `core`/`alloc`/`std` themselves remain a foundational trust base.
- **No refuted obligations remain (`0 failed`)**, and `scripts/verify-ready.sh` enforces `0 failed`
  across all 21 workspace library and binary targets across all 15 crates (`11,887 proved, 0 failed, 0 runtime-checked` on e467a1d, with `0 mandated` across 10 of 15 library crates: `astream-wire`, `astream-evidence`, `astream-cap`, `astream-kafka`, `astream-aead`, `astream-pump`, `astream-agent`, `astream-effects`, `astream-digest`, and `astream-term`, including
  `--all-features` on `astream-broker`, `astream-cap`, and `astream-aead`), while all 15 workspace crates
  and all 8 of their binaries embed 72 `clean { ... }` TLA+ / Clean-Origin (`I5`) islands.

## History (superseded captures)

- **2026-10-17, Trust `321aaeda7`, before astream b10ea2f.** 166 functions analyzed, 235 obligations
  (135 proved, 0 failed, 100 unknown): the refutation clean-up had left `crc_table_at` an
  `.unwrap_or(0)` lookup whose one obligation stayed unknown and the table builders in forms that
  carry no bounds obligation, so the proved count fell below the baseline's 139. b10ea2f indexes
  the rows with `u8`.
- **2026-09-17, Trust `321aaeda7` (pre-Wave-4 baseline).** Before eliminating the 39 refutations in
  `hash.rs` (28), `subject.rs` (7), `partition.rs` (3), and `frame.rs` (1) and adding `cut.rs` and
  `receipt.rs`: 72 functions analyzed, 235 obligations (139 proved, 39 failed, 57 unknown).
- **2026-08-20, Trust `4b3506be5`.** Reported 69 functions, 98 obligations: 61 proved, 4 failed,
  7 unknown, 26 runtime-checked.
- **2026-06, Trust `181db695c`.** Standalone guard re-encoding; withdrawn.
