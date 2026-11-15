<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- Copyright 2026 Andrew Yates -->

# astream-digest: the HMAC, HKDF and ct_eq specs

> Status 2026-10-20: these rows came here from aterm's `crates/aterm-digest/SPECS.md` with the
> code they describe. In astream, astream-cap's private const HMAC core and astream-aead's private
> wiping HMAC are now one construction in `src/hmac.rs`, beside a port of aterm-digest's
> streaming API and `ct_eq`, and the tests each row cites moved with them.
>
> Status 2026-10-21: aterm's own copies are gone too. aterm-digest re-exports this crate's
> `HmacSha256`, `hmac_sha256_parts`, `hkdf_extract`, `hkdf_expand_32` and `ct_eq`, with its
> `hmac_sha256.rs` and `ct_eq` deleted (aterm cb93e33cff); aterm-net's fleet keys derive through
> them (aterm a719a8ff7d); and aterm-gui's and aterm-core's token compares call this `ct_eq`
> (aterm 216a880e16). So a row proved here is proved of the code aterm runs. The SHA-256 rows (`sha256-*`, and the `Sha256` half of
> `opaque-debug`) stay in aterm's file for now, where they were written; every row here is built
> on them, and `src/lib.rs`'s Clean island already discharges the streaming buffer's
> obligations.

Each row is a property the cited tests sample, written so a proof through Trust/Clean against
the compiled Rust function can retire those tests. Nothing here is proved yet: a row is a spec,
not a claim. The claims are `evidence/manifest.toml`'s (`digest.hmac-one-construction`).

Gap numbers refer to the table in aterm's historical development audit
`docs/AUDIT-trust-for-test-migration-2026-10-15.md` §7. Gap 0 (a seal that publishes
Clean-discharged rows) blocks every spec, so it is listed on every row. **N1** is a gap that
table does not have: a relational (2-safety / information-flow) lane, needed for the
constant-time spec.

## 0. Notation used in the statements

- `FIPS.SHA256(m)`: a Clean model of FIPS 180-4 SHA-256 over `List UInt8` (aterm's SPECS §0).
  The RFC 4231 and RFC 5869 vectors become kernel-evaluated (`decide`/`rfl`) facts about the
  HMAC and HKDF **models**, validating the models against the standards; they are no longer tests
  of the Rust.
- `HMAC.Kp(key)` = (|key| > 64 ? FIPS.SHA256(key) : key), zero-padded to 64 bytes.
  `HMAC(key, m)` = FIPS.SHA256((Kp ⊕ 0x5c^64) ++ FIPS.SHA256((Kp ⊕ 0x36^64) ++ m)) (RFC 2104).
- `ShaInv(h, M)`: the abstraction of a `Sha256` value `h` that has absorbed the ghost message `M`
  (aterm's SPECS §0: `buf_len < 64`, `buf_len = |M| mod 64`, `len = |M| mod 2^64`, the live tail,
  and `state` = the fold of `FIPS.compress` over M's full blocks).
- `PadsAbs(p, key)` for a `KeyPads` value `p`: `p.k0 = Kp(key)` ∧ `p.ipad = Kp(key) ⊕ 0x36^64` ∧
  `p.opad = Kp(key) ⊕ 0x5c^64`.
- `MacAbs(m)` = (key, M) for an `HmacSha256` value `m`:
  `m.outer_key = Kp(key) ⊕ 0x5c^64` ∧ `ShaInv(m.inner, (Kp(key) ⊕ 0x36^64) ++ M)`.
- `HKDF.Extract(salt, ikm)` = `HMAC(salt, ikm)`; `HKDF.Expand32(prk, info)` =
  `HMAC(prk, info ++ [0x01])` (RFC 5869 §2.2, §2.3 with L = 32).
- `Trace(f, args)`: the sequence of MIR basic-block/branch decisions an execution of `f` takes.
- `black_box`: `core::hint::black_box` is modelled as the identity on its value (and as an
  opaque call for `Trace`).
- **Precondition everywhere:** total absorbed length < 2^61 bytes (a legal FIPS message).

## 1. Specs (TSV)

Columns: `id`, `kind`, `functions`, `statement`, `subsumes (primary tests; secondary in §2)`,
`difficulty (Rust features the proof must handle)`, `blocking_gaps (audit §7)`.

```tsv
id	kind	functions	statement	subsumes	difficulty	blocking_gaps
ct-eq-is-slice-equality	contract	astream_digest::ct_eq	∀ a b : &[u8]: ct_eq(a,b) = (a == b), i.e. true ⇔ |a| = |b| ∧ ∀ i<|a|, a[i] = b[i]. Loop invariant after i pairs: diff = OR_{j<i}(a[j] ⊕ b[j]), and diff = 0 ⇔ a[..i] = b[..i]. black_box = identity. The loop lemma (the OR of the pairwise XORs is zero iff the prefixes are equal) is yet to be written, and must be proved of the compiled body here, not of a hand model: no such lemma exists in either repository (aterm deleted its hand-run ct_eq.lean, bound to no test, in 13fe5533a8).	lib.rs::ct_eq_accepts_identical_slices, ct_eq_rejects_same_length_differences, ct_eq_rejects_length_mismatch	EASY-MEDIUM: two slice params, early return on length, a while loop with a two-sided bound, u8 xor/or accumulator, a black_box call (needs an identity model), bool result.	0,1,3,5,7
ct-eq-data-independent-control-flow	other (2-safety / non-interference)	astream_digest::ct_eq	∀ a b a' b' with |a| = |a'| ∧ |b| = |b'|: Trace(ct_eq,(a,b)) = Trace(ct_eq,(a',b')). The only input-dependent branch is a.len() != b.len(); the fold runs exactly |a| iterations with no data-dependent exit; the result is read from the accumulator only after the loop, through the opaque barrier. A MIR-level property; it says nothing about LLVM's machine code (black_box is the code's own guard for that).	(none: `ct_eq`'s doc states the fold's shape and its `black_box` barrier until gap N1 closes)	HARD: relational (product-program) reasoning over a loop, black_box as an opaque call. No Trust lane exists for information-flow / constant-time properties.	0,1,5,7,N1
hmac-key-pads	contract	hmac::KeyPads::of (via key_block, hmac_ipad, hmac_opad, pad_digest_key)	∀ key : &[u8] (any length < 2^61): PadsAbs(KeyPads::of(key), key), and KeyPads::of never panics: key_block hashes the key iff |key| > 64 (a 64-byte key is used verbatim), every write k[i & 63] is in range and, because i counts the bytes copied and |key| ≤ 64 on that branch, the mask never folds a write; the pad expansions are literal-index array builds.	-	MEDIUM: a branch on key.len() > 64, a while-let slice-pattern loop with a masked index, a call to Sha256::digest_slice (callee ensures), two 64-element array literals of xors	0,1,3,4,7
hmac-refines-rfc2104	refinement	HmacSha256::new_from_slice, update, finalize; hmac_sha256_parts	∀ key, m with |key|, |m| < 2^61 - 128: (let mac = new_from_slice(key).unwrap(); mac.update(m); mac.finalize()) = HMAC(key, m), and hmac_sha256_parts(key, [m]) = HMAC(key, m). new_from_slice never returns Err(InvalidLength): it is Ok(keyed(key)), and MacAbs(keyed(key)) = (key, []) by hmac-key-pads and ShaInv of inner_primed. Corollaries: |key| > 64 ⇒ HMAC(key,m) = HMAC(FIPS.SHA256(key),m); |key| ≤ 64 ⇒ HMAC(key,m) = HMAC(key ++ 0^(64-|key|),m). RFC 4231 cases 1-7, the 64/65-byte block-boundary answers and the key/message length sweeps are instances; the vectors become evaluated facts about the HMAC model.	hmac.rs::rfc4231_test_vectors, known_answers_on_both_sides_of_the_block_size; tests/lengths_and_streaming.rs::hmac_over_every_message_and_key_length_is_pinned	MEDIUM given the Sha256 specs and hmac-key-pads: a struct holding a Sha256 and a [u8;64]; composition across calls (callee ensures); self by value	0,1,2,3,4,5,7
hmac-streaming-equals-one-shot	equivalence	HmacSha256::update, HmacSha256::finalize, hmac_sha256_parts	∀ key, partitions [x1..xn] (n ≥ 0, empty pieces included): feeding the pieces to new_from_slice(key).unwrap() and finalizing gives HMAC(key, x1 ++ … ++ xn), and hmac_sha256_parts(key, [x1..xn]) is that same tag (it is keyed, fed each part, finalized). Proof: MacAbs(m) = (key,M) ⇒ MacAbs(m.update(x)) = (key, M ++ x) (update only forwards to inner; outer_key is unchanged), then hmac-refines-rfc2104.	tests/lengths_and_streaming.rs::hmac_fed_in_arbitrary_chunks_matches_one_shot; hmac.rs::the_parts_doors_mac_the_concatenation_wherever_it_is_cut	EASY given the Sha256 invariant: &mut self delegation to Sha256::update_slice, a while-let loop over a slice of slices, induction over call sequences	0,1,2,4,5,7
hmac-wiping-equals-parts	equivalence	hmac_sha256_wiping, tag_then_wipe, KeyPads::wipe	∀ key, parts: hmac_sha256_wiping(key, parts) = tag_then_wipe(KeyPads::of(key), parts) = hmac_sha256_parts(key, parts) (the same KeyPads::of, inner_primed, updates and outer_tag), and after tag_then_wipe(p, parts) every byte of p.k0, p.ipad and p.opad is 0. The second clause is about the frame's arrays only: copies the compiler makes and the SHA-256 states the pads were fed into are outside it, and no clause here can say a wipe is not elided by codegen.	hmac.rs::the_wiping_door_zeroes_its_key_block_and_both_pads, the_parts_doors_mac_the_concatenation_wherever_it_is_cut, rfc4231_test_vectors (through mac_all_doors); tests/lengths_and_streaming.rs::hmac_fed_in_arbitrary_chunks_matches_one_shot	EASY given hmac-streaming-equals-one-shot: a for loop over a slice of slices, slice fill (needs a model), black_box as identity	0,1,2,4,7
hmac-verify-slice-iff	contract	HmacSha256::verify_slice (via finalize, ct_eq)	∀ m with MacAbs(m) = (key,M), ∀ tag : &[u8]: m.verify_slice(tag) = Ok(()) ⇔ tag == HMAC(key,M) as slices, and Err(MacError) otherwise. So |tag| = 32 is required (a 16-byte prefix or a 33-byte extension is refused), and a tag differing from the true one in any bit is refused. The comparison inherits ct-eq-data-independent-control-flow.	hmac.rs::verify_slice_rejects_a_truncated_or_extended_tag, verify_slice_refuses_every_one_bit_flip_of_the_tag; tests/lengths_and_streaming.rs::hmac_verify_slice_accepts_the_tag_and_refuses_a_flipped_bit	EASY given ct-eq-is-slice-equality and hmac-refines-rfc2104: self by value, calls to finalize and ct_eq (callee ensures), Result<(), MacError> with a unit-struct error	0,1,2,4
hkdf-refines-rfc5869	refinement	hkdf_extract, hkdf_expand_32	∀ salt, ikm, info, prk: hkdf_extract(salt, ikm) = HKDF.Extract(salt, ikm) and hkdf_expand_32(prk, info) = HKDF.Expand32(prk, info); in particular hkdf_extract([], ikm) = hkdf_extract(0^32, ikm) (RFC 5869's default salt), because Kp zero-pads both to the same block. RFC 5869 A.1-A.3 (PRK and the first 32 OKM bytes) and astream-aead's recorded session key are instances.	hmac.rs::hkdf_matches_rfc5869_a1_a2_and_a3, an_empty_salt_is_32_zero_bytes, the_handshake_session_key_is_the_recorded_answer	EASY given hmac-wiping-equals-parts and hmac-refines-rfc2104: one call each, a two-part list with a one-byte literal slice	0,1,4
opaque-debug-hmac	contract	<HmacSha256 as Debug>::fmt	∀ m : HmacSha256: format!("{m:?}") = "HmacSha256 { .. }", a constant independent of every field, so no key-derived byte reaches the output. The general form of "does not contain \"secret\"".	hmac.rs::debug_does_not_leak_the_key	EASY-MEDIUM: a trait impl on &self, std::fmt::Formatter and debug_struct/finish_non_exhaustive (std calls that need models)	0,1,2,3,4,11
```

### Proof dependency order

`ct-eq-is-slice-equality` and `hmac-key-pads` (independent leaves, given aterm's SHA-256 rows) →
`hmac-refines-rfc2104` → `hmac-streaming-equals-one-shot` → `hmac-wiping-equals-parts` →
`hkdf-refines-rfc5869`; `hmac-verify-slice-iff` needs `ct-eq-is-slice-equality` and
`hmac-refines-rfc2104`. `opaque-debug-hmac` is independent. `ct-eq-data-independent-control-flow`
waits for gap N1.

## 2. Test → spec map (TSV)

`primary` is the spec that retires the test. `also` lists the other specs the same test samples.

```tsv
file	test	primary	also
src/lib.rs	ct_eq_accepts_identical_slices	ct-eq-is-slice-equality	
src/lib.rs	ct_eq_rejects_same_length_differences	ct-eq-is-slice-equality	
src/lib.rs	ct_eq_rejects_length_mismatch	ct-eq-is-slice-equality	
src/hmac.rs	rfc4231_test_vectors	hmac-refines-rfc2104	hmac-wiping-equals-parts, hmac-key-pads (vectors move to model facts)
src/hmac.rs	known_answers_on_both_sides_of_the_block_size	hmac-refines-rfc2104	hmac-key-pads
src/hmac.rs	the_parts_doors_mac_the_concatenation_wherever_it_is_cut	hmac-streaming-equals-one-shot	hmac-wiping-equals-parts
src/hmac.rs	the_wiping_door_zeroes_its_key_block_and_both_pads	hmac-wiping-equals-parts	hmac-key-pads
src/hmac.rs	verify_slice_rejects_a_truncated_or_extended_tag	hmac-verify-slice-iff	
src/hmac.rs	verify_slice_refuses_every_one_bit_flip_of_the_tag	hmac-verify-slice-iff	
src/hmac.rs	debug_does_not_leak_the_key	opaque-debug-hmac	hmac-key-pads (its control reads the key block)
src/hmac.rs	hkdf_matches_rfc5869_a1_a2_and_a3	hkdf-refines-rfc5869	(vectors move to model facts)
src/hmac.rs	an_empty_salt_is_32_zero_bytes	hkdf-refines-rfc5869	hmac-key-pads
src/hmac.rs	the_handshake_session_key_is_the_recorded_answer	hkdf-refines-rfc5869	
tests/lengths_and_streaming.rs	hmac_over_every_message_and_key_length_is_pinned	hmac-refines-rfc2104	hmac-key-pads
tests/lengths_and_streaming.rs	hmac_fed_in_arbitrary_chunks_matches_one_shot	hmac-streaming-equals-one-shot	hmac-wiping-equals-parts
tests/lengths_and_streaming.rs	hmac_verify_slice_accepts_the_tag_and_refuses_a_flipped_bit	hmac-verify-slice-iff	
```

The two SHA-256 tests of `tests/lengths_and_streaming.rs` (`sha256_over_every_length_and_large_inputs_is_pinned`,
`sha256_fed_in_arbitrary_chunks_matches_one_shot`) sample aterm's `sha256-digest-refines-fips` and
`sha256-streaming-equals-one-shot` rows.

## 3. Where the specs and the code disagree, or could

1. **No test samples `ct-eq-data-independent-control-flow`.** It is a relational constant-time
   spec, and Trust has no lane for that (gap N1). No source-text rule stands in for it: a
   data-dependent branch written another way (`match`, `?`, `break`, a short-circuit `&&` in the
   fold) passes any rule about spelling. astream-cap's `ct_diff` is the one compare whose shape a
   test pins, through the function its verify calls, because its width is fixed.
2. **The wipe is a property of the pads the door is handed, not of memory.**
   `the_wiping_door_zeroes_its_key_block_and_both_pads` holds the pads across `tag_then_wipe`, the
   wiping door's body, and sees them zero after it (deleting the wipe fails it); it cannot pin that
   `hmac_sha256_wiping`'s stores survive codegen, or that no copy of a pad outlives the call (the
   `Sha256` buffers the pads were fed into are not wiped). `hmac-wiping-equals-parts` says as much.
3. **The sweep oracle cannot be regenerated.** `HMAC_SWEEP` was recorded once against the removed
   `hmac` crate (in aterm). Under `hmac-refines-rfc2104` the oracle becomes the Clean HMAC model.
