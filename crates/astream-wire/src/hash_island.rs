// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `hash.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `hash.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaSlicingCrc32)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaSlicingCrc32

    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop

    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)

    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    prefix:100 "□" => _root_.Astream.Wire.TlaSlicingCrc32.Always
    infixl:45 " ⊨ " => _root_.Astream.Wire.TlaSlicingCrc32.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      @Nat.rec (fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun step => hStep (b k) (b (Nat.succ k)) ih step)
            (fun stutter => Eq.mpr (congrArg I stutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    end TlaSlicingCrc32
    end Wire
    end Astream

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    --    Compiled directly from these Clean kernel definitions into Rust MIR
    --    (`pub const fn crc_table_index_clamp`, `pub const fn crc32_poly_select`,
    --    `pub const fn fnv1a_64_xor`, and `pub const fn fnv1a_64_mul_prime`) and
    --    verified by `trust_clean_origin::Faithful` (`clean-kernel-defeq`).
    -- ========================================================================

    -- Clamp a table lookup index `idx` to `max_idx` (`255` for a 256-entry CRC row).
    -- Compiled directly to `pub const fn crc_table_index_clamp(idx: u64, max_idx: u64) -> u64`.
    def crc_table_index_clamp (idx : UInt64) (max_idx : UInt64) : UInt64 :=
      if idx < max_idx then idx else max_idx

    -- Reflected CRC-32/IEEE polynomial tap selector for one bit-step:
    -- selects `0` when the low bit `crc &&& 1` is `0`, or the generator
    -- polynomial `poly` (`0xEDB8_8320`) when `crc &&& 1` is `1`.
    -- Compiled directly to `pub const fn crc32_poly_select(crc: u32, poly: u32) -> u32`.
    def crc32_poly_select (crc : UInt32) (poly : UInt32) : UInt32 :=
      if (crc &&& 1) == 0 then 0 else poly

    -- 64-bit FNV-1a word/byte XOR step (`h ^^^ word`).
    -- Compiled directly to `pub const fn fnv1a_64_xor(h: u64, word: u64) -> u64`.
    def fnv1a_64_xor (h : UInt64) (word : UInt64) : UInt64 :=
      h ^^^ word

    -- 64-bit FNV-1a prime multiplication step (`xored * prime`).
    -- Compiled directly to `pub const fn fnv1a_64_mul_prime(xored: u64, prime: u64) -> u64`.
    def fnv1a_64_mul_prime (xored : UInt64) (prime : UInt64) : UInt64 :=
      xored * prime

    -- ========================================================================
    -- 3. TLA+ Protocol Specification & Functional Refinement Contracts:
    --    Slicing-by-8 Table Recurrence, Streaming CRC-32 Homomorphism,
    --    and FNV-1a/64 Left-Fold Specification
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaSlicingCrc32

    -- Island specification of `pub fn crc_table_index_in_bounds(idx: u64, max_idx: u64) -> bool`.
    def crc_table_index_in_bounds_isl (idx : UInt64) (max_idx : UInt64) : Bool :=
      decide (idx <= max_idx)

    -- Island specification of `pub const fn fnv1a_64_state_matches(h: u64, expected: u64) -> bool`.
    def fnv1a_64_state_matches_isl (h : UInt64) (expected : UInt64) : Bool :=
      decide (h = expected)

    -- Published CRC-32/IEEE reflected generator polynomial (`0xEDB8_8320`).
    def crc32_ieee_poly_isl : UInt32 := 3988292384

    -- Published 64-bit FNV-1a parameters (`FNV1A_64_INIT = 0xcbf2_9ce4_8422_2325`,
    -- `FNV1A_64_PRIME = 0x0000_0100_0000_01b3`).
    def fnv1a_64_init_isl : UInt64 := 14695981039346656037
    def fnv1a_64_prime_isl : UInt64 := 1099511628211

    -- Island specifications of `crc32_is_ieee_poly`, `fnv1a_64_is_init`, and `fnv1a_64_is_prime`.
    def crc32_is_ieee_poly_isl (poly : UInt32) : Bool :=
      decide (poly = crc32_ieee_poly_isl)

    def fnv1a_64_is_init_isl (h : UInt64) : Bool :=
      decide (h = fnv1a_64_init_isl)

    def fnv1a_64_is_prime_isl (p : UInt64) : Bool :=
      decide (p = fnv1a_64_prime_isl)

    -- Island specification of `pub const fn fnv1a_64_mix_u64(h: u64, word: u64) -> u64`:
    -- `(h ^ word).wrapping_mul(FNV1A_64_PRIME)`.
    def fnv1a_64_mix_u64_isl (h : UInt64) (word : UInt64) : UInt64 :=
      (h ^^^ word) * fnv1a_64_prime_isl

    -- ------------------------------------------------------------------------
    -- 3a. Slice-by-8 Table Generation Recurrence Lemma (`crc32_row0`, `crc32_tables`)
    -- ------------------------------------------------------------------------

    theorem crc32_poly_select_even (poly : UInt32) : _root_.crc32_poly_select 0 poly = 0 :=
      rfl

    theorem crc32_poly_select_odd (poly : UInt32) : _root_.crc32_poly_select 1 poly = poly :=
      rfl

    -- One reflected polynomial bit-step of register `c`:
    -- `(c >> 1) ^ crc32_poly_select(c, CRC32_IEEE_POLY)`.
    def crc32_bit_step (shr1 : UInt32 → UInt32) (xor_op : UInt32 → UInt32 → UInt32) (c : UInt32) : UInt32 :=
      xor_op (shr1 c) (_root_.crc32_poly_select c crc32_ieee_poly_isl)

    -- `steps` iterated reflected bit-steps from register `c`.
    def crc32_bit_steps (bit_step : UInt32 → UInt32) (steps : Nat) (c : UInt32) : UInt32 :=
      @Nat.rec (fun _ => UInt32 → UInt32)
        (fun x => x)
        (fun _ step_fn x => step_fn (bit_step x))
        steps
        c

    -- `crc32_row0()[n]`: eight reflected bit-steps of byte `n` under `0xEDB8_8320`.
    def crc32_row0_entry (bit_step : UInt32 → UInt32) (b : UInt32) : UInt32 :=
      crc32_bit_steps bit_step 8 b

    theorem crc32_row0_entry_unfold (bit_step : UInt32 → UInt32) (b : UInt32) :
        crc32_row0_entry bit_step b =
          bit_step (bit_step (bit_step (bit_step (bit_step (bit_step (bit_step (bit_step b))))))) :=
      rfl

    -- Row `k` of `crc32_tables()`: row 0 is `row0`, and row `k + 1` applies one
    -- zero-byte Sarwate step `zero_step c = (c >> 8) ^ row0 (c as u8)` to row `k`.
    def crc32_table_row (zero_step : UInt32 → UInt32) (row0 : UInt8 → UInt32) (k : Nat) (n : UInt8) : UInt32 :=
      @Nat.rec (fun _ => UInt8 → UInt32)
        row0
        (fun _ prev_row b => zero_step (prev_row b))
        k
        n

    -- Register state after `k` trailing zero bytes starting from register `c`.
    def crc32_zero_run (zero_step : UInt32 → UInt32) (k : Nat) (c : UInt32) : UInt32 :=
      @Nat.rec (fun _ => UInt32)
        c
        (fun _ acc => zero_step acc)
        k

    -- Slice-by-8 table lemma: row `k` of `crc32_tables()` at byte `n` is the register
    -- after byte `n` (`row0 n`) followed by `k` zero-byte steps, from register 0.
    theorem crc32_table_row_eq_zero_run
        (zero_step : UInt32 → UInt32) (row0 : UInt8 → UInt32) (k : Nat) (n : UInt8) :
        crc32_table_row zero_step row0 k n = crc32_zero_run zero_step k (row0 n) :=
      @Nat.rec
        (fun m => ∀ b : UInt8, crc32_table_row zero_step row0 m b = crc32_zero_run zero_step m (row0 b))
        (fun _ => rfl)
        (fun _ ih b => congrArg zero_step (ih b))
        k
        n

    theorem crc32_table_row0_eq (zero_step : UInt32 → UInt32) (row0 : UInt8 → UInt32) (n : UInt8) :
        crc32_table_row zero_step row0 0 n = row0 n :=
      rfl

    theorem crc32_table_row7_eq (zero_step : UInt32 → UInt32) (row0 : UInt8 → UInt32) (n : UInt8) :
        crc32_table_row zero_step row0 7 n =
          zero_step (zero_step (zero_step (zero_step (zero_step (zero_step (zero_step (row0 n))))))) :=
      rfl

    -- ------------------------------------------------------------------------
    -- 3b. Streaming CRC-32/IEEE Refinement & Split-Invariance Homomorphism
    --     `crc32_ieee_update(crc32_ref(p), d) == crc32_ref(p ++ d)`
    -- ------------------------------------------------------------------------

    inductive ByteList where
      | nil : ByteList
      | cons : UInt8 → ByteList → ByteList

    def ByteList.append (a b : ByteList) : ByteList :=
      @ByteList.rec (fun _ => ByteList)
        b
        (fun head _ tail_acc => ByteList.cons head tail_acc)
        a

    -- Left fold of the uninverted CRC-32 register across a byte sequence `d`.
    def crc32_step_fold (byte_step : UInt32 → UInt8 → UInt32) (d : ByteList) (c : UInt32) : UInt32 :=
      @ByteList.rec (fun _ => UInt32 → UInt32)
        (fun acc => acc)
        (fun head _ tail_fn acc => tail_fn (byte_step acc head))
        d
        c

    theorem crc32_step_fold_nil (byte_step : UInt32 → UInt8 → UInt32) (c : UInt32) :
        crc32_step_fold byte_step ByteList.nil c = c :=
      rfl

    theorem crc32_step_fold_cons
        (byte_step : UInt32 → UInt8 → UInt32) (b : UInt8) (tail : ByteList) (c : UInt32) :
        crc32_step_fold byte_step (ByteList.cons b tail) c =
          crc32_step_fold byte_step tail (byte_step c b) :=
      rfl

    -- Register fold homomorphism: folding `a` then `b` equals folding `a ++ b`.
    theorem crc32_step_fold_append
        (byte_step : UInt32 → UInt8 → UInt32) (a b : ByteList) (c : UInt32) :
        crc32_step_fold byte_step b (crc32_step_fold byte_step a c) =
          crc32_step_fold byte_step (ByteList.append a b) c :=
      @ByteList.rec
        (fun xs => ∀ acc : UInt32,
          crc32_step_fold byte_step b (crc32_step_fold byte_step xs acc) =
            crc32_step_fold byte_step (ByteList.append xs b) acc)
        (fun _ => rfl)
        (fun head _ ih acc => ih (byte_step acc head))
        a
        c

    -- Bitwise reference model `crc32_ref(d)`: seed register at `inv 0` (`0xFFFF_FFFF`),
    -- fold `byte_step` across `d`, and invert out via `inv` (`!state`).
    def crc32_ref_model
        (inv : UInt32 → UInt32) (byte_step : UInt32 → UInt8 → UInt32) (d : ByteList) : UInt32 :=
      inv (crc32_step_fold byte_step d (inv 0))

    -- Streaming `crc32_ieee_update(crc, d)` model: un-invert `crc` via `inv`,
    -- fold `byte_step` across `d`, and invert out via `inv`.
    def crc32_update_model
        (inv : UInt32 → UInt32) (byte_step : UInt32 → UInt8 → UInt32) (crc : UInt32) (d : ByteList) : UInt32 :=
      inv (crc32_step_fold byte_step d (inv crc))

    -- Base refinement identity: `crc32_ieee_update(0, d) == crc32_ref(d)`.
    theorem crc32_update_zero_eq_ref
        (inv : UInt32 → UInt32) (byte_step : UInt32 → UInt8 → UInt32) (d : ByteList) :
        crc32_update_model inv byte_step 0 d = crc32_ref_model inv byte_step d :=
      rfl

    -- Streaming refinement identity:
    -- `crc32_ieee_update(crc32_ref(p), d) == crc32_ref(p ++ d)` for any involutive
    -- bitwise complement `inv` (`∀ c, inv (inv c) = c`).
    theorem crc32_update_ref_append
        (inv : UInt32 → UInt32) (byte_step : UInt32 → UInt8 → UInt32)
        (hInv : ∀ c : UInt32, inv (inv c) = c) (p d : ByteList) :
        crc32_update_model inv byte_step (crc32_ref_model inv byte_step p) d =
          crc32_ref_model inv byte_step (ByteList.append p d) :=
      Eq.trans
        (congrArg (fun seed => inv (crc32_step_fold byte_step d seed))
          (hInv (crc32_step_fold byte_step p (inv 0))))
        (congrArg inv (crc32_step_fold_append byte_step p d (inv 0)))

    -- General split-invariance homomorphism from any initial `crc`:
    -- `crc32_ieee_update(crc32_ieee_update(crc, a), b) == crc32_ieee_update(crc, a ++ b)`.
    theorem crc32_update_assoc
        (inv : UInt32 → UInt32) (byte_step : UInt32 → UInt8 → UInt32)
        (hInv : ∀ c : UInt32, inv (inv c) = c) (crc : UInt32) (a b : ByteList) :
        crc32_update_model inv byte_step (crc32_update_model inv byte_step crc a) b =
          crc32_update_model inv byte_step crc (ByteList.append a b) :=
      Eq.trans
        (congrArg (fun seed => inv (crc32_step_fold byte_step b seed))
          (hInv (crc32_step_fold byte_step a (inv crc))))
        (congrArg inv (crc32_step_fold_append byte_step a b (inv crc)))

    -- 8-byte Slicing-by-8 chunk prepended to `tail`.
    def crc32_chunk8_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (tail : ByteList) : ByteList :=
      ByteList.cons b0 (ByteList.cons b1 (ByteList.cons b2 (ByteList.cons b3
        (ByteList.cons b4 (ByteList.cons b5 (ByteList.cons b6 (ByteList.cons b7 tail)))))))

    -- Slicing-by-8 loop invariant step: when one 8-table lookup step `slice8_step`
    -- equals 8 sequential `byte_step` transitions, advancing by `slice8_step` and
    -- folding `tail` equals folding the 8-byte chunk followed by `tail`.
    theorem crc32_slice8_chunk_eq_step_fold
        (byte_step : UInt32 → UInt8 → UInt32)
        (slice8_step : UInt32 → UInt8 → UInt8 → UInt8 → UInt8 → UInt8 → UInt8 → UInt8 → UInt8 → UInt32)
        (hSlice8 : ∀ (c : UInt32) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8),
          slice8_step c b0 b1 b2 b3 b4 b5 b6 b7 =
            byte_step (byte_step (byte_step (byte_step (byte_step (byte_step (byte_step (byte_step c b0) b1) b2) b3) b4) b5) b6) b7)
        (c : UInt32) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (tail : ByteList) :
        crc32_step_fold byte_step tail (slice8_step c b0 b1 b2 b3 b4 b5 b6 b7) =
          crc32_step_fold byte_step (crc32_chunk8_bytes b0 b1 b2 b3 b4 b5 b6 b7 tail) c :=
      congrArg (crc32_step_fold byte_step tail) (hSlice8 c b0 b1 b2 b3 b4 b5 b6 b7)

    -- ------------------------------------------------------------------------
    -- 3c. FNV-1a/64 Left-Fold Contract & Published Parameters
    --     `fnv1a_64_update(h, d)` = left fold of `(h ^ b) * 0x0000_0100_0000_01b3`
    -- ------------------------------------------------------------------------

    theorem fnv1a_64_xor_def (h : UInt64) (word : UInt64) :
        _root_.fnv1a_64_xor h word = h ^^^ word :=
      rfl

    theorem fnv1a_64_mul_prime_def (xored : UInt64) (prime : UInt64) :
        _root_.fnv1a_64_mul_prime xored prime = xored * prime :=
      rfl

    -- Composition theorem for `fnv1a_64_mix_u64`: composing the two Clean-origin (`I5`)
    -- kernels `_root_.fnv1a_64_xor` and `_root_.fnv1a_64_mul_prime` at `FNV1A_64_PRIME`
    -- computes `(h ^ word).wrapping_mul(FNV1A_64_PRIME)` (`fnv1a_64_mix_u64_isl`).
    theorem fnv1a_64_mix_u64_eq_pieces (h : UInt64) (word : UInt64) :
        _root_.fnv1a_64_mul_prime (_root_.fnv1a_64_xor h word) fnv1a_64_prime_isl =
          fnv1a_64_mix_u64_isl h word :=
      rfl

    -- One byte step of FNV-1a/64: `(h ^ b) * 0x0000_0100_0000_01b3`, calling the
    -- Clean-origin `_root_.fnv1a_64_mul_prime` compiled directly to Rust MIR.
    def fnv1a_64_step (xor_byte : UInt64 → UInt8 → UInt64) (h : UInt64) (b : UInt8) : UInt64 :=
      _root_.fnv1a_64_mul_prime (xor_byte h b) fnv1a_64_prime_isl

    -- Left fold of `fnv1a_64_step` across a byte sequence `d` from seed `h`.
    def fnv1a_64_fold (xor_byte : UInt64 → UInt8 → UInt64) (d : ByteList) (h : UInt64) : UInt64 :=
      @ByteList.rec (fun _ => UInt64 → UInt64)
        (fun acc => acc)
        (fun head _ tail_fn acc => tail_fn (fnv1a_64_step xor_byte acc head))
        d
        h

    -- One-shot `fnv1a_64(d)` model: `fnv1a_64_fold` seeded at `FNV1A_64_INIT`.
    def fnv1a_64_model (xor_byte : UInt64 → UInt8 → UInt64) (d : ByteList) : UInt64 :=
      fnv1a_64_fold xor_byte d fnv1a_64_init_isl

    theorem fnv1a_64_fold_nil (xor_byte : UInt64 → UInt8 → UInt64) (h : UInt64) :
        fnv1a_64_fold xor_byte ByteList.nil h = h :=
      rfl

    theorem fnv1a_64_fold_cons
        (xor_byte : UInt64 → UInt8 → UInt64) (b : UInt8) (tail : ByteList) (h : UInt64) :
        fnv1a_64_fold xor_byte (ByteList.cons b tail) h =
          fnv1a_64_fold xor_byte tail (_root_.fnv1a_64_mul_prime (xor_byte h b) fnv1a_64_prime_isl) :=
      rfl

    theorem fnv1a_64_fold_singleton
        (xor_byte : UInt64 → UInt8 → UInt64) (b : UInt8) (h : UInt64) :
        fnv1a_64_fold xor_byte (ByteList.cons b ByteList.nil) h =
          _root_.fnv1a_64_mul_prime (xor_byte h b) fnv1a_64_prime_isl :=
      rfl

    -- Left-fold append homomorphism:
    -- `fnv1a_64_update(fnv1a_64_update(h, a), b) == fnv1a_64_update(h, a ++ b)`.
    theorem fnv1a_64_fold_append
        (xor_byte : UInt64 → UInt8 → UInt64) (a b : ByteList) (h : UInt64) :
        fnv1a_64_fold xor_byte b (fnv1a_64_fold xor_byte a h) =
          fnv1a_64_fold xor_byte (ByteList.append a b) h :=
      @ByteList.rec
        (fun xs => ∀ acc : UInt64,
          fnv1a_64_fold xor_byte b (fnv1a_64_fold xor_byte xs acc) =
            fnv1a_64_fold xor_byte (ByteList.append xs b) acc)
        (fun _ => rfl)
        (fun head _ ih acc => ih (fnv1a_64_step xor_byte acc head))
        a
        h

    theorem fnv1a_64_update_init_eq_model
        (xor_byte : UInt64 → UInt8 → UInt64) (d : ByteList) :
        fnv1a_64_fold xor_byte d fnv1a_64_init_isl = fnv1a_64_model xor_byte d :=
      rfl

    -- ------------------------------------------------------------------------
    -- 3d. Slicing-by-8 Table Lookup Bounds Safety State Machine
    -- ------------------------------------------------------------------------

    theorem crc_table_index_clamp_le_max : forall (idx : UInt64) (max_idx : UInt64),
        Nat.le (UInt64.toNat (_root_.crc_table_index_clamp idx max_idx)) (UInt64.toNat max_idx) :=
      fun idx max_idx => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt idx max_idx)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_idx) (fun _ => idx))) (UInt64.toNat max_idx))
        (instDecidableUInt64Lt idx max_idx)
        (fun _ => Nat.le.refl (UInt64.toNat max_idx))
        (fun h => Nat.le_of_lt h)

    -- State of the Slicing-by-8 streaming CRC-32 engine:
    --   lastIdx : most recent table row lookup index (`UInt64`)
    --   maxIdx  : upper bound of a 256-entry CRC table row (`UInt64`, 255)
    structure CrcLookupState where
      lastIdx : UInt64
      maxIdx  : UInt64

    -- TLA+ Safety Invariant:
    -- `lastIdx <= maxIdx`: every Slicing-by-8 table lookup index stays within `[0, maxIdx]`.
    def SlicingCrcSafetyInv (s : CrcLookupState) : Prop :=
      Nat.le (UInt64.toNat s.lastIdx) (UInt64.toNat s.maxIdx)

    def Init (s : CrcLookupState) : Prop :=
      s.lastIdx = 0 ∧
      s.maxIdx = 255

    -- Action 1: LookupByte — performs a bounded table lookup at `_root_.crc_table_index_clamp raw_idx s.maxIdx`.
    def LookupByte (raw_idx : UInt64) (s sNext : CrcLookupState) : Prop :=
      sNext.lastIdx = _root_.crc_table_index_clamp raw_idx s.maxIdx ∧
      sNext.maxIdx = s.maxIdx

    -- Action 2: ResetState — resets `lastIdx` to `0` at the start of a new frame.
    def ResetState (s sNext : CrcLookupState) : Prop :=
      sNext.lastIdx = 0 ∧
      sNext.maxIdx = s.maxIdx

    def Next (s sNext : CrcLookupState) : Prop :=
      (∃ raw_idx : UInt64, LookupByte raw_idx s sNext) ∨ ResetState s sNext

    def Spec : StateMachine CrcLookupState :=
      StateMachine.mk Init Next

    theorem zero_le_uint64 (u : UInt64) (hZero : u = 0) :
        forall (m : UInt64), Nat.le (UInt64.toNat u) (UInt64.toNat m) :=
      fun m =>
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat m)) hZero)
          (Nat.zero_le (UInt64.toNat m))

    theorem init_implies_inv (s : CrcLookupState) (hInit : Init s) : SlicingCrcSafetyInv s :=
      zero_le_uint64 s.lastIdx hInit.1 s.maxIdx

    theorem lookup_preserves_inv (raw_idx : UInt64) (s sNext : CrcLookupState)
        (_hInv : SlicingCrcSafetyInv s) (hAct : LookupByte raw_idx s sNext) :
        SlicingCrcSafetyInv sNext :=
      let h1 : Nat.le (UInt64.toNat sNext.lastIdx) (UInt64.toNat s.maxIdx) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxIdx)) hAct.1)
          (crc_table_index_clamp_le_max raw_idx s.maxIdx)
      Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat sNext.lastIdx) (UInt64.toNat x)) hAct.2)
        h1

    theorem reset_preserves_inv (s sNext : CrcLookupState)
        (_hInv : SlicingCrcSafetyInv s) (hAct : ResetState s sNext) :
        SlicingCrcSafetyInv sNext :=
      zero_le_uint64 sNext.lastIdx hAct.1 sNext.maxIdx

    theorem next_preserves_inv (s sNext : CrcLookupState)
        (hInv : SlicingCrcSafetyInv s) (hNext : Next s sNext) :
        SlicingCrcSafetyInv sNext :=
      Or.elim hNext
        (fun hLook => Exists.elim hLook (fun raw hAct => lookup_preserves_inv raw s sNext hInv hAct))
        (fun hRes => reset_preserves_inv s sNext hInv hRes)

    -- ========================================================================
    -- 4. Top-Level Temporal Theorem: `Spec ⊨ □ (Lift SlicingCrcSafetyInv)`
    -- ========================================================================
    theorem spec_satisfies_always_crc_safety : Spec ⊨ □ (Lift SlicingCrcSafetyInv) :=
      invariantSatisfies Spec SlicingCrcSafetyInv init_implies_inv next_preserves_inv

    end TlaSlicingCrc32
    end Wire
    end Astream
}
