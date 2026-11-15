// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `lib.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `lib.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    --    Compiled directly from these Clean kernel definitions into Rust MIR
    --    (`pub const fn sha256_partial_take`, `pub const fn sha256_clamp_partial_len`)
    --    and verified by `trust_clean_origin::Faithful` (`clean-kernel-defeq`).
    -- ========================================================================

    -- Partial-block top-up byte count (`min(avail, data_len)`).
    def sha256_partial_take (avail : UInt64) (data_len : UInt64) : UInt64 :=
      if data_len < avail then data_len else avail

    -- Partial-block occupancy clamp (`min(buf_len, max_partial)`).
    def sha256_clamp_partial_len (buf_len : UInt64) (max_partial : UInt64) : UInt64 :=
      if buf_len < max_partial then buf_len else max_partial

    -- Top-level specification of `pub fn buf_len_is_partial(buf_len: u64, block_len: u64) -> bool`.
    def buf_len_is_partial_isl (buf_len : UInt64) (block_len : UInt64) : Bool :=
      decide (buf_len < block_len)

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & Streaming SHA-256 Protocol Specification
    --    (`Astream.Digest.TlaStreamingSha256`)
    -- ========================================================================
    namespace Astream
    namespace Digest
    namespace TlaStreamingSha256

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

    prefix:100 "□" => _root_.Astream.Digest.TlaStreamingSha256.Always
    infixl:45 " ⊨ " => _root_.Astream.Digest.TlaStreamingSha256.Satisfies

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

    -- Algebraic bound of `_root_.sha256_partial_take`:
    -- `sha256_partial_take avail data_len <= avail`.
    theorem sha256_partial_take_le_avail (avail data_len : UInt64) :
        Nat.le (UInt64.toNat (_root_.sha256_partial_take avail data_len)) (UInt64.toNat avail) :=
      @Decidable.casesOn (LT.lt data_len avail)
        (fun (d : Decidable (LT.lt data_len avail)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt data_len avail) d data_len avail)) (UInt64.toNat avail))
        (instDecidableUInt64Lt data_len avail)
        (fun _ => Nat.le_refl (UInt64.toNat avail))
        (fun hLt => Nat.le_of_lt hLt)

    -- Algebraic bound of `_root_.sha256_clamp_partial_len`:
    -- `sha256_clamp_partial_len buf_len max_partial <= max_partial`.
    theorem sha256_clamp_partial_le_max (buf_len max_partial : UInt64) :
        Nat.le (UInt64.toNat (_root_.sha256_clamp_partial_len buf_len max_partial)) (UInt64.toNat max_partial) :=
      @Decidable.casesOn (LT.lt buf_len max_partial)
        (fun (d : Decidable (LT.lt buf_len max_partial)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt buf_len max_partial) d buf_len max_partial)) (UInt64.toNat max_partial))
        (instDecidableUInt64Lt buf_len max_partial)
        (fun _ => Nat.le_refl (UInt64.toNat max_partial))
        (fun hLt => Nat.le_of_lt hLt)

    -- Multi-parameter compound streaming buffer transition specification:
    def sha256_next_buf_len_isl (cur_buf_len data_len tail_len : UInt64) : UInt64 :=
      if cur_buf_len == 0 then
        _root_.sha256_clamp_partial_len tail_len 63
      else
        let clamped_cur := _root_.sha256_clamp_partial_len cur_buf_len 63
        let take := _root_.sha256_partial_take (64 - clamped_cur) data_len
        if clamped_cur + take < 64 then
          clamped_cur + take
        else
          _root_.sha256_clamp_partial_len tail_len 63

    theorem bool_false_ne_true (h : false = true) : False :=
      Bool.noConfusion h

    theorem buf_len_is_partial_true_lt (buf_len block_len : UInt64) :
        _root_.buf_len_is_partial_isl buf_len block_len = true →
          Nat.lt (UInt64.toNat buf_len) (UInt64.toNat block_len) :=
      @Decidable.casesOn (LT.lt buf_len block_len)
        (fun (d : Decidable (LT.lt buf_len block_len)) =>
          @Decidable.decide (LT.lt buf_len block_len) d = true →
            Nat.lt (UInt64.toNat buf_len) (UInt64.toNat block_len))
        (instDecidableUInt64Lt buf_len block_len)
        (fun _ hEq => False.elim (bool_false_ne_true hEq))
        (fun hLt _ => hLt)

    -- Streaming SHA-256 state machine variables:
    --   bufLen           : partial-block byte count (`UInt64`, always `< 64` while active)
    --   totalBytes       : total message bytes absorbed
    --   blocksCompressed : 512-bit compression rounds executed
    --   finalized        : 0 = streaming (`update`), 1 = padded & finalized (`finalize`)
    structure StreamingState where
      bufLen           : UInt64
      totalBytes       : Nat
      blocksCompressed : Nat
      finalized        : Nat

    -- TLA+ Safety Invariant:
    -- 1. While streaming (`finalized = 0`), `bufLen < 64` holds before every `update`
    --    and `finalize` call so the `0x80` padding byte always fits in `buf[bufLen]`.
    -- 2. Once `finalize` completes (`finalized = 1`), the partial buffer is drained
    --    (`bufLen = 0`).
    def StreamingSha256Inv (s : StreamingState) : Prop :=
      (s.finalized = 0 → Nat.lt (UInt64.toNat s.bufLen) (UInt64.toNat 64)) ∧
      (s.finalized = 1 → s.bufLen = 0)

    def Init (s : StreamingState) : Prop :=
      s.bufLen = 0 ∧
      s.totalBytes = 0 ∧
      s.blocksCompressed = 0 ∧
      s.finalized = 0

    -- Action 1: BufferPartial — `update` buffers a partial tail `nextLen` satisfying
    -- the `buf_len_is_partial_isl` guard (`_root_.buf_len_is_partial_isl nextLen 64 = true`).
    def BufferPartial (nextLen : UInt64) (deltaBytes : Nat) (s sNext : StreamingState) : Prop :=
      s.finalized = 0 ∧
      _root_.buf_len_is_partial_isl nextLen 64 = true ∧
      sNext.bufLen = nextLen ∧
      sNext.totalBytes = s.totalBytes + deltaBytes ∧
      sNext.blocksCompressed = s.blocksCompressed ∧
      sNext.finalized = 0

    -- Action 2: CompressFullBlock — `update` fills `buf` to 64 bytes, runs `compress`,
    -- and resets `bufLen' = 0`.
    def CompressFullBlock (deltaBytes : Nat) (s sNext : StreamingState) : Prop :=
      s.finalized = 0 ∧
      sNext.bufLen = 0 ∧
      sNext.totalBytes = s.totalBytes + deltaBytes ∧
      sNext.blocksCompressed = Nat.succ s.blocksCompressed ∧
      sNext.finalized = 0

    -- Action 3: FinalizeDigest — `finalize` writes `0x80` at `bufLen < 64`, pads and
    -- compresses 1 or 2 blocks (`paddingBlocks`), and drains `bufLen' = 0`.
    def FinalizeDigest (paddingBlocks : Nat) (s sNext : StreamingState) : Prop :=
      s.finalized = 0 ∧
      sNext.bufLen = 0 ∧
      sNext.totalBytes = s.totalBytes ∧
      sNext.blocksCompressed = s.blocksCompressed + paddingBlocks ∧
      sNext.finalized = 1

    def Next (nextLen : UInt64) (deltaBytes paddingBlocks : Nat) (s sNext : StreamingState) : Prop :=
      BufferPartial nextLen deltaBytes s sNext ∨
        (CompressFullBlock deltaBytes s sNext ∨ FinalizeDigest paddingBlocks s sNext)

    def Spec (nextLen : UInt64) (deltaBytes paddingBlocks : Nat) : StateMachine StreamingState :=
      StateMachine.mk Init (Next nextLen deltaBytes paddingBlocks)

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem one_ne_zero (h : 1 = 0) : False :=
      Nat.noConfusion h

    theorem zero_lt_64 : Nat.lt (UInt64.toNat 0) (UInt64.toNat 64) :=
      Nat.zero_lt_succ 63

    theorem init_establishes_inv (s : StreamingState) (hInit : Init s) :
        StreamingSha256Inv s :=
      And.intro
        (fun _ =>
          Eq.mpr (congrArg (fun b => Nat.lt (UInt64.toNat b) (UInt64.toNat 64)) hInit.1) zero_lt_64)
        (fun hFin1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.2.2) hFin1
          False.elim (zero_ne_one h01))

    theorem bufferPartial_preserves_inv (nextLen : UInt64) (deltaBytes : Nat)
        (s sNext : StreamingState) (hAct : BufferPartial nextLen deltaBytes s sNext) :
        StreamingSha256Inv sNext :=
      And.intro
        (fun _ =>
          let hLt : Nat.lt (UInt64.toNat nextLen) (UInt64.toNat 64) :=
            buf_len_is_partial_true_lt nextLen 64 hAct.2.1
          Eq.mpr (congrArg (fun b => Nat.lt (UInt64.toNat b) (UInt64.toNat 64)) hAct.2.2.1) hLt)
        (fun hFin1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2.2.2.2) hFin1
          False.elim (zero_ne_one h01))

    theorem compressFullBlock_preserves_inv (deltaBytes : Nat)
        (s sNext : StreamingState) (hAct : CompressFullBlock deltaBytes s sNext) :
        StreamingSha256Inv sNext :=
      And.intro
        (fun _ =>
          Eq.mpr (congrArg (fun b => Nat.lt (UInt64.toNat b) (UInt64.toNat 64)) hAct.2.1) zero_lt_64)
        (fun hFin1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2.2.2) hFin1
          False.elim (zero_ne_one h01))

    theorem finalizeDigest_preserves_inv (paddingBlocks : Nat)
        (s sNext : StreamingState) (hAct : FinalizeDigest paddingBlocks s sNext) :
        StreamingSha256Inv sNext :=
      And.intro
        (fun hFin0 =>
          let h10 : 1 = 0 := Eq.trans (Eq.symm hAct.2.2.2.2) hFin0
          False.elim (one_ne_zero h10))
        (fun _ => hAct.2.1)

    theorem next_preserves_inv (nextLen : UInt64) (deltaBytes paddingBlocks : Nat)
        (s sNext : StreamingState) (hNext : Next nextLen deltaBytes paddingBlocks s sNext) :
        StreamingSha256Inv sNext :=
      Or.elim hNext
        (fun hBuf => bufferPartial_preserves_inv nextLen deltaBytes s sNext hBuf)
        (fun hRest =>
          Or.elim hRest
            (fun hComp => compressFullBlock_preserves_inv deltaBytes s sNext hComp)
            (fun hFin => finalizeDigest_preserves_inv paddingBlocks s sNext hFin))

    -- Full TLA+ Temporal Safety Theorem:
    --   `Spec nextLen deltaBytes paddingBlocks ⊨ □ (Lift StreamingSha256Inv)`
    theorem spec_satisfies_streaming_sha256_safety
        (nextLen : UInt64) (deltaBytes paddingBlocks : Nat) :
        (Spec nextLen deltaBytes paddingBlocks) ⊨ □ (Lift StreamingSha256Inv) :=
      invariantSatisfies (Spec nextLen deltaBytes paddingBlocks) StreamingSha256Inv
        init_establishes_inv
        (fun s sNext _ hNext => next_preserves_inv nextLen deltaBytes paddingBlocks s sNext hNext)

    end TlaStreamingSha256
    end Digest
    end Astream
}
