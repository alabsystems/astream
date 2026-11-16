// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for DEC private mode (`?1..=?2026`) bitmask snapshotting and bounded
// VT restore emission (`Astream.Term.TlaDecPrivateModeMask`), mounted under
// `cfg(clean_islands)` in `decset_mode_snapshot.rs`. Proves
// `emittedBytes <= maxRestoreBytes` and `activeBits <= maxModeBits`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def dec_restore_bytes_clamp (proposed_bytes : UInt64) (max_bytes : UInt64) : UInt64 :=
      if proposed_bytes < max_bytes then proposed_bytes else max_bytes

    def dec_mode_bits_clamp (active_bits : UInt64) (max_bits : UInt64) : UInt64 :=
      if active_bits < max_bits then active_bits else max_bits

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaDecPrivateModeMask)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaDecPrivateModeMask

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Term.TlaDecPrivateModeMask.Satisfies M F
    prefix:75 "□" => _root_.Astream.Term.TlaDecPrivateModeMask.Always

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      Nat.rec
        (motive := fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun hNext => hStep (b k) (b (Nat.succ k)) ih hNext)
            (fun hStutter => Eq.mpr (congrArg I hStutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    -- ========================================================================
    -- 3. DEC Private Mode Snapshot State Machine
    -- ========================================================================

    structure DecModeState where
      emittedBytes    : UInt64
      maxRestoreBytes : UInt64
      activeBits      : UInt64
      maxModeBits     : UInt64

    def DecModeInv (s : DecModeState) : Prop :=
      Nat.le (UInt64.toNat s.emittedBytes) (UInt64.toNat s.maxRestoreBytes) ∧
      Nat.le (UInt64.toNat s.activeBits) (UInt64.toNat s.maxModeBits)

    def Init (maxRestoreBytes maxModeBits : UInt64) (s : DecModeState) : Prop :=
      s.emittedBytes = (0 : UInt64) ∧
      s.maxRestoreBytes = maxRestoreBytes ∧
      s.activeBits = (0 : UInt64) ∧
      s.maxModeBits = maxModeBits

    def EmitModeDiff (rawBytes rawBits : UInt64) (s sNext : DecModeState) : Prop :=
      sNext.emittedBytes = _root_.dec_restore_bytes_clamp rawBytes s.maxRestoreBytes ∧
      sNext.maxRestoreBytes = s.maxRestoreBytes ∧
      sNext.activeBits = _root_.dec_mode_bits_clamp rawBits s.maxModeBits ∧
      sNext.maxModeBits = s.maxModeBits

    def Next (s sNext : DecModeState) : Prop :=
      ∃ rb : UInt64, ∃ rbits : UInt64, EmitModeDiff rb rbits s sNext

    def Spec (maxRestoreBytes maxModeBits : UInt64) : StateMachine DecModeState :=
      StateMachine.mk (Init maxRestoreBytes maxModeBits) Next

    theorem bytes_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.dec_restore_bytes_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem bits_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.dec_mode_bits_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxRestoreBytes maxModeBits : UInt64) (s : DecModeState)
        (hInit : Init maxRestoreBytes maxModeBits s) : DecModeInv s :=
      And.intro
        (zero_u64_le s.emittedBytes s.maxRestoreBytes hInit.1)
        (zero_u64_le s.activeBits s.maxModeBits hInit.2.2.1)

    theorem emitModeDiff_preserves_inv (rb rbits : UInt64) (s sNext : DecModeState)
        (hAct : EmitModeDiff rb rbits s sNext) : DecModeInv sNext :=
      let hB1 : Nat.le (UInt64.toNat sNext.emittedBytes) (UInt64.toNat s.maxRestoreBytes) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRestoreBytes)) hAct.1)
          (bytes_clamp_le rb s.maxRestoreBytes)
      let hB2 : Nat.le (UInt64.toNat sNext.emittedBytes) (UInt64.toNat sNext.maxRestoreBytes) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.emittedBytes) (UInt64.toNat y)) hAct.2.1)
          hB1
      let hM1 : Nat.le (UInt64.toNat sNext.activeBits) (UInt64.toNat s.maxModeBits) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxModeBits)) hAct.2.2.1)
          (bits_clamp_le rbits s.maxModeBits)
      let hM2 : Nat.le (UInt64.toNat sNext.activeBits) (UInt64.toNat sNext.maxModeBits) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.activeBits) (UInt64.toNat y)) hAct.2.2.2)
          hM1
      And.intro hB2 hM2

    theorem next_preserves_inv (s sNext : DecModeState)
        (_hInv : DecModeInv s) (hNext : Next s sNext) : DecModeInv sNext :=
      Exists.elim hNext (fun rb hEx2 =>
        Exists.elim hEx2 (fun rbits hAct => emitModeDiff_preserves_inv rb rbits s sNext hAct))

    theorem spec_satisfies_dec_private_mode_mask_safety (maxRestoreBytes maxModeBits : UInt64) :
        (Spec maxRestoreBytes maxModeBits) ⊨ □ (Lift DecModeInv) :=
      invariantSatisfies (Spec maxRestoreBytes maxModeBits) DecModeInv
        (init_establishes_inv maxRestoreBytes maxModeBits)
        next_preserves_inv

    end TlaDecPrivateModeMask
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def dec_restore_fits_budget_isl (proposed_bytes : UInt64) (max_bytes : UInt64) : Bool :=
      decide (proposed_bytes ≤ max_bytes)
}
