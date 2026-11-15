// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `envelope.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `envelope.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================

    -- Clamps a cause-block byte length `raw_len` to the maximum cause-block ceiling `max_len` (`18`).
    def envelope_clamp_cause_len (raw_len : UInt64) (max_len : UInt64) : UInt64 :=
      if raw_len < max_len then raw_len else max_len

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaEnvelope)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaEnvelope

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

    prefix:100 "□" => _root_.Astream.Engine.TlaEnvelope.Always
    infixl:45 " ⊨ " => _root_.Astream.Engine.TlaEnvelope.Satisfies

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

    structure EnvelopeState where
      cause_len : UInt64
      max_len : UInt64

    def EnvelopeCauseBoundedInv (s : EnvelopeState) : Prop :=
      Nat.le (UInt64.toNat s.cause_len) (UInt64.toNat s.max_len)

    def Init (max_len : UInt64) (s : EnvelopeState) : Prop :=
      s.cause_len = 0 ∧ s.max_len = max_len

    def sizeCauseAction (raw_len : UInt64) (s sNext : EnvelopeState) : Prop :=
      sNext.max_len = s.max_len ∧
      sNext.cause_len = _root_.envelope_clamp_cause_len raw_len s.max_len

    def Next (s sNext : EnvelopeState) : Prop :=
      ∃ raw_len : UInt64, sizeCauseAction raw_len s sNext

    def Spec (max_len : UInt64) : StateMachine EnvelopeState :=
      StateMachine.mk (Init max_len) Next

    theorem clamp_le_max : forall (raw_len : UInt64) (max_len : UInt64),
        Nat.le (UInt64.toNat (_root_.envelope_clamp_cause_len raw_len max_len)) (UInt64.toNat max_len) :=
      fun raw_len max_len => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw_len max_len)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_len) (fun _ => raw_len))) (UInt64.toNat max_len))
        (instDecidableUInt64Lt raw_len max_len)
        (fun _ => Nat.le.refl (UInt64.toNat max_len))
        (fun h => Nat.le_of_lt h)

    theorem uint64_zero_le (a : UInt64) (hZero : a = 0) (b : UInt64) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_len : UInt64) (s : EnvelopeState) (hInit : Init max_len s) :
        EnvelopeCauseBoundedInv s :=
      uint64_zero_le s.cause_len hInit.1 s.max_len

    theorem next_preserves_inv (s sNext : EnvelopeState)
        (_hInv : EnvelopeCauseBoundedInv s) (hNext : Next s sNext) :
        EnvelopeCauseBoundedInv sNext :=
      Exists.elim hNext (fun raw_len hStep =>
        let hClamp : Nat.le (UInt64.toNat sNext.cause_len) (UInt64.toNat s.max_len) :=
          Eq.mpr
            (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.max_len)) hStep.2)
            (clamp_le_max raw_len s.max_len)
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.cause_len) (UInt64.toNat y)) hStep.1)
          hClamp)

    theorem spec_satisfies_envelope_cause_bounds (max_len : UInt64) :
        (Spec max_len) ⊨ □ (Lift EnvelopeCauseBoundedInv) :=
      invariantSatisfies (Spec max_len) EnvelopeCauseBoundedInv
        (init_establishes_inv max_len)
        next_preserves_inv

    end TlaEnvelope
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def envelope_version_valid_isl (version : UInt8) : Bool :=
      decide (version = 3)
}
