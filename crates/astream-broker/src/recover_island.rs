// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `recover.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `recover.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `twins.rs` of the function it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def recover_unit_start_advance (seal_end : UInt64) (floor : UInt64) : UInt64 :=
      if seal_end < floor then floor else seal_end

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaRecoveryClassifier)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaRecoveryClassifier

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaRecoveryClassifier.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaRecoveryClassifier.Always

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

    structure RecoverUnitState where
      sealEnd   : UInt64
      unitStart : UInt64

    def RecoverUnitStartInv (s : RecoverUnitState) : Prop :=
      Nat.le (UInt64.toNat s.sealEnd) (UInt64.toNat s.unitStart)

    def Init (s : RecoverUnitState) : Prop :=
      s.sealEnd = s.unitStart

    def computeUnitStartAction (floor : UInt64) (s sNext : RecoverUnitState) : Prop :=
      sNext.sealEnd = s.unitStart ∧
      sNext.unitStart = _root_.recover_unit_start_advance s.unitStart floor

    def Next (s sNext : RecoverUnitState) : Prop :=
      ∃ floor : UInt64, computeUnitStartAction floor s sNext

    def Spec : StateMachine RecoverUnitState :=
      StateMachine.mk Init Next

    theorem advance_ge_seal : forall (seal_end : UInt64) (floor : UInt64),
        Nat.le (UInt64.toNat seal_end) (UInt64.toNat (_root_.recover_unit_start_advance seal_end floor)) :=
      fun seal_end floor => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt seal_end floor)) =>
          Nat.le (UInt64.toNat seal_end) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => seal_end) (fun _ => floor))))
        (instDecidableUInt64Lt seal_end floor)
        (fun _ => Nat.le.refl (UInt64.toNat seal_end))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : RecoverUnitState) (hInit : Init s) :
        RecoverUnitStartInv s :=
      uint64_eq_le s.sealEnd s.unitStart hInit

    theorem next_preserves_inv (s sNext : RecoverUnitState)
        (_hInv : RecoverUnitStartInv s) (hNext : Next s sNext) :
        RecoverUnitStartInv sNext :=
      Exists.elim hNext (fun floor hAct =>
        let hAdv : Nat.le (UInt64.toNat s.unitStart) (UInt64.toNat (_root_.recover_unit_start_advance s.unitStart floor)) :=
          advance_ge_seal s.unitStart floor
        let hEqSeal : sNext.sealEnd = s.unitStart := hAct.1
        let hEqUnit : sNext.unitStart = _root_.recover_unit_start_advance s.unitStart floor := hAct.2
        Eq.mpr
          (congrArg (fun (p : UInt64) => Nat.le (UInt64.toNat p) (UInt64.toNat sNext.unitStart)) hEqSeal)
          (Eq.mpr
            (congrArg (fun (c : UInt64) => Nat.le (UInt64.toNat s.unitStart) (UInt64.toNat c)) hEqUnit)
            hAdv))

    theorem spec_satisfies_recover_unit_start_monotonicity :
        Spec ⊨ □ (Lift RecoverUnitStartInv) :=
      invariantSatisfies Spec RecoverUnitStartInv init_establishes_inv next_preserves_inv

    end TlaRecoveryClassifier
    end Broker
    end Astream

    def recover_keep_within_len_isl (keep : USize) (len : USize) : Bool :=
      decide (keep ≤ len)
}
