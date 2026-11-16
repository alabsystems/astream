// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for Trust toolchain lane selection & stale-link repair bounding
// (`Astream.Host.TlaTrustLaneSelector`), mounted under `cfg(clean_islands)` in
// `trust_lane_selector.rs`. Proves that bare `targo <cmd>` without an explicit lane is
// never allowed (`bareAllowed = 0`) and `repairAttempts <= maxRepairs`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def trust_repair_clamp (attempts : UInt64) (max_repairs : UInt64) : UInt64 :=
      if attempts < max_repairs then attempts else max_repairs

    def trust_zero_bare (_flag : UInt64) : UInt64 :=
      (0 : UInt64)

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel
    -- ========================================================================
    namespace Astream
    namespace Host
    namespace TlaTrustLaneSelector

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Host.TlaTrustLaneSelector.Satisfies M F
    prefix:75 "□" => _root_.Astream.Host.TlaTrustLaneSelector.Always

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
    -- 3. Trust Toolchain Lane & Repair-Bound State Machine
    -- ========================================================================

    structure SelectorState where
      bareAllowed    : UInt64
      repairAttempts : UInt64
      maxRepairs     : UInt64

    def LaneExplicitnessInv (s : SelectorState) : Prop :=
      s.bareAllowed = (0 : UInt64) ∧
      Nat.le (UInt64.toNat s.repairAttempts) (UInt64.toNat s.maxRepairs)

    def Init (maxRepairs : UInt64) (s : SelectorState) : Prop :=
      s.bareAllowed = (0 : UInt64) ∧
      s.repairAttempts = (0 : UInt64) ∧
      s.maxRepairs = maxRepairs

    def SelectOrRepair (rawAttempts : UInt64) (s sNext : SelectorState) : Prop :=
      sNext.bareAllowed = _root_.trust_zero_bare rawAttempts ∧
      sNext.repairAttempts = _root_.trust_repair_clamp rawAttempts s.maxRepairs ∧
      sNext.maxRepairs = s.maxRepairs

    def Next (s sNext : SelectorState) : Prop :=
      ∃ ra : UInt64, SelectOrRepair ra s sNext

    def Spec (maxRepairs : UInt64) : StateMachine SelectorState :=
      StateMachine.mk (Init maxRepairs) Next

    theorem repair_clamp_le : forall (a : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.trust_repair_clamp a cap)) (UInt64.toNat cap) :=
      fun a cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt a cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => a))) (UInt64.toNat cap))
        (instDecidableUInt64Lt a cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxRepairs : UInt64) (s : SelectorState)
        (hInit : Init maxRepairs s) : LaneExplicitnessInv s :=
      And.intro hInit.1 (zero_u64_le s.repairAttempts s.maxRepairs hInit.2.1)

    theorem select_preserves_inv (ra : UInt64) (s sNext : SelectorState)
        (hAct : SelectOrRepair ra s sNext) : LaneExplicitnessInv sNext :=
      let hB : sNext.bareAllowed = (0 : UInt64) := hAct.1
      let hR1 : Nat.le (UInt64.toNat sNext.repairAttempts) (UInt64.toNat s.maxRepairs) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRepairs)) hAct.2.1)
          (repair_clamp_le ra s.maxRepairs)
      let hR2 : Nat.le (UInt64.toNat sNext.repairAttempts) (UInt64.toNat sNext.maxRepairs) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.repairAttempts) (UInt64.toNat y)) hAct.2.2)
          hR1
      And.intro hB hR2

    theorem next_preserves_inv (s sNext : SelectorState)
        (_hInv : LaneExplicitnessInv s) (hNext : Next s sNext) :
        LaneExplicitnessInv sNext :=
      Exists.elim hNext (fun ra hAct => select_preserves_inv ra s sNext hAct)

    theorem spec_satisfies_lane_explicitness (maxRepairs : UInt64) :
        (Spec maxRepairs) ⊨ □ (Lift LaneExplicitnessInv) :=
      invariantSatisfies (Spec maxRepairs) LaneExplicitnessInv
        (init_establishes_inv maxRepairs)
        next_preserves_inv

    end TlaTrustLaneSelector
    end Host
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def trust_repair_budget_remains_isl (attempts : UInt64) (max_repairs : UInt64) : Bool :=
      decide (attempts < max_repairs)
}
