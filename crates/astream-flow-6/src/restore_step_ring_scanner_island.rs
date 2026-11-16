// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `aterm-restore` crash-restore step-ring zero-gap classification
// (`Astream.Wire.TlaRestoreStepRingScanner`, Island #277), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def restore_ring_valid_clamp (valid_len : UInt64) (ring_cap : UInt64) : UInt64 :=
      if valid_len < ring_cap then valid_len else ring_cap

    def restore_resync_budget_advance (floor_budget : UInt64) (scaled_budget : UInt64) : UInt64 :=
      if floor_budget < scaled_budget then scaled_budget else floor_budget

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Step-Ring Scanner Spec
    -- =======================================================================

    namespace Astream
    namespace Wire
    namespace TlaRestoreStepRingScanner

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop
    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun (k : Nat) => b (Nat.add n k)
    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (n : Nat), P (drop n b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (n : Nat), M.Next (b n) (b (Nat.add n 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (P : Formula State) (Q : Formula State) : Prop :=
      ∀ (b : Behavior State), P b → Q b

    theorem invariantAt
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s')
      (b : Behavior State)
      (hRun : Runs M b)
      (k : Nat) :
      Inv (b k) :=
      Nat.rec
        (hInit (b 0) (And.left hRun))
        (fun (j : Nat) (ih : Inv (b j)) =>
          hStep (b j) (b (Nat.add j 1)) ih (And.right hRun j))
        k

    theorem invariantSatisfies
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s') :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure RingScanState where
      valid_len : UInt64
      ring_cap : UInt64
      floor_budget : UInt64
      budget : UInt64

    def RingScanSafetyInv (s : RingScanState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.valid_len) (UInt64.toNat s.ring_cap))
        (Nat.le (UInt64.toNat s.floor_budget) (UInt64.toNat s.budget))

    def Init (s : RingScanState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.valid_len) (UInt64.toNat s.ring_cap))
        (s.floor_budget = s.budget)

    def scanStep (raw_valid : UInt64) (scaled_budget : UInt64) (s : RingScanState) : RingScanState :=
      RingScanState.mk
        (_root_.restore_ring_valid_clamp raw_valid s.ring_cap)
        s.ring_cap
        s.floor_budget
        (_root_.restore_resync_budget_advance s.floor_budget scaled_budget)

    def Next (s : RingScanState) (s' : RingScanState) : Prop :=
      ∃ (raw_valid : UInt64), ∃ (scaled_budget : UInt64),
        s' = scanStep raw_valid scaled_budget s

    def Spec : StateMachine RingScanState :=
      StateMachine.mk Init Next

    theorem valid_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.restore_ring_valid_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem budget_ge_floor : forall (flr : UInt64) (scaled : UInt64),
        Nat.le (UInt64.toNat flr) (UInt64.toNat (_root_.restore_resync_budget_advance flr scaled)) :=
      fun flr scaled => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt flr scaled)) =>
          Nat.le (UInt64.toNat flr) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => flr) (fun _ => scaled))))
        (instDecidableUInt64Lt flr scaled)
        (fun _ => @Nat.le.refl (UInt64.toNat flr))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : RingScanState) (hInit : Init s) :
      RingScanSafetyInv s :=
      And.intro
        (And.left hInit)
        (uint64_eq_le s.floor_budget s.budget (And.right hInit))

    theorem next_preserves_inv (s : RingScanState) (s' : RingScanState)
      (_hInv : RingScanSafetyInv s) (hNext : Next s s') :
      RingScanSafetyInv s' :=
      Exists.elim hNext (fun (rv : UInt64) (hRest : ∃ (sb : UInt64), s' = scanStep rv sb s) =>
        Exists.elim hRest (fun (sb : UInt64) (hEq : s' = scanStep rv sb s) =>
          Eq.mpr
            (congrArg (fun (st : RingScanState) => RingScanSafetyInv st) hEq)
            (And.intro
              (valid_le_cap rv s.ring_cap)
              (budget_ge_floor s.floor_budget sb))))

    theorem ring_scan_safety_always :
      Satisfies (Runs Spec) (Always (Lift RingScanSafetyInv)) :=
      invariantSatisfies Spec RingScanSafetyInv init_establishes_inv next_preserves_inv

    end TlaRestoreStepRingScanner
    end Wire
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def restore_gap_within_ring_isl (valid_len : UInt64) (ring_cap : UInt64) : Bool :=
      decide (valid_len ≤ ring_cap)
}
