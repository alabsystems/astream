// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `land_readiness.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `land_readiness.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def land_debt_clamp (raw_debt : UInt64) (debt_cap : UInt64) : UInt64 :=
      if raw_debt < debt_cap then raw_debt else debt_cap

    def land_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Land Readiness Gate Spec
    -- =======================================================================

    namespace Astream
    namespace Evidence
    namespace TlaLandReadinessGate

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

    structure LandReadinessState where
      bounded_debt : UInt64
      debt_cap : UInt64
      verified_epoch : UInt64
      prev_epoch : UInt64

    def LandReadinessInv (s : LandReadinessState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.bounded_debt) (UInt64.toNat s.debt_cap))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.verified_epoch))

    def Init (debt_cap : UInt64) (s : LandReadinessState) : Prop :=
      And
        (And (s.bounded_debt = 0) (s.debt_cap = debt_cap))
        (And (s.verified_epoch = 0) (s.prev_epoch = 0))

    def evaluateStep (cand_debt : UInt64) (cand_epoch : UInt64) (s : LandReadinessState) : LandReadinessState :=
      LandReadinessState.mk
        (_root_.land_debt_clamp cand_debt s.debt_cap)
        s.debt_cap
        (_root_.land_epoch_advance s.verified_epoch cand_epoch)
        s.verified_epoch

    def Next (s : LandReadinessState) (s' : LandReadinessState) : Prop :=
      ∃ (cand_debt : UInt64), ∃ (cand_epoch : UInt64),
        s' = evaluateStep cand_debt cand_epoch s

    def Spec (debt_cap : UInt64) : StateMachine LandReadinessState :=
      StateMachine.mk (Init debt_cap) Next

    theorem debt_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.land_debt_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.land_epoch_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (debt_cap : UInt64) (s : LandReadinessState)
      (hInit : Init debt_cap s) :
      LandReadinessInv s :=
      And.intro
        (eq_zero_le s.bounded_debt s.debt_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_epoch s.verified_epoch (And.right (And.right hInit)))

    theorem next_preserves_inv (s : LandReadinessState) (s' : LandReadinessState)
      (_hInv : LandReadinessInv s) (hNext : Next s s') :
      LandReadinessInv s' :=
      Exists.elim hNext (fun (cd : UInt64) (hRest : ∃ (ce : UInt64), s' = evaluateStep cd ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = evaluateStep cd ce s) =>
          Eq.mpr
            (congrArg (fun (st : LandReadinessState) => LandReadinessInv st) hEq)
            (And.intro
              (debt_clamp_le cd s.debt_cap)
              (epoch_monotone s.verified_epoch ce))))

    theorem land_readiness_safety_always (debt_cap : UInt64) :
      Satisfies (Runs (Spec debt_cap)) (Always (Lift LandReadinessInv)) :=
      invariantSatisfies (Spec debt_cap) LandReadinessInv (init_establishes_inv debt_cap) next_preserves_inv

    end TlaLandReadinessGate
    end Evidence
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def land_debt_is_zero_isl (total_debt : UInt64) : Bool :=
      decide (total_debt = 0)
}
