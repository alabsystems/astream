// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `atpkg-abrew` native prefix isolation and `--real`/`ABREW_REAL`
// bypass refusal (`Astream.Host.TlaAbrewBottleIsolationGuard`, Island #281).
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def abrew_cask_kind_clamp (kind_code : UInt64) (max_kind : UInt64) : UInt64 :=
      if kind_code < max_kind then kind_code else max_kind

    def abrew_refusal_count_advance (prev : UInt64) (next : UInt64) : UInt64 :=
      if prev < next then next else prev

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Abrew Isolation Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaAbrewBottleIsolationGuard

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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next)
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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next) :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure AbrewState where
      cask_kind : UInt64
      max_kind : UInt64
      prev_refusals : UInt64
      refusals : UInt64

    def AbrewSafetyInv (s : AbrewState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.cask_kind) (UInt64.toNat s.max_kind))
        (Nat.le (UInt64.toNat s.prev_refusals) (UInt64.toNat s.refusals))

    def Init (s : AbrewState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.cask_kind) (UInt64.toNat s.max_kind))
        (s.prev_refusals = s.refusals)

    def evalCmdStep (raw_kind : UInt64) (cand_refusals : UInt64) (s : AbrewState) : AbrewState :=
      AbrewState.mk
        (_root_.abrew_cask_kind_clamp raw_kind s.max_kind)
        s.max_kind
        s.refusals
        (_root_.abrew_refusal_count_advance s.refusals cand_refusals)

    def Next (s : AbrewState) (s_next : AbrewState) : Prop :=
      ∃ (raw_kind : UInt64), ∃ (cand_refusals : UInt64),
        s_next = evalCmdStep raw_kind cand_refusals s

    def Spec : StateMachine AbrewState :=
      StateMachine.mk Init Next

    theorem kind_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.abrew_cask_kind_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem refusals_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.abrew_refusal_count_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : AbrewState) (hInit : Init s) :
      AbrewSafetyInv s :=
      And.intro
        (And.left hInit)
        (uint64_eq_le s.prev_refusals s.refusals (And.right hInit))

    theorem next_preserves_inv (s : AbrewState) (s_next : AbrewState)
      (_hInv : AbrewSafetyInv s) (hNext : Next s s_next) :
      AbrewSafetyInv s_next :=
      Exists.elim hNext (fun (rk : UInt64) (hRest : ∃ (cr : UInt64), s_next = evalCmdStep rk cr s) =>
        Exists.elim hRest (fun (cr : UInt64) (hEq : s_next = evalCmdStep rk cr s) =>
          Eq.mpr
            (congrArg (fun (st : AbrewState) => AbrewSafetyInv st) hEq)
            (And.intro
              (kind_le_max rk s.max_kind)
              (refusals_ge_prev s.refusals cr))))

    theorem abrew_isolation_safety_always :
      Satisfies (Runs Spec) (Always (Lift AbrewSafetyInv)) :=
      invariantSatisfies Spec AbrewSafetyInv init_establishes_inv next_preserves_inv

    end TlaAbrewBottleIsolationGuard
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def abrew_no_bypass_requested_isl (bypass_flags : UInt64) : Bool :=
      decide (bypass_flags = (0 : UInt64))
}
