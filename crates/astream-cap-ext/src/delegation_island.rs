// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `delegation.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `delegation.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def delegation_hop_clamp (hops : UInt64) (max_hops : UInt64) : UInt64 :=
      if hops < max_hops then hops else max_hops

    def delegation_expiry_tighten (parent_exp : UInt64) (child_exp : UInt64) : UInt64 :=
      if child_exp < parent_exp then child_exp else parent_exp

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Subagent Delegation Spec
    -- =======================================================================

    namespace Astream
    namespace Cap
    namespace TlaSubagentDelegation

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

    structure DelegationState where
      hops : UInt64
      max_hops : UInt64
      eff_exp : UInt64
      parent_exp : UInt64

    def DelegationInv (s : DelegationState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.hops) (UInt64.toNat s.max_hops))
        (Nat.le (UInt64.toNat s.eff_exp) (UInt64.toNat s.parent_exp))

    def Init (s : DelegationState) : Prop :=
      And
        (s.hops = 0)
        (s.eff_exp = s.parent_exp)

    def delegateStep (raw_hops : UInt64) (child_exp : UInt64) (s : DelegationState) : DelegationState :=
      DelegationState.mk
        (_root_.delegation_hop_clamp raw_hops s.max_hops)
        s.max_hops
        (_root_.delegation_expiry_tighten s.eff_exp child_exp)
        s.eff_exp

    def Next (s : DelegationState) (s' : DelegationState) : Prop :=
      ∃ (raw_hops : UInt64), ∃ (child_exp : UInt64),
        s' = delegateStep raw_hops child_exp s

    def Spec : StateMachine DelegationState :=
      StateMachine.mk Init Next

    theorem hops_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.delegation_hop_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem exp_le_parent : forall (pexp : UInt64) (cexp : UInt64),
        Nat.le (UInt64.toNat (_root_.delegation_expiry_tighten pexp cexp)) (UInt64.toNat pexp) :=
      fun pexp cexp => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cexp pexp)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => pexp) (fun _ => cexp))) (UInt64.toNat pexp))
        (instDecidableUInt64Lt cexp pexp)
        (fun _ => Nat.le.refl (UInt64.toNat pexp))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : DelegationState) (hInit : Init s) :
      DelegationInv s :=
      And.intro
        (zero_le_cap s.hops s.max_hops (And.left hInit))
        (uint64_eq_le s.eff_exp s.parent_exp (And.right hInit))

    theorem next_preserves_inv (s : DelegationState) (s' : DelegationState)
      (_hInv : DelegationInv s) (hNext : Next s s') :
      DelegationInv s' :=
      Exists.elim hNext (fun (rh : UInt64) (hRest : ∃ (ce : UInt64), s' = delegateStep rh ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = delegateStep rh ce s) =>
          Eq.mpr
            (congrArg (fun (st : DelegationState) => DelegationInv st) hEq)
            (And.intro
              (hops_le_max rh s.max_hops)
              (exp_le_parent s.eff_exp ce))))

    theorem delegation_safety_always :
      Satisfies (Runs Spec) (Always (Lift DelegationInv)) :=
      invariantSatisfies Spec DelegationInv init_establishes_inv next_preserves_inv

    end TlaSubagentDelegation
    end Cap
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def delegation_within_hops_isl (hops : USize) (max_hops : USize) : Bool :=
      decide (hops ≤ max_hops)
}
