// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `cap_attenuation_chain.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `cap_attenuation_chain.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def attenuation_exp_clamp (child_exp_ms : UInt64) (parent_exp_ms : UInt64) : UInt64 :=
      if child_exp_ms < parent_exp_ms then child_exp_ms else parent_exp_ms

    def delegation_depth_advance (cur_depth : UInt64) (cand_depth : UInt64) : UInt64 :=
      if cur_depth < cand_depth then cand_depth else cur_depth

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Cap Attenuation Spec
    -- =======================================================================

    namespace Astream
    namespace Cap
    namespace TlaCapAttenuationChain

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

    structure AttenuationState where
      effective_exp_ms : UInt64
      root_exp_ms : UInt64
      depth : UInt64
      prev_depth : UInt64

    def AttenuationInv (s : AttenuationState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.effective_exp_ms) (UInt64.toNat s.root_exp_ms))
        (Nat.le (UInt64.toNat s.prev_depth) (UInt64.toNat s.depth))

    def Init (root_exp_ms : UInt64) (s : AttenuationState) : Prop :=
      And
        (And (s.effective_exp_ms = root_exp_ms) (s.root_exp_ms = root_exp_ms))
        (And (s.depth = 0) (s.prev_depth = 0))

    def attenuateStep (cand_exp : UInt64) (cand_depth : UInt64) (s : AttenuationState) : AttenuationState :=
      AttenuationState.mk
        (_root_.attenuation_exp_clamp cand_exp s.effective_exp_ms)
        s.root_exp_ms
        (_root_.delegation_depth_advance s.depth cand_depth)
        s.depth

    def Next (s : AttenuationState) (s' : AttenuationState) : Prop :=
      ∃ (cand_exp : UInt64), ∃ (cand_depth : UInt64),
        s' = attenuateStep cand_exp cand_depth s

    def Spec (root_exp_ms : UInt64) : StateMachine AttenuationState :=
      StateMachine.mk (Init root_exp_ms) Next

    theorem exp_clamp_le : forall (cand : UInt64) (cur : UInt64),
        Nat.le (UInt64.toNat (_root_.attenuation_exp_clamp cand cur)) (UInt64.toNat cur) :=
      fun cand cur => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cur)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))) (UInt64.toNat cur))
        (instDecidableUInt64Lt cand cur)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem depth_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.delegation_depth_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_le_refl (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (root_exp_ms : UInt64) (s : AttenuationState)
      (hInit : Init root_exp_ms s) :
      AttenuationInv s :=
      And.intro
        (eq_le_refl s.effective_exp_ms s.root_exp_ms
          (Eq.trans (And.left (And.left hInit)) (Eq.symm (And.right (And.left hInit)))))
        (eq_le_refl s.prev_depth s.depth
          (Eq.trans (And.right (And.right hInit)) (Eq.symm (And.left (And.right hInit)))))

    theorem next_preserves_inv (s : AttenuationState) (s' : AttenuationState)
      (hInv : AttenuationInv s) (hNext : Next s s') :
      AttenuationInv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (cd : UInt64), s' = attenuateStep ce cd s) =>
        Exists.elim hRest (fun (cd : UInt64) (hEq : s' = attenuateStep ce cd s) =>
          Eq.mpr
            (congrArg (fun (st : AttenuationState) => AttenuationInv st) hEq)
            (And.intro
              (Nat.le_trans (exp_clamp_le ce s.effective_exp_ms) (And.left hInv))
              (depth_monotone s.depth cd))))

    theorem cap_attenuation_safety_always (root_exp_ms : UInt64) :
      Satisfies (Runs (Spec root_exp_ms)) (Always (Lift AttenuationInv)) :=
      invariantSatisfies (Spec root_exp_ms) AttenuationInv (init_establishes_inv root_exp_ms) next_preserves_inv

    end TlaCapAttenuationChain
    end Cap
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def attenuated_exp_within_parent_isl (child_exp : UInt64) (parent_exp : UInt64) : Bool :=
      decide (child_exp <= parent_exp)
}
