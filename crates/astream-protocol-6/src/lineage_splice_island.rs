// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `lineage_splice.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `lineage_splice.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def lineage_rewind_clamp (cand_dist : UInt64) (max_dist : UInt64) : UInt64 :=
      if cand_dist < max_dist then cand_dist else max_dist

    def lineage_gen_advance (cur_gen : UInt64) (cand_gen : UInt64) : UInt64 :=
      if cur_gen < cand_gen then cand_gen else cur_gen

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Lineage Splice Spec
    -- =======================================================================

    namespace Astream
    namespace Engine
    namespace TlaLineageSplicePlanner

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

    structure LineageSpliceState where
      rewind_dist : UInt64
      max_dist : UInt64
      witnessed_gen : UInt64
      prev_gen : UInt64

    def LineageSpliceInv (s : LineageSpliceState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.rewind_dist) (UInt64.toNat s.max_dist))
        (Nat.le (UInt64.toNat s.prev_gen) (UInt64.toNat s.witnessed_gen))

    def Init (max_dist : UInt64) (s : LineageSpliceState) : Prop :=
      And
        (And (s.rewind_dist = 0) (s.max_dist = max_dist))
        (And (s.witnessed_gen = 0) (s.prev_gen = 0))

    def spliceStep (cand_dist : UInt64) (cand_gen : UInt64) (s : LineageSpliceState) : LineageSpliceState :=
      LineageSpliceState.mk
        (_root_.lineage_rewind_clamp cand_dist s.max_dist)
        s.max_dist
        (_root_.lineage_gen_advance s.witnessed_gen cand_gen)
        s.witnessed_gen

    def Next (s : LineageSpliceState) (s' : LineageSpliceState) : Prop :=
      ∃ (cand_dist : UInt64), ∃ (cand_gen : UInt64),
        s' = spliceStep cand_dist cand_gen s

    def Spec (max_dist : UInt64) : StateMachine LineageSpliceState :=
      StateMachine.mk (Init max_dist) Next

    theorem rewind_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.lineage_rewind_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem gen_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.lineage_gen_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_dist : UInt64) (s : LineageSpliceState)
      (hInit : Init max_dist s) :
      LineageSpliceInv s :=
      And.intro
        (eq_zero_le s.rewind_dist s.max_dist (And.left (And.left hInit)))
        (eq_zero_le s.prev_gen s.witnessed_gen (And.right (And.right hInit)))

    theorem next_preserves_inv (s : LineageSpliceState) (s' : LineageSpliceState)
      (_hInv : LineageSpliceInv s) (hNext : Next s s') :
      LineageSpliceInv s' :=
      Exists.elim hNext (fun (cd : UInt64) (hRest : ∃ (cg : UInt64), s' = spliceStep cd cg s) =>
        Exists.elim hRest (fun (cg : UInt64) (hEq : s' = spliceStep cd cg s) =>
          Eq.mpr
            (congrArg (fun (st : LineageSpliceState) => LineageSpliceInv st) hEq)
            (And.intro
              (rewind_clamp_le cd s.max_dist)
              (gen_monotone s.witnessed_gen cg))))

    theorem lineage_splice_safety_always (max_dist : UInt64) :
      Satisfies (Runs (Spec max_dist)) (Always (Lift LineageSpliceInv)) :=
      invariantSatisfies (Spec max_dist) LineageSpliceInv (init_establishes_inv max_dist) next_preserves_inv

    end TlaLineageSplicePlanner
    end Engine
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def lineage_cursor_within_diverge_isl (cursor : UInt64) (diverge_offset : UInt64) : Bool :=
      decide (cursor <= diverge_offset)
}
