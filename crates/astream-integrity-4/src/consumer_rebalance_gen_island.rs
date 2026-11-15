// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `consumer_rebalance_gen.rs`, out of line so that only a Trust compiler
// opens it: no stock rustc can lex `clean { ... }`. `consumer_rebalance_gen.rs` mounts this file
// under `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def rebalance_assigned_clamp (cand_assigned : UInt64) (total_partitions : UInt64) : UInt64 :=
      if cand_assigned < total_partitions then cand_assigned else total_partitions

    def rebalance_gen_advance (cur_gen : UInt64) (cand_gen : UInt64) : UInt64 :=
      if cur_gen < cand_gen then cand_gen else cur_gen

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Cooperative Rebalance Spec
    -- =======================================================================

    namespace Astream
    namespace Kafka
    namespace TlaCooperativeRebalance

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

    structure RebalanceState where
      assigned_partitions : UInt64
      total_partitions : UInt64
      generation_id : UInt64
      prev_generation : UInt64

    def RebalanceInv (s : RebalanceState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.assigned_partitions) (UInt64.toNat s.total_partitions))
        (Nat.le (UInt64.toNat s.prev_generation) (UInt64.toNat s.generation_id))

    def Init (total_partitions : UInt64) (s : RebalanceState) : Prop :=
      And
        (And (s.assigned_partitions = 0) (s.total_partitions = total_partitions))
        (And (s.generation_id = 0) (s.prev_generation = 0))

    def rebalanceStep (cand_assigned : UInt64) (cand_gen : UInt64) (s : RebalanceState) : RebalanceState :=
      RebalanceState.mk
        (_root_.rebalance_assigned_clamp cand_assigned s.total_partitions)
        s.total_partitions
        (_root_.rebalance_gen_advance s.generation_id cand_gen)
        s.generation_id

    def Next (s : RebalanceState) (s' : RebalanceState) : Prop :=
      ∃ (cand_assigned : UInt64), ∃ (cand_gen : UInt64),
        s' = rebalanceStep cand_assigned cand_gen s

    def Spec (total_partitions : UInt64) : StateMachine RebalanceState :=
      StateMachine.mk (Init total_partitions) Next

    theorem assigned_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.rebalance_assigned_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem gen_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.rebalance_gen_advance cur cand)) :=
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

    theorem init_establishes_inv (total_partitions : UInt64) (s : RebalanceState)
      (hInit : Init total_partitions s) :
      RebalanceInv s :=
      And.intro
        (eq_zero_le s.assigned_partitions s.total_partitions (And.left (And.left hInit)))
        (eq_zero_le s.prev_generation s.generation_id (And.right (And.right hInit)))

    theorem next_preserves_inv (s : RebalanceState) (s' : RebalanceState)
      (_hInv : RebalanceInv s) (hNext : Next s s') :
      RebalanceInv s' :=
      Exists.elim hNext (fun (ca : UInt64) (hRest : ∃ (cg : UInt64), s' = rebalanceStep ca cg s) =>
        Exists.elim hRest (fun (cg : UInt64) (hEq : s' = rebalanceStep ca cg s) =>
          Eq.mpr
            (congrArg (fun (st : RebalanceState) => RebalanceInv st) hEq)
            (And.intro
              (assigned_clamp_le ca s.total_partitions)
              (gen_monotone s.generation_id cg))))

    theorem cooperative_rebalance_safety_always (total_partitions : UInt64) :
      Satisfies (Runs (Spec total_partitions)) (Always (Lift RebalanceInv)) :=
      invariantSatisfies (Spec total_partitions) RebalanceInv (init_establishes_inv total_partitions) next_preserves_inv

    end TlaCooperativeRebalance
    end Kafka
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def rebalance_assigned_within_total_isl (assigned : UInt64) (total : UInt64) : Bool :=
      decide (assigned <= total)
}
