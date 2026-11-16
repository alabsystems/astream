// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `bus_cut.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `bus_cut.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def bus_cut_frontier_advance (cur_off : UInt64) (proposed_off : UInt64) : UInt64 :=
      if cur_off < proposed_off then proposed_off else cur_off

    def bus_cut_edges_clamp (edge_count : UInt64) (max_edges : UInt64) : UInt64 :=
      if edge_count < max_edges then edge_count else max_edges

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Bus Causal Cut Spec
    -- =======================================================================

    namespace Astream
    namespace Engine
    namespace TlaBusCausalCut

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

    structure BusCutState where
      prev_frontier : UInt64
      frontier : UInt64
      edges : UInt64
      max_edges : UInt64

    def BusCutInv (s : BusCutState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_frontier) (UInt64.toNat s.frontier))
        (Nat.le (UInt64.toNat s.edges) (UInt64.toNat s.max_edges))

    def Init (s : BusCutState) : Prop :=
      And
        (s.prev_frontier = s.frontier)
        (Nat.le (UInt64.toNat s.edges) (UInt64.toNat s.max_edges))

    def ingestRecordStep (proposed_frontier : UInt64) (raw_edges : UInt64) (s : BusCutState) : BusCutState :=
      BusCutState.mk
        s.frontier
        (_root_.bus_cut_frontier_advance s.frontier proposed_frontier)
        (_root_.bus_cut_edges_clamp raw_edges s.max_edges)
        s.max_edges

    def Next (s : BusCutState) (s' : BusCutState) : Prop :=
      ∃ (proposed_frontier : UInt64), ∃ (raw_edges : UInt64),
        s' = ingestRecordStep proposed_frontier raw_edges s

    def Spec : StateMachine BusCutState :=
      StateMachine.mk Init Next

    theorem frontier_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.bus_cut_frontier_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem edges_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.bus_cut_edges_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : BusCutState) (hInit : Init s) :
      BusCutInv s :=
      And.intro
        (uint64_eq_le s.prev_frontier s.frontier (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : BusCutState) (s' : BusCutState)
      (_hInv : BusCutInv s) (hNext : Next s s') :
      BusCutInv s' :=
      Exists.elim hNext (fun (pf : UInt64) (hRest : ∃ (re : UInt64), s' = ingestRecordStep pf re s) =>
        Exists.elim hRest (fun (re : UInt64) (hEq : s' = ingestRecordStep pf re s) =>
          Eq.mpr
            (congrArg (fun (st : BusCutState) => BusCutInv st) hEq)
            (And.intro
              (frontier_ge_prev s.frontier pf)
              (edges_le_max re s.max_edges))))

    theorem bus_cut_safety_always :
      Satisfies (Runs Spec) (Always (Lift BusCutInv)) :=
      invariantSatisfies Spec BusCutInv init_establishes_inv next_preserves_inv

    end TlaBusCausalCut
    end Engine
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def bus_cut_admits_isl (off : UInt64) (cut_off : UInt64) : Bool :=
      decide (off ≤ cut_off)
}
