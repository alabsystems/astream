// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `causal_barrier.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `causal_barrier.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def vclock_entries_clamp (cand_entries : UInt64) (max_entries : UInt64) : UInt64 :=
      if cand_entries < max_entries then cand_entries else max_entries

    def vclock_offset_advance (cur_off : UInt64) (cand_off : UInt64) : UInt64 :=
      if cur_off < cand_off then cand_off else cur_off

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Causal Vector Clock Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaCausalVectorClock

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

    structure VectorClockState where
      entry_count : UInt64
      max_entries : UInt64
      shard_hw : UInt64
      prev_hw : UInt64

    def CausalVectorClockInv (s : VectorClockState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.entry_count) (UInt64.toNat s.max_entries))
        (Nat.le (UInt64.toNat s.prev_hw) (UInt64.toNat s.shard_hw))

    def Init (max_entries : UInt64) (s : VectorClockState) : Prop :=
      And
        (And (s.entry_count = 0) (s.max_entries = max_entries))
        (And (s.shard_hw = 0) (s.prev_hw = 0))

    def witnessStep (cand_entries : UInt64) (cand_off : UInt64) (s : VectorClockState) : VectorClockState :=
      VectorClockState.mk
        (_root_.vclock_entries_clamp cand_entries s.max_entries)
        s.max_entries
        (_root_.vclock_offset_advance s.shard_hw cand_off)
        s.shard_hw

    def Next (s : VectorClockState) (s' : VectorClockState) : Prop :=
      ∃ (cand_entries : UInt64), ∃ (cand_off : UInt64),
        s' = witnessStep cand_entries cand_off s

    def Spec (max_entries : UInt64) : StateMachine VectorClockState :=
      StateMachine.mk (Init max_entries) Next

    theorem entries_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.vclock_entries_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem offset_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.vclock_offset_advance cur cand)) :=
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

    theorem init_establishes_inv (max_entries : UInt64) (s : VectorClockState)
      (hInit : Init max_entries s) :
      CausalVectorClockInv s :=
      And.intro
        (eq_zero_le s.entry_count s.max_entries (And.left (And.left hInit)))
        (eq_zero_le s.prev_hw s.shard_hw (And.right (And.right hInit)))

    theorem next_preserves_inv (s : VectorClockState) (s' : VectorClockState)
      (_hInv : CausalVectorClockInv s) (hNext : Next s s') :
      CausalVectorClockInv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (co : UInt64), s' = witnessStep ce co s) =>
        Exists.elim hRest (fun (co : UInt64) (hEq : s' = witnessStep ce co s) =>
          Eq.mpr
            (congrArg (fun (st : VectorClockState) => CausalVectorClockInv st) hEq)
            (And.intro
              (entries_clamp_le ce s.max_entries)
              (offset_monotone s.shard_hw co))))

    theorem causal_vector_clock_safety_always (max_entries : UInt64) :
      Satisfies (Runs (Spec max_entries)) (Always (Lift CausalVectorClockInv)) :=
      invariantSatisfies (Spec max_entries) CausalVectorClockInv (init_establishes_inv max_entries) next_preserves_inv

    end TlaCausalVectorClock
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def vclock_entries_within_cap_isl (count : UInt64) (max_entries : UInt64) : Bool :=
      decide (count <= max_entries)
}
