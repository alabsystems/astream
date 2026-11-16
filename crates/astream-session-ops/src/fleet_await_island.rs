// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `fleet_await.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `fleet_await.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def await_rev_advance (prev_rev : UInt64) (cand_rev : UInt64) : UInt64 :=
      if prev_rev < cand_rev then cand_rev else prev_rev

    def await_targets_clamp (targets : UInt64) (max_targets : UInt64) : UInt64 :=
      if targets < max_targets then targets else max_targets

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Fleet Task Await Spec
    -- =======================================================================

    namespace Astream
    namespace Engine
    namespace TlaFleetAwait

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

    structure FleetAwaitState where
      cur_rev : UInt64
      prev_rev : UInt64
      watched_targets : UInt64
      max_targets : UInt64

    def FleetAwaitInv (s : FleetAwaitState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_rev) (UInt64.toNat s.cur_rev))
        (Nat.le (UInt64.toNat s.watched_targets) (UInt64.toNat s.max_targets))

    def Init (s : FleetAwaitState) : Prop :=
      And
        (s.watched_targets = 0)
        (And (s.cur_rev = 0) (s.prev_rev = 0))

    def awaitStep (cand_rev : UInt64) (raw_targets : UInt64) (s : FleetAwaitState) : FleetAwaitState :=
      FleetAwaitState.mk
        (_root_.await_rev_advance s.cur_rev cand_rev)
        s.cur_rev
        (_root_.await_targets_clamp raw_targets s.max_targets)
        s.max_targets

    def Next (s : FleetAwaitState) (s' : FleetAwaitState) : Prop :=
      ∃ (cand_rev : UInt64), ∃ (raw_targets : UInt64),
        s' = awaitStep cand_rev raw_targets s

    def Spec : StateMachine FleetAwaitState :=
      StateMachine.mk Init Next

    theorem rev_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.await_rev_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem targets_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.await_targets_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : FleetAwaitState) (hInit : Init s) :
      FleetAwaitInv s :=
      And.intro
        (eq_zero_le
          s.prev_rev
          s.cur_rev
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.watched_targets s.max_targets (And.left hInit))

    theorem next_preserves_inv (s : FleetAwaitState) (s' : FleetAwaitState)
      (_hInv : FleetAwaitInv s) (hNext : Next s s') :
      FleetAwaitInv s' :=
      Exists.elim hNext (fun (cr : UInt64) (hRest : ∃ (rt : UInt64), s' = awaitStep cr rt s) =>
        Exists.elim hRest (fun (rt : UInt64) (hEq : s' = awaitStep cr rt s) =>
          Eq.mpr
            (congrArg (fun (st : FleetAwaitState) => FleetAwaitInv st) hEq)
            (And.intro
              (rev_monotone s.cur_rev cr)
              (targets_le_max rt s.max_targets))))

    theorem fleet_await_safety_always :
      Satisfies (Runs Spec) (Always (Lift FleetAwaitInv)) :=
      invariantSatisfies Spec FleetAwaitInv init_establishes_inv next_preserves_inv

    end TlaFleetAwait
    end Engine
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def await_rev_fresh_isl (since_rev : UInt64) (cur_rev : UInt64) : Bool :=
      decide (since_rev < cur_rev)
}
