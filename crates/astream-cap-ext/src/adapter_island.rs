// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `adapter.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `adapter.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def task_lease_epoch_advance (cur_epoch : UInt64) (proposed_epoch : UInt64) : UInt64 :=
      if cur_epoch < proposed_epoch then proposed_epoch else cur_epoch

    def task_retry_clamp (attempts : UInt64) (max_attempts : UInt64) : UInt64 :=
      if attempts < max_attempts then attempts else max_attempts

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Task Adapter Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaTaskAdapter

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

    structure TaskAdapterState where
      prev_epoch : UInt64
      lease_epoch : UInt64
      attempts : UInt64
      max_attempts : UInt64

    def TaskAdapterSafetyInv (s : TaskAdapterState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.lease_epoch))
        (Nat.le (UInt64.toNat s.attempts) (UInt64.toNat s.max_attempts))

    def Init (s : TaskAdapterState) : Prop :=
      And
        (s.prev_epoch = s.lease_epoch)
        (Nat.le (UInt64.toNat s.attempts) (UInt64.toNat s.max_attempts))

    def leaseStep (proposed_epoch : UInt64) (raw_attempts : UInt64) (s : TaskAdapterState) : TaskAdapterState :=
      TaskAdapterState.mk
        s.lease_epoch
        (_root_.task_lease_epoch_advance s.lease_epoch proposed_epoch)
        (_root_.task_retry_clamp raw_attempts s.max_attempts)
        s.max_attempts

    def Next (s : TaskAdapterState) (s' : TaskAdapterState) : Prop :=
      ∃ (proposed_epoch : UInt64), ∃ (raw_attempts : UInt64),
        s' = leaseStep proposed_epoch raw_attempts s

    def Spec : StateMachine TaskAdapterState :=
      StateMachine.mk Init Next

    theorem epoch_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.task_lease_epoch_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem retry_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.task_retry_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : TaskAdapterState) (hInit : Init s) :
      TaskAdapterSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_epoch s.lease_epoch (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : TaskAdapterState) (s' : TaskAdapterState)
      (_hInv : TaskAdapterSafetyInv s) (hNext : Next s s') :
      TaskAdapterSafetyInv s' :=
      Exists.elim hNext (fun (proposed_epoch : UInt64) (hRest : ∃ (raw_attempts : UInt64), s' = leaseStep proposed_epoch raw_attempts s) =>
        Exists.elim hRest (fun (raw_attempts : UInt64) (hEq : s' = leaseStep proposed_epoch raw_attempts s) =>
          Eq.mpr
            (congrArg (fun (st : TaskAdapterState) => TaskAdapterSafetyInv st) hEq)
            (And.intro
              (epoch_ge_prev s.lease_epoch proposed_epoch)
              (retry_le_max raw_attempts s.max_attempts))))

    theorem task_adapter_safety_always :
      Satisfies (Runs Spec) (Always (Lift TaskAdapterSafetyInv)) :=
      invariantSatisfies Spec TaskAdapterSafetyInv init_establishes_inv next_preserves_inv

    end TlaTaskAdapter
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def task_lease_matches_epoch_isl (req_epoch : UInt64) (cur_epoch : UInt64) : Bool :=
      decide (req_epoch = cur_epoch)
}
