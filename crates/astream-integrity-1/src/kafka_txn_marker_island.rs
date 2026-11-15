// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `kafka_txn_marker.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `kafka_txn_marker.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def txn_active_clamp (cand_active : UInt64) (max_txns : UInt64) : UInt64 :=
      if cand_active < max_txns then cand_active else max_txns

    def txn_pid_advance (cur_pid : UInt64) (cand_pid : UInt64) : UInt64 :=
      if cur_pid < cand_pid then cand_pid else cur_pid

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Kafka Txn Coordinator Spec
    -- =======================================================================

    namespace Astream
    namespace Kafka
    namespace TlaKafkaTxnCoordinator

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

    structure KafkaTxnState where
      active_txns : UInt64
      max_txns : UInt64
      next_pid : UInt64
      prev_pid : UInt64

    def KafkaTxnCoordinatorInv (s : KafkaTxnState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.active_txns) (UInt64.toNat s.max_txns))
        (Nat.le (UInt64.toNat s.prev_pid) (UInt64.toNat s.next_pid))

    def Init (max_txns : UInt64) (s : KafkaTxnState) : Prop :=
      And
        (And (s.active_txns = 0) (s.max_txns = max_txns))
        (And (s.next_pid = 0) (s.prev_pid = 0))

    def txnStep (cand_active : UInt64) (cand_pid : UInt64) (s : KafkaTxnState) : KafkaTxnState :=
      KafkaTxnState.mk
        (_root_.txn_active_clamp cand_active s.max_txns)
        s.max_txns
        (_root_.txn_pid_advance s.next_pid cand_pid)
        s.next_pid

    def Next (s : KafkaTxnState) (s' : KafkaTxnState) : Prop :=
      ∃ (cand_active : UInt64), ∃ (cand_pid : UInt64),
        s' = txnStep cand_active cand_pid s

    def Spec (max_txns : UInt64) : StateMachine KafkaTxnState :=
      StateMachine.mk (Init max_txns) Next

    theorem active_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.txn_active_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem pid_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.txn_pid_advance cur cand)) :=
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

    theorem init_establishes_inv (max_txns : UInt64) (s : KafkaTxnState)
      (hInit : Init max_txns s) :
      KafkaTxnCoordinatorInv s :=
      And.intro
        (eq_zero_le s.active_txns s.max_txns (And.left (And.left hInit)))
        (eq_zero_le s.prev_pid s.next_pid (And.right (And.right hInit)))

    theorem next_preserves_inv (s : KafkaTxnState) (s' : KafkaTxnState)
      (_hInv : KafkaTxnCoordinatorInv s) (hNext : Next s s') :
      KafkaTxnCoordinatorInv s' :=
      Exists.elim hNext (fun (ca : UInt64) (hRest : ∃ (cp : UInt64), s' = txnStep ca cp s) =>
        Exists.elim hRest (fun (cp : UInt64) (hEq : s' = txnStep ca cp s) =>
          Eq.mpr
            (congrArg (fun (st : KafkaTxnState) => KafkaTxnCoordinatorInv st) hEq)
            (And.intro
              (active_clamp_le ca s.max_txns)
              (pid_monotone s.next_pid cp))))

    theorem kafka_txn_coordinator_safety_always (max_txns : UInt64) :
      Satisfies (Runs (Spec max_txns)) (Always (Lift KafkaTxnCoordinatorInv)) :=
      invariantSatisfies (Spec max_txns) KafkaTxnCoordinatorInv (init_establishes_inv max_txns) next_preserves_inv

    end TlaKafkaTxnCoordinator
    end Kafka
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def txn_active_within_cap_isl (active : UInt64) (max_txns : UInt64) : Bool :=
      decide (active <= max_txns)
}
