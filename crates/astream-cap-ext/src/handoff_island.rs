// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `handoff.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `handoff.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def handoff_epoch_advance (prev_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if prev_epoch < cand_epoch then cand_epoch else prev_epoch

    def handoff_summary_clamp (len : UInt64) (max_len : UInt64) : UInt64 :=
      if len < max_len then len else max_len

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Restart Handoff Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaRestartHandoff

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

    structure RestartHandoffState where
      restart_epoch : UInt64
      prev_epoch : UInt64
      summary_len : UInt64
      max_summary_len : UInt64

    def RestartHandoffInv (s : RestartHandoffState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.restart_epoch))
        (Nat.le (UInt64.toNat s.summary_len) (UInt64.toNat s.max_summary_len))

    def Init (s : RestartHandoffState) : Prop :=
      And
        (s.summary_len = 0)
        (And (s.restart_epoch = 0) (s.prev_epoch = 0))

    def handoffStep (cand_epoch : UInt64) (raw_len : UInt64) (s : RestartHandoffState) : RestartHandoffState :=
      RestartHandoffState.mk
        (_root_.handoff_epoch_advance s.restart_epoch cand_epoch)
        s.restart_epoch
        (_root_.handoff_summary_clamp raw_len s.max_summary_len)
        s.max_summary_len

    def Next (s : RestartHandoffState) (s' : RestartHandoffState) : Prop :=
      ∃ (cand_epoch : UInt64), ∃ (raw_len : UInt64),
        s' = handoffStep cand_epoch raw_len s

    def Spec : StateMachine RestartHandoffState :=
      StateMachine.mk Init Next

    theorem epoch_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.handoff_epoch_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem len_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.handoff_summary_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
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

    theorem init_establishes_inv (s : RestartHandoffState) (hInit : Init s) :
      RestartHandoffInv s :=
      And.intro
        (eq_zero_le
          s.prev_epoch
          s.restart_epoch
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.summary_len s.max_summary_len (And.left hInit))

    theorem next_preserves_inv (s : RestartHandoffState) (s' : RestartHandoffState)
      (_hInv : RestartHandoffInv s) (hNext : Next s s') :
      RestartHandoffInv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (rl : UInt64), s' = handoffStep ce rl s) =>
        Exists.elim hRest (fun (rl : UInt64) (hEq : s' = handoffStep ce rl s) =>
          Eq.mpr
            (congrArg (fun (st : RestartHandoffState) => RestartHandoffInv st) hEq)
            (And.intro
              (epoch_monotone s.restart_epoch ce)
              (len_le_max rl s.max_summary_len))))

    theorem restart_handoff_safety_always :
      Satisfies (Runs Spec) (Always (Lift RestartHandoffInv)) :=
      invariantSatisfies Spec RestartHandoffInv init_establishes_inv next_preserves_inv

    end TlaRestartHandoff
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def handoff_pid_eq_isl (expected_pid : UInt32) (observed_pid : UInt32) : Bool :=
      decide (expected_pid = observed_pid)
}
