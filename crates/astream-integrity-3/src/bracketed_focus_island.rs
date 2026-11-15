// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `bracketed_focus.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `bracketed_focus.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def focus_burst_clamp (cand_transitions : UInt64) (burst_cap : UInt64) : UInt64 :=
      if cand_transitions < burst_cap then cand_transitions else burst_cap

    def focus_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Focus Reporting Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaFocusInOutTracker

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

    structure FocusTrackerState where
      burst_transitions : UInt64
      burst_cap : UInt64
      focus_epoch : UInt64
      prev_epoch : UInt64

    def FocusTrackerInv (s : FocusTrackerState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.burst_transitions) (UInt64.toNat s.burst_cap))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.focus_epoch))

    def Init (burst_cap : UInt64) (s : FocusTrackerState) : Prop :=
      And
        (And (s.burst_transitions = 0) (s.burst_cap = burst_cap))
        (And (s.focus_epoch = 0) (s.prev_epoch = 0))

    def focusStep (cand_burst : UInt64) (cand_epoch : UInt64) (s : FocusTrackerState) : FocusTrackerState :=
      FocusTrackerState.mk
        (_root_.focus_burst_clamp cand_burst s.burst_cap)
        s.burst_cap
        (_root_.focus_epoch_advance s.focus_epoch cand_epoch)
        s.focus_epoch

    def Next (s : FocusTrackerState) (s' : FocusTrackerState) : Prop :=
      ∃ (cand_burst : UInt64), ∃ (cand_epoch : UInt64),
        s' = focusStep cand_burst cand_epoch s

    def Spec (burst_cap : UInt64) : StateMachine FocusTrackerState :=
      StateMachine.mk (Init burst_cap) Next

    theorem burst_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.focus_burst_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.focus_epoch_advance cur cand)) :=
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

    theorem init_establishes_inv (burst_cap : UInt64) (s : FocusTrackerState)
      (hInit : Init burst_cap s) :
      FocusTrackerInv s :=
      And.intro
        (eq_zero_le s.burst_transitions s.burst_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_epoch s.focus_epoch (And.right (And.right hInit)))

    theorem next_preserves_inv (s : FocusTrackerState) (s' : FocusTrackerState)
      (_hInv : FocusTrackerInv s) (hNext : Next s s') :
      FocusTrackerInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (ce : UInt64), s' = focusStep cb ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = focusStep cb ce s) =>
          Eq.mpr
            (congrArg (fun (st : FocusTrackerState) => FocusTrackerInv st) hEq)
            (And.intro
              (burst_clamp_le cb s.burst_cap)
              (epoch_monotone s.focus_epoch ce))))

    theorem focus_tracker_safety_always (burst_cap : UInt64) :
      Satisfies (Runs (Spec burst_cap)) (Always (Lift FocusTrackerInv)) :=
      invariantSatisfies (Spec burst_cap) FocusTrackerInv (init_establishes_inv burst_cap) next_preserves_inv

    end TlaFocusInOutTracker
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def focus_burst_within_cap_isl (transitions : UInt64) (burst_cap : UInt64) : Bool :=
      decide (transitions <= burst_cap)
}
