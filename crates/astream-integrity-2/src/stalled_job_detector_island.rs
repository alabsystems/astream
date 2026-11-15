// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `stalled_job_detector.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `stalled_job_detector.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def job_stall_ticks_clamp (cand_ticks : UInt64) (stall_cap : UInt64) : UInt64 :=
      if cand_ticks < stall_cap then cand_ticks else stall_cap

    def job_progress_advance (cur_prog : UInt64) (cand_prog : UInt64) : UInt64 :=
      if cur_prog < cand_prog then cand_prog else cur_prog

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Stalled Job Detector Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaStalledJobDetector

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

    structure StalledJobState where
      stall_ticks : UInt64
      stall_cap : UInt64
      progress_mark : UInt64
      prev_mark : UInt64

    def StalledJobDetectorInv (s : StalledJobState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.stall_ticks) (UInt64.toNat s.stall_cap))
        (Nat.le (UInt64.toNat s.prev_mark) (UInt64.toNat s.progress_mark))

    def Init (stall_cap : UInt64) (s : StalledJobState) : Prop :=
      And
        (And (s.stall_ticks = 0) (s.stall_cap = stall_cap))
        (And (s.progress_mark = 0) (s.prev_mark = 0))

    def sampleJobStep (cand_ticks : UInt64) (cand_prog : UInt64) (s : StalledJobState) : StalledJobState :=
      StalledJobState.mk
        (_root_.job_stall_ticks_clamp cand_ticks s.stall_cap)
        s.stall_cap
        (_root_.job_progress_advance s.progress_mark cand_prog)
        s.progress_mark

    def Next (s : StalledJobState) (s' : StalledJobState) : Prop :=
      ∃ (cand_ticks : UInt64), ∃ (cand_prog : UInt64),
        s' = sampleJobStep cand_ticks cand_prog s

    def Spec (stall_cap : UInt64) : StateMachine StalledJobState :=
      StateMachine.mk (Init stall_cap) Next

    theorem stall_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.job_stall_ticks_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem prog_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.job_progress_advance cur cand)) :=
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

    theorem init_establishes_inv (stall_cap : UInt64) (s : StalledJobState)
      (hInit : Init stall_cap s) :
      StalledJobDetectorInv s :=
      And.intro
        (eq_zero_le s.stall_ticks s.stall_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_mark s.progress_mark (And.right (And.right hInit)))

    theorem next_preserves_inv (s : StalledJobState) (s' : StalledJobState)
      (_hInv : StalledJobDetectorInv s) (hNext : Next s s') :
      StalledJobDetectorInv s' :=
      Exists.elim hNext (fun (ct : UInt64) (hRest : ∃ (cp : UInt64), s' = sampleJobStep ct cp s) =>
        Exists.elim hRest (fun (cp : UInt64) (hEq : s' = sampleJobStep ct cp s) =>
          Eq.mpr
            (congrArg (fun (st : StalledJobState) => StalledJobDetectorInv st) hEq)
            (And.intro
              (stall_clamp_le ct s.stall_cap)
              (prog_monotone s.progress_mark cp))))

    theorem stalled_job_detector_safety_always (stall_cap : UInt64) :
      Satisfies (Runs (Spec stall_cap)) (Always (Lift StalledJobDetectorInv)) :=
      invariantSatisfies (Spec stall_cap) StalledJobDetectorInv (init_establishes_inv stall_cap) next_preserves_inv

    end TlaStalledJobDetector
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def job_stall_threshold_reached_isl (stall_ticks : UInt64) (stall_cap : UInt64) : Bool :=
      decide (stall_cap <= stall_ticks)
}
