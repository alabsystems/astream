// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `sys_pressure_gate.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `sys_pressure_gate.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def sys_jobs_clamp (cand_jobs : UInt64) (max_jobs : UInt64) : UInt64 :=
      if cand_jobs < max_jobs then cand_jobs else max_jobs

    def sys_sample_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Sys Pressure Gate Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaSysPressureGate

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

    structure SysPressureState where
      granted_jobs : UInt64
      max_jobs : UInt64
      sample_epoch : UInt64
      prev_epoch : UInt64

    def SysPressureGateInv (s : SysPressureState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.granted_jobs) (UInt64.toNat s.max_jobs))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.sample_epoch))

    def Init (max_jobs : UInt64) (s : SysPressureState) : Prop :=
      And
        (And (s.granted_jobs = 0) (s.max_jobs = max_jobs))
        (And (s.sample_epoch = 0) (s.prev_epoch = 0))

    def sampleStep (cand_jobs : UInt64) (cand_epoch : UInt64) (s : SysPressureState) : SysPressureState :=
      SysPressureState.mk
        (_root_.sys_jobs_clamp cand_jobs s.max_jobs)
        s.max_jobs
        (_root_.sys_sample_epoch_advance s.sample_epoch cand_epoch)
        s.sample_epoch

    def Next (s : SysPressureState) (s' : SysPressureState) : Prop :=
      ∃ (cand_jobs : UInt64), ∃ (cand_epoch : UInt64),
        s' = sampleStep cand_jobs cand_epoch s

    def Spec (max_jobs : UInt64) : StateMachine SysPressureState :=
      StateMachine.mk (Init max_jobs) Next

    theorem jobs_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sys_jobs_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.sys_sample_epoch_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_jobs : UInt64) (s : SysPressureState)
      (hInit : Init max_jobs s) :
      SysPressureGateInv s :=
      And.intro
        (eq_zero_le s.granted_jobs s.max_jobs (And.left (And.left hInit)))
        (eq_zero_le s.prev_epoch s.sample_epoch (And.right (And.right hInit)))

    theorem next_preserves_inv (s : SysPressureState) (s' : SysPressureState)
      (_hInv : SysPressureGateInv s) (hNext : Next s s') :
      SysPressureGateInv s' :=
      Exists.elim hNext (fun (cj : UInt64) (hRest : ∃ (ce : UInt64), s' = sampleStep cj ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = sampleStep cj ce s) =>
          Eq.mpr
            (congrArg (fun (st : SysPressureState) => SysPressureGateInv st) hEq)
            (And.intro
              (jobs_clamp_le cj s.max_jobs)
              (epoch_monotone s.sample_epoch ce))))

    theorem sys_pressure_gate_safety_always (max_jobs : UInt64) :
      Satisfies (Runs (Spec max_jobs)) (Always (Lift SysPressureGateInv)) :=
      invariantSatisfies (Spec max_jobs) SysPressureGateInv (init_establishes_inv max_jobs) next_preserves_inv

    end TlaSysPressureGate
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def sys_jobs_within_cap_isl (jobs : UInt64) (max_jobs : UInt64) : Bool :=
      decide (jobs <= max_jobs)
}
