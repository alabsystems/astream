// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `aterm ctl @self sys jobs` command stall detection
// (`Astream.Host.TlaSysStallWatchdog`, Island #284), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def sys_progress_advance (prev_work : UInt64) (cur_work : UInt64) : UInt64 :=
      if prev_work < cur_work then cur_work else prev_work

    def sys_silent_ms_clamp (silent_ms : UInt64) (max_ms : UInt64) : UInt64 :=
      if silent_ms < max_ms then silent_ms else max_ms

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Sys Stall Watchdog Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaSysStallWatchdog

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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next)
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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next) :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure SysJobState where
      prev_work : UInt64
      work : UInt64
      silent_ms : UInt64
      max_silent_ms : UInt64

    def SysJobSafetyInv (s : SysJobState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_work) (UInt64.toNat s.work))
        (Nat.le (UInt64.toNat s.silent_ms) (UInt64.toNat s.max_silent_ms))

    def Init (s : SysJobState) : Prop :=
      And
        (s.prev_work = s.work)
        (Nat.le (UInt64.toNat s.silent_ms) (UInt64.toNat s.max_silent_ms))

    def sampleJobStep (cand_work : UInt64) (raw_silent : UInt64) (s : SysJobState) : SysJobState :=
      SysJobState.mk
        s.work
        (_root_.sys_progress_advance s.work cand_work)
        (_root_.sys_silent_ms_clamp raw_silent s.max_silent_ms)
        s.max_silent_ms

    def Next (s : SysJobState) (s_next : SysJobState) : Prop :=
      ∃ (cand_work : UInt64), ∃ (raw_silent : UInt64),
        s_next = sampleJobStep cand_work raw_silent s

    def Spec : StateMachine SysJobState :=
      StateMachine.mk Init Next

    theorem work_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.sys_progress_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem silent_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sys_silent_ms_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : SysJobState) (hInit : Init s) :
      SysJobSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_work s.work (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : SysJobState) (s_next : SysJobState)
      (_hInv : SysJobSafetyInv s) (hNext : Next s s_next) :
      SysJobSafetyInv s_next :=
      Exists.elim hNext (fun (cw : UInt64) (hRest : ∃ (rs : UInt64), s_next = sampleJobStep cw rs s) =>
        Exists.elim hRest (fun (rs : UInt64) (hEq : s_next = sampleJobStep cw rs s) =>
          Eq.mpr
            (congrArg (fun (st : SysJobState) => SysJobSafetyInv st) hEq)
            (And.intro
              (work_ge_prev s.work cw)
              (silent_le_cap rs s.max_silent_ms))))

    theorem sys_watchdog_safety_always :
      Satisfies (Runs Spec) (Always (Lift SysJobSafetyInv)) :=
      invariantSatisfies Spec SysJobSafetyInv init_establishes_inv next_preserves_inv

    end TlaSysStallWatchdog
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def sys_silence_past_threshold_isl (silent_ms : UInt64) (threshold_ms : UInt64) : Bool :=
      decide (threshold_ms ≤ silent_ms)
}
