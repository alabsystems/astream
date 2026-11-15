// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `timer_wheel.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `timer_wheel.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def timer_clock_advance (cur_ms : UInt64) (sample_ms : UInt64) : UInt64 :=
      if cur_ms < sample_ms then sample_ms else cur_ms

    def timer_pending_clamp (pending : UInt64) (max_timers : UInt64) : UInt64 :=
      if pending < max_timers then pending else max_timers

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Deterministic Timer Spec
    -- =======================================================================

    namespace Astream
    namespace Effects
    namespace TlaDeterministicTimerWheel

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

    structure TimerWheelState where
      clock_ms : UInt64
      prev_clock_ms : UInt64
      pending : UInt64
      max_timers : UInt64

    def TimerWheelInv (s : TimerWheelState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_clock_ms) (UInt64.toNat s.clock_ms))
        (Nat.le (UInt64.toNat s.pending) (UInt64.toNat s.max_timers))

    def Init (s : TimerWheelState) : Prop :=
      And
        (s.pending = 0)
        (And (s.clock_ms = 0) (s.prev_clock_ms = 0))

    def advanceWheelStep (sample_ms : UInt64) (cand_pending : UInt64) (s : TimerWheelState) : TimerWheelState :=
      TimerWheelState.mk
        (_root_.timer_clock_advance s.clock_ms sample_ms)
        s.clock_ms
        (_root_.timer_pending_clamp cand_pending s.max_timers)
        s.max_timers

    def Next (s : TimerWheelState) (s' : TimerWheelState) : Prop :=
      ∃ (sample_ms : UInt64), ∃ (cand_pending : UInt64),
        s' = advanceWheelStep sample_ms cand_pending s

    def Spec : StateMachine TimerWheelState :=
      StateMachine.mk Init Next

    theorem clock_monotone : forall (cur : UInt64) (samp : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.timer_clock_advance cur samp)) :=
      fun cur samp => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur samp)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => samp))))
        (instDecidableUInt64Lt cur samp)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem pending_le_max : forall (pend : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.timer_pending_clamp pend cap)) (UInt64.toNat cap) :=
      fun pend cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt pend cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => pend))) (UInt64.toNat cap))
        (instDecidableUInt64Lt pend cap)
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

    theorem init_establishes_inv (s : TimerWheelState) (hInit : Init s) :
      TimerWheelInv s :=
      And.intro
        (eq_zero_le
          s.prev_clock_ms
          s.clock_ms
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.pending s.max_timers (And.left hInit))

    theorem next_preserves_inv (s : TimerWheelState) (s' : TimerWheelState)
      (_hInv : TimerWheelInv s) (hNext : Next s s') :
      TimerWheelInv s' :=
      Exists.elim hNext (fun (sm : UInt64) (hRest : ∃ (cp : UInt64), s' = advanceWheelStep sm cp s) =>
        Exists.elim hRest (fun (cp : UInt64) (hEq : s' = advanceWheelStep sm cp s) =>
          Eq.mpr
            (congrArg (fun (st : TimerWheelState) => TimerWheelInv st) hEq)
            (And.intro
              (clock_monotone s.clock_ms sm)
              (pending_le_max cp s.max_timers))))

    theorem timer_wheel_safety_always :
      Satisfies (Runs Spec) (Always (Lift TimerWheelInv)) :=
      invariantSatisfies Spec TimerWheelInv init_establishes_inv next_preserves_inv

    end TlaDeterministicTimerWheel
    end Effects
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def timer_deadline_due_isl (deadline_ms : UInt64) (clock_ms : UInt64) : Bool :=
      decide (deadline_ms ≤ clock_ms)
}
