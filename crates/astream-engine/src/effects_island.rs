// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `effects.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `effects.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================

    -- Monotone logical clock jump past a stored timestamp `ts` (`next_ts = ts.saturating_add(1)`).
    def logical_clock_advance_past_tick (cur_tick : UInt64) (_ts : UInt64) (next_ts : UInt64) : UInt64 :=
      if cur_tick < next_ts then next_ts else cur_tick

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaLogicalClock)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaLogicalClock

    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop

    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)

    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    prefix:100 "□" => _root_.Astream.Engine.TlaLogicalClock.Always
    infixl:45 " ⊨ " => _root_.Astream.Engine.TlaLogicalClock.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      @Nat.rec (fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun step => hStep (b k) (b (Nat.succ k)) ih step)
            (fun stutter => Eq.mpr (congrArg I stutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    structure ClockState where
      floor_tick : UInt64
      cur_tick : UInt64

    def ClockMonotoneInv (s : ClockState) : Prop :=
      Nat.le (UInt64.toNat s.floor_tick) (UInt64.toNat s.cur_tick)

    def Init (start_tick : UInt64) (s : ClockState) : Prop :=
      s.floor_tick = start_tick ∧ s.cur_tick = start_tick

    def advanceAction (ts next_ts : UInt64) (s sNext : ClockState) : Prop :=
      sNext.floor_tick = s.floor_tick ∧
      sNext.cur_tick = _root_.logical_clock_advance_past_tick s.cur_tick ts next_ts

    def Next (s sNext : ClockState) : Prop :=
      ∃ ts : UInt64, ∃ next_ts : UInt64, advanceAction ts next_ts s sNext

    def Spec (start_tick : UInt64) : StateMachine ClockState :=
      StateMachine.mk (Init start_tick) Next

    theorem advance_ge_cur : forall (cur : UInt64) (ts : UInt64) (next_ts : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.logical_clock_advance_past_tick cur ts next_ts)) :=
      fun cur _ts next_ts => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur next_ts)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => next_ts))))
        (instDecidableUInt64Lt cur next_ts)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat a) (UInt64.toNat x)) (Eq.symm hEq))
        (@Nat.le.refl (UInt64.toNat a))

    theorem init_establishes_inv (start_tick : UInt64) (s : ClockState)
        (hInit : Init start_tick s) : ClockMonotoneInv s :=
      uint64_eq_le s.floor_tick s.cur_tick (Eq.trans hInit.1 (Eq.symm hInit.2))

    theorem next_preserves_inv (s sNext : ClockState)
        (hInv : ClockMonotoneInv s) (hNext : Next s sNext) : ClockMonotoneInv sNext :=
      Exists.elim hNext (fun ts hEx =>
        Exists.elim hEx (fun next_ts hStep =>
          let hFloor : Nat.le (UInt64.toNat sNext.floor_tick) (UInt64.toNat s.cur_tick) :=
            Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.cur_tick)) hStep.1) hInv
          let hAdv : Nat.le (UInt64.toNat s.cur_tick) (UInt64.toNat sNext.cur_tick) :=
            Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.cur_tick) (UInt64.toNat y)) hStep.2)
              (advance_ge_cur s.cur_tick ts next_ts)
          Nat.le_trans hFloor hAdv))

    theorem spec_satisfies_clock_monotonicity (start_tick : UInt64) :
        (Spec start_tick) ⊨ □ (Lift ClockMonotoneInv) :=
      invariantSatisfies (Spec start_tick) ClockMonotoneInv
        (init_establishes_inv start_tick)
        next_preserves_inv

    end TlaLogicalClock
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def logical_clock_at_max_isl (ts : UInt64) : Bool :=
      decide (ts = 18446744073709551615)
}
