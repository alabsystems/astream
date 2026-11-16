// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `log.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `log.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================

    -- Monotone single-writer offset advance (`max(cur_next, assigned_next)`).
    def log_advance_offset_monotone (cur_next : UInt64) (assigned_next : UInt64) : UInt64 :=
      if cur_next < assigned_next then assigned_next else cur_next

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaLogSpine)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaLogSpine

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

    prefix:100 "□" => _root_.Astream.Engine.TlaLogSpine.Always
    infixl:45 " ⊨ " => _root_.Astream.Engine.TlaLogSpine.Satisfies

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

    structure LogState where
      init_off : UInt64
      next_off : UInt64

    def LogOffsetMonotoneInv (s : LogState) : Prop :=
      Nat.le (UInt64.toNat s.init_off) (UInt64.toNat s.next_off)

    def Init (init_off : UInt64) (s : LogState) : Prop :=
      s.init_off = init_off ∧ s.next_off = init_off

    def appendAction (assigned_next : UInt64) (s sNext : LogState) : Prop :=
      sNext.init_off = s.init_off ∧
      sNext.next_off = _root_.log_advance_offset_monotone s.next_off assigned_next

    def Next (s sNext : LogState) : Prop :=
      ∃ assigned_next : UInt64, appendAction assigned_next s sNext

    def Spec (init_off : UInt64) : StateMachine LogState :=
      StateMachine.mk (Init init_off) Next

    theorem advance_ge_cur : forall (cur : UInt64) (assigned : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.log_advance_offset_monotone cur assigned)) :=
      fun cur assigned => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur assigned)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => assigned))))
        (instDecidableUInt64Lt cur assigned)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat a) (UInt64.toNat x)) (Eq.symm hEq))
        (@Nat.le.refl (UInt64.toNat a))

    theorem init_establishes_inv (init_off : UInt64) (s : LogState)
        (hInit : Init init_off s) : LogOffsetMonotoneInv s :=
      uint64_eq_le s.init_off s.next_off (Eq.trans hInit.1 (Eq.symm hInit.2))

    theorem next_preserves_inv (s sNext : LogState)
        (hInv : LogOffsetMonotoneInv s) (hNext : Next s sNext) :
        LogOffsetMonotoneInv sNext :=
      Exists.elim hNext (fun assigned hStep =>
        let hInitLe : Nat.le (UInt64.toNat sNext.init_off) (UInt64.toNat s.next_off) :=
          Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.next_off)) hStep.1) hInv
        let hAdv : Nat.le (UInt64.toNat s.next_off) (UInt64.toNat sNext.next_off) :=
          Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.next_off) (UInt64.toNat y)) hStep.2)
            (advance_ge_cur s.next_off assigned)
        Nat.le_trans hInitLe hAdv)

    theorem spec_satisfies_log_offset_monotonicity (init_off : UInt64) :
        (Spec init_off) ⊨ □ (Lift LogOffsetMonotoneInv) :=
      invariantSatisfies (Spec init_off) LogOffsetMonotoneInv
        (init_establishes_inv init_off)
        next_preserves_inv

    end TlaLogSpine
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def log_same_log_cause_valid_isl (cause_offset : UInt64) (seq : UInt64) : Bool :=
      decide (cause_offset < seq)
}
