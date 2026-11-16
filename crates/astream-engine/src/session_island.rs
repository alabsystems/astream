// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `session.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `session.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================

    -- Monotone per-client high-water bump (`max(cur_hw, client_seq)`).
    def session_bump_high_water (cur_hw : UInt64) (client_seq : UInt64) : UInt64 :=
      if cur_hw < client_seq then client_seq else cur_hw

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaSessionDedup)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaSessionDedup

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

    prefix:100 "□" => _root_.Astream.Engine.TlaSessionDedup.Always
    infixl:45 " ⊨ " => _root_.Astream.Engine.TlaSessionDedup.Satisfies

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

    structure DedupState where
      init_hw : UInt64
      cur_hw : UInt64

    def HighWaterMonotoneInv (s : DedupState) : Prop :=
      Nat.le (UInt64.toNat s.init_hw) (UInt64.toNat s.cur_hw)

    def Init (init_hw : UInt64) (s : DedupState) : Prop :=
      s.init_hw = init_hw ∧ s.cur_hw = init_hw

    def bumpAction (client_seq : UInt64) (s sNext : DedupState) : Prop :=
      sNext.init_hw = s.init_hw ∧
      sNext.cur_hw = _root_.session_bump_high_water s.cur_hw client_seq

    def Next (s sNext : DedupState) : Prop :=
      ∃ client_seq : UInt64, bumpAction client_seq s sNext

    def Spec (init_hw : UInt64) : StateMachine DedupState :=
      StateMachine.mk (Init init_hw) Next

    theorem bump_ge_cur : forall (cur : UInt64) (seq : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.session_bump_high_water cur seq)) :=
      fun cur seq => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur seq)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => seq))))
        (instDecidableUInt64Lt cur seq)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat a) (UInt64.toNat x)) (Eq.symm hEq))
        (@Nat.le.refl (UInt64.toNat a))

    theorem init_establishes_inv (init_hw : UInt64) (s : DedupState)
        (hInit : Init init_hw s) : HighWaterMonotoneInv s :=
      uint64_eq_le s.init_hw s.cur_hw (Eq.trans hInit.1 (Eq.symm hInit.2))

    theorem next_preserves_inv (s sNext : DedupState)
        (hInv : HighWaterMonotoneInv s) (hNext : Next s sNext) :
        HighWaterMonotoneInv sNext :=
      Exists.elim hNext (fun seq hStep =>
        let hInitLe : Nat.le (UInt64.toNat sNext.init_hw) (UInt64.toNat s.cur_hw) :=
          Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.cur_hw)) hStep.1) hInv
        let hBump : Nat.le (UInt64.toNat s.cur_hw) (UInt64.toNat sNext.cur_hw) :=
          Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.cur_hw) (UInt64.toNat y)) hStep.2)
            (bump_ge_cur s.cur_hw seq)
        Nat.le_trans hInitLe hBump)

    theorem spec_satisfies_high_water_monotonicity (init_hw : UInt64) :
        (Spec init_hw) ⊨ □ (Lift HighWaterMonotoneInv) :=
      invariantSatisfies (Spec init_hw) HighWaterMonotoneInv
        (init_establishes_inv init_hw)
        next_preserves_inv

    end TlaSessionDedup
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def session_seq_is_duplicate_isl (client_seq : UInt64) (high_water : UInt64) : Bool :=
      decide (client_seq ≤ high_water)
}
