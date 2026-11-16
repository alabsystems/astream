// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `store.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `store.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================

    -- Monotone recovery prefix byte length progression (`max(cur_len, next_len)`).
    def store_advance_valid_len (cur_len : UInt64) (next_len : UInt64) : UInt64 :=
      if cur_len < next_len then next_len else cur_len

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaStoreRecovery)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaStoreRecovery

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

    prefix:100 "□" => _root_.Astream.Engine.TlaStoreRecovery.Always
    infixl:45 " ⊨ " => _root_.Astream.Engine.TlaStoreRecovery.Satisfies

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

    structure RecoveryState where
      init_len : UInt64
      valid_len : UInt64

    def StorePrefixMonotoneInv (s : RecoveryState) : Prop :=
      Nat.le (UInt64.toNat s.init_len) (UInt64.toNat s.valid_len)

    def Init (init_len : UInt64) (s : RecoveryState) : Prop :=
      s.init_len = init_len ∧ s.valid_len = init_len

    def acceptFrameAction (next_len : UInt64) (s sNext : RecoveryState) : Prop :=
      sNext.init_len = s.init_len ∧
      sNext.valid_len = _root_.store_advance_valid_len s.valid_len next_len

    def Next (s sNext : RecoveryState) : Prop :=
      ∃ next_len : UInt64, acceptFrameAction next_len s sNext

    def Spec (init_len : UInt64) : StateMachine RecoveryState :=
      StateMachine.mk (Init init_len) Next

    theorem advance_ge_cur : forall (cur : UInt64) (next_len : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.store_advance_valid_len cur next_len)) :=
      fun cur next_len => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur next_len)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => next_len))))
        (instDecidableUInt64Lt cur next_len)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat a) (UInt64.toNat x)) (Eq.symm hEq))
        (@Nat.le.refl (UInt64.toNat a))

    theorem init_establishes_inv (init_len : UInt64) (s : RecoveryState)
        (hInit : Init init_len s) : StorePrefixMonotoneInv s :=
      uint64_eq_le s.init_len s.valid_len (Eq.trans hInit.1 (Eq.symm hInit.2))

    theorem next_preserves_inv (s sNext : RecoveryState)
        (hInv : StorePrefixMonotoneInv s) (hNext : Next s sNext) :
        StorePrefixMonotoneInv sNext :=
      Exists.elim hNext (fun next_len hStep =>
        let hInitLe : Nat.le (UInt64.toNat sNext.init_len) (UInt64.toNat s.valid_len) :=
          Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.valid_len)) hStep.1) hInv
        let hAdv : Nat.le (UInt64.toNat s.valid_len) (UInt64.toNat sNext.valid_len) :=
          Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.valid_len) (UInt64.toNat y)) hStep.2)
            (advance_ge_cur s.valid_len next_len)
        Nat.le_trans hInitLe hAdv)

    theorem spec_satisfies_store_prefix_monotonicity (init_len : UInt64) :
        (Spec init_len) ⊨ □ (Lift StorePrefixMonotoneInv) :=
      invariantSatisfies (Spec init_len) StorePrefixMonotoneInv
        (init_establishes_inv init_len)
        next_preserves_inv

    end TlaStoreRecovery
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def store_seq_matches_expected_isl (found_seq : UInt64) (expected_seq : UInt64) : Bool :=
      decide (found_seq = expected_seq)
}
