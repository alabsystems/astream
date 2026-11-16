// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `fork.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `fork.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================

    -- Clamped fork index bounded by `len`.
    def fork_clamped_index (idx : UInt64) (len : UInt64) : UInt64 :=
      if idx < len then idx else len

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaForkSwap)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaForkSwap

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

    prefix:100 "□" => _root_.Astream.Engine.TlaForkSwap.Always
    infixl:45 " ⊨ " => _root_.Astream.Engine.TlaForkSwap.Satisfies

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

    structure ForkState where
      swapped_at : UInt64
      total_len : UInt64

    def ForkIndexBoundedInv (s : ForkState) : Prop :=
      Nat.le (UInt64.toNat s.swapped_at) (UInt64.toNat s.total_len)

    def Init (total_len : UInt64) (s : ForkState) : Prop :=
      s.swapped_at = 0 ∧ s.total_len = total_len

    def swapAction (idx : UInt64) (s sNext : ForkState) : Prop :=
      sNext.total_len = s.total_len ∧
      sNext.swapped_at = _root_.fork_clamped_index idx s.total_len

    def Next (s sNext : ForkState) : Prop :=
      ∃ idx : UInt64, swapAction idx s sNext

    def Spec (total_len : UInt64) : StateMachine ForkState :=
      StateMachine.mk (Init total_len) Next

    theorem clamped_le_len : forall (idx : UInt64) (len : UInt64),
        Nat.le (UInt64.toNat (_root_.fork_clamped_index idx len)) (UInt64.toNat len) :=
      fun idx len => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt idx len)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => len) (fun _ => idx))) (UInt64.toNat len))
        (instDecidableUInt64Lt idx len)
        (fun _ => @Nat.le.refl (UInt64.toNat len))
        (fun h => Nat.le_of_lt h)

    theorem uint64_zero_le (a : UInt64) (hZero : a = 0) (b : UInt64) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (total_len : UInt64) (s : ForkState)
        (hInit : Init total_len s) : ForkIndexBoundedInv s :=
      uint64_zero_le s.swapped_at hInit.1 s.total_len

    theorem next_preserves_inv (s sNext : ForkState)
        (_hInv : ForkIndexBoundedInv s) (hNext : Next s sNext) :
        ForkIndexBoundedInv sNext :=
      Exists.elim hNext (fun idx hStep =>
        let hClamp : Nat.le (UInt64.toNat sNext.swapped_at) (UInt64.toNat s.total_len) :=
          Eq.mpr
            (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.total_len)) hStep.2)
            (clamped_le_len idx s.total_len)
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.swapped_at) (UInt64.toNat y)) hStep.1)
          hClamp)

    theorem spec_satisfies_fork_index_bounded (total_len : UInt64) :
        (Spec total_len) ⊨ □ (Lift ForkIndexBoundedInv) :=
      invariantSatisfies (Spec total_len) ForkIndexBoundedInv
        (init_establishes_inv total_len)
        next_preserves_inv

    end TlaForkSwap
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def fork_index_in_bounds_isl (idx : UInt64) (len : UInt64) : Bool :=
      decide (idx < len)
}
