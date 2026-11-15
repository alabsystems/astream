// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `fleet.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `fleet.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================

    -- Clamped replay frontier progression up to `cut_off`.
    def fleet_clamp_to_cut (seq : UInt64) (cut_off : UInt64) : UInt64 :=
      if seq < cut_off then seq else cut_off

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaFleetCut)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaFleetCut

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

    prefix:100 "□" => _root_.Astream.Engine.TlaFleetCut.Always
    infixl:45 " ⊨ " => _root_.Astream.Engine.TlaFleetCut.Satisfies

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

    structure ReplayState where
      folded_seq : UInt64
      cut_off : UInt64

    def ReplayWithinCutInv (s : ReplayState) : Prop :=
      Nat.le (UInt64.toNat s.folded_seq) (UInt64.toNat s.cut_off)

    def Init (cut_off : UInt64) (s : ReplayState) : Prop :=
      s.folded_seq = 0 ∧ s.cut_off = cut_off

    def foldRecordAction (seq : UInt64) (s sNext : ReplayState) : Prop :=
      sNext.cut_off = s.cut_off ∧
      sNext.folded_seq = _root_.fleet_clamp_to_cut seq s.cut_off

    def Next (s sNext : ReplayState) : Prop :=
      ∃ seq : UInt64, foldRecordAction seq s sNext

    def Spec (cut_off : UInt64) : StateMachine ReplayState :=
      StateMachine.mk (Init cut_off) Next

    theorem clamp_le_cut : forall (seq : UInt64) (cut_off : UInt64),
        Nat.le (UInt64.toNat (_root_.fleet_clamp_to_cut seq cut_off)) (UInt64.toNat cut_off) :=
      fun seq cut_off => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt seq cut_off)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cut_off) (fun _ => seq))) (UInt64.toNat cut_off))
        (instDecidableUInt64Lt seq cut_off)
        (fun _ => Nat.le.refl (UInt64.toNat cut_off))
        (fun h => Nat.le_of_lt h)

    theorem uint64_zero_le (a : UInt64) (hZero : a = 0) (b : UInt64) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (cut_off : UInt64) (s : ReplayState)
        (hInit : Init cut_off s) : ReplayWithinCutInv s :=
      uint64_zero_le s.folded_seq hInit.1 s.cut_off

    theorem next_preserves_inv (s sNext : ReplayState)
        (_hInv : ReplayWithinCutInv s) (hNext : Next s sNext) :
        ReplayWithinCutInv sNext :=
      Exists.elim hNext (fun seq hStep =>
        let hClamp : Nat.le (UInt64.toNat sNext.folded_seq) (UInt64.toNat s.cut_off) :=
          Eq.mpr
            (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.cut_off)) hStep.2)
            (clamp_le_cut seq s.cut_off)
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.folded_seq) (UInt64.toNat y)) hStep.1)
          hClamp)

    theorem spec_satisfies_fleet_replay_bounded (cut_off : UInt64) :
        (Spec cut_off) ⊨ □ (Lift ReplayWithinCutInv) :=
      invariantSatisfies (Spec cut_off) ReplayWithinCutInv
        (init_establishes_inv cut_off)
        next_preserves_inv

    end TlaFleetCut
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def fleet_seq_within_cut_isl (seq : UInt64) (cut_off : UInt64) : Bool :=
      decide (seq ≤ cut_off)
}
