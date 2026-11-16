// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `capture.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `capture.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `islands/capture_twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def capture_clamp_dim (dim : UInt64) (max_dim : UInt64) : UInt64 :=
      if dim < max_dim then dim else max_dim

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Live.TlaCaptureBin)
    -- ========================================================================
    namespace Astream
    namespace Live
    namespace TlaCaptureBin

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (k : Nat) (b : Behavior State) : Behavior State :=
      fun (n : Nat) => b (Nat.add k n)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (k : Nat), P (drop k b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        M.Init (b 0) ∧ ∀ (k : Nat), M.Next (b k) (b (Nat.add k 1))

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun (b : Behavior State) => P (b 0)

    def Satisfies {State : Type} (SpecF : Formula State) (PropF : Formula State) : Prop :=
      ∀ (b : Behavior State), SpecF b → PropF b

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

    structure CaptureReplayState where
      cols : UInt64
      max_cols : UInt64

    def CaptureDimBoundedInv (s : CaptureReplayState) : Prop :=
      Nat.le (UInt64.toNat s.cols) (UInt64.toNat s.max_cols)

    def Init (s : CaptureReplayState) : Prop :=
      s.cols = (0 : UInt64)

    def setColsAction (requested : UInt64) (max_cols : UInt64) (_s : CaptureReplayState) : CaptureReplayState :=
      CaptureReplayState.mk (_root_.capture_clamp_dim requested max_cols) max_cols

    def Next (s : CaptureReplayState) (s' : CaptureReplayState) : Prop :=
      ∃ (requested : UInt64), ∃ (max_cols : UInt64), s' = setColsAction requested max_cols s

    def Spec : StateMachine CaptureReplayState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (requested : UInt64) (max_cols : UInt64),
        Nat.le (UInt64.toNat (_root_.capture_clamp_dim requested max_cols)) (UInt64.toNat max_cols) :=
      fun requested max_cols => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt requested max_cols)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_cols) (fun _ => requested))) (UInt64.toNat max_cols))
        (instDecidableUInt64Lt requested max_cols)
        (fun _ => @Nat.le.refl (UInt64.toNat max_cols))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : CaptureReplayState) (hInit : Init s) :
      CaptureDimBoundedInv s :=
      uint64_zero_le s.cols s.max_cols hInit

    theorem next_preserves_inv (s : CaptureReplayState) (s' : CaptureReplayState)
      (_hInv : CaptureDimBoundedInv s) (hNext : Next s s') :
      CaptureDimBoundedInv s' :=
      Exists.elim hNext (fun (requested : UInt64) (hEx : ∃ (max_cols : UInt64), s' = setColsAction requested max_cols s) =>
        Exists.elim hEx (fun (max_cols : UInt64) (hEq : s' = setColsAction requested max_cols s) =>
          Eq.mpr
            (congrArg (fun (st : CaptureReplayState) => CaptureDimBoundedInv st) hEq)
            (clamp_le_max requested max_cols)))

    theorem spec_satisfies_capture_dim_bounded :
      Satisfies (Runs Spec) (Always (Lift CaptureDimBoundedInv)) :=
      invariantSatisfies Spec CaptureDimBoundedInv init_establishes_inv next_preserves_inv

    end TlaCaptureBin
    end Live
    end Astream

    def capture_decisions_present_isl (decisions : USize) : Bool :=
      decide (0 < decisions)
}
