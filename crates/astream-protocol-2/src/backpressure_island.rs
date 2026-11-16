// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `backpressure.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `backpressure.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def pump_queue_bytes_clamp (queued : UInt64) (high_watermark : UInt64) : UInt64 :=
      if queued < high_watermark then queued else high_watermark

    def pump_flushed_batches_advance (prev_batches : UInt64) (cand_batches : UInt64) : UInt64 :=
      if prev_batches < cand_batches then cand_batches else prev_batches

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Pump Backpressure Spec
    -- =======================================================================

    namespace Astream
    namespace Pump
    namespace TlaPumpBackpressure

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

    structure PumpBackpressureState where
      queued_bytes : UInt64
      high_watermark : UInt64
      flushed_batches : UInt64
      prev_flushed : UInt64

    def PumpBackpressureInv (s : PumpBackpressureState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.queued_bytes) (UInt64.toNat s.high_watermark))
        (Nat.le (UInt64.toNat s.prev_flushed) (UInt64.toNat s.flushed_batches))

    def Init (s : PumpBackpressureState) : Prop :=
      And
        (s.queued_bytes = 0)
        (And (s.flushed_batches = 0) (s.prev_flushed = 0))

    def bpStep (raw_queued : UInt64) (cand_flushed : UInt64) (s : PumpBackpressureState) : PumpBackpressureState :=
      PumpBackpressureState.mk
        (_root_.pump_queue_bytes_clamp raw_queued s.high_watermark)
        s.high_watermark
        (_root_.pump_flushed_batches_advance s.flushed_batches cand_flushed)
        s.flushed_batches

    def Next (s : PumpBackpressureState) (s' : PumpBackpressureState) : Prop :=
      ∃ (raw_queued : UInt64), ∃ (cand_flushed : UInt64),
        s' = bpStep raw_queued cand_flushed s

    def Spec : StateMachine PumpBackpressureState :=
      StateMachine.mk Init Next

    theorem queued_le_hwm : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.pump_queue_bytes_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem flushed_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.pump_flushed_batches_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
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

    theorem init_establishes_inv (s : PumpBackpressureState) (hInit : Init s) :
      PumpBackpressureInv s :=
      And.intro
        (zero_le_cap s.queued_bytes s.high_watermark (And.left hInit))
        (eq_zero_le
          s.prev_flushed
          s.flushed_batches
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : PumpBackpressureState) (s' : PumpBackpressureState)
      (_hInv : PumpBackpressureInv s) (hNext : Next s s') :
      PumpBackpressureInv s' :=
      Exists.elim hNext (fun (rq : UInt64) (hRest : ∃ (cf : UInt64), s' = bpStep rq cf s) =>
        Exists.elim hRest (fun (cf : UInt64) (hEq : s' = bpStep rq cf s) =>
          Eq.mpr
            (congrArg (fun (st : PumpBackpressureState) => PumpBackpressureInv st) hEq)
            (And.intro
              (queued_le_hwm rq s.high_watermark)
              (flushed_monotone s.flushed_batches cf))))

    theorem pump_backpressure_safety_always :
      Satisfies (Runs Spec) (Always (Lift PumpBackpressureInv)) :=
      invariantSatisfies Spec PumpBackpressureInv init_establishes_inv next_preserves_inv

    end TlaPumpBackpressure
    end Pump
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def pump_should_throttle_pty_isl (queued_bytes : UInt64) (high_watermark : UInt64) : Bool :=
      decide (high_watermark ≤ queued_bytes)
}
