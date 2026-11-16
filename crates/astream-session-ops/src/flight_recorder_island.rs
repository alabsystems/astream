// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `flight_recorder.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `flight_recorder.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def flight_ring_bytes_clamp (cur_bytes : UInt64) (max_bytes : UInt64) : UInt64 :=
      if cur_bytes < max_bytes then cur_bytes else max_bytes

    def flight_pin_epoch_advance (prev_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if prev_epoch < cand_epoch then cand_epoch else prev_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & §3.3 Flight Recorder Spec
    -- =======================================================================

    namespace Astream
    namespace Engine
    namespace TlaFlightRecorder

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

    structure FlightRecorderState where
      ring_bytes : UInt64
      max_bytes : UInt64
      pin_epoch : UInt64
      prev_epoch : UInt64

    def FlightRecorderInv (s : FlightRecorderState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.ring_bytes) (UInt64.toNat s.max_bytes))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.pin_epoch))

    def Init (s : FlightRecorderState) : Prop :=
      And
        (s.ring_bytes = 0)
        (And (s.pin_epoch = 0) (s.prev_epoch = 0))

    def recorderStep (raw_bytes : UInt64) (cand_epoch : UInt64) (s : FlightRecorderState) : FlightRecorderState :=
      FlightRecorderState.mk
        (_root_.flight_ring_bytes_clamp raw_bytes s.max_bytes)
        s.max_bytes
        (_root_.flight_pin_epoch_advance s.pin_epoch cand_epoch)
        s.pin_epoch

    def Next (s : FlightRecorderState) (s' : FlightRecorderState) : Prop :=
      ∃ (raw_bytes : UInt64), ∃ (cand_epoch : UInt64),
        s' = recorderStep raw_bytes cand_epoch s

    def Spec : StateMachine FlightRecorderState :=
      StateMachine.mk Init Next

    theorem bytes_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.flight_ring_bytes_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.flight_pin_epoch_advance prev cand)) :=
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

    theorem init_establishes_inv (s : FlightRecorderState) (hInit : Init s) :
      FlightRecorderInv s :=
      And.intro
        (zero_le_cap s.ring_bytes s.max_bytes (And.left hInit))
        (eq_zero_le
          s.prev_epoch
          s.pin_epoch
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : FlightRecorderState) (s' : FlightRecorderState)
      (_hInv : FlightRecorderInv s) (hNext : Next s s') :
      FlightRecorderInv s' :=
      Exists.elim hNext (fun (rb : UInt64) (hRest : ∃ (ce : UInt64), s' = recorderStep rb ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = recorderStep rb ce s) =>
          Eq.mpr
            (congrArg (fun (st : FlightRecorderState) => FlightRecorderInv st) hEq)
            (And.intro
              (bytes_le_max rb s.max_bytes)
              (epoch_monotone s.pin_epoch ce))))

    theorem flight_recorder_safety_always :
      Satisfies (Runs Spec) (Always (Lift FlightRecorderInv)) :=
      invariantSatisfies Spec FlightRecorderInv init_establishes_inv next_preserves_inv

    end TlaFlightRecorder
    end Engine
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def flight_evict_permitted_isl (pinned : Bool) (cur_bytes : UInt64) (max_bytes : UInt64) : Bool :=
      and (not pinned) (decide (max_bytes < cur_bytes))
}
