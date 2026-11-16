// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `sasl.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `sasl.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def kafka_sasl_phase_advance (cur_phase : UInt64) (next_phase : UInt64) : UInt64 :=
      if cur_phase < next_phase then next_phase else cur_phase

    def kafka_sasl_pbkdf2_clamp (iters : UInt64) (max_iters : UInt64) : UInt64 :=
      if iters < max_iters then iters else max_iters

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & SASL Auth State Machine
    -- =======================================================================

    namespace Astream
    namespace Kafka
    namespace TlaSaslAuth

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

    -- Phases:
    --   0 = Unauthenticated
    --   1 = Handshaken
    --   2 = ScramChallenge
    --   3 = Authenticated
    --   4 = Failed (terminal absorbing state >= 4)
    structure SaslState where
      prev_phase : UInt64
      phase : UInt64
      max_iters : UInt64
      chosen_iters : UInt64

    def SaslSafetyInv (s : SaslState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_phase) (UInt64.toNat s.phase))
        (Nat.le (UInt64.toNat s.chosen_iters) (UInt64.toNat s.max_iters))

    def Init (s : SaslState) : Prop :=
      And
        (s.prev_phase = s.phase)
        (Nat.le (UInt64.toNat s.chosen_iters) (UInt64.toNat s.max_iters))

    def stepAuthAction (proposed_phase : UInt64) (req_iters : UInt64) (s : SaslState) : SaslState :=
      SaslState.mk
        s.phase
        (_root_.kafka_sasl_phase_advance s.phase proposed_phase)
        s.max_iters
        (_root_.kafka_sasl_pbkdf2_clamp req_iters s.max_iters)

    def Next (s : SaslState) (s' : SaslState) : Prop :=
      ∃ (proposed_phase : UInt64), ∃ (req_iters : UInt64),
        s' = stepAuthAction proposed_phase req_iters s

    def Spec : StateMachine SaslState :=
      StateMachine.mk Init Next

    theorem advance_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.kafka_sasl_phase_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem clamp_le_max : forall (req : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kafka_sasl_pbkdf2_clamp req cap)) (UInt64.toNat cap) :=
      fun req cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt req cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => req))) (UInt64.toNat cap))
        (instDecidableUInt64Lt req cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : SaslState) (hInit : Init s) :
      SaslSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_phase s.phase (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : SaslState) (s' : SaslState)
      (_hInv : SaslSafetyInv s) (hNext : Next s s') :
      SaslSafetyInv s' :=
      Exists.elim hNext (fun (proposed_phase : UInt64) (hRest : ∃ (req_iters : UInt64), s' = stepAuthAction proposed_phase req_iters s) =>
        Exists.elim hRest (fun (req_iters : UInt64) (hEq : s' = stepAuthAction proposed_phase req_iters s) =>
          Eq.mpr
            (congrArg (fun (st : SaslState) => SaslSafetyInv st) hEq)
            (And.intro
              (advance_ge_prev s.phase proposed_phase)
              (clamp_le_max req_iters s.max_iters))))

    theorem sasl_safety_always :
      Satisfies (Runs Spec) (Always (Lift SaslSafetyInv)) :=
      invariantSatisfies Spec SaslSafetyInv init_establishes_inv next_preserves_inv

    end TlaSaslAuth
    end Kafka
    end Astream

    def kafka_sasl_is_authenticated_isl (phase : UInt64) : Bool :=
      decide (phase = 3)
}
