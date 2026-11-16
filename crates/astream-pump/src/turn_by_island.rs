// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `turn_by.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `turn_by.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def turn_seq_advance (prev_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if prev_seq < cand_seq then cand_seq else prev_seq

    def turn_driver_len_clamp (driver_len : UInt64) (max_len : UInt64) : UInt64 :=
      if driver_len < max_len then driver_len else max_len

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Turn Attribution Spec
    -- =======================================================================

    namespace Astream
    namespace Pump
    namespace TlaTurnAttribution

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

    structure TurnAttributionState where
      emitted_seq : UInt64
      prev_seq : UInt64
      driver_len : UInt64
      max_driver_len : UInt64

    def TurnAttributionInv (s : TurnAttributionState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.emitted_seq))
        (Nat.le (UInt64.toNat s.driver_len) (UInt64.toNat s.max_driver_len))

    def Init (s : TurnAttributionState) : Prop :=
      And
        (s.driver_len = 0)
        (And (s.emitted_seq = 0) (s.prev_seq = 0))

    def turnStep (cand_seq : UInt64) (raw_len : UInt64) (s : TurnAttributionState) : TurnAttributionState :=
      TurnAttributionState.mk
        (_root_.turn_seq_advance s.emitted_seq cand_seq)
        s.emitted_seq
        (_root_.turn_driver_len_clamp raw_len s.max_driver_len)
        s.max_driver_len

    def Next (s : TurnAttributionState) (s' : TurnAttributionState) : Prop :=
      ∃ (cand_seq : UInt64), ∃ (raw_len : UInt64),
        s' = turnStep cand_seq raw_len s

    def Spec : StateMachine TurnAttributionState :=
      StateMachine.mk Init Next

    theorem seq_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.turn_seq_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem driver_len_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.turn_driver_len_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
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

    theorem init_establishes_inv (s : TurnAttributionState) (hInit : Init s) :
      TurnAttributionInv s :=
      And.intro
        (eq_zero_le
          s.prev_seq
          s.emitted_seq
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.driver_len s.max_driver_len (And.left hInit))

    theorem next_preserves_inv (s : TurnAttributionState) (s' : TurnAttributionState)
      (_hInv : TurnAttributionInv s) (hNext : Next s s') :
      TurnAttributionInv s' :=
      Exists.elim hNext (fun (cs : UInt64) (hRest : ∃ (rl : UInt64), s' = turnStep cs rl s) =>
        Exists.elim hRest (fun (rl : UInt64) (hEq : s' = turnStep cs rl s) =>
          Eq.mpr
            (congrArg (fun (st : TurnAttributionState) => TurnAttributionInv st) hEq)
            (And.intro
              (seq_monotone s.emitted_seq cs)
              (driver_len_le_max rl s.max_driver_len))))

    theorem turn_attribution_safety_always :
      Satisfies (Runs Spec) (Always (Lift TurnAttributionInv)) :=
      invariantSatisfies Spec TurnAttributionInv init_establishes_inv next_preserves_inv

    end TlaTurnAttribution
    end Pump
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def turn_attribution_valid_isl (cause_off : UInt64) (turn_off : UInt64) : Bool :=
      decide (cause_off ≤ turn_off)
}
