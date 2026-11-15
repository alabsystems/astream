// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `restart_handoff.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `restart_handoff.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def restart_handoff_bytes_clamp (cand_bytes : UInt64) (byte_cap : UInt64) : UInt64 :=
      if cand_bytes < byte_cap then cand_bytes else byte_cap

    def restart_gen_advance (cur_gen : UInt64) (cand_gen : UInt64) : UInt64 :=
      if cur_gen < cand_gen then cand_gen else cur_gen

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Self-Restart Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaSelfRestartValidator

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

    structure RestartValidatorState where
      handoff_bytes : UInt64
      byte_cap : UInt64
      restart_gen : UInt64
      prev_gen : UInt64

    def SelfRestartValidatorInv (s : RestartValidatorState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.handoff_bytes) (UInt64.toNat s.byte_cap))
        (Nat.le (UInt64.toNat s.prev_gen) (UInt64.toNat s.restart_gen))

    def Init (byte_cap : UInt64) (s : RestartValidatorState) : Prop :=
      And
        (And (s.handoff_bytes = 0) (s.byte_cap = byte_cap))
        (And (s.restart_gen = 0) (s.prev_gen = 0))

    def restartStep (cand_bytes : UInt64) (cand_gen : UInt64) (s : RestartValidatorState) : RestartValidatorState :=
      RestartValidatorState.mk
        (_root_.restart_handoff_bytes_clamp cand_bytes s.byte_cap)
        s.byte_cap
        (_root_.restart_gen_advance s.restart_gen cand_gen)
        s.restart_gen

    def Next (s : RestartValidatorState) (s' : RestartValidatorState) : Prop :=
      ∃ (cand_bytes : UInt64), ∃ (cand_gen : UInt64),
        s' = restartStep cand_bytes cand_gen s

    def Spec (byte_cap : UInt64) : StateMachine RestartValidatorState :=
      StateMachine.mk (Init byte_cap) Next

    theorem handoff_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.restart_handoff_bytes_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem gen_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.restart_gen_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (byte_cap : UInt64) (s : RestartValidatorState)
      (hInit : Init byte_cap s) :
      SelfRestartValidatorInv s :=
      And.intro
        (eq_zero_le s.handoff_bytes s.byte_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_gen s.restart_gen (And.right (And.right hInit)))

    theorem next_preserves_inv (s : RestartValidatorState) (s' : RestartValidatorState)
      (_hInv : SelfRestartValidatorInv s) (hNext : Next s s') :
      SelfRestartValidatorInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (cg : UInt64), s' = restartStep cb cg s) =>
        Exists.elim hRest (fun (cg : UInt64) (hEq : s' = restartStep cb cg s) =>
          Eq.mpr
            (congrArg (fun (st : RestartValidatorState) => SelfRestartValidatorInv st) hEq)
            (And.intro
              (handoff_clamp_le cb s.byte_cap)
              (gen_monotone s.restart_gen cg))))

    theorem self_restart_validator_safety_always (byte_cap : UInt64) :
      Satisfies (Runs (Spec byte_cap)) (Always (Lift SelfRestartValidatorInv)) :=
      invariantSatisfies (Spec byte_cap) SelfRestartValidatorInv (init_establishes_inv byte_cap) next_preserves_inv

    end TlaSelfRestartValidator
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def restart_handoff_within_cap_isl (handoff_bytes : UInt64) (byte_cap : UInt64) : Bool :=
      decide (handoff_bytes <= byte_cap)
}
