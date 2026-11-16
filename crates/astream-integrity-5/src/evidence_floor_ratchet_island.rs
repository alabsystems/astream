// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `evidence_floor_ratchet.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `evidence_floor_ratchet.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def ratchet_floor_clamp (cand_floor : UInt64) (proved_count : UInt64) : UInt64 :=
      if cand_floor < proved_count then cand_floor else proved_count

    def ratchet_floor_advance (cur_floor : UInt64) (cand_floor : UInt64) : UInt64 :=
      if cur_floor < cand_floor then cand_floor else cur_floor

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Floor Ratchet Spec
    -- =======================================================================

    namespace Astream
    namespace Evidence
    namespace TlaProvedFloorRatchet

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

    structure FloorState where
      candidate_floor : UInt64
      max_proved : UInt64
      ratcheted_floor : UInt64
      prev_floor : UInt64

    def FloorInv (s : FloorState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.candidate_floor) (UInt64.toNat s.max_proved))
        (Nat.le (UInt64.toNat s.prev_floor) (UInt64.toNat s.ratcheted_floor))

    def Init (max_proved : UInt64) (s : FloorState) : Prop :=
      And
        (And (s.candidate_floor = 0) (s.max_proved = max_proved))
        (And (s.ratcheted_floor = 0) (s.prev_floor = 0))

    def ratchetStep (cand_floor : UInt64) (s : FloorState) : FloorState :=
      let bounded := _root_.ratchet_floor_clamp cand_floor s.max_proved
      FloorState.mk
        bounded
        s.max_proved
        (_root_.ratchet_floor_advance s.ratcheted_floor bounded)
        s.ratcheted_floor

    def Next (s : FloorState) (s' : FloorState) : Prop :=
      ∃ (cand_floor : UInt64),
        s' = ratchetStep cand_floor s

    def Spec (max_proved : UInt64) : StateMachine FloorState :=
      StateMachine.mk (Init max_proved) Next

    theorem floor_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.ratchet_floor_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem floor_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.ratchet_floor_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_proved : UInt64) (s : FloorState)
      (hInit : Init max_proved s) :
      FloorInv s :=
      And.intro
        (eq_zero_le s.candidate_floor s.max_proved (And.left (And.left hInit)))
        (eq_zero_le s.prev_floor s.ratcheted_floor (And.right (And.right hInit)))

    theorem next_preserves_inv (s : FloorState) (s' : FloorState)
      (_hInv : FloorInv s) (hNext : Next s s') :
      FloorInv s' :=
      Exists.elim hNext (fun (cf : UInt64) (hEq : s' = ratchetStep cf s) =>
        Eq.mpr
          (congrArg (fun (st : FloorState) => FloorInv st) hEq)
          (And.intro
            (floor_clamp_le cf s.max_proved)
            (floor_monotone s.ratcheted_floor (_root_.ratchet_floor_clamp cf s.max_proved))))

    theorem proved_floor_ratchet_safety_always (max_proved : UInt64) :
      Satisfies (Runs (Spec max_proved)) (Always (Lift FloorInv)) :=
      invariantSatisfies (Spec max_proved) FloorInv (init_establishes_inv max_proved) next_preserves_inv

    end TlaProvedFloorRatchet
    end Evidence
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def ratchet_floor_within_proved_isl (floor_val : UInt64) (proved_val : UInt64) : Bool :=
      decide (floor_val <= proved_val)
}
