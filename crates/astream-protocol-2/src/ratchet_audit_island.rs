// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `ratchet_audit.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `ratchet_audit.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def floor_ratchet_advance (prev_floor : UInt64) (cand_floor : UInt64) : UInt64 :=
      if prev_floor < cand_floor then cand_floor else prev_floor

    def floor_target_clamp (target : UInt64) (proved : UInt64) : UInt64 :=
      if target < proved then target else proved

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Proof-Floor Ratchet Spec
    -- =======================================================================

    namespace Astream
    namespace Evidence
    namespace TlaFloorRatchet

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

    structure FloorRatchetState where
      floor : UInt64
      prev_floor : UInt64
      recommended : UInt64
      proved_cap : UInt64

    def FloorRatchetInv (s : FloorRatchetState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_floor) (UInt64.toNat s.floor))
        (Nat.le (UInt64.toNat s.recommended) (UInt64.toNat s.proved_cap))

    def Init (s : FloorRatchetState) : Prop :=
      And
        (s.recommended = 0)
        (And (s.floor = 0) (s.prev_floor = 0))

    def ratchetFloorStep (cand_floor : UInt64) (raw_rec : UInt64) (s : FloorRatchetState) : FloorRatchetState :=
      FloorRatchetState.mk
        (_root_.floor_ratchet_advance s.floor cand_floor)
        s.floor
        (_root_.floor_target_clamp raw_rec s.proved_cap)
        s.proved_cap

    def Next (s : FloorRatchetState) (s' : FloorRatchetState) : Prop :=
      ∃ (cand_floor : UInt64), ∃ (raw_rec : UInt64),
        s' = ratchetFloorStep cand_floor raw_rec s

    def Spec : StateMachine FloorRatchetState :=
      StateMachine.mk Init Next

    theorem floor_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.floor_ratchet_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem rec_le_proved : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.floor_target_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : FloorRatchetState) (hInit : Init s) :
      FloorRatchetInv s :=
      And.intro
        (eq_zero_le
          s.prev_floor
          s.floor
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.recommended s.proved_cap (And.left hInit))

    theorem next_preserves_inv (s : FloorRatchetState) (s' : FloorRatchetState)
      (_hInv : FloorRatchetInv s) (hNext : Next s s') :
      FloorRatchetInv s' :=
      Exists.elim hNext (fun (cf : UInt64) (hRest : ∃ (rr : UInt64), s' = ratchetFloorStep cf rr s) =>
        Exists.elim hRest (fun (rr : UInt64) (hEq : s' = ratchetFloorStep cf rr s) =>
          Eq.mpr
            (congrArg (fun (st : FloorRatchetState) => FloorRatchetInv st) hEq)
            (And.intro
              (floor_monotone s.floor cf)
              (rec_le_proved rr s.proved_cap))))

    theorem floor_ratchet_safety_always :
      Satisfies (Runs Spec) (Always (Lift FloorRatchetInv)) :=
      invariantSatisfies Spec FloorRatchetInv init_establishes_inv next_preserves_inv

    end TlaFloorRatchet
    end Evidence
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def floor_meets_bar_isl (proved : UInt64) (floor : UInt64) : Bool :=
      decide (floor ≤ proved)
}
