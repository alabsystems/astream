// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `foreign_tape.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `foreign_tape.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def foreign_tape_cursor_advance (prev : UInt64) (next : UInt64) : UInt64 :=
      if prev < next then next else prev

    def foreign_tape_clamp_records (count : UInt64) (max_records : UInt64) : UInt64 :=
      if count < max_records then count else max_records

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Foreign-Tape Splice Safety
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaForeignTape

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

    structure ForeignTapeState where
      prev_cursor : UInt64
      cursor : UInt64
      total : UInt64

    def ForeignTapeSafetyInv (s : ForeignTapeState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_cursor) (UInt64.toNat s.cursor))
        (Nat.le (UInt64.toNat s.cursor) (UInt64.toNat s.total))

    def Init (s : ForeignTapeState) : Prop :=
      And (s.prev_cursor = s.cursor) (Nat.le (UInt64.toNat s.cursor) (UInt64.toNat s.total))

    def spliceSpanAction (proposed : UInt64) (s : ForeignTapeState) : ForeignTapeState :=
      let clamped := _root_.foreign_tape_clamp_records proposed s.total
      let advanced := _root_.foreign_tape_cursor_advance s.cursor clamped
      ForeignTapeState.mk s.cursor advanced s.total

    def Next (s : ForeignTapeState) (s' : ForeignTapeState) : Prop :=
      ∃ (proposed : UInt64), s' = spliceSpanAction proposed s

    def Spec : StateMachine ForeignTapeState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (n : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.foreign_tape_clamp_records n cap)) (UInt64.toNat cap) :=
      fun n cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt n cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => n))) (UInt64.toNat cap))
        (instDecidableUInt64Lt n cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem advance_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.foreign_tape_cursor_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem advance_le_bound : forall (cur : UInt64) (proposed : UInt64) (bound : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat bound) →
        Nat.le (UInt64.toNat proposed) (UInt64.toNat bound) →
        Nat.le (UInt64.toNat (_root_.foreign_tape_cursor_advance cur proposed)) (UInt64.toNat bound) :=
      fun cur proposed bound hCur hProp => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => hCur)
        (fun _ => hProp)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : ForeignTapeState) (hInit : Init s) :
      ForeignTapeSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_cursor s.cursor (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : ForeignTapeState) (s' : ForeignTapeState)
      (hInv : ForeignTapeSafetyInv s) (hNext : Next s s') :
      ForeignTapeSafetyInv s' :=
      Exists.elim hNext (fun (proposed : UInt64) (hEq : s' = spliceSpanAction proposed s) =>
        Eq.mpr
          (congrArg (fun (st : ForeignTapeState) => ForeignTapeSafetyInv st) hEq)
          (And.intro
            (advance_ge_prev s.cursor (_root_.foreign_tape_clamp_records proposed s.total))
            (advance_le_bound
              s.cursor
              (_root_.foreign_tape_clamp_records proposed s.total)
              s.total
              (And.right hInv)
              (clamp_le_max proposed s.total))))

    theorem foreign_tape_safety_always :
      Satisfies (Runs Spec) (Always (Lift ForeignTapeSafetyInv)) :=
      invariantSatisfies Spec ForeignTapeSafetyInv init_establishes_inv next_preserves_inv

    end TlaForeignTape
    end Agent
    end Astream

    def foreign_tape_exhausted_isl (cursor : UInt64) (total : UInt64) : Bool :=
      decide (cursor = total)
}
