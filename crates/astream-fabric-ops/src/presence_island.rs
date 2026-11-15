// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `presence.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `presence.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def presence_watchers_clamp (count : UInt64) (max_watchers : UInt64) : UInt64 :=
      if count < max_watchers then count else max_watchers

    def presence_field_clamp (field_len : UInt64) (max_len : UInt64) : UInt64 :=
      if field_len < max_len then field_len else max_len

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & §4.2 Presence Row Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaPresenceRow

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

    structure PresenceRowState where
      watchers : UInt64
      max_watchers : UInt64
      field_len : UInt64
      max_field_len : UInt64

    def PresenceRowInv (s : PresenceRowState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.watchers) (UInt64.toNat s.max_watchers))
        (Nat.le (UInt64.toNat s.field_len) (UInt64.toNat s.max_field_len))

    def Init (s : PresenceRowState) : Prop :=
      And
        (s.watchers = 0)
        (s.field_len = 0)

    def updateRowStep (raw_watchers : UInt64) (raw_field : UInt64) (s : PresenceRowState) : PresenceRowState :=
      PresenceRowState.mk
        (_root_.presence_watchers_clamp raw_watchers s.max_watchers)
        s.max_watchers
        (_root_.presence_field_clamp raw_field s.max_field_len)
        s.max_field_len

    def Next (s : PresenceRowState) (s' : PresenceRowState) : Prop :=
      ∃ (raw_watchers : UInt64), ∃ (raw_field : UInt64),
        s' = updateRowStep raw_watchers raw_field s

    def Spec : StateMachine PresenceRowState :=
      StateMachine.mk Init Next

    theorem watchers_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.presence_watchers_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem field_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.presence_field_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : PresenceRowState) (hInit : Init s) :
      PresenceRowInv s :=
      And.intro
        (zero_le_cap s.watchers s.max_watchers (And.left hInit))
        (zero_le_cap s.field_len s.max_field_len (And.right hInit))

    theorem next_preserves_inv (s : PresenceRowState) (s' : PresenceRowState)
      (_hInv : PresenceRowInv s) (hNext : Next s s') :
      PresenceRowInv s' :=
      Exists.elim hNext (fun (rw : UInt64) (hRest : ∃ (rf : UInt64), s' = updateRowStep rw rf s) =>
        Exists.elim hRest (fun (rf : UInt64) (hEq : s' = updateRowStep rw rf s) =>
          Eq.mpr
            (congrArg (fun (st : PresenceRowState) => PresenceRowInv st) hEq)
            (And.intro
              (watchers_le_max rw s.max_watchers)
              (field_le_max rf s.max_field_len))))

    theorem presence_row_safety_always :
      Satisfies (Runs Spec) (Always (Lift PresenceRowInv)) :=
      invariantSatisfies Spec PresenceRowInv init_establishes_inv next_preserves_inv

    end TlaPresenceRow
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def presence_row_within_cap_isl (len : USize) (max_len : USize) : Bool :=
      decide (len ≤ max_len)
}
