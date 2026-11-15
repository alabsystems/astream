// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `outbox.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `outbox.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def outbox_committed_advance (prev_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if prev_seq < cand_seq then cand_seq else prev_seq

    def outbox_capacity_clamp (entries : UInt64) (max_entries : UInt64) : UInt64 :=
      if entries < max_entries then entries else max_entries

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Idempotent Outbox Spec
    -- =======================================================================

    namespace Astream
    namespace Effects
    namespace TlaEffectOutbox

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

    structure EffectOutboxState where
      committed_seq : UInt64
      prev_committed : UInt64
      active_entries : UInt64
      max_entries : UInt64

    def EffectOutboxInv (s : EffectOutboxState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_committed) (UInt64.toNat s.committed_seq))
        (Nat.le (UInt64.toNat s.active_entries) (UInt64.toNat s.max_entries))

    def Init (s : EffectOutboxState) : Prop :=
      And
        (s.active_entries = 0)
        (And (s.committed_seq = 0) (s.prev_committed = 0))

    def outboxStep (cand_seq : UInt64) (raw_entries : UInt64) (s : EffectOutboxState) : EffectOutboxState :=
      EffectOutboxState.mk
        (_root_.outbox_committed_advance s.committed_seq cand_seq)
        s.committed_seq
        (_root_.outbox_capacity_clamp raw_entries s.max_entries)
        s.max_entries

    def Next (s : EffectOutboxState) (s' : EffectOutboxState) : Prop :=
      ∃ (cand_seq : UInt64), ∃ (raw_entries : UInt64),
        s' = outboxStep cand_seq raw_entries s

    def Spec : StateMachine EffectOutboxState :=
      StateMachine.mk Init Next

    theorem committed_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.outbox_committed_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem entries_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.outbox_capacity_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : EffectOutboxState) (hInit : Init s) :
      EffectOutboxInv s :=
      And.intro
        (eq_zero_le
          s.prev_committed
          s.committed_seq
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.active_entries s.max_entries (And.left hInit))

    theorem next_preserves_inv (s : EffectOutboxState) (s' : EffectOutboxState)
      (_hInv : EffectOutboxInv s) (hNext : Next s s') :
      EffectOutboxInv s' :=
      Exists.elim hNext (fun (cs : UInt64) (hRest : ∃ (re : UInt64), s' = outboxStep cs re s) =>
        Exists.elim hRest (fun (re : UInt64) (hEq : s' = outboxStep cs re s) =>
          Eq.mpr
            (congrArg (fun (st : EffectOutboxState) => EffectOutboxInv st) hEq)
            (And.intro
              (committed_monotone s.committed_seq cs)
              (entries_le_max re s.max_entries))))

    theorem effect_outbox_safety_always :
      Satisfies (Runs Spec) (Always (Lift EffectOutboxInv)) :=
      invariantSatisfies Spec EffectOutboxInv init_establishes_inv next_preserves_inv

    end TlaEffectOutbox
    end Effects
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def outbox_is_duplicate_isl (effect_seq : UInt64) (committed_seq : UInt64) : Bool :=
      decide (effect_seq ≤ committed_seq)
}
