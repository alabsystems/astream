// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `osc52_clipboard_guard.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `osc52_clipboard_guard.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def osc52_payload_clamp (cand_bytes : UInt64) (max_bytes : UInt64) : UInt64 :=
      if cand_bytes < max_bytes then cand_bytes else max_bytes

    def osc52_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & OSC 52 Clipboard Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaOsc52ClipboardGuard

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

    structure Osc52State where
      copied_bytes : UInt64
      max_copy_bytes : UInt64
      copy_epoch : UInt64
      prev_epoch : UInt64

    def Osc52Inv (s : Osc52State) : Prop :=
      And
        (Nat.le (UInt64.toNat s.copied_bytes) (UInt64.toNat s.max_copy_bytes))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.copy_epoch))

    def Init (max_copy_bytes : UInt64) (s : Osc52State) : Prop :=
      And
        (And (s.copied_bytes = 0) (s.max_copy_bytes = max_copy_bytes))
        (And (s.copy_epoch = 0) (s.prev_epoch = 0))

    def osc52Step (cand_bytes : UInt64) (cand_epoch : UInt64) (s : Osc52State) : Osc52State :=
      Osc52State.mk
        (_root_.osc52_payload_clamp cand_bytes s.max_copy_bytes)
        s.max_copy_bytes
        (_root_.osc52_epoch_advance s.copy_epoch cand_epoch)
        s.copy_epoch

    def Next (s : Osc52State) (s' : Osc52State) : Prop :=
      ∃ (cand_bytes : UInt64), ∃ (cand_epoch : UInt64),
        s' = osc52Step cand_bytes cand_epoch s

    def Spec (max_copy_bytes : UInt64) : StateMachine Osc52State :=
      StateMachine.mk (Init max_copy_bytes) Next

    theorem payload_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.osc52_payload_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem copy_epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.osc52_epoch_advance cur cand)) :=
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

    theorem init_establishes_inv (max_copy_bytes : UInt64) (s : Osc52State)
      (hInit : Init max_copy_bytes s) :
      Osc52Inv s :=
      And.intro
        (eq_zero_le s.copied_bytes s.max_copy_bytes (And.left (And.left hInit)))
        (eq_zero_le s.prev_epoch s.copy_epoch (And.right (And.right hInit)))

    theorem next_preserves_inv (s : Osc52State) (s' : Osc52State)
      (_hInv : Osc52Inv s) (hNext : Next s s') :
      Osc52Inv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (ce : UInt64), s' = osc52Step cb ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = osc52Step cb ce s) =>
          Eq.mpr
            (congrArg (fun (st : Osc52State) => Osc52Inv st) hEq)
            (And.intro
              (payload_clamp_le cb s.max_copy_bytes)
              (copy_epoch_monotone s.copy_epoch ce))))

    theorem osc52_clipboard_guard_safety_always (max_copy_bytes : UInt64) :
      Satisfies (Runs (Spec max_copy_bytes)) (Always (Lift Osc52Inv)) :=
      invariantSatisfies (Spec max_copy_bytes) Osc52Inv (init_establishes_inv max_copy_bytes) next_preserves_inv

    end TlaOsc52ClipboardGuard
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def osc52_payload_within_max_isl (copied : UInt64) (max_bytes : UInt64) : Bool :=
      decide (copied <= max_bytes)
}
