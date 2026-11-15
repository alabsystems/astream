// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `paste_guard.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `paste_guard.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def paste_bytes_clamp (paste_len : UInt64) (max_bytes : UInt64) : UInt64 :=
      if paste_len < max_bytes then paste_len else max_bytes

    def paste_threats_advance (prev_threats : UInt64) (cand_threats : UInt64) : UInt64 :=
      if prev_threats < cand_threats then cand_threats else prev_threats

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & DEC ?2004 Paste Guard Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaBracketedPaste

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

    structure PasteGuardState where
      admitted_bytes : UInt64
      max_bytes : UInt64
      scrubbed_threats : UInt64
      prev_threats : UInt64

    def PasteGuardInv (s : PasteGuardState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.admitted_bytes) (UInt64.toNat s.max_bytes))
        (Nat.le (UInt64.toNat s.prev_threats) (UInt64.toNat s.scrubbed_threats))

    def Init (s : PasteGuardState) : Prop :=
      And
        (s.admitted_bytes = 0)
        (And (s.scrubbed_threats = 0) (s.prev_threats = 0))

    def pasteStep (raw_bytes : UInt64) (cand_threats : UInt64) (s : PasteGuardState) : PasteGuardState :=
      PasteGuardState.mk
        (_root_.paste_bytes_clamp raw_bytes s.max_bytes)
        s.max_bytes
        (_root_.paste_threats_advance s.scrubbed_threats cand_threats)
        s.scrubbed_threats

    def Next (s : PasteGuardState) (s' : PasteGuardState) : Prop :=
      ∃ (raw_bytes : UInt64), ∃ (cand_threats : UInt64),
        s' = pasteStep raw_bytes cand_threats s

    def Spec : StateMachine PasteGuardState :=
      StateMachine.mk Init Next

    theorem bytes_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.paste_bytes_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem threats_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.paste_threats_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
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

    theorem init_establishes_inv (s : PasteGuardState) (hInit : Init s) :
      PasteGuardInv s :=
      And.intro
        (zero_le_cap s.admitted_bytes s.max_bytes (And.left hInit))
        (eq_zero_le
          s.prev_threats
          s.scrubbed_threats
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : PasteGuardState) (s' : PasteGuardState)
      (_hInv : PasteGuardInv s) (hNext : Next s s') :
      PasteGuardInv s' :=
      Exists.elim hNext (fun (rb : UInt64) (hRest : ∃ (ct : UInt64), s' = pasteStep rb ct s) =>
        Exists.elim hRest (fun (ct : UInt64) (hEq : s' = pasteStep rb ct s) =>
          Eq.mpr
            (congrArg (fun (st : PasteGuardState) => PasteGuardInv st) hEq)
            (And.intro
              (bytes_le_max rb s.max_bytes)
              (threats_monotone s.scrubbed_threats ct))))

    theorem paste_guard_safety_always :
      Satisfies (Runs Spec) (Always (Lift PasteGuardInv)) :=
      invariantSatisfies Spec PasteGuardInv init_establishes_inv next_preserves_inv

    end TlaBracketedPaste
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def paste_requires_confirm_isl (bracketed : Bool) (newline_count : USize) : Bool :=
      and (not bracketed) (decide (0 < newline_count))
}
