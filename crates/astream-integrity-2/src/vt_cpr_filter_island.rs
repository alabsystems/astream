// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `vt_cpr_filter.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `vt_cpr_filter.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def vt_query_strip_clamp (cand_stripped : UInt64) (strip_cap : UInt64) : UInt64 :=
      if cand_stripped < strip_cap then cand_stripped else strip_cap

    def vt_sanitize_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Reply Sanitizer Spec
    -- =======================================================================

    namespace Astream
    namespace Pump
    namespace TlaTerminalReplySanitizer

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

    structure ReplySanitizerState where
      stripped_queries : UInt64
      strip_cap : UInt64
      sanitize_epoch : UInt64
      prev_epoch : UInt64

    def TerminalReplySanitizerInv (s : ReplySanitizerState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.stripped_queries) (UInt64.toNat s.strip_cap))
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.sanitize_epoch))

    def Init (strip_cap : UInt64) (s : ReplySanitizerState) : Prop :=
      And
        (And (s.stripped_queries = 0) (s.strip_cap = strip_cap))
        (And (s.sanitize_epoch = 0) (s.prev_epoch = 0))

    def sanitizeStep (cand_stripped : UInt64) (cand_epoch : UInt64) (s : ReplySanitizerState) : ReplySanitizerState :=
      ReplySanitizerState.mk
        (_root_.vt_query_strip_clamp cand_stripped s.strip_cap)
        s.strip_cap
        (_root_.vt_sanitize_epoch_advance s.sanitize_epoch cand_epoch)
        s.sanitize_epoch

    def Next (s : ReplySanitizerState) (s' : ReplySanitizerState) : Prop :=
      ∃ (cand_stripped : UInt64), ∃ (cand_epoch : UInt64),
        s' = sanitizeStep cand_stripped cand_epoch s

    def Spec (strip_cap : UInt64) : StateMachine ReplySanitizerState :=
      StateMachine.mk (Init strip_cap) Next

    theorem strip_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.vt_query_strip_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.vt_sanitize_epoch_advance cur cand)) :=
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

    theorem init_establishes_inv (strip_cap : UInt64) (s : ReplySanitizerState)
      (hInit : Init strip_cap s) :
      TerminalReplySanitizerInv s :=
      And.intro
        (eq_zero_le s.stripped_queries s.strip_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_epoch s.sanitize_epoch (And.right (And.right hInit)))

    theorem next_preserves_inv (s : ReplySanitizerState) (s' : ReplySanitizerState)
      (_hInv : TerminalReplySanitizerInv s) (hNext : Next s s') :
      TerminalReplySanitizerInv s' :=
      Exists.elim hNext (fun (cs : UInt64) (hRest : ∃ (ce : UInt64), s' = sanitizeStep cs ce s) =>
        Exists.elim hRest (fun (ce : UInt64) (hEq : s' = sanitizeStep cs ce s) =>
          Eq.mpr
            (congrArg (fun (st : ReplySanitizerState) => TerminalReplySanitizerInv st) hEq)
            (And.intro
              (strip_clamp_le cs s.strip_cap)
              (epoch_monotone s.sanitize_epoch ce))))

    theorem terminal_reply_sanitizer_safety_always (strip_cap : UInt64) :
      Satisfies (Runs (Spec strip_cap)) (Always (Lift TerminalReplySanitizerInv)) :=
      invariantSatisfies (Spec strip_cap) TerminalReplySanitizerInv (init_establishes_inv strip_cap) next_preserves_inv

    end TlaTerminalReplySanitizer
    end Pump
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def vt_stripped_within_cap_isl (stripped : UInt64) (strip_cap : UInt64) : Bool :=
      decide (stripped <= strip_cap)
}
