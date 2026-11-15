// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `privacy_consent_classifier.rs`, out of line so that only a Trust compiler
// opens it: no stock rustc can lex `clean { ... }`. `privacy_consent_classifier.rs` mounts this
// file under `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def tcc_denial_clamp (cand_denials : UInt64) (max_denials : UInt64) : UInt64 :=
      if cand_denials < max_denials then cand_denials else max_denials

    def tcc_audit_seq_advance (cur_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if cur_seq < cand_seq then cand_seq else cur_seq

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & TCC Privacy Guard Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaMacPrivacyConsent

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

    structure TccState where
      denial_count : UInt64
      max_denials : UInt64
      audit_seq : UInt64
      prev_seq : UInt64

    def TccInv (s : TccState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.denial_count) (UInt64.toNat s.max_denials))
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.audit_seq))

    def Init (max_denials : UInt64) (s : TccState) : Prop :=
      And
        (And (s.denial_count = 0) (s.max_denials = max_denials))
        (And (s.audit_seq = 0) (s.prev_seq = 0))

    def tccStep (cand_denials : UInt64) (cand_seq : UInt64) (s : TccState) : TccState :=
      TccState.mk
        (_root_.tcc_denial_clamp cand_denials s.max_denials)
        s.max_denials
        (_root_.tcc_audit_seq_advance s.audit_seq cand_seq)
        s.audit_seq

    def Next (s : TccState) (s' : TccState) : Prop :=
      ∃ (cand_denials : UInt64), ∃ (cand_seq : UInt64),
        s' = tccStep cand_denials cand_seq s

    def Spec (max_denials : UInt64) : StateMachine TccState :=
      StateMachine.mk (Init max_denials) Next

    theorem denial_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.tcc_denial_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem audit_seq_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.tcc_audit_seq_advance cur cand)) :=
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

    theorem init_establishes_inv (max_denials : UInt64) (s : TccState)
      (hInit : Init max_denials s) :
      TccInv s :=
      And.intro
        (eq_zero_le s.denial_count s.max_denials (And.left (And.left hInit)))
        (eq_zero_le s.prev_seq s.audit_seq (And.right (And.right hInit)))

    theorem next_preserves_inv (s : TccState) (s' : TccState)
      (_hInv : TccInv s) (hNext : Next s s') :
      TccInv s' :=
      Exists.elim hNext (fun (cd : UInt64) (hRest : ∃ (cs : UInt64), s' = tccStep cd cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = tccStep cd cs s) =>
          Eq.mpr
            (congrArg (fun (st : TccState) => TccInv st) hEq)
            (And.intro
              (denial_clamp_le cd s.max_denials)
              (audit_seq_monotone s.audit_seq cs))))

    theorem mac_privacy_consent_safety_always (max_denials : UInt64) :
      Satisfies (Runs (Spec max_denials)) (Always (Lift TccInv)) :=
      invariantSatisfies (Spec max_denials) TccInv (init_establishes_inv max_denials) next_preserves_inv

    end TlaMacPrivacyConsent
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def tcc_denials_within_cap_isl (denials : UInt64) (max_denials : UInt64) : Bool :=
      decide (denials <= max_denials)
}
