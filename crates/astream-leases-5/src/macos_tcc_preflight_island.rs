// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for macOS TCC privacy-consent pre-flight classification
// (`Astream.Cap.TlaPrivacyConsentGate`), mounted under `cfg(clean_islands)` in
// `privacy_gate.rs` (`aterm ctl privacy` & Full Disk Access boundary rules).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def tcc_fda_folder_risk (fda_granted : UInt64) : UInt64 :=
      if fda_granted < 1 then 1 else 0

    def tcc_class_ge2_select (surface_class : UInt64) (class1_risk : UInt64) : UInt64 :=
      if surface_class < 2 then class1_risk else 2

    def tcc_class0_select (surface_class : UInt64) (nonzero_risk : UInt64) : UInt64 :=
      if surface_class < 1 then 0 else nonzero_risk

    def tcc_grant_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Cap.TlaPrivacyConsentGate)
    -- ========================================================================
    namespace Astream
    namespace Cap
    namespace TlaPrivacyConsentGate

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

    def tcc_risk_code_isl (surface_class : UInt64) (fda_granted : UInt64) : UInt64 :=
      _root_.tcc_class0_select
        surface_class
        (_root_.tcc_class_ge2_select surface_class (_root_.tcc_fda_folder_risk fda_granted))

    theorem fda_risk_le_two : forall (fda : UInt64),
        Nat.le (UInt64.toNat (_root_.tcc_fda_folder_risk fda)) (UInt64.toNat 2) :=
      fun fda => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt fda 1)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => (0 : UInt64)) (fun _ => (1 : UInt64)))) (UInt64.toNat 2))
        (instDecidableUInt64Lt fda 1)
        (fun _ => Nat.zero_le (UInt64.toNat 2))
        (fun _ => @Nat.le.step 1 1 (@Nat.le.refl 1))

    theorem class_ge2_le_two (sc : UInt64) (r1 : UInt64)
        (h1 : Nat.le (UInt64.toNat r1) (UInt64.toNat 2)) :
        Nat.le (UInt64.toNat (_root_.tcc_class_ge2_select sc r1)) (UInt64.toNat 2) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt sc 2)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => (2 : UInt64)) (fun _ => r1))) (UInt64.toNat 2))
        (instDecidableUInt64Lt sc 2)
        (fun _ => @Nat.le.refl (UInt64.toNat 2))
        (fun _ => h1)

    theorem class0_le_two (sc : UInt64) (rnz : UInt64)
        (h2 : Nat.le (UInt64.toNat rnz) (UInt64.toNat 2)) :
        Nat.le (UInt64.toNat (_root_.tcc_class0_select sc rnz)) (UInt64.toNat 2) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt sc 1)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => rnz) (fun _ => (0 : UInt64)))) (UInt64.toNat 2))
        (instDecidableUInt64Lt sc 1)
        (fun _ => h2)
        (fun _ => Nat.zero_le (UInt64.toNat 2))

    theorem risk_code_bounded (sc : UInt64) (fda : UInt64) :
        Nat.le (UInt64.toNat (tcc_risk_code_isl sc fda)) (UInt64.toNat 2) :=
      class0_le_two sc
        (_root_.tcc_class_ge2_select sc (_root_.tcc_fda_folder_risk fda))
        (class_ge2_le_two sc (_root_.tcc_fda_folder_risk fda) (fda_risk_le_two fda))

    theorem epoch_advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.tcc_grant_epoch_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    structure PrivacyGateState where
      prevEpoch : UInt64
      epoch : UInt64
      lastRisk : UInt64

    def PrivacyGateSafetyInv (s : PrivacyGateState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prevEpoch) (UInt64.toNat s.epoch))
        (Nat.le (UInt64.toNat s.lastRisk) (UInt64.toNat 2))

    def Init (s : PrivacyGateState) : Prop :=
      And
        (s.prevEpoch = s.epoch)
        (Nat.le (UInt64.toNat s.lastRisk) (UInt64.toNat 2))

    def evalStep (sc : UInt64) (fda : UInt64) (ce : UInt64) (s : PrivacyGateState) : PrivacyGateState :=
      PrivacyGateState.mk
        s.epoch
        (_root_.tcc_grant_epoch_advance s.epoch ce)
        (tcc_risk_code_isl sc fda)

    def Next (s : PrivacyGateState) (s' : PrivacyGateState) : Prop :=
      ∃ (sc : UInt64), ∃ (fda : UInt64), ∃ (ce : UInt64), s' = evalStep sc fda ce s

    def Spec : StateMachine PrivacyGateState :=
      StateMachine.mk Init Next

    theorem init_establishes_inv (s : PrivacyGateState) (hInit : Init s) :
      PrivacyGateSafetyInv s :=
      And.intro
        (uint64_eq_le s.prevEpoch s.epoch (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : PrivacyGateState) (s' : PrivacyGateState)
      (_hInv : PrivacyGateSafetyInv s) (hNext : Next s s') :
      PrivacyGateSafetyInv s' :=
      Exists.elim hNext (fun (sc : UInt64) (h1 : ∃ (fda : UInt64), ∃ (ce : UInt64), s' = evalStep sc fda ce s) =>
        Exists.elim h1 (fun (fda : UInt64) (h2 : ∃ (ce : UInt64), s' = evalStep sc fda ce s) =>
          Exists.elim h2 (fun (ce : UInt64) (hEq : s' = evalStep sc fda ce s) =>
            Eq.mpr
              (congrArg (fun (st : PrivacyGateState) => PrivacyGateSafetyInv st) hEq)
              (And.intro
                (epoch_advance_ge_cur s.epoch ce)
                (risk_code_bounded sc fda)))))

    theorem spec_satisfies_privacy_consent_safety :
      Satisfies (Runs Spec) (Always (Lift PrivacyGateSafetyInv)) :=
      invariantSatisfies Spec PrivacyGateSafetyInv init_establishes_inv next_preserves_inv

    end TlaPrivacyConsentGate
    end Cap
    end Astream

    def tcc_probe_safe_without_dialog_isl (risk_code : UInt64) : Bool :=
      decide (risk_code = 0)
}
