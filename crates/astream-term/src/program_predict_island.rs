// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `program_predict.rs`, out of line so that only a Trust compiler
// opens it: no stock rustc can lex `clean { ... }`. `program_predict.rs` mounts this file
// under `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is
// Trust. Every other compiler calls the plain-Rust twins in `twins.rs` of the functions
// it compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    -- Clamp the learned program-transition rule count to `cap` (`min(count, cap)`).
    def program_rule_cap_clamp (count : UInt64) (cap : UInt64) : UInt64 :=
      if count < cap then count else cap

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaProgramSpeculation)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaProgramSpeculation

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (k : Nat) (b : Behavior State) : Behavior State :=
      fun (n : Nat) => b (Nat.add k n)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (k : Nat), P (drop k b)
    prefix:90 "□" => _root_.Astream.Term.TlaProgramSpeculation.Always

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (k : Nat), M.Next (b k) (b (Nat.succ k)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (P : Formula State) : Prop :=
      ∀ (b : Behavior State), Runs M b → P b
    infix:50 " ⊨ " => _root_.Astream.Term.TlaProgramSpeculation.Satisfies

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
        (motive := fun j => Inv (b j))
        (hInit (b 0) hRun.1)
        (fun (j : Nat) (ih : Inv (b j)) =>
          hStep (b j) (b (Nat.succ j)) ih (hRun.2 j))
        k

    theorem invariantSatisfies
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s') :
      M ⊨ □ (Lift Inv) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        let hAt : Inv (b k) := invariantAt M Inv hInit hStep b hRun k
        let hEq : Nat.add k 0 = k := Nat.add_zero k
        Eq.mpr (congrArg (fun (idx : Nat) => Inv (b idx)) hEq) hAt

    -- ========================================================================
    -- 3. Program-Response Speculation (`P̂`) Confluence & Bounded-Cache Spec
    -- ========================================================================

    structure ProgramSpecState where
      authScreen   : Nat
      viewScreen   : Nat
      pendingCount : Nat
      ruleCount    : UInt64
      ruleCap      : UInt64

    -- Safety Invariant:
    -- 1. Ground-Truth Confluence: whenever all speculative transitions have retired
    --    or been squashed (`pendingCount = 0`), `viewScreen = authScreen`.
    -- 2. Bounded Rule Table: `ruleCount <= ruleCap`.
    def ProgramSpecSafetyInv (s : ProgramSpecState) : Prop :=
      (s.pendingCount = 0 → s.viewScreen = s.authScreen) ∧
      Nat.le (UInt64.toNat s.ruleCount) (UInt64.toNat s.ruleCap)

    def Init (s0 : Nat) (cap : UInt64) (s : ProgramSpecState) : Prop :=
      s.authScreen = s0 ∧
      s.viewScreen = s0 ∧
      s.pendingCount = 0 ∧
      s.ruleCount = (0 : UInt64) ∧
      s.ruleCap = cap

    def PredictTransition (specView : Nat) (s sNext : ProgramSpecState) : Prop :=
      sNext.authScreen = s.authScreen ∧
      sNext.viewScreen = specView ∧
      sNext.pendingCount = Nat.succ s.pendingCount ∧
      sNext.ruleCount = s.ruleCount ∧
      sNext.ruleCap = s.ruleCap

    def ReconcileGroundTruth (newAuth : Nat) (rawRules : UInt64) (s sNext : ProgramSpecState) : Prop :=
      sNext.authScreen = newAuth ∧
      sNext.viewScreen = newAuth ∧
      sNext.pendingCount = 0 ∧
      sNext.ruleCount = _root_.program_rule_cap_clamp rawRules s.ruleCap ∧
      sNext.ruleCap = s.ruleCap

    def Next (s sNext : ProgramSpecState) : Prop :=
      (∃ sv : Nat, PredictTransition sv s sNext) ∨
      (∃ na : Nat, ∃ rr : UInt64, ReconcileGroundTruth na rr s sNext)

    def Spec (s0 : Nat) (cap : UInt64) : StateMachine ProgramSpecState :=
      StateMachine.mk (Init s0 cap) Next

    theorem succ_ne_zero (n : Nat) (h : Nat.succ n = 0) : False :=
      Nat.noConfusion h

    theorem clamp_le_cap : forall (count : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.program_rule_cap_clamp count cap)) (UInt64.toNat cap) :=
      fun count cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt count cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => count))) (UInt64.toNat cap))
        (instDecidableUInt64Lt count cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem init_establishes_inv (s0 : Nat) (cap : UInt64) (s : ProgramSpecState)
        (hInit : Init s0 cap s) : ProgramSpecSafetyInv s :=
      let hConv : s.pendingCount = 0 → s.viewScreen = s.authScreen :=
        fun _ => Eq.trans hInit.2.1 (Eq.symm hInit.1)
      let hZeroLe : Nat.le (UInt64.toNat (0 : UInt64)) (UInt64.toNat s.ruleCap) :=
        Nat.zero_le (UInt64.toNat s.ruleCap)
      let hBounded : Nat.le (UInt64.toNat s.ruleCount) (UInt64.toNat s.ruleCap) :=
        Eq.mpr
          (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat s.ruleCap)) hInit.2.2.2.1)
          hZeroLe
      And.intro hConv hBounded

    theorem predictTransition_preserves_inv (sv : Nat) (s sNext : ProgramSpecState)
        (hInv : ProgramSpecSafetyInv s) (hAct : PredictTransition sv s sNext) :
        ProgramSpecSafetyInv sNext :=
      let hConv : sNext.pendingCount = 0 → sNext.viewScreen = sNext.authScreen :=
        fun hZero =>
          let hSuccZero : Nat.succ s.pendingCount = 0 :=
            Eq.trans (Eq.symm hAct.2.2.1) hZero
          False.elim (succ_ne_zero s.pendingCount hSuccZero)
      let hCountEq : sNext.ruleCount = s.ruleCount := hAct.2.2.2.1
      let hCapEq : sNext.ruleCap = s.ruleCap := hAct.2.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.ruleCount) (UInt64.toNat s.ruleCap) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.ruleCap)) hCountEq) hInv.2
      let hBounded : Nat.le (UInt64.toNat sNext.ruleCount) (UInt64.toNat sNext.ruleCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.ruleCount) (UInt64.toNat y)) hCapEq) hLe1
      And.intro hConv hBounded

    theorem reconcileGroundTruth_preserves_inv (na : Nat) (rr : UInt64) (s sNext : ProgramSpecState)
        (hAct : ReconcileGroundTruth na rr s sNext) :
        ProgramSpecSafetyInv sNext :=
      let hConv : sNext.pendingCount = 0 → sNext.viewScreen = sNext.authScreen :=
        fun _ => Eq.trans hAct.2.1 (Eq.symm hAct.1)
      let hCountEq : sNext.ruleCount = _root_.program_rule_cap_clamp rr s.ruleCap := hAct.2.2.2.1
      let hCapEq : sNext.ruleCap = s.ruleCap := hAct.2.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.ruleCount) (UInt64.toNat s.ruleCap) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.ruleCap)) hCountEq)
          (clamp_le_cap rr s.ruleCap)
      let hBounded : Nat.le (UInt64.toNat sNext.ruleCount) (UInt64.toNat sNext.ruleCap) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.ruleCount) (UInt64.toNat y)) hCapEq) hLe1
      And.intro hConv hBounded

    theorem next_preserves_inv (s sNext : ProgramSpecState)
        (hInv : ProgramSpecSafetyInv s) (hNext : Next s sNext) :
        ProgramSpecSafetyInv sNext :=
      Or.elim hNext
        (fun hPred =>
          Exists.elim hPred (fun sv hP => predictTransition_preserves_inv sv s sNext hInv hP))
        (fun hRec =>
          Exists.elim hRec (fun na hRecR =>
            Exists.elim hRecR (fun rr hR => reconcileGroundTruth_preserves_inv na rr s sNext hR)))

    theorem spec_satisfies_program_speculation_safety (s0 : Nat) (cap : UInt64) :
        (Spec s0 cap) ⊨ □ (Lift ProgramSpecSafetyInv) :=
      invariantSatisfies (Spec s0 cap) ProgramSpecSafetyInv
        (init_establishes_inv s0 cap)
        next_preserves_inv

    end TlaProgramSpeculation
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def program_ops_within_cap_isl (ops_len : USize) (cap : USize) : Bool :=
      decide (ops_len ≤ cap)
}
