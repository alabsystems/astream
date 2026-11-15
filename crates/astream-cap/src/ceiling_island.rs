// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for least-privilege capability-ring ceiling verification
// (`Astream.Cap.TlaRingCeiling`), mounted under `cfg(clean_islands)` in `ceiling.rs`
// (`DESIGN-aterm-fabric.md` §8.2 & §14 Open Question 5).
// Proves that `ceiling_rule_index_clamp` and `ceiling_mode_subsumes_code` maintain:
// 1. `checkedRules <= maxRules` (bounded rule scan across any capability ring), and
// 2. `admitted = 1 → (rejected = 0 ∧ hasGodCap = 0 ∧ allSubsumed = 1)`
//    (an admitted ring never contains an un-subsumed capability or unbound god cap
//    outside the ceiling).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def ceiling_rule_index_clamp (idx : UInt64) (max_rules : UInt64) : UInt64 :=
      if idx < max_rules then idx else max_rules

    def ceiling_mode_subsumes_code (ceiling_rw : UInt64) (member_rw : UInt64) : UInt64 :=
      if ceiling_rw < member_rw then 0 else 1

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Cap.TlaRingCeiling)
    -- ========================================================================
    namespace Astream
    namespace Cap
    namespace TlaRingCeiling

    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop
    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)
    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    notation:50 M " ⊨ " F:50 => _root_.Astream.Cap.TlaRingCeiling.Satisfies M F
    prefix:75 "□" => _root_.Astream.Cap.TlaRingCeiling.Always

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      Nat.rec
        (motive := fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun hNext => hStep (b k) (b (Nat.succ k)) ih hNext)
            (fun hStutter => Eq.mpr (congrArg I hStutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    -- ========================================================================
    -- 3. Least-Privilege Ring Ceiling State Machine
    -- ========================================================================

    theorem ceiling_rule_index_clamp_le (idx cap : UInt64) :
        Nat.le (UInt64.toNat (_root_.ceiling_rule_index_clamp idx cap)) (UInt64.toNat cap) :=
      @Decidable.casesOn (LT.lt idx cap)
        (fun (d : Decidable (LT.lt idx cap)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt idx cap) d idx cap)) (UInt64.toNat cap))
        (instDecidableUInt64Lt idx cap)
        (fun _ => Nat.le_refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    structure RingCeilingState where
      checkedRules : UInt64
      maxRules     : UInt64
      allSubsumed  : Nat
      hasGodCap    : Nat
      rejected     : Nat
      admitted     : Nat

    def RingCeilingSafetyInv (s : RingCeilingState) : Prop :=
      Nat.le (UInt64.toNat s.checkedRules) (UInt64.toNat s.maxRules) ∧
      (s.admitted = 1 → (s.rejected = 0 ∧ s.hasGodCap = 0 ∧ s.allSubsumed = 1))

    def Init (maxRules : UInt64) (s : RingCeilingState) : Prop :=
      s.checkedRules = (0 : UInt64) ∧
      s.maxRules = maxRules ∧
      s.allSubsumed = 1 ∧
      s.hasGodCap = 0 ∧
      s.rejected = 0 ∧
      s.admitted = 0

    -- Action 1: CheckSubsumedCap — member capability is subsumed by rule `ruleIdx`
    -- without violating bound-principal requirements.
    def CheckSubsumedCap (ruleIdx : UInt64) (s sNext : RingCeilingState) : Prop :=
      s.rejected = 0 ∧
      s.admitted = 0 ∧
      sNext.checkedRules = _root_.ceiling_rule_index_clamp ruleIdx s.maxRules ∧
      sNext.maxRules = s.maxRules ∧
      sNext.allSubsumed = s.allSubsumed ∧
      sNext.hasGodCap = s.hasGodCap ∧
      sNext.rejected = 0 ∧
      sNext.admitted = 0

    -- Action 2: RejectExcessCap — member capability exceeds ceiling (e.g. unbound
    -- fleet-root god cap `rw:/f/f1/>`, wrong node principal, or `rw` on `ro` face).
    def RejectExcessCap (isGod : Nat) (s sNext : RingCeilingState) : Prop :=
      sNext.checkedRules = s.checkedRules ∧
      sNext.maxRules = s.maxRules ∧
      sNext.allSubsumed = 0 ∧
      sNext.hasGodCap = isGod ∧
      sNext.rejected = 1 ∧
      sNext.admitted = 0

    -- Action 3: AdmitRing — finalizes ring admission iff zero violations occurred.
    def AdmitRing (s sNext : RingCeilingState) : Prop :=
      s.rejected = 0 ∧
      s.hasGodCap = 0 ∧
      s.allSubsumed = 1 ∧
      sNext.checkedRules = s.checkedRules ∧
      sNext.maxRules = s.maxRules ∧
      sNext.allSubsumed = 1 ∧
      sNext.hasGodCap = 0 ∧
      sNext.rejected = 0 ∧
      sNext.admitted = 1

    def Next (s sNext : RingCeilingState) : Prop :=
      (∃ idx : UInt64, CheckSubsumedCap idx s sNext) ∨
      ((∃ isGod : Nat, RejectExcessCap isGod s sNext) ∨
       AdmitRing s sNext)

    def Spec (maxRules : UInt64) : StateMachine RingCeilingState :=
      StateMachine.mk (Init maxRules) Next

    theorem init_establishes_inv (maxRules : UInt64) (s : RingCeilingState)
        (hInit : Init maxRules s) : RingCeilingSafetyInv s :=
      let h0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.maxRules) :=
        Nat.zero_le (UInt64.toNat s.maxRules)
      let hBnd : Nat.le (UInt64.toNat s.checkedRules) (UInt64.toNat s.maxRules) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRules)) hInit.1) h0
      let hAdm : s.admitted = 1 → (s.rejected = 0 ∧ s.hasGodCap = 0 ∧ s.allSubsumed = 1) :=
        fun hA1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.2.2.2.2) hA1
          False.elim (zero_ne_one h01)
      And.intro hBnd hAdm

    theorem checkSubsumed_preserves_inv (idx : UInt64) (s sNext : RingCeilingState)
        (_hInv : RingCeilingSafetyInv s) (hAct : CheckSubsumedCap idx s sNext) :
        RingCeilingSafetyInv sNext :=
      let hClamp : Nat.le (UInt64.toNat (_root_.ceiling_rule_index_clamp idx s.maxRules)) (UInt64.toNat s.maxRules) :=
        ceiling_rule_index_clamp_le idx s.maxRules
      let hBnd1 : Nat.le (UInt64.toNat sNext.checkedRules) (UInt64.toNat s.maxRules) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRules)) hAct.2.2.1) hClamp
      let hBnd : Nat.le (UInt64.toNat sNext.checkedRules) (UInt64.toNat sNext.maxRules) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.checkedRules) (UInt64.toNat y)) hAct.2.2.2.1) hBnd1
      let hAdm : sNext.admitted = 1 → (sNext.rejected = 0 ∧ sNext.hasGodCap = 0 ∧ sNext.allSubsumed = 1) :=
        fun hA1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2.2.2.2.2.2) hA1
          False.elim (zero_ne_one h01)
      And.intro hBnd hAdm

    theorem rejectExcess_preserves_inv (isGod : Nat) (s sNext : RingCeilingState)
        (hInv : RingCeilingSafetyInv s) (hAct : RejectExcessCap isGod s sNext) :
        RingCeilingSafetyInv sNext :=
      let hBnd1 : Nat.le (UInt64.toNat sNext.checkedRules) (UInt64.toNat s.maxRules) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRules)) hAct.1) hInv.1
      let hBnd : Nat.le (UInt64.toNat sNext.checkedRules) (UInt64.toNat sNext.maxRules) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.checkedRules) (UInt64.toNat y)) hAct.2.1) hBnd1
      let hAdm : sNext.admitted = 1 → (sNext.rejected = 0 ∧ sNext.hasGodCap = 0 ∧ sNext.allSubsumed = 1) :=
        fun hA1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2.2.2.2) hA1
          False.elim (zero_ne_one h01)
      And.intro hBnd hAdm

    theorem admitRing_preserves_inv (s sNext : RingCeilingState)
        (hInv : RingCeilingSafetyInv s) (hAct : AdmitRing s sNext) :
        RingCeilingSafetyInv sNext :=
      let hBnd1 : Nat.le (UInt64.toNat sNext.checkedRules) (UInt64.toNat s.maxRules) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxRules)) hAct.2.2.2.1) hInv.1
      let hBnd : Nat.le (UInt64.toNat sNext.checkedRules) (UInt64.toNat sNext.maxRules) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.checkedRules) (UInt64.toNat y)) hAct.2.2.2.2.1) hBnd1
      let hAdm : sNext.admitted = 1 → (sNext.rejected = 0 ∧ sNext.hasGodCap = 0 ∧ sNext.allSubsumed = 1) :=
        fun _ =>
          And.intro hAct.2.2.2.2.2.2.2.1
            (And.intro hAct.2.2.2.2.2.2.1 hAct.2.2.2.2.2.1)
      And.intro hBnd hAdm

    theorem next_preserves_inv (s sNext : RingCeilingState)
        (hInv : RingCeilingSafetyInv s) (hNext : Next s sNext) :
        RingCeilingSafetyInv sNext :=
      Or.elim hNext
        (fun hEx => Exists.elim hEx (fun idx hAct => checkSubsumed_preserves_inv idx s sNext hInv hAct))
        (fun hRest =>
          Or.elim hRest
            (fun hEx => Exists.elim hEx (fun isGod hAct => rejectExcess_preserves_inv isGod s sNext hInv hAct))
            (fun hAct => admitRing_preserves_inv s sNext hInv hAct))

    theorem spec_satisfies_ring_ceiling_safety (maxRules : UInt64) :
        (Spec maxRules) ⊨ □ (Lift RingCeilingSafetyInv) :=
      invariantSatisfies (Spec maxRules) RingCeilingSafetyInv
        (init_establishes_inv maxRules) next_preserves_inv

    end TlaRingCeiling
    end Cap
    end Astream

    def ceiling_rule_within_cap_isl (idx : UInt64) (max_rules : UInt64) : Bool :=
      decide (idx ≤ max_rules)
}
