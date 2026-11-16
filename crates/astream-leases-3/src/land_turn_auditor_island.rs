// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for Autopilot Land turn-end auditing (`Astream.Agent.TlaLandTurnAuditor`),
// mounted under `cfg(clean_islands)` in `land_turn_auditor.rs`. Proves monotone turn
// progression (`prevTurn <= curTurn`), bounded dirty-item accounting (`dirtyItems <= maxItems`),
// and the Land parking safety invariant (`parkedDone = true -> dirtyItems = 0`) so an agent
// session never parks under `autopilot=land` while uncommitted, unpushed, or unmerged work
// remains.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def land_audit_count_clamp (dirty_items : UInt64) (max_items : UInt64) : UInt64 :=
      if dirty_items < max_items then dirty_items else max_items

    def land_audit_turn_advance (cur_turn : UInt64) (next_turn : UInt64) : UInt64 :=
      if cur_turn < next_turn then next_turn else cur_turn

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Agent.TlaLandTurnAuditor)
    -- ========================================================================
    namespace Astream
    namespace Agent
    namespace TlaLandTurnAuditor

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Agent.TlaLandTurnAuditor.Satisfies M F
    prefix:75 "□" => _root_.Astream.Agent.TlaLandTurnAuditor.Always

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
    -- 3. Autopilot Land Turn-Audit State Machine & Safety Theorem
    -- ========================================================================

    structure LandAuditState where
      prevTurn   : UInt64
      curTurn    : UInt64
      dirtyItems : UInt64
      maxItems   : UInt64
      parkedDone : Bool

    def LandAuditSafetyInv (s : LandAuditState) : Prop :=
      Nat.le (UInt64.toNat s.prevTurn) (UInt64.toNat s.curTurn) ∧
      Nat.le (UInt64.toNat s.dirtyItems) (UInt64.toNat s.maxItems) ∧
      (s.parkedDone = true → s.dirtyItems = (0 : UInt64))

    def Init (maxItems : UInt64) (s : LandAuditState) : Prop :=
      s.prevTurn = (0 : UInt64) ∧
      s.curTurn = (0 : UInt64) ∧
      s.dirtyItems = (0 : UInt64) ∧
      s.maxItems = maxItems ∧
      s.parkedDone = false

    def ContinueDirtyTurn (rawDirty nextTurn : UInt64) (s sNext : LandAuditState) : Prop :=
      sNext.prevTurn = s.curTurn ∧
      sNext.curTurn = _root_.land_audit_turn_advance s.curTurn nextTurn ∧
      sNext.dirtyItems = _root_.land_audit_count_clamp rawDirty s.maxItems ∧
      sNext.maxItems = s.maxItems ∧
      sNext.parkedDone = false

    def ParkCleanLand (nextTurn : UInt64) (s sNext : LandAuditState) : Prop :=
      sNext.prevTurn = s.curTurn ∧
      sNext.curTurn = _root_.land_audit_turn_advance s.curTurn nextTurn ∧
      sNext.dirtyItems = (0 : UInt64) ∧
      sNext.maxItems = s.maxItems ∧
      sNext.parkedDone = true

    def Next (s sNext : LandAuditState) : Prop :=
      (∃ rd : UInt64, ∃ nt : UInt64, ContinueDirtyTurn rd nt s sNext) ∨
      (∃ nt : UInt64, ParkCleanLand nt s sNext)

    def Spec (maxItems : UInt64) : StateMachine LandAuditState :=
      StateMachine.mk (Init maxItems) Next

    theorem false_ne_true (h : false = true) : False :=
      Bool.noConfusion h

    theorem clamp_le_cap : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.land_audit_count_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.land_audit_turn_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_u64_le (x y : UInt64) (hEq : x = y) :
        Nat.le (UInt64.toNat x) (UInt64.toNat y) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat y)) hEq)
        (@Nat.le.refl (UInt64.toNat y))

    theorem init_establishes_inv (maxItems : UInt64) (s : LandAuditState)
        (hInit : Init maxItems s) : LandAuditSafetyInv s :=
      And.intro
        (eq_u64_le s.prevTurn s.curTurn (Eq.trans hInit.1 (Eq.symm hInit.2.1)))
        (And.intro
          (zero_u64_le s.dirtyItems s.maxItems hInit.2.2.1)
          (fun hTrue =>
            False.elim (false_ne_true (Eq.trans (Eq.symm hInit.2.2.2.2) hTrue))))

    theorem continueDirty_preserves_inv (rd nt : UInt64) (s sNext : LandAuditState)
        (hAct : ContinueDirtyTurn rd nt s sNext) : LandAuditSafetyInv sNext :=
      let hT1 : Nat.le (UInt64.toNat s.curTurn) (UInt64.toNat sNext.curTurn) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat s.curTurn) (UInt64.toNat y)) hAct.2.1)
          (advance_ge_cur s.curTurn nt)
      let hT2 : Nat.le (UInt64.toNat sNext.prevTurn) (UInt64.toNat sNext.curTurn) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.curTurn)) hAct.1)
          hT1
      let hD1 : Nat.le (UInt64.toNat sNext.dirtyItems) (UInt64.toNat s.maxItems) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxItems)) hAct.2.2.1)
          (clamp_le_cap rd s.maxItems)
      let hD2 : Nat.le (UInt64.toNat sNext.dirtyItems) (UInt64.toNat sNext.maxItems) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.dirtyItems) (UInt64.toNat y)) hAct.2.2.2.1)
          hD1
      And.intro hT2
        (And.intro hD2
          (fun hTrue =>
            False.elim (false_ne_true (Eq.trans (Eq.symm hAct.2.2.2.2) hTrue))))

    theorem parkClean_preserves_inv (nt : UInt64) (s sNext : LandAuditState)
        (hAct : ParkCleanLand nt s sNext) : LandAuditSafetyInv sNext :=
      let hT1 : Nat.le (UInt64.toNat s.curTurn) (UInt64.toNat sNext.curTurn) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat s.curTurn) (UInt64.toNat y)) hAct.2.1)
          (advance_ge_cur s.curTurn nt)
      let hT2 : Nat.le (UInt64.toNat sNext.prevTurn) (UInt64.toNat sNext.curTurn) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.curTurn)) hAct.1)
          hT1
      let hD : Nat.le (UInt64.toNat sNext.dirtyItems) (UInt64.toNat sNext.maxItems) :=
        zero_u64_le sNext.dirtyItems sNext.maxItems hAct.2.2.1
      And.intro hT2 (And.intro hD (fun _ => hAct.2.2.1))

    theorem next_preserves_inv (s sNext : LandAuditState)
        (_hInv : LandAuditSafetyInv s) (hNext : Next s sNext) :
        LandAuditSafetyInv sNext :=
      Or.elim hNext
        (fun hEx1 =>
          Exists.elim hEx1 (fun rd hEx2 =>
            Exists.elim hEx2 (fun nt hC => continueDirty_preserves_inv rd nt s sNext hC)))
        (fun hExP =>
          Exists.elim hExP (fun nt hP => parkClean_preserves_inv nt s sNext hP))

    theorem spec_satisfies_land_turn_auditor_safety (maxItems : UInt64) :
        (Spec maxItems) ⊨ □ (Lift LandAuditSafetyInv) :=
      invariantSatisfies (Spec maxItems) LandAuditSafetyInv
        (init_establishes_inv maxItems)
        next_preserves_inv

    end TlaLandTurnAuditor
    end Agent
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def land_audit_is_clean_isl (dirty_items : UInt64) : Bool :=
      decide (dirty_items = 0)
}
