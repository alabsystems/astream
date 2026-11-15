// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for deficit-round-robin (`DRR`) multi-session live stream multiplexing
// (`Astream.Live.TlaLiveSessionMux`), mounted under `cfg(clean_islands)` in
// `live_session_multiplex.rs`. Proves `slotDeficit <= maxCredit` and `activeTabs <= maxTabs`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def mux_deficit_clamp (proposed_deficit : UInt64) (max_credit : UInt64) : UInt64 :=
      if proposed_deficit < max_credit then proposed_deficit else max_credit

    def mux_tabs_clamp (proposed_tabs : UInt64) (max_tabs : UInt64) : UInt64 :=
      if proposed_tabs < max_tabs then proposed_tabs else max_tabs

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Live.TlaLiveSessionMux)
    -- ========================================================================
    namespace Astream
    namespace Live
    namespace TlaLiveSessionMux

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Live.TlaLiveSessionMux.Satisfies M F
    prefix:75 "□" => _root_.Astream.Live.TlaLiveSessionMux.Always

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
    -- 3. Deficit-Round-Robin Live Session Multiplexer State Machine
    -- ========================================================================

    structure LiveMuxState where
      slotDeficit : UInt64
      maxCredit   : UInt64
      activeTabs  : UInt64
      maxTabs     : UInt64

    def LiveMuxInv (s : LiveMuxState) : Prop :=
      Nat.le (UInt64.toNat s.slotDeficit) (UInt64.toNat s.maxCredit) ∧
      Nat.le (UInt64.toNat s.activeTabs) (UInt64.toNat s.maxTabs)

    def Init (maxCredit maxTabs : UInt64) (s : LiveMuxState) : Prop :=
      s.slotDeficit = (0 : UInt64) ∧
      s.maxCredit = maxCredit ∧
      s.activeTabs = (0 : UInt64) ∧
      s.maxTabs = maxTabs

    def StepScheduler (rawDeficit rawTabs : UInt64) (s sNext : LiveMuxState) : Prop :=
      sNext.slotDeficit = _root_.mux_deficit_clamp rawDeficit s.maxCredit ∧
      sNext.maxCredit = s.maxCredit ∧
      sNext.activeTabs = _root_.mux_tabs_clamp rawTabs s.maxTabs ∧
      sNext.maxTabs = s.maxTabs

    def Next (s sNext : LiveMuxState) : Prop :=
      ∃ rd : UInt64, ∃ rt : UInt64, StepScheduler rd rt s sNext

    def Spec (maxCredit maxTabs : UInt64) : StateMachine LiveMuxState :=
      StateMachine.mk (Init maxCredit maxTabs) Next

    theorem deficit_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.mux_deficit_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem tabs_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.mux_tabs_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxCredit maxTabs : UInt64) (s : LiveMuxState)
        (hInit : Init maxCredit maxTabs s) : LiveMuxInv s :=
      And.intro
        (zero_u64_le s.slotDeficit s.maxCredit hInit.1)
        (zero_u64_le s.activeTabs s.maxTabs hInit.2.2.1)

    theorem stepScheduler_preserves_inv (rd rt : UInt64) (s sNext : LiveMuxState)
        (hAct : StepScheduler rd rt s sNext) : LiveMuxInv sNext :=
      let hD1 : Nat.le (UInt64.toNat sNext.slotDeficit) (UInt64.toNat s.maxCredit) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxCredit)) hAct.1)
          (deficit_clamp_le rd s.maxCredit)
      let hD2 : Nat.le (UInt64.toNat sNext.slotDeficit) (UInt64.toNat sNext.maxCredit) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.slotDeficit) (UInt64.toNat y)) hAct.2.1)
          hD1
      let hT1 : Nat.le (UInt64.toNat sNext.activeTabs) (UInt64.toNat s.maxTabs) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxTabs)) hAct.2.2.1)
          (tabs_clamp_le rt s.maxTabs)
      let hT2 : Nat.le (UInt64.toNat sNext.activeTabs) (UInt64.toNat sNext.maxTabs) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.activeTabs) (UInt64.toNat y)) hAct.2.2.2)
          hT1
      And.intro hD2 hT2

    theorem next_preserves_inv (s sNext : LiveMuxState)
        (_hInv : LiveMuxInv s) (hNext : Next s sNext) : LiveMuxInv sNext :=
      Exists.elim hNext (fun rd hEx2 =>
        Exists.elim hEx2 (fun rt hAct => stepScheduler_preserves_inv rd rt s sNext hAct))

    theorem spec_satisfies_live_session_mux_safety (maxCredit maxTabs : UInt64) :
        (Spec maxCredit maxTabs) ⊨ □ (Lift LiveMuxInv) :=
      invariantSatisfies (Spec maxCredit maxTabs) LiveMuxInv
        (init_establishes_inv maxCredit maxTabs)
        next_preserves_inv

    end TlaLiveSessionMux
    end Live
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def mux_frame_fits_credit_isl (frame_bytes : UInt64) (credit : UInt64) : Bool :=
      decide (frame_bytes ≤ credit)
}
