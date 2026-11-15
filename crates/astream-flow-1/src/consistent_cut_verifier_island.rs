// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for bus-record causal consistent cuts (`DESIGN-aterm-fabric.md` §10,
// `Astream.Engine.TlaBusConsistentCut`), mounted under `cfg(clean_islands)` in
// `consistent_cut_verifier.rs`. Proves `maxCauseOffset <= cutFrontier` and
// `verifiedLinks <= totalLinks` across transport-independent `(stream_id, offset)` cuts.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def bus_cut_cause_clamp (cause_off : UInt64) (frontier : UInt64) : UInt64 :=
      if cause_off < frontier then cause_off else frontier

    def bus_cut_verified_clamp (verified : UInt64) (total : UInt64) : UInt64 :=
      if verified < total then verified else total

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaBusConsistentCut

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Engine.TlaBusConsistentCut.Satisfies M F
    prefix:75 "□" => _root_.Astream.Engine.TlaBusConsistentCut.Always

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
    -- 3. Bus Consistent-Cut Causal Verification State Machine
    -- ========================================================================

    structure CutState where
      maxCauseOffset : UInt64
      cutFrontier    : UInt64
      verifiedLinks  : UInt64
      totalLinks     : UInt64

    def CausalCutSafetyInv (s : CutState) : Prop :=
      Nat.le (UInt64.toNat s.maxCauseOffset) (UInt64.toNat s.cutFrontier) ∧
      Nat.le (UInt64.toNat s.verifiedLinks) (UInt64.toNat s.totalLinks)

    def Init (cutFrontier : UInt64) (s : CutState) : Prop :=
      s.maxCauseOffset = (0 : UInt64) ∧
      s.cutFrontier = cutFrontier ∧
      s.verifiedLinks = (0 : UInt64) ∧
      s.totalLinks = (0 : UInt64)

    def CheckCausalEdge (rawCause newFrontier rawVerified newTotal : UInt64)
        (s sNext : CutState) : Prop :=
      sNext.maxCauseOffset = _root_.bus_cut_cause_clamp rawCause newFrontier ∧
      sNext.cutFrontier = newFrontier ∧
      sNext.verifiedLinks = _root_.bus_cut_verified_clamp rawVerified newTotal ∧
      sNext.totalLinks = newTotal

    def Next (s sNext : CutState) : Prop :=
      ∃ rc : UInt64, ∃ nf : UInt64, ∃ rv : UInt64, ∃ nt : UInt64,
        CheckCausalEdge rc nf rv nt s sNext

    def Spec (cutFrontier : UInt64) : StateMachine CutState :=
      StateMachine.mk (Init cutFrontier) Next

    theorem cause_clamp_le : forall (c : UInt64) (f : UInt64),
        Nat.le (UInt64.toNat (_root_.bus_cut_cause_clamp c f)) (UInt64.toNat f) :=
      fun c f => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt c f)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => f) (fun _ => c))) (UInt64.toNat f))
        (instDecidableUInt64Lt c f)
        (fun _ => Nat.le.refl (UInt64.toNat f))
        (fun hLt => Nat.le_of_lt hLt)

    theorem verified_clamp_le : forall (v : UInt64) (tot : UInt64),
        Nat.le (UInt64.toNat (_root_.bus_cut_verified_clamp v tot)) (UInt64.toNat tot) :=
      fun v tot => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt v tot)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => tot) (fun _ => v))) (UInt64.toNat tot))
        (instDecidableUInt64Lt v tot)
        (fun _ => Nat.le.refl (UInt64.toNat tot))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (cutFrontier : UInt64) (s : CutState)
        (hInit : Init cutFrontier s) : CausalCutSafetyInv s :=
      And.intro
        (zero_u64_le s.maxCauseOffset s.cutFrontier hInit.1)
        (zero_u64_le s.verifiedLinks s.totalLinks hInit.2.2.1)

    theorem check_preserves_inv (rc nf rv nt : UInt64) (s sNext : CutState)
        (hAct : CheckCausalEdge rc nf rv nt s sNext) : CausalCutSafetyInv sNext :=
      let hC1 : Nat.le (UInt64.toNat sNext.maxCauseOffset) (UInt64.toNat nf) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat nf)) hAct.1)
          (cause_clamp_le rc nf)
      let hC2 : Nat.le (UInt64.toNat sNext.maxCauseOffset) (UInt64.toNat sNext.cutFrontier) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.maxCauseOffset) (UInt64.toNat y)) hAct.2.1)
          hC1
      let hV1 : Nat.le (UInt64.toNat sNext.verifiedLinks) (UInt64.toNat nt) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat nt)) hAct.2.2.1)
          (verified_clamp_le rv nt)
      let hV2 : Nat.le (UInt64.toNat sNext.verifiedLinks) (UInt64.toNat sNext.totalLinks) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.verifiedLinks) (UInt64.toNat y)) hAct.2.2.2)
          hV1
      And.intro hC2 hV2

    theorem next_preserves_inv (s sNext : CutState)
        (_hInv : CausalCutSafetyInv s) (hNext : Next s sNext) :
        CausalCutSafetyInv sNext :=
      Exists.elim hNext (fun rc hEx1 =>
        Exists.elim hEx1 (fun nf hEx2 =>
          Exists.elim hEx2 (fun rv hEx3 =>
            Exists.elim hEx3 (fun nt hAct => check_preserves_inv rc nf rv nt s sNext hAct))))

    theorem spec_satisfies_causal_cut_safety (cutFrontier : UInt64) :
        (Spec cutFrontier) ⊨ □ (Lift CausalCutSafetyInv) :=
      invariantSatisfies (Spec cutFrontier) CausalCutSafetyInv
        (init_establishes_inv cutFrontier)
        next_preserves_inv

    end TlaBusConsistentCut
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def bus_cut_includes_cause_isl (cause_offset : UInt64) (stream_frontier_exclusive : UInt64) : Bool :=
      decide (cause_offset < stream_frontier_exclusive)
}
