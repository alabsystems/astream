// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for log-identity-bound at-rest encryption (`AUDIT-2026-09` L72,
// `ROADMAP.md` L53, `DESIGN-aterm-fabric` §8.1 T12), mounted under `cfg(clean_islands)`
// in `store.rs`. Proves that at-rest AAD binding version selection is monotone
// (`prevVer <= curVer`, preventing v2 -> v1 downgrade) and that distinct `(domain,
// sealId, index)` tuples are rejected by authenticated unsealing (preventing cross-log,
// cross-sidecar, and intra-log record swaps under a shared 32-byte key).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def at_rest_version_advance (prev_ver : UInt64) (next_ver : UInt64) : UInt64 :=
      if prev_ver < next_ver then next_ver else prev_ver

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaAtRestLogBinding)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaAtRestLogBinding

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaAtRestLogBinding.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaAtRestLogBinding.Always

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

    structure AadContext where
      domain : UInt64
      sealId : UInt64
      index  : UInt64

    def AuthenticatedOpen (sealedCtx openCtx : AadContext) : Prop :=
      sealedCtx.domain = openCtx.domain ∧
      sealedCtx.sealId = openCtx.sealId ∧
      sealedCtx.index  = openCtx.index

    theorem cross_log_splice_rejected (sealedCtx openCtx : AadContext)
        (hDiffLog : sealedCtx.sealId = openCtx.sealId → False) :
        AuthenticatedOpen sealedCtx openCtx → False :=
      fun hAuth => hDiffLog hAuth.2.1

    theorem cross_domain_splice_rejected (sealedCtx openCtx : AadContext)
        (hDiffDom : sealedCtx.domain = openCtx.domain → False) :
        AuthenticatedOpen sealedCtx openCtx → False :=
      fun hAuth => hDiffDom hAuth.1

    theorem intra_log_reorder_rejected (sealedCtx openCtx : AadContext)
        (hDiffIdx : sealedCtx.index = openCtx.index → False) :
        AuthenticatedOpen sealedCtx openCtx → False :=
      fun hAuth => hDiffIdx hAuth.2.2

    structure BindingState where
      prevVer : UInt64
      curVer  : UInt64

    def NoDowngradeInv (s : BindingState) : Prop :=
      Nat.le (UInt64.toNat s.prevVer) (UInt64.toNat s.curVer)

    def Init (s : BindingState) : Prop :=
      s.prevVer = s.curVer

    def advanceBindingAction (candidateVer : UInt64) (s sNext : BindingState) : Prop :=
      sNext.prevVer = s.curVer ∧
      sNext.curVer = _root_.at_rest_version_advance s.curVer candidateVer

    def Next (s sNext : BindingState) : Prop :=
      ∃ candidateVer : UInt64, advanceBindingAction candidateVer s sNext

    def Spec : StateMachine BindingState :=
      StateMachine.mk Init Next

    theorem version_advance_ge_prev : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.at_rest_version_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : BindingState) (hInit : Init s) :
        NoDowngradeInv s :=
      uint64_eq_le s.prevVer s.curVer hInit

    theorem next_preserves_inv (s sNext : BindingState)
        (_hInv : NoDowngradeInv s) (hNext : Next s sNext) :
        NoDowngradeInv sNext :=
      Exists.elim hNext (fun cand hAct =>
        let hAdv : Nat.le (UInt64.toNat s.curVer) (UInt64.toNat (_root_.at_rest_version_advance s.curVer cand)) :=
          version_advance_ge_prev s.curVer cand
        let hEqPrev : sNext.prevVer = s.curVer := hAct.1
        let hEqCur : sNext.curVer = _root_.at_rest_version_advance s.curVer cand := hAct.2
        Eq.mpr
          (congrArg (fun (p : UInt64) => Nat.le (UInt64.toNat p) (UInt64.toNat sNext.curVer)) hEqPrev)
          (Eq.mpr
            (congrArg (fun (c : UInt64) => Nat.le (UInt64.toNat s.curVer) (UInt64.toNat c)) hEqCur)
            hAdv))

    theorem spec_satisfies_at_rest_no_downgrade :
        Spec ⊨ □ (Lift NoDowngradeInv) :=
      invariantSatisfies Spec NoDowngradeInv init_establishes_inv next_preserves_inv

    end TlaAtRestLogBinding
    end Broker
    end Astream

    def at_rest_version_is_bound_isl (ver : UInt64) (min_bound : UInt64) : Bool :=
      decide (min_bound ≤ ver)
}
