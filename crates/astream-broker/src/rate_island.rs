// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for per-principal / per-producer monotone token-bucket rate limiting
// (`DESIGN-aterm-fabric` T9 & T17), mounted under `cfg(clean_islands)` in `broker.rs`.
// Proves that `rate_tokens_clamp` and `rate_clock_advance` maintain `tokens <= burst`
// and monotone bucket clock progression across arbitrary refill/spend steps.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    -- ========================================================================
    def rate_tokens_clamp (cand_tokens : UInt64) (burst : UInt64) : UInt64 :=
      if cand_tokens < burst then cand_tokens else burst

    def rate_clock_advance (prev_ms : UInt64) (now_ms : UInt64) : UInt64 :=
      if prev_ms < now_ms then now_ms else prev_ms

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaRateBudget)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaRateBudget

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaRateBudget.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaRateBudget.Always

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

    structure RateBucketState where
      tokens  : UInt64
      burst   : UInt64
      epochMs : UInt64
      clockMs : UInt64

    def RateBucketInv (s : RateBucketState) : Prop :=
      Nat.le (UInt64.toNat s.tokens) (UInt64.toNat s.burst) ∧
      Nat.le (UInt64.toNat s.epochMs) (UInt64.toNat s.clockMs)

    def Init (s : RateBucketState) : Prop :=
      s.tokens = s.burst ∧ s.epochMs = s.clockMs

    def stepBucketAction (candTokens : UInt64) (nowMs : UInt64)
        (s sNext : RateBucketState) : Prop :=
      sNext.burst = s.burst ∧
      sNext.epochMs = s.epochMs ∧
      sNext.tokens = _root_.rate_tokens_clamp candTokens s.burst ∧
      sNext.clockMs = _root_.rate_clock_advance s.clockMs nowMs

    def Next (s sNext : RateBucketState) : Prop :=
      ∃ candTokens : UInt64, ∃ nowMs : UInt64,
        stepBucketAction candTokens nowMs s sNext

    def Spec : StateMachine RateBucketState :=
      StateMachine.mk Init Next

    theorem clamp_le_burst : forall (cand : UInt64) (burst : UInt64),
        Nat.le (UInt64.toNat (_root_.rate_tokens_clamp cand burst)) (UInt64.toNat burst) :=
      fun cand burst => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand burst)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => burst) (fun _ => cand))) (UInt64.toNat burst))
        (instDecidableUInt64Lt cand burst)
        (fun _ => Nat.le.refl (UInt64.toNat burst))
        (fun hLt => Nat.le_of_lt hLt)

    theorem clock_advance_ge_prev : forall (prev : UInt64) (now : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.rate_clock_advance prev now)) :=
      fun prev now => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev now)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => now))))
        (instDecidableUInt64Lt prev now)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : RateBucketState) (hInit : Init s) :
        RateBucketInv s :=
      And.intro
        (uint64_eq_le s.tokens s.burst hInit.1)
        (uint64_eq_le s.epochMs s.clockMs hInit.2)

    theorem next_preserves_inv (s sNext : RateBucketState)
        (hInv : RateBucketInv s) (hNext : Next s sNext) :
        RateBucketInv sNext :=
      Exists.elim hNext (fun candTokens h1 =>
        Exists.elim h1 (fun nowMs hAct =>
          let hEqBurst : sNext.burst = s.burst := hAct.1
          let hEqEpoch : sNext.epochMs = s.epochMs := hAct.2.1
          let hEqTok : sNext.tokens = _root_.rate_tokens_clamp candTokens s.burst := hAct.2.2.1
          let hEqClk : sNext.clockMs = _root_.rate_clock_advance s.clockMs nowMs := hAct.2.2.2
          let hTokBound : Nat.le (UInt64.toNat (_root_.rate_tokens_clamp candTokens s.burst)) (UInt64.toNat s.burst) :=
            clamp_le_burst candTokens s.burst
          let hClkGrow : Nat.le (UInt64.toNat s.clockMs) (UInt64.toNat (_root_.rate_clock_advance s.clockMs nowMs)) :=
            clock_advance_ge_prev s.clockMs nowMs
          let hEpochBound : Nat.le (UInt64.toNat s.epochMs) (UInt64.toNat (_root_.rate_clock_advance s.clockMs nowMs)) :=
            Nat.le_trans hInv.2 hClkGrow
          And.intro
            (Eq.mpr
              (congrArg (fun (t : UInt64) => Nat.le (UInt64.toNat t) (UInt64.toNat sNext.burst)) hEqTok)
              (Eq.mpr
                (congrArg (fun (b : UInt64) => Nat.le (UInt64.toNat (_root_.rate_tokens_clamp candTokens s.burst)) (UInt64.toNat b)) hEqBurst)
                hTokBound))
            (Eq.mpr
              (congrArg (fun (e : UInt64) => Nat.le (UInt64.toNat e) (UInt64.toNat sNext.clockMs)) hEqEpoch)
              (Eq.mpr
                (congrArg (fun (c : UInt64) => Nat.le (UInt64.toNat s.epochMs) (UInt64.toNat c)) hEqClk)
                hEpochBound))))

    theorem spec_satisfies_rate_budget_safety :
        Spec ⊨ □ (Lift RateBucketInv) :=
      invariantSatisfies Spec RateBucketInv init_establishes_inv next_preserves_inv

    end TlaRateBudget
    end Broker
    end Astream

    def rate_tokens_sufficient_isl (tokens : UInt64) (cost : UInt64) : Bool :=
      decide (cost ≤ tokens)
}
