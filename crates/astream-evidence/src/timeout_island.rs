// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for per-claim wall-clock timeout enforcement in the evidence runner
// (`Astream.Evidence.TlaClaimTimeout`), mounted under `cfg(clean_islands)` in `runner.rs`
// (`docs/AUDIT-2026-09.md` line 90).
// Proves that `claim_elapsed_clamp` and `claim_timeout_floor` maintain:
// 1. `0 < limitMs` whenever `0 < floorMs` (every claim timeout is strictly positive),
// 2. `elapsedMs <= limitMs` across running ticks, and
// 3. `timedOut = 1 -> elapsedMs = limitMs` (fail-closed termination only at or past ceiling).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def claim_elapsed_clamp (elapsed_ms : UInt64) (limit_ms : UInt64) : UInt64 :=
      if elapsed_ms < limit_ms then elapsed_ms else limit_ms

    def claim_timeout_floor (requested_ms : UInt64) (floor_ms : UInt64) : UInt64 :=
      if floor_ms < requested_ms then requested_ms else floor_ms

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Evidence.TlaClaimTimeout)
    -- ========================================================================
    namespace Astream
    namespace Evidence
    namespace TlaClaimTimeout

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Evidence.TlaClaimTimeout.Satisfies M F
    prefix:75 "□" => _root_.Astream.Evidence.TlaClaimTimeout.Always

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

    theorem claim_elapsed_clamp_le_limit (el lim : UInt64) :
        Nat.le (UInt64.toNat (_root_.claim_elapsed_clamp el lim)) (UInt64.toNat lim) :=
      @Decidable.casesOn (LT.lt el lim)
        (fun (d : Decidable (LT.lt el lim)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt el lim) d el lim)) (UInt64.toNat lim))
        (instDecidableUInt64Lt el lim)
        (fun _ => Nat.le_refl (UInt64.toNat lim))
        (fun hLt => Nat.le_of_lt hLt)

    theorem claim_timeout_floor_ge (req flr : UInt64) :
        Nat.le (UInt64.toNat flr) (UInt64.toNat (_root_.claim_timeout_floor req flr)) :=
      @Decidable.casesOn (LT.lt flr req)
        (fun (d : Decidable (LT.lt flr req)) =>
          Nat.le (UInt64.toNat flr) (UInt64.toNat (@ite UInt64 (LT.lt flr req) d req flr)))
        (instDecidableUInt64Lt flr req)
        (fun _ => Nat.le_refl (UInt64.toNat flr))
        (fun hLt => Nat.le_of_lt hLt)

    structure ClaimTimeoutState where
      elapsedMs : UInt64
      limitMs   : UInt64
      floorMs   : UInt64
      timedOut  : Nat

    def ClaimTimeoutSafetyInv (s : ClaimTimeoutState) : Prop :=
      Nat.le (UInt64.toNat s.elapsedMs) (UInt64.toNat s.limitMs) ∧
      Nat.le (UInt64.toNat s.floorMs) (UInt64.toNat s.limitMs) ∧
      (s.timedOut = 1 → s.elapsedMs = s.limitMs)

    def Init (reqMs floorMs : UInt64) (s : ClaimTimeoutState) : Prop :=
      s.elapsedMs = (0 : UInt64) ∧
      s.limitMs = _root_.claim_timeout_floor reqMs floorMs ∧
      s.floorMs = floorMs ∧
      s.timedOut = 0

    def PollRunning (sampleMs : UInt64) (s sNext : ClaimTimeoutState) : Prop :=
      s.timedOut = 0 ∧
      sNext.elapsedMs = _root_.claim_elapsed_clamp sampleMs s.limitMs ∧
      sNext.limitMs = s.limitMs ∧
      sNext.floorMs = s.floorMs ∧
      sNext.timedOut = 0

    def KillOnDeadline (s sNext : ClaimTimeoutState) : Prop :=
      sNext.elapsedMs = s.limitMs ∧
      sNext.limitMs = s.limitMs ∧
      sNext.floorMs = s.floorMs ∧
      sNext.timedOut = 1

    def Next (s sNext : ClaimTimeoutState) : Prop :=
      (∃ sm : UInt64, PollRunning sm s sNext) ∨
      KillOnDeadline s sNext

    def Spec (reqMs floorMs : UInt64) : StateMachine ClaimTimeoutState :=
      StateMachine.mk (Init reqMs floorMs) Next

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (reqMs floorMs : UInt64) (s : ClaimTimeoutState)
        (hInit : Init reqMs floorMs s) : ClaimTimeoutSafetyInv s :=
      let hEl0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.limitMs) :=
        Nat.zero_le (UInt64.toNat s.limitMs)
      let hEl : Nat.le (UInt64.toNat s.elapsedMs) (UInt64.toNat s.limitMs) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.limitMs)) hInit.1) hEl0
      let hFlr0 : Nat.le (UInt64.toNat floorMs) (UInt64.toNat (_root_.claim_timeout_floor reqMs floorMs)) :=
        claim_timeout_floor_ge reqMs floorMs
      let hFlr1 : Nat.le (UInt64.toNat floorMs) (UInt64.toNat s.limitMs) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat floorMs) (UInt64.toNat y)) hInit.2.1) hFlr0
      let hFlr : Nat.le (UInt64.toNat s.floorMs) (UInt64.toNat s.limitMs) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.limitMs)) hInit.2.2.1) hFlr1
      let hTo : s.timedOut = 1 → s.elapsedMs = s.limitMs :=
        fun hEq1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.2.2) hEq1
          False.elim (zero_ne_one h01)
      And.intro hEl (And.intro hFlr hTo)

    theorem pollRunning_preserves_inv (sm : UInt64) (s sNext : ClaimTimeoutState)
        (hInv : ClaimTimeoutSafetyInv s) (hAct : PollRunning sm s sNext) :
        ClaimTimeoutSafetyInv sNext :=
      let hClamp : Nat.le (UInt64.toNat (_root_.claim_elapsed_clamp sm s.limitMs)) (UInt64.toNat s.limitMs) :=
        claim_elapsed_clamp_le_limit sm s.limitMs
      let hEl1 : Nat.le (UInt64.toNat sNext.elapsedMs) (UInt64.toNat s.limitMs) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.limitMs)) hAct.2.1) hClamp
      let hEl : Nat.le (UInt64.toNat sNext.elapsedMs) (UInt64.toNat sNext.limitMs) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.elapsedMs) (UInt64.toNat y)) hAct.2.2.1) hEl1
      let hFlr1 : Nat.le (UInt64.toNat sNext.floorMs) (UInt64.toNat s.limitMs) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.limitMs)) hAct.2.2.2.1) hInv.2.1
      let hFlr : Nat.le (UInt64.toNat sNext.floorMs) (UInt64.toNat sNext.limitMs) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.floorMs) (UInt64.toNat y)) hAct.2.2.1) hFlr1
      let hTo : sNext.timedOut = 1 → sNext.elapsedMs = sNext.limitMs :=
        fun hEq1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2.2.2) hEq1
          False.elim (zero_ne_one h01)
      And.intro hEl (And.intro hFlr hTo)

    theorem killOnDeadline_preserves_inv (s sNext : ClaimTimeoutState)
        (hInv : ClaimTimeoutSafetyInv s) (hAct : KillOnDeadline s sNext) :
        ClaimTimeoutSafetyInv sNext :=
      let hEqLim : sNext.elapsedMs = sNext.limitMs :=
        Eq.trans hAct.1 (Eq.symm hAct.2.1)
      let hEl : Nat.le (UInt64.toNat sNext.elapsedMs) (UInt64.toNat sNext.limitMs) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.limitMs)) hEqLim)
          (Nat.le_refl (UInt64.toNat sNext.limitMs))
      let hFlr1 : Nat.le (UInt64.toNat sNext.floorMs) (UInt64.toNat s.limitMs) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.limitMs)) hAct.2.2.1) hInv.2.1
      let hFlr : Nat.le (UInt64.toNat sNext.floorMs) (UInt64.toNat sNext.limitMs) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.floorMs) (UInt64.toNat y)) hAct.2.1) hFlr1
      let hTo : sNext.timedOut = 1 → sNext.elapsedMs = sNext.limitMs :=
        fun _ => hEqLim
      And.intro hEl (And.intro hFlr hTo)

    theorem next_preserves_inv (s sNext : ClaimTimeoutState)
        (hInv : ClaimTimeoutSafetyInv s) (hNext : Next s sNext) :
        ClaimTimeoutSafetyInv sNext :=
      Or.elim hNext
        (fun hPoll =>
          Exists.elim hPoll (fun sm hP => pollRunning_preserves_inv sm s sNext hInv hP))
        (fun hKill => killOnDeadline_preserves_inv s sNext hInv hKill)

    theorem spec_satisfies_claim_timeout_safety (reqMs floorMs : UInt64) :
        (Spec reqMs floorMs) ⊨ □ (Lift ClaimTimeoutSafetyInv) :=
      invariantSatisfies (Spec reqMs floorMs) ClaimTimeoutSafetyInv
        (init_establishes_inv reqMs floorMs)
        next_preserves_inv

    end TlaClaimTimeout
    end Evidence
    end Astream

    def claim_timed_out_isl (elapsed_ms : UInt64) (limit_ms : UInt64) : Bool :=
      decide (limit_ms ≤ elapsed_ms)
}
