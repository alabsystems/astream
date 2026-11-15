// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `predict.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `predict.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    --    Compiled directly from these Clean kernel definitions into Rust MIR
    --    (`pub const fn ...`) and verified by `Faithful`.
    -- ========================================================================

    -- Monotone speculative-echo authoritative watermark advance (`max(cur_wm, new_wm)`).
    def echo_watermark_monotone (cur_wm : UInt64) (new_wm : UInt64) : UInt64 :=
      if cur_wm < new_wm then new_wm else cur_wm

    -- 4-parameter Clean-origin causal watermark selector:
    -- selects `next_wm` iff `in_off == pred_in_off`, else keeps `cur_wm`.
    def echo_causal_watermark_select (in_off : UInt64) (pred_in_off : UInt64) (next_wm : UInt64) (cur_wm : UInt64) : UInt64 :=
      if in_off == pred_in_off then next_wm else cur_wm

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaSpeculativeEcho)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaSpeculativeEcho

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun k => b (Nat.add n k)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun b => ∀ n : Nat, P (drop n b)
    prefix:90 "□" => _root_.Astream.Term.TlaSpeculativeEcho.Always

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun b => M.Init (b 0) ∧ ∀ n : Nat, M.Next (b n) (b (Nat.succ n))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun b => pred (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (P : Formula State) : Prop :=
      ∀ b : Behavior State, Runs M b → P b
    infix:50 " ⊨ " => _root_.Astream.Term.TlaSpeculativeEcho.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (Inv : State → Prop)
        (hInit : ∀ s : State, M.Init s → Inv s)
        (hStep : ∀ s s' : State, Inv s → M.Next s s' → Inv s')
        (b : Behavior State) (hRun : Runs M b) (n : Nat) : Inv (b n) :=
      Nat.rec
        (motive := fun k => Inv (b k))
        (hInit (b 0) hRun.1)
        (fun k ih => hStep (b k) (b (Nat.succ k)) ih (hRun.2 k))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (Inv : State → Prop)
        (hInit : ∀ s : State, M.Init s → Inv s)
        (hStep : ∀ s s' : State, Inv s → M.Next s s' → Inv s') :
        M ⊨ □ (Lift Inv) :=
      fun b hRun n =>
        let hAt : Inv (b n) := invariantAt M Inv hInit hStep b hRun n
        let hEq : Nat.add n 0 = n := Nat.add_zero n
        Eq.mpr (congrArg (fun idx => Inv (b idx)) hEq) hAt

    -- ========================================================================
    -- 3. TLA+ Specification of Speculative Local Echo & Watermark Retirement
    -- ========================================================================
    structure EchoState where
      authScreen   : Nat
      viewScreen   : Nat
      pendingCount : Nat
      watermark    : UInt64

    -- Safety Invariant: whenever all outstanding predictions have retired or
    -- been squashed (`pendingCount = 0`), the user-visible view equals the
    -- pure authoritative VT screen fold (`viewScreen = authScreen`).
    def EchoConvergenceInv (s : EchoState) : Prop :=
      s.pendingCount = 0 → s.viewScreen = s.authScreen

    def Init (s0 : Nat) (w0 : UInt64) (s : EchoState) : Prop :=
      s.authScreen = s0 ∧ s.viewScreen = s0 ∧ s.pendingCount = 0 ∧ s.watermark = w0

    -- Action 1: Speculatively echo a printable keystroke on top of the view.
    def PredictKey (newOverlay : Nat) (s sNext : EchoState) : Prop :=
      sNext.authScreen = s.authScreen ∧
      sNext.viewScreen = newOverlay ∧
      sNext.pendingCount = Nat.succ s.pendingCount ∧
      sNext.watermark = s.watermark

    -- Action 2: Retire all predictions (either all confirmed or contradicted +
    -- tail squashed) at a strictly advancing authoritative out-watermark via
    -- Clean-origin `_root_.echo_watermark_monotone`.
    def RetireToGroundTruth (newAuth : Nat) (newWm : UInt64) (s sNext : EchoState) : Prop :=
      LT.lt s.watermark newWm ∧
      sNext.authScreen = newAuth ∧
      sNext.viewScreen = newAuth ∧
      sNext.pendingCount = 0 ∧
      sNext.watermark = _root_.echo_watermark_monotone s.watermark newWm

    -- Action 3: Reject an out-of-order / non-advancing watermark without mutating state.
    def RejectStaleWatermark (staleWm : UInt64) (s sNext : EchoState) : Prop :=
      Nat.le (UInt64.toNat staleWm) (UInt64.toNat s.watermark) ∧
      sNext.authScreen = s.authScreen ∧
      sNext.viewScreen = s.viewScreen ∧
      sNext.pendingCount = s.pendingCount ∧
      sNext.watermark = s.watermark

    def Next (s sNext : EchoState) : Prop :=
      (∃ ov : Nat, PredictKey ov s sNext) ∨
        ((∃ a : Nat, ∃ w : UInt64, RetireToGroundTruth a w s sNext) ∨
          (∃ sw : UInt64, RejectStaleWatermark sw s sNext))

    def Spec (s0 : Nat) (w0 : UInt64) : StateMachine EchoState :=
      StateMachine.mk (Init s0 w0) Next

    theorem succ_ne_zero (n : Nat) (h : Nat.succ n = 0) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (s0 : Nat) (w0 : UInt64) (s : EchoState)
        (hInit : Init s0 w0 s) : EchoConvergenceInv s :=
      fun _ => Eq.trans hInit.2.1 (Eq.symm hInit.1)

    theorem predictKey_preserves_inv (ov : Nat) (s sNext : EchoState)
        (hAct : PredictKey ov s sNext) : EchoConvergenceInv sNext :=
      fun hZero =>
        let hSuccZero : Nat.succ s.pendingCount = 0 :=
          Eq.trans (Eq.symm hAct.2.2.1) hZero
        False.elim (succ_ne_zero s.pendingCount hSuccZero)

    theorem retireToGroundTruth_preserves_inv (a : Nat) (w : UInt64) (s sNext : EchoState)
        (hAct : RetireToGroundTruth a w s sNext) : EchoConvergenceInv sNext :=
      fun _ => Eq.trans hAct.2.2.1 (Eq.symm hAct.2.1)

    theorem rejectStaleWatermark_preserves_inv (sw : UInt64) (s sNext : EchoState)
        (hInv : EchoConvergenceInv s) (hAct : RejectStaleWatermark sw s sNext) :
        EchoConvergenceInv sNext :=
      fun hZeroNext =>
        let hZero : s.pendingCount = 0 := Eq.trans (Eq.symm hAct.2.2.2.1) hZeroNext
        let hEq : s.viewScreen = s.authScreen := hInv hZero
        Eq.trans hAct.2.2.1 (Eq.trans hEq (Eq.symm hAct.2.1))

    theorem next_preserves_inv (s sNext : EchoState)
        (hInv : EchoConvergenceInv s) (hNext : Next s sNext) :
        EchoConvergenceInv sNext :=
      Or.elim hNext
        (fun hPred =>
          Exists.elim hPred (fun ov hP => predictKey_preserves_inv ov s sNext hP))
        (fun hRest =>
          Or.elim hRest
            (fun hRet =>
              Exists.elim hRet (fun a hRetW =>
                Exists.elim hRetW (fun w hR =>
                  retireToGroundTruth_preserves_inv a w s sNext hR)))
            (fun hStale =>
              Exists.elim hStale (fun sw hS =>
                rejectStaleWatermark_preserves_inv sw s sNext hInv hS)))

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec s0 w0) ⊨ □ (Lift EchoConvergenceInv)`
    theorem spec_satisfies_echo_convergence (s0 : Nat) (w0 : UInt64) :
        (Spec s0 w0) ⊨ □ (Lift EchoConvergenceInv) :=
      invariantSatisfies (Spec s0 w0) EchoConvergenceInv
        (init_establishes_inv s0 w0)
        next_preserves_inv

    def echo_admit_causal_watermark_isl (in_off : UInt64) (pred_in_off : UInt64) (cur_wm : UInt64) (cand_wm : UInt64) : UInt64 :=
      _root_.echo_causal_watermark_select in_off pred_in_off (_root_.echo_watermark_monotone cur_wm cand_wm) cur_wm

    theorem echo_watermark_lub (cur cand bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hCand : Nat.le (UInt64.toNat cand) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.echo_watermark_monotone cur cand)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur cand)
        (fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur cand) d cand cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur cand)
        (fun _ => hCur)
        (fun _ => hCand)

    -- Least-upper-bound theorem over the 4-parameter Clean-origin causal watermark kernel:
    -- whenever `cur_wm <= bound` and `cand_wm <= bound`, the admitted watermark is `<= bound`.
    theorem echo_admit_causal_watermark_lub (in_off pred_in_off cur_wm cand_wm bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur_wm) (UInt64.toNat bound))
        (hCand : Nat.le (UInt64.toNat cand_wm) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (echo_admit_causal_watermark_isl in_off pred_in_off cur_wm cand_wm)) (UInt64.toNat bound) :=
      @Decidable.casesOn (Eq (BEq.beq in_off pred_in_off) Bool.true)
        (fun (dEq : Decidable (Eq (BEq.beq in_off pred_in_off) Bool.true)) =>
          Nat.le
            (UInt64.toNat
              (@ite UInt64 (Eq (BEq.beq in_off pred_in_off) Bool.true) dEq
                (_root_.echo_watermark_monotone cur_wm cand_wm)
                cur_wm))
            (UInt64.toNat bound))
        (Bool.decEq (BEq.beq in_off pred_in_off) Bool.true)
        (fun _ => hCur)
        (fun _ => echo_watermark_lub cur_wm cand_wm bound hCur hCand)

    end TlaSpeculativeEcho
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def watermark_advances_isl (cur_wm : UInt64) (new_wm : UInt64) : Bool :=
      decide (cur_wm < new_wm)
}
