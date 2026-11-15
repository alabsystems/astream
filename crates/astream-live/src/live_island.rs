// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `lib.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `lib.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn live_bridge_advance_step`) and verified by `Faithful`.
    -- ========================================================================

    -- Monotone live-capture causal step advance (`max(cur_step, next_step)`).
    def live_bridge_advance_step (cur_step : UInt64) (next_step : UInt64) : UInt64 :=
      if cur_step < next_step then next_step else cur_step

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Live.TlaLiveBridge)
    -- ========================================================================
    namespace Astream
    namespace Live
    namespace TlaLiveBridge

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

    prefix:100 "□" => _root_.Astream.Live.TlaLiveBridge.Always
    infixl:45 " ⊨ " => _root_.Astream.Live.TlaLiveBridge.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      @Nat.rec (fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun step => hStep (b k) (b (Nat.succ k)) ih step)
            (fun stutter => Eq.mpr (congrArg I stutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    theorem live_bridge_advance_lub (cur req bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hReq : Nat.le (UInt64.toNat req) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.live_bridge_advance_step cur req)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur req)
        (fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur req) d req cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur req)
        (fun _ => hCur)
        (fun _ => hReq)

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Live-Capture Four-Stream Session Bridge
    -- ========================================================================
    -- State of assembling a live LLM turn into a unified 5-event four-stream session
    -- (`Completion -> In -> Effect(Clock) -> Out -> ToolResult`):
    --   emitted      : number of unified events emitted so far (`UInt64`)
    --   totalEvents  : target session length (`UInt64`, 5 for `unified_from_capture`)
    --   causalPrefix : number of events emitted in strict causal stream order (`UInt64`)
    --   toolIdBound  : 0 = matched to completion call id, 1 = diverged
    structure BridgeState where
      emitted      : UInt64
      totalEvents  : UInt64
      causalPrefix : UInt64
      toolIdBound  : Nat

    -- TLA+ Safety Invariant:
    -- 1. Emitted events never exceed the target bridge session bound (`emitted <= totalEvents`).
    -- 2. Every emitted event preserves causal four-stream order (`causalPrefix = emitted`).
    def BridgeSafetyInv (s : BridgeState) : Prop :=
      Nat.le (UInt64.toNat s.emitted) (UInt64.toNat s.totalEvents) ∧
      s.causalPrefix = s.emitted

    def Init (n : UInt64) (s : BridgeState) : Prop :=
      s.emitted = 0 ∧
      s.totalEvents = n ∧
      s.causalPrefix = 0 ∧
      s.toolIdBound = 0

    -- Action 1: EmitCausalEvent — emit the next four-stream event in causal order
    -- (`Completion -> In -> Effect -> Out -> ToolResult`) with matching `tool_use_id`,
    -- advancing via Clean-origin `_root_.live_bridge_advance_step`.
    def EmitCausalEvent (nextStep : UInt64) (expectedToolId actualToolId : Nat) (s sNext : BridgeState) : Prop :=
      s.toolIdBound = 0 ∧
      Nat.le (UInt64.toNat nextStep) (UInt64.toNat s.totalEvents) ∧
      expectedToolId = actualToolId ∧
      sNext.emitted = _root_.live_bridge_advance_step s.emitted nextStep ∧
      sNext.totalEvents = s.totalEvents ∧
      sNext.causalPrefix = _root_.live_bridge_advance_step s.causalPrefix nextStep ∧
      sNext.toolIdBound = 0

    -- Action 2: CompleteSession — once `emitted = totalEvents`, remain at the sealed boundary.
    def CompleteSession (s sNext : BridgeState) : Prop :=
      s.toolIdBound = 0 ∧
      s.emitted = s.totalEvents ∧
      sNext.emitted = s.emitted ∧
      sNext.totalEvents = s.totalEvents ∧
      sNext.causalPrefix = s.causalPrefix ∧
      sNext.toolIdBound = 0

    def Next (s sNext : BridgeState) : Prop :=
      (∃ ns : UInt64, ∃ et : Nat, ∃ atId : Nat, EmitCausalEvent ns et atId s sNext) ∨
        CompleteSession s sNext

    def Spec (n : UInt64) : StateMachine BridgeState :=
      StateMachine.mk (Init n) Next

    theorem init_establishes_inv (n : UInt64) (s : BridgeState)
        (hInit : Init n s) : BridgeSafetyInv s :=
      let hLe0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.totalEvents) :=
        Nat.zero_le (UInt64.toNat s.totalEvents)
      let hLeEmitted : Nat.le (UInt64.toNat s.emitted) (UInt64.toNat s.totalEvents) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalEvents)) hInit.1) hLe0
      let hPrefix : s.causalPrefix = s.emitted :=
        Eq.trans hInit.2.2.1 (Eq.symm hInit.1)
      And.intro hLeEmitted hPrefix

    theorem emitCausal_preserves_inv (ns : UInt64) (et atId : Nat) (s sNext : BridgeState)
        (hInv : BridgeSafetyInv s) (hAct : EmitCausalEvent ns et atId s sNext) :
        BridgeSafetyInv sNext :=
      let hLt : Nat.le (UInt64.toNat ns) (UInt64.toNat s.totalEvents) := hAct.2.1
      let hEm : sNext.emitted = _root_.live_bridge_advance_step s.emitted ns := hAct.2.2.2.1
      let hTot : sNext.totalEvents = s.totalEvents := hAct.2.2.2.2.1
      let hPre : sNext.causalPrefix = _root_.live_bridge_advance_step s.causalPrefix ns := hAct.2.2.2.2.2.1
      let hLub : Nat.le (UInt64.toNat (_root_.live_bridge_advance_step s.emitted ns)) (UInt64.toNat s.totalEvents) :=
        live_bridge_advance_lub s.emitted ns s.totalEvents hInv.1 hLt
      let hLe1 : Nat.le (UInt64.toNat sNext.emitted) (UInt64.toNat s.totalEvents) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalEvents)) hEm) hLub
      let hLeNext : Nat.le (UInt64.toNat sNext.emitted) (UInt64.toNat sNext.totalEvents) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.emitted) (UInt64.toNat y)) hTot) hLe1
      let hAdvEq : _root_.live_bridge_advance_step s.causalPrefix ns = _root_.live_bridge_advance_step s.emitted ns :=
        congrArg (fun x => _root_.live_bridge_advance_step x ns) hInv.2
      let hPreNext : sNext.causalPrefix = sNext.emitted :=
        Eq.trans hPre (Eq.trans hAdvEq (Eq.symm hEm))
      And.intro hLeNext hPreNext

    theorem completeSession_preserves_inv (s sNext : BridgeState)
        (hInv : BridgeSafetyInv s) (hAct : CompleteSession s sNext) :
        BridgeSafetyInv sNext :=
      let hEm : sNext.emitted = s.emitted := hAct.2.2.1
      let hTot : sNext.totalEvents = s.totalEvents := hAct.2.2.2.1
      let hPre : sNext.causalPrefix = s.causalPrefix := hAct.2.2.2.2.1
      let hLe1 : Nat.le (UInt64.toNat sNext.emitted) (UInt64.toNat s.totalEvents) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalEvents)) hEm) hInv.1
      let hLeNext : Nat.le (UInt64.toNat sNext.emitted) (UInt64.toNat sNext.totalEvents) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.emitted) (UInt64.toNat y)) hTot) hLe1
      let hPreNext : sNext.causalPrefix = sNext.emitted :=
        Eq.trans hPre (Eq.trans hInv.2 (Eq.symm hEm))
      And.intro hLeNext hPreNext

    theorem next_preserves_inv (s sNext : BridgeState)
        (hInv : BridgeSafetyInv s) (hNext : Next s sNext) :
        BridgeSafetyInv sNext :=
      Or.elim hNext
        (fun hEx0 =>
          Exists.elim hEx0 (fun ns hEx1 =>
            Exists.elim hEx1 (fun et hEx2 =>
              Exists.elim hEx2 (fun atId hEmit =>
                emitCausal_preserves_inv ns et atId s sNext hInv hEmit))))
        (fun hComp => completeSession_preserves_inv s sNext hInv hComp)

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec n) ⊨ □ (Lift BridgeSafetyInv)`
    theorem spec_satisfies_live_bridge_safety (n : UInt64) :
        (Spec n) ⊨ □ (Lift BridgeSafetyInv) :=
      invariantSatisfies (Spec n) BridgeSafetyInv
        (init_establishes_inv n)
        next_preserves_inv

    end TlaLiveBridge
    end Live
    end Astream

    def live_bridge_step_in_bounds_isl (step : UInt64) (total_steps : UInt64) : Bool :=
      decide (step ≤ total_steps)
}
