// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `control.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `control.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn control_handoff_holder`) and verified by `Faithful`.
    -- ========================================================================

    -- Single-writer keyboard control handoff (`(_cur_holder, next_holder) -> next_holder`).
    def control_handoff_holder (_cur_holder : UInt64) (next_holder : UInt64) : UInt64 :=
      next_holder

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Trust.Temporal)
    -- ========================================================================
    namespace Trust
    namespace Temporal

    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop

    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)

    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    def Eventually {State : Type} (F : Formula State) : Formula State :=
      fun b => ∃ n, F (drop b n)

    def LeadsTo {State : Type} (F G : Formula State) : Formula State :=
      Always (fun b => F b → Eventually G b)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    prefix:100 "□" => _root_.Trust.Temporal.Always
    prefix:100 "◇" => _root_.Trust.Temporal.Eventually
    infixl:50 " ~> " => _root_.Trust.Temporal.LeadsTo
    infixl:45 " ⊨ " => _root_.Trust.Temporal.Satisfies

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

    end Temporal
    end Trust

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Single-Writer Control Arbitration
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaControlHandoff

    open Trust.Temporal

    -- State variables of the single-writer keyboard arbitration protocol:
    --   holder       : current client_id holding the ControlToken (`UInt64`)
    --   activeWriter : client_id of the most recently admitted `In` write (`UInt64`)
    --   writing      : 0 = idle / after handoff, 1 = active write admitted in current epoch
    structure ControlState where
      holder       : UInt64
      activeWriter : UInt64
      writing      : Nat

    -- TLA+ Safety Invariant:
    -- Whenever an input is admitted in the current control epoch (`writing = 1`),
    -- its writer equals the sole `ControlToken` holder (`activeWriter = holder`).
    def SingleWriterInv (s : ControlState) : Prop :=
      s.writing = 1 → s.activeWriter = s.holder

    def Init (h0 : UInt64) (s : ControlState) : Prop :=
      s.holder = h0 ∧
      s.activeWriter = h0 ∧
      s.writing = 0

    -- Action 1: WriteAsHolder — the current holder applies an input (`Session::apply_input_as`).
    def WriteAsHolder (s sNext : ControlState) : Prop :=
      sNext.holder = s.holder ∧
      sNext.activeWriter = s.holder ∧
      sNext.writing = 1

    -- Action 2: GrantControl — the current holder hands off control to `toClient` (`ControlToken::grant`),
    -- stepping via Clean-origin `_root_.control_handoff_holder`.
    def GrantControl (toClient : UInt64) (s sNext : ControlState) : Prop :=
      sNext.holder = _root_.control_handoff_holder s.holder toClient ∧
      sNext.activeWriter = _root_.control_handoff_holder s.activeWriter toClient ∧
      sNext.writing = 0

    -- Action 3: ClaimControl — human operator seizes control (`ControlToken::claim`),
    -- stepping via Clean-origin `_root_.control_handoff_holder`.
    def ClaimControl (human : UInt64) (s sNext : ControlState) : Prop :=
      sNext.holder = _root_.control_handoff_holder s.holder human ∧
      sNext.activeWriter = _root_.control_handoff_holder s.activeWriter human ∧
      sNext.writing = 0

    -- Action 4: RefuseNonHolder — non-holder write or grant is rejected with `EngineError::NotHolder`.
    def RefuseNonHolder (s sNext : ControlState) : Prop :=
      sNext.holder = s.holder ∧
      sNext.activeWriter = s.activeWriter ∧
      sNext.writing = s.writing

    def Next (toClient human : UInt64) (s sNext : ControlState) : Prop :=
      WriteAsHolder s sNext ∨
        (GrantControl toClient s sNext ∨
          (ClaimControl human s sNext ∨ RefuseNonHolder s sNext))

    def Spec (h0 toClient human : UInt64) : StateMachine ControlState :=
      StateMachine.mk (Init h0) (Next toClient human)

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (h0 : UInt64) (s : ControlState) (hInit : Init h0 s) :
        SingleWriterInv s :=
      fun hW =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.2) hW
        False.elim (zero_ne_one h01)

    theorem write_preserves_inv (s sNext : ControlState)
        (hAct : WriteAsHolder s sNext) : SingleWriterInv sNext :=
      fun _ => Eq.trans hAct.2.1 (Eq.symm hAct.1)

    theorem grant_preserves_inv (toClient : UInt64) (s sNext : ControlState)
        (hAct : GrantControl toClient s sNext) : SingleWriterInv sNext :=
      fun hW =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2) hW
        False.elim (zero_ne_one h01)

    theorem claim_preserves_inv (human : UInt64) (s sNext : ControlState)
        (hAct : ClaimControl human s sNext) : SingleWriterInv sNext :=
      fun hW =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2) hW
        False.elim (zero_ne_one h01)

    theorem refuse_preserves_inv (s sNext : ControlState)
        (hInv : SingleWriterInv s) (hAct : RefuseNonHolder s sNext) :
        SingleWriterInv sNext :=
      fun hWNext =>
        let hW : s.writing = 1 := Eq.trans (Eq.symm hAct.2.2) hWNext
        let hEq : s.activeWriter = s.holder := hInv hW
        Eq.trans hAct.2.1 (Eq.trans hEq (Eq.symm hAct.1))

    theorem next_preserves_inv (toClient human : UInt64) (s sNext : ControlState)
        (hInv : SingleWriterInv s) (hNext : Next toClient human s sNext) :
        SingleWriterInv sNext :=
      Or.elim hNext
        (fun hWr => write_preserves_inv s sNext hWr)
        (fun hR1 =>
          Or.elim hR1
            (fun hGr => grant_preserves_inv toClient s sNext hGr)
            (fun hR2 =>
              Or.elim hR2
                (fun hCl => claim_preserves_inv human s sNext hCl)
                (fun hRef => refuse_preserves_inv s sNext hInv hRef)))

    -- Full TLA+ Temporal Safety Theorem:
    --   `Spec h0 toClient human ⊨ □ (Lift SingleWriterInv)`
    theorem spec_satisfies_single_writer (h0 toClient human : UInt64) :
        (Spec h0 toClient human) ⊨ □ (Lift SingleWriterInv) :=
      invariantSatisfies (Spec h0 toClient human) SingleWriterInv
        (init_establishes_inv h0)
        (next_preserves_inv toClient human)

    -- Mutual exclusion of writers: at most one client can satisfy `may_write`
    -- (`client = holder`) at any instant.
    theorem exclusive_holder (holder c1 c2 : UInt64)
        (h1 : c1 = holder) (h2 : c2 = holder) : c1 = c2 :=
      Eq.trans h1 (Eq.symm h2)

    end TlaControlHandoff
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definition
    -- ========================================================================

    def holder_matches_isl (holder : UInt64) (client : UInt64) : Bool :=
      decide (client = holder)
}
