// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `fork.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `fork.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn fork_prefix_bound`) and verified by `Faithful`.
    -- ========================================================================

    -- Clamped counterfactual fork prefix bound (`min(at_off, len)`).
    def fork_prefix_bound (at_off : UInt64) (len : UInt64) : UInt64 :=
      if at_off < len then at_off else len

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Agent.TlaCounterfactualFork)
    -- ========================================================================
    namespace Astream
    namespace Agent
    namespace TlaCounterfactualFork

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

    prefix:100 "□" => _root_.Astream.Agent.TlaCounterfactualFork.Always
    infixl:45 " ⊨ " => _root_.Astream.Agent.TlaCounterfactualFork.Satisfies

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

    theorem fork_prefix_bound_eq_at (at_off len : UInt64)
        (hLt : LT.lt at_off len) :
        _root_.fork_prefix_bound at_off len = at_off :=
      @Decidable.casesOn (LT.lt at_off len)
        (fun (d : Decidable (LT.lt at_off len)) =>
          (@ite UInt64 (LT.lt at_off len) d at_off len) = at_off)
        (instDecidableUInt64Lt at_off len)
        (fun hNotLt => False.elim (hNotLt hLt))
        (fun _ => rfl)

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Counterfactual Cognition-Log Forking
    -- ========================================================================
    -- State of a counterfactual cognition-log fork:
    --   logLen          : number of records in the cognition log (`UInt64`)
    --   forked          : 0 = Unforked, 1 = Forked
    --   forkAt          : index swapped by the counterfactual fork (`UInt64`)
    --   prefixPreserved : number of prefix records (`< forkAt`) preserved byte-for-byte (`UInt64`)
    --   atVal           : value at `forkAt` after fork
    --   expectedRep     : replacement value requested by the fork
    structure ForkState where
      logLen          : UInt64
      forked          : Nat
      forkAt          : UInt64
      prefixPreserved : UInt64
      atVal           : Nat
      expectedRep     : Nat

    -- TLA+ Safety Invariant:
    -- Whenever a counterfactual fork has been applied (`forked = 1`),
    -- 1. `forkAt < logLen` (`LT.lt s.forkAt s.logLen`),
    -- 2. Every prefix record `< forkAt` is preserved (`prefixPreserved = forkAt`), and
    -- 3. The record at `forkAt` equals the replacement (`atVal = expectedRep`).
    def PrefixStabilityInv (s : ForkState) : Prop :=
      s.forked = 1 →
        (LT.lt s.forkAt s.logLen ∧
         s.prefixPreserved = s.forkAt ∧
         s.atVal = s.expectedRep)

    def Init (n : UInt64) (s : ForkState) : Prop :=
      s.logLen = n ∧
      s.forked = 0 ∧
      s.forkAt = 0 ∧
      s.prefixPreserved = 0 ∧
      s.atVal = 0 ∧
      s.expectedRep = 0

    -- Action 1: ApplyFork — swap record at in-range `atIdx < logLen` with `repVal`,
    -- computing the preserved prefix bound via Clean-origin `_root_.fork_prefix_bound`.
    def ApplyFork (atIdx : UInt64) (repVal : Nat) (s sNext : ForkState) : Prop :=
      s.forked = 0 ∧
      LT.lt atIdx s.logLen ∧
      sNext.logLen = s.logLen ∧
      sNext.forked = 1 ∧
      sNext.forkAt = atIdx ∧
      sNext.prefixPreserved = _root_.fork_prefix_bound atIdx s.logLen ∧
      sNext.atVal = repVal ∧
      sNext.expectedRep = repVal

    -- Action 2: RefuseOutOfRange — reject out-of-range `atIdx >= logLen` (`try_cog_fork_swap -> None`).
    def RefuseOutOfRange (atIdx : UInt64) (s sNext : ForkState) : Prop :=
      s.forked = 0 ∧
      Nat.le (UInt64.toNat s.logLen) (UInt64.toNat atIdx) ∧
      sNext.logLen = s.logLen ∧
      sNext.forked = s.forked ∧
      sNext.forkAt = s.forkAt ∧
      sNext.prefixPreserved = s.prefixPreserved ∧
      sNext.atVal = s.atVal ∧
      sNext.expectedRep = s.expectedRep

    def Next (s sNext : ForkState) : Prop :=
      (∃ atIdx : UInt64, ∃ repVal : Nat, ApplyFork atIdx repVal s sNext) ∨
        (∃ atIdx : UInt64, RefuseOutOfRange atIdx s sNext)

    def Spec (n : UInt64) : StateMachine ForkState :=
      StateMachine.mk (Init n) Next

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (n : UInt64) (s : ForkState)
        (hInit : Init n s) : PrefixStabilityInv s :=
      fun hFork1 =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.1) hFork1
        False.elim (zero_ne_one h01)

    theorem applyFork_preserves_inv (atIdx : UInt64) (repVal : Nat) (s sNext : ForkState)
        (hAct : ApplyFork atIdx repVal s sNext) :
        PrefixStabilityInv sNext :=
      fun _ =>
        let hLt : LT.lt atIdx s.logLen := hAct.2.1
        let hLenEq : sNext.logLen = s.logLen := hAct.2.2.1
        let hAtEq : sNext.forkAt = atIdx := hAct.2.2.2.2.1
        let hPrefEq : sNext.prefixPreserved = _root_.fork_prefix_bound atIdx s.logLen := hAct.2.2.2.2.2.1
        let hValEq : sNext.atVal = repVal := hAct.2.2.2.2.2.2.1
        let hRepEq : sNext.expectedRep = repVal := hAct.2.2.2.2.2.2.2
        let hLt1 : LT.lt sNext.forkAt s.logLen :=
          Eq.mpr (congrArg (fun x => LT.lt x s.logLen) hAtEq) hLt
        let hLtNext : LT.lt sNext.forkAt sNext.logLen :=
          Eq.mpr (congrArg (fun y => LT.lt sNext.forkAt y) hLenEq) hLt1
        let hBoundEq : _root_.fork_prefix_bound atIdx s.logLen = atIdx :=
          fork_prefix_bound_eq_at atIdx s.logLen hLt
        let hPrefMatch : sNext.prefixPreserved = sNext.forkAt :=
          Eq.trans hPrefEq (Eq.trans hBoundEq (Eq.symm hAtEq))
        let hValMatch : sNext.atVal = sNext.expectedRep :=
          Eq.trans hValEq (Eq.symm hRepEq)
        And.intro hLtNext (And.intro hPrefMatch hValMatch)

    theorem refuseOutOfRange_preserves_inv (atIdx : UInt64) (s sNext : ForkState)
        (hAct : RefuseOutOfRange atIdx s sNext) :
        PrefixStabilityInv sNext :=
      fun hFork1 =>
        let hFork0 : s.forked = 0 := hAct.1
        let hForkEq : sNext.forked = s.forked := hAct.2.2.2.1
        let h01 : 0 = 1 := Eq.trans (Eq.symm hFork0) (Eq.trans (Eq.symm hForkEq) hFork1)
        False.elim (zero_ne_one h01)

    theorem next_preserves_inv (s sNext : ForkState)
        (_hInv : PrefixStabilityInv s) (hNext : Next s sNext) :
        PrefixStabilityInv sNext :=
      Or.elim hNext
        (fun hEx1 =>
          Exists.elim hEx1 (fun atIdx hEx2 =>
            Exists.elim hEx2 (fun repVal hApp =>
              applyFork_preserves_inv atIdx repVal s sNext hApp)))
        (fun hEx =>
          Exists.elim hEx (fun atIdx hRef =>
            refuseOutOfRange_preserves_inv atIdx s sNext hRef))

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec n) ⊨ □ (Lift PrefixStabilityInv)`
    theorem spec_satisfies_prefix_stability (n : UInt64) :
        (Spec n) ⊨ □ (Lift PrefixStabilityInv) :=
      invariantSatisfies (Spec n) PrefixStabilityInv
        (init_establishes_inv n)
        next_preserves_inv

    end TlaCounterfactualFork
    end Agent
    end Astream

    def fork_offset_in_range_isl (at_off : UInt64) (len : UInt64) : Bool :=
      decide (at_off < len)
}
