// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `pty_master_drain_budget.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `pty_master_drain_budget.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def pty_drain_bytes_clamp (candBytes : UInt64) (maxTurnBytes : UInt64) : UInt64 :=
      if candBytes < maxTurnBytes then candBytes else maxTurnBytes
    def pty_drain_reads_clamp (candReads : UInt64) (maxTurnReads : UInt64) : UInt64 :=
      if candReads < maxTurnReads then candReads else maxTurnReads

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Protocol Safety Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaPtyMasterDrainBudget
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
        Satisfies M (Always (Lift I)) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    structure PtyMasterDrainBudgetState where
      val_0 : UInt64
      cap_0 : UInt64
      val_1 : UInt64
      cap_1 : UInt64

    def PtyMasterDrainBudgetInv (s : PtyMasterDrainBudgetState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.val_0) (UInt64.toNat s.cap_0))
        (Nat.le (UInt64.toNat s.val_1) (UInt64.toNat s.cap_1))

    def Init (s : PtyMasterDrainBudgetState) : Prop :=
      And
        (s.val_0 = 0)
        (s.val_1 = 0)

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (s : PtyMasterDrainBudgetState) : PtyMasterDrainBudgetState :=
      PtyMasterDrainBudgetState.mk
        (_root_.pty_drain_bytes_clamp c_0 s.cap_0)
        s.cap_0
        (_root_.pty_drain_reads_clamp c_1 s.cap_1)
        s.cap_1

    def Next (s : PtyMasterDrainBudgetState) (s' : PtyMasterDrainBudgetState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64),
        s' = stepTransition c_0 c_1 s

    def Spec : StateMachine PtyMasterDrainBudgetState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.pty_drain_bytes_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.pty_drain_reads_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_u64 (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : PtyMasterDrainBudgetState) (hInit : Init s) :
      PtyMasterDrainBudgetInv s :=
      And.intro
        (zero_le_u64 s.val_0 s.cap_0 (And.left hInit))
        (zero_le_u64 s.val_1 s.cap_1 (And.right hInit))

    theorem next_preserves_inv (s : PtyMasterDrainBudgetState) (s' : PtyMasterDrainBudgetState)
      (_hInv : PtyMasterDrainBudgetInv s) (hNext : Next s s') :
      PtyMasterDrainBudgetInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hRest : ∃ (c_1 : UInt64), s' = stepTransition c_0 c_1 s) =>
        Exists.elim hRest (fun (c_1 : UInt64) (hEq : s' = stepTransition c_0 c_1 s) =>
          Eq.mpr
            (congrArg (fun (st : PtyMasterDrainBudgetState) => PtyMasterDrainBudgetInv st) hEq)
            (And.intro
              (helper_bound_0 c_0 s.cap_0)
              (helper_bound_1 c_1 s.cap_1))))

    theorem pty_master_drain_budget_safety_always :
      Satisfies Spec (Always (Lift PtyMasterDrainBudgetInv)) :=
      invariantSatisfies Spec PtyMasterDrainBudgetInv init_establishes_inv next_preserves_inv

    end TlaPtyMasterDrainBudget
    end Host
    end Astream

    def pty_drain_within_turn_cap_isl (drainedBytes : UInt64) (maxTurnBytes : UInt64) : Bool :=
      decide (drainedBytes < maxTurnBytes)
}
