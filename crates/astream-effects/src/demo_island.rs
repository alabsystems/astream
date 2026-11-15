// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `demo.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `demo.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def demo_clamp_poll_index (idx : UInt64) (max_reads : UInt64) : UInt64 :=
      if idx < max_reads then idx else max_reads

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Effects.TlaDemoPoll)
    -- ========================================================================
    namespace Astream
    namespace Effects
    namespace TlaDemoPoll

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (k : Nat) (b : Behavior State) : Behavior State :=
      fun (n : Nat) => b (Nat.add k n)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (k : Nat), P (drop k b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        M.Init (b 0) ∧ ∀ (k : Nat), M.Next (b k) (b (Nat.add k 1))

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun (b : Behavior State) => P (b 0)

    def Satisfies {State : Type} (SpecF : Formula State) (PropF : Formula State) : Prop :=
      ∀ (b : Behavior State), SpecF b → PropF b

    theorem invariantAt
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s')
      (b : Behavior State)
      (hRun : Runs M b)
      (k : Nat) :
      Inv (b k) :=
      Nat.rec
        (hInit (b 0) (And.left hRun))
        (fun (j : Nat) (ih : Inv (b j)) =>
          hStep (b j) (b (Nat.add j 1)) ih (And.right hRun j))
        k

    theorem invariantSatisfies
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s') :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure PollState where
      idx : UInt64
      max_reads : UInt64

    def DemoPollBoundedInv (s : PollState) : Prop :=
      Nat.le (UInt64.toNat s.idx) (UInt64.toNat s.max_reads)

    def Init (s : PollState) : Prop :=
      s.idx = (0 : UInt64)

    def pollAction (requested : UInt64) (max_reads : UInt64) (_s : PollState) : PollState :=
      PollState.mk (_root_.demo_clamp_poll_index requested max_reads) max_reads

    def Next (s : PollState) (s' : PollState) : Prop :=
      ∃ (requested : UInt64), ∃ (max_reads : UInt64), s' = pollAction requested max_reads s

    def Spec : StateMachine PollState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (requested : UInt64) (max_reads : UInt64),
        Nat.le (UInt64.toNat (_root_.demo_clamp_poll_index requested max_reads)) (UInt64.toNat max_reads) :=
      fun requested max_reads => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt requested max_reads)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_reads) (fun _ => requested))) (UInt64.toNat max_reads))
        (instDecidableUInt64Lt requested max_reads)
        (fun _ => Nat.le.refl (UInt64.toNat max_reads))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : PollState) (hInit : Init s) :
      DemoPollBoundedInv s :=
      uint64_zero_le s.idx s.max_reads hInit

    theorem next_preserves_inv (s : PollState) (s' : PollState)
      (_hInv : DemoPollBoundedInv s) (hNext : Next s s') :
      DemoPollBoundedInv s' :=
      Exists.elim hNext (fun (requested : UInt64) (hEx : ∃ (max_reads : UInt64), s' = pollAction requested max_reads s) =>
        Exists.elim hEx (fun (max_reads : UInt64) (hEq : s' = pollAction requested max_reads s) =>
          Eq.mpr
            (congrArg (fun (st : PollState) => DemoPollBoundedInv st) hEq)
            (clamp_le_max requested max_reads)))

    theorem spec_satisfies_demo_poll_bounded :
      Satisfies (Runs Spec) (Always (Lift DemoPollBoundedInv)) :=
      invariantSatisfies Spec DemoPollBoundedInv init_establishes_inv next_preserves_inv

    end TlaDemoPoll
    end Effects
    end Astream

    def demo_poll_in_range_isl (idx : UInt64) (max_reads : UInt64) : Bool :=
      decide (idx < max_reads)
}
