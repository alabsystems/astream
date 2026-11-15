// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `record.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `record.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def record_client_seq_advance (cur_seq : UInt64) (proposed_seq : UInt64) : UInt64 :=
      if cur_seq < proposed_seq then proposed_seq else cur_seq

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaRecordSeq)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaRecordSeq

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
        And (M.Init (b 0)) (∀ (k : Nat), M.Next (b k) (b (Nat.add k 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

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

    -- ========================================================================
    -- 3. Record Client Sequence Monotonicity State Machine & Safety Theorem
    -- ========================================================================

    structure ClientSeqState where
      cur_seq : UInt64
      prev_seq : UInt64

    def ClientSeqMonotoneInv (s : ClientSeqState) : Prop :=
      Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.cur_seq)

    def Init (s : ClientSeqState) : Prop :=
      And (s.cur_seq = (0 : UInt64)) (s.prev_seq = (0 : UInt64))

    def proposeInAction (proposed_seq : UInt64) (s : ClientSeqState) : ClientSeqState :=
      ClientSeqState.mk
        (_root_.record_client_seq_advance s.cur_seq proposed_seq)
        s.cur_seq

    def Next (s : ClientSeqState) (s' : ClientSeqState) : Prop :=
      ∃ (proposed_seq : UInt64), s' = proposeInAction proposed_seq s

    def Spec : StateMachine ClientSeqState :=
      StateMachine.mk Init Next

    theorem advance_ge_cur : forall (cur_seq : UInt64) (proposed_seq : UInt64),
        Nat.le (UInt64.toNat cur_seq) (UInt64.toNat (_root_.record_client_seq_advance cur_seq proposed_seq)) :=
      fun cur_seq proposed_seq => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur_seq proposed_seq)) =>
          Nat.le (UInt64.toNat cur_seq)
            (UInt64.toNat (Decidable.casesOn
              (motive := fun _ => UInt64) d (fun _ => cur_seq) (fun _ => proposed_seq))))
        (instDecidableUInt64Lt cur_seq proposed_seq)
        (fun _ => Nat.le.refl (UInt64.toNat cur_seq))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat a) (UInt64.toNat x)) (Eq.symm hEq))
        (Nat.le.refl (UInt64.toNat a))

    theorem init_establishes_inv (s : ClientSeqState) (hInit : Init s) :
      ClientSeqMonotoneInv s :=
      uint64_eq_le
        s.prev_seq
        s.cur_seq
        (Eq.trans (And.right hInit) (Eq.symm (And.left hInit)))

    theorem next_preserves_inv (s : ClientSeqState) (s' : ClientSeqState)
      (_hInv : ClientSeqMonotoneInv s) (hNext : Next s s') :
      ClientSeqMonotoneInv s' :=
      Exists.elim hNext (fun (proposed_seq : UInt64) (hEq : s' = proposeInAction proposed_seq s) =>
        Eq.mpr
          (congrArg (fun (st : ClientSeqState) => ClientSeqMonotoneInv st) hEq)
          (advance_ge_cur s.cur_seq proposed_seq))

    theorem spec_satisfies_client_seq_monotonicity :
      Satisfies (Runs Spec) (Always (Lift ClientSeqMonotoneInv)) :=
      invariantSatisfies Spec ClientSeqMonotoneInv init_establishes_inv next_preserves_inv

    end TlaRecordSeq
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def record_tag_paints_screen_isl (tag : UInt8) : Bool :=
      decide (tag = 1)
}
