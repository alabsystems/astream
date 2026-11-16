// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `inbox_wire.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `inbox_wire.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def inbox_seq_advance (cur_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if cur_seq < cand_seq then cand_seq else cur_seq

    def inbox_body_clamp (body_len : UInt64) (max_bytes : UInt64) : UInt64 :=
      if body_len < max_bytes then body_len else max_bytes

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Inbox Mail Envelope Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaInboxMailCodec

    def Behavior (State : Type) : Type := Nat → State

    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun (k : Nat) => b (Nat.add n k)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (n : Nat), P (drop n b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (n : Nat), M.Next (b n) (b (Nat.add n 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (P : Formula State) (Q : Formula State) : Prop :=
      ∀ (b : Behavior State), P b → Q b

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

    structure InboxMailState where
      mail_seq : UInt64
      prev_seq : UInt64
      body_bytes : UInt64
      max_mail_bytes : UInt64

    def InboxMailInv (s : InboxMailState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.mail_seq))
        (Nat.le (UInt64.toNat s.body_bytes) (UInt64.toNat s.max_mail_bytes))

    def Init (s : InboxMailState) : Prop :=
      And
        (s.body_bytes = 0)
        (And (s.mail_seq = 0) (s.prev_seq = 0))

    def deliverMailStep (cand_seq : UInt64) (raw_body : UInt64) (s : InboxMailState) : InboxMailState :=
      InboxMailState.mk
        (_root_.inbox_seq_advance s.mail_seq cand_seq)
        s.mail_seq
        (_root_.inbox_body_clamp raw_body s.max_mail_bytes)
        s.max_mail_bytes

    def Next (s : InboxMailState) (s' : InboxMailState) : Prop :=
      ∃ (cand_seq : UInt64), ∃ (raw_body : UInt64),
        s' = deliverMailStep cand_seq raw_body s

    def Spec : StateMachine InboxMailState :=
      StateMachine.mk Init Next

    theorem seq_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.inbox_seq_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem body_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.inbox_body_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) (hB : b = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : InboxMailState) (hInit : Init s) :
      InboxMailInv s :=
      And.intro
        (eq_zero_le
          s.prev_seq
          s.mail_seq
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.body_bytes s.max_mail_bytes (And.left hInit))

    theorem next_preserves_inv (s : InboxMailState) (s' : InboxMailState)
      (_hInv : InboxMailInv s) (hNext : Next s s') :
      InboxMailInv s' :=
      Exists.elim hNext (fun (cs : UInt64) (hRest : ∃ (rb : UInt64), s' = deliverMailStep cs rb s) =>
        Exists.elim hRest (fun (rb : UInt64) (hEq : s' = deliverMailStep cs rb s) =>
          Eq.mpr
            (congrArg (fun (st : InboxMailState) => InboxMailInv st) hEq)
            (And.intro
              (seq_monotone s.mail_seq cs)
              (body_le_max rb s.max_mail_bytes))))

    theorem inbox_mail_safety_always :
      Satisfies (Runs Spec) (Always (Lift InboxMailInv)) :=
      invariantSatisfies Spec InboxMailInv init_establishes_inv next_preserves_inv

    end TlaInboxMailCodec
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def inbox_body_within_cap_isl (body_len : UInt64) (max_bytes : UInt64) : Bool :=
      decide (body_len ≤ max_bytes)
}
