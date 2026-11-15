// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `wire_keepalive_rtt.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `wire_keepalive_rtt.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def rto_floor_max (cand_rto_us : UInt64) (min_rto_us : UInt64) : UInt64 :=
      if cand_rto_us < min_rto_us then min_rto_us else cand_rto_us

    def rto_ceil_min (cand_rto_us : UInt64) (max_rto_us : UInt64) : UInt64 :=
      if cand_rto_us < max_rto_us then cand_rto_us else max_rto_us

    def ping_seq_advance (cur_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if cur_seq < cand_seq then cand_seq else cur_seq

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Keepalive RTT Spec
    -- =======================================================================

    namespace Astream
    namespace Wire
    namespace TlaKeepaliveRttEstimator

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

    structure RttState where
      rto_us : UInt64
      max_rto_us : UInt64
      acked_seq : UInt64
      prev_seq : UInt64

    def RttInv (s : RttState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.rto_us) (UInt64.toNat s.max_rto_us))
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.acked_seq))

    def Init (max_rto_us : UInt64) (s : RttState) : Prop :=
      And
        (And (s.rto_us = 0) (s.max_rto_us = max_rto_us))
        (And (s.acked_seq = 0) (s.prev_seq = 0))

    def rto_clamp_bounds_isl (cand_rto_us : UInt64) (min_rto_us : UInt64) (max_rto_us : UInt64) : UInt64 :=
      _root_.rto_ceil_min (_root_.rto_floor_max cand_rto_us min_rto_us) max_rto_us

    def rttStep (cand_rto : UInt64) (min_rto : UInt64) (cand_seq : UInt64) (s : RttState) : RttState :=
      RttState.mk
        (rto_clamp_bounds_isl cand_rto min_rto s.max_rto_us)
        s.max_rto_us
        (_root_.ping_seq_advance s.acked_seq cand_seq)
        s.acked_seq

    def Next (s : RttState) (s' : RttState) : Prop :=
      ∃ (cand_rto : UInt64), ∃ (min_rto : UInt64), ∃ (cand_seq : UInt64),
        s' = rttStep cand_rto min_rto cand_seq s

    def Spec (max_rto_us : UInt64) : StateMachine RttState :=
      StateMachine.mk (Init max_rto_us) Next

    theorem clamp_pair_le (x : UInt64) (hi : UInt64) :
      Nat.le
        (UInt64.toNat (_root_.rto_ceil_min x hi))
        (UInt64.toNat hi) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt x hi)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => hi) (fun _ => x))) (UInt64.toNat hi))
        (instDecidableUInt64Lt x hi)
        (fun _ => Nat.le.refl (UInt64.toNat hi))
        (fun hLt => Nat.le_of_lt hLt)

    theorem rto_clamp_le_max : forall (cand : UInt64) (lo : UInt64) (hi : UInt64),
        Nat.le (UInt64.toNat (rto_clamp_bounds_isl cand lo hi)) (UInt64.toNat hi) :=
      fun cand lo hi => clamp_pair_le (_root_.rto_floor_max cand lo) hi

    theorem seq_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.ping_seq_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_rto_us : UInt64) (s : RttState)
      (hInit : Init max_rto_us s) :
      RttInv s :=
      And.intro
        (eq_zero_le s.rto_us s.max_rto_us (And.left (And.left hInit)))
        (eq_zero_le s.prev_seq s.acked_seq (And.right (And.right hInit)))

    theorem next_preserves_inv (s : RttState) (s' : RttState)
      (_hInv : RttInv s) (hNext : Next s s') :
      RttInv s' :=
      Exists.elim hNext (fun (cr : UInt64) (h1 : ∃ (lo : UInt64), ∃ (cs : UInt64), s' = rttStep cr lo cs s) =>
        Exists.elim h1 (fun (lo : UInt64) (h2 : ∃ (cs : UInt64), s' = rttStep cr lo cs s) =>
          Exists.elim h2 (fun (cs : UInt64) (hEq : s' = rttStep cr lo cs s) =>
            Eq.mpr
              (congrArg (fun (st : RttState) => RttInv st) hEq)
              (And.intro
                (rto_clamp_le_max cr lo s.max_rto_us)
                (seq_monotone s.acked_seq cs)))))

    theorem keepalive_rtt_safety_always (max_rto_us : UInt64) :
      Satisfies (Runs (Spec max_rto_us)) (Always (Lift RttInv)) :=
      invariantSatisfies (Spec max_rto_us) RttInv (init_establishes_inv max_rto_us) next_preserves_inv

    end TlaKeepaliveRttEstimator
    end Wire
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def rto_within_max_isl (rto_us : UInt64) (max_rto_us : UInt64) : Bool :=
      decide (rto_us <= max_rto_us)
}
