// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `nonce_challenge.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `nonce_challenge.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def nonce_pending_clamp (cand_pending : UInt64) (max_pending : UInt64) : UInt64 :=
      if cand_pending < max_pending then cand_pending else max_pending

    def nonce_seq_advance (cur_seq : UInt64) (cand_seq : UInt64) : UInt64 :=
      if cur_seq < cand_seq then cand_seq else cur_seq

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Nonce Challenge Ring Spec
    -- =======================================================================

    namespace Astream
    namespace Cap
    namespace TlaNonceChallengeRing

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

    structure NonceChallengeState where
      pending_count : UInt64
      max_pending : UInt64
      challenge_seq : UInt64
      prev_seq : UInt64

    def NonceChallengeRingInv (s : NonceChallengeState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.pending_count) (UInt64.toNat s.max_pending))
        (Nat.le (UInt64.toNat s.prev_seq) (UInt64.toNat s.challenge_seq))

    def Init (max_pending : UInt64) (s : NonceChallengeState) : Prop :=
      And
        (And (s.pending_count = 0) (s.max_pending = max_pending))
        (And (s.challenge_seq = 0) (s.prev_seq = 0))

    def issueChallengeStep (cand_pending : UInt64) (cand_seq : UInt64) (s : NonceChallengeState) : NonceChallengeState :=
      NonceChallengeState.mk
        (_root_.nonce_pending_clamp cand_pending s.max_pending)
        s.max_pending
        (_root_.nonce_seq_advance s.challenge_seq cand_seq)
        s.challenge_seq

    def Next (s : NonceChallengeState) (s' : NonceChallengeState) : Prop :=
      ∃ (cand_pending : UInt64), ∃ (cand_seq : UInt64),
        s' = issueChallengeStep cand_pending cand_seq s

    def Spec (max_pending : UInt64) : StateMachine NonceChallengeState :=
      StateMachine.mk (Init max_pending) Next

    theorem pending_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.nonce_pending_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem seq_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.nonce_seq_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem eq_zero_le (a : UInt64) (b : UInt64) (hA : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hA)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_pending : UInt64) (s : NonceChallengeState)
      (hInit : Init max_pending s) :
      NonceChallengeRingInv s :=
      And.intro
        (eq_zero_le s.pending_count s.max_pending (And.left (And.left hInit)))
        (eq_zero_le s.prev_seq s.challenge_seq (And.right (And.right hInit)))

    theorem next_preserves_inv (s : NonceChallengeState) (s' : NonceChallengeState)
      (_hInv : NonceChallengeRingInv s) (hNext : Next s s') :
      NonceChallengeRingInv s' :=
      Exists.elim hNext (fun (cp : UInt64) (hRest : ∃ (cs : UInt64), s' = issueChallengeStep cp cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = issueChallengeStep cp cs s) =>
          Eq.mpr
            (congrArg (fun (st : NonceChallengeState) => NonceChallengeRingInv st) hEq)
            (And.intro
              (pending_clamp_le cp s.max_pending)
              (seq_monotone s.challenge_seq cs))))

    theorem nonce_challenge_ring_safety_always (max_pending : UInt64) :
      Satisfies (Runs (Spec max_pending)) (Always (Lift NonceChallengeRingInv)) :=
      invariantSatisfies (Spec max_pending) NonceChallengeRingInv (init_establishes_inv max_pending) next_preserves_inv

    end TlaNonceChallengeRing
    end Cap
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def nonce_pending_within_cap_isl (pending : UInt64) (max_pending : UInt64) : Bool :=
      decide (pending <= max_pending)
}
