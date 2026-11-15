// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `kafka_fetch_session.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `kafka_fetch_session.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def fetch_session_count_clamp (cand_count : UInt64) (max_sessions : UInt64) : UInt64 :=
      if cand_count < max_sessions then cand_count else max_sessions

    def fetch_session_id_advance (cur_id : UInt64) (cand_id : UInt64) : UInt64 :=
      if cur_id < cand_id then cand_id else cur_id

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & KIP-227 Fetch Session Spec
    -- =======================================================================

    namespace Astream
    namespace Kafka
    namespace TlaIncrementalFetchSession

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

    structure FetchSessionState where
      active_sessions : UInt64
      max_sessions : UInt64
      next_session_id : UInt64
      prev_session_id : UInt64

    def IncrementalFetchSessionInv (s : FetchSessionState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.active_sessions) (UInt64.toNat s.max_sessions))
        (Nat.le (UInt64.toNat s.prev_session_id) (UInt64.toNat s.next_session_id))

    def Init (max_sessions : UInt64) (s : FetchSessionState) : Prop :=
      And
        (And (s.active_sessions = 0) (s.max_sessions = max_sessions))
        (And (s.next_session_id = 0) (s.prev_session_id = 0))

    def sessionStep (cand_count : UInt64) (cand_id : UInt64) (s : FetchSessionState) : FetchSessionState :=
      FetchSessionState.mk
        (_root_.fetch_session_count_clamp cand_count s.max_sessions)
        s.max_sessions
        (_root_.fetch_session_id_advance s.next_session_id cand_id)
        s.next_session_id

    def Next (s : FetchSessionState) (s' : FetchSessionState) : Prop :=
      ∃ (cand_count : UInt64), ∃ (cand_id : UInt64),
        s' = sessionStep cand_count cand_id s

    def Spec (max_sessions : UInt64) : StateMachine FetchSessionState :=
      StateMachine.mk (Init max_sessions) Next

    theorem count_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.fetch_session_count_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem session_id_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.fetch_session_id_advance cur cand)) :=
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

    theorem init_establishes_inv (max_sessions : UInt64) (s : FetchSessionState)
      (hInit : Init max_sessions s) :
      IncrementalFetchSessionInv s :=
      And.intro
        (eq_zero_le s.active_sessions s.max_sessions (And.left (And.left hInit)))
        (eq_zero_le s.prev_session_id s.next_session_id (And.right (And.right hInit)))

    theorem next_preserves_inv (s : FetchSessionState) (s' : FetchSessionState)
      (_hInv : IncrementalFetchSessionInv s) (hNext : Next s s') :
      IncrementalFetchSessionInv s' :=
      Exists.elim hNext (fun (cc : UInt64) (hRest : ∃ (ci : UInt64), s' = sessionStep cc ci s) =>
        Exists.elim hRest (fun (ci : UInt64) (hEq : s' = sessionStep cc ci s) =>
          Eq.mpr
            (congrArg (fun (st : FetchSessionState) => IncrementalFetchSessionInv st) hEq)
            (And.intro
              (count_clamp_le cc s.max_sessions)
              (session_id_monotone s.next_session_id ci))))

    theorem incremental_fetch_session_safety_always (max_sessions : UInt64) :
      Satisfies (Runs (Spec max_sessions)) (Always (Lift IncrementalFetchSessionInv)) :=
      invariantSatisfies (Spec max_sessions) IncrementalFetchSessionInv (init_establishes_inv max_sessions) next_preserves_inv

    end TlaIncrementalFetchSession
    end Kafka
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def fetch_sessions_within_cap_isl (active : UInt64) (max_sessions : UInt64) : Bool :=
      decide (active <= max_sessions)
}
