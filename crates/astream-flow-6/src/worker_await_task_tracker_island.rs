// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `aterm ctl await task @<sid>:<rev>` worker swarm wakeup tracking
// (`Astream.Agent.TlaWorkerAwaitTaskTracker`, Island #278), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def await_tracker_rev_advance (cur_rev : UInt64) (next_rev : UInt64) : UInt64 :=
      if cur_rev < next_rev then next_rev else cur_rev

    def await_tracker_watch_clamp (count : UInt64) (max_watched : UInt64) : UInt64 :=
      if count < max_watched then count else max_watched

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Worker Await Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaWorkerAwaitTaskTracker

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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next)
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
      (hStep : ∀ (s : State) (s_next : State), Inv s → M.Next s s_next → Inv s_next) :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    structure WorkerAwaitState where
      prev_rev : UInt64
      rev : UInt64
      watched : UInt64
      max_watched : UInt64

    def WorkerAwaitSafetyInv (s : WorkerAwaitState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_rev) (UInt64.toNat s.rev))
        (Nat.le (UInt64.toNat s.watched) (UInt64.toNat s.max_watched))

    def Init (s : WorkerAwaitState) : Prop :=
      And
        (s.prev_rev = s.rev)
        (Nat.le (UInt64.toNat s.watched) (UInt64.toNat s.max_watched))

    def observeWorkerStep (cand_rev : UInt64) (raw_watched : UInt64) (s : WorkerAwaitState) : WorkerAwaitState :=
      WorkerAwaitState.mk
        s.rev
        (_root_.await_tracker_rev_advance s.rev cand_rev)
        (_root_.await_tracker_watch_clamp raw_watched s.max_watched)
        s.max_watched

    def Next (s : WorkerAwaitState) (s_next : WorkerAwaitState) : Prop :=
      ∃ (cand_rev : UInt64), ∃ (raw_watched : UInt64),
        s_next = observeWorkerStep cand_rev raw_watched s

    def Spec : StateMachine WorkerAwaitState :=
      StateMachine.mk Init Next

    theorem rev_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.await_tracker_rev_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem watched_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.await_tracker_watch_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : WorkerAwaitState) (hInit : Init s) :
      WorkerAwaitSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_rev s.rev (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : WorkerAwaitState) (s_next : WorkerAwaitState)
      (_hInv : WorkerAwaitSafetyInv s) (hNext : Next s s_next) :
      WorkerAwaitSafetyInv s_next :=
      Exists.elim hNext (fun (cr : UInt64) (hRest : ∃ (rw : UInt64), s_next = observeWorkerStep cr rw s) =>
        Exists.elim hRest (fun (rw : UInt64) (hEq : s_next = observeWorkerStep cr rw s) =>
          Eq.mpr
            (congrArg (fun (st : WorkerAwaitState) => WorkerAwaitSafetyInv st) hEq)
            (And.intro
              (rev_ge_prev s.rev cr)
              (watched_le_cap rw s.max_watched))))

    theorem worker_await_safety_always :
      Satisfies (Runs Spec) (Always (Lift WorkerAwaitSafetyInv)) :=
      invariantSatisfies Spec WorkerAwaitSafetyInv init_establishes_inv next_preserves_inv

    end TlaWorkerAwaitTaskTracker
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def worker_rev_advanced_isl (since_rev : UInt64) (cur_rev : UInt64) : Bool :=
      decide (since_rev < cur_rev)
}
