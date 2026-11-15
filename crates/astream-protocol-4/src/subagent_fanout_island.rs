// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `subagent_fanout.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `subagent_fanout.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def fanout_rev_advance (cur_rev : UInt64) (cand_rev : UInt64) : UInt64 :=
      if cur_rev < cand_rev then cand_rev else cur_rev

    def fanout_active_clamp (active : UInt64) (max_workers : UInt64) : UInt64 :=
      if active < max_workers then active else max_workers

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Subagent Fan-Out Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaSubagentFanout

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

    structure FanoutState where
      rev : UInt64
      prev_rev : UInt64
      active_workers : UInt64
      max_workers : UInt64

    def FanoutInv (s : FanoutState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_rev) (UInt64.toNat s.rev))
        (Nat.le (UInt64.toNat s.active_workers) (UInt64.toNat s.max_workers))

    def Init (s : FanoutState) : Prop :=
      And
        (s.active_workers = 0)
        (And (s.rev = 0) (s.prev_rev = 0))

    def observeWorkerStep (cand_rev : UInt64) (cand_active : UInt64) (s : FanoutState) : FanoutState :=
      FanoutState.mk
        (_root_.fanout_rev_advance s.rev cand_rev)
        s.rev
        (_root_.fanout_active_clamp cand_active s.max_workers)
        s.max_workers

    def Next (s : FanoutState) (s' : FanoutState) : Prop :=
      ∃ (cand_rev : UInt64), ∃ (cand_active : UInt64),
        s' = observeWorkerStep cand_rev cand_active s

    def Spec : StateMachine FanoutState :=
      StateMachine.mk Init Next

    theorem rev_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.fanout_rev_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem active_le_max : forall (act : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.fanout_active_clamp act cap)) (UInt64.toNat cap) :=
      fun act cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt act cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => act))) (UInt64.toNat cap))
        (instDecidableUInt64Lt act cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
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

    theorem init_establishes_inv (s : FanoutState) (hInit : Init s) :
      FanoutInv s :=
      And.intro
        (eq_zero_le
          s.prev_rev
          s.rev
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.active_workers s.max_workers (And.left hInit))

    theorem next_preserves_inv (s : FanoutState) (s' : FanoutState)
      (_hInv : FanoutInv s) (hNext : Next s s') :
      FanoutInv s' :=
      Exists.elim hNext (fun (cr : UInt64) (hRest : ∃ (ca : UInt64), s' = observeWorkerStep cr ca s) =>
        Exists.elim hRest (fun (ca : UInt64) (hEq : s' = observeWorkerStep cr ca s) =>
          Eq.mpr
            (congrArg (fun (st : FanoutState) => FanoutInv st) hEq)
            (And.intro
              (rev_monotone s.rev cr)
              (active_le_max ca s.max_workers))))

    theorem subagent_fanout_safety_always :
      Satisfies (Runs Spec) (Always (Lift FanoutInv)) :=
      invariantSatisfies Spec FanoutInv init_establishes_inv next_preserves_inv

    end TlaSubagentFanout
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def fanout_rev_unseen_isl (since_rev : UInt64) (event_rev : UInt64) : Bool :=
      decide (since_rev < event_rev)
}
