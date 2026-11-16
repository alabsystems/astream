// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `abrew_guard.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `abrew_guard.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def cmd_guard_block_clamp (cand_blocks : UInt64) (block_cap : UInt64) : UInt64 :=
      if cand_blocks < block_cap then cand_blocks else block_cap

    def cmd_guard_rev_advance (cur_rev : UInt64) (cand_rev : UInt64) : UInt64 :=
      if cur_rev < cand_rev then cand_rev else cur_rev

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Command Guard Spec
    -- =======================================================================

    namespace Astream
    namespace Live
    namespace TlaAbrewCommandGuard

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

    structure CommandGuardState where
      blocked_count : UInt64
      block_cap : UInt64
      policy_rev : UInt64
      prev_rev : UInt64

    def AbrewCommandGuardInv (s : CommandGuardState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.blocked_count) (UInt64.toNat s.block_cap))
        (Nat.le (UInt64.toNat s.prev_rev) (UInt64.toNat s.policy_rev))

    def Init (block_cap : UInt64) (s : CommandGuardState) : Prop :=
      And
        (And (s.blocked_count = 0) (s.block_cap = block_cap))
        (And (s.policy_rev = 0) (s.prev_rev = 0))

    def guardStep (cand_blocks : UInt64) (cand_rev : UInt64) (s : CommandGuardState) : CommandGuardState :=
      CommandGuardState.mk
        (_root_.cmd_guard_block_clamp cand_blocks s.block_cap)
        s.block_cap
        (_root_.cmd_guard_rev_advance s.policy_rev cand_rev)
        s.policy_rev

    def Next (s : CommandGuardState) (s' : CommandGuardState) : Prop :=
      ∃ (cand_blocks : UInt64), ∃ (cand_rev : UInt64),
        s' = guardStep cand_blocks cand_rev s

    def Spec (block_cap : UInt64) : StateMachine CommandGuardState :=
      StateMachine.mk (Init block_cap) Next

    theorem block_clamp_le : forall (cand : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.cmd_guard_block_clamp cand cap)) (UInt64.toNat cap) :=
      fun cand cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cand))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cand cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem rev_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.cmd_guard_rev_advance cur cand)) :=
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

    theorem init_establishes_inv (block_cap : UInt64) (s : CommandGuardState)
      (hInit : Init block_cap s) :
      AbrewCommandGuardInv s :=
      And.intro
        (eq_zero_le s.blocked_count s.block_cap (And.left (And.left hInit)))
        (eq_zero_le s.prev_rev s.policy_rev (And.right (And.right hInit)))

    theorem next_preserves_inv (s : CommandGuardState) (s' : CommandGuardState)
      (_hInv : AbrewCommandGuardInv s) (hNext : Next s s') :
      AbrewCommandGuardInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (cr : UInt64), s' = guardStep cb cr s) =>
        Exists.elim hRest (fun (cr : UInt64) (hEq : s' = guardStep cb cr s) =>
          Eq.mpr
            (congrArg (fun (st : CommandGuardState) => AbrewCommandGuardInv st) hEq)
            (And.intro
              (block_clamp_le cb s.block_cap)
              (rev_monotone s.policy_rev cr))))

    theorem abrew_command_guard_safety_always (block_cap : UInt64) :
      Satisfies (Runs (Spec block_cap)) (Always (Lift AbrewCommandGuardInv)) :=
      invariantSatisfies (Spec block_cap) AbrewCommandGuardInv (init_establishes_inv block_cap) next_preserves_inv

    end TlaAbrewCommandGuard
    end Live
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def cmd_guard_blocks_within_cap_isl (blocked_count : UInt64) (block_cap : UInt64) : Bool :=
      decide (blocked_count <= block_cap)
}
