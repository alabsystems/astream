// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for macOS live `aterm` executable overwrite protection
// (`Astream.Host.TlaAppBundleOverwriteGuard`, Island #283), mounted under `cfg(clean_islands)`.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def bundle_protected_hits_advance (prev : UInt64) (next : UInt64) : UInt64 :=
      if prev < next then next else prev

    def bundle_path_len_clamp (raw_len : UInt64) (max_len : UInt64) : UInt64 :=
      if raw_len < max_len then raw_len else max_len

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & App Bundle Guard Spec
    -- =======================================================================

    namespace Astream
    namespace Host
    namespace TlaAppBundleOverwriteGuard

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

    structure BundleGuardState where
      prev_blocked : UInt64
      blocked_writes : UInt64
      path_len : UInt64
      max_path_len : UInt64

    def BundleGuardSafetyInv (s : BundleGuardState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_blocked) (UInt64.toNat s.blocked_writes))
        (Nat.le (UInt64.toNat s.path_len) (UInt64.toNat s.max_path_len))

    def Init (s : BundleGuardState) : Prop :=
      And
        (s.prev_blocked = s.blocked_writes)
        (Nat.le (UInt64.toNat s.path_len) (UInt64.toNat s.max_path_len))

    def checkWriteStep (cand_blocked : UInt64) (raw_len : UInt64) (s : BundleGuardState) : BundleGuardState :=
      BundleGuardState.mk
        s.blocked_writes
        (_root_.bundle_protected_hits_advance s.blocked_writes cand_blocked)
        (_root_.bundle_path_len_clamp raw_len s.max_path_len)
        s.max_path_len

    def Next (s : BundleGuardState) (s_next : BundleGuardState) : Prop :=
      ∃ (cand_blocked : UInt64), ∃ (raw_len : UInt64),
        s_next = checkWriteStep cand_blocked raw_len s

    def Spec : StateMachine BundleGuardState :=
      StateMachine.mk Init Next

    theorem blocked_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.bundle_protected_hits_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem plen_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.bundle_path_len_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : BundleGuardState) (hInit : Init s) :
      BundleGuardSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_blocked s.blocked_writes (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : BundleGuardState) (s_next : BundleGuardState)
      (_hInv : BundleGuardSafetyInv s) (hNext : Next s s_next) :
      BundleGuardSafetyInv s_next :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (rl : UInt64), s_next = checkWriteStep cb rl s) =>
        Exists.elim hRest (fun (rl : UInt64) (hEq : s_next = checkWriteStep cb rl s) =>
          Eq.mpr
            (congrArg (fun (st : BundleGuardState) => BundleGuardSafetyInv st) hEq)
            (And.intro
              (blocked_ge_prev s.blocked_writes cb)
              (plen_le_cap rl s.max_path_len))))

    theorem bundle_guard_safety_always :
      Satisfies (Runs Spec) (Always (Lift BundleGuardSafetyInv)) :=
      invariantSatisfies Spec BundleGuardSafetyInv init_establishes_inv next_preserves_inv

    end TlaAppBundleOverwriteGuard
    end Host
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def bundle_mutation_allowed_isl (is_live_executable : UInt64) : Bool :=
      decide (is_live_executable = (0 : UInt64))
}
