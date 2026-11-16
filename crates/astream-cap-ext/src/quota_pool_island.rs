// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `quota_pool.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `quota_pool.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def quota_bps_clamp (bps : UInt64) (max_bps : UInt64) : UInt64 :=
      if bps < max_bps then bps else max_bps

    def quota_rotation_advance (prev_rot : UInt64) (cand_rot : UInt64) : UInt64 :=
      if prev_rot < cand_rot then cand_rot else prev_rot

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Quota Pool Router Spec
    -- =======================================================================

    namespace Astream
    namespace Agent
    namespace TlaQuotaPoolRouter

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

    structure QuotaRouterState where
      remaining_bps : UInt64
      max_bps : UInt64
      rotations : UInt64
      prev_rotations : UInt64

    def QuotaRouterInv (s : QuotaRouterState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.remaining_bps) (UInt64.toNat s.max_bps))
        (Nat.le (UInt64.toNat s.prev_rotations) (UInt64.toNat s.rotations))

    def Init (s : QuotaRouterState) : Prop :=
      And
        (s.remaining_bps = 0)
        (And (s.rotations = 0) (s.prev_rotations = 0))

    def quotaStep (raw_bps : UInt64) (cand_rot : UInt64) (s : QuotaRouterState) : QuotaRouterState :=
      QuotaRouterState.mk
        (_root_.quota_bps_clamp raw_bps s.max_bps)
        s.max_bps
        (_root_.quota_rotation_advance s.rotations cand_rot)
        s.rotations

    def Next (s : QuotaRouterState) (s' : QuotaRouterState) : Prop :=
      ∃ (raw_bps : UInt64), ∃ (cand_rot : UInt64),
        s' = quotaStep raw_bps cand_rot s

    def Spec : StateMachine QuotaRouterState :=
      StateMachine.mk Init Next

    theorem bps_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.quota_bps_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem rot_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.quota_rotation_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
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

    theorem init_establishes_inv (s : QuotaRouterState) (hInit : Init s) :
      QuotaRouterInv s :=
      And.intro
        (zero_le_cap s.remaining_bps s.max_bps (And.left hInit))
        (eq_zero_le
          s.prev_rotations
          s.rotations
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : QuotaRouterState) (s' : QuotaRouterState)
      (_hInv : QuotaRouterInv s) (hNext : Next s s') :
      QuotaRouterInv s' :=
      Exists.elim hNext (fun (rb : UInt64) (hRest : ∃ (cr : UInt64), s' = quotaStep rb cr s) =>
        Exists.elim hRest (fun (cr : UInt64) (hEq : s' = quotaStep rb cr s) =>
          Eq.mpr
            (congrArg (fun (st : QuotaRouterState) => QuotaRouterInv st) hEq)
            (And.intro
              (bps_le_max rb s.max_bps)
              (rot_monotone s.rotations cr))))

    theorem quota_router_safety_always :
      Satisfies (Runs Spec) (Always (Lift QuotaRouterInv)) :=
      invariantSatisfies Spec QuotaRouterInv init_establishes_inv next_preserves_inv

    end TlaQuotaPoolRouter
    end Agent
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def quota_pool_healthy_isl (weekly_bps : UInt64) (five_hour_bps : UInt64) (floor_bps : UInt64) : Bool :=
      and (decide (floor_bps ≤ weekly_bps)) (decide (floor_bps ≤ five_hour_bps))
}
