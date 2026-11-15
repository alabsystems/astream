// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `boot_fence.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `boot_fence.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def boot_fence_epoch_advance (cur_epoch : UInt64) (cand_epoch : UInt64) : UInt64 :=
      if cur_epoch < cand_epoch then cand_epoch else cur_epoch

    def boot_unflushed_clamp (unflushed : UInt64) (committed : UInt64) : UInt64 :=
      if unflushed < committed then unflushed else committed

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Boot-Epoch Fence Spec
    -- =======================================================================

    namespace Astream
    namespace Engine
    namespace TlaBootEpochFence

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

    structure BootFenceState where
      epoch : UInt64
      prev_epoch : UInt64
      trusted_head : UInt64
      durable_head : UInt64

    def BootFenceInv (s : BootFenceState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_epoch) (UInt64.toNat s.epoch))
        (Nat.le (UInt64.toNat s.trusted_head) (UInt64.toNat s.durable_head))

    def Init (s : BootFenceState) : Prop :=
      And
        (s.trusted_head = 0)
        (And (s.epoch = 0) (s.prev_epoch = 0))

    def reconcileBootStep (cand_epoch : UInt64) (raw_head : UInt64) (s : BootFenceState) : BootFenceState :=
      BootFenceState.mk
        (_root_.boot_fence_epoch_advance s.epoch cand_epoch)
        s.epoch
        (_root_.boot_unflushed_clamp raw_head s.durable_head)
        s.durable_head

    def Next (s : BootFenceState) (s' : BootFenceState) : Prop :=
      ∃ (cand_epoch : UInt64), ∃ (raw_head : UInt64),
        s' = reconcileBootStep cand_epoch raw_head s

    def Spec : StateMachine BootFenceState :=
      StateMachine.mk Init Next

    theorem epoch_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.boot_fence_epoch_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem clamp_le_durable : forall (raw : UInt64) (dur : UInt64),
        Nat.le (UInt64.toNat (_root_.boot_unflushed_clamp raw dur)) (UInt64.toNat dur) :=
      fun raw dur => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw dur)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => dur) (fun _ => raw))) (UInt64.toNat dur))
        (instDecidableUInt64Lt raw dur)
        (fun _ => Nat.le.refl (UInt64.toNat dur))
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

    theorem init_establishes_inv (s : BootFenceState) (hInit : Init s) :
      BootFenceInv s :=
      And.intro
        (eq_zero_le
          s.prev_epoch
          s.epoch
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.trusted_head s.durable_head (And.left hInit))

    theorem next_preserves_inv (s : BootFenceState) (s' : BootFenceState)
      (_hInv : BootFenceInv s) (hNext : Next s s') :
      BootFenceInv s' :=
      Exists.elim hNext (fun (ce : UInt64) (hRest : ∃ (rh : UInt64), s' = reconcileBootStep ce rh s) =>
        Exists.elim hRest (fun (rh : UInt64) (hEq : s' = reconcileBootStep ce rh s) =>
          Eq.mpr
            (congrArg (fun (st : BootFenceState) => BootFenceInv st) hEq)
            (And.intro
              (epoch_monotone s.epoch ce)
              (clamp_le_durable rh s.durable_head))))

    theorem boot_fence_safety_always :
      Satisfies (Runs Spec) (Always (Lift BootFenceInv)) :=
      invariantSatisfies Spec BootFenceInv init_establishes_inv next_preserves_inv

    end TlaBootEpochFence
    end Engine
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def boot_epoch_fresh_isl (recorded_epoch : UInt64) (fence_epoch : UInt64) : Bool :=
      decide (fence_epoch ≤ recorded_epoch)
}
