// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `barrier_route.rs`, out of line so that only a Trust compiler opens
// it: no stock rustc can lex `clean { ... }`. `barrier_route.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def barrier_active_slots_clamp (slots : UInt64) (max_slots : UInt64) : UInt64 :=
      if slots < max_slots then slots else max_slots

    def barrier_settled_advance (prev : UInt64) (cand : UInt64) : UInt64 :=
      if prev < cand then cand else prev

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & §5.4 Barrier Router Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaBarrierRouter
    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop
    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)
    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      Nat.rec
        (motive := fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun hNext => hStep (b k) (b (Nat.succ k)) ih hNext)
            (fun hStutter => Eq.mpr (congrArg I hStutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        Satisfies M (Always (Lift I)) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    structure BarrierRouterState where
      active_slots : UInt64
      max_slots : UInt64
      settled_floor : UInt64
      prev_settled : UInt64

    def BarrierRouterInv (s : BarrierRouterState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.active_slots) (UInt64.toNat s.max_slots))
        (Nat.le (UInt64.toNat s.prev_settled) (UInt64.toNat s.settled_floor))

    def Init (s : BarrierRouterState) : Prop :=
      And
        (s.active_slots = 0)
        (And (s.settled_floor = 0) (s.prev_settled = 0))

    def routerStep (raw_slots : UInt64) (cand_settled : UInt64) (s : BarrierRouterState) : BarrierRouterState :=
      BarrierRouterState.mk
        (_root_.barrier_active_slots_clamp raw_slots s.max_slots)
        s.max_slots
        (_root_.barrier_settled_advance s.settled_floor cand_settled)
        s.settled_floor

    def Next (s : BarrierRouterState) (s' : BarrierRouterState) : Prop :=
      ∃ (raw_slots : UInt64), ∃ (cand_settled : UInt64),
        s' = routerStep raw_slots cand_settled s

    def Spec : StateMachine BarrierRouterState :=
      StateMachine.mk Init Next

    theorem slots_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.barrier_active_slots_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem settled_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.barrier_settled_advance prev cand)) :=
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

    theorem init_establishes_inv (s : BarrierRouterState) (hInit : Init s) :
      BarrierRouterInv s :=
      And.intro
        (zero_le_cap s.active_slots s.max_slots (And.left hInit))
        (eq_zero_le
          s.prev_settled
          s.settled_floor
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : BarrierRouterState) (s' : BarrierRouterState)
      (_hInv : BarrierRouterInv s) (hNext : Next s s') :
      BarrierRouterInv s' :=
      Exists.elim hNext (fun (rs : UInt64) (hRest : ∃ (cs : UInt64), s' = routerStep rs cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = routerStep rs cs s) =>
          Eq.mpr
            (congrArg (fun (st : BarrierRouterState) => BarrierRouterInv st) hEq)
            (And.intro
              (slots_le_max rs s.max_slots)
              (settled_monotone s.settled_floor cs))))

    theorem barrier_router_safety_always :
      Satisfies Spec (Always (Lift BarrierRouterInv)) :=
      invariantSatisfies Spec BarrierRouterInv init_establishes_inv next_preserves_inv

    end TlaBarrierRouter
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def barrier_quorum_reached_isl (acked : UInt64) (required : UInt64) : Bool :=
      decide (required ≤ acked)
}
