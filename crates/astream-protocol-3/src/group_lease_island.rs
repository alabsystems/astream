// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `group_lease.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `group_lease.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def group_lease_gen_advance (cur_gen : UInt64) (cand_gen : UInt64) : UInt64 :=
      if cur_gen < cand_gen then cand_gen else cur_gen

    def group_lease_ttl_clamp (req_ttl : UInt64) (max_ttl : UInt64) : UInt64 :=
      if req_ttl < max_ttl then req_ttl else max_ttl

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Sticky Lease Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaGroupStickyLease

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

    structure StickyLeaseState where
      generation : UInt64
      prev_generation : UInt64
      lease_ttl_ms : UInt64
      max_ttl_ms : UInt64

    def StickyLeaseInv (s : StickyLeaseState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_generation) (UInt64.toNat s.generation))
        (Nat.le (UInt64.toNat s.lease_ttl_ms) (UInt64.toNat s.max_ttl_ms))

    def Init (s : StickyLeaseState) : Prop :=
      And
        (s.lease_ttl_ms = 0)
        (And (s.generation = 0) (s.prev_generation = 0))

    def rebalanceLeaseStep (cand_gen : UInt64) (req_ttl : UInt64) (s : StickyLeaseState) : StickyLeaseState :=
      StickyLeaseState.mk
        (_root_.group_lease_gen_advance s.generation cand_gen)
        s.generation
        (_root_.group_lease_ttl_clamp req_ttl s.max_ttl_ms)
        s.max_ttl_ms

    def Next (s : StickyLeaseState) (s' : StickyLeaseState) : Prop :=
      ∃ (cand_gen : UInt64), ∃ (req_ttl : UInt64),
        s' = rebalanceLeaseStep cand_gen req_ttl s

    def Spec : StateMachine StickyLeaseState :=
      StateMachine.mk Init Next

    theorem gen_monotone : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.group_lease_gen_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem ttl_le_max : forall (req : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.group_lease_ttl_clamp req cap)) (UInt64.toNat cap) :=
      fun req cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt req cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => req))) (UInt64.toNat cap))
        (instDecidableUInt64Lt req cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
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

    theorem init_establishes_inv (s : StickyLeaseState) (hInit : Init s) :
      StickyLeaseInv s :=
      And.intro
        (eq_zero_le
          s.prev_generation
          s.generation
          (And.right (And.right hInit))
          (And.left (And.right hInit)))
        (zero_le_cap s.lease_ttl_ms s.max_ttl_ms (And.left hInit))

    theorem next_preserves_inv (s : StickyLeaseState) (s' : StickyLeaseState)
      (_hInv : StickyLeaseInv s) (hNext : Next s s') :
      StickyLeaseInv s' :=
      Exists.elim hNext (fun (cg : UInt64) (hRest : ∃ (rt : UInt64), s' = rebalanceLeaseStep cg rt s) =>
        Exists.elim hRest (fun (rt : UInt64) (hEq : s' = rebalanceLeaseStep cg rt s) =>
          Eq.mpr
            (congrArg (fun (st : StickyLeaseState) => StickyLeaseInv st) hEq)
            (And.intro
              (gen_monotone s.generation cg)
              (ttl_le_max rt s.max_ttl_ms))))

    theorem sticky_lease_safety_always :
      Satisfies Spec (Always (Lift StickyLeaseInv)) :=
      invariantSatisfies Spec StickyLeaseInv init_establishes_inv next_preserves_inv

    end TlaGroupStickyLease
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def group_lease_gen_matches_isl (req_gen : UInt64) (cur_gen : UInt64) : Bool :=
      decide (req_gen = cur_gen)
}
