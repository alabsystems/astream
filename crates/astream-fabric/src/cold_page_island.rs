// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `cold_page.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `cold_page.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def cold_hot_floor_advance (cur_floor : UInt64) (proposed_floor : UInt64) : UInt64 :=
      if cur_floor < proposed_floor then proposed_floor else cur_floor

    def cold_resident_clamp (resident_bytes : UInt64) (budget_bytes : UInt64) : UInt64 :=
      if resident_bytes < budget_bytes then resident_bytes else budget_bytes

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Cold Prefix Eviction Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaColdPrefixEvict
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

    structure ColdPageState where
      prev_floor : UInt64
      hot_floor : UInt64
      resident : UInt64
      budget : UInt64

    def ColdEvictInv (s : ColdPageState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_floor) (UInt64.toNat s.hot_floor))
        (Nat.le (UInt64.toNat s.resident) (UInt64.toNat s.budget))

    def Init (s : ColdPageState) : Prop :=
      And
        (s.prev_floor = s.hot_floor)
        (Nat.le (UInt64.toNat s.resident) (UInt64.toNat s.budget))

    def evictStep (proposed_floor : UInt64) (raw_res : UInt64) (s : ColdPageState) : ColdPageState :=
      ColdPageState.mk
        s.hot_floor
        (_root_.cold_hot_floor_advance s.hot_floor proposed_floor)
        (_root_.cold_resident_clamp raw_res s.budget)
        s.budget

    def Next (s : ColdPageState) (s' : ColdPageState) : Prop :=
      ∃ (proposed_floor : UInt64), ∃ (raw_res : UInt64),
        s' = evictStep proposed_floor raw_res s

    def Spec : StateMachine ColdPageState :=
      StateMachine.mk Init Next

    theorem floor_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.cold_hot_floor_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem resident_le_budget : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.cold_resident_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : ColdPageState) (hInit : Init s) :
      ColdEvictInv s :=
      And.intro
        (uint64_eq_le s.prev_floor s.hot_floor (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : ColdPageState) (s' : ColdPageState)
      (_hInv : ColdEvictInv s) (hNext : Next s s') :
      ColdEvictInv s' :=
      Exists.elim hNext (fun (pf : UInt64) (hRest : ∃ (rr : UInt64), s' = evictStep pf rr s) =>
        Exists.elim hRest (fun (rr : UInt64) (hEq : s' = evictStep pf rr s) =>
          Eq.mpr
            (congrArg (fun (st : ColdPageState) => ColdEvictInv st) hEq)
            (And.intro
              (floor_ge_prev s.hot_floor pf)
              (resident_le_budget rr s.budget))))

    theorem cold_evict_safety_always :
      Satisfies Spec (Always (Lift ColdEvictInv)) :=
      invariantSatisfies Spec ColdEvictInv init_establishes_inv next_preserves_inv

    end TlaColdPrefixEvict
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def cold_is_evicted_isl (seq : UInt64) (hot_floor : UInt64) : Bool :=
      decide (seq < hot_floor)
}
