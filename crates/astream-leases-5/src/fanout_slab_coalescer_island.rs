// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for pre-serialized wire-frame slab coalescing in `tail_loop`
// (`Astream.Broker.TlaFanoutSlabCoalescer`), mounted under `cfg(clean_islands)` in
// `fanout_slab_coalescer.rs`. Proves `slabCursor <= slabHead` and
// `coalescedWakes <= parkedSubscribers`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def slab_cursor_clamp (cursor : UInt64) (slab_head : UInt64) : UInt64 :=
      if cursor < slab_head then cursor else slab_head

    def slab_wakes_clamp (wakes : UInt64) (parked : UInt64) : UInt64 :=
      if wakes < parked then wakes else parked

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaFanoutSlabCoalescer)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaFanoutSlabCoalescer

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

    structure SlabState where
      slabCursor        : UInt64
      slabHead          : UInt64
      coalescedWakes    : UInt64
      parkedSubscribers : UInt64

    def FanoutSlabSafetyInv (s : SlabState) : Prop :=
      Nat.le (UInt64.toNat s.slabCursor) (UInt64.toNat s.slabHead) ∧
      Nat.le (UInt64.toNat s.coalescedWakes) (UInt64.toNat s.parkedSubscribers)

    def Init (parked : UInt64) (s : SlabState) : Prop :=
      s.slabCursor = (0 : UInt64) ∧
      s.slabHead = (0 : UInt64) ∧
      s.coalescedWakes = (0 : UInt64) ∧
      s.parkedSubscribers = parked

    def PublishSlab (rawCursor newHead rawWakes newParked : UInt64)
        (s sNext : SlabState) : Prop :=
      sNext.slabCursor = _root_.slab_cursor_clamp rawCursor newHead ∧
      sNext.slabHead = newHead ∧
      sNext.coalescedWakes = _root_.slab_wakes_clamp rawWakes newParked ∧
      sNext.parkedSubscribers = newParked

    def Next (s sNext : SlabState) : Prop :=
      ∃ rc : UInt64, ∃ nh : UInt64, ∃ rw : UInt64, ∃ np : UInt64,
        PublishSlab rc nh rw np s sNext

    def Spec (parked : UInt64) : StateMachine SlabState :=
      StateMachine.mk (Init parked) Next

    theorem cursor_clamp_le : forall (c : UInt64) (h : UInt64),
        Nat.le (UInt64.toNat (_root_.slab_cursor_clamp c h)) (UInt64.toNat h) :=
      fun c h => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt c h)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => h) (fun _ => c))) (UInt64.toNat h))
        (instDecidableUInt64Lt c h)
        (fun _ => Nat.le.refl (UInt64.toNat h))
        (fun hLt => Nat.le_of_lt hLt)

    theorem wakes_clamp_le : forall (w : UInt64) (p : UInt64),
        Nat.le (UInt64.toNat (_root_.slab_wakes_clamp w p)) (UInt64.toNat p) :=
      fun w p => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt w p)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => p) (fun _ => w))) (UInt64.toNat p))
        (instDecidableUInt64Lt w p)
        (fun _ => Nat.le.refl (UInt64.toNat p))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (parked : UInt64) (s : SlabState)
        (hInit : Init parked s) : FanoutSlabSafetyInv s :=
      And.intro
        (zero_u64_le s.slabCursor s.slabHead hInit.1)
        (zero_u64_le s.coalescedWakes s.parkedSubscribers hInit.2.2.1)

    theorem publish_preserves_inv (rc nh rw np : UInt64) (s sNext : SlabState)
        (hAct : PublishSlab rc nh rw np s sNext) : FanoutSlabSafetyInv sNext :=
      let hC1 : Nat.le (UInt64.toNat sNext.slabCursor) (UInt64.toNat nh) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat nh)) hAct.1)
          (cursor_clamp_le rc nh)
      let hC2 : Nat.le (UInt64.toNat sNext.slabCursor) (UInt64.toNat sNext.slabHead) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.slabCursor) (UInt64.toNat y)) hAct.2.1)
          hC1
      let hW1 : Nat.le (UInt64.toNat sNext.coalescedWakes) (UInt64.toNat np) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat np)) hAct.2.2.1)
          (wakes_clamp_le rw np)
      let hW2 : Nat.le (UInt64.toNat sNext.coalescedWakes) (UInt64.toNat sNext.parkedSubscribers) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.coalescedWakes) (UInt64.toNat y)) hAct.2.2.2)
          hW1
      And.intro hC2 hW2

    theorem next_preserves_inv (s sNext : SlabState)
        (_hInv : FanoutSlabSafetyInv s) (hNext : Next s sNext) :
        FanoutSlabSafetyInv sNext :=
      Exists.elim hNext (fun rc hEx1 =>
        Exists.elim hEx1 (fun nh hEx2 =>
          Exists.elim hEx2 (fun rw hEx3 =>
            Exists.elim hEx3 (fun np hAct => publish_preserves_inv rc nh rw np s sNext hAct))))

    theorem spec_satisfies_fanout_slab_safety (parked : UInt64) :
        Satisfies (Spec parked) (Always (Lift FanoutSlabSafetyInv)) :=
      invariantSatisfies (Spec parked) FanoutSlabSafetyInv
        (init_establishes_inv parked)
        next_preserves_inv

    end TlaFanoutSlabCoalescer
    end Broker
    end Astream

    -- ========================================================================
    -- 3. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def slab_cursor_behind_head_isl (cursor : UInt64) (slab_head : UInt64) : Bool :=
      decide (cursor < slab_head)
}
