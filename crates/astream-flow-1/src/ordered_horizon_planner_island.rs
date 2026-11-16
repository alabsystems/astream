// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for `aterm-link` Ordered-tier horizon & pipeline-window planning
// (`Astream.Broker.TlaOrderedHorizonPlanner`), mounted under `cfg(clean_islands)` in
// `ordered_horizon_planner.rs`. Proves `durableHead <= orderedHead` and
// `windowUsed <= maxWindow` across barrier-ordered pipelined batches and horizon full flushes.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def ordered_durable_clamp (durable : UInt64) (ordered : UInt64) : UInt64 :=
      if durable < ordered then durable else ordered

    def ordered_window_clamp (in_flight : UInt64) (max_window : UInt64) : UInt64 :=
      if in_flight < max_window then in_flight else max_window

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaOrderedHorizonPlanner

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

    -- ========================================================================
    -- 3. Ordered-Tier Barrier & Horizon Flush State Machine
    -- ========================================================================

    structure HorizonState where
      durableHead : UInt64
      orderedHead : UInt64
      windowUsed  : UInt64
      maxWindow   : UInt64

    def OrderedDurabilityInv (s : HorizonState) : Prop :=
      Nat.le (UInt64.toNat s.durableHead) (UInt64.toNat s.orderedHead) ∧
      Nat.le (UInt64.toNat s.windowUsed) (UInt64.toNat s.maxWindow)

    def Init (maxWindow : UInt64) (s : HorizonState) : Prop :=
      s.durableHead = (0 : UInt64) ∧
      s.orderedHead = (0 : UInt64) ∧
      s.windowUsed = (0 : UInt64) ∧
      s.maxWindow = maxWindow

    def StepBatchOrFlush (rawDurable newOrdered rawWindow : UInt64)
        (s sNext : HorizonState) : Prop :=
      sNext.durableHead = _root_.ordered_durable_clamp rawDurable newOrdered ∧
      sNext.orderedHead = newOrdered ∧
      sNext.windowUsed = _root_.ordered_window_clamp rawWindow s.maxWindow ∧
      sNext.maxWindow = s.maxWindow

    def Next (s sNext : HorizonState) : Prop :=
      ∃ rd : UInt64, ∃ no : UInt64, ∃ rw : UInt64, StepBatchOrFlush rd no rw s sNext

    def Spec (maxWindow : UInt64) : StateMachine HorizonState :=
      StateMachine.mk (Init maxWindow) Next

    theorem durable_clamp_le : forall (d : UInt64) (o : UInt64),
        Nat.le (UInt64.toNat (_root_.ordered_durable_clamp d o)) (UInt64.toNat o) :=
      fun d o => Decidable.casesOn
        (motive := fun (dec : Decidable (LT.lt d o)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) dec (fun _ => o) (fun _ => d))) (UInt64.toNat o))
        (instDecidableUInt64Lt d o)
        (fun _ => @Nat.le.refl (UInt64.toNat o))
        (fun hLt => Nat.le_of_lt hLt)

    theorem window_clamp_le : forall (w : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.ordered_window_clamp w cap)) (UInt64.toNat cap) :=
      fun w cap => Decidable.casesOn
        (motive := fun (dec : Decidable (LT.lt w cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) dec (fun _ => cap) (fun _ => w))) (UInt64.toNat cap))
        (instDecidableUInt64Lt w cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_u64_le (x : UInt64) (cap : UInt64) (hZero : x = (0 : UInt64)) :
        Nat.le (UInt64.toNat x) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (maxWindow : UInt64) (s : HorizonState)
        (hInit : Init maxWindow s) : OrderedDurabilityInv s :=
      And.intro
        (zero_u64_le s.durableHead s.orderedHead hInit.1)
        (zero_u64_le s.windowUsed s.maxWindow hInit.2.2.1)

    theorem step_preserves_inv (rd no rw : UInt64) (s sNext : HorizonState)
        (hAct : StepBatchOrFlush rd no rw s sNext) : OrderedDurabilityInv sNext :=
      let hD1 : Nat.le (UInt64.toNat sNext.durableHead) (UInt64.toNat no) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat no)) hAct.1)
          (durable_clamp_le rd no)
      let hD2 : Nat.le (UInt64.toNat sNext.durableHead) (UInt64.toNat sNext.orderedHead) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.durableHead) (UInt64.toNat y)) hAct.2.1)
          hD1
      let hW1 : Nat.le (UInt64.toNat sNext.windowUsed) (UInt64.toNat s.maxWindow) :=
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxWindow)) hAct.2.2.1)
          (window_clamp_le rw s.maxWindow)
      let hW2 : Nat.le (UInt64.toNat sNext.windowUsed) (UInt64.toNat sNext.maxWindow) :=
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.windowUsed) (UInt64.toNat y)) hAct.2.2.2)
          hW1
      And.intro hD2 hW2

    theorem next_preserves_inv (s sNext : HorizonState)
        (_hInv : OrderedDurabilityInv s) (hNext : Next s sNext) :
        OrderedDurabilityInv sNext :=
      Exists.elim hNext (fun rd hEx1 =>
        Exists.elim hEx1 (fun no hEx2 =>
          Exists.elim hEx2 (fun rw hAct => step_preserves_inv rd no rw s sNext hAct)))

    theorem spec_satisfies_ordered_durability (maxWindow : UInt64) :
        Satisfies (Spec maxWindow) (Always (Lift OrderedDurabilityInv)) :=
      invariantSatisfies (Spec maxWindow) OrderedDurabilityInv
        (init_establishes_inv maxWindow)
        next_preserves_inv

    end TlaOrderedHorizonPlanner
    end Broker
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def ordered_horizon_elapsed_isl (elapsed_ms : UInt64) (horizon_ms : UInt64) : Bool :=
      decide (horizon_ms ≤ elapsed_ms)
}
