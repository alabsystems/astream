// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `server.rs` (consumer-group generation & multi-partition bounds),
// out of line so that only a Trust compiler opens it (`cfg(clean_islands)`).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    -- ========================================================================

    -- Monotonically advance a Kafka consumer-group coordinator generation id.
    def kafka_generation_advance (cur_gen : UInt64) (next_gen : UInt64) : UInt64 :=
      if cur_gen < next_gen then next_gen else cur_gen

    -- Clamp a requested topic partition count to `max_parts`.
    def kafka_partition_clamp (requested : UInt64) (max_parts : UInt64) : UInt64 :=
      if requested < max_parts then requested else max_parts

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Kafka.TlaConsumerGroup)
    -- ========================================================================
    namespace Astream
    namespace Kafka
    namespace TlaConsumerGroup

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

    prefix:100 "□" => _root_.Astream.Kafka.TlaConsumerGroup.Always
    infixl:45 " ⊨ " => _root_.Astream.Kafka.TlaConsumerGroup.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) (n : Nat) : I (b n) :=
      @Nat.rec (fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih =>
          Or.elim (runs.2 k)
            (fun step => hStep (b k) (b (Nat.succ k)) ih step)
            (fun stutter => Eq.mpr (congrArg I stutter) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    theorem gen_advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.kafka_generation_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem part_clamp_le_max : forall (req : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kafka_partition_clamp req cap)) (UInt64.toNat cap) :=
      fun req cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt req cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => req))) (UInt64.toNat cap))
        (instDecidableUInt64Lt req cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun h => Nat.le_of_lt h)

    structure GroupCoordState where
      prevGen      : UInt64
      curGen       : UInt64
      partCount    : UInt64
      maxParts     : UInt64

    -- TLA+ Safety Invariant:
    -- 1. Coordinator generation never regresses (`prevGen <= curGen`).
    -- 2. Partition count stays bounded (`partCount <= maxParts`).
    def GroupCoordSafetyInv (s : GroupCoordState) : Prop :=
      Nat.le (UInt64.toNat s.prevGen) (UInt64.toNat s.curGen) ∧
      Nat.le (UInt64.toNat s.partCount) (UInt64.toNat s.maxParts)

    def Init (initGen cap : UInt64) (s : GroupCoordState) : Prop :=
      s.prevGen = initGen ∧
      s.curGen = initGen ∧
      s.partCount = 0 ∧
      s.maxParts = cap

    def RebalanceGroup (candGen reqParts : UInt64) (s sNext : GroupCoordState) : Prop :=
      sNext.prevGen = s.curGen ∧
      sNext.curGen = _root_.kafka_generation_advance s.curGen candGen ∧
      sNext.partCount = _root_.kafka_partition_clamp reqParts s.maxParts ∧
      sNext.maxParts = s.maxParts

    def Next (s sNext : GroupCoordState) : Prop :=
      ∃ candGen : UInt64, ∃ reqParts : UInt64, RebalanceGroup candGen reqParts s sNext

    def Spec (initGen cap : UInt64) : StateMachine GroupCoordState :=
      StateMachine.mk (Init initGen cap) Next

    theorem init_establishes_inv (initGen cap : UInt64) (s : GroupCoordState)
        (hInit : Init initGen cap s) : GroupCoordSafetyInv s :=
      let hGenLe : Nat.le (UInt64.toNat s.prevGen) (UInt64.toNat s.curGen) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.curGen)) hInit.1)
          (Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat initGen) (UInt64.toNat y)) hInit.2.1)
            (@Nat.le.refl (UInt64.toNat initGen)))
      let hPartLe : Nat.le (UInt64.toNat s.partCount) (UInt64.toNat s.maxParts) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxParts)) hInit.2.2.1)
          (Nat.zero_le (UInt64.toNat s.maxParts))
      And.intro hGenLe hPartLe

    theorem next_preserves_inv (s sNext : GroupCoordState)
        (hInv : GroupCoordSafetyInv s) (hNext : Next s sNext) : GroupCoordSafetyInv sNext :=
      let _ := hInv
      Exists.elim hNext (fun candGen hEx2 =>
        Exists.elim hEx2 (fun reqParts hAct =>
          let hPrevEq : sNext.prevGen = s.curGen := hAct.1
          let hCurEq : sNext.curGen = _root_.kafka_generation_advance s.curGen candGen := hAct.2.1
          let hPartEq : sNext.partCount = _root_.kafka_partition_clamp reqParts s.maxParts := hAct.2.2.1
          let hCapEq : sNext.maxParts = s.maxParts := hAct.2.2.2
          let hGen1 : Nat.le (UInt64.toNat s.curGen) (UInt64.toNat sNext.curGen) :=
            Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.curGen) (UInt64.toNat y)) hCurEq)
              (gen_advance_ge_cur s.curGen candGen)
          let hGen2 : Nat.le (UInt64.toNat sNext.prevGen) (UInt64.toNat sNext.curGen) :=
            Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.curGen)) hPrevEq) hGen1
          let hPart1 : Nat.le (UInt64.toNat sNext.partCount) (UInt64.toNat s.maxParts) :=
            Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.maxParts)) hPartEq)
              (part_clamp_le_max reqParts s.maxParts)
          let hPart2 : Nat.le (UInt64.toNat sNext.partCount) (UInt64.toNat sNext.maxParts) :=
            Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.partCount) (UInt64.toNat y)) hCapEq) hPart1
          And.intro hGen2 hPart2))

    theorem spec_satisfies_consumer_group_safety (initGen cap : UInt64) :
        (Spec initGen cap) ⊨ □ (Lift GroupCoordSafetyInv) :=
      invariantSatisfies (Spec initGen cap) GroupCoordSafetyInv
        (init_establishes_inv initGen cap)
        next_preserves_inv

    end TlaConsumerGroup
    end Kafka
    end Astream

    -- ========================================================================
    -- 3. Rust Contract Reference (`clean-kernel-defeq`)
    -- ========================================================================
    def kafka_generation_matches_isl (req_gen : UInt64) (cur_gen : UInt64) : Bool :=
      decide (req_gen = cur_gen)
}
