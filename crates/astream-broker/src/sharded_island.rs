// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `sharded.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `sharded.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twin in `twins.rs` of the function it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================
    def sharded_clamp_index (idx : UInt64) (shards : UInt64) : UInt64 :=
      if idx < shards then idx else shards

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaShardedBroker)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaShardedBroker

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaShardedBroker.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaShardedBroker.Always

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
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    structure ShardedRouteState where
      shardIdx   : UInt64
      shardCount : UInt64

    def ShardedIndexBoundedInv (s : ShardedRouteState) : Prop :=
      Nat.le (UInt64.toNat s.shardIdx) (UInt64.toNat s.shardCount)

    def Init (s : ShardedRouteState) : Prop :=
      s.shardIdx = 0 ∧ s.shardCount = 4

    def routeSubjectAction (rawIdx : UInt64) (s sNext : ShardedRouteState) : Prop :=
      sNext.shardCount = s.shardCount ∧
      sNext.shardIdx = _root_.sharded_clamp_index rawIdx s.shardCount

    def Next (s sNext : ShardedRouteState) : Prop :=
      ∃ rawIdx : UInt64, routeSubjectAction rawIdx s sNext

    def Spec : StateMachine ShardedRouteState :=
      StateMachine.mk Init Next

    theorem clamp_le_shards : forall (idx : UInt64) (shards : UInt64),
        Nat.le (UInt64.toNat (_root_.sharded_clamp_index idx shards)) (UInt64.toNat shards) :=
      fun idx shards => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt idx shards)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => shards) (fun _ => idx))) (UInt64.toNat shards))
        (instDecidableUInt64Lt idx shards)
        (fun _ => Nat.le.refl (UInt64.toNat shards))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a b : UInt64) (hZero : a = 0) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : ShardedRouteState) (hInit : Init s) :
        ShardedIndexBoundedInv s :=
      uint64_zero_le s.shardIdx s.shardCount hInit.1

    theorem next_preserves_inv (s sNext : ShardedRouteState)
        (_hInv : ShardedIndexBoundedInv s) (hNext : Next s sNext) :
        ShardedIndexBoundedInv sNext :=
      Exists.elim hNext (fun rawIdx hAct =>
        let hClamp : Nat.le (UInt64.toNat (_root_.sharded_clamp_index rawIdx s.shardCount)) (UInt64.toNat s.shardCount) :=
          clamp_le_shards rawIdx s.shardCount
        let hEqIdx : sNext.shardIdx = _root_.sharded_clamp_index rawIdx s.shardCount := hAct.2
        let hEqCnt : sNext.shardCount = s.shardCount := hAct.1
        Eq.mpr
          (congrArg (fun (m : UInt64) => Nat.le (UInt64.toNat sNext.shardIdx) (UInt64.toNat m)) hEqCnt)
          (Eq.mpr
            (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat v) (UInt64.toNat s.shardCount)) hEqIdx)
            hClamp))

    theorem spec_satisfies_sharded_index_bounded :
        Spec ⊨ □ (Lift ShardedIndexBoundedInv) :=
      invariantSatisfies Spec ShardedIndexBoundedInv init_establishes_inv next_preserves_inv

    end TlaShardedBroker
    end Broker
    end Astream

    def sharded_count_nonzero_isl (shards : UInt32) : Bool :=
      decide (0 < shards)
}
