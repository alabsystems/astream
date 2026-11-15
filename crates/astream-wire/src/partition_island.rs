// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `partition.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `partition.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaPartitionRouter)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaPartitionRouter

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

    prefix:100 "□" => _root_.Astream.Wire.TlaPartitionRouter.Always
    infixl:45 " ⊨ " => _root_.Astream.Wire.TlaPartitionRouter.Satisfies

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

    end TlaPartitionRouter
    end Wire
    end Astream

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn partition_modulus_clamp`) and verified by
    --    `trust_clean_origin::Faithful` (`clean-kernel-defeq`).
    -- ========================================================================

    -- Clamp a partition count `num_partitions` below `floor` (`1`) up to `floor`.
    -- Compiled directly to `pub const fn partition_modulus_clamp(num_partitions: u64, floor: u64) -> u64`.
    def partition_modulus_clamp (num_partitions : UInt64) (floor : UInt64) : UInt64 :=
      if floor < num_partitions then num_partitions else floor

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Canonical Partition Router
    --    Directly over `UInt64` partition counts, `_root_.partition_modulus_clamp`,
    --    and `partition_in_bounds_isl`
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaPartitionRouter

    -- Island specification of `pub fn partition_in_bounds(partition: u64, modulus: u64) -> bool`.
    def partition_in_bounds_isl (partition : UInt64) (modulus : UInt64) : Bool :=
      decide (partition < modulus)

    theorem partition_modulus_clamp_ge_floor : forall (n : UInt64) (fl : UInt64),
        Nat.le (UInt64.toNat fl) (UInt64.toNat (_root_.partition_modulus_clamp n fl)) :=
      fun n fl => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt fl n)) =>
          Nat.le (UInt64.toNat fl) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => fl) (fun _ => n))))
        (instDecidableUInt64Lt fl n)
        (fun _ => Nat.le.refl (UInt64.toNat fl))
        (fun h => Nat.le_of_lt h)

    -- State of the partition router:
    --   floor    : minimum allowed partition modulus (`UInt64`, initialized to 1)
    --   modulus  : active clamped partition count (`UInt64`)
    --   assigned : most recently assigned partition index (`UInt64`)
    structure RouterState where
      floor    : UInt64
      modulus  : UInt64
      assigned : UInt64

    -- TLA+ Safety Invariant:
    -- 1. `floor <= modulus`: the active partition modulus is never below `floor` (`1`),
    --    ruling out division/remainder by zero.
    -- 2. `assigned <= modulus`: the routed partition never exceeds the active modulus.
    def RouterSafetyInv (s : RouterState) : Prop :=
      Nat.le (UInt64.toNat s.floor) (UInt64.toNat s.modulus) ∧
      Nat.le (UInt64.toNat s.assigned) (UInt64.toNat s.modulus)

    def Init (s : RouterState) : Prop :=
      s.floor = 1 ∧
      s.modulus = 1 ∧
      s.assigned = 0

    -- Action 1: ReconfigureModulus — updates `modulus` to `_root_.partition_modulus_clamp raw s.floor`
    -- and resets `assigned` to `0`.
    def ReconfigureModulus (raw : UInt64) (s sNext : RouterState) : Prop :=
      sNext.floor = s.floor ∧
      sNext.modulus = _root_.partition_modulus_clamp raw s.floor ∧
      sNext.assigned = 0

    -- Action 2: RouteToZero — routes a key to partition 0 while keeping `modulus` fixed.
    def RouteToZero (s sNext : RouterState) : Prop :=
      sNext.floor = s.floor ∧
      sNext.modulus = s.modulus ∧
      sNext.assigned = 0

    def Next (s sNext : RouterState) : Prop :=
      (∃ raw : UInt64, ReconfigureModulus raw s sNext) ∨ RouteToZero s sNext

    def Spec : StateMachine RouterState :=
      StateMachine.mk Init Next

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat a) (UInt64.toNat x)) (Eq.symm hEq))
        (Nat.le.refl (UInt64.toNat a))

    theorem zero_le_uint64 (u : UInt64) (hZero : u = 0) :
        forall (m : UInt64), Nat.le (UInt64.toNat u) (UInt64.toNat m) :=
      fun m =>
        Eq.mpr
          (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat m)) hZero)
          (Nat.zero_le (UInt64.toNat m))

    theorem init_implies_inv (s : RouterState) (hInit : Init s) : RouterSafetyInv s :=
      And.intro
        (uint64_eq_le s.floor s.modulus (Eq.trans hInit.1 (Eq.symm hInit.2.1)))
        (zero_le_uint64 s.assigned hInit.2.2 s.modulus)

    theorem reconfig_preserves_inv (raw : UInt64) (s sNext : RouterState)
        (_hInv : RouterSafetyInv s) (hAct : ReconfigureModulus raw s sNext) :
        RouterSafetyInv sNext :=
      let hFl : Nat.le (UInt64.toNat s.floor) (UInt64.toNat sNext.modulus) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat s.floor) (UInt64.toNat x)) hAct.2.1)
          (partition_modulus_clamp_ge_floor raw s.floor)
      let hFlNext : Nat.le (UInt64.toNat sNext.floor) (UInt64.toNat sNext.modulus) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.modulus)) hAct.1)
          hFl
      And.intro hFlNext (zero_le_uint64 sNext.assigned hAct.2.2 sNext.modulus)

    theorem route_zero_preserves_inv (s sNext : RouterState)
        (hInv : RouterSafetyInv s) (hAct : RouteToZero s sNext) :
        RouterSafetyInv sNext :=
      let h1 : Nat.le (UInt64.toNat sNext.floor) (UInt64.toNat s.modulus) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.modulus)) hAct.1)
          hInv.1
      let h2 : Nat.le (UInt64.toNat sNext.floor) (UInt64.toNat sNext.modulus) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat sNext.floor) (UInt64.toNat x)) hAct.2.1)
          h1
      And.intro h2 (zero_le_uint64 sNext.assigned hAct.2.2 sNext.modulus)

    theorem next_preserves_inv (s sNext : RouterState)
        (hInv : RouterSafetyInv s) (hNext : Next s sNext) :
        RouterSafetyInv sNext :=
      Or.elim hNext
        (fun hRec => Exists.elim hRec (fun raw hAct => reconfig_preserves_inv raw s sNext hInv hAct))
        (fun hRoute => route_zero_preserves_inv s sNext hInv hRoute)

    -- ========================================================================
    -- 4. Top-Level Temporal Theorem: `Spec ⊨ □ (Lift RouterSafetyInv)`
    -- ========================================================================
    theorem spec_satisfies_always_router_safety : Spec ⊨ □ (Lift RouterSafetyInv) :=
      invariantSatisfies Spec RouterSafetyInv init_implies_inv next_preserves_inv

    end TlaPartitionRouter
    end Wire
    end Astream
}
