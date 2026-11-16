// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `merkle.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `merkle.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================

    -- Clamps a commit node's parent count `raw_parents` to `max_parents` (`2`:
    -- `0` = genesis, `1` = linear commit, `2` = two-branch input merge).
    def merkle_parent_count_clamp (raw_parents : UInt64) (max_parents : UInt64) : UInt64 :=
      if raw_parents < max_parents then raw_parents else max_parents

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaMerkleDag)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaMerkleDag

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

    prefix:100 "□" => _root_.Astream.Engine.TlaMerkleDag.Always
    infixl:45 " ⊨ " => _root_.Astream.Engine.TlaMerkleDag.Satisfies

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

    structure MerkleState where
      parent_count : UInt64
      max_parents  : UInt64

    def MerkleDagSafetyInv (s : MerkleState) : Prop :=
      Nat.le (UInt64.toNat s.parent_count) (UInt64.toNat s.max_parents)

    def Init (max_parents : UInt64) (s : MerkleState) : Prop :=
      s.parent_count = 0 ∧ s.max_parents = max_parents

    def commitNodeAction (raw_parents : UInt64) (s sNext : MerkleState) : Prop :=
      sNext.max_parents = s.max_parents ∧
      sNext.parent_count = _root_.merkle_parent_count_clamp raw_parents s.max_parents

    def Next (s sNext : MerkleState) : Prop :=
      ∃ raw_parents : UInt64, commitNodeAction raw_parents s sNext

    def Spec (max_parents : UInt64) : StateMachine MerkleState :=
      StateMachine.mk (Init max_parents) Next

    theorem clamp_le_max : forall (raw_parents : UInt64) (max_parents : UInt64),
        Nat.le (UInt64.toNat (_root_.merkle_parent_count_clamp raw_parents max_parents)) (UInt64.toNat max_parents) :=
      fun raw_parents max_parents => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw_parents max_parents)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_parents) (fun _ => raw_parents))) (UInt64.toNat max_parents))
        (instDecidableUInt64Lt raw_parents max_parents)
        (fun _ => @Nat.le.refl (UInt64.toNat max_parents))
        (fun h => Nat.le_of_lt h)

    theorem uint64_zero_le (a : UInt64) (hZero : a = 0) (b : UInt64) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (max_parents : UInt64) (s : MerkleState) (hInit : Init max_parents s) :
        MerkleDagSafetyInv s :=
      uint64_zero_le s.parent_count hInit.1 s.max_parents

    theorem next_preserves_inv (s sNext : MerkleState)
        (_hInv : MerkleDagSafetyInv s) (hNext : Next s sNext) :
        MerkleDagSafetyInv sNext :=
      Exists.elim hNext (fun raw_parents hStep =>
        let hClamp : Nat.le (UInt64.toNat sNext.parent_count) (UInt64.toNat s.max_parents) :=
          Eq.mpr
            (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.max_parents)) hStep.2)
            (clamp_le_max raw_parents s.max_parents)
        Eq.mpr
          (congrArg (fun y => Nat.le (UInt64.toNat sNext.parent_count) (UInt64.toNat y)) hStep.1)
          hClamp)

    theorem spec_satisfies_merkle_dag_safety (max_parents : UInt64) :
        (Spec max_parents) ⊨ □ (Lift MerkleDagSafetyInv) :=
      invariantSatisfies (Spec max_parents) MerkleDagSafetyInv
        (init_establishes_inv max_parents)
        next_preserves_inv

    end TlaMerkleDag
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def merkle_offset_matches_isl (expected_seq : UInt64) (found_seq : UInt64) : Bool :=
      decide (expected_seq = found_seq)
}
