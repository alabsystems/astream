// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `merkle_proof.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `merkle_proof.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def merkle_proof_depth_clamp (depth : UInt64) (max_depth : UInt64) : UInt64 :=
      if depth < max_depth then depth else max_depth

    def merkle_tree_size_advance (prev_size : UInt64) (cand_size : UInt64) : UInt64 :=
      if prev_size < cand_size then cand_size else prev_size

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & RFC 6962 Merkle Proof Spec
    -- =======================================================================

    namespace Astream
    namespace Digest
    namespace TlaMerkleAuditProof

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

    structure MerkleProofState where
      proof_depth : UInt64
      max_depth : UInt64
      tree_size : UInt64
      prev_size : UInt64

    def MerkleProofInv (s : MerkleProofState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.proof_depth) (UInt64.toNat s.max_depth))
        (Nat.le (UInt64.toNat s.prev_size) (UInt64.toNat s.tree_size))

    def Init (s : MerkleProofState) : Prop :=
      And
        (s.proof_depth = 0)
        (And (s.tree_size = 0) (s.prev_size = 0))

    def merkleStep (raw_depth : UInt64) (cand_size : UInt64) (s : MerkleProofState) : MerkleProofState :=
      MerkleProofState.mk
        (_root_.merkle_proof_depth_clamp raw_depth s.max_depth)
        s.max_depth
        (_root_.merkle_tree_size_advance s.tree_size cand_size)
        s.tree_size

    def Next (s : MerkleProofState) (s' : MerkleProofState) : Prop :=
      ∃ (raw_depth : UInt64), ∃ (cand_size : UInt64),
        s' = merkleStep raw_depth cand_size s

    def Spec : StateMachine MerkleProofState :=
      StateMachine.mk Init Next

    theorem depth_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.merkle_proof_depth_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem size_monotone : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.merkle_tree_size_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => Nat.le.refl (UInt64.toNat prev))
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

    theorem init_establishes_inv (s : MerkleProofState) (hInit : Init s) :
      MerkleProofInv s :=
      And.intro
        (zero_le_cap s.proof_depth s.max_depth (And.left hInit))
        (eq_zero_le
          s.prev_size
          s.tree_size
          (And.right (And.right hInit))
          (And.left (And.right hInit)))

    theorem next_preserves_inv (s : MerkleProofState) (s' : MerkleProofState)
      (_hInv : MerkleProofInv s) (hNext : Next s s') :
      MerkleProofInv s' :=
      Exists.elim hNext (fun (rd : UInt64) (hRest : ∃ (cs : UInt64), s' = merkleStep rd cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = merkleStep rd cs s) =>
          Eq.mpr
            (congrArg (fun (st : MerkleProofState) => MerkleProofInv st) hEq)
            (And.intro
              (depth_le_max rd s.max_depth)
              (size_monotone s.tree_size cs))))

    theorem merkle_proof_safety_always :
      Satisfies (Runs Spec) (Always (Lift MerkleProofInv)) :=
      invariantSatisfies Spec MerkleProofInv init_establishes_inv next_preserves_inv

    end TlaMerkleAuditProof
    end Digest
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def merkle_leaf_in_range_isl (leaf_idx : USize) (leaf_count : USize) : Bool :=
      decide (leaf_idx < leaf_count)
}
