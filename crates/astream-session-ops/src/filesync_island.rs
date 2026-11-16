// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `filesync.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `filesync.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def filesync_rev_advance (cur_rev : UInt64) (proposed_rev : UInt64) : UInt64 :=
      if cur_rev < proposed_rev then proposed_rev else cur_rev

    def filesync_chunk_clamp (chunk_len : UInt64) (max_chunk : UInt64) : UInt64 :=
      if chunk_len < max_chunk then chunk_len else max_chunk

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & File-Sync Spec
    -- =======================================================================

    namespace Astream
    namespace Engine
    namespace TlaFileSync

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

    structure FileSyncState where
      prev_rev : UInt64
      rev : UInt64
      chunk_bytes : UInt64
      max_chunk : UInt64

    def FileSyncSafetyInv (s : FileSyncState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_rev) (UInt64.toNat s.rev))
        (Nat.le (UInt64.toNat s.chunk_bytes) (UInt64.toNat s.max_chunk))

    def Init (s : FileSyncState) : Prop :=
      And
        (s.prev_rev = s.rev)
        (Nat.le (UInt64.toNat s.chunk_bytes) (UInt64.toNat s.max_chunk))

    def syncDeltaStep (proposed_rev : UInt64) (raw_chunk : UInt64) (s : FileSyncState) : FileSyncState :=
      FileSyncState.mk
        s.rev
        (_root_.filesync_rev_advance s.rev proposed_rev)
        (_root_.filesync_chunk_clamp raw_chunk s.max_chunk)
        s.max_chunk

    def Next (s : FileSyncState) (s' : FileSyncState) : Prop :=
      ∃ (proposed_rev : UInt64), ∃ (raw_chunk : UInt64),
        s' = syncDeltaStep proposed_rev raw_chunk s

    def Spec : StateMachine FileSyncState :=
      StateMachine.mk Init Next

    theorem rev_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.filesync_rev_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem chunk_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.filesync_chunk_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : FileSyncState) (hInit : Init s) :
      FileSyncSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_rev s.rev (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : FileSyncState) (s' : FileSyncState)
      (_hInv : FileSyncSafetyInv s) (hNext : Next s s') :
      FileSyncSafetyInv s' :=
      Exists.elim hNext (fun (proposed_rev : UInt64) (hRest : ∃ (raw_chunk : UInt64), s' = syncDeltaStep proposed_rev raw_chunk s) =>
        Exists.elim hRest (fun (raw_chunk : UInt64) (hEq : s' = syncDeltaStep proposed_rev raw_chunk s) =>
          Eq.mpr
            (congrArg (fun (st : FileSyncState) => FileSyncSafetyInv st) hEq)
            (And.intro
              (rev_ge_prev s.rev proposed_rev)
              (chunk_le_max raw_chunk s.max_chunk))))

    theorem filesync_safety_always :
      Satisfies (Runs Spec) (Always (Lift FileSyncSafetyInv)) :=
      invariantSatisfies Spec FileSyncSafetyInv init_establishes_inv next_preserves_inv

    end TlaFileSync
    end Engine
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def filesync_rev_is_fresh_isl (cur_rev : UInt64) (next_rev : UInt64) : Bool :=
      decide (cur_rev < next_rev)
}
