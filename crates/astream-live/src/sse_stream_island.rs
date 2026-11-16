// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `sse_stream.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `sse_stream.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def sse_accum_clamp_bytes (cur : UInt64) (cap : UInt64) : UInt64 :=
      if cur < cap then cur else cap

    def sse_block_count_clamp (blocks : UInt64) (max_blocks : UInt64) : UInt64 :=
      if blocks < max_blocks then blocks else max_blocks

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & SSE Stream Assembler Spec
    -- =======================================================================

    namespace Astream
    namespace Live
    namespace TlaSseStreamAssembler

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

    structure SseAssemblerState where
      accum_bytes : UInt64
      max_accum_bytes : UInt64
      block_count : UInt64
      max_blocks : UInt64

    def SseAssemblerInv (s : SseAssemblerState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.accum_bytes) (UInt64.toNat s.max_accum_bytes))
        (Nat.le (UInt64.toNat s.block_count) (UInt64.toNat s.max_blocks))

    def Init (s : SseAssemblerState) : Prop :=
      And (s.accum_bytes = 0) (s.block_count = 0)

    def feedDeltaStep (cand_bytes : UInt64) (cand_blocks : UInt64) (s : SseAssemblerState) : SseAssemblerState :=
      SseAssemblerState.mk
        (_root_.sse_accum_clamp_bytes cand_bytes s.max_accum_bytes)
        s.max_accum_bytes
        (_root_.sse_block_count_clamp cand_blocks s.max_blocks)
        s.max_blocks

    def Next (s : SseAssemblerState) (s' : SseAssemblerState) : Prop :=
      ∃ (cand_bytes : UInt64), ∃ (cand_blocks : UInt64),
        s' = feedDeltaStep cand_bytes cand_blocks s

    def Spec : StateMachine SseAssemblerState :=
      StateMachine.mk Init Next

    theorem clamp_bytes_le_cap : forall (cur : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.sse_accum_clamp_bytes cur cap)) (UInt64.toNat cap) :=
      fun cur cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => cur))) (UInt64.toNat cap))
        (instDecidableUInt64Lt cur cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem clamp_blocks_le_max : forall (blocks : UInt64) (max_b : UInt64),
        Nat.le (UInt64.toNat (_root_.sse_block_count_clamp blocks max_b)) (UInt64.toNat max_b) :=
      fun blocks max_b => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt blocks max_b)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_b) (fun _ => blocks))) (UInt64.toNat max_b))
        (instDecidableUInt64Lt blocks max_b)
        (fun _ => @Nat.le.refl (UInt64.toNat max_b))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : SseAssemblerState) (hInit : Init s) :
      SseAssemblerInv s :=
      And.intro
        (zero_le_cap s.accum_bytes s.max_accum_bytes (And.left hInit))
        (zero_le_cap s.block_count s.max_blocks (And.right hInit))

    theorem next_preserves_inv (s : SseAssemblerState) (s' : SseAssemblerState)
      (_hInv : SseAssemblerInv s) (hNext : Next s s') :
      SseAssemblerInv s' :=
      Exists.elim hNext (fun (cb : UInt64) (hRest : ∃ (ck : UInt64), s' = feedDeltaStep cb ck s) =>
        Exists.elim hRest (fun (ck : UInt64) (hEq : s' = feedDeltaStep cb ck s) =>
          Eq.mpr
            (congrArg (fun (st : SseAssemblerState) => SseAssemblerInv st) hEq)
            (And.intro
              (clamp_bytes_le_cap cb s.max_accum_bytes)
              (clamp_blocks_le_max ck s.max_blocks))))

    theorem sse_assembler_safety_always :
      Satisfies (Runs Spec) (Always (Lift SseAssemblerInv)) :=
      invariantSatisfies Spec SseAssemblerInv init_establishes_inv next_preserves_inv

    end TlaSseStreamAssembler
    end Live
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def sse_accum_within_cap_isl (cur : UInt64) (cap : UInt64) : Bool :=
      decide (cur ≤ cap)
}
