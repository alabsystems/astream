// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `binbody.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `binbody.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def binbody_chunk_idx_clamp (idx : UInt64) (total : UInt64) : UInt64 :=
      if idx < total then idx else total

    def binbody_bytes_accum_clamp (accum : UInt64) (max_bytes : UInt64) : UInt64 :=
      if accum < max_bytes then accum else max_bytes

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & §9.1 Binary Envelope Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaBinaryEnvelope

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

    structure BinaryEnvelopeState where
      chunk_idx : UInt64
      total_chunks : UInt64
      accum_bytes : UInt64
      max_bytes : UInt64

    def BinaryEnvelopeInv (s : BinaryEnvelopeState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.chunk_idx) (UInt64.toNat s.total_chunks))
        (Nat.le (UInt64.toNat s.accum_bytes) (UInt64.toNat s.max_bytes))

    def Init (s : BinaryEnvelopeState) : Prop :=
      And
        (s.chunk_idx = 0)
        (s.accum_bytes = 0)

    def envelopeStep (raw_idx : UInt64) (raw_accum : UInt64) (s : BinaryEnvelopeState) : BinaryEnvelopeState :=
      BinaryEnvelopeState.mk
        (_root_.binbody_chunk_idx_clamp raw_idx s.total_chunks)
        s.total_chunks
        (_root_.binbody_bytes_accum_clamp raw_accum s.max_bytes)
        s.max_bytes

    def Next (s : BinaryEnvelopeState) (s' : BinaryEnvelopeState) : Prop :=
      ∃ (raw_idx : UInt64), ∃ (raw_accum : UInt64),
        s' = envelopeStep raw_idx raw_accum s

    def Spec : StateMachine BinaryEnvelopeState :=
      StateMachine.mk Init Next

    theorem idx_le_total : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.binbody_chunk_idx_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem accum_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.binbody_bytes_accum_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_cap (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : BinaryEnvelopeState) (hInit : Init s) :
      BinaryEnvelopeInv s :=
      And.intro
        (zero_le_cap s.chunk_idx s.total_chunks (And.left hInit))
        (zero_le_cap s.accum_bytes s.max_bytes (And.right hInit))

    theorem next_preserves_inv (s : BinaryEnvelopeState) (s' : BinaryEnvelopeState)
      (_hInv : BinaryEnvelopeInv s) (hNext : Next s s') :
      BinaryEnvelopeInv s' :=
      Exists.elim hNext (fun (ri : UInt64) (hRest : ∃ (ra : UInt64), s' = envelopeStep ri ra s) =>
        Exists.elim hRest (fun (ra : UInt64) (hEq : s' = envelopeStep ri ra s) =>
          Eq.mpr
            (congrArg (fun (st : BinaryEnvelopeState) => BinaryEnvelopeInv st) hEq)
            (And.intro
              (idx_le_total ri s.total_chunks)
              (accum_le_max ra s.max_bytes))))

    theorem binary_envelope_safety_always :
      Satisfies (Runs Spec) (Always (Lift BinaryEnvelopeInv)) :=
      invariantSatisfies Spec BinaryEnvelopeInv init_establishes_inv next_preserves_inv

    end TlaBinaryEnvelope
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def binbody_complete_valid_isl (received : UInt64) (total : UInt64) : Bool :=
      decide (received = total)
}
