// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `media_guard.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `media_guard.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def media_session_bytes_clamp (retained : UInt64) (session_quota : UInt64) : UInt64 :=
      if retained < session_quota then retained else session_quota

    def media_chunk_bytes_clamp (accum : UInt64) (max_image_bytes : UInt64) : UInt64 :=
      if accum < max_image_bytes then accum else max_image_bytes

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Inline Media Quota Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaInlineMediaGuard

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

    structure InlineMediaState where
      retained_bytes : UInt64
      session_quota : UInt64
      chunk_bytes : UInt64
      max_image_bytes : UInt64

    def InlineMediaInv (s : InlineMediaState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.retained_bytes) (UInt64.toNat s.session_quota))
        (Nat.le (UInt64.toNat s.chunk_bytes) (UInt64.toNat s.max_image_bytes))

    def Init (s : InlineMediaState) : Prop :=
      And (s.retained_bytes = 0) (s.chunk_bytes = 0)

    def mediaStep (raw_ret : UInt64) (raw_chk : UInt64) (s : InlineMediaState) : InlineMediaState :=
      InlineMediaState.mk
        (_root_.media_session_bytes_clamp raw_ret s.session_quota)
        s.session_quota
        (_root_.media_chunk_bytes_clamp raw_chk s.max_image_bytes)
        s.max_image_bytes

    def Next (s : InlineMediaState) (s' : InlineMediaState) : Prop :=
      ∃ (raw_ret : UInt64), ∃ (raw_chk : UInt64),
        s' = mediaStep raw_ret raw_chk s

    def Spec : StateMachine InlineMediaState :=
      StateMachine.mk Init Next

    theorem retained_le_quota : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.media_session_bytes_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem chunk_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.media_chunk_bytes_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : InlineMediaState) (hInit : Init s) :
      InlineMediaInv s :=
      And.intro
        (zero_le_cap s.retained_bytes s.session_quota (And.left hInit))
        (zero_le_cap s.chunk_bytes s.max_image_bytes (And.right hInit))

    theorem next_preserves_inv (s : InlineMediaState) (s' : InlineMediaState)
      (_hInv : InlineMediaInv s) (hNext : Next s s') :
      InlineMediaInv s' :=
      Exists.elim hNext (fun (rr : UInt64) (hRest : ∃ (rc : UInt64), s' = mediaStep rr rc s) =>
        Exists.elim hRest (fun (rc : UInt64) (hEq : s' = mediaStep rr rc s) =>
          Eq.mpr
            (congrArg (fun (st : InlineMediaState) => InlineMediaInv st) hEq)
            (And.intro
              (retained_le_quota rr s.session_quota)
              (chunk_le_max rc s.max_image_bytes))))

    theorem inline_media_safety_always :
      Satisfies (Runs Spec) (Always (Lift InlineMediaInv)) :=
      invariantSatisfies Spec InlineMediaInv init_establishes_inv next_preserves_inv

    end TlaInlineMediaGuard
    end Term
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def media_dims_within_cap_isl (cells : UInt64) (max_cells : UInt64) : Bool :=
      decide (cells ≤ max_cells)
}
