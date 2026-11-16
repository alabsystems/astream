// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `json.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `json.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` / I5)
    -- ========================================================================

    def json_clamp_depth (depth : UInt64) (max_depth : UInt64) : UInt64 :=
      if depth < max_depth then depth else max_depth

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Live.TlaJsonParser)
    -- ========================================================================
    namespace Astream
    namespace Live
    namespace TlaJsonParser

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (k : Nat) (b : Behavior State) : Behavior State :=
      fun (n : Nat) => b (Nat.add k n)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (k : Nat), P (drop k b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        M.Init (b 0) ∧ ∀ (k : Nat), M.Next (b k) (b (Nat.add k 1))

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun (b : Behavior State) => P (b 0)

    def Satisfies {State : Type} (SpecF : Formula State) (PropF : Formula State) : Prop :=
      ∀ (b : Behavior State), SpecF b → PropF b

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

    -- ========================================================================
    -- 3. JSON Parser Depth Bounding State Machine & Safety Theorem
    -- ========================================================================

    structure ParserDepthState where
      depth : UInt64
      max_depth : UInt64

    def JsonDepthBoundedInv (s : ParserDepthState) : Prop :=
      Nat.le (UInt64.toNat s.depth) (UInt64.toNat s.max_depth)

    def Init (s : ParserDepthState) : Prop :=
      s.depth = (0 : UInt64)

    def descendAction (requested : UInt64) (max_depth : UInt64) (_s : ParserDepthState) : ParserDepthState :=
      ParserDepthState.mk (_root_.json_clamp_depth requested max_depth) max_depth

    def Next (s : ParserDepthState) (s' : ParserDepthState) : Prop :=
      ∃ (requested : UInt64), ∃ (max_depth : UInt64), s' = descendAction requested max_depth s

    def Spec : StateMachine ParserDepthState :=
      StateMachine.mk Init Next

    theorem clamp_le_max : forall (requested : UInt64) (max_depth : UInt64),
        Nat.le (UInt64.toNat (_root_.json_clamp_depth requested max_depth)) (UInt64.toNat max_depth) :=
      fun requested max_depth => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt requested max_depth)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_depth) (fun _ => requested))) (UInt64.toNat max_depth))
        (instDecidableUInt64Lt requested max_depth)
        (fun _ => @Nat.le.refl (UInt64.toNat max_depth))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : ParserDepthState) (hInit : Init s) :
      JsonDepthBoundedInv s :=
      uint64_zero_le s.depth s.max_depth hInit

    theorem next_preserves_inv (s : ParserDepthState) (s' : ParserDepthState)
      (_hInv : JsonDepthBoundedInv s) (hNext : Next s s') :
      JsonDepthBoundedInv s' :=
      Exists.elim hNext (fun (requested : UInt64) (hEx : ∃ (max_depth : UInt64), s' = descendAction requested max_depth s) =>
        Exists.elim hEx (fun (max_depth : UInt64) (hEq : s' = descendAction requested max_depth s) =>
          Eq.mpr
            (congrArg (fun (st : ParserDepthState) => JsonDepthBoundedInv st) hEq)
            (clamp_le_max requested max_depth)))

    theorem spec_satisfies_json_depth_bounded :
      Satisfies (Runs Spec) (Always (Lift JsonDepthBoundedInv)) :=
      invariantSatisfies Spec JsonDepthBoundedInv init_establishes_inv next_preserves_inv

    end TlaJsonParser
    end Live
    end Astream

    def json_depth_within_max_isl (depth : USize) (max_depth : USize) : Bool :=
      decide (depth ≤ max_depth)
}
