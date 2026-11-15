// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for 24-bit truecolour SGR channel clamping and per-cell zero-width
// combining-mark capacity bounds (`screen.rs`), mounted under `cfg(clean_islands)`.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def color_clamp_channel (val : UInt64) (max_val : UInt64) : UInt64 :=
      if val < max_val then val else max_val

    def combining_cap_clamp (len : UInt64) (cap : UInt64) : UInt64 :=
      if len < cap then len else cap

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Term.TlaTruecolorCell)
    -- ========================================================================
    namespace Astream
    namespace Term
    namespace TlaTruecolorCell

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
        And (M.Init (b 0)) (∀ (k : Nat), M.Next (b k) (b (Nat.add k 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

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
    -- 3. Truecolour Channel & Combining-Mark Capacity Safety Theorems
    -- ========================================================================

    structure CellExtState where
      channel : UInt64
      max_channel : UInt64
      comb_len : UInt64
      comb_cap : UInt64

    def CellExtBoundedInv (s : CellExtState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.channel) (UInt64.toNat s.max_channel))
        (Nat.le (UInt64.toNat s.comb_len) (UInt64.toNat s.comb_cap))

    def Init (s : CellExtState) : Prop :=
      And (s.channel = (0 : UInt64)) (s.comb_len = (0 : UInt64))

    def updateCellExtAction
      (raw_chan : UInt64)
      (max_chan : UInt64)
      (raw_len : UInt64)
      (cap : UInt64)
      (_s : CellExtState) : CellExtState :=
      CellExtState.mk
        (_root_.color_clamp_channel raw_chan max_chan)
        max_chan
        (_root_.combining_cap_clamp raw_len cap)
        cap

    def Next (s : CellExtState) (s' : CellExtState) : Prop :=
      ∃ (raw_chan : UInt64),
        ∃ (max_chan : UInt64),
          ∃ (raw_len : UInt64),
            ∃ (cap : UInt64),
              s' = updateCellExtAction raw_chan max_chan raw_len cap s

    def Spec : StateMachine CellExtState :=
      StateMachine.mk Init Next

    theorem channel_clamp_le_max : forall (val : UInt64) (max_val : UInt64),
        Nat.le (UInt64.toNat (_root_.color_clamp_channel val max_val)) (UInt64.toNat max_val) :=
      fun val max_val => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt val max_val)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => max_val) (fun _ => val))) (UInt64.toNat max_val))
        (instDecidableUInt64Lt val max_val)
        (fun _ => Nat.le.refl (UInt64.toNat max_val))
        (fun hLt => Nat.le_of_lt hLt)

    theorem combining_clamp_le_cap : forall (len : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.combining_cap_clamp len cap)) (UInt64.toNat cap) :=
      fun len cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt len cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => len))) (UInt64.toNat cap))
        (instDecidableUInt64Lt len cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_zero_le (a : UInt64) (b : UInt64) (hZero : a = (0 : UInt64)) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hZero)
        (Nat.zero_le (UInt64.toNat b))

    theorem init_establishes_inv (s : CellExtState) (hInit : Init s) :
      CellExtBoundedInv s :=
      And.intro
        (uint64_zero_le s.channel s.max_channel (And.left hInit))
        (uint64_zero_le s.comb_len s.comb_cap (And.right hInit))

    theorem next_preserves_inv (s : CellExtState) (s' : CellExtState)
      (_hInv : CellExtBoundedInv s) (hNext : Next s s') :
      CellExtBoundedInv s' :=
      Exists.elim hNext (fun (rc : UInt64) (h1 : ∃ (mc : UInt64), ∃ (rl : UInt64), ∃ (cp : UInt64), s' = updateCellExtAction rc mc rl cp s) =>
        Exists.elim h1 (fun (mc : UInt64) (h2 : ∃ (rl : UInt64), ∃ (cp : UInt64), s' = updateCellExtAction rc mc rl cp s) =>
          Exists.elim h2 (fun (rl : UInt64) (h3 : ∃ (cp : UInt64), s' = updateCellExtAction rc mc rl cp s) =>
            Exists.elim h3 (fun (cp : UInt64) (hEq : s' = updateCellExtAction rc mc rl cp s) =>
              Eq.mpr
                (congrArg (fun (st : CellExtState) => CellExtBoundedInv st) hEq)
                (And.intro
                  (channel_clamp_le_max rc mc)
                  (combining_clamp_le_cap rl cp))))))

    theorem spec_satisfies_truecolor_cell_bounded :
      Satisfies (Runs Spec) (Always (Lift CellExtBoundedInv)) :=
      invariantSatisfies Spec CellExtBoundedInv init_establishes_inv next_preserves_inv

    end TlaTruecolorCell
    end Term
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def combining_len_within_cap_isl (len : UInt8) (cap : UInt8) : Bool :=
      decide (len ≤ cap)
}
