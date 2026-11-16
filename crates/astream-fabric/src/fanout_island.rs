// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `fanout.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `fanout.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def fanout_cursor_advance (cur_off : UInt64) (next_off : UInt64) : UInt64 :=
      if cur_off < next_off then next_off else cur_off

    def fanout_page_clamp (requested : UInt64) (max_page : UInt64) : UInt64 :=
      if requested < max_page then requested else max_page

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Fanout Page Cache Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaFanoutPageCache

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
        Satisfies M (Always (Lift I)) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    structure FanoutState where
      prev_cursor : UInt64
      cursor : UInt64
      page_len : UInt64
      max_page : UInt64

    def FanoutSafetyInv (s : FanoutState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_cursor) (UInt64.toNat s.cursor))
        (Nat.le (UInt64.toNat s.page_len) (UInt64.toNat s.max_page))

    def Init (s : FanoutState) : Prop :=
      And
        (s.prev_cursor = s.cursor)
        (Nat.le (UInt64.toNat s.page_len) (UInt64.toNat s.max_page))

    def drainPageStep (proposed_cursor : UInt64) (raw_page : UInt64) (s : FanoutState) : FanoutState :=
      FanoutState.mk
        s.cursor
        (_root_.fanout_cursor_advance s.cursor proposed_cursor)
        (_root_.fanout_page_clamp raw_page s.max_page)
        s.max_page

    def Next (s : FanoutState) (s' : FanoutState) : Prop :=
      ∃ (proposed_cursor : UInt64), ∃ (raw_page : UInt64),
        s' = drainPageStep proposed_cursor raw_page s

    def Spec : StateMachine FanoutState :=
      StateMachine.mk Init Next

    theorem cursor_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.fanout_cursor_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem page_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.fanout_page_clamp raw cap)) (UInt64.toNat cap) :=
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

    theorem init_establishes_inv (s : FanoutState) (hInit : Init s) :
      FanoutSafetyInv s :=
      And.intro
        (uint64_eq_le s.prev_cursor s.cursor (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : FanoutState) (s' : FanoutState)
      (_hInv : FanoutSafetyInv s) (hNext : Next s s') :
      FanoutSafetyInv s' :=
      Exists.elim hNext (fun (pc : UInt64) (hRest : ∃ (rp : UInt64), s' = drainPageStep pc rp s) =>
        Exists.elim hRest (fun (rp : UInt64) (hEq : s' = drainPageStep pc rp s) =>
          Eq.mpr
            (congrArg (fun (st : FanoutState) => FanoutSafetyInv st) hEq)
            (And.intro
              (cursor_ge_prev s.cursor pc)
              (page_le_max rp s.max_page))))

    theorem fanout_safety_always :
      Satisfies Spec (Always (Lift FanoutSafetyInv)) :=
      invariantSatisfies Spec FanoutSafetyInv init_establishes_inv next_preserves_inv

    end TlaFanoutPageCache
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def fanout_cursor_below_end_isl (cursor : UInt64) (end_off : UInt64) : Bool :=
      decide (cursor < end_off)
}
