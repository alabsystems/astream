// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `last_index.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `last_index.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def last_offset_advance (cur_off : UInt64) (next_off : UInt64) : UInt64 :=
      if cur_off < next_off then next_off else cur_off

    def last_scan_clamp (scanned : UInt64) (scan_max : UInt64) : UInt64 :=
      if scanned < scan_max then scanned else scan_max

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Last Prefix Scan Spec
    -- =======================================================================

    namespace Astream
    namespace Broker
    namespace TlaLastPrefixScan
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

    structure LastPrefixState where
      prev_off : UInt64
      cur_off : UInt64
      scanned : UInt64
      scan_max : UInt64

    def LastPrefixInv (s : LastPrefixState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prev_off) (UInt64.toNat s.cur_off))
        (Nat.le (UInt64.toNat s.scanned) (UInt64.toNat s.scan_max))

    def Init (s : LastPrefixState) : Prop :=
      And
        (s.prev_off = s.cur_off)
        (Nat.le (UInt64.toNat s.scanned) (UInt64.toNat s.scan_max))

    def prefixQueryStep (proposed_off : UInt64) (raw_scanned : UInt64) (s : LastPrefixState) : LastPrefixState :=
      LastPrefixState.mk
        s.cur_off
        (_root_.last_offset_advance s.cur_off proposed_off)
        (_root_.last_scan_clamp raw_scanned s.scan_max)
        s.scan_max

    def Next (s : LastPrefixState) (s' : LastPrefixState) : Prop :=
      ∃ (proposed_off : UInt64), ∃ (raw_scanned : UInt64),
        s' = prefixQueryStep proposed_off raw_scanned s

    def Spec : StateMachine LastPrefixState :=
      StateMachine.mk Init Next

    theorem off_ge_prev : forall (cur : UInt64) (proposed : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.last_offset_advance cur proposed)) :=
      fun cur proposed => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur proposed)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => proposed))))
        (instDecidableUInt64Lt cur proposed)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem scan_le_max : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.last_scan_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : LastPrefixState) (hInit : Init s) :
      LastPrefixInv s :=
      And.intro
        (uint64_eq_le s.prev_off s.cur_off (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : LastPrefixState) (s' : LastPrefixState)
      (_hInv : LastPrefixInv s) (hNext : Next s s') :
      LastPrefixInv s' :=
      Exists.elim hNext (fun (po : UInt64) (hRest : ∃ (rs : UInt64), s' = prefixQueryStep po rs s) =>
        Exists.elim hRest (fun (rs : UInt64) (hEq : s' = prefixQueryStep po rs s) =>
          Eq.mpr
            (congrArg (fun (st : LastPrefixState) => LastPrefixInv st) hEq)
            (And.intro
              (off_ge_prev s.cur_off po)
              (scan_le_max rs s.scan_max))))

    theorem last_prefix_safety_always :
      Satisfies Spec (Always (Lift LastPrefixInv)) :=
      invariantSatisfies Spec LastPrefixInv init_establishes_inv next_preserves_inv

    end TlaLastPrefixScan
    end Broker
    end Astream

    -- =======================================================================
    -- 3. Rust `contract_fn!` `#[ensures]` Specification Counterparts (`_isl`)
    -- =======================================================================

    def last_scan_within_cap_isl (scanned : USize) (scan_max : USize) : Bool :=
      decide (scanned ≤ scan_max)
}
