// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `offset.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `offset.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaLogOffset)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaLogOffset

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

    prefix:100 "□" => _root_.Astream.Wire.TlaLogOffset.Always
    infixl:45 " ⊨ " => _root_.Astream.Wire.TlaLogOffset.Satisfies

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

    end TlaLogOffset
    end Wire
    end Astream

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn offset_advance_monotone`) and verified by
    --    `trust_clean_origin::Faithful` (`clean-kernel-defeq`).
    -- ========================================================================

    -- Monotone advance of a partition offset (`max(current, candidate)`).
    -- Compiled directly to `pub const fn offset_advance_monotone(current: u64, candidate: u64) -> u64`.
    def offset_advance_monotone (current : UInt64) (candidate : UInt64) : UInt64 :=
      if current < candidate then candidate else current

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Partition Log Offset Progression
    --    Directly over `UInt64` log offsets, `_root_.offset_advance_monotone`,
    --    and `offset_precedes_or_eq_isl`
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaLogOffset

    -- Island specification of `pub fn offset_precedes_or_eq(earlier: u64, later: u64) -> bool`.
    def offset_precedes_or_eq_isl (earlier : UInt64) (later : UInt64) : Bool :=
      decide (earlier <= later)

    theorem offset_advance_monotone_ge_current : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.offset_advance_monotone cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    -- State of a single partition's log offset progression:
    --   status     : 0 = Open, 1 = Sealed
    --   baseOffset : earliest retained offset (`UInt64`)
    --   hwm        : high-water mark offset (`UInt64`)
    structure LogState where
      status     : Nat
      baseOffset : UInt64
      hwm        : UInt64

    -- TLA+ Safety Invariant:
    -- `baseOffset <= hwm`: the retention base offset never exceeds the
    -- high-water mark, so `hwm.delta_from(baseOffset)` is always defined.
    def LogOffsetSafetyInv (s : LogState) : Prop :=
      Nat.le (UInt64.toNat s.baseOffset) (UInt64.toNat s.hwm)

    def Init (s : LogState) : Prop :=
      s.status = 0 ∧
      s.baseOffset = 0 ∧
      s.hwm = 0

    -- Action 1: AppendRecord — advances `hwm` monotonically via
    -- `_root_.offset_advance_monotone s.hwm candidate_hwm`.
    def AppendRecord (candidate_hwm : UInt64) (s sNext : LogState) : Prop :=
      s.status = 0 ∧
      sNext.status = 0 ∧
      sNext.baseOffset = s.baseOffset ∧
      sNext.hwm = _root_.offset_advance_monotone s.hwm candidate_hwm

    -- Action 2: RetainToHwm — advances `baseOffset` up to the current `hwm`.
    def RetainToHwm (s sNext : LogState) : Prop :=
      s.status = 0 ∧
      sNext.status = 0 ∧
      sNext.baseOffset = s.hwm ∧
      sNext.hwm = s.hwm

    -- Action 3: SealLog — seals the partition log, preserving `baseOffset` and `hwm`.
    def SealLog (s sNext : LogState) : Prop :=
      s.status = 0 ∧
      sNext.status = 1 ∧
      sNext.baseOffset = s.baseOffset ∧
      sNext.hwm = s.hwm

    def Next (s sNext : LogState) : Prop :=
      (∃ candidate_hwm : UInt64, AppendRecord candidate_hwm s sNext) ∨
        (RetainToHwm s sNext ∨ SealLog s sNext)

    def Spec : StateMachine LogState :=
      StateMachine.mk Init Next

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat a) (UInt64.toNat x)) (Eq.symm hEq))
        (Nat.le.refl (UInt64.toNat a))

    theorem init_implies_inv (s : LogState) (hInit : Init s) : LogOffsetSafetyInv s :=
      uint64_eq_le s.baseOffset s.hwm (Eq.trans hInit.2.1 (Eq.symm hInit.2.2))

    theorem append_preserves_inv (candidate_hwm : UInt64) (s sNext : LogState)
        (hInv : LogOffsetSafetyInv s) (hAct : AppendRecord candidate_hwm s sNext) :
        LogOffsetSafetyInv sNext :=
      let hBaseEq : sNext.baseOffset = s.baseOffset := hAct.2.2.1
      let hHwmEq : sNext.hwm = _root_.offset_advance_monotone s.hwm candidate_hwm := hAct.2.2.2
      let hBaseLeHwm : Nat.le (UInt64.toNat sNext.baseOffset) (UInt64.toNat s.hwm) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.hwm)) hBaseEq) hInv
      let hHwmLeNext : Nat.le (UInt64.toNat s.hwm) (UInt64.toNat sNext.hwm) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat s.hwm) (UInt64.toNat x)) hHwmEq)
          (offset_advance_monotone_ge_current s.hwm candidate_hwm)
      Nat.le_trans hBaseLeHwm hHwmLeNext

    theorem retain_preserves_inv (s sNext : LogState)
        (_hInv : LogOffsetSafetyInv s) (hAct : RetainToHwm s sNext) :
        LogOffsetSafetyInv sNext :=
      uint64_eq_le sNext.baseOffset sNext.hwm
        (Eq.trans hAct.2.2.1 (Eq.symm hAct.2.2.2))

    theorem seal_preserves_inv (s sNext : LogState)
        (hInv : LogOffsetSafetyInv s) (hAct : SealLog s sNext) :
        LogOffsetSafetyInv sNext :=
      let h1 : Nat.le (UInt64.toNat sNext.baseOffset) (UInt64.toNat s.hwm) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.hwm)) hAct.2.2.1) hInv
      Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat sNext.baseOffset) (UInt64.toNat x)) hAct.2.2.2) h1

    theorem next_preserves_inv (s sNext : LogState)
        (hInv : LogOffsetSafetyInv s) (hNext : Next s sNext) :
        LogOffsetSafetyInv sNext :=
      Or.elim hNext
        (fun hApp => Exists.elim hApp (fun cand hAct => append_preserves_inv cand s sNext hInv hAct))
        (fun hRest => Or.elim hRest
          (fun hRet => retain_preserves_inv s sNext hInv hRet)
          (fun hSeal => seal_preserves_inv s sNext hInv hSeal))

    -- ========================================================================
    -- 4. Top-Level Temporal Theorem: `Spec ⊨ □ (Lift LogOffsetSafetyInv)`
    -- ========================================================================
    theorem spec_satisfies_always_offset_safety : Spec ⊨ □ (Lift LogOffsetSafetyInv) :=
      invariantSatisfies Spec LogOffsetSafetyInv init_implies_inv next_preserves_inv

    end TlaLogOffset
    end Wire
    end Astream
}
