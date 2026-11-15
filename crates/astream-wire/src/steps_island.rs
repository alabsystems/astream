// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `steps.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `steps.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaStepScan)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaStepScan

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

    prefix:100 "□" => _root_.Astream.Wire.TlaStepScan.Always
    infixl:45 " ⊨ " => _root_.Astream.Wire.TlaStepScan.Satisfies

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

    end TlaStepScan
    end Wire
    end Astream

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn step_prefix_advance`) and verified by
    --    `trust_clean_origin::Faithful` (`clean-kernel-defeq`).
    -- ========================================================================

    -- Monotone advance of the intact step prefix byte offset (`max(valid_len, next_pos)`).
    -- Compiled directly to `pub const fn step_prefix_advance(valid_len: u64, next_pos: u64) -> u64`.
    def step_prefix_advance (valid_len : UInt64) (next_pos : UInt64) : UInt64 :=
      if valid_len < next_pos then next_pos else valid_len

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Step-Record Prefix & Torn/Fault Scanner
    --    Directly over `UInt64` byte offsets, `_root_.step_prefix_advance`, and
    --    `step_within_bounds_isl`
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaStepScan

    -- Island specification of `pub fn step_within_bounds(pos: u64, limit: u64) -> bool`.
    def step_within_bounds_isl (pos : UInt64) (limit : UInt64) : Bool :=
      decide (pos <= limit)

    theorem step_prefix_advance_ge_valid : forall (v : UInt64) (n : UInt64),
        Nat.le (UInt64.toNat v) (UInt64.toNat (_root_.step_prefix_advance v n)) :=
      fun v n => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt v n)) =>
          Nat.le (UInt64.toNat v) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => v) (fun _ => n))))
        (instDecidableUInt64Lt v n)
        (fun _ => Nat.le.refl (UInt64.toNat v))
        (fun h => Nat.le_of_lt h)

    -- State of `scan_steps_from`:
    --   status   : 0 = Scanning, 1 = CleanEnd, 2 = TornTail, 3 = Fault
    --   validLen : byte length of the longest intact, in-order prefix (`UInt64`)
    --   scanPos  : byte offset reached by the scanner (`UInt64`)
    structure ScanState where
      status   : Nat
      validLen : UInt64
      scanPos  : UInt64

    -- TLA+ Safety Invariant:
    -- 1. `validLen <= scanPos`: the intact prefix never overruns the scanned cursor.
    -- 2. `status = 1 -> validLen = scanPos`: a `Clean` end holds only when every
    --    scanned byte belongs to the intact prefix (no torn or faulted tail).
    def StepScanSafetyInv (s : ScanState) : Prop :=
      Nat.le (UInt64.toNat s.validLen) (UInt64.toNat s.scanPos) ∧
      (s.status = 1 → s.validLen = s.scanPos)

    def Init (s : ScanState) : Prop :=
      s.status = 0 ∧
      s.validLen = 0 ∧
      s.scanPos = 0

    -- Action 1: AcceptInOrderStep — frame and step record are intact and match `expected`;
    -- both `validLen` and `scanPos` advance together to `_root_.step_prefix_advance s.validLen next_pos`.
    def AcceptInOrderStep (next_pos : UInt64) (s sNext : ScanState) : Prop :=
      s.status = 0 ∧
      sNext.status = 0 ∧
      sNext.validLen = _root_.step_prefix_advance s.validLen next_pos ∧
      sNext.scanPos = _root_.step_prefix_advance s.validLen next_pos

    -- Action 2: FinishClean — scan reaches exact end of bytes at a record boundary.
    def FinishClean (s sNext : ScanState) : Prop :=
      s.status = 0 ∧
      s.validLen = s.scanPos ∧
      sNext.status = 1 ∧
      sNext.validLen = s.validLen ∧
      sNext.scanPos = s.scanPos

    -- Action 3: FinishTornTail — trailing bytes after `validLen` hold no complete frame.
    def FinishTornTail (tail_pos : UInt64) (s sNext : ScanState) : Prop :=
      s.status = 0 ∧
      sNext.status = 2 ∧
      sNext.validLen = s.validLen ∧
      sNext.scanPos = _root_.step_prefix_advance s.validLen tail_pos

    -- Action 4: FinishFault — out-of-order step, bad version, or mid-run corruption.
    def FinishFault (fault_pos : UInt64) (s sNext : ScanState) : Prop :=
      s.status = 0 ∧
      sNext.status = 3 ∧
      sNext.validLen = s.validLen ∧
      sNext.scanPos = _root_.step_prefix_advance s.validLen fault_pos

    def Next (s sNext : ScanState) : Prop :=
      (∃ next_pos : UInt64, AcceptInOrderStep next_pos s sNext) ∨
        (FinishClean s sNext ∨
          ((∃ tail_pos : UInt64, FinishTornTail tail_pos s sNext) ∨
            (∃ fault_pos : UInt64, FinishFault fault_pos s sNext)))

    def Spec : StateMachine ScanState :=
      StateMachine.mk Init Next

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem two_ne_one (h : 2 = 1) : False :=
      Nat.noConfusion h (fun h10 => Nat.noConfusion h10)

    theorem three_ne_one (h : 3 = 1) : False :=
      Nat.noConfusion h (fun h20 => Nat.noConfusion h20)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : ScanState) (hInit : Init s) : StepScanSafetyInv s :=
      let hEq : s.validLen = s.scanPos := Eq.trans hInit.2.1 (Eq.symm hInit.2.2)
      And.intro
        (uint64_eq_le s.validLen s.scanPos hEq)
        (fun hSt1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.1) hSt1
          False.elim (zero_ne_one h01))

    theorem accept_preserves_inv (next_pos : UInt64) (s sNext : ScanState)
        (hAct : AcceptInOrderStep next_pos s sNext) : StepScanSafetyInv sNext :=
      let hEq : sNext.validLen = sNext.scanPos :=
        Eq.trans hAct.2.2.1 (Eq.symm hAct.2.2.2)
      And.intro
        (uint64_eq_le sNext.validLen sNext.scanPos hEq)
        (fun hSt1 =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.1) hSt1
          False.elim (zero_ne_one h01))

    theorem clean_preserves_inv (s sNext : ScanState)
        (hInv : StepScanSafetyInv s) (hAct : FinishClean s sNext) : StepScanSafetyInv sNext :=
      let hVal : sNext.validLen = s.validLen := hAct.2.2.2.1
      let hPos : sNext.scanPos = s.scanPos := hAct.2.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.validLen) (UInt64.toNat s.scanPos) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.scanPos)) hVal) hInv.1
      let hLe2 : Nat.le (UInt64.toNat sNext.validLen) (UInt64.toNat sNext.scanPos) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.validLen) (UInt64.toNat y)) hPos) hLe1
      let hEqNext : sNext.validLen = sNext.scanPos :=
        Eq.trans hVal (Eq.trans hAct.2.1 (Eq.symm hPos))
      And.intro hLe2 (fun _ => hEqNext)

    theorem torn_preserves_inv (tail_pos : UInt64) (s sNext : ScanState)
        (hAct : FinishTornTail tail_pos s sNext) : StepScanSafetyInv sNext :=
      let hAdv : Nat.le (UInt64.toNat s.validLen) (UInt64.toNat (_root_.step_prefix_advance s.validLen tail_pos)) :=
        step_prefix_advance_ge_valid s.validLen tail_pos
      let hVal : sNext.validLen = s.validLen := hAct.2.2.1
      let hPos : sNext.scanPos = _root_.step_prefix_advance s.validLen tail_pos := hAct.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.validLen) (UInt64.toNat (_root_.step_prefix_advance s.validLen tail_pos)) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (_root_.step_prefix_advance s.validLen tail_pos))) hVal) hAdv
      let hLe2 : Nat.le (UInt64.toNat sNext.validLen) (UInt64.toNat sNext.scanPos) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.validLen) (UInt64.toNat y)) hPos) hLe1
      And.intro
        hLe2
        (fun hSt1 =>
          let h21 : 2 = 1 := Eq.trans (Eq.symm hAct.2.1) hSt1
          False.elim (two_ne_one h21))

    theorem fault_preserves_inv (fault_pos : UInt64) (s sNext : ScanState)
        (hAct : FinishFault fault_pos s sNext) : StepScanSafetyInv sNext :=
      let hAdv : Nat.le (UInt64.toNat s.validLen) (UInt64.toNat (_root_.step_prefix_advance s.validLen fault_pos)) :=
        step_prefix_advance_ge_valid s.validLen fault_pos
      let hVal : sNext.validLen = s.validLen := hAct.2.2.1
      let hPos : sNext.scanPos = _root_.step_prefix_advance s.validLen fault_pos := hAct.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.validLen) (UInt64.toNat (_root_.step_prefix_advance s.validLen fault_pos)) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (_root_.step_prefix_advance s.validLen fault_pos))) hVal) hAdv
      let hLe2 : Nat.le (UInt64.toNat sNext.validLen) (UInt64.toNat sNext.scanPos) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.validLen) (UInt64.toNat y)) hPos) hLe1
      And.intro
        hLe2
        (fun hSt1 =>
          let h31 : 3 = 1 := Eq.trans (Eq.symm hAct.2.1) hSt1
          False.elim (three_ne_one h31))

    theorem next_preserves_inv (s sNext : ScanState)
        (hInv : StepScanSafetyInv s) (hNext : Next s sNext) : StepScanSafetyInv sNext :=
      Or.elim hNext
        (fun hAcc => Exists.elim hAcc (fun next_pos hAct => accept_preserves_inv next_pos s sNext hAct))
        (fun hRest1 =>
          Or.elim hRest1
            (fun hClean => clean_preserves_inv s sNext hInv hClean)
            (fun hRest2 =>
              Or.elim hRest2
                (fun hTorn => Exists.elim hTorn (fun tail_pos hAct => torn_preserves_inv tail_pos s sNext hAct))
                (fun hFault => Exists.elim hFault (fun fault_pos hAct => fault_preserves_inv fault_pos s sNext hAct))))

    theorem spec_satisfies_step_scan_safety :
        Spec ⊨ □ (Lift StepScanSafetyInv) :=
      invariantSatisfies Spec StepScanSafetyInv
        init_establishes_inv
        next_preserves_inv

    end TlaStepScan
    end Wire
    end Astream
}
