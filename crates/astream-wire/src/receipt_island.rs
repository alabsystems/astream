// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `receipt.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `receipt.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic & State-Machine Kernel (Astream.Wire.TlaFabricReceipts)
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaFabricReceipts

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

    prefix:100 "□" => _root_.Astream.Wire.TlaFabricReceipts.Always
    infixl:45 " ⊨ " => _root_.Astream.Wire.TlaFabricReceipts.Satisfies

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

    end TlaFabricReceipts
    end Wire
    end Astream

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn monotone_clock_tick`) and verified by
    --    `trust_clean_origin::Faithful` (`clean-kernel-defeq`).
    -- ========================================================================

    -- Monotone broker/bridge clock advance (`max(now_ms, sample_ms)`).
    -- Compiled directly to `pub const fn monotone_clock_tick(now_ms: u64, sample_ms: u64) -> u64`.
    def monotone_clock_tick (now_ms : UInt64) (sample_ms : UInt64) : UInt64 :=
      if now_ms < sample_ms then sample_ms else now_ms

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Fabric Receipts & Deadlines (R8)
    --    Directly over `UInt64` timestamps, `_root_.monotone_clock_tick`, and
    --    `deadline_elapsed_isl`
    --    SCOPE: one request whose deadline is an ABSOLUTE `dlMs` on the clock
    --    that stamps `btMs`. The bus's deadline is a RELATIVE `dl=` the asker's
    --    bridge judges on its own clock, and no record carries that instant or a
    --    `bt=`, so this model does not cover it (receipt.rs, `V1Receipt`).
    -- ========================================================================
    namespace Astream
    namespace Wire
    namespace TlaFabricReceipts

    -- Island specification of `pub fn deadline_elapsed(dl_ms: u64, bt_ms: u64) -> bool`.
    def deadline_elapsed_isl (dl_ms : UInt64) (bt_ms : UInt64) : Bool :=
      decide (dl_ms <= bt_ms)

    -- Monotonicity of the Clean-origin `_root_.monotone_clock_tick` function:
    -- `now_ms <= monotone_clock_tick now_ms sample_ms`.
    theorem monotone_clock_tick_ge_now (now_ms sample_ms : UInt64) :
        Nat.le (UInt64.toNat now_ms) (UInt64.toNat (_root_.monotone_clock_tick now_ms sample_ms)) :=
      @Decidable.casesOn (LT.lt now_ms sample_ms)
        (fun (d : Decidable (LT.lt now_ms sample_ms)) =>
          Nat.le (UInt64.toNat now_ms)
            (UInt64.toNat (@ite UInt64 (LT.lt now_ms sample_ms) d sample_ms now_ms)))
        (instDecidableUInt64Lt now_ms sample_ms)
        (fun _ => Nat.le_refl (UInt64.toNat now_ms))
        (fun hLt => Nat.le_of_lt hLt)

    -- State of a tracked request at offset `re` with deadline `dlMs`:
    --   status  : 0 = Pending, 1 = Acked, 2 = Expired
    --   verdict : 0 = None, 1 = Handled, 2 = Refused, 3 = Deferred
    --   dlMs    : deadline timestamp (unix ms, `UInt64`)
    --   btMs    : broker timestamp recorded on the terminal receipt (`UInt64`)
    --   nowMs   : monotone clock (unix ms, `UInt64`)
    structure ReceiptState where
      status  : Nat
      verdict : Nat
      dlMs    : UInt64
      btMs    : UInt64
      nowMs   : UInt64

    -- TLA+ Safety Invariant over `UInt64` timestamps:
    -- 1. If `status = 0` (Pending), no verdict has been recorded (`verdict = 0`).
    -- 2. If `status = 2` (Expired), no ack verdict is set (`verdict = 0`) and
    --    the expiry receipt timestamp satisfies `dlMs <= btMs` (`deadline_elapsed_isl`)
    --    and `btMs <= nowMs`.
    def ReceiptSafetyInv (s : ReceiptState) : Prop :=
      (s.status = 0 → s.verdict = 0) ∧
      (s.status = 2 →
        (s.verdict = 0 ∧
         Nat.le (UInt64.toNat s.dlMs) (UInt64.toNat s.btMs) ∧
         Nat.le (UInt64.toNat s.btMs) (UInt64.toNat s.nowMs)))

    def Init (dl t0 : UInt64) (s : ReceiptState) : Prop :=
      s.status = 0 ∧
      s.verdict = 0 ∧
      s.dlMs = dl ∧
      s.btMs = 0 ∧
      s.nowMs = t0

    -- Action 1: ReceiveAck — recipient bridge emits `ack re=<off> verdict=<v> bt=<nowMs>`
    -- while the request is still Pending (`status = 0`).
    def ReceiveAck (v : Nat) (s sNext : ReceiptState) : Prop :=
      s.status = 0 ∧
      sNext.status = 1 ∧
      sNext.verdict = v ∧
      sNext.dlMs = s.dlMs ∧
      sNext.btMs = s.nowMs ∧
      sNext.nowMs = s.nowMs

    theorem bool_false_ne_true (h : false = true) : False :=
      Bool.noConfusion h

    -- Soundness of the `deadline_elapsed_isl` guard over `UInt64`:
    -- `deadline_elapsed_isl dl bt = true -> dl <= bt`.
    theorem deadline_elapsed_isl_true_le (dl bt : UInt64) :
        deadline_elapsed_isl dl bt = true → Nat.le (UInt64.toNat dl) (UInt64.toNat bt) :=
      @Decidable.casesOn (LE.le dl bt)
        (fun (d : Decidable (LE.le dl bt)) =>
          @Decidable.decide (LE.le dl bt) d = true → Nat.le (UInt64.toNat dl) (UInt64.toNat bt))
        (instDecidableUInt64Le dl bt)
        (fun _ hEq => False.elim (bool_false_ne_true hEq))
        (fun hLe _ => hLe)

    -- Action 2: EmitExpired — asker bridge emits `expired re=<off> dl=<dlMs> bt=<nowMs>`
    -- when `status = 0` and the Rust-verified `deadline_elapsed_isl s.dlMs s.nowMs`
    -- guard returns `true`.
    def EmitExpired (s sNext : ReceiptState) : Prop :=
      s.status = 0 ∧
      deadline_elapsed_isl s.dlMs s.nowMs = true ∧
      sNext.status = 2 ∧
      sNext.verdict = 0 ∧
      sNext.dlMs = s.dlMs ∧
      sNext.btMs = s.nowMs ∧
      sNext.nowMs = s.nowMs

    -- Action 3: TickClock — monotone progression of `nowMs` directly via the
    -- Clean-origin Rust function `_root_.monotone_clock_tick`.
    def TickClock (sample_ms : UInt64) (s sNext : ReceiptState) : Prop :=
      sNext.nowMs = _root_.monotone_clock_tick s.nowMs sample_ms ∧
      sNext.status = s.status ∧
      sNext.verdict = s.verdict ∧
      sNext.dlMs = s.dlMs ∧
      sNext.btMs = s.btMs

    def Next (s sNext : ReceiptState) : Prop :=
      (∃ v : Nat, ReceiveAck v s sNext) ∨
        (EmitExpired s sNext ∨ (∃ sample_ms : UInt64, TickClock sample_ms s sNext))

    def Spec (dl t0 : UInt64) : StateMachine ReceiptState :=
      StateMachine.mk (Init dl t0) Next

    theorem zero_ne_two (h : 0 = 2) : False :=
      Nat.noConfusion h

    theorem one_ne_zero (h : 1 = 0) : False :=
      Nat.noConfusion h

    theorem one_ne_two (h : 1 = 2) : False :=
      Nat.noConfusion h (fun h01 => Nat.noConfusion h01)

    theorem two_ne_zero (h : 2 = 0) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (dl t0 : UInt64) (s : ReceiptState)
        (hInit : Init dl t0 s) : ReceiptSafetyInv s :=
      And.intro
        (fun _ => hInit.2.1)
        (fun hSt2 =>
          let h02 : 0 = 2 := Eq.trans (Eq.symm hInit.1) hSt2
          False.elim (zero_ne_two h02))

    theorem receiveAck_preserves_inv (v : Nat) (s sNext : ReceiptState)
        (hAct : ReceiveAck v s sNext) : ReceiptSafetyInv sNext :=
      And.intro
        (fun hSt0 =>
          let h10 : 1 = 0 := Eq.trans (Eq.symm hAct.2.1) hSt0
          False.elim (one_ne_zero h10))
        (fun hSt2 =>
          let h12 : 1 = 2 := Eq.trans (Eq.symm hAct.2.1) hSt2
          False.elim (one_ne_two h12))

    theorem emitExpired_preserves_inv (s sNext : ReceiptState)
        (hAct : EmitExpired s sNext) : ReceiptSafetyInv sNext :=
      And.intro
        (fun hSt0 =>
          let h20 : 2 = 0 := Eq.trans (Eq.symm hAct.2.2.1) hSt0
          False.elim (two_ne_zero h20))
        (fun _ =>
          let hLeGuard : Nat.le (UInt64.toNat s.dlMs) (UInt64.toNat s.nowMs) :=
            deadline_elapsed_isl_true_le s.dlMs s.nowMs hAct.2.1
          let hDl : sNext.dlMs = s.dlMs := hAct.2.2.2.2.1
          let hBt : sNext.btMs = s.nowMs := hAct.2.2.2.2.2.1
          let hNow : sNext.nowMs = s.nowMs := hAct.2.2.2.2.2.2
          let hLe1 : Nat.le (UInt64.toNat sNext.dlMs) (UInt64.toNat s.nowMs) :=
            Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.nowMs)) hDl) hLeGuard
          let hLeDlBt : Nat.le (UInt64.toNat sNext.dlMs) (UInt64.toNat sNext.btMs) :=
            Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.dlMs) (UInt64.toNat y)) hBt) hLe1
          let hRefl : Nat.le (UInt64.toNat s.nowMs) (UInt64.toNat s.nowMs) :=
            Nat.le_refl (UInt64.toNat s.nowMs)
          let hLe2 : Nat.le (UInt64.toNat sNext.btMs) (UInt64.toNat s.nowMs) :=
            Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.nowMs)) hBt) hRefl
          let hLeBtNow : Nat.le (UInt64.toNat sNext.btMs) (UInt64.toNat sNext.nowMs) :=
            Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.btMs) (UInt64.toNat y)) hNow) hLe2
          And.intro hAct.2.2.2.1 (And.intro hLeDlBt hLeBtNow))

    theorem tickClock_preserves_inv (sample_ms : UInt64) (s sNext : ReceiptState)
        (hInv : ReceiptSafetyInv s) (hAct : TickClock sample_ms s sNext) :
        ReceiptSafetyInv sNext :=
      And.intro
        (fun hSt0Next =>
          let hSt0 : s.status = 0 := Eq.trans (Eq.symm hAct.2.1) hSt0Next
          Eq.trans hAct.2.2.1 (hInv.1 hSt0))
        (fun hSt2Next =>
          let hSt2 : s.status = 2 := Eq.trans (Eq.symm hAct.2.1) hSt2Next
          let hPre := hInv.2 hSt2
          let hVerd : sNext.verdict = 0 := Eq.trans hAct.2.2.1 hPre.1
          let hLe1 : Nat.le (UInt64.toNat sNext.dlMs) (UInt64.toNat s.btMs) :=
            Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.btMs)) hAct.2.2.2.1) hPre.2.1
          let hLeDlBt : Nat.le (UInt64.toNat sNext.dlMs) (UInt64.toNat sNext.btMs) :=
            Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.dlMs) (UInt64.toNat y)) hAct.2.2.2.2) hLe1
          let hLeBtOldNow : Nat.le (UInt64.toNat sNext.btMs) (UInt64.toNat s.nowMs) :=
            Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.nowMs)) hAct.2.2.2.2) hPre.2.2
          let hTickLe : Nat.le (UInt64.toNat s.nowMs)
              (UInt64.toNat (_root_.monotone_clock_tick s.nowMs sample_ms)) :=
            monotone_clock_tick_ge_now s.nowMs sample_ms
          let hNowLe : Nat.le (UInt64.toNat s.nowMs) (UInt64.toNat sNext.nowMs) :=
            Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat s.nowMs) (UInt64.toNat y)) hAct.1) hTickLe
          let hLeBtNow : Nat.le (UInt64.toNat sNext.btMs) (UInt64.toNat sNext.nowMs) :=
            Nat.le_trans hLeBtOldNow hNowLe
          And.intro hVerd (And.intro hLeDlBt hLeBtNow))

    theorem next_preserves_inv (s sNext : ReceiptState)
        (hInv : ReceiptSafetyInv s) (hNext : Next s sNext) :
        ReceiptSafetyInv sNext :=
      Or.elim hNext
        (fun hEx =>
          Exists.elim hEx (fun v hAck => receiveAck_preserves_inv v s sNext hAck))
        (fun hRest =>
          Or.elim hRest
            (fun hExp => emitExpired_preserves_inv s sNext hExp)
            (fun hExTick =>
              Exists.elim hExTick (fun sample_ms hTick =>
                tickClock_preserves_inv sample_ms s sNext hInv hTick)))

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec dl t0) ⊨ □ (Lift ReceiptSafetyInv)`
    theorem spec_satisfies_receipt_safety (dl t0 : UInt64) :
        (Spec dl t0) ⊨ □ (Lift ReceiptSafetyInv) :=
      invariantSatisfies (Spec dl t0) ReceiptSafetyInv
        (init_establishes_inv dl t0)
        next_preserves_inv

    end TlaFabricReceipts
    end Wire
    end Astream
}
