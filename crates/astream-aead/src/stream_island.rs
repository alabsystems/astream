// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `stream.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `stream.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic & State-Machine Kernel (Trust.Temporal)
    -- ========================================================================
    namespace Trust
    namespace Temporal

    def Behavior (State : Type) := Nat → State
    def Formula (State : Type) := Behavior State → Prop

    def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
      fun k => b (n + k)

    def Always {State : Type} (F : Formula State) : Formula State :=
      fun b => ∀ n, F (drop b n)

    def Eventually {State : Type} (F : Formula State) : Formula State :=
      fun b => ∃ n, F (drop b n)

    def LeadsTo {State : Type} (F G : Formula State) : Formula State :=
      Always (fun b => F b → Eventually G b)

    structure StateMachine (State : Type) where
      init : State → Prop
      next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
      M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

    def Lift {State : Type} (P : State → Prop) : Formula State :=
      fun b => P (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
      ∀ b, Runs M b → F b

    prefix:100 "□" => _root_.Trust.Temporal.Always
    prefix:100 "◇" => _root_.Trust.Temporal.Eventually
    infixl:50 " ~> " => _root_.Trust.Temporal.LeadsTo
    infixl:45 " ⊨ " => _root_.Trust.Temporal.Satisfies

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

    end Temporal
    end Trust

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    --    Compiled directly from these Clean kernel definitions into Rust MIR
    --    (`pub const fn ...`) and verified by `trust_clean_origin::Faithful`.
    -- ========================================================================

    -- Monotone AEAD record sequence watermark (`max(cur_seq, next_seq)`).
    def aead_seq_monotone (cur_seq : UInt64) (next_seq : UInt64) : UInt64 :=
      if cur_seq < next_seq then next_seq else cur_seq

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: SealedStream Ordered-Record AEAD
    -- ========================================================================
    namespace Astream
    namespace Aead
    namespace TlaSealedStream

    open Trust.Temporal

    theorem aead_seq_ge_cur : forall (cur_seq : UInt64) (next_seq : UInt64),
        Nat.le (UInt64.toNat cur_seq) (UInt64.toNat (_root_.aead_seq_monotone cur_seq next_seq)) :=
      fun cur next => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur next)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => next))))
        (instDecidableUInt64Lt cur next)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem aead_seq_lub (cur next bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hNext : Nat.le (UInt64.toNat next) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.aead_seq_monotone cur next)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur next)
        (fun (d : Decidable (LT.lt cur next)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur next) d next cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur next)
        (fun _ => hCur)
        (fun _ => hNext)

    theorem aead_seq_gt_cur (cur next : UInt64)
        (hLt : Nat.lt (UInt64.toNat cur) (UInt64.toNat next)) :
        Nat.lt (UInt64.toNat cur) (UInt64.toNat (_root_.aead_seq_monotone cur next)) :=
      @Decidable.casesOn (LT.lt cur next)
        (fun (d : Decidable (LT.lt cur next)) =>
          Nat.lt (UInt64.toNat cur) (UInt64.toNat (@ite UInt64 (LT.lt cur next) d next cur)))
        (instDecidableUInt64Lt cur next)
        (fun hNotLt => False.elim (hNotLt hLt))
        (fun _ => hLt)

    -- State variables for one direction of a SealedStream connection:
    --   sendSeq    : number of records sealed by the sender (`UInt64`)
    --   recvSeq    : next record sequence number expected by the receiver's AAD (`UInt64`)
    --   lastOpened : sequence number of the most recently opened record (`UInt64`)
    --   hasOpened  : 0 before any record is opened, 1 thereafter
    --   poisoned   : 0 while healthy, 1 after any tag/replay/reorder/truncation error
    structure StreamState where
      sendSeq    : UInt64
      recvSeq    : UInt64
      lastOpened : UInt64
      hasOpened  : Nat
      poisoned   : Nat

    -- TLA+ Safety Invariant:
    -- 1. The receiver never opens beyond what the sender has sealed (`recvSeq <= sendSeq`).
    -- 2. Once at least one record has been opened (`hasOpened = 1`), its sequence
    --    number is strictly below the next expected `recvSeq` (`lastOpened < recvSeq`),
    --    guaranteeing strict monotonicity and anti-replay.
    def SealedStreamInv (s : StreamState) : Prop :=
      Nat.le (UInt64.toNat s.recvSeq) (UInt64.toNat s.sendSeq) ∧
      (s.hasOpened = 1 → Nat.lt (UInt64.toNat s.lastOpened) (UInt64.toNat s.recvSeq))

    def Init (s : StreamState) : Prop :=
      s.sendSeq = 0 ∧
      s.recvSeq = 0 ∧
      s.lastOpened = 0 ∧
      s.hasOpened = 0 ∧
      s.poisoned = 0

    -- Action 1: SealRecord — sender seals the next record and advances `sendSeq`
    -- via Clean-origin `_root_.aead_seq_monotone`.
    def SealRecord (nextSend : UInt64) (s sNext : StreamState) : Prop :=
      s.poisoned = 0 ∧
      sNext.sendSeq = _root_.aead_seq_monotone s.sendSeq nextSend ∧
      sNext.recvSeq = s.recvSeq ∧
      sNext.lastOpened = s.lastOpened ∧
      sNext.hasOpened = s.hasOpened ∧
      sNext.poisoned = s.poisoned

    -- Action 2: OpenInOrder — receiver opens the next authentic record at `recvSeq < nextRecv <= sendSeq`
    -- and advances `recvSeq` via Clean-origin `_root_.aead_seq_monotone`.
    def OpenInOrder (nextRecv : UInt64) (s sNext : StreamState) : Prop :=
      s.poisoned = 0 ∧
      Nat.lt (UInt64.toNat s.recvSeq) (UInt64.toNat nextRecv) ∧
      Nat.le (UInt64.toNat nextRecv) (UInt64.toNat s.sendSeq) ∧
      sNext.sendSeq = s.sendSeq ∧
      sNext.recvSeq = _root_.aead_seq_monotone s.recvSeq nextRecv ∧
      sNext.lastOpened = s.recvSeq ∧
      sNext.hasOpened = 1 ∧
      sNext.poisoned = s.poisoned

    -- Action 3: RejectOutOfOrderOrTamper — replayed, reordered, reflected, or
    -- tampered record fails its Poly1305 tag check and poisons the stream.
    def RejectOutOfOrderOrTamper (s sNext : StreamState) : Prop :=
      sNext.sendSeq = s.sendSeq ∧
      sNext.recvSeq = s.recvSeq ∧
      sNext.lastOpened = s.lastOpened ∧
      sNext.hasOpened = s.hasOpened ∧
      sNext.poisoned = 1

    def Next (s sNext : StreamState) : Prop :=
      (∃ nextSend : UInt64, SealRecord nextSend s sNext) ∨
        ((∃ nextRecv : UInt64, OpenInOrder nextRecv s sNext) ∨ RejectOutOfOrderOrTamper s sNext)

    def Spec : StateMachine StreamState :=
      StateMachine.mk Init Next

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (s : StreamState) (hInit : Init s) :
        SealedStreamInv s :=
      let hLe0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.sendSeq) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat 0) (UInt64.toNat x)) hInit.1) (Nat.le_refl (UInt64.toNat 0))
      let hLe : Nat.le (UInt64.toNat s.recvSeq) (UInt64.toNat s.sendSeq) :=
        Eq.mpr (congrArg (fun r => Nat.le (UInt64.toNat r) (UInt64.toNat s.sendSeq)) hInit.2.1) hLe0
      let hOrd : s.hasOpened = 1 → Nat.lt (UInt64.toNat s.lastOpened) (UInt64.toNat s.recvSeq) :=
        fun hOpen =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.2.2.1) hOpen
          False.elim (zero_ne_one h01)
      And.intro hLe hOrd

    theorem seal_preserves_inv (nextSend : UInt64) (s sNext : StreamState)
        (hInv : SealedStreamInv s) (hAct : SealRecord nextSend s sNext) :
        SealedStreamInv sNext :=
      let hMono : Nat.le (UInt64.toNat s.sendSeq) (UInt64.toNat (_root_.aead_seq_monotone s.sendSeq nextSend)) :=
        aead_seq_ge_cur s.sendSeq nextSend
      let hStep : Nat.le (UInt64.toNat s.recvSeq) (UInt64.toNat (_root_.aead_seq_monotone s.sendSeq nextSend)) :=
        Nat.le_trans hInv.1 hMono
      let hLe1 : Nat.le (UInt64.toNat s.recvSeq) (UInt64.toNat sNext.sendSeq) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat s.recvSeq) (UInt64.toNat x)) hAct.2.1) hStep
      let hLeNext : Nat.le (UInt64.toNat sNext.recvSeq) (UInt64.toNat sNext.sendSeq) :=
        Eq.mpr (congrArg (fun r => Nat.le (UInt64.toNat r) (UInt64.toNat sNext.sendSeq)) hAct.2.2.1) hLe1
      let hOrdNext : sNext.hasOpened = 1 → Nat.lt (UInt64.toNat sNext.lastOpened) (UInt64.toNat sNext.recvSeq) :=
        fun hOpenNext =>
          let hOpen : s.hasOpened = 1 := Eq.trans (Eq.symm hAct.2.2.2.2.1) hOpenNext
          let hLt : Nat.lt (UInt64.toNat s.lastOpened) (UInt64.toNat s.recvSeq) := hInv.2 hOpen
          let hLt1 : Nat.lt (UInt64.toNat sNext.lastOpened) (UInt64.toNat s.recvSeq) :=
            Eq.mpr (congrArg (fun l => Nat.lt (UInt64.toNat l) (UInt64.toNat s.recvSeq)) hAct.2.2.2.1) hLt
          Eq.mpr (congrArg (fun r => Nat.lt (UInt64.toNat sNext.lastOpened) (UInt64.toNat r)) hAct.2.2.1) hLt1
      And.intro hLeNext hOrdNext

    theorem open_preserves_inv (nextRecv : UInt64) (s sNext : StreamState)
        (hInv : SealedStreamInv s) (hAct : OpenInOrder nextRecv s sNext) :
        SealedStreamInv sNext :=
      let hLub : Nat.le (UInt64.toNat (_root_.aead_seq_monotone s.recvSeq nextRecv)) (UInt64.toNat s.sendSeq) :=
        aead_seq_lub s.recvSeq nextRecv s.sendSeq hInv.1 hAct.2.2.1
      let hLe1 : Nat.le (UInt64.toNat (_root_.aead_seq_monotone s.recvSeq nextRecv)) (UInt64.toNat sNext.sendSeq) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat (_root_.aead_seq_monotone s.recvSeq nextRecv)) (UInt64.toNat x)) hAct.2.2.2.1) hLub
      let hLeNext : Nat.le (UInt64.toNat sNext.recvSeq) (UInt64.toNat sNext.sendSeq) :=
        Eq.mpr (congrArg (fun r => Nat.le (UInt64.toNat r) (UInt64.toNat sNext.sendSeq)) hAct.2.2.2.2.1) hLe1
      let hOrdNext : sNext.hasOpened = 1 → Nat.lt (UInt64.toNat sNext.lastOpened) (UInt64.toNat sNext.recvSeq) :=
        fun _ =>
          let hLtSelf : Nat.lt (UInt64.toNat s.recvSeq) (UInt64.toNat (_root_.aead_seq_monotone s.recvSeq nextRecv)) :=
            aead_seq_gt_cur s.recvSeq nextRecv hAct.2.1
          let hLt1 : Nat.lt (UInt64.toNat sNext.lastOpened) (UInt64.toNat (_root_.aead_seq_monotone s.recvSeq nextRecv)) :=
            Eq.mpr (congrArg (fun l => Nat.lt (UInt64.toNat l) (UInt64.toNat (_root_.aead_seq_monotone s.recvSeq nextRecv))) hAct.2.2.2.2.2.1) hLtSelf
          Eq.mpr (congrArg (fun r => Nat.lt (UInt64.toNat sNext.lastOpened) (UInt64.toNat r)) hAct.2.2.2.2.1) hLt1
      And.intro hLeNext hOrdNext

    theorem reject_preserves_inv (s sNext : StreamState)
        (hInv : SealedStreamInv s) (hAct : RejectOutOfOrderOrTamper s sNext) :
        SealedStreamInv sNext :=
      let hLe1 : Nat.le (UInt64.toNat s.recvSeq) (UInt64.toNat sNext.sendSeq) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat s.recvSeq) (UInt64.toNat x)) hAct.1) hInv.1
      let hLeNext : Nat.le (UInt64.toNat sNext.recvSeq) (UInt64.toNat sNext.sendSeq) :=
        Eq.mpr (congrArg (fun r => Nat.le (UInt64.toNat r) (UInt64.toNat sNext.sendSeq)) hAct.2.1) hLe1
      let hOrdNext : sNext.hasOpened = 1 → Nat.lt (UInt64.toNat sNext.lastOpened) (UInt64.toNat sNext.recvSeq) :=
        fun hOpenNext =>
          let hOpen : s.hasOpened = 1 := Eq.trans (Eq.symm hAct.2.2.2.1) hOpenNext
          let hLt : Nat.lt (UInt64.toNat s.lastOpened) (UInt64.toNat s.recvSeq) := hInv.2 hOpen
          let hLt1 : Nat.lt (UInt64.toNat sNext.lastOpened) (UInt64.toNat s.recvSeq) :=
            Eq.mpr (congrArg (fun l => Nat.lt (UInt64.toNat l) (UInt64.toNat s.recvSeq)) hAct.2.2.1) hLt
          Eq.mpr (congrArg (fun r => Nat.lt (UInt64.toNat sNext.lastOpened) (UInt64.toNat r)) hAct.2.1) hLt1
      And.intro hLeNext hOrdNext

    theorem next_preserves_inv (s sNext : StreamState)
        (hInv : SealedStreamInv s) (hNext : Next s sNext) :
        SealedStreamInv sNext :=
      Or.elim hNext
        (fun hEx1 =>
          Exists.elim hEx1 (fun nextSend hSeal => seal_preserves_inv nextSend s sNext hInv hSeal))
        (fun hRest =>
          Or.elim hRest
            (fun hEx2 =>
              Exists.elim hEx2 (fun nextRecv hOpen => open_preserves_inv nextRecv s sNext hInv hOpen))
            (fun hRej => reject_preserves_inv s sNext hInv hRej))

    -- Full TLA+ Temporal Safety Theorem:
    --   `Spec ⊨ □ (Lift SealedStreamInv)`
    theorem spec_satisfies_sealed_stream_safety :
        Spec ⊨ □ (Lift SealedStreamInv) :=
      invariantSatisfies Spec SealedStreamInv
        init_establishes_inv
        next_preserves_inv

    -- Anti-replay theorem: any record accepted by the receiver (`candidateSeq = recvSeq`)
    -- has a sequence number strictly greater than `lastOpened` (`lastOpened < candidateSeq`).
    theorem no_replay_possible (lastOpened recvSeq candidateSeq : Nat)
        (hInv : Nat.lt lastOpened recvSeq) (hAccept : candidateSeq = recvSeq) :
        Nat.lt lastOpened candidateSeq :=
      Eq.mpr (congrArg (Nat.lt lastOpened) hAccept) hInv

    end TlaSealedStream
    end Aead
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def aead_can_open_in_order_isl (recv_seq : UInt64) (send_seq : UInt64) : Bool :=
      decide (recv_seq < send_seq)
}
