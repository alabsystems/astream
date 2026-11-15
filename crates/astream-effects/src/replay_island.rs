// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `replay.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `replay.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn replay_cursor_monotone`) and verified by `Faithful`.
    -- ========================================================================

    -- Monotone replay cursor advance (`max(cur_cursor, next_cursor)`).
    def replay_cursor_monotone (cur_cursor : UInt64) (next_cursor : UInt64) : UInt64 :=
      if cur_cursor < next_cursor then next_cursor else cur_cursor

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Effects.TlaDeterministicReplay)
    -- ========================================================================
    namespace Astream
    namespace Effects
    namespace TlaDeterministicReplay

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

    prefix:100 "□" => _root_.Astream.Effects.TlaDeterministicReplay.Always
    infixl:45 " ⊨ " => _root_.Astream.Effects.TlaDeterministicReplay.Satisfies

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

    theorem replay_cursor_ge_cur : forall (cur_cursor : UInt64) (next_cursor : UInt64),
        Nat.le (UInt64.toNat cur_cursor) (UInt64.toNat (_root_.replay_cursor_monotone cur_cursor next_cursor)) :=
      fun cur next => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur next)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => next))))
        (instDecidableUInt64Lt cur next)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem replay_cursor_lub (cur next bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hNext : Nat.le (UInt64.toNat next) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.replay_cursor_monotone cur next)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur next)
        (fun (d : Decidable (LT.lt cur next)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur next) d next cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur next)
        (fun _ => hCur)
        (fun _ => hNext)

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Deterministic Effect-Tape Replay
    -- ========================================================================
    -- State of a replay run over an effect tape of length `tapeLen`:
    --   cursor        : number of effects consumed so far (`UInt64`)
    --   tapeLen       : total recorded effects on the tape (`UInt64`)
    --   status        : 0 = Active, 1 = Diverged (refused)
    --   matchedPrefix : number of effects replayed with matching kind and path (`UInt64`)
    structure ReplayState where
      cursor        : UInt64
      tapeLen       : UInt64
      status        : Nat
      matchedPrefix : UInt64

    -- TLA+ Safety Invariant:
    -- 1. The replay cursor never exceeds the recorded tape length (`cursor <= tapeLen`).
    -- 2. Every consumed effect matched the recorded kind and path (`matchedPrefix = cursor`).
    def ReplaySafetyInv (s : ReplayState) : Prop :=
      Nat.le (UInt64.toNat s.cursor) (UInt64.toNat s.tapeLen) ∧
      s.matchedPrefix = s.cursor

    def Init (n : UInt64) (s : ReplayState) : Prop :=
      s.cursor = 0 ∧
      s.tapeLen = n ∧
      s.status = 0 ∧
      s.matchedPrefix = 0

    -- Action 1: PopMatching — consume matching effects through `nextCur <= tapeLen`
    -- via Clean-origin `_root_.replay_cursor_monotone`.
    def PopMatching (nextCur : UInt64) (reqKind tapeKind reqPath tapePath : Nat) (s sNext : ReplayState) : Prop :=
      s.status = 0 ∧
      Nat.le (UInt64.toNat nextCur) (UInt64.toNat s.tapeLen) ∧
      reqKind = tapeKind ∧
      reqPath = tapePath ∧
      sNext.cursor = _root_.replay_cursor_monotone s.cursor nextCur ∧
      sNext.tapeLen = s.tapeLen ∧
      sNext.status = 0 ∧
      sNext.matchedPrefix = _root_.replay_cursor_monotone s.matchedPrefix nextCur

    -- Action 2: RefuseExhausted — fail closed when `cursor = tapeLen`.
    def RefuseExhausted (s sNext : ReplayState) : Prop :=
      s.status = 0 ∧
      s.cursor = s.tapeLen ∧
      sNext.cursor = s.cursor ∧
      sNext.tapeLen = s.tapeLen ∧
      sNext.status = 1 ∧
      sNext.matchedPrefix = s.matchedPrefix

    -- Action 3: RefuseMismatch — fail closed on kind or path divergence without advancing `cursor`.
    def RefuseMismatch (s sNext : ReplayState) : Prop :=
      s.status = 0 ∧
      Nat.lt (UInt64.toNat s.cursor) (UInt64.toNat s.tapeLen) ∧
      sNext.cursor = s.cursor ∧
      sNext.tapeLen = s.tapeLen ∧
      sNext.status = 1 ∧
      sNext.matchedPrefix = s.matchedPrefix

    def Next (s sNext : ReplayState) : Prop :=
      (∃ nc : UInt64, ∃ rk : Nat, ∃ tk : Nat, ∃ rp : Nat, ∃ tp : Nat, PopMatching nc rk tk rp tp s sNext) ∨
        (RefuseExhausted s sNext ∨ RefuseMismatch s sNext)

    def Spec (n : UInt64) : StateMachine ReplayState :=
      StateMachine.mk (Init n) Next

    theorem init_establishes_inv (n : UInt64) (s : ReplayState)
        (hInit : Init n s) : ReplaySafetyInv s :=
      let hLe0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.tapeLen) :=
        Nat.zero_le (UInt64.toNat s.tapeLen)
      let hLeCursor : Nat.le (UInt64.toNat s.cursor) (UInt64.toNat s.tapeLen) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.tapeLen)) hInit.1) hLe0
      let hMatch : s.matchedPrefix = s.cursor :=
        Eq.trans hInit.2.2.2 (Eq.symm hInit.1)
      And.intro hLeCursor hMatch

    theorem popMatching_preserves_inv (nc : UInt64) (rk tk rp tp : Nat) (s sNext : ReplayState)
        (hInv : ReplaySafetyInv s) (hAct : PopMatching nc rk tk rp tp s sNext) :
        ReplaySafetyInv sNext :=
      let hNextLe : Nat.le (UInt64.toNat nc) (UInt64.toNat s.tapeLen) := hAct.2.1
      let hCur : sNext.cursor = _root_.replay_cursor_monotone s.cursor nc := hAct.2.2.2.2.1
      let hTape : sNext.tapeLen = s.tapeLen := hAct.2.2.2.2.2.1
      let hMat : sNext.matchedPrefix = _root_.replay_cursor_monotone s.matchedPrefix nc := hAct.2.2.2.2.2.2.2
      let hLub : Nat.le (UInt64.toNat (_root_.replay_cursor_monotone s.cursor nc)) (UInt64.toNat s.tapeLen) :=
        replay_cursor_lub s.cursor nc s.tapeLen hInv.1 hNextLe
      let hLe1 : Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat s.tapeLen) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.tapeLen)) hCur) hLub
      let hLeNext : Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat sNext.tapeLen) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat y)) hTape) hLe1
      let hMonoEq : _root_.replay_cursor_monotone s.matchedPrefix nc = _root_.replay_cursor_monotone s.cursor nc :=
        congrArg (fun x => _root_.replay_cursor_monotone x nc) hInv.2
      let hMatNext : sNext.matchedPrefix = sNext.cursor :=
        Eq.trans hMat (Eq.trans hMonoEq (Eq.symm hCur))
      And.intro hLeNext hMatNext

    theorem refuseExhausted_preserves_inv (s sNext : ReplayState)
        (hInv : ReplaySafetyInv s) (hAct : RefuseExhausted s sNext) :
        ReplaySafetyInv sNext :=
      let hCur : sNext.cursor = s.cursor := hAct.2.2.1
      let hTape : sNext.tapeLen = s.tapeLen := hAct.2.2.2.1
      let hMat : sNext.matchedPrefix = s.matchedPrefix := hAct.2.2.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat s.tapeLen) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.tapeLen)) hCur) hInv.1
      let hLeNext : Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat sNext.tapeLen) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat y)) hTape) hLe1
      let hMatNext : sNext.matchedPrefix = sNext.cursor :=
        Eq.trans hMat (Eq.trans hInv.2 (Eq.symm hCur))
      And.intro hLeNext hMatNext

    theorem refuseMismatch_preserves_inv (s sNext : ReplayState)
        (hInv : ReplaySafetyInv s) (hAct : RefuseMismatch s sNext) :
        ReplaySafetyInv sNext :=
      let hCur : sNext.cursor = s.cursor := hAct.2.2.1
      let hTape : sNext.tapeLen = s.tapeLen := hAct.2.2.2.1
      let hMat : sNext.matchedPrefix = s.matchedPrefix := hAct.2.2.2.2.2
      let hLe1 : Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat s.tapeLen) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.tapeLen)) hCur) hInv.1
      let hLeNext : Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat sNext.tapeLen) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.cursor) (UInt64.toNat y)) hTape) hLe1
      let hMatNext : sNext.matchedPrefix = sNext.cursor :=
        Eq.trans hMat (Eq.trans hInv.2 (Eq.symm hCur))
      And.intro hLeNext hMatNext

    theorem next_preserves_inv (s sNext : ReplayState)
        (hInv : ReplaySafetyInv s) (hNext : Next s sNext) :
        ReplaySafetyInv sNext :=
      Or.elim hNext
        (fun hEx0 =>
          Exists.elim hEx0 (fun nc hEx1 =>
            Exists.elim hEx1 (fun rk hEx2 =>
              Exists.elim hEx2 (fun tk hEx3 =>
                Exists.elim hEx3 (fun rp hEx4 =>
                  Exists.elim hEx4 (fun tp hPop =>
                    popMatching_preserves_inv nc rk tk rp tp s sNext hInv hPop))))))
        (fun hRest =>
          Or.elim hRest
            (fun hExh => refuseExhausted_preserves_inv s sNext hInv hExh)
            (fun hMis => refuseMismatch_preserves_inv s sNext hInv hMis))

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec n) ⊨ □ (Lift ReplaySafetyInv)`
    theorem spec_satisfies_replay_safety (n : UInt64) :
        (Spec n) ⊨ □ (Lift ReplaySafetyInv) :=
      invariantSatisfies (Spec n) ReplaySafetyInv
        (init_establishes_inv n)
        next_preserves_inv

    end TlaDeterministicReplay
    end Effects
    end Astream

    def replay_cursor_in_bounds_isl (cursor : UInt64) (tape_len : UInt64) : Bool :=
      decide (cursor < tape_len)
}
