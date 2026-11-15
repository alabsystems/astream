// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `durable.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `durable.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    --    Compiled directly from this Clean kernel definition into Rust MIR
    --    (`pub const fn journal_committed_monotone`) and verified by `Faithful`.
    -- ========================================================================

    -- Monotone durable workflow step commit (`max(cur_steps, next_steps)`).
    def journal_committed_monotone (cur_steps : UInt64) (next_steps : UInt64) : UInt64 :=
      if cur_steps < next_steps then next_steps else cur_steps

    -- Dense step-sequence gate: admits `next_steps` iff `step_index == cur_steps`.
    def journal_step_match_or_keep (step_index : UInt64) (cur_steps : UInt64) (next_steps : UInt64) : UInt64 :=
      if step_index == cur_steps then next_steps else cur_steps

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaDurableJournal)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaDurableJournal

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun k => b (Nat.add n k)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun b => ∀ n : Nat, P (drop n b)
    prefix:90 "□" => _root_.Astream.Engine.TlaDurableJournal.Always

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun b => M.Init (b 0) ∧ ∀ n : Nat, M.Next (b n) (b (Nat.succ n))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun b => pred (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (P : Formula State) : Prop :=
      ∀ b : Behavior State, Runs M b → P b
    infix:50 " ⊨ " => _root_.Astream.Engine.TlaDurableJournal.Satisfies

    theorem invariantAt {State : Type} (M : StateMachine State) (Inv : State → Prop)
        (hInit : ∀ s : State, M.Init s → Inv s)
        (hStep : ∀ s s' : State, Inv s → M.Next s s' → Inv s')
        (b : Behavior State) (hRun : Runs M b) (n : Nat) : Inv (b n) :=
      Nat.rec
        (motive := fun k => Inv (b k))
        (hInit (b 0) hRun.1)
        (fun k ih => hStep (b k) (b (Nat.succ k)) ih (hRun.2 k))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (Inv : State → Prop)
        (hInit : ∀ s : State, M.Init s → Inv s)
        (hStep : ∀ s s' : State, Inv s → M.Next s s' → Inv s') :
        M ⊨ □ (Lift Inv) :=
      fun b hRun n =>
        let hAt : Inv (b n) := invariantAt M Inv hInit hStep b hRun n
        let hEq : Nat.add n 0 = n := Nat.add_zero n
        Eq.mpr (congrArg (fun idx => Inv (b idx)) hEq) hAt

    theorem journal_committed_lub (cur req bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hReq : Nat.le (UInt64.toNat req) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.journal_committed_monotone cur req)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur req)
        (fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur req) d req cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur req)
        (fun _ => hCur)
        (fun _ => hReq)

    def journal_admit_step_commit_isl (poisoned : UInt64) (cur_steps : UInt64) (step_index : UInt64) (next_steps : UInt64) : UInt64 :=
      if poisoned == 0 then
        _root_.journal_step_match_or_keep step_index cur_steps (_root_.journal_committed_monotone cur_steps next_steps)
      else cur_steps

    theorem journal_admit_step_commit_lub (poisoned cur idx req bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hReq : Nat.le (UInt64.toNat req) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (journal_admit_step_commit_isl poisoned cur idx req)) (UInt64.toNat bound) :=
      @Decidable.casesOn (Eq (BEq.beq poisoned 0) Bool.true)
        (fun (dP : Decidable (Eq (BEq.beq poisoned 0) Bool.true)) =>
          Nat.le
            (UInt64.toNat
              (@ite UInt64 (Eq (BEq.beq poisoned 0) Bool.true) dP
                (_root_.journal_step_match_or_keep idx cur (_root_.journal_committed_monotone cur req))
                cur))
            (UInt64.toNat bound))
        (Bool.decEq (BEq.beq poisoned 0) Bool.true)
        (fun _ => hCur)
        (fun _ =>
          @Decidable.casesOn (Eq (BEq.beq idx cur) Bool.true)
            (fun (dI : Decidable (Eq (BEq.beq idx cur) Bool.true)) =>
              Nat.le
                (UInt64.toNat
                  (@ite UInt64 (Eq (BEq.beq idx cur) Bool.true) dI
                    (_root_.journal_committed_monotone cur req)
                    cur))
                (UInt64.toNat bound))
            (Bool.decEq (BEq.beq idx cur) Bool.true)
            (fun _ => hCur)
            (fun _ => journal_committed_lub cur req bound hCur hReq))

    -- ========================================================================
    -- 3. TLA+ Specification of Crash-Resumable WorkflowJournal & Torn-Tail Recovery
    -- ========================================================================
    structure JournalState where
      committedSteps : UInt64
      totalSteps     : UInt64
      hasTornTail    : Nat

    -- Safety Invariant: the committed step count never exceeds `totalSteps`, and
    -- the journal is either clean (`hasTornTail = 0`) or holds a single uncommitted
    -- torn frame at the tail (`hasTornTail = 1`).
    def JournalPrefixSafetyInv (s : JournalState) : Prop :=
      Nat.le (UInt64.toNat s.committedSteps) (UInt64.toNat s.totalSteps) ∧
      (s.hasTornTail = 0 ∨ s.hasTornTail = 1)

    def Init (total : UInt64) (s : JournalState) : Prop :=
      s.committedSteps = 0 ∧ s.totalSteps = total ∧ s.hasTornTail = 0

    -- Action 1: Execute and fsync the next uncommitted step, advancing `committedSteps`
    -- via Clean-origin `_root_.journal_committed_monotone`.
    def CommitStep (nextSteps : UInt64) (s sNext : JournalState) : Prop :=
      s.hasTornTail = 0 ∧
      Nat.le (UInt64.toNat nextSteps) (UInt64.toNat s.totalSteps) ∧
      sNext.committedSteps = _root_.journal_committed_monotone s.committedSteps nextSteps ∧
      sNext.totalSteps = s.totalSteps ∧
      sNext.hasTornTail = 0

    -- Action 2: Process crashes mid-step (leaving a torn frame after `committedSteps`).
    def CrashMidStep (s sNext : JournalState) : Prop :=
      s.hasTornTail = 0 ∧
      LT.lt s.committedSteps s.totalSteps ∧
      sNext.committedSteps = s.committedSteps ∧
      sNext.totalSteps = s.totalSteps ∧
      sNext.hasTornTail = 1

    -- Action 3: Reopen truncates the torn tail back to the exact committed prefix.
    def RecoverTruncateTornTail (s sNext : JournalState) : Prop :=
      s.hasTornTail = 1 ∧
      sNext.committedSteps = s.committedSteps ∧
      sNext.totalSteps = s.totalSteps ∧
      sNext.hasTornTail = 0

    def Next (s sNext : JournalState) : Prop :=
      (∃ ns : UInt64, CommitStep ns s sNext) ∨
        (CrashMidStep s sNext ∨ RecoverTruncateTornTail s sNext)

    def Spec (total : UInt64) : StateMachine JournalState :=
      StateMachine.mk (Init total) Next

    theorem init_establishes_inv (total : UInt64) (s : JournalState)
        (hInit : Init total s) : JournalPrefixSafetyInv s :=
      let h0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.totalSteps) :=
        Nat.zero_le (UInt64.toNat s.totalSteps)
      let hLe : Nat.le (UInt64.toNat s.committedSteps) (UInt64.toNat s.totalSteps) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalSteps)) hInit.1) h0
      And.intro hLe (Or.inl hInit.2.2)

    theorem commitStep_preserves_inv (ns : UInt64) (s sNext : JournalState)
        (hInv : JournalPrefixSafetyInv s) (hAct : CommitStep ns s sNext) :
        JournalPrefixSafetyInv sNext :=
      let hNsLe : Nat.le (UInt64.toNat ns) (UInt64.toNat s.totalSteps) := hAct.2.1
      let hLub : Nat.le (UInt64.toNat (_root_.journal_committed_monotone s.committedSteps ns)) (UInt64.toNat s.totalSteps) :=
        journal_committed_lub s.committedSteps ns s.totalSteps hInv.1 hNsLe
      let hLe1 : Nat.le (UInt64.toNat sNext.committedSteps) (UInt64.toNat s.totalSteps) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalSteps)) hAct.2.2.1) hLub
      let hLe2 : Nat.le (UInt64.toNat sNext.committedSteps) (UInt64.toNat sNext.totalSteps) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedSteps) (UInt64.toNat y)) hAct.2.2.2.1) hLe1
      And.intro hLe2 (Or.inl hAct.2.2.2.2)

    theorem crashMidStep_preserves_inv (s sNext : JournalState)
        (hInv : JournalPrefixSafetyInv s) (hAct : CrashMidStep s sNext) :
        JournalPrefixSafetyInv sNext :=
      let hLe1 : Nat.le (UInt64.toNat sNext.committedSteps) (UInt64.toNat s.totalSteps) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalSteps)) hAct.2.2.1) hInv.1
      let hLe2 : Nat.le (UInt64.toNat sNext.committedSteps) (UInt64.toNat sNext.totalSteps) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedSteps) (UInt64.toNat y)) hAct.2.2.2.1) hLe1
      And.intro hLe2 (Or.inr hAct.2.2.2.2)

    theorem recoverTruncate_preserves_inv (s sNext : JournalState)
        (hInv : JournalPrefixSafetyInv s) (hAct : RecoverTruncateTornTail s sNext) :
        JournalPrefixSafetyInv sNext :=
      let hLe1 : Nat.le (UInt64.toNat sNext.committedSteps) (UInt64.toNat s.totalSteps) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalSteps)) hAct.2.1) hInv.1
      let hLe2 : Nat.le (UInt64.toNat sNext.committedSteps) (UInt64.toNat sNext.totalSteps) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedSteps) (UInt64.toNat y)) hAct.2.2.1) hLe1
      And.intro hLe2 (Or.inl hAct.2.2.2)

    theorem next_preserves_inv (s sNext : JournalState)
        (hInv : JournalPrefixSafetyInv s) (hNext : Next s sNext) :
        JournalPrefixSafetyInv sNext :=
      Or.elim hNext
        (fun hEx =>
          Exists.elim hEx (fun ns hCom =>
            commitStep_preserves_inv ns s sNext hInv hCom))
        (fun hRest =>
          Or.elim hRest
            (fun hCrash => crashMidStep_preserves_inv s sNext hInv hCrash)
            (fun hRec => recoverTruncate_preserves_inv s sNext hInv hRec))

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec total) ⊨ □ (Lift JournalPrefixSafetyInv)`
    theorem spec_satisfies_journal_prefix_safety (total : UInt64) :
        (Spec total) ⊨ □ (Lift JournalPrefixSafetyInv) :=
      invariantSatisfies (Spec total) JournalPrefixSafetyInv
        (init_establishes_inv total)
        next_preserves_inv

    end TlaDurableJournal
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def step_matches_next_isl (expected_step : UInt64) (found_step : UInt64) : Bool :=
      decide (expected_step = found_step)
}
