// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `dag.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `dag.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Function (`clean_origin_mir` I5)
    -- ========================================================================

    -- Monotone step-DAG committed-node counter (`max(cur_committed, next_committed)`).
    def dag_committed_advance (cur_committed : UInt64) (next_committed : UInt64) : UInt64 :=
      if cur_committed < next_committed then next_committed else cur_committed

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Engine.TlaDurableDag)
    -- ========================================================================
    namespace Astream
    namespace Engine
    namespace TlaDurableDag

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop

    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun k => b (Nat.add n k)

    def Always {State : Type} (P : Formula State) : Formula State :=
      fun b => ∀ n : Nat, P (drop n b)
    prefix:90 "□" => _root_.Astream.Engine.TlaDurableDag.Always

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun b => M.Init (b 0) ∧ ∀ n : Nat, M.Next (b n) (b (Nat.succ n))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun b => pred (b 0)

    def Satisfies {State : Type} (M : StateMachine State) (P : Formula State) : Prop :=
      ∀ b : Behavior State, Runs M b → P b
    infix:50 " ⊨ " => _root_.Astream.Engine.TlaDurableDag.Satisfies

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

    theorem dag_committed_lub (cur req bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hReq : Nat.le (UInt64.toNat req) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.dag_committed_advance cur req)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur req)
        (fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur req) d req cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur req)
        (fun _ => hCur)
        (fun _ => hReq)

    -- ========================================================================
    -- 3. TLA+ Specification of Crash-Resumable Topological Step-DAG Execution
    -- ========================================================================
    structure DagState where
      committedNodes : UInt64
      totalNodes     : UInt64
      hasTornTail    : Nat

    def DagTopologicalSafetyInv (s : DagState) : Prop :=
      Nat.le (UInt64.toNat s.committedNodes) (UInt64.toNat s.totalNodes) ∧
      (s.hasTornTail = 0 ∨ s.hasTornTail = 1)

    def Init (total : UInt64) (s : DagState) : Prop :=
      s.committedNodes = 0 ∧ s.totalNodes = total ∧ s.hasTornTail = 0

    -- Action 1: Execute and fsync a ready DAG node whose dependencies are all committed.
    def CommitReadyNode (nextNodes : UInt64) (s sNext : DagState) : Prop :=
      s.hasTornTail = 0 ∧
      Nat.le (UInt64.toNat nextNodes) (UInt64.toNat s.totalNodes) ∧
      sNext.committedNodes = _root_.dag_committed_advance s.committedNodes nextNodes ∧
      sNext.totalNodes = s.totalNodes ∧
      sNext.hasTornTail = 0

    -- Action 2: Process crashes mid-node (leaving a torn frame after `committedNodes`).
    def CrashMidNode (s sNext : DagState) : Prop :=
      s.hasTornTail = 0 ∧
      LT.lt s.committedNodes s.totalNodes ∧
      sNext.committedNodes = s.committedNodes ∧
      sNext.totalNodes = s.totalNodes ∧
      sNext.hasTornTail = 1

    -- Action 3: Reopen truncates the torn tail back to the committed DAG prefix.
    def RecoverTruncateTornTail (s sNext : DagState) : Prop :=
      s.hasTornTail = 1 ∧
      sNext.committedNodes = s.committedNodes ∧
      sNext.totalNodes = s.totalNodes ∧
      sNext.hasTornTail = 0

    def Next (s sNext : DagState) : Prop :=
      (∃ nn : UInt64, CommitReadyNode nn s sNext) ∨
        (CrashMidNode s sNext ∨ RecoverTruncateTornTail s sNext)

    def Spec (total : UInt64) : StateMachine DagState :=
      StateMachine.mk (Init total) Next

    theorem init_establishes_inv (total : UInt64) (s : DagState)
        (hInit : Init total s) : DagTopologicalSafetyInv s :=
      let h0 : Nat.le (UInt64.toNat 0) (UInt64.toNat s.totalNodes) :=
        Nat.zero_le (UInt64.toNat s.totalNodes)
      let hLe : Nat.le (UInt64.toNat s.committedNodes) (UInt64.toNat s.totalNodes) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalNodes)) hInit.1) h0
      And.intro hLe (Or.inl hInit.2.2)

    theorem commitNode_preserves_inv (nn : UInt64) (s sNext : DagState)
        (hInv : DagTopologicalSafetyInv s) (hAct : CommitReadyNode nn s sNext) :
        DagTopologicalSafetyInv sNext :=
      let hNnLe : Nat.le (UInt64.toNat nn) (UInt64.toNat s.totalNodes) := hAct.2.1
      let hLub : Nat.le (UInt64.toNat (_root_.dag_committed_advance s.committedNodes nn)) (UInt64.toNat s.totalNodes) :=
        dag_committed_lub s.committedNodes nn s.totalNodes hInv.1 hNnLe
      let hLe1 : Nat.le (UInt64.toNat sNext.committedNodes) (UInt64.toNat s.totalNodes) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalNodes)) hAct.2.2.1) hLub
      let hLe2 : Nat.le (UInt64.toNat sNext.committedNodes) (UInt64.toNat sNext.totalNodes) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedNodes) (UInt64.toNat y)) hAct.2.2.2.1) hLe1
      And.intro hLe2 (Or.inl hAct.2.2.2.2)

    theorem crashMidNode_preserves_inv (s sNext : DagState)
        (hInv : DagTopologicalSafetyInv s) (hAct : CrashMidNode s sNext) :
        DagTopologicalSafetyInv sNext :=
      let hLe1 : Nat.le (UInt64.toNat sNext.committedNodes) (UInt64.toNat s.totalNodes) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalNodes)) hAct.2.2.1) hInv.1
      let hLe2 : Nat.le (UInt64.toNat sNext.committedNodes) (UInt64.toNat sNext.totalNodes) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedNodes) (UInt64.toNat y)) hAct.2.2.2.1) hLe1
      And.intro hLe2 (Or.inr hAct.2.2.2.2)

    theorem recoverTruncate_preserves_inv (s sNext : DagState)
        (hInv : DagTopologicalSafetyInv s) (hAct : RecoverTruncateTornTail s sNext) :
        DagTopologicalSafetyInv sNext :=
      let hLe1 : Nat.le (UInt64.toNat sNext.committedNodes) (UInt64.toNat s.totalNodes) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.totalNodes)) hAct.2.1) hInv.1
      let hLe2 : Nat.le (UInt64.toNat sNext.committedNodes) (UInt64.toNat sNext.totalNodes) :=
        Eq.mpr (congrArg (fun y => Nat.le (UInt64.toNat sNext.committedNodes) (UInt64.toNat y)) hAct.2.2.1) hLe1
      And.intro hLe2 (Or.inl hAct.2.2.2)

    theorem next_preserves_inv (s sNext : DagState)
        (hInv : DagTopologicalSafetyInv s) (hNext : Next s sNext) :
        DagTopologicalSafetyInv sNext :=
      Or.elim hNext
        (fun hEx =>
          Exists.elim hEx (fun nn hCom =>
            commitNode_preserves_inv nn s sNext hInv hCom))
        (fun hRest =>
          Or.elim hRest
            (fun hCrash => crashMidNode_preserves_inv s sNext hInv hCrash)
            (fun hRec => recoverTruncate_preserves_inv s sNext hInv hRec))

    theorem spec_satisfies_dag_topological_safety (total : UInt64) :
        (Spec total) ⊨ □ (Lift DagTopologicalSafetyInv) :=
      invariantSatisfies (Spec total) DagTopologicalSafetyInv
        (init_establishes_inv total)
        next_preserves_inv

    end TlaDurableDag
    end Engine
    end Astream

    -- ========================================================================
    -- 4. Two-Language Rust ↔ Clean Kernel-Certified Contract Definitions
    -- ========================================================================

    def dag_deps_satisfied_isl (unsatisfied_deps : UInt64) : Bool :=
      decide (unsatisfied_deps = 0)
}
