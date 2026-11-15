// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for selective filter-indexed subscriber tail wakeups (`cost study B4 step 2`),
// mounted under `cfg(clean_islands)` in `broker.rs`. Proves that `tail_wake_head_advance` and
// `tail_skip_clamp` maintain `safeSkip <= visibleHead` and `matchedHead <= visibleHead` across
// both matching and non-matching batches.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    -- ========================================================================
    def tail_wake_head_advance (cur_matched : UInt64) (new_vis : UInt64) : UInt64 :=
      if cur_matched < new_vis then new_vis else cur_matched

    def tail_skip_clamp (cand_skip : UInt64) (vis_head : UInt64) : UInt64 :=
      if cand_skip < vis_head then cand_skip else vis_head

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaTailWake)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaTailWake

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaTailWake.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaTailWake.Always

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
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    structure TailWakeState where
      safeSkip    : UInt64
      matchedHead : UInt64
      visibleHead : UInt64

    def TailWakeInv (s : TailWakeState) : Prop :=
      Nat.le (UInt64.toNat s.safeSkip) (UInt64.toNat s.visibleHead) ∧
      Nat.le (UInt64.toNat s.matchedHead) (UInt64.toNat s.visibleHead)

    def Init (s : TailWakeState) : Prop :=
      s.safeSkip = s.visibleHead ∧ s.matchedHead = s.visibleHead

    def publishBatchAction (candSkip : UInt64) (newVis : UInt64) (matched : Bool)
        (s sNext : TailWakeState) : Prop :=
      let visNext := _root_.tail_wake_head_advance s.visibleHead newVis
      sNext.visibleHead = visNext ∧
      sNext.safeSkip = _root_.tail_skip_clamp candSkip visNext ∧
      sNext.matchedHead =
        (if matched = true then _root_.tail_wake_head_advance s.matchedHead visNext else s.matchedHead)

    def Next (s sNext : TailWakeState) : Prop :=
      ∃ candSkip : UInt64, ∃ newVis : UInt64, ∃ matched : Bool,
        publishBatchAction candSkip newVis matched s sNext

    def Spec : StateMachine TailWakeState :=
      StateMachine.mk Init Next

    theorem head_advance_ge_left : forall (a : UInt64) (b : UInt64),
        Nat.le (UInt64.toNat a) (UInt64.toNat (_root_.tail_wake_head_advance a b)) :=
      fun a b => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt a b)) =>
          Nat.le (UInt64.toNat a) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => a) (fun _ => b))))
        (instDecidableUInt64Lt a b)
        (fun _ => Nat.le.refl (UInt64.toNat a))
        (fun hLt => Nat.le_of_lt hLt)

    theorem head_advance_le_bound (a b : UInt64)
        (hA : Nat.le (UInt64.toNat a) (UInt64.toNat b)) :
        Nat.le (UInt64.toNat (_root_.tail_wake_head_advance a b)) (UInt64.toNat b) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt a b)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => a) (fun _ => b))) (UInt64.toNat b))
        (instDecidableUInt64Lt a b)
        (fun _ => hA)
        (fun _ => Nat.le.refl (UInt64.toNat b))

    theorem skip_clamp_le_vis : forall (cand : UInt64) (vis : UInt64),
        Nat.le (UInt64.toNat (_root_.tail_skip_clamp cand vis)) (UInt64.toNat vis) :=
      fun cand vis => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cand vis)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => vis) (fun _ => cand))) (UInt64.toNat vis))
        (instDecidableUInt64Lt cand vis)
        (fun _ => Nat.le.refl (UInt64.toNat vis))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem matched_branch_le_vis (curMatched visNext : UInt64)
        (hBound : Nat.le (UInt64.toNat curMatched) (UInt64.toNat visNext))
        (matched : Bool) :
        Nat.le
          (UInt64.toNat (if matched = true then _root_.tail_wake_head_advance curMatched visNext else curMatched))
          (UInt64.toNat visNext) :=
      Decidable.casesOn
        (motive := fun (d : Decidable (matched = true)) =>
          Nat.le
            (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64) d
              (fun _ => curMatched)
              (fun _ => _root_.tail_wake_head_advance curMatched visNext)))
            (UInt64.toNat visNext))
        (instDecidableEqBool matched true)
        (fun _ => hBound)
        (fun _ => head_advance_le_bound curMatched visNext hBound)

    theorem init_establishes_inv (s : TailWakeState) (hInit : Init s) :
        TailWakeInv s :=
      And.intro
        (uint64_eq_le s.safeSkip s.visibleHead hInit.1)
        (uint64_eq_le s.matchedHead s.visibleHead hInit.2)

    theorem next_preserves_inv (s sNext : TailWakeState)
        (hInv : TailWakeInv s) (hNext : Next s sNext) :
        TailWakeInv sNext :=
      Exists.elim hNext (fun candSkip h1 =>
        Exists.elim h1 (fun newVis h2 =>
          Exists.elim h2 (fun matched hAct =>
            let visNext := _root_.tail_wake_head_advance s.visibleHead newVis
            let hEqVis : sNext.visibleHead = visNext := hAct.1
            let hEqSkip : sNext.safeSkip = _root_.tail_skip_clamp candSkip visNext := hAct.2.1
            let hEqMat : sNext.matchedHead =
                (if matched = true then _root_.tail_wake_head_advance s.matchedHead visNext else s.matchedHead) :=
              hAct.2.2
            let hSkipBound : Nat.le (UInt64.toNat (_root_.tail_skip_clamp candSkip visNext)) (UInt64.toNat visNext) :=
              skip_clamp_le_vis candSkip visNext
            let hVisGrow : Nat.le (UInt64.toNat s.visibleHead) (UInt64.toNat visNext) :=
              head_advance_ge_left s.visibleHead newVis
            let hCurBound : Nat.le (UInt64.toNat s.matchedHead) (UInt64.toNat visNext) :=
              Nat.le_trans hInv.2 hVisGrow
            let hMatBound : Nat.le
                (UInt64.toNat (if matched = true then _root_.tail_wake_head_advance s.matchedHead visNext else s.matchedHead))
                (UInt64.toNat visNext) :=
              matched_branch_le_vis s.matchedHead visNext hCurBound matched
            And.intro
              (Eq.mpr
                (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.visibleHead)) hEqSkip)
                (Eq.mpr
                  (congrArg (fun (v : UInt64) => Nat.le (UInt64.toNat (_root_.tail_skip_clamp candSkip visNext)) (UInt64.toNat v)) hEqVis)
                  hSkipBound))
              (Eq.mpr
                (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.visibleHead)) hEqMat)
                (Eq.mpr
                  (congrArg (fun (v : UInt64) => Nat.le
                    (UInt64.toNat (if matched = true then _root_.tail_wake_head_advance s.matchedHead visNext else s.matchedHead))
                    (UInt64.toNat v)) hEqVis)
                  hMatBound)))))

    theorem spec_satisfies_tail_wake_safety :
        Spec ⊨ □ (Lift TailWakeInv) :=
      invariantSatisfies Spec TailWakeInv init_establishes_inv next_preserves_inv

    end TlaTailWake
    end Broker
    end Astream

    def tail_wake_caught_up_isl (matched_head : UInt64) (cursor : UInt64) : Bool :=
      decide (matched_head ≤ cursor)
}
