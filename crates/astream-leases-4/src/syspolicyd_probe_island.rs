// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for macOS `syspolicyd=stuck` deadlock classification
// (`Astream.Host.TlaSyspolicydProbe`), mounted under `cfg(clean_islands)` in
// `syspolicyd_probe.rs` (`aterm ctl @self status` `syspolicyd=stuck` -> `NEEDS YOU: restart the Mac`).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def syspolicy_probe_hang_clamp (streak : UInt64) (cap : UInt64) : UInt64 :=
      if streak < cap then streak else cap

    def syspolicy_probe_stuck_latch (cur_stuck : UInt64) (cand_stuck : UInt64) : UInt64 :=
      if cur_stuck < cand_stuck then cand_stuck else cur_stuck

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Host.TlaSyspolicydProbe)
    -- ========================================================================
    namespace Astream
    namespace Host
    namespace TlaSyspolicydProbe

    def Behavior (State : Type) : Type := Nat → State
    def Formula (State : Type) : Type := Behavior State → Prop
    def drop {State : Type} (n : Nat) (b : Behavior State) : Behavior State :=
      fun (k : Nat) => b (Nat.add n k)
    def Always {State : Type} (P : Formula State) : Formula State :=
      fun (b : Behavior State) => ∀ (n : Nat), P (drop n b)

    structure StateMachine (State : Type) where
      Init : State → Prop
      Next : State → State → Prop

    def Runs {State : Type} (M : StateMachine State) : Formula State :=
      fun (b : Behavior State) =>
        And (M.Init (b 0)) (∀ (n : Nat), M.Next (b n) (b (Nat.add n 1)))

    def Lift {State : Type} (pred : State → Prop) : Formula State :=
      fun (b : Behavior State) => pred (b 0)

    def Satisfies {State : Type} (P : Formula State) (Q : Formula State) : Prop :=
      ∀ (b : Behavior State), P b → Q b

    theorem invariantAt
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s')
      (b : Behavior State)
      (hRun : Runs M b)
      (k : Nat) :
      Inv (b k) :=
      Nat.rec
        (hInit (b 0) (And.left hRun))
        (fun (j : Nat) (ih : Inv (b j)) =>
          hStep (b j) (b (Nat.add j 1)) ih (And.right hRun j))
        k

    theorem invariantSatisfies
      {State : Type}
      (M : StateMachine State)
      (Inv : State → Prop)
      (hInit : ∀ (s : State), M.Init s → Inv s)
      (hStep : ∀ (s : State) (s' : State), Inv s → M.Next s s' → Inv s') :
      Satisfies (Runs M) (Always (Lift Inv)) :=
      fun (b : Behavior State) (hRun : Runs M b) (k : Nat) =>
        Eq.mpr
          (congrArg (fun (idx : Nat) => Inv (b idx)) (Nat.add_zero k))
          (invariantAt M Inv hInit hStep b hRun k)

    theorem hang_clamp_le_cap : forall (streak : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.syspolicy_probe_hang_clamp streak cap)) (UInt64.toNat cap) :=
      fun streak cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt streak cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => streak))) (UInt64.toNat cap))
        (instDecidableUInt64Lt streak cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem latch_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.syspolicy_probe_stuck_latch cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => @Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (@Nat.le.refl (UInt64.toNat b))

    structure SyspolicyState where
      hangStreak : UInt64
      maxCap : UInt64
      prevStuck : UInt64
      stuck : UInt64

    def SyspolicySafetyInv (s : SyspolicyState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.hangStreak) (UInt64.toNat s.maxCap))
        (Nat.le (UInt64.toNat s.prevStuck) (UInt64.toNat s.stuck))

    def Init (s : SyspolicyState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.hangStreak) (UInt64.toNat s.maxCap))
        (s.prevStuck = s.stuck)

    def observeStep (rs : UInt64) (cs : UInt64) (s : SyspolicyState) : SyspolicyState :=
      SyspolicyState.mk
        (_root_.syspolicy_probe_hang_clamp rs s.maxCap)
        s.maxCap
        s.stuck
        (_root_.syspolicy_probe_stuck_latch s.stuck cs)

    def Next (s : SyspolicyState) (s' : SyspolicyState) : Prop :=
      ∃ (rs : UInt64), ∃ (cs : UInt64), s' = observeStep rs cs s

    def Spec : StateMachine SyspolicyState :=
      StateMachine.mk Init Next

    theorem init_establishes_inv (s : SyspolicyState) (hInit : Init s) :
      SyspolicySafetyInv s :=
      And.intro
        (And.left hInit)
        (uint64_eq_le s.prevStuck s.stuck (And.right hInit))

    theorem next_preserves_inv (s : SyspolicyState) (s' : SyspolicyState)
      (_hInv : SyspolicySafetyInv s) (hNext : Next s s') :
      SyspolicySafetyInv s' :=
      Exists.elim hNext (fun (rs : UInt64) (hRest : ∃ (cs : UInt64), s' = observeStep rs cs s) =>
        Exists.elim hRest (fun (cs : UInt64) (hEq : s' = observeStep rs cs s) =>
          Eq.mpr
            (congrArg (fun (st : SyspolicyState) => SyspolicySafetyInv st) hEq)
            (And.intro
              (hang_clamp_le_cap rs s.maxCap)
              (latch_ge_cur s.stuck cs))))

    theorem spec_satisfies_syspolicyd_probe_safety :
      Satisfies (Runs Spec) (Always (Lift SyspolicySafetyInv)) :=
      invariantSatisfies Spec SyspolicySafetyInv init_establishes_inv next_preserves_inv

    end TlaSyspolicydProbe
    end Host
    end Astream

    def syspolicy_probe_is_stuck_isl (stuck_flag : UInt64) : Bool :=
      decide (stuck_flag = 1)
}
