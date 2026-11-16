// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `kitty_kbd_stack_fence.rs`, out of line so that only a Trust compiler opens it:
// no stock rustc can lex `clean { ... }`. `kitty_kbd_stack_fence.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
clean {
    -- =======================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- =======================================================================

    def kitty_depth_clamp (candDepth : UInt64) (maxDepth : UInt64) : UInt64 :=
      if candDepth < maxDepth then candDepth else maxDepth
    def kitty_flags_clamp (rawFlags : UInt64) (maxFlags : UInt64) : UInt64 :=
      if rawFlags < maxFlags then rawFlags else maxFlags
    def kitty_epoch_advance (curEpoch : UInt64) (candEpoch : UInt64) : UInt64 :=
      if curEpoch < candEpoch then candEpoch else curEpoch

    -- =======================================================================
    -- 2. TLA+ Behavioral Temporal Logic Framework & Protocol Safety Spec
    -- =======================================================================

    namespace Astream
    namespace Term
    namespace TlaKittyKbdStackFence
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

    structure KittyKbdStackFenceState where
      val_0 : UInt64
      cap_0 : UInt64
      val_1 : UInt64
      cap_1 : UInt64
      cur_2 : UInt64
      prev_2 : UInt64

    def KittyKbdStackFenceInv (s : KittyKbdStackFenceState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.val_0) (UInt64.toNat s.cap_0))
        (And (Nat.le (UInt64.toNat s.val_1) (UInt64.toNat s.cap_1)) (Nat.le (UInt64.toNat s.prev_2) (UInt64.toNat s.cur_2)))

    def Init (s : KittyKbdStackFenceState) : Prop :=
      And
        (s.val_0 = 0)
        (And (s.val_1 = 0) (s.prev_2 = 0))

    def stepTransition (c_0 : UInt64) (c_1 : UInt64) (c_2 : UInt64) (s : KittyKbdStackFenceState) : KittyKbdStackFenceState :=
      KittyKbdStackFenceState.mk
        (_root_.kitty_depth_clamp c_0 s.cap_0)
        s.cap_0
        (_root_.kitty_flags_clamp c_1 s.cap_1)
        s.cap_1
        (_root_.kitty_epoch_advance s.cur_2 c_2)
        s.cur_2

    def Next (s : KittyKbdStackFenceState) (s' : KittyKbdStackFenceState) : Prop :=
      ∃ (c_0 : UInt64), ∃ (c_1 : UInt64), ∃ (c_2 : UInt64),
        s' = stepTransition c_0 c_1 c_2 s

    def Spec : StateMachine KittyKbdStackFenceState :=
      StateMachine.mk Init Next

    theorem helper_bound_0 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kitty_depth_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_1 : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.kitty_flags_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => @Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem helper_bound_2 : forall (prev : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat prev) (UInt64.toNat (_root_.kitty_epoch_advance prev cand)) :=
      fun prev cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt prev cand)) =>
          Nat.le (UInt64.toNat prev) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => prev) (fun _ => cand))))
        (instDecidableUInt64Lt prev cand)
        (fun _ => @Nat.le.refl (UInt64.toNat prev))
        (fun hLt => Nat.le_of_lt hLt)

    theorem zero_le_u64 (a : UInt64) (cap : UInt64) (hZero : a = 0) :
      Nat.le (UInt64.toNat a) (UInt64.toNat cap) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat cap)) hZero)
        (Nat.zero_le (UInt64.toNat cap))

    theorem init_establishes_inv (s : KittyKbdStackFenceState) (hInit : Init s) :
      KittyKbdStackFenceInv s :=
      And.intro
        (zero_le_u64 s.val_0 s.cap_0 (And.left hInit))
        (And.intro
          (zero_le_u64 s.val_1 s.cap_1 (And.left (And.right hInit)))
          (zero_le_u64 s.prev_2 s.cur_2 (And.right (And.right hInit))))

    theorem next_preserves_inv (s : KittyKbdStackFenceState) (s' : KittyKbdStackFenceState)
      (_hInv : KittyKbdStackFenceInv s) (hNext : Next s s') :
      KittyKbdStackFenceInv s' :=
      Exists.elim hNext (fun (c_0 : UInt64) (hR1 : ∃ (c_1 : UInt64), ∃ (c_2 : UInt64), s' = stepTransition c_0 c_1 c_2 s) =>
        Exists.elim hR1 (fun (c_1 : UInt64) (hR2 : ∃ (c_2 : UInt64), s' = stepTransition c_0 c_1 c_2 s) =>
          Exists.elim hR2 (fun (c_2 : UInt64) (hEq : s' = stepTransition c_0 c_1 c_2 s) =>
            Eq.mpr
              (congrArg (fun (st : KittyKbdStackFenceState) => KittyKbdStackFenceInv st) hEq)
              (And.intro
                (helper_bound_0 c_0 s.cap_0)
                (And.intro
                  (helper_bound_1 c_1 s.cap_1)
                  (helper_bound_2 s.cur_2 c_2))))))

    theorem kitty_kbd_stack_fence_safety_always :
      Satisfies Spec (Always (Lift KittyKbdStackFenceInv)) :=
      invariantSatisfies Spec KittyKbdStackFenceInv init_establishes_inv next_preserves_inv

    end TlaKittyKbdStackFence
    end Term
    end Astream
}
