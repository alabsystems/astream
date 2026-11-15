// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for fabric peer session status & survey excerpt sanitization
// (`Astream.Host.TlaPeerStatusExcerpt`), mounted under `cfg(clean_islands)` in
// `peer_status.rs` (`aterm ctl ls` / `aterm ctl survey` fabric status rows).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def peer_rev_advance (cur_rev : UInt64) (cand_rev : UInt64) : UInt64 :=
      if cur_rev < cand_rev then cand_rev else cur_rev

    def peer_excerpt_clamp (raw_len : UInt64) (max_cap : UInt64) : UInt64 :=
      if raw_len < max_cap then raw_len else max_cap

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Host.TlaPeerStatusExcerpt)
    -- ========================================================================
    namespace Astream
    namespace Host
    namespace TlaPeerStatusExcerpt

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

    theorem rev_advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.peer_rev_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem excerpt_clamp_le_cap : forall (raw : UInt64) (cap : UInt64),
        Nat.le (UInt64.toNat (_root_.peer_excerpt_clamp raw cap)) (UInt64.toNat cap) :=
      fun raw cap => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt raw cap)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cap) (fun _ => raw))) (UInt64.toNat cap))
        (instDecidableUInt64Lt raw cap)
        (fun _ => Nat.le.refl (UInt64.toNat cap))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a : UInt64) (b : UInt64) (hEq : a = b) :
      Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    structure PeerStatusState where
      prevRev : UInt64
      rev : UInt64
      excerptBytes : UInt64
      maxCap : UInt64

    def PeerStatusSafetyInv (s : PeerStatusState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.prevRev) (UInt64.toNat s.rev))
        (Nat.le (UInt64.toNat s.excerptBytes) (UInt64.toNat s.maxCap))

    def Init (s : PeerStatusState) : Prop :=
      And
        (s.prevRev = s.rev)
        (Nat.le (UInt64.toNat s.excerptBytes) (UInt64.toNat s.maxCap))

    def publishStep (candRev : UInt64) (rawLen : UInt64) (s : PeerStatusState) : PeerStatusState :=
      PeerStatusState.mk
        s.rev
        (_root_.peer_rev_advance s.rev candRev)
        (_root_.peer_excerpt_clamp rawLen s.maxCap)
        s.maxCap

    def Next (s : PeerStatusState) (s' : PeerStatusState) : Prop :=
      ∃ (cr : UInt64), ∃ (rl : UInt64), s' = publishStep cr rl s

    def Spec : StateMachine PeerStatusState :=
      StateMachine.mk Init Next

    theorem init_establishes_inv (s : PeerStatusState) (hInit : Init s) :
      PeerStatusSafetyInv s :=
      And.intro
        (uint64_eq_le s.prevRev s.rev (And.left hInit))
        (And.right hInit)

    theorem next_preserves_inv (s : PeerStatusState) (s' : PeerStatusState)
      (_hInv : PeerStatusSafetyInv s) (hNext : Next s s') :
      PeerStatusSafetyInv s' :=
      Exists.elim hNext (fun (cr : UInt64) (hRest : ∃ (rl : UInt64), s' = publishStep cr rl s) =>
        Exists.elim hRest (fun (rl : UInt64) (hEq : s' = publishStep cr rl s) =>
          Eq.mpr
            (congrArg (fun (st : PeerStatusState) => PeerStatusSafetyInv st) hEq)
            (And.intro
              (rev_advance_ge_cur s.rev cr)
              (excerpt_clamp_le_cap rl s.maxCap))))

    theorem spec_satisfies_peer_status_safety :
      Satisfies (Runs Spec) (Always (Lift PeerStatusSafetyInv)) :=
      invariantSatisfies Spec PeerStatusSafetyInv init_establishes_inv next_preserves_inv

    end TlaPeerStatusExcerpt
    end Host
    end Astream

    def peer_excerpt_within_cap_isl (len : USize) (cap : USize) : Bool :=
      decide (len ≤ cap)
}
