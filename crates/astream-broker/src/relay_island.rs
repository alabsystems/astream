// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for the origin-keyed relay (`relay_floor.rs`, `broker.relay`), mounted under
// `cfg(clean_islands)`. It models one origin's key on one subject of one broker, on the `Relay` verb,
// through arrivals over any bridge, retention cuts of that key and of the subject's other keys, and
// replays: however they interleave, the broker appends the key at most once. The law rests on the
// guard (a record is appended only when its key is not held and `relay_floor_admits` lets it pass)
// and on a cut raising the floor to at least the key it drops. Drop the raise and a replay after a
// cut appends again. Out of the model: `Publish`, which reads no floor, and the same sequence sealed
// on two subjects, which breaks the origin's own contract. The code holds its end by refusing a
// relayed sequence in the ack half, which no floor covers, and by marking an origin durably, so that
// every cut of its keys carries a floor.
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    -- ========================================================================
    def relay_floor_raise (floor : UInt64) (seq : UInt64) : UInt64 :=
      if floor < seq then seq else floor

    def relay_floor_admits (floor : UInt64) (seq : UInt64) : UInt64 :=
      if floor < seq then 1 else 0

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaOriginRelay)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaOriginRelay

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaOriginRelay.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaOriginRelay.Always

    theorem invariantAt {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext)
        (b : Behavior State) (runs : Runs M b) :
        ∀ n, I (b n) :=
      fun n => Nat.rec (motive := fun k => I (b k))
        (hInit (b 0) runs.1)
        (fun k ih => Or.elim (runs.2 k)
          (fun hNext => hStep (b k) (b (Nat.succ k)) ih hNext)
          (fun hEq => Eq.mpr (congrArg I hEq) ih))
        n

    theorem invariantSatisfies {State : Type} (M : StateMachine State) (I : State → Prop)
        (hInit : ∀ s : State, M.init s → I s)
        (hStep : ∀ s sNext : State, I s → M.next s sNext → I sNext) :
        M ⊨ □ (Lift I) :=
      fun b runs n => invariantAt M I hInit hStep b runs n

    -- One key `seq` on one broker. `held`: its dedup key is held. `floor`: the relay floor of its
    -- origin and subject. `appended`: how many times the broker has appended it.
    structure RelayState where
      seq      : UInt64
      held     : Bool
      floor    : UInt64
      appended : Nat

    -- Once appended, the key answers for itself: its dedup key is held, or a floor has passed it.
    def Answers (s : RelayState) : Prop :=
      s.held = true ∨ Nat.le (UInt64.toNat s.seq) (UInt64.toNat s.floor)

    def RelayInv (s : RelayState) : Prop :=
      s.appended = 0 ∨ (s.appended = 1 ∧ Answers s)

    def Init (s : RelayState) : Prop :=
      s.appended = 0

    -- A relayed copy arrives, over any bridge, and the broker appends it.
    def arriveAction (s sNext : RelayState) : Prop :=
      s.held = false ∧
      _root_.relay_floor_admits s.floor s.seq = 1 ∧
      sNext.seq = s.seq ∧ sNext.held = true ∧ sNext.floor = s.floor ∧
      sNext.appended = Nat.succ s.appended

    -- A retention cut drops the key and raises the floor past it.
    def cutAction (s sNext : RelayState) : Prop :=
      sNext.seq = s.seq ∧ sNext.held = false ∧
      sNext.floor = _root_.relay_floor_raise s.floor s.seq ∧
      sNext.appended = s.appended

    -- A cut reaches another key of the subject.
    def cutOtherAction (other : UInt64) (s sNext : RelayState) : Prop :=
      sNext.seq = s.seq ∧ sNext.held = s.held ∧
      sNext.floor = _root_.relay_floor_raise s.floor other ∧
      sNext.appended = s.appended

    -- A duplicate or a replay answers and changes nothing, which `Runs` allows as a stutter.
    def Next (s sNext : RelayState) : Prop :=
      arriveAction s sNext ∨ cutAction s sNext ∨
        ∃ other : UInt64, cutOtherAction other s sNext

    def Spec : StateMachine RelayState :=
      StateMachine.mk Init Next

    theorem raise_ge_floor : forall (floor : UInt64) (seq : UInt64),
        Nat.le (UInt64.toNat floor) (UInt64.toNat (_root_.relay_floor_raise floor seq)) :=
      fun floor seq => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt floor seq)) =>
          Nat.le (UInt64.toNat floor) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => floor) (fun _ => seq))))
        (instDecidableUInt64Lt floor seq)
        (fun _ => Nat.le.refl (UInt64.toNat floor))
        (fun hLt => Nat.le_of_lt hLt)

    theorem raise_ge_seq : forall (floor : UInt64) (seq : UInt64),
        Nat.le (UInt64.toNat seq) (UInt64.toNat (_root_.relay_floor_raise floor seq)) :=
      fun floor seq => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt floor seq)) =>
          Nat.le (UInt64.toNat seq) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => floor) (fun _ => seq))))
        (instDecidableUInt64Lt floor seq)
        (fun hNotLt => Nat.le_of_not_lt hNotLt)
        (fun _ => Nat.le.refl (UInt64.toNat seq))

    theorem bool_true_is_not_false (h : true = false) : False :=
      absurd h (by decide)

    theorem zero_is_not_one (h : (0 : UInt64) = 1) : False :=
      absurd h (by decide)

    -- A floor at or past the key refuses it.
    theorem passed_is_not_admitted (floor seq : UInt64)
        (hLe : Nat.le (UInt64.toNat seq) (UInt64.toNat floor))
        (hAdmits : _root_.relay_floor_admits floor seq = 1) : False :=
      Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt floor seq)) =>
          (Decidable.casesOn (motive := fun _ => UInt64) d (fun _ => 0) (fun _ => 1)) = 1 → False)
        (instDecidableUInt64Lt floor seq)
        (fun _ hZero => zero_is_not_one hZero)
        (fun hLt _ => Nat.lt_irrefl (UInt64.toNat floor) (Nat.le_trans hLt hLe))
        hAdmits

    theorem init_establishes_inv (s : RelayState) (hInit : Init s) : RelayInv s :=
      Or.inl hInit

    -- An arrival that was appended cannot follow an append: its key would answer.
    theorem arrive_needs_no_answer (s sNext : RelayState)
        (hArrive : arriveAction s sNext) (hAnswers : Answers s) : False :=
      Or.elim hAnswers
        (fun hHeld => bool_true_is_not_false (Eq.trans (Eq.symm hHeld) (And.left hArrive)))
        (fun hLe => passed_is_not_admitted s.floor s.seq hLe (And.left (And.right hArrive)))

    theorem arrive_preserves_inv (s sNext : RelayState)
        (hInv : RelayInv s) (hArrive : arriveAction s sNext) : RelayInv sNext :=
      Or.elim hInv
        (fun hZero =>
          Or.inr (And.intro
            (Eq.trans hArrive.2.2.2.2.2 (congrArg Nat.succ hZero))
            (Or.inl hArrive.2.2.2.1)))
        (fun hOne => False.elim (arrive_needs_no_answer s sNext hArrive (And.right hOne)))

    theorem cut_preserves_inv (s sNext : RelayState)
        (hInv : RelayInv s) (hCut : cutAction s sNext) : RelayInv sNext :=
      Or.elim hInv
        (fun hZero => Or.inl (Eq.trans hCut.2.2.2 hZero))
        (fun hOne => Or.inr (And.intro
          (Eq.trans hCut.2.2.2 (And.left hOne))
          (Or.inr
            (Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.floor)) hCut.1)
              (Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat s.seq) (UInt64.toNat x)) hCut.2.2.1)
                (raise_ge_seq s.floor s.seq))))))

    theorem cutOther_keeps_answer (other : UInt64) (s sNext : RelayState)
        (hAct : cutOtherAction other s sNext) (hAnswers : Answers s) : Answers sNext :=
      Or.elim hAnswers
        (fun hHeld => Or.inl (Eq.trans hAct.2.1 hHeld))
        (fun hLe => Or.inr
          (Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat sNext.floor)) hAct.1)
            (Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat s.seq) (UInt64.toNat x)) hAct.2.2.1)
              (Nat.le_trans hLe (raise_ge_floor s.floor other)))))

    theorem cutOther_preserves_inv (other : UInt64) (s sNext : RelayState)
        (hInv : RelayInv s) (hAct : cutOtherAction other s sNext) : RelayInv sNext :=
      Or.elim hInv
        (fun hZero => Or.inl (Eq.trans hAct.2.2.2 hZero))
        (fun hOne => Or.inr (And.intro
          (Eq.trans hAct.2.2.2 (And.left hOne))
          (cutOther_keeps_answer other s sNext hAct (And.right hOne))))

    theorem next_preserves_inv (s sNext : RelayState)
        (hInv : RelayInv s) (hNext : Next s sNext) : RelayInv sNext :=
      Or.elim hNext
        (fun hArrive => arrive_preserves_inv s sNext hInv hArrive)
        (fun hRest =>
          Or.elim hRest
            (fun hCut => cut_preserves_inv s sNext hInv hCut)
            (fun hEx => Exists.elim hEx (fun other hAct =>
              cutOther_preserves_inv other s sNext hInv hAct)))

    -- The law: however arrivals, cuts and replays interleave, a key is appended at most once.
    theorem appended_at_most_once (s : RelayState) (hInv : RelayInv s) :
        Nat.le s.appended 1 :=
      Or.elim hInv
        (fun hZero => Eq.mpr (congrArg (fun x => Nat.le x 1) hZero) (Nat.zero_le 1))
        (fun hOne => Eq.mpr (congrArg (fun x => Nat.le x 1) hOne.1) (Nat.le.refl 1))

    theorem spec_satisfies_origin_relay_safety :
        Spec ⊨ □ (Lift RelayInv) :=
      invariantSatisfies Spec RelayInv init_establishes_inv next_preserves_inv

    end TlaOriginRelay
    end Broker
    end Astream
}
