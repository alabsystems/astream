// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for shared volume free-space hysteresis & idle build-cache eviction
// (`Astream.Broker.TlaBuildDiskRoom`), mounted under `cfg(clean_islands)` in
// `disk_room.rs` (`aterm ctl @self status` `disk_free_mb=` & `await sys 'free>=room'`).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` / I5)
    -- ========================================================================

    def room_free_clamp (free_mb : UInt64) (total_mb : UInt64) : UInt64 :=
      if free_mb < total_mb then free_mb else total_mb

    def room_resume_floor (low_mb : UInt64) (resume_mb : UInt64) : UInt64 :=
      if low_mb < resume_mb then resume_mb else low_mb

    -- ========================================================================
    -- 2. TLA+ Temporal Logic & State-Machine Kernel (Astream.Broker.TlaBuildDiskRoom)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaBuildDiskRoom

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

    theorem free_clamp_le_total : forall (f : UInt64) (t : UInt64),
        Nat.le (UInt64.toNat (_root_.room_free_clamp f t)) (UInt64.toNat t) :=
      fun f t => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt f t)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => t) (fun _ => f))) (UInt64.toNat t))
        (instDecidableUInt64Lt f t)
        (fun _ => Nat.le.refl (UInt64.toNat t))
        (fun hLt => Nat.le_of_lt hLt)

    theorem resume_ge_low : forall (low : UInt64) (res : UInt64),
        Nat.le (UInt64.toNat low) (UInt64.toNat (_root_.room_resume_floor low res)) :=
      fun low res => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt low res)) =>
          Nat.le (UInt64.toNat low) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => low) (fun _ => res))))
        (instDecidableUInt64Lt low res)
        (fun _ => Nat.le.refl (UInt64.toNat low))
        (fun hLt => Nat.le_of_lt hLt)

    structure DiskRoomState where
      lowRoomMb : UInt64
      resumeRoomMb : UInt64
      freeMb : UInt64
      totalMb : UInt64

    def DiskRoomSafetyInv (s : DiskRoomState) : Prop :=
      And
        (Nat.le (UInt64.toNat s.lowRoomMb) (UInt64.toNat s.resumeRoomMb))
        (Nat.le (UInt64.toNat s.freeMb) (UInt64.toNat s.totalMb))

    def Init (s : DiskRoomState) : Prop :=
      DiskRoomSafetyInv s

    def sampleStep (rf : UInt64) (s : DiskRoomState) : DiskRoomState :=
      DiskRoomState.mk
        s.lowRoomMb
        (_root_.room_resume_floor s.lowRoomMb s.resumeRoomMb)
        (_root_.room_free_clamp rf s.totalMb)
        s.totalMb

    def Next (s : DiskRoomState) (s' : DiskRoomState) : Prop :=
      ∃ (rf : UInt64), s' = sampleStep rf s

    def Spec : StateMachine DiskRoomState :=
      StateMachine.mk Init Next

    theorem init_establishes_inv (s : DiskRoomState) (hInit : Init s) :
      DiskRoomSafetyInv s :=
      hInit

    theorem next_preserves_inv (s : DiskRoomState) (s' : DiskRoomState)
      (_hInv : DiskRoomSafetyInv s) (hNext : Next s s') :
      DiskRoomSafetyInv s' :=
      Exists.elim hNext (fun (rf : UInt64) (hEq : s' = sampleStep rf s) =>
        Eq.mpr
          (congrArg (fun (st : DiskRoomState) => DiskRoomSafetyInv st) hEq)
          (And.intro
            (resume_ge_low s.lowRoomMb s.resumeRoomMb)
            (free_clamp_le_total rf s.totalMb)))

    theorem spec_satisfies_disk_room_safety :
      Satisfies (Runs Spec) (Always (Lift DiskRoomSafetyInv)) :=
      invariantSatisfies Spec DiskRoomSafetyInv init_establishes_inv next_preserves_inv

    end TlaBuildDiskRoom
    end Broker
    end Astream

    def room_satisfies_floor_isl (free_mb : UInt64) (floor_mb : UInt64) : Bool :=
      decide (floor_mb ≤ free_mb)
}
