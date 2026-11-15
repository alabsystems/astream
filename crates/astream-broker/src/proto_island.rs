// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island of `proto.rs`, out of line so that only a Trust compiler opens it: no
// stock rustc can lex `clean { ... }`. `proto.rs` mounts this file under
// `cfg(clean_islands)`, which build.rs sets when the compiler answers that it is Trust.
// Every other compiler calls the plain-Rust twins in `twins.rs` of the functions it
// compiles from Clean.
clean {
    -- ========================================================================
    -- 1. TLA+ Temporal Logic, State-Machine & Refinement Kernel (Trust.Temporal)
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

    -- TLA+ Forward Refinement (`f` maps ConcreteState -> AbstractState):
    structure ForwardRefinement {Concrete Abstract : Type}
        (C : StateMachine Concrete) (A : StateMachine Abstract)
        (f : Concrete → Abstract) where
      init_refines : ∀ c : Concrete, C.init c → A.init (f c)
      step_refines : ∀ c cNext : Concrete, C.next c cNext → A.next (f c) (f cNext) ∨ f cNext = f c

    theorem refinementPreservesRuns {Concrete Abstract : Type}
        (C : StateMachine Concrete) (A : StateMachine Abstract)
        (f : Concrete → Abstract)
        (R : ForwardRefinement C A f)
        (b : Behavior Concrete) (runs : Runs C b) :
        Runs A (fun n => f (b n)) :=
      And.intro
        (R.init_refines (b 0) runs.1)
        (fun n =>
          Or.elim (runs.2 n)
            (fun hStep => R.step_refines (b n) (b (Nat.succ n)) hStep)
            (fun hStut => Or.inr (congrArg f hStut)))

    end Temporal
    end Trust

    -- ========================================================================
    -- 2. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    --    Compiled directly from these Clean kernel definitions into Rust MIR
    --    (`pub const fn ...`) and verified by `trust_clean_origin::Faithful`
    --    (`clean-kernel-defeq`). Called directly by `BrokerLog` (`store.rs`),
    --    `broker.rs`, and `CreditWindow` (`client.rs`) — zero duplicate Rust fn
    --    bodies!
    -- ========================================================================

    -- Monotone consumer-group commit cursor advance (`max(cur_upto, req_upto)`).
    def group_commit_monotone (cur_upto : UInt64) (req_upto : UInt64) : UInt64 :=
      if cur_upto < req_upto then req_upto else cur_upto

    -- Monotone producer sequence high-water mark (`max(cur_hw, seq)`).
    def high_water_monotone (cur_hw : UInt64) (seq : UInt64) : UInt64 :=
      if cur_hw < seq then seq else cur_hw

    -- Monotone log compaction base-offset floor (`max(base_off, req_min)`).
    def compact_floor_monotone (req_min : UInt64) (base_off : UInt64) : UInt64 :=
      if base_off < req_min then req_min else base_off

    -- Monotone leader/follower replication epoch advance (`max(cur_epoch, req_epoch)`).
    def epoch_advance_monotone (cur_epoch : UInt64) (req_epoch : UInt64) : UInt64 :=
      if cur_epoch < req_epoch then req_epoch else cur_epoch

    -- Monotone follower replication ack advance (`max(cur_ack, new_ack)`).
    def replica_ack_monotone (cur_ack : UInt64) (new_ack : UInt64) : UInt64 :=
      if cur_ack < new_ack then new_ack else cur_ack

    -- Replicated high-watermark commit frontier (`min(head_offset, replica_ack)`).
    def committed_watermark (head_offset : UInt64) (replica_ack : UInt64) : UInt64 :=
      if head_offset < replica_ack then head_offset else replica_ack

    -- Monotone pipelined flow-control credit horizon (`max(cur_horizon, new_horizon)`).
    def credit_horizon_monotone (cur_horizon : UInt64) (new_horizon : UInt64) : UInt64 :=
      if cur_horizon < new_horizon then new_horizon else cur_horizon

    -- 4-parameter epoch-fenced replication ack selector (`clean_origin_mir` I5):
    -- rejects stale-epoch follower acks (`req_epoch < leader_epoch`) by retaining
    -- `cur_ack`, and otherwise selects `healed_ack`.
    def fenced_ack_select (req_epoch : UInt64) (leader_epoch : UInt64) (cur_ack : UInt64) (healed_ack : UInt64) : UInt64 :=
      if req_epoch < leader_epoch then cur_ack else healed_ack

    -- 4-parameter credit-windowed send gate (`clean_origin_mir` I5):
    -- advances to `clamped_cand` when `sent_seq < credit_horizon`, and otherwise
    -- retains `fallback_sent`.
    def window_gate_send (sent_seq : UInt64) (credit_horizon : UInt64) (clamped_cand : UInt64) (fallback_sent : UInt64) : UInt64 :=
      if sent_seq < credit_horizon then clamped_cand else fallback_sent

    -- ========================================================================
    -- 3. TLA+ Protocol Specification: Broker Exactly-Once Ingest & Dedup
    --    Directly over `_root_.group_commit_monotone`!
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaExactlyOnceIngest

    open Trust.Temporal

    theorem group_commit_ge_cur : forall (cur_upto : UInt64) (req_upto : UInt64),
        Nat.le (UInt64.toNat cur_upto) (UInt64.toNat (_root_.group_commit_monotone cur_upto req_upto)) :=
      fun cur req => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => req))))
        (instDecidableUInt64Lt cur req)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    -- Least-upper-bound property of `_root_.group_commit_monotone`:
    -- if `cur <= bound` and `req <= bound`, then `group_commit_monotone cur req <= bound`.
    theorem group_commit_lub (cur req bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hReq : Nat.le (UInt64.toNat req) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.group_commit_monotone cur req)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur req)
        (fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur req) d req cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur req)
        (fun _ => hCur)
        (fun _ => hReq)

    -- State variables for a `(producer_id, producer_seq)` key and consumer group:
    --   nextOffset    : broker log head (`next_offset`, initially 0)
    --   groupCursor   : committed consumer-group offset (`UInt64`, `<= nextOffset`)
    --   dedupSeen     : 0 before `(producer_id, producer_seq)` is published, 1 after
    --   dedupOffset   : log offset durably assigned to `(producer_id, producer_seq)`
    --   lastAckOffset : offset returned in the most recent `Response::Ack`
    structure IngestState where
      nextOffset    : Nat
      groupCursor   : UInt64
      dedupSeen     : Nat
      dedupOffset   : Nat
      lastAckOffset : Nat

    -- TLA+ Safety Invariant:
    -- 1. The consumer-group cursor never exceeds `nextOffset` (`groupCursor <= nextOffset`).
    -- 2. Once `(producer_id, producer_seq)` has been published (`dedupSeen = 1`),
    --    its assigned offset is strictly below `nextOffset` (`dedupOffset < nextOffset`)
    --    and every ack returns that exact same `dedupOffset` (`lastAckOffset = dedupOffset`).
    def ExactlyOnceInv (s : IngestState) : Prop :=
      Nat.le (UInt64.toNat s.groupCursor) s.nextOffset ∧
      (s.dedupSeen = 1 → (Nat.lt s.dedupOffset s.nextOffset ∧ s.lastAckOffset = s.dedupOffset))

    def Init (s : IngestState) : Prop :=
      s.nextOffset = 0 ∧
      s.groupCursor = 0 ∧
      s.dedupSeen = 0 ∧
      s.dedupOffset = 0 ∧
      s.lastAckOffset = 0

    -- Action 1: PublishFresh — first publish of `(producer_id, producer_seq)`
    -- assigns `dedupOffset' = nextOffset` and advances `nextOffset' = nextOffset + 1`.
    def PublishFresh (s sNext : IngestState) : Prop :=
      s.dedupSeen = 0 ∧
      sNext.nextOffset = Nat.succ s.nextOffset ∧
      sNext.groupCursor = s.groupCursor ∧
      sNext.dedupSeen = 1 ∧
      sNext.dedupOffset = s.nextOffset ∧
      sNext.lastAckOffset = s.nextOffset

    -- Action 2: PublishDuplicate — retry of an already-published `(producer_id, producer_seq)`
    -- returns `lastAckOffset' = dedupOffset` without appending or advancing `nextOffset`.
    def PublishDuplicate (s sNext : IngestState) : Prop :=
      s.dedupSeen = 1 ∧
      sNext.nextOffset = s.nextOffset ∧
      sNext.groupCursor = s.groupCursor ∧
      sNext.dedupSeen = s.dedupSeen ∧
      sNext.dedupOffset = s.dedupOffset ∧
      sNext.lastAckOffset = s.dedupOffset

    -- Action 3: ProcessAndProduceFresh — atomic read-process-write transaction
    -- (`Request::ProcessAndProduce`) that appends output at `nextOffset` AND
    -- advances `groupCursor' = _root_.group_commit_monotone s.groupCursor upto`
    -- in one atomic transition.
    def ProcessAndProduceFresh (upto : UInt64) (s sNext : IngestState) : Prop :=
      s.dedupSeen = 0 ∧
      Nat.le (UInt64.toNat upto) (Nat.succ s.nextOffset) ∧
      sNext.nextOffset = Nat.succ s.nextOffset ∧
      sNext.groupCursor = _root_.group_commit_monotone s.groupCursor upto ∧
      sNext.dedupSeen = 1 ∧
      sNext.dedupOffset = s.nextOffset ∧
      sNext.lastAckOffset = s.nextOffset

    def Next (upto : UInt64) (s sNext : IngestState) : Prop :=
      PublishFresh s sNext ∨
        (PublishDuplicate s sNext ∨ ProcessAndProduceFresh upto s sNext)

    def Spec (upto : UInt64) : StateMachine IngestState :=
      StateMachine.mk Init (Next upto)

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (s : IngestState) (hInit : Init s) :
        ExactlyOnceInv s :=
      let hLe0 : Nat.le (UInt64.toNat 0) s.nextOffset :=
        Eq.mpr (congrArg (Nat.le (UInt64.toNat 0)) hInit.1) (Nat.le_refl 0)
      let hCur : Nat.le (UInt64.toNat s.groupCursor) s.nextOffset :=
        Eq.mpr (congrArg (fun g => Nat.le (UInt64.toNat g) s.nextOffset) hInit.2.1) hLe0
      let hDedup : s.dedupSeen = 1 → (Nat.lt s.dedupOffset s.nextOffset ∧ s.lastAckOffset = s.dedupOffset) :=
        fun hSeen =>
          let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.2.1) hSeen
          False.elim (zero_ne_one h01)
      And.intro hCur hDedup

    theorem publishFresh_preserves_inv (s sNext : IngestState)
        (hInv : ExactlyOnceInv s) (hAct : PublishFresh s sNext) :
        ExactlyOnceInv sNext :=
      let hStep : Nat.le (UInt64.toNat s.groupCursor) (Nat.succ s.nextOffset) :=
        @Nat.le.step (UInt64.toNat s.groupCursor) s.nextOffset hInv.1
      let hCur1 : Nat.le (UInt64.toNat s.groupCursor) sNext.nextOffset :=
        Eq.mpr (congrArg (Nat.le (UInt64.toNat s.groupCursor)) hAct.2.1) hStep
      let hCurNext : Nat.le (UInt64.toNat sNext.groupCursor) sNext.nextOffset :=
        Eq.mpr (congrArg (fun g => Nat.le (UInt64.toNat g) sNext.nextOffset) hAct.2.2.1) hCur1
      let hDedupNext : sNext.dedupSeen = 1 → (Nat.lt sNext.dedupOffset sNext.nextOffset ∧ sNext.lastAckOffset = sNext.dedupOffset) :=
        fun _ =>
          let hLtSelf : Nat.lt s.nextOffset (Nat.succ s.nextOffset) :=
            Nat.le_refl (Nat.succ s.nextOffset)
          let hLt1 : Nat.lt sNext.dedupOffset (Nat.succ s.nextOffset) :=
            Eq.mpr (congrArg (fun d => Nat.lt d (Nat.succ s.nextOffset)) hAct.2.2.2.2.1) hLtSelf
          let hLtNext : Nat.lt sNext.dedupOffset sNext.nextOffset :=
            Eq.mpr (congrArg (Nat.lt sNext.dedupOffset) hAct.2.1) hLt1
          let hEqNext : sNext.lastAckOffset = sNext.dedupOffset :=
            Eq.trans hAct.2.2.2.2.2 (Eq.symm hAct.2.2.2.2.1)
          And.intro hLtNext hEqNext
      And.intro hCurNext hDedupNext

    theorem publishDup_preserves_inv (s sNext : IngestState)
        (hInv : ExactlyOnceInv s) (hAct : PublishDuplicate s sNext) :
        ExactlyOnceInv sNext :=
      let hCur1 : Nat.le (UInt64.toNat s.groupCursor) sNext.nextOffset :=
        Eq.mpr (congrArg (Nat.le (UInt64.toNat s.groupCursor)) hAct.2.1) hInv.1
      let hCurNext : Nat.le (UInt64.toNat sNext.groupCursor) sNext.nextOffset :=
        Eq.mpr (congrArg (fun g => Nat.le (UInt64.toNat g) sNext.nextOffset) hAct.2.2.1) hCur1
      let hDedupNext : sNext.dedupSeen = 1 → (Nat.lt sNext.dedupOffset sNext.nextOffset ∧ sNext.lastAckOffset = sNext.dedupOffset) :=
        fun _ =>
          let hPre := hInv.2 hAct.1
          let hLt1 : Nat.lt sNext.dedupOffset s.nextOffset :=
            Eq.mpr (congrArg (fun d => Nat.lt d s.nextOffset) hAct.2.2.2.2.1) hPre.1
          let hLtNext : Nat.lt sNext.dedupOffset sNext.nextOffset :=
            Eq.mpr (congrArg (Nat.lt sNext.dedupOffset) hAct.2.1) hLt1
          let hEqNext : sNext.lastAckOffset = sNext.dedupOffset :=
            Eq.trans hAct.2.2.2.2.2 (Eq.symm hAct.2.2.2.2.1)
          And.intro hLtNext hEqNext
      And.intro hCurNext hDedupNext

    theorem group_commit_le_nat (cur req : UInt64) (bound : Nat)
        (hCur : Nat.le (UInt64.toNat cur) bound)
        (hReq : Nat.le (UInt64.toNat req) bound) :
        Nat.le (UInt64.toNat (_root_.group_commit_monotone cur req)) bound :=
      @Decidable.casesOn (LT.lt cur req)
        (fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur req) d req cur)) bound)
        (instDecidableUInt64Lt cur req)
        (fun _ => hCur)
        (fun _ => hReq)

    theorem processFresh_preserves_inv (upto : UInt64) (s sNext : IngestState)
        (hInv : ExactlyOnceInv s) (hAct : ProcessAndProduceFresh upto s sNext) :
        ExactlyOnceInv sNext :=
      let hCurStep : Nat.le (UInt64.toNat s.groupCursor) (Nat.succ s.nextOffset) :=
        @Nat.le.step (UInt64.toNat s.groupCursor) s.nextOffset hInv.1
      let hGcLe : Nat.le (UInt64.toNat (_root_.group_commit_monotone s.groupCursor upto)) (Nat.succ s.nextOffset) :=
        group_commit_le_nat s.groupCursor upto (Nat.succ s.nextOffset) hCurStep hAct.2.1
      let hCur1 : Nat.le (UInt64.toNat (_root_.group_commit_monotone s.groupCursor upto)) sNext.nextOffset :=
        Eq.mpr (congrArg (Nat.le (UInt64.toNat (_root_.group_commit_monotone s.groupCursor upto))) hAct.2.2.1) hGcLe
      let hCurNext : Nat.le (UInt64.toNat sNext.groupCursor) sNext.nextOffset :=
        Eq.mpr (congrArg (fun g => Nat.le (UInt64.toNat g) sNext.nextOffset) hAct.2.2.2.1) hCur1
      let hDedupNext : sNext.dedupSeen = 1 → (Nat.lt sNext.dedupOffset sNext.nextOffset ∧ sNext.lastAckOffset = sNext.dedupOffset) :=
        fun _ =>
          let hLtSelf : Nat.lt s.nextOffset (Nat.succ s.nextOffset) :=
            Nat.le_refl (Nat.succ s.nextOffset)
          let hLt1 : Nat.lt sNext.dedupOffset (Nat.succ s.nextOffset) :=
            Eq.mpr (congrArg (fun d => Nat.lt d (Nat.succ s.nextOffset)) hAct.2.2.2.2.2.1) hLtSelf
          let hLtNext : Nat.lt sNext.dedupOffset sNext.nextOffset :=
            Eq.mpr (congrArg (Nat.lt sNext.dedupOffset) hAct.2.2.1) hLt1
          let hEqNext : sNext.lastAckOffset = sNext.dedupOffset :=
            Eq.trans hAct.2.2.2.2.2.2 (Eq.symm hAct.2.2.2.2.2.1)
          And.intro hLtNext hEqNext
      And.intro hCurNext hDedupNext

    theorem next_preserves_inv (upto : UInt64) (s sNext : IngestState)
        (hInv : ExactlyOnceInv s) (hNext : Next upto s sNext) :
        ExactlyOnceInv sNext :=
      Or.elim hNext
        (fun hPub => publishFresh_preserves_inv s sNext hInv hPub)
        (fun hRest =>
          Or.elim hRest
            (fun hDup => publishDup_preserves_inv s sNext hInv hDup)
            (fun hProc => processFresh_preserves_inv upto s sNext hInv hProc))

    -- Full TLA+ Temporal Safety Theorem:
    --   `Spec upto ⊨ □ (Lift ExactlyOnceInv)`
    theorem spec_satisfies_exactly_once_safety (upto : UInt64) :
        (Spec upto) ⊨ □ (Lift ExactlyOnceInv) :=
      invariantSatisfies (Spec upto) ExactlyOnceInv
        init_establishes_inv
        (next_preserves_inv upto)

    end TlaExactlyOnceIngest

    -- ========================================================================
    -- 4. TLA+ Protocol Specification: Incarnation-Fenced Will & Revocation
    --    Directly over `UInt64` sequences/timestamps and the Clean-origin
    --    `_root_.high_water_monotone` transition function!
    -- ========================================================================
    namespace TlaWillFencing

    open Trust.Temporal

    -- Island specification of `pub fn will_is_fenced(high_water: u64, will_seq: u64) -> bool`
    -- (`BrokerLog::stage_will_fire`: `if will_is_fenced(hw, will.producer_seq)`).
    def will_is_fenced_isl (high_water : UInt64) (will_seq : UInt64) : Bool :=
      decide (will_seq < high_water)

    theorem bool_true_ne_false (h : true = false) : False :=
      Bool.noConfusion h

    -- Soundness of the `!will_is_fenced(high_water, will_seq)` guard over `UInt64`:
    -- `will_is_fenced_isl high_water will_seq = false -> ¬ (will_seq < high_water)`.
    theorem will_not_fenced_isl_not_lt (hw ws : UInt64) :
        will_is_fenced_isl hw ws = false → (Nat.lt (UInt64.toNat ws) (UInt64.toNat hw) → False) :=
      @Decidable.casesOn (LT.lt ws hw)
        (fun (d : Decidable (LT.lt ws hw)) =>
          @Decidable.decide (LT.lt ws hw) d = false → (Nat.lt (UInt64.toNat ws) (UInt64.toNat hw) → False))
        (instDecidableUInt64Lt ws hw)
        (fun hNotLt _ => hNotLt)
        (fun _ hEq => False.elim (bool_true_ne_false hEq))

    -- State variables for a pending connection `Will`:
    --   willSeq   : `producer_seq` carried by the registered will (`UInt64`)
    --   willExpMs : capability expiry of the registering connection (`UInt64`)
    --   highWater : `producer_high_water[producer_id]` (`UInt64`)
    --   revoked   : 0 = active, 1 = peer identity revoked (`R6`)
    --   nowMs     : broker clock at disconnect (`UInt64`)
    --   willFired : 0 = not fired, 1 = will appended on disconnect
    structure WillState where
      willSeq   : UInt64
      willExpMs : UInt64
      highWater : UInt64
      revoked   : Nat
      nowMs     : UInt64
      willFired : Nat

    -- TLA+ Safety Invariant over `UInt64`:
    -- Whenever a will fires (`willFired = 1`), no newer incarnation has published a
    -- record with `willSeq < highWater` (`will_is_fenced_isl highWater willSeq = false`
    -- in `BrokerLog::stage_will_fire`), the capability is not expired (`nowMs < willExpMs`),
    -- and the principal is not revoked (`revoked = 0`).
    --
    -- THE PRODUCER OBLIGATION is NOT this invariant's assumption: it holds for EVERY
    -- `newSeq`, and says only that a will which fired was not fenced. It does not say
    -- that a reconnect FENCES the will, i.e. raises the high water above it. That holds
    -- only when the newer incarnation publishes ABOVE the will, `willSeq < newSeq`, and
    -- the broker cannot check it: a will is a hidden record, and incarnations are the
    -- producer's own count. The producer owes it (`Request::Will`, `Client::will`): a
    -- new incarnation's sequences sit above every sequence of any incarnation it ever
    -- presented, and the incarnation is flushed before its will is registered.
    -- `astream_broker::will_seq` exports the layout that meets the first half (aterm's:
    -- `(inc << 32) | 0xFFFF_FFFF`, up to `INC_MAX`). The obligation is the hypothesis of
    -- what the fence buys, proved below: the newer incarnation's publish fences the will
    -- (`newer_incarnation_publish_fences_the_will`), every later step keeps it fenced
    -- (`next_keeps_a_fenced_will_fenced`), a fenced will has no fire step
    -- (`a_fenced_will_cannot_fire`), and over the spec, once the publish has landed the
    -- will is fenced and unfired in every state (`obliged_spec_fences_the_will_once_landed`).
    -- A producer that reuses an incarnation has `newSeq ≤ willSeq`, and its old will
    -- fires (`will::a_reused_incarnation_is_not_fenced`).
    def WillFencingInv (s : WillState) : Prop :=
      s.willFired = 1 →
        ((Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat s.highWater) → False) ∧
         Nat.lt (UInt64.toNat s.nowMs) (UInt64.toNat s.willExpMs) ∧
         s.revoked = 0)

    def Init (wSeq wExp t0 : UInt64) (s : WillState) : Prop :=
      s.willSeq = wSeq ∧
      s.willExpMs = wExp ∧
      s.highWater = 0 ∧
      s.revoked = 0 ∧
      s.nowMs = t0 ∧
      s.willFired = 0

    -- Action 1: NewerIncarnationPublish — a reconnected incarnation publishes a
    -- normal record (`seq < ACK_SEQ_BASE`) advancing `highWater` via the
    -- Clean-origin `_root_.high_water_monotone` function before the stale TCP socket closes.
    def NewerIncarnationPublish (newSeq : UInt64) (s sNext : WillState) : Prop :=
      s.willFired = 0 ∧
      sNext.willSeq = s.willSeq ∧
      sNext.willExpMs = s.willExpMs ∧
      sNext.highWater = _root_.high_water_monotone s.highWater newSeq ∧
      sNext.revoked = s.revoked ∧
      sNext.nowMs = s.nowMs ∧
      sNext.willFired = 0

    -- Action 2: RevokePrincipal — operator revokes the peer's identity (`R6`).
    def RevokePrincipal (s sNext : WillState) : Prop :=
      s.willFired = 0 ∧
      sNext.willSeq = s.willSeq ∧
      sNext.willExpMs = s.willExpMs ∧
      sNext.highWater = s.highWater ∧
      sNext.revoked = 1 ∧
      sNext.nowMs = s.nowMs ∧
      sNext.willFired = 0

    -- Action 3: FireWillOnDisconnect — socket closes while the Rust-verified
    -- `will_is_fenced_isl s.highWater s.willSeq` guard is `false` (`¬ (willSeq < highWater)`),
    -- `nowMs < willExpMs`, and `revoked = 0`.
    def FireWillOnDisconnect (s sNext : WillState) : Prop :=
      will_is_fenced_isl s.highWater s.willSeq = false ∧
      Nat.lt (UInt64.toNat s.nowMs) (UInt64.toNat s.willExpMs) ∧
      s.revoked = 0 ∧
      sNext.willSeq = s.willSeq ∧
      sNext.willExpMs = s.willExpMs ∧
      sNext.highWater = s.highWater ∧
      sNext.revoked = s.revoked ∧
      sNext.nowMs = s.nowMs ∧
      sNext.willFired = 1

    -- Action 4: SuppressWillOnDisconnect — socket closes when fenced, expired, or
    -- revoked; the will is suppressed (`willFired' = 0`).
    def SuppressWillOnDisconnect (s sNext : WillState) : Prop :=
      sNext.willSeq = s.willSeq ∧
      sNext.willExpMs = s.willExpMs ∧
      sNext.highWater = s.highWater ∧
      sNext.revoked = s.revoked ∧
      sNext.nowMs = s.nowMs ∧
      sNext.willFired = 0

    def Next (newSeq : UInt64) (s sNext : WillState) : Prop :=
      NewerIncarnationPublish newSeq s sNext ∨
        (RevokePrincipal s sNext ∨
          (FireWillOnDisconnect s sNext ∨ SuppressWillOnDisconnect s sNext))

    def Spec (wSeq wExp t0 newSeq : UInt64) : StateMachine WillState :=
      StateMachine.mk (Init wSeq wExp t0) (Next newSeq)

    theorem zero_ne_one (h : 0 = 1) : False :=
      Nat.noConfusion h

    theorem init_establishes_inv (wSeq wExp t0 : UInt64) (s : WillState)
        (hInit : Init wSeq wExp t0 s) : WillFencingInv s :=
      fun hF =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hInit.2.2.2.2.2) hF
        False.elim (zero_ne_one h01)

    theorem publish_preserves_inv (newSeq : UInt64) (s sNext : WillState)
        (hAct : NewerIncarnationPublish newSeq s sNext) : WillFencingInv sNext :=
      fun hF =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2.2.2.2.2) hF
        False.elim (zero_ne_one h01)

    theorem revoke_preserves_inv (s sNext : WillState)
        (hAct : RevokePrincipal s sNext) : WillFencingInv sNext :=
      fun hF =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2.2.2.2.2) hF
        False.elim (zero_ne_one h01)

    theorem fire_preserves_inv (s sNext : WillState)
        (hAct : FireWillOnDisconnect s sNext) : WillFencingInv sNext :=
      fun _ =>
        let hFenceGuard : Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat s.highWater) → False :=
          will_not_fenced_isl_not_lt s.highWater s.willSeq hAct.1
        let hFence1 : Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat sNext.highWater) → False :=
          Eq.mpr (congrArg (fun h => Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat h) → False) hAct.2.2.2.2.2.1) hFenceGuard
        let hFenceNext : Nat.lt (UInt64.toNat sNext.willSeq) (UInt64.toNat sNext.highWater) → False :=
          Eq.mpr (congrArg (fun w => Nat.lt (UInt64.toNat w) (UInt64.toNat sNext.highWater) → False) hAct.2.2.2.1) hFence1
        let hExp1 : Nat.lt (UInt64.toNat sNext.nowMs) (UInt64.toNat s.willExpMs) :=
          Eq.mpr (congrArg (fun t => Nat.lt (UInt64.toNat t) (UInt64.toNat s.willExpMs)) hAct.2.2.2.2.2.2.2.1) hAct.2.1
        let hExpNext : Nat.lt (UInt64.toNat sNext.nowMs) (UInt64.toNat sNext.willExpMs) :=
          Eq.mpr (congrArg (fun e => Nat.lt (UInt64.toNat sNext.nowMs) (UInt64.toNat e)) hAct.2.2.2.2.1) hExp1
        let hRevNext : sNext.revoked = 0 :=
          Eq.trans hAct.2.2.2.2.2.2.1 hAct.2.2.1
        And.intro hFenceNext (And.intro hExpNext hRevNext)

    theorem suppress_preserves_inv (s sNext : WillState)
        (hAct : SuppressWillOnDisconnect s sNext) : WillFencingInv sNext :=
      fun hF =>
        let h01 : 0 = 1 := Eq.trans (Eq.symm hAct.2.2.2.2.2) hF
        False.elim (zero_ne_one h01)

    theorem next_preserves_inv (newSeq : UInt64) (s sNext : WillState)
        (hNext : Next newSeq s sNext) : WillFencingInv sNext :=
      Or.elim hNext
        (fun hPub => publish_preserves_inv newSeq s sNext hPub)
        (fun hR1 =>
          Or.elim hR1
            (fun hRev => revoke_preserves_inv s sNext hRev)
            (fun hR2 =>
              Or.elim hR2
                (fun hFire => fire_preserves_inv s sNext hFire)
                (fun hSup => suppress_preserves_inv s sNext hSup)))

    -- Full TLA+ Temporal Safety Theorem:
    --   `Spec wSeq wExp t0 newSeq ⊨ □ (Lift WillFencingInv)`
    theorem spec_satisfies_will_fencing_safety (wSeq wExp t0 newSeq : UInt64) :
        (Spec wSeq wExp t0 newSeq) ⊨ □ (Lift WillFencingInv) :=
      invariantSatisfies (Spec wSeq wExp t0 newSeq) WillFencingInv
        (init_establishes_inv wSeq wExp t0)
        (fun _ sNext _ hNext => next_preserves_inv newSeq _ sNext hNext)

    -- WHAT THE OBLIGATION BUYS, step by step, each kernel-checked.
    --
    -- (1) A record above the will raises the high water above the will, whatever the
    -- high water was before it ...
    theorem high_water_above_a_newer_seq (hw newSeq ws : UInt64)
        (hAbove : Nat.lt (UInt64.toNat ws) (UInt64.toNat newSeq)) :
        Nat.lt (UInt64.toNat ws) (UInt64.toNat (_root_.high_water_monotone hw newSeq)) :=
      @Decidable.casesOn (LT.lt hw newSeq)
        (fun (d : Decidable (LT.lt hw newSeq)) =>
          Nat.lt (UInt64.toNat ws) (UInt64.toNat (@ite UInt64 (LT.lt hw newSeq) d newSeq hw)))
        (instDecidableUInt64Lt hw newSeq)
        (fun hNotLt =>
          -- Not below the new record, so the high water is at or above it (Nat totality).
          let hNewLe : Nat.le (UInt64.toNat newSeq) (UInt64.toNat hw) :=
            Or.elim (Nat.le_or_lt (UInt64.toNat newSeq) (UInt64.toNat hw))
              (fun hLe => hLe)
              (fun hLt => False.elim (hNotLt hLt))
          Nat.le_trans hAbove hNewLe)
        (fun _ => hAbove)

    -- (2) ... and the high water NEVER FALLS, whatever sequence a later publish
    -- carries: a stale incarnation's record below it leaves it where it was. This is
    -- what `_root_.high_water_monotone` being a maximum buys, and a "latest record
    -- wins" rule would fail here ...
    theorem high_water_never_falls (hw pubSeq : UInt64) :
        Nat.le (UInt64.toNat hw) (UInt64.toNat (_root_.high_water_monotone hw pubSeq)) :=
      @Decidable.casesOn (LT.lt hw pubSeq)
        (fun (d : Decidable (LT.lt hw pubSeq)) =>
          Nat.le (UInt64.toNat hw) (UInt64.toNat (@ite UInt64 (LT.lt hw pubSeq) d pubSeq hw)))
        (instDecidableUInt64Lt hw pubSeq)
        (fun _ => Nat.le.refl (UInt64.toNat hw))
        (fun hLt => Nat.le_of_lt hLt)

    -- A step that keeps the will and sets the high water to `hw` keeps `willSeq < hw`.
    theorem fenced_carried (s sNext : WillState) (hw : UInt64)
        (hWs : sNext.willSeq = s.willSeq) (hHw : sNext.highWater = hw)
        (hLt : Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat hw)) :
        Nat.lt (UInt64.toNat sNext.willSeq) (UInt64.toNat sNext.highWater) :=
      let h1 : Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat sNext.highWater) :=
        Eq.mpr (congrArg (fun h => Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat h)) hHw) hLt
      Eq.mpr (congrArg (fun w => Nat.lt (UInt64.toNat w) (UInt64.toNat sNext.highWater)) hWs) h1

    -- (3) ... the Rust-verified guard reads a will below the high water as fenced, so
    -- a fenced will has no fire step ...
    theorem fenced_isl_of_lt (hw ws : UInt64)
        (hLt : Nat.lt (UInt64.toNat ws) (UInt64.toNat hw)) :
        will_is_fenced_isl hw ws = true :=
      @Decidable.casesOn (LT.lt ws hw)
        (fun (d : Decidable (LT.lt ws hw)) => @Decidable.decide (LT.lt ws hw) d = true)
        (instDecidableUInt64Lt ws hw)
        (fun hNotLt => False.elim (hNotLt hLt))
        (fun _ => rfl)

    theorem a_fenced_will_cannot_fire (s sNext : WillState)
        (hFenced : Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat s.highWater)) :
        FireWillOnDisconnect s sNext → False :=
      fun hFire =>
        bool_true_ne_false
          (Eq.trans (Eq.symm (fenced_isl_of_lt s.highWater s.willSeq hFenced)) hFire.1)

    -- (4) ... so EVERY step keeps a fenced will fenced, a publish under ANY sequence
    -- included (a stale incarnation's, below the will): a publish only raises the high
    -- water (2), a revocation or a suppression leaves the will and the high water as
    -- they were, and a fire step does not exist from a fenced will (3) ...
    theorem next_keeps_a_fenced_will_fenced (pubSeq : UInt64) (s sNext : WillState)
        (hFenced : Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat s.highWater))
        (hNext : Next pubSeq s sNext) :
        Nat.lt (UInt64.toNat sNext.willSeq) (UInt64.toNat sNext.highWater) :=
      Or.elim hNext
        (fun hPub =>
          fenced_carried s sNext (_root_.high_water_monotone s.highWater pubSeq)
            hPub.2.1 hPub.2.2.2.1
            (Nat.le_trans hFenced (high_water_never_falls s.highWater pubSeq)))
        (fun hR1 =>
          Or.elim hR1
            (fun hRev => fenced_carried s sNext s.highWater hRev.2.1 hRev.2.2.2.1 hFenced)
            (fun hR2 =>
              Or.elim hR2
                (fun hFire => False.elim (a_fenced_will_cannot_fire s sNext hFenced hFire))
                (fun hSup => fenced_carried s sNext s.highWater hSup.1 hSup.2.2.1 hFenced)))

    -- (5) ... and under the producer obligation (`willSeq < newSeq`) the newer
    -- incarnation's publish is what fences the will. From that publish on, by (4) and
    -- (3), the will is fenced in every later state and has no fire step in any of them.
    theorem newer_incarnation_publish_fences_the_will (newSeq : UInt64)
        (s sNext : WillState)
        (hObligation : Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat newSeq))
        (hPub : NewerIncarnationPublish newSeq s sNext) :
        Nat.lt (UInt64.toNat sNext.willSeq) (UInt64.toNat sNext.highWater) :=
      fenced_carried s sNext (_root_.high_water_monotone s.highWater newSeq)
        hPub.2.1 hPub.2.2.2.1
        (high_water_above_a_newer_seq s.highWater newSeq s.willSeq hObligation)

    -- OVER THE SPEC, as a temporal law like `WillFencingInv`'s. Under the obligation
    -- (`wSeq < newSeq`), in EVERY reachable state, once the newer incarnation's publish
    -- has landed (`newSeq ≤ highWater`: the high water starts at 0 and only that publish
    -- moves it) the will is fenced and has not fired. The high water never falls (2),
    -- so every state after the landing is one this clause speaks for.
    def FencedOnceLanded (newSeq : UInt64) (s : WillState) : Prop :=
      Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat newSeq) ∧
        (Nat.le (UInt64.toNat newSeq) (UInt64.toNat s.highWater) →
          (Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat s.highWater) ∧ s.willFired = 0))

    theorem fenced_once_landed_of_unfired (newSeq : UInt64) (s : WillState)
        (hBelow : Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat newSeq))
        (hUnfired : s.willFired = 0) : FencedOnceLanded newSeq s :=
      And.intro hBelow (fun hLanded => And.intro (Nat.le_trans hBelow hLanded) hUnfired)

    theorem will_stays_below (newSeq : UInt64) (s sNext : WillState)
        (hWs : sNext.willSeq = s.willSeq)
        (hBelow : Nat.lt (UInt64.toNat s.willSeq) (UInt64.toNat newSeq)) :
        Nat.lt (UInt64.toNat sNext.willSeq) (UInt64.toNat newSeq) :=
      Eq.mpr (congrArg (fun w => Nat.lt (UInt64.toNat w) (UInt64.toNat newSeq)) hWs) hBelow

    theorem init_establishes_fenced_once_landed (wSeq wExp t0 newSeq : UInt64)
        (hObligation : Nat.lt (UInt64.toNat wSeq) (UInt64.toNat newSeq))
        (s : WillState) (hInit : Init wSeq wExp t0 s) : FencedOnceLanded newSeq s :=
      fenced_once_landed_of_unfired newSeq s
        (Eq.mpr (congrArg (fun w => Nat.lt (UInt64.toNat w) (UInt64.toNat newSeq)) hInit.1)
          hObligation)
        hInit.2.2.2.2.2

    theorem next_preserves_fenced_once_landed (newSeq : UInt64) (s sNext : WillState)
        (hInv : FencedOnceLanded newSeq s) (hNext : Next newSeq s sNext) :
        FencedOnceLanded newSeq sNext :=
      Or.elim hNext
        (fun hPub =>
          fenced_once_landed_of_unfired newSeq sNext
            (will_stays_below newSeq s sNext hPub.2.1 hInv.1) hPub.2.2.2.2.2.2)
        (fun hR1 =>
          Or.elim hR1
            (fun hRev =>
              fenced_once_landed_of_unfired newSeq sNext
                (will_stays_below newSeq s sNext hRev.2.1 hInv.1) hRev.2.2.2.2.2.2)
            (fun hR2 =>
              Or.elim hR2
                (fun hFire =>
                  -- A fire step leaves the high water where it was: had the publish
                  -- landed after it, it had landed before it, the will was fenced
                  -- there (the obligation), and a fenced will has no fire step (3).
                  And.intro (will_stays_below newSeq s sNext hFire.2.2.2.1 hInv.1)
                    (fun hLanded =>
                      let hLandedBefore : Nat.le (UInt64.toNat newSeq) (UInt64.toNat s.highWater) :=
                        Eq.mp (congrArg (fun h => Nat.le (UInt64.toNat newSeq) (UInt64.toNat h))
                          hFire.2.2.2.2.2.1) hLanded
                      False.elim
                        (a_fenced_will_cannot_fire s sNext (Nat.le_trans hInv.1 hLandedBefore) hFire)))
                (fun hSup =>
                  fenced_once_landed_of_unfired newSeq sNext
                    (will_stays_below newSeq s sNext hSup.1 hInv.1) hSup.2.2.2.2.2)))

    -- Full TLA+ Temporal Safety Theorem, under the producer obligation:
    --   `wSeq < newSeq → Spec wSeq wExp t0 newSeq ⊨ □ (Lift (FencedOnceLanded newSeq))`
    theorem obliged_spec_fences_the_will_once_landed (wSeq wExp t0 newSeq : UInt64)
        (hObligation : Nat.lt (UInt64.toNat wSeq) (UInt64.toNat newSeq)) :
        (Spec wSeq wExp t0 newSeq) ⊨ □ (Lift (FencedOnceLanded newSeq)) :=
      invariantSatisfies (Spec wSeq wExp t0 newSeq) (FencedOnceLanded newSeq)
        (init_establishes_fenced_once_landed wSeq wExp t0 newSeq hObligation)
        (fun s sNext hInv hNext => next_preserves_fenced_once_landed newSeq s sNext hInv hNext)

    end TlaWillFencing

    -- ========================================================================
    -- 5. TLA+ Compaction Refinement (`retain_before_carrying_state`)
    --    Directly over `UInt64` offsets and `_root_.compact_floor_monotone`!
    -- ========================================================================
    namespace TlaCompactionRefinement

    open Trust.Temporal

    theorem compact_floor_ge_base : forall (req_min : UInt64) (base_off : UInt64),
        Nat.le (UInt64.toNat base_off) (UInt64.toNat (_root_.compact_floor_monotone req_min base_off)) :=
      fun req base => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt base req)) =>
          Nat.le (UInt64.toNat base) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => base) (fun _ => req))))
        (instDecidableUInt64Lt base req)
        (fun _ => Nat.le.refl (UInt64.toNat base))
        (fun h => Nat.le_of_lt h)

    -- Abstract control-plane state (live principal bindings, pending wills, and
    -- consumer-group cursors) vs. Concrete compacted log + `<log>.state` sidecar:
    structure AbstractControlState where
      bindTableDigest  : Nat
      willTableDigest  : Nat
      groupTableDigest : Nat

    structure ConcreteCompactedStore where
      baseOffset       : UInt64
      headOffset       : UInt64
      sidecarBind      : Nat
      sidecarWills     : Nat
      sidecarGroups    : Nat

    def abstractionMap (c : ConcreteCompactedStore) : AbstractControlState :=
      AbstractControlState.mk c.sidecarBind c.sidecarWills c.sidecarGroups

    -- A compaction step (`retain_before_carrying_state`) advances `baseOffset` via
    -- the Clean-origin `_root_.compact_floor_monotone reqMin c.baseOffset` transition
    -- while preserving the control-plane digests in `<log>.state`, refining an abstract
    -- stuttering step (`abstractionMap cNext = abstractionMap c`).
    def CompactStep (reqMin : UInt64) (c cNext : ConcreteCompactedStore) : Prop :=
      cNext.baseOffset = _root_.compact_floor_monotone reqMin c.baseOffset ∧
      cNext.headOffset = c.headOffset ∧
      cNext.sidecarBind = c.sidecarBind ∧
      cNext.sidecarWills = c.sidecarWills ∧
      cNext.sidecarGroups = c.sidecarGroups

    theorem compactStep_monotone_base (reqMin : UInt64)
        (c cNext : ConcreteCompactedStore) (hStep : CompactStep reqMin c cNext) :
        Nat.le (UInt64.toNat c.baseOffset) (UInt64.toNat cNext.baseOffset) :=
      Eq.mpr
        (congrArg (fun b => Nat.le (UInt64.toNat c.baseOffset) (UInt64.toNat b)) hStep.1)
        (compact_floor_ge_base reqMin c.baseOffset)

    theorem compactStep_preserves_abstraction (reqMin : UInt64)
        (c cNext : ConcreteCompactedStore) (hStep : CompactStep reqMin c cNext) :
        (abstractionMap cNext).bindTableDigest = (abstractionMap c).bindTableDigest ∧
        (abstractionMap cNext).willTableDigest = (abstractionMap c).willTableDigest ∧
        (abstractionMap cNext).groupTableDigest = (abstractionMap c).groupTableDigest :=
      And.intro hStep.2.2.1
        (And.intro hStep.2.2.2.1 hStep.2.2.2.2)

    end TlaCompactionRefinement

    -- ========================================================================
    -- 6. TLA+ Protocol Specification: Epoch-Fenced Watermark Replication
    --    Directly over `UInt64` and Clean-origin `_root_.epoch_advance_monotone`,
    --    `_root_.replica_ack_monotone`, and `_root_.committed_watermark`!
    -- ========================================================================
    namespace TlaEpochWatermarkReplication

    open Trust.Temporal

    -- Island specification of `pub fn epoch_is_fenced(cur_epoch: u64, req_epoch: u64) -> bool`.
    def epoch_is_fenced_isl (cur_epoch : UInt64) (req_epoch : UInt64) : Bool :=
      decide (req_epoch < cur_epoch)

    -- Island specification of `pub fn offset_is_committed(committed_upto: u64, offset: u64) -> bool`.
    def offset_is_committed_isl (committed_upto : UInt64) (offset : UInt64) : Bool :=
      decide (offset < committed_upto)

    -- Proof that `_root_.committed_watermark head ack <= head` (committed frontier never
    -- exceeds the primary log head).
    theorem committed_watermark_le_head (head ack : UInt64) :
        _root_.committed_watermark head ack <= head := by
      unfold _root_.committed_watermark
      split <;> omega

    -- Proof that `_root_.committed_watermark head ack <= ack` (committed frontier never
    -- exceeds the durable replica acknowledgement).
    theorem committed_watermark_le_ack : forall (head : UInt64) (ack : UInt64),
        Nat.le (UInt64.toNat (_root_.committed_watermark head ack)) (UInt64.toNat ack) :=
      fun head ack => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt head ack)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => ack) (fun _ => head))) (UInt64.toNat ack))
        (instDecidableUInt64Lt head ack)
        (fun _ => Nat.le.refl (UInt64.toNat ack))
        (fun h => Nat.le_of_lt h)

    theorem epoch_advance_ge_cur : forall (cur : UInt64) (req : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.epoch_advance_monotone cur req)) :=
      fun cur req => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => req))))
        (instDecidableUInt64Lt cur req)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem replica_ack_ge_cur : forall (cur : UInt64) (new_ack : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.replica_ack_monotone cur new_ack)) :=
      fun cur ack => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur ack)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => ack))))
        (instDecidableUInt64Lt cur ack)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    def fenced_replica_watermark_isl (leader_epoch req_epoch primary_head cur_ack cand_ack : UInt64) : UInt64 :=
      _root_.committed_watermark primary_head
        (_root_.fenced_ack_select req_epoch leader_epoch cur_ack
          (_root_.replica_ack_monotone cur_ack cand_ack))

    -- Proof that the 5-parameter `fenced_replica_watermark_isl` kernel never exceeds `primary_head`.
    theorem fenced_replica_watermark_le_head (le re head cur cand : UInt64) :
        Nat.le (UInt64.toNat (fenced_replica_watermark_isl le re head cur cand)) (UInt64.toNat head) :=
      committed_watermark_le_head head
        (_root_.fenced_ack_select re le cur (_root_.replica_ack_monotone cur cand))

    structure ReplicationState where
      epoch         : UInt64
      headOffset    : UInt64
      replicaAck    : UInt64
      committedUpto : UInt64

    -- TLA+ Safety Invariant:
    -- The committed read watermark `committedUpto` is always simultaneously bounded
    -- by `headOffset` (durable on primary) AND `replicaAck` (durable on follower).
    def ReplicationSafetyInv (s : ReplicationState) : Prop :=
      Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat s.headOffset) ∧
      Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat s.replicaAck)

    def Init (e0 : UInt64) (s : ReplicationState) : Prop :=
      s.epoch = e0 ∧
      s.headOffset = 0 ∧
      s.replicaAck = 0 ∧
      s.committedUpto = 0

    -- Action 1: AdvanceEpoch — unfenced leader/follower advances `epoch` via the
    -- Clean-origin `_root_.epoch_advance_monotone` function.
    def AdvanceEpoch (reqEpoch : UInt64) (s sNext : ReplicationState) : Prop :=
      epoch_is_fenced_isl s.epoch reqEpoch = false ∧
      sNext.epoch = _root_.epoch_advance_monotone s.epoch reqEpoch ∧
      sNext.headOffset = s.headOffset ∧
      sNext.replicaAck = s.replicaAck ∧
      sNext.committedUpto = s.committedUpto

    -- Action 2: PrimaryAppend — primary appends records advancing `headOffset` and
    -- recomputes `committedUpto` via the Clean-origin `_root_.committed_watermark`.
    def PrimaryAppend (newHead : UInt64) (s sNext : ReplicationState) : Prop :=
      sNext.epoch = s.epoch ∧
      sNext.headOffset = _root_.replica_ack_monotone s.headOffset newHead ∧
      sNext.replicaAck = s.replicaAck ∧
      sNext.committedUpto = _root_.committed_watermark sNext.headOffset s.replicaAck

    -- Action 3: FollowerAck — follower acknowledges durable replication up to `newAck`
    -- via Clean-origin `_root_.replica_ack_monotone`, advancing `committedUpto` via
    -- Clean-origin `_root_.committed_watermark`.
    def FollowerAck (newAck : UInt64) (s sNext : ReplicationState) : Prop :=
      sNext.epoch = s.epoch ∧
      sNext.headOffset = s.headOffset ∧
      sNext.replicaAck = _root_.replica_ack_monotone s.replicaAck newAck ∧
      sNext.committedUpto = _root_.committed_watermark s.headOffset sNext.replicaAck

    def Next (reqEpoch newHead newAck : UInt64) (s sNext : ReplicationState) : Prop :=
      AdvanceEpoch reqEpoch s sNext ∨
        (PrimaryAppend newHead s sNext ∨ FollowerAck newAck s sNext)

    def Spec (e0 reqEpoch newHead newAck : UInt64) : StateMachine ReplicationState :=
      StateMachine.mk (Init e0) (Next reqEpoch newHead newAck)

    theorem init_establishes_inv (e0 : UInt64) (s : ReplicationState)
        (hInit : Init e0 s) : ReplicationSafetyInv s :=
      let h0 : Nat.le (UInt64.toNat 0) (UInt64.toNat 0) := Nat.le_refl (UInt64.toNat 0)
      let hHead1 : Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat 0) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat c) (UInt64.toNat 0)) hInit.2.2.2) h0
      let hHead : Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat s.headOffset) :=
        Eq.mpr (congrArg (fun h => Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat h)) hInit.2.1) hHead1
      let hAck : Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat s.replicaAck) :=
        Eq.mpr (congrArg (fun a => Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat a)) hInit.2.2.1) hHead1
      And.intro hHead hAck

    theorem advanceEpoch_preserves_inv (reqEpoch : UInt64) (s sNext : ReplicationState)
        (hInv : ReplicationSafetyInv s) (hAct : AdvanceEpoch reqEpoch s sNext) :
        ReplicationSafetyInv sNext :=
      let hHead1 : Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat sNext.headOffset) :=
        Eq.mpr (congrArg (fun h => Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat h)) hAct.2.2.1) hInv.1
      let hHead : Nat.le (UInt64.toNat sNext.committedUpto) (UInt64.toNat sNext.headOffset) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat c) (UInt64.toNat sNext.headOffset)) hAct.2.2.2.2) hHead1
      let hAck1 : Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat sNext.replicaAck) :=
        Eq.mpr (congrArg (fun a => Nat.le (UInt64.toNat s.committedUpto) (UInt64.toNat a)) hAct.2.2.2.1) hInv.2
      let hAck : Nat.le (UInt64.toNat sNext.committedUpto) (UInt64.toNat sNext.replicaAck) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat c) (UInt64.toNat sNext.replicaAck)) hAct.2.2.2.2) hAck1
      And.intro hHead hAck

    theorem primaryAppend_preserves_inv (newHead : UInt64) (s sNext : ReplicationState)
        (hAct : PrimaryAppend newHead s sNext) : ReplicationSafetyInv sNext :=
      let hCwHead : Nat.le (UInt64.toNat (_root_.committed_watermark sNext.headOffset s.replicaAck))
          (UInt64.toNat sNext.headOffset) :=
        committed_watermark_le_head sNext.headOffset s.replicaAck
      let hHead : Nat.le (UInt64.toNat sNext.committedUpto) (UInt64.toNat sNext.headOffset) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat c) (UInt64.toNat sNext.headOffset)) hAct.2.2.2) hCwHead
      let hCwAck : Nat.le (UInt64.toNat (_root_.committed_watermark sNext.headOffset s.replicaAck))
          (UInt64.toNat s.replicaAck) :=
        committed_watermark_le_ack sNext.headOffset s.replicaAck
      let hCwAckNext : Nat.le (UInt64.toNat (_root_.committed_watermark sNext.headOffset s.replicaAck))
          (UInt64.toNat sNext.replicaAck) :=
        Eq.mpr (congrArg (fun a => Nat.le (UInt64.toNat (_root_.committed_watermark sNext.headOffset s.replicaAck)) (UInt64.toNat a)) hAct.2.2.1) hCwAck
      let hAck : Nat.le (UInt64.toNat sNext.committedUpto) (UInt64.toNat sNext.replicaAck) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat c) (UInt64.toNat sNext.replicaAck)) hAct.2.2.2) hCwAckNext
      And.intro hHead hAck

    theorem followerAck_preserves_inv (newAck : UInt64) (s sNext : ReplicationState)
        (hAct : FollowerAck newAck s sNext) : ReplicationSafetyInv sNext :=
      let hCwHead : Nat.le (UInt64.toNat (_root_.committed_watermark s.headOffset sNext.replicaAck))
          (UInt64.toNat s.headOffset) :=
        committed_watermark_le_head s.headOffset sNext.replicaAck
      let hCwHeadNext : Nat.le (UInt64.toNat (_root_.committed_watermark s.headOffset sNext.replicaAck))
          (UInt64.toNat sNext.headOffset) :=
        Eq.mpr (congrArg (fun h => Nat.le (UInt64.toNat (_root_.committed_watermark s.headOffset sNext.replicaAck)) (UInt64.toNat h)) hAct.2.1) hCwHead
      let hHead : Nat.le (UInt64.toNat sNext.committedUpto) (UInt64.toNat sNext.headOffset) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat c) (UInt64.toNat sNext.headOffset)) hAct.2.2.2) hCwHeadNext
      let hCwAck : Nat.le (UInt64.toNat (_root_.committed_watermark s.headOffset sNext.replicaAck))
          (UInt64.toNat sNext.replicaAck) :=
        committed_watermark_le_ack s.headOffset sNext.replicaAck
      let hAck : Nat.le (UInt64.toNat sNext.committedUpto) (UInt64.toNat sNext.replicaAck) :=
        Eq.mpr (congrArg (fun c => Nat.le (UInt64.toNat c) (UInt64.toNat sNext.replicaAck)) hAct.2.2.2) hCwAck
      And.intro hHead hAck

    theorem next_preserves_inv (reqEpoch newHead newAck : UInt64)
        (s sNext : ReplicationState)
        (hInv : ReplicationSafetyInv s)
        (hNext : Next reqEpoch newHead newAck s sNext) :
        ReplicationSafetyInv sNext :=
      Or.elim hNext
        (fun hEp => advanceEpoch_preserves_inv reqEpoch s sNext hInv hEp)
        (fun hRest =>
          Or.elim hRest
            (fun hApp => primaryAppend_preserves_inv newHead s sNext hApp)
            (fun hAck => followerAck_preserves_inv newAck s sNext hAck))

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec e0 reqEpoch newHead newAck) ⊨ □ (Lift ReplicationSafetyInv)`
    theorem spec_satisfies_replication_safety (e0 reqEpoch newHead newAck : UInt64) :
        (Spec e0 reqEpoch newHead newAck) ⊨ □ (Lift ReplicationSafetyInv) :=
      invariantSatisfies (Spec e0 reqEpoch newHead newAck) ReplicationSafetyInv
        (init_establishes_inv e0)
        (next_preserves_inv reqEpoch newHead newAck)

    end TlaEpochWatermarkReplication

    -- ========================================================================
    -- 7. TLA+ Protocol Specification: Credit-Windowed Pipelined Flow Control
    --    Directly over `UInt64` and Clean-origin `_root_.replica_ack_monotone`
    --    and `_root_.credit_horizon_monotone`!
    -- ========================================================================
    namespace TlaCreditFlowWindow

    open Trust.Temporal

    -- Island specification of `pub fn can_send_in_window(horizon: u64, next_seq: u64) -> bool`.
    def can_send_in_window_isl (horizon : UInt64) (next_seq : UInt64) : Bool :=
      decide (next_seq < horizon)

    theorem credit_horizon_ge_cur : forall (cur : UInt64) (new_h : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.credit_horizon_monotone cur new_h)) :=
      fun cur new_h => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur new_h)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => new_h))))
        (instDecidableUInt64Lt cur new_h)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun h => Nat.le_of_lt h)

    theorem credit_horizon_lub (cur req bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hReq : Nat.le (UInt64.toNat req) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.credit_horizon_monotone cur req)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur req)
        (fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur req) d req cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur req)
        (fun _ => hCur)
        (fun _ => hReq)

    theorem replica_ack_lub (cur req bound : UInt64)
        (hCur : Nat.le (UInt64.toNat cur) (UInt64.toNat bound))
        (hReq : Nat.le (UInt64.toNat req) (UInt64.toNat bound)) :
        Nat.le (UInt64.toNat (_root_.replica_ack_monotone cur req)) (UInt64.toNat bound) :=
      @Decidable.casesOn (LT.lt cur req)
        (fun (d : Decidable (LT.lt cur req)) =>
          Nat.le (UInt64.toNat (@ite UInt64 (LT.lt cur req) d req cur)) (UInt64.toNat bound))
        (instDecidableUInt64Lt cur req)
        (fun _ => hCur)
        (fun _ => hReq)

    def windowed_send_advance_isl (sent_seq ack_seq credit_horizon cand_seq : UInt64) : UInt64 :=
      if ack_seq <= sent_seq then
        _root_.window_gate_send sent_seq credit_horizon
          (_root_.credit_horizon_monotone sent_seq
            (_root_.committed_watermark credit_horizon cand_seq))
          sent_seq
      else sent_seq

    -- Proof that the 4-parameter `windowed_send_advance_isl` kernel is monotone (`>= sent`).
    theorem windowed_send_advance_ge_sent : forall (sent ack hor cand : UInt64),
        Nat.le (UInt64.toNat sent) (UInt64.toNat (windowed_send_advance_isl sent ack hor cand)) :=
      fun sent ack hor cand => Decidable.casesOn
        (motive := fun (d1 : Decidable (LE.le ack sent)) =>
          Nat.le (UInt64.toNat sent) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d1
            (fun _ => sent)
            (fun _ => _root_.window_gate_send sent hor
              (_root_.credit_horizon_monotone sent (_root_.committed_watermark hor cand))
              sent))))
        (instDecidableUInt64Le ack sent)
        (fun _ => Nat.le.refl (UInt64.toNat sent))
        (fun _ => Decidable.casesOn
          (motive := fun (d2 : Decidable (LT.lt sent hor)) =>
            Nat.le (UInt64.toNat sent) (UInt64.toNat (Decidable.casesOn
              (motive := fun _ => UInt64) d2
              (fun _ => sent)
              (fun _ => _root_.credit_horizon_monotone sent (_root_.committed_watermark hor cand)))))
          (instDecidableUInt64Lt sent hor)
          (fun _ => Nat.le.refl (UInt64.toNat sent))
          (fun _ => credit_horizon_ge_cur sent (_root_.committed_watermark hor cand)))

    structure WindowState where
      ackedSeq      : UInt64
      sentSeq       : UInt64
      creditHorizon : UInt64

    -- TLA+ Safety Invariant:
    -- 1. `ackedSeq <= sentSeq` (cannot acknowledge frames not yet sent)
    -- 2. `sentSeq <= creditHorizon` (in-flight pipeline never overruns granted credit window)
    def CreditWindowSafetyInv (s : WindowState) : Prop :=
      Nat.le (UInt64.toNat s.ackedSeq) (UInt64.toNat s.sentSeq) ∧
      Nat.le (UInt64.toNat s.sentSeq) (UInt64.toNat s.creditHorizon)

    def Init (h0 : UInt64) (s : WindowState) : Prop :=
      s.ackedSeq = 0 ∧
      s.sentSeq = 0 ∧
      s.creditHorizon = h0

    -- Action 1: SendBatch — pipeline frames up to `nextSent <= creditHorizon`
    -- via Clean-origin `_root_.credit_horizon_monotone s.sentSeq nextSent`.
    def SendBatch (nextSent : UInt64) (s sNext : WindowState) : Prop :=
      Nat.le (UInt64.toNat nextSent) (UInt64.toNat s.creditHorizon) ∧
      sNext.ackedSeq = s.ackedSeq ∧
      sNext.sentSeq = _root_.credit_horizon_monotone s.sentSeq nextSent ∧
      sNext.creditHorizon = s.creditHorizon

    -- Action 2: AckDelivered — advance `ackedSeq` up to `newAck <= sentSeq`
    -- via Clean-origin `_root_.replica_ack_monotone s.ackedSeq newAck`.
    def AckDelivered (newAck : UInt64) (s sNext : WindowState) : Prop :=
      Nat.le (UInt64.toNat newAck) (UInt64.toNat s.sentSeq) ∧
      sNext.ackedSeq = _root_.replica_ack_monotone s.ackedSeq newAck ∧
      sNext.sentSeq = s.sentSeq ∧
      sNext.creditHorizon = s.creditHorizon

    -- Action 3: GrantHorizon — peer grants additional credit advancing `creditHorizon`
    -- via Clean-origin `_root_.credit_horizon_monotone s.creditHorizon newHorizon`.
    def GrantHorizon (newHorizon : UInt64) (s sNext : WindowState) : Prop :=
      sNext.ackedSeq = s.ackedSeq ∧
      sNext.sentSeq = s.sentSeq ∧
      sNext.creditHorizon = _root_.credit_horizon_monotone s.creditHorizon newHorizon

    def Next (nextSent newAck newHorizon : UInt64) (s sNext : WindowState) : Prop :=
      SendBatch nextSent s sNext ∨
        (AckDelivered newAck s sNext ∨ GrantHorizon newHorizon s sNext)

    def Spec (h0 nextSent newAck newHorizon : UInt64) : StateMachine WindowState :=
      StateMachine.mk (Init h0) (Next nextSent newAck newHorizon)

    theorem init_establishes_inv (h0 : UInt64) (s : WindowState)
        (hInit : Init h0 s) : CreditWindowSafetyInv s :=
      let h00 : Nat.le (UInt64.toNat 0) (UInt64.toNat 0) := Nat.le_refl (UInt64.toNat 0)
      let hAckSent1 : Nat.le (UInt64.toNat s.ackedSeq) (UInt64.toNat 0) :=
        Eq.mpr (congrArg (fun a => Nat.le (UInt64.toNat a) (UInt64.toNat 0)) hInit.1) h00
      let hAckSent : Nat.le (UInt64.toNat s.ackedSeq) (UInt64.toNat s.sentSeq) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat s.ackedSeq) (UInt64.toNat x)) hInit.2.1) hAckSent1
      let h0H : Nat.le (UInt64.toNat 0) (UInt64.toNat s.creditHorizon) :=
        Nat.zero_le (UInt64.toNat s.creditHorizon)
      let hSentHor : Nat.le (UInt64.toNat s.sentSeq) (UInt64.toNat s.creditHorizon) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.creditHorizon)) hInit.2.1) h0H
      And.intro hAckSent hSentHor

    theorem sendBatch_preserves_inv (nextSent : UInt64) (s sNext : WindowState)
        (hInv : CreditWindowSafetyInv s) (hAct : SendBatch nextSent s sNext) :
        CreditWindowSafetyInv sNext :=
      let hSentMono : Nat.le (UInt64.toNat s.sentSeq)
          (UInt64.toNat (_root_.credit_horizon_monotone s.sentSeq nextSent)) :=
        credit_horizon_ge_cur s.sentSeq nextSent
      let hAckLeNewSent : Nat.le (UInt64.toNat s.ackedSeq)
          (UInt64.toNat (_root_.credit_horizon_monotone s.sentSeq nextSent)) :=
        Nat.le_trans hInv.1 hSentMono
      let hAck1 : Nat.le (UInt64.toNat sNext.ackedSeq)
          (UInt64.toNat (_root_.credit_horizon_monotone s.sentSeq nextSent)) :=
        Eq.mpr (congrArg (fun a => Nat.le (UInt64.toNat a) (UInt64.toNat (_root_.credit_horizon_monotone s.sentSeq nextSent))) hAct.2.1) hAckLeNewSent
      let hAckSent : Nat.le (UInt64.toNat sNext.ackedSeq) (UInt64.toNat sNext.sentSeq) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat sNext.ackedSeq) (UInt64.toNat x)) hAct.2.2.1) hAck1
      let hLub : Nat.le (UInt64.toNat (_root_.credit_horizon_monotone s.sentSeq nextSent))
          (UInt64.toNat s.creditHorizon) :=
        credit_horizon_lub s.sentSeq nextSent s.creditHorizon hInv.2 hAct.1
      let hSent1 : Nat.le (UInt64.toNat sNext.sentSeq) (UInt64.toNat s.creditHorizon) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.creditHorizon)) hAct.2.2.1) hLub
      let hSentHor : Nat.le (UInt64.toNat sNext.sentSeq) (UInt64.toNat sNext.creditHorizon) :=
        Eq.mpr (congrArg (fun h => Nat.le (UInt64.toNat sNext.sentSeq) (UInt64.toNat h)) hAct.2.2.2) hSent1
      And.intro hAckSent hSentHor

    theorem ackDelivered_preserves_inv (newAck : UInt64) (s sNext : WindowState)
        (hInv : CreditWindowSafetyInv s) (hAct : AckDelivered newAck s sNext) :
        CreditWindowSafetyInv sNext :=
      let hLub : Nat.le (UInt64.toNat (_root_.replica_ack_monotone s.ackedSeq newAck))
          (UInt64.toNat s.sentSeq) :=
        replica_ack_lub s.ackedSeq newAck s.sentSeq hInv.1 hAct.1
      let hAck1 : Nat.le (UInt64.toNat sNext.ackedSeq) (UInt64.toNat s.sentSeq) :=
        Eq.mpr (congrArg (fun a => Nat.le (UInt64.toNat a) (UInt64.toNat s.sentSeq)) hAct.2.1) hLub
      let hAckSent : Nat.le (UInt64.toNat sNext.ackedSeq) (UInt64.toNat sNext.sentSeq) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat sNext.ackedSeq) (UInt64.toNat x)) hAct.2.2.1) hAck1
      let hSent1 : Nat.le (UInt64.toNat sNext.sentSeq) (UInt64.toNat s.creditHorizon) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat s.creditHorizon)) hAct.2.2.1) hInv.2
      let hSentHor : Nat.le (UInt64.toNat sNext.sentSeq) (UInt64.toNat sNext.creditHorizon) :=
        Eq.mpr (congrArg (fun h => Nat.le (UInt64.toNat sNext.sentSeq) (UInt64.toNat h)) hAct.2.2.2) hSent1
      And.intro hAckSent hSentHor

    theorem grantHorizon_preserves_inv (newHorizon : UInt64) (s sNext : WindowState)
        (hInv : CreditWindowSafetyInv s) (hAct : GrantHorizon newHorizon s sNext) :
        CreditWindowSafetyInv sNext :=
      let hAck1 : Nat.le (UInt64.toNat sNext.ackedSeq) (UInt64.toNat s.sentSeq) :=
        Eq.mpr (congrArg (fun a => Nat.le (UInt64.toNat a) (UInt64.toNat s.sentSeq)) hAct.1) hInv.1
      let hAckSent : Nat.le (UInt64.toNat sNext.ackedSeq) (UInt64.toNat sNext.sentSeq) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat sNext.ackedSeq) (UInt64.toNat x)) hAct.2.1) hAck1
      let hHorMono : Nat.le (UInt64.toNat s.creditHorizon)
          (UInt64.toNat (_root_.credit_horizon_monotone s.creditHorizon newHorizon)) :=
        credit_horizon_ge_cur s.creditHorizon newHorizon
      let hSentLeNewHor : Nat.le (UInt64.toNat s.sentSeq)
          (UInt64.toNat (_root_.credit_horizon_monotone s.creditHorizon newHorizon)) :=
        Nat.le_trans hInv.2 hHorMono
      let hSent1 : Nat.le (UInt64.toNat sNext.sentSeq)
          (UInt64.toNat (_root_.credit_horizon_monotone s.creditHorizon newHorizon)) :=
        Eq.mpr (congrArg (fun x => Nat.le (UInt64.toNat x) (UInt64.toNat (_root_.credit_horizon_monotone s.creditHorizon newHorizon))) hAct.2.1) hSentLeNewHor
      let hSentHor : Nat.le (UInt64.toNat sNext.sentSeq) (UInt64.toNat sNext.creditHorizon) :=
        Eq.mpr (congrArg (fun h => Nat.le (UInt64.toNat sNext.sentSeq) (UInt64.toNat h)) hAct.2.2) hSent1
      And.intro hAckSent hSentHor

    theorem next_preserves_inv (nextSent newAck newHorizon : UInt64)
        (s sNext : WindowState)
        (hInv : CreditWindowSafetyInv s)
        (hNext : Next nextSent newAck newHorizon s sNext) :
        CreditWindowSafetyInv sNext :=
      Or.elim hNext
        (fun hSend => sendBatch_preserves_inv nextSent s sNext hInv hSend)
        (fun hRest =>
          Or.elim hRest
            (fun hAck => ackDelivered_preserves_inv newAck s sNext hInv hAck)
            (fun hGrant => grantHorizon_preserves_inv newHorizon s sNext hInv hGrant))

    -- Full TLA+ Temporal Safety Theorem:
    --   `(Spec h0 nextSent newAck newHorizon) ⊨ □ (Lift CreditWindowSafetyInv)`
    theorem spec_satisfies_credit_window_safety (h0 nextSent newAck newHorizon : UInt64) :
        (Spec h0 nextSent newAck newHorizon) ⊨ □ (Lift CreditWindowSafetyInv) :=
      invariantSatisfies (Spec h0 nextSent newAck newHorizon) CreditWindowSafetyInv
        (init_establishes_inv h0)
        (next_preserves_inv nextSent newAck newHorizon)

    end TlaCreditFlowWindow
    end Broker
    end Astream
}
