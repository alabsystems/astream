// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

// The Clean island for cross-broker federation (`ROADMAP.md` & `DESIGN-aterm-fabric`
// Federation across brokers), mounted under `cfg(clean_islands)` in `federation.rs`.
// Proves that `federation_cursor_advance` and `federation_seq_clamp` maintain monotone
// source cursor progression and keep mirrored producer sequences strictly below the
// reserved ack-sequence half (`seq <= max_seq`), and that a push edge never has its group
// resume past a record it carries that nobody answered or reported (`TlaPushEdge.NoSkip`).
clean {
    -- ========================================================================
    -- 1. Clean-Origin Rust Implementation Functions (`clean_origin_mir` I5)
    -- ========================================================================
    def federation_cursor_advance (cur_cursor : UInt64) (next_cursor : UInt64) : UInt64 :=
      if cur_cursor < next_cursor then next_cursor else cur_cursor

    def federation_seq_clamp (src_offset : UInt64) (max_seq : UInt64) : UInt64 :=
      if src_offset < max_seq then src_offset else max_seq

    -- Where a push bridge has its group resume after a burst (`FederationBridge::finish_burst`,
    -- through `Client::commit_before`, the one place the exclusive end becomes the inclusive
    -- commit): the burst's scan, or the lowest record held back for an origin the destination
    -- does not take yet, whichever is lower. `TlaPushEdge` proves no resume at it skips a record.
    def federation_commit_bound (upto : UInt64) (held : UInt64) : UInt64 :=
      if upto < held then upto else held

    -- ========================================================================
    -- 2. TLA+ State-Machine Specification (Astream.Broker.TlaFederationBridge)
    -- ========================================================================
    namespace Astream
    namespace Broker
    namespace TlaFederationBridge

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

    notation:50 M " ⊨ " F:50 => _root_.Astream.Broker.TlaFederationBridge.Satisfies M F
    prefix:75 "□" => _root_.Astream.Broker.TlaFederationBridge.Always

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

    structure FederationState where
      startCursor : UInt64
      cursor      : UInt64
      seq         : UInt64
      maxSeq      : UInt64

    def FederationInv (s : FederationState) : Prop :=
      Nat.le (UInt64.toNat s.startCursor) (UInt64.toNat s.cursor) ∧
      Nat.le (UInt64.toNat s.seq) (UInt64.toNat s.maxSeq)

    def Init (s : FederationState) : Prop :=
      s.startCursor = s.cursor ∧ s.seq = s.maxSeq

    def mirrorStepAction (candCursor : UInt64) (srcOff : UInt64)
        (s sNext : FederationState) : Prop :=
      sNext.startCursor = s.startCursor ∧
      sNext.maxSeq = s.maxSeq ∧
      sNext.cursor = _root_.federation_cursor_advance s.cursor candCursor ∧
      sNext.seq = _root_.federation_seq_clamp srcOff s.maxSeq

    def Next (s sNext : FederationState) : Prop :=
      ∃ candCursor : UInt64, ∃ srcOff : UInt64,
        mirrorStepAction candCursor srcOff s sNext

    def Spec : StateMachine FederationState :=
      StateMachine.mk Init Next

    theorem cursor_advance_ge_cur : forall (cur : UInt64) (cand : UInt64),
        Nat.le (UInt64.toNat cur) (UInt64.toNat (_root_.federation_cursor_advance cur cand)) :=
      fun cur cand => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt cur cand)) =>
          Nat.le (UInt64.toNat cur) (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => cur) (fun _ => cand))))
        (instDecidableUInt64Lt cur cand)
        (fun _ => Nat.le.refl (UInt64.toNat cur))
        (fun hLt => Nat.le_of_lt hLt)

    theorem seq_clamp_le_max : forall (src : UInt64) (maxSeq : UInt64),
        Nat.le (UInt64.toNat (_root_.federation_seq_clamp src maxSeq)) (UInt64.toNat maxSeq) :=
      fun src maxSeq => Decidable.casesOn
        (motive := fun (d : Decidable (LT.lt src maxSeq)) =>
          Nat.le (UInt64.toNat (Decidable.casesOn
            (motive := fun _ => UInt64) d (fun _ => maxSeq) (fun _ => src))) (UInt64.toNat maxSeq))
        (instDecidableUInt64Lt src maxSeq)
        (fun _ => Nat.le.refl (UInt64.toNat maxSeq))
        (fun hLt => Nat.le_of_lt hLt)

    theorem uint64_eq_le (a b : UInt64) (hEq : a = b) :
        Nat.le (UInt64.toNat a) (UInt64.toNat b) :=
      Eq.mpr
        (congrArg (fun (x : UInt64) => Nat.le (UInt64.toNat x) (UInt64.toNat b)) hEq)
        (Nat.le.refl (UInt64.toNat b))

    theorem init_establishes_inv (s : FederationState) (hInit : Init s) :
        FederationInv s :=
      And.intro
        (uint64_eq_le s.startCursor s.cursor hInit.1)
        (uint64_eq_le s.seq s.maxSeq hInit.2)

    theorem next_preserves_inv (s sNext : FederationState)
        (hInv : FederationInv s) (hNext : Next s sNext) :
        FederationInv sNext :=
      Exists.elim hNext (fun candCursor h1 =>
        Exists.elim h1 (fun srcOff hAct =>
          let hEqStart : sNext.startCursor = s.startCursor := hAct.1
          let hEqMax : sNext.maxSeq = s.maxSeq := hAct.2.1
          let hEqCur : sNext.cursor = _root_.federation_cursor_advance s.cursor candCursor := hAct.2.2.1
          let hEqSeq : sNext.seq = _root_.federation_seq_clamp srcOff s.maxSeq := hAct.2.2.2
          let hCurGrow : Nat.le (UInt64.toNat s.cursor) (UInt64.toNat (_root_.federation_cursor_advance s.cursor candCursor)) :=
            cursor_advance_ge_cur s.cursor candCursor
          let hStartBound : Nat.le (UInt64.toNat s.startCursor) (UInt64.toNat (_root_.federation_cursor_advance s.cursor candCursor)) :=
            Nat.le_trans hInv.1 hCurGrow
          let hSeqBound : Nat.le (UInt64.toNat (_root_.federation_seq_clamp srcOff s.maxSeq)) (UInt64.toNat s.maxSeq) :=
            seq_clamp_le_max srcOff s.maxSeq
          And.intro
            (Eq.mpr
              (congrArg (fun (st : UInt64) => Nat.le (UInt64.toNat st) (UInt64.toNat sNext.cursor)) hEqStart)
              (Eq.mpr
                (congrArg (fun (c : UInt64) => Nat.le (UInt64.toNat s.startCursor) (UInt64.toNat c)) hEqCur)
                hStartBound))
            (Eq.mpr
              (congrArg (fun (sq : UInt64) => Nat.le (UInt64.toNat sq) (UInt64.toNat sNext.maxSeq)) hEqSeq)
              (Eq.mpr
                (congrArg (fun (mx : UInt64) => Nat.le (UInt64.toNat (_root_.federation_seq_clamp srcOff s.maxSeq)) (UInt64.toNat mx)) hEqMax)
                hSeqBound))))

    theorem spec_satisfies_federation_bridge_safety :
        Spec ⊨ □ (Lift FederationInv) :=
      invariantSatisfies Spec FederationInv init_establishes_inv next_preserves_inv

    end TlaFederationBridge

    -- ========================================================================
    -- 3. One push edge, for every log, burst, held-back record, retention gap, crash and resume
    --    (Astream.Broker.TlaPushEdge), on TlaFederationBridge's temporal prelude
    -- ========================================================================
    -- A source log of `len` offsets, `data o` when offset `o` holds a record the edge carries (a
    -- group commit, a mark, a hidden subject, one outside the bridge's `carry` filters or one the
    -- rewrite drops does not; an edge that follows its group over several lanes carries their
    -- union, so it is one edge here, where two bridges on one group would be two edges sharing one
    -- `resumeAt`, which this model does not admit: either one's commit could pass the other's
    -- records), where the group
    -- resumes (`resumeAt`, the broker's `group_start`: one past its inclusive commit, and `from_`
    -- before this edge's first, as a relay that starts at the head commits it), and the bridge's
    -- runs. A run scans from `resumeAt`; the destination answers each carried record for good
    -- (appended, already held, refused for good) or the bridge holds it back (an origin the
    -- destination does not take yet); a held record is answered later or let go; retention may cut
    -- what a run has not scanned, which the bridge reports (`told`); a run may end at any step. A
    -- commit is `commit_before(group, federation_commit_bound(scanned, lowest held))`: the group
    -- resumes at the bound, or stays where it was if that is higher (`group_commit_monotone`), and
    -- its record lands at the head.
    namespace TlaPushEdge

    structure Edge where
      len      : Nat
      data     : Nat → Bool
      resumeAt : Nat
      live     : Bool
      pos      : Nat
      answered : Nat → Bool
      held     : Nat → Bool
      told     : Nat → Bool
      from_    : Nat

    def maxN (a b : Nat) : Nat := if a < b then b else a

    def land (d : Bool) (e : Edge) : Edge :=
      { e with len := e.len + 1, data := fun o => if o = e.len then d else e.data o }

    def Init (e : Edge) : Prop :=
      e.resumeAt = e.from_ ∧ e.from_ ≤ e.len ∧ e.live = false ∧ (∀ o, e.held o = false)

    def Land (e e' : Edge) : Prop := ∃ d, e' = land d e

    def DeliverAnswered (e e' : Edge) : Prop :=
      e.live = true ∧ e.pos < e.len ∧ e.data e.pos = true ∧
      e' = { e with pos := e.pos + 1, answered := fun o => if o = e.pos then true else e.answered o }

    def DeliverHeld (e e' : Edge) : Prop :=
      e.live = true ∧ e.pos < e.len ∧ e.data e.pos = true ∧
      e' = { e with pos := e.pos + 1, held := fun o => if o = e.pos then true else e.held o }

    def Skip (e e' : Edge) : Prop :=
      e.live = true ∧ e.pos < e.len ∧ e.data e.pos = false ∧ e' = { e with pos := e.pos + 1 }

    def Release (x : Nat) (e e' : Edge) : Prop :=
      e.live = true ∧ e.held x = true ∧
      e' = { e with held := fun o => if o = x then false else e.held o,
                    answered := fun o => if o = x then true else e.answered o }

    def Gap (b : Nat) (e e' : Edge) : Prop :=
      e.live = true ∧ e.pos ≤ b ∧ b ≤ e.len ∧
      e' = { e with pos := b, told := fun o => if e.pos ≤ o ∧ o < b then true else e.told o }

    -- `u` is the scan (no record at or past it delivered yet: `u ≤ pos`), `h` at or below every
    -- record held; the shipped bridge passes the lowest held, or MAX with none.
    def Commit (e e' : Edge) : Prop :=
      e.live = true ∧
      ∃ u h : UInt64,
        UInt64.toNat u ≤ e.pos ∧ (∀ o, e.held o = true → UInt64.toNat h ≤ o) ∧
        e' = land false { e with resumeAt :=
          maxN e.resumeAt (UInt64.toNat (_root_.federation_commit_bound u h)) }

    def End (e e' : Edge) : Prop :=
      e.live = true ∧ e' = { e with live := false, held := fun _ => false }

    def Resume (e e' : Edge) : Prop :=
      e.live = false ∧ e' = { e with live := true, pos := e.resumeAt }

    -- Every action but the commit, which the negative controls replace.
    def NextWith (C : Edge → Edge → Prop) (e e' : Edge) : Prop :=
      Land e e' ∨ DeliverAnswered e e' ∨ DeliverHeld e e' ∨ Skip e e' ∨
      (∃ x, Release x e e') ∨ (∃ b, Gap b e e') ∨ C e e' ∨ End e e' ∨ Resume e e'

    def SpecWith (C : Edge → Edge → Prop) : TlaFederationBridge.StateMachine Edge :=
      TlaFederationBridge.StateMachine.mk Init (NextWith C)

    def Spec : TlaFederationBridge.StateMachine Edge := SpecWith Commit

    -- A carried record the destination answered, or one retention took that the bridge reported.
    def Covered (e : Edge) (o : Nat) : Prop := e.answered o = true ∨ e.told o = true

    -- The law: every carried record below where the group resumes is covered, and while a run
    -- lives every one it scanned is covered or held. So a run that resumes skips nothing.
    def NoSkip (e : Edge) : Prop :=
      (e.from_ ≤ e.resumeAt ∧ e.resumeAt ≤ e.len ∧
        ∀ o, e.from_ ≤ o → o < e.resumeAt → e.data o = true → Covered e o) ∧
      (e.live = true → e.from_ ≤ e.pos ∧ e.pos ≤ e.len ∧
        ∀ o, e.from_ ≤ o → o < e.pos → e.data o = true → Covered e o ∨ e.held o = true) ∧
      (e.live = false → ∀ o, e.held o = false)

    -- Arithmetic on plain variables (Clean's omega reads no structure projection).
    theorem ar_lt_lt_le (o p l : Nat) (h1 : o < p) (h2 : p ≤ l) : o < l := by omega
    theorem ar_ne_of_lt (o l : Nat) (h : o < l) (heq : o = l) : False :=
      Nat.lt_irrefl l (Eq.mp (congrArg (fun x => x < l) heq) h)
    theorem ar_lt_ne (o p : Nat) (h1 : o < p + 1) (h2 : Not (o = p)) : o < p := by omega
    theorem ar_le_succ (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by omega
    theorem ar_succ_le (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega
    theorem ar_not_le_lt (o p : Nat) (h : Not (p ≤ o)) : o < p := by omega
    theorem ar_le_le (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by omega
    theorem ar_chain_held (o b h : Nat) (h1 : o < b) (h2 : b ≤ h) (h3 : h ≤ o) : False := by omega
    theorem ar_lt_le_lt (o b u p : Nat) (h1 : o < b) (h2 : b ≤ u) (h3 : u ≤ p) : o < p := by omega
    theorem ar_le_le_le (b u p l : Nat) (h2 : b ≤ u) (h3 : u ≤ p) (h4 : p ≤ l) : b ≤ l := by omega
    theorem true_ne_false (h : true = false) : False := by cases h

    theorem max_cases (a b : Nat) : maxN a b = a ∨ maxN a b = b :=
      if h : a < b then Or.inr (if_pos h) else Or.inl (if_neg h)
    theorem le_maxN (a b : Nat) : a ≤ maxN a b :=
      if h : a < b then Eq.mpr (congrArg (fun y => a ≤ y) (if_pos h)) (Nat.le_of_lt h)
      else Eq.mpr (congrArg (fun y => a ≤ y) (if_neg h)) (Nat.le_refl a)

    -- The kernel's meaning: the bound is at or below both the scan and the lowest record held.
    theorem bound_le_upto (u h : UInt64) :
        UInt64.toNat (_root_.federation_commit_bound u h) ≤ UInt64.toNat u := by
      unfold federation_commit_bound
      by_cases hl : u < h
      · rw [if_pos hl]; exact Nat.le_refl _
      · rw [if_neg hl]; exact Nat.le_of_not_lt hl

    theorem bound_le_held (u h : UInt64) :
        UInt64.toNat (_root_.federation_commit_bound u h) ≤ UInt64.toNat h := by
      unfold federation_commit_bound
      by_cases hl : u < h
      · rw [if_pos hl]; exact Nat.le_of_lt hl
      · rw [if_neg hl]; exact Nat.le_refl _

    theorem covered_answer (e : Edge) (x o : Nat) (hc : Covered e o) :
        Covered { e with answered := fun y => if y = x then true else e.answered y } o :=
      Or.elim hc
        (fun ha => Or.inl (if hox : o = x then if_pos hox else Eq.trans (if_neg hox) ha))
        (fun ht => Or.inr ht)

    theorem init_inv (e : Edge) (h : Init e) : NoSkip e :=
      And.intro
        (And.intro (Eq.mpr (congrArg (fun y => e.from_ ≤ y) h.1) (Nat.le_refl e.from_))
          (And.intro (Eq.mpr (congrArg (fun y => y ≤ e.len) h.1) h.2.1)
            (fun o hf ho _ => False.elim (Nat.lt_irrefl o
              (Nat.lt_of_lt_of_le ho (Eq.mpr (congrArg (fun y => y ≤ o) h.1) hf))))))
        (And.intro
          (fun hl => False.elim (true_ne_false (Eq.trans hl.symm h.2.2.1)))
          (fun _ o => h.2.2.2 o))

    theorem land_inv (d : Bool) (e : Edge) (hi : NoSkip e) : NoSkip (land d e) :=
      And.intro
        (And.intro hi.1.1 (And.intro (ar_le_succ e.resumeAt e.len hi.1.2.1)
          (fun o hf ho hd =>
            have hne : Not (o = e.len) := ar_ne_of_lt o e.len (ar_lt_lt_le o e.resumeAt e.len ho hi.1.2.1)
            hi.1.2.2 o hf ho (Eq.trans (if_neg hne).symm hd))))
        (And.intro
          (fun hl =>
            have h2 := hi.2.1 hl
            And.intro h2.1 (And.intro (ar_le_succ e.pos e.len h2.2.1)
              (fun o hf ho hd =>
                have hne : Not (o = e.len) := ar_ne_of_lt o e.len (ar_lt_lt_le o e.pos e.len ho h2.2.1)
                h2.2.2 o hf ho (Eq.trans (if_neg hne).symm hd))))
          (fun hl o => hi.2.2 hl o))

    theorem deliverAnswered_inv (e : Edge) (hi : NoSkip e) (hl : e.live = true) (hp : e.pos < e.len) :
        NoSkip { e with pos := e.pos + 1, answered := fun o => if o = e.pos then true else e.answered o } :=
      have h2 := hi.2.1 hl
      And.intro
        (And.intro hi.1.1 (And.intro hi.1.2.1 (fun o hf ho hd => covered_answer e e.pos o (hi.1.2.2 o hf ho hd))))
        (And.intro
          (fun _ =>
            And.intro (ar_le_succ e.from_ e.pos h2.1) (And.intro (ar_succ_le e.pos e.len hp)
              (fun o hf ho hd =>
                if hop : o = e.pos then Or.inl (Or.inl (if_pos hop))
                else
                  Or.elim (h2.2.2 o hf (ar_lt_ne o e.pos ho hop) hd)
                    (fun hc => Or.inl (covered_answer e e.pos o hc))
                    (fun hh => Or.inr hh))))
          (fun hl2 _ => False.elim (true_ne_false (Eq.trans hl.symm hl2))))

    theorem deliverHeld_inv (e : Edge) (hi : NoSkip e) (hl : e.live = true) (hp : e.pos < e.len) :
        NoSkip { e with pos := e.pos + 1, held := fun o => if o = e.pos then true else e.held o } :=
      have h2 := hi.2.1 hl
      And.intro hi.1
        (And.intro
          (fun _ =>
            And.intro (ar_le_succ e.from_ e.pos h2.1) (And.intro (ar_succ_le e.pos e.len hp)
              (fun o hf ho hd =>
                if hop : o = e.pos then Or.inr (if_pos hop)
                else
                  Or.elim (h2.2.2 o hf (ar_lt_ne o e.pos ho hop) hd)
                    (fun hc => Or.inl hc)
                    (fun hh => Or.inr (Eq.trans (if_neg hop) hh)))))
          (fun hl2 _ => False.elim (true_ne_false (Eq.trans hl.symm hl2))))

    theorem skip_inv (e : Edge) (hi : NoSkip e) (hl : e.live = true) (hp : e.pos < e.len)
        (hd0 : e.data e.pos = false) : NoSkip { e with pos := e.pos + 1 } :=
      have h2 := hi.2.1 hl
      And.intro hi.1
        (And.intro
          (fun _ =>
            And.intro (ar_le_succ e.from_ e.pos h2.1) (And.intro (ar_succ_le e.pos e.len hp)
              (fun o hf ho hd =>
                if hop : o = e.pos then
                  False.elim (true_ne_false (Eq.trans (Eq.trans hd.symm (congrArg e.data hop)) hd0))
                else
                  h2.2.2 o hf (ar_lt_ne o e.pos ho hop) hd)))
          (fun hl2 _ => False.elim (true_ne_false (Eq.trans hl.symm hl2))))

    theorem release_inv (x : Nat) (e : Edge) (hi : NoSkip e) (hl : e.live = true) :
        NoSkip { e with held := fun o => if o = x then false else e.held o,
                        answered := fun o => if o = x then true else e.answered o } :=
      have h2 := hi.2.1 hl
      And.intro
        (And.intro hi.1.1 (And.intro hi.1.2.1 (fun o hf ho hd => covered_answer e x o (hi.1.2.2 o hf ho hd))))
        (And.intro
          (fun _ =>
            And.intro h2.1 (And.intro h2.2.1
              (fun o hf ho hd =>
                if hox : o = x then Or.inl (Or.inl (if_pos hox))
                else
                  Or.elim (h2.2.2 o hf ho hd)
                    (fun hc => Or.inl (covered_answer e x o hc))
                    (fun hh => Or.inr (Eq.trans (if_neg hox) hh)))))
          (fun hl2 _ => False.elim (true_ne_false (Eq.trans hl.symm hl2))))

    theorem gap_inv (b : Nat) (e : Edge) (hi : NoSkip e) (hl : e.live = true)
        (hpb : e.pos ≤ b) (hbl : b ≤ e.len) :
        NoSkip { e with pos := b, told := fun o => if e.pos ≤ o ∧ o < b then true else e.told o } :=
      have h2 := hi.2.1 hl
      have mono : ∀ o, Covered e o →
          Covered { e with pos := b, told := fun o => if e.pos ≤ o ∧ o < b then true else e.told o } o :=
        fun o hc => Or.elim hc (fun ha => Or.inl ha)
          (fun ht => Or.inr (if hr : e.pos ≤ o ∧ o < b then if_pos hr else Eq.trans (if_neg hr) ht))
      And.intro
        (And.intro hi.1.1 (And.intro hi.1.2.1 (fun o hf ho hd => mono o (hi.1.2.2 o hf ho hd))))
        (And.intro
          (fun _ =>
            And.intro (ar_le_le e.from_ e.pos b h2.1 hpb) (And.intro hbl
              (fun o hf ho hd =>
                if hlo : e.pos ≤ o then Or.inl (Or.inr (if_pos (And.intro hlo ho)))
                else
                  Or.elim (h2.2.2 o hf (ar_not_le_lt o e.pos hlo) hd)
                    (fun hc => Or.inl (mono o hc))
                    (fun hh => Or.inr hh))))
          (fun hl2 _ => False.elim (true_ne_false (Eq.trans hl.symm hl2))))

    theorem commit_inv (e : Edge) (hi : NoSkip e) (hl : e.live = true) (u h : UInt64)
        (hu : UInt64.toNat u ≤ e.pos) (hh : ∀ o, e.held o = true → UInt64.toNat h ≤ o) :
        NoSkip { e with resumeAt := maxN e.resumeAt (UInt64.toNat (_root_.federation_commit_bound u h)) } :=
      have h2 := hi.2.1 hl
      have hbu := bound_le_upto u h
      have hbh := bound_le_held u h
      have newSound : e.from_ ≤ UInt64.toNat (_root_.federation_commit_bound u h) →
          UInt64.toNat (_root_.federation_commit_bound u h) ≤ e.len ∧
          ∀ o, e.from_ ≤ o → o < UInt64.toNat (_root_.federation_commit_bound u h) →
            e.data o = true → Covered e o :=
        fun _ => And.intro
          (ar_le_le_le (UInt64.toNat (_root_.federation_commit_bound u h)) (UInt64.toNat u) e.pos e.len
            hbu hu h2.2.1)
          (fun o hf ho hd =>
            Or.elim (h2.2.2 o hf (ar_lt_le_lt o (UInt64.toNat (_root_.federation_commit_bound u h))
                (UInt64.toNat u) e.pos ho hbu hu) hd)
              (fun hc => hc)
              (fun hheld => False.elim (ar_chain_held o (UInt64.toNat (_root_.federation_commit_bound u h))
                (UInt64.toNat h) ho hbh (hh o hheld))))
      have hmax : e.resumeAt ≤ maxN e.resumeAt (UInt64.toNat (_root_.federation_commit_bound u h)) :=
        le_maxN _ _
      And.intro
        (Or.elim (max_cases e.resumeAt (UInt64.toNat (_root_.federation_commit_bound u h)))
          (fun hm => Eq.mpr (congrArg (fun y => e.from_ ≤ y ∧ y ≤ e.len ∧
              ∀ o, e.from_ ≤ o → o < y → e.data o = true → Covered e o) hm) hi.1)
          (fun hm =>
            have hfb : e.from_ ≤ UInt64.toNat (_root_.federation_commit_bound u h) :=
              ar_le_le e.from_ e.resumeAt _ hi.1.1 (Eq.mp (congrArg (fun y => e.resumeAt ≤ y) hm) hmax)
            Eq.mpr (congrArg (fun y => e.from_ ≤ y ∧ y ≤ e.len ∧
              ∀ o, e.from_ ≤ o → o < y → e.data o = true → Covered e o) hm)
              (And.intro hfb (newSound hfb))))
        (And.intro (fun _ => h2) (fun hl2 _ => False.elim (true_ne_false (Eq.trans hl.symm hl2))))

    theorem end_inv (e : Edge) (hi : NoSkip e) :
        NoSkip { e with live := false, held := fun _ => false } :=
      And.intro hi.1 (And.intro (fun hl2 => False.elim (true_ne_false hl2.symm)) (fun _ _ => rfl))

    theorem resume_inv (e : Edge) (hi : NoSkip e) :
        NoSkip { e with live := true, pos := e.resumeAt } :=
      And.intro hi.1
        (And.intro
          (fun _ => And.intro hi.1.1 (And.intro hi.1.2.1
            (fun o hf ho hd => Or.inl (hi.1.2.2 o hf ho hd))))
          (fun hl2 _ => False.elim (true_ne_false hl2)))

    -- One lemma per action keeps elaboration to a few seconds.
    theorem land_step (e e' : Edge) (hi : NoSkip e) (h : Land e e') : NoSkip e' :=
      Exists.elim h (fun d hd => Eq.mpr (congrArg NoSkip hd) (land_inv d e hi))
    theorem deliverAnswered_step (e e' : Edge) (hi : NoSkip e) (h : DeliverAnswered e e') : NoSkip e' :=
      Eq.mpr (congrArg NoSkip h.2.2.2) (deliverAnswered_inv e hi h.1 h.2.1)
    theorem deliverHeld_step (e e' : Edge) (hi : NoSkip e) (h : DeliverHeld e e') : NoSkip e' :=
      Eq.mpr (congrArg NoSkip h.2.2.2) (deliverHeld_inv e hi h.1 h.2.1)
    theorem skip_step (e e' : Edge) (hi : NoSkip e) (h : Skip e e') : NoSkip e' :=
      Eq.mpr (congrArg NoSkip h.2.2.2) (skip_inv e hi h.1 h.2.1 h.2.2.1)
    theorem release_step (e e' : Edge) (hi : NoSkip e) (h : ∃ x, Release x e e') : NoSkip e' :=
      Exists.elim h (fun x hx => Eq.mpr (congrArg NoSkip hx.2.2) (release_inv x e hi hx.1))
    theorem gap_step (e e' : Edge) (hi : NoSkip e) (h : ∃ b, Gap b e e') : NoSkip e' :=
      Exists.elim h (fun b hb => Eq.mpr (congrArg NoSkip hb.2.2.2) (gap_inv b e hi hb.1 hb.2.1 hb.2.2.1))
    theorem commit_step (e e' : Edge) (hi : NoSkip e) (h : Commit e e') : NoSkip e' :=
      Exists.elim h.2 (fun u h1 => Exists.elim h1 (fun hb h3 =>
        Eq.mpr (congrArg NoSkip h3.2.2) (land_inv false _ (commit_inv e hi h.1 u hb h3.1 h3.2.1))))
    theorem end_step (e e' : Edge) (hi : NoSkip e) (h : End e e') : NoSkip e' :=
      Eq.mpr (congrArg NoSkip h.2) (end_inv e hi)
    theorem resume_step (e e' : Edge) (hi : NoSkip e) (h : Resume e e') : NoSkip e' :=
      Eq.mpr (congrArg NoSkip h.2) (resume_inv e hi)

    theorem next_inv (e e' : Edge) (hi : NoSkip e) (hn : NextWith Commit e e') : NoSkip e' :=
      Or.elim hn (land_step e e' hi) (fun h1 =>
      Or.elim h1 (deliverAnswered_step e e' hi) (fun h2 =>
      Or.elim h2 (deliverHeld_step e e' hi) (fun h3 =>
      Or.elim h3 (skip_step e e' hi) (fun h4 =>
      Or.elim h4 (release_step e e' hi) (fun h5 =>
      Or.elim h5 (gap_step e e' hi) (fun h6 =>
      Or.elim h6 (commit_step e e' hi) (fun h7 =>
      Or.elim h7 (end_step e e' hi) (resume_step e e' hi))))))))

    -- On every source log, through every burst, held-back record, retention gap, commit, crash
    -- and resume, the group never resumes past a carried record nobody answered or reported.
    theorem spec_satisfies_push_edge_no_skip :
        TlaFederationBridge.Satisfies Spec (TlaFederationBridge.Always (TlaFederationBridge.Lift NoSkip)) :=
      TlaFederationBridge.invariantSatisfies Spec NoSkip init_inv next_inv

    -- Negative controls: runs of a mutant Spec that break the law, never rejected declarations.
    def e0 : Edge :=
      { len := 0, data := fun _ => false, resumeAt := 0, live := false, pos := 0,
        answered := fun _ => false, held := fun _ => false, told := fun _ => false, from_ := 0 }

    -- The rule before a2c31169: a burst cut at its cap committed `Burst::next`, the exclusive end,
    -- as if it were inclusive, so the group resumed one past the bound.
    def CommitUpto (e e' : Edge) : Prop :=
      e.live = true ∧
      ∃ u h : UInt64,
        UInt64.toNat u ≤ e.pos ∧ (∀ o, e.held o = true → UInt64.toNat h ≤ o) ∧
        e' = land false { e with resumeAt :=
          maxN e.resumeAt (UInt64.toNat (_root_.federation_commit_bound u h) + 1) }

    -- Two records land; a run delivers the first and is cut at a cap of 1; the old rule has the
    -- group resume at 2, so the record at 1 never goes.
    def u1 : Edge := land true e0
    def u2 : Edge := land true u1
    def u3 : Edge := { u2 with live := true, pos := 0 }
    def u4 : Edge := { u3 with pos := 1, answered := fun o => if o = 0 then true else u3.answered o }
    def u5 : Edge := land false { u4 with resumeAt := 2 }
    def uptoRun : TlaFederationBridge.Behavior Edge
      | 0 => e0 | 1 => u1 | 2 => u2 | 3 => u3 | 4 => u4 | _ => u5

    theorem upto_commit_step : CommitUpto u4 u5 :=
      And.intro rfl (Exists.intro 1 (Exists.intro 18446744073709551615
        (And.intro (by decide) (And.intro (fun _ hh => False.elim (true_ne_false hh.symm)) rfl))))

    theorem upto_run_runs : TlaFederationBridge.Runs (SpecWith CommitUpto) uptoRun :=
      And.intro (And.intro rfl (And.intro (Nat.le_refl 0) (And.intro rfl (fun _ => rfl))))
        (fun n => match n with
          | 0 => Or.inl (Or.inl (Exists.intro true rfl))
          | 1 => Or.inl (Or.inl (Exists.intro true rfl))
          | 2 => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (And.intro rfl rfl)))))))))
          | 3 => Or.inl (Or.inr (Or.inl (And.intro rfl (And.intro (by decide) (And.intro rfl rfl)))))
          | 4 => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl upto_commit_step)))))))
          | _ + 5 => Or.inr rfl)

    theorem uncovered (e : Edge) (o : Nat) (ha : e.answered o = false) (ht : e.told o = false) :
        Not (Covered e o) :=
      fun hc => Or.elim hc (fun h1 => true_ne_false (Eq.trans h1.symm ha))
        (fun h2 => true_ne_false (Eq.trans h2.symm ht))

    theorem u5_breaks_no_skip : Not (NoSkip u5) :=
      fun h => uncovered u5 1 rfl rfl (h.1.2.2 1 (Nat.zero_le 1) (by decide) rfl)

    theorem the_rule_before_a2c31169_breaks_the_law :
        Not (TlaFederationBridge.Satisfies (SpecWith CommitUpto)
          (TlaFederationBridge.Always (TlaFederationBridge.Lift NoSkip))) :=
      fun h => u5_breaks_no_skip (h uptoRun upto_run_runs 5)

    -- A commit blind to what is held: the bound of the scan alone. A record the destination did
    -- not take is held; the group resumes past it, and the run that resumes never offers it.
    def CommitPastHeld (e e' : Edge) : Prop :=
      e.live = true ∧
      ∃ u : UInt64, UInt64.toNat u ≤ e.pos ∧
        e' = land false { e with resumeAt := maxN e.resumeAt (UInt64.toNat u) }

    def p1 : Edge := land true e0
    def p2 : Edge := { p1 with live := true, pos := 0 }
    def p3 : Edge := { p2 with pos := 1, held := fun o => if o = 0 then true else p2.held o }
    def p4 : Edge := land false { p3 with resumeAt := 1 }
    def pastHeldRun : TlaFederationBridge.Behavior Edge
      | 0 => e0 | 1 => p1 | 2 => p2 | 3 => p3 | _ => p4

    theorem past_held_commit_step : CommitPastHeld p3 p4 :=
      And.intro rfl (Exists.intro 1 (And.intro (by decide) rfl))

    theorem past_held_run_runs : TlaFederationBridge.Runs (SpecWith CommitPastHeld) pastHeldRun :=
      And.intro (And.intro rfl (And.intro (Nat.le_refl 0) (And.intro rfl (fun _ => rfl))))
        (fun n => match n with
          | 0 => Or.inl (Or.inl (Exists.intro true rfl))
          | 1 => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  (And.intro rfl rfl)))))))))
          | 2 => Or.inl (Or.inr (Or.inr (Or.inl (And.intro rfl (And.intro (by decide) (And.intro rfl rfl))))))
          | 3 => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl past_held_commit_step)))))))
          | _ + 4 => Or.inr rfl)

    theorem p4_breaks_no_skip : Not (NoSkip p4) :=
      fun h => uncovered p4 0 rfl rfl (h.1.2.2 0 (Nat.le_refl 0) (by decide) rfl)

    theorem a_commit_blind_to_what_is_held_breaks_the_law :
        Not (TlaFederationBridge.Satisfies (SpecWith CommitPastHeld)
          (TlaFederationBridge.Always (TlaFederationBridge.Lift NoSkip))) :=
      fun h => p4_breaks_no_skip (h pastHeldRun past_held_run_runs 4)

    -- The shipped kernel bounds that commit by the record held: the group stays at 0.
    theorem the_kernel_stays_below_a_record_held : _root_.federation_commit_bound 1 0 = 0 := by
      decide

    end TlaPushEdge
    end Broker
    end Astream

    def federation_hop_allowed_isl (hops : UInt8) (max_hops : UInt8) : Bool :=
      decide (hops < max_hops)

    def federation_route_preferred_isl (cur_rtt_us : UInt64) (switch_threshold_us : UInt64) : Bool :=
      decide (switch_threshold_us ≤ cur_rtt_us)

    def federation_incarnation_fresh_isl (observed_inc : UInt64) (min_inc : UInt64) : Bool :=
      decide (min_inc ≤ observed_inc)
}
