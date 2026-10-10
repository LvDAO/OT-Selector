import OTSelector.Feedback.ForcedHistory

/-!
# Deterministic branch extraction at the first feedback tie

This file contains only the finite combinatorial part of the no-tie argument.  A bad step is
unwrapped at its first occurrence, all preceding singleton steps are recorded as a forced history,
and two labels at the bad step are exposed.  No measure-theoretic statement is made here.
-/

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Elementary label extraction -/

theorem exists_labelStepRealizes_of_card_sum_eq_one
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (hone : (state.newSource sample lam).card +
      (state.newTarget sample lam).card = 1) :
    ∃ label : FeedbackLabel n,
      labelStepRealizes sample lam state label := by
  classical
  by_cases hs : (state.newSource sample lam).Nonempty
  · obtain ⟨i, hi⟩ := hs
    have hsource : (state.newSource sample lam).card = 1 := by
      have hpos : 0 < (state.newSource sample lam).card :=
        Finset.card_pos.mpr ⟨i, hi⟩
      omega
    have htarget : (state.newTarget sample lam).card = 0 := by
      omega
    obtain ⟨i, hsi⟩ := Finset.card_eq_one.mp hsource
    refine ⟨Sum.inl i, hsi, Finset.card_eq_zero.mp htarget⟩
  · have hsource : state.newSource sample lam = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hs
    have htarget_card : (state.newTarget sample lam).card = 1 := by
      simpa [hsource] using hone
    obtain ⟨j, htj⟩ := Finset.card_eq_one.mp htarget_card
    refine ⟨Sum.inr j, hsource, htj⟩

/-! ## Labels in a feedback state -/

noncomputable def newLabelSet (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : Finset (FeedbackLabel n) :=
  (state.newSource sample lam).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (state.newTarget sample lam).map ⟨Sum.inr, Sum.inr_injective⟩

theorem mem_newLabelSet_iff (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (label : FeedbackLabel n) :
    label ∈ newLabelSet sample lam state ↔
      match label with
      | Sum.inl i => i ∈ state.newSource sample lam
      | Sum.inr j => j ∈ state.newTarget sample lam := by
  cases label <;> simp [newLabelSet]

theorem exists_distinct_newLabels_of_card_sum_gt_one
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (hcount : 1 < (state.newSource sample lam).card +
      (state.newTarget sample lam).card) :
    ∃ l₁ l₂ : FeedbackLabel n,
      l₁ ∈ newLabelSet sample lam state ∧
      l₂ ∈ newLabelSet sample lam state ∧ l₁ ≠ l₂ := by
  classical
  by_cases hsource : 1 < (state.newSource sample lam).card
  · obtain ⟨i, hi, j, hj, hij⟩ :=
      Finset.one_lt_card.mp hsource
    refine ⟨Sum.inl i, Sum.inl j, ?_, ?_, ?_⟩
    · rw [mem_newLabelSet_iff]
      exact hi
    · rw [mem_newLabelSet_iff]
      exact hj
    · simpa using hij
  · have hsource_le : (state.newSource sample lam).card ≤ 1 :=
      Nat.le_of_not_gt hsource
    by_cases hsource_empty : (state.newSource sample lam).Nonempty
    · have hsource_one : (state.newSource sample lam).card = 1 := by
        have hpos : 0 < (state.newSource sample lam).card :=
          Finset.card_pos.mpr hsource_empty
        omega
      have htarget_pos : 0 < (state.newTarget sample lam).card := by omega
      obtain ⟨i, hi⟩ := hsource_empty
      obtain ⟨j, hj⟩ := Finset.card_pos.mp htarget_pos
      refine ⟨Sum.inl i, Sum.inr j, ?_, ?_, ?_⟩
      · rw [mem_newLabelSet_iff]
        exact hi
      · rw [mem_newLabelSet_iff]
        exact hj
      · simp
    · have hsource_zero : (state.newSource sample lam).card = 0 := by
        rw [Finset.card_eq_zero]
        exact Finset.not_nonempty_iff_eq_empty.mp hsource_empty
      have htarget_two : 1 < (state.newTarget sample lam).card := by omega
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp htarget_two
      refine ⟨Sum.inr i, Sum.inr j, ?_, ?_, ?_⟩
      · rw [mem_newLabelSet_iff]
        exact hi
      · rw [mem_newLabelSet_iff]
        exact hj
      · simpa using hij

theorem labelCoordinate_eq_next_of_mem_newLabelSet
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    {label : FeedbackLabel n} (hlabel : label ∈ newLabelSet sample lam state) :
    state.labelCoordinate sample lam label = state.nextCoordinate sample lam := by
  cases label with
  | inl i =>
      have hi : i ∈ state.newSource sample lam :=
        (mem_newLabelSet_iff sample lam state (Sum.inl i)).mp hlabel
      exact (Finset.mem_filter.mp hi).2
  | inr j =>
      have hj : j ∈ state.newTarget sample lam :=
        (mem_newLabelSet_iff sample lam state (Sum.inr j)).mp hlabel
      exact (Finset.mem_filter.mp hj).2

theorem label_not_mem_history_of_mem_newLabelSet
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (state : FeedbackStepState n)
    (hstate : state = scheduledState sample lam x0 p0 sourcePattern targetPattern history)
    {label : FeedbackLabel n} (hlabel : label ∈ newLabelSet sample lam state) :
    label ∉ history := by
  intro hhistory
  cases label with
  | inl i =>
      have hi : i ∈ state.newSource sample lam :=
        (mem_newLabelSet_iff sample lam state (Sum.inl i)).mp hlabel
      have hi_not : i ∉ state.seenSource := (Finset.mem_sdiff.mp
        (Finset.mem_filter.mp hi).1).2
      have hi_seen : i ∈
          (scheduledState sample lam x0 p0 sourcePattern targetPattern history).seenSource :=
        scheduledState_mem_seenSource_of_mem_history sample lam x0 p0 sourcePattern
          targetPattern history i hhistory
      rw [← hstate] at hi_seen
      exact hi_not (by simpa using hi_seen)
  | inr j =>
      have hj : j ∈ state.newTarget sample lam :=
        (mem_newLabelSet_iff sample lam state (Sum.inr j)).mp hlabel
      have hj_not : j ∉ state.seenTarget := (Finset.mem_sdiff.mp
        (Finset.mem_filter.mp hj).1).2
      have hj_seen : j ∈
          (scheduledState sample lam x0 p0 sourcePattern targetPattern history).seenTarget :=
        scheduledState_mem_seenTarget_of_mem_history sample lam x0 p0 sourcePattern
          targetPattern history j hhistory
      rw [← hstate] at hj_seen
      exact hj_not (by simpa using hj_seen)

/-! ## Empty states remain empty -/

theorem newSource_eq_empty_of_candidates_eq_empty
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (hcand : state.candidates sample lam = ∅) :
    state.newSource sample lam = ∅ := by
  have hseen := (state.candidates_eq_empty_iff sample lam).mp hcand
  simp [FeedbackStepState.newSource, hseen.1]

theorem newTarget_eq_empty_of_candidates_eq_empty
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (hcand : state.candidates sample lam = ∅) :
    state.newTarget sample lam = ∅ := by
  have hseen := (state.candidates_eq_empty_iff sample lam).mp hcand
  simp [FeedbackStepState.newTarget, hseen.2]

theorem feedbackState_eq_of_candidates_eq_empty
    (sample : FiniteSample n) (lam x0 p0 : ℝ) (k : ℕ)
    (hcand : (feedbackState sample lam x0 p0 k).candidates sample lam = ∅)
    (r : ℕ) :
    feedbackState sample lam x0 p0 (k + r) =
      feedbackState sample lam x0 p0 k := by
  induction r with
  | zero => simp
  | succ r ihr =>
      have hdone :
          (feedbackState sample lam x0 p0 (k + r)).candidates sample lam = ∅ := by
        rw [ihr]
        exact hcand
      rw [Nat.add_succ,
        sample.feedbackState_succ_eq_of_candidates_eq_empty lam x0 p0 (k + r) hdone]
      exact ihr

theorem feedbackState_candidates_nonempty_of_bad_later
    (sample : FiniteSample n) (lam x0 p0 : ℝ) {k m : ℕ}
    (hkm : k < m)
    (hbad : ¬ ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
      ((feedbackState sample lam x0 p0 m).newTarget sample lam).card ≤ 1) :
    ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty := by
  by_contra hnonempty
  have hcand : (feedbackState sample lam x0 p0 k).candidates sample lam = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnonempty
  have hstate : feedbackState sample lam x0 p0 m =
      feedbackState sample lam x0 p0 k := by
    simpa [Nat.add_sub_of_le (Nat.le_of_lt hkm)] using
      sample.feedbackState_eq_of_candidates_eq_empty lam x0 p0 k hcand (m - k)
  have hsource := sample.newSource_eq_empty_of_candidates_eq_empty lam
    (feedbackState sample lam x0 p0 k) hcand
  have htarget := sample.newTarget_eq_empty_of_candidates_eq_empty lam
    (feedbackState sample lam x0 p0 k) hcand
  apply hbad
  rw [hstate, hsource, htarget]
  simp

/-! ## Appending one label to a realized forced history -/

theorem ForcedHistoryRealizes.append_singleton
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (history : List (FeedbackLabel n)) (label : FeedbackLabel n)
    (hgood : ForcedHistoryRealizes sample lam state history)
    (hlabel : labelStepRealizes sample lam
      (scheduledStateFrom sample lam state history) label) :
    ForcedHistoryRealizes sample lam state (history ++ [label]) := by
  induction history generalizing state with
  | nil =>
      exact ⟨hlabel, trivial⟩
  | cons head tail ih =>
      have hhead : labelStepRealizes sample lam state head := hgood.1
      have htail : ForcedHistoryRealizes sample lam
          (state.forcedLabelStep sample lam head) tail := hgood.2
      apply And.intro hhead
      apply ih (state := state.forcedLabelStep sample lam head) htail
      simpa [scheduledStateFrom] using hlabel

/-! ## Constructing the singleton history before a bad step -/

theorem exists_forced_history_of_active
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (hinit : sample.initialFeedbackState x0 p0 =
      forcedInitialState x0 p0 sourcePattern targetPattern)
    (m : ℕ)
    (hactive : ∀ k ≤ m,
      ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty)
    (hprior : ∀ k < m,
      ((feedbackState sample lam x0 p0 k).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 k).newTarget sample lam).card ≤ 1) :
    ∃ history : List (FeedbackLabel n),
      history.length = m ∧
      ForcedHistoryRealizes sample lam
        (forcedInitialState x0 p0 sourcePattern targetPattern) history ∧
      feedbackState sample lam x0 p0 m =
        scheduledState sample lam x0 p0 sourcePattern targetPattern history := by
  induction m with
  | zero =>
      refine ⟨[], rfl, trivial, ?_⟩
      simpa [feedbackState_zero, scheduledState, scheduledStateFrom] using hinit
  | succ m ih =>
      have hactive' : ∀ k ≤ m,
          ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty := by
        intro k hk
        exact hactive k (le_trans hk (Nat.le_succ m))
      have hprior' : ∀ k < m,
          ((feedbackState sample lam x0 p0 k).newSource sample lam).card +
            ((feedbackState sample lam x0 p0 k).newTarget sample lam).card ≤ 1 := by
        intro k hk
        exact hprior k (lt_trans hk (Nat.lt_succ_self m))
      obtain ⟨history, hlen, hgood, hstate⟩ := ih hactive' hprior'
      have hcount :
          ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
            ((feedbackState sample lam x0 p0 m).newTarget sample lam).card = 1 := by
        have hpos := sample.new_label_count_pos_of_candidates_nonempty lam _ (hactive m
          (Nat.le_succ m))
        have hup := hprior m (Nat.lt_succ_self m)
        omega
      obtain ⟨label, hlabel⟩ := sample.exists_labelStepRealizes_of_card_sum_eq_one
        lam (feedbackState sample lam x0 p0 m) hcount
      have hlabel' : labelStepRealizes sample lam
          (scheduledState sample lam x0 p0 sourcePattern targetPattern history) label := by
        rw [← hstate]
        exact hlabel
      have hgood' : ForcedHistoryRealizes sample lam
          (forcedInitialState x0 p0 sourcePattern targetPattern) (history ++ [label]) := by
        apply ForcedHistoryRealizes.append_singleton sample lam
          (forcedInitialState x0 p0 sourcePattern targetPattern) history label hgood
        simpa [scheduledState] using hlabel'
      have hstate' := feedbackState_eq_scheduledState_of_history sample lam x0 p0
        sourcePattern targetPattern (history ++ [label]) hinit hgood'
      refine ⟨history ++ [label], by simp [hlen], hgood', ?_⟩
      simpa [Nat.succ_eq_add_one, hlen] using hstate'

/-! ## The first bad step and its two distinct labels -/

theorem exists_noTieBranch_of_not_NoFeedbackTies
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    (hbadAll : ¬ sample.NoFeedbackTies lam x0 p0) :
    ∃ (sourcePattern targetPattern : Finset (Fin n))
      (history : List (FeedbackLabel n)) (l₁ l₂ : FeedbackLabel n),
      history.length < 2 * n ∧
      ForcedHistoryRealizes sample lam
        (forcedInitialState x0 p0 sourcePattern targetPattern) history ∧
      l₁ ∉ history ∧ l₁ ≠ l₂ ∧
      feedbackState sample lam x0 p0 history.length =
        scheduledState sample lam x0 p0 sourcePattern targetPattern history ∧
      (scheduledState sample lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          sample lam l₁ =
        (scheduledState sample lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          sample lam l₂ := by
  classical
  have hex : ∃ m, m < 2 * n ∧
      ¬ ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 m).newTarget sample lam).card ≤ 1 := by
    rw [NoFeedbackTies] at hbadAll
    push Not at hbadAll
    rcases hbadAll with ⟨m, hm, hcount⟩
    exact ⟨m, hm, not_le.mpr hcount⟩
  let bad : ℕ → Prop := fun m ↦ m < 2 * n ∧
      ¬ ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 m).newTarget sample lam).card ≤ 1
  have hex' : ∃ m, bad m := by simpa [bad] using hex
  let m := Nat.find hex'
  have hm_spec : bad m := Nat.find_spec hex'
  have hm : m < 2 * n := hm_spec.1
  have hmbad : ¬ ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
      ((feedbackState sample lam x0 p0 m).newTarget sample lam).card ≤ 1 := hm_spec.2
  have hprior : ∀ k < m,
      ((feedbackState sample lam x0 p0 k).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 k).newTarget sample lam).card ≤ 1 := by
    intro k hkm
    by_contra hk
    exact (Nat.find_min hex' hkm) ⟨lt_trans hkm hm, hk⟩
  have hactive : ∀ k ≤ m,
      ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty := by
    intro k hkm
    by_cases hkeq : k = m
    · subst k
      by_contra hnone
      have hcand : (feedbackState sample lam x0 p0 m).candidates sample lam = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnone
      have hsource := sample.newSource_eq_empty_of_candidates_eq_empty lam
        (feedbackState sample lam x0 p0 m) hcand
      have htarget := sample.newTarget_eq_empty_of_candidates_eq_empty lam
        (feedbackState sample lam x0 p0 m) hcand
      apply hmbad
      rw [hsource, htarget]
      simp
    · exact sample.feedbackState_candidates_nonempty_of_bad_later lam x0 p0
        (Nat.lt_of_le_of_ne hkm hkeq) hmbad
  let sourcePattern := sample.initialSeenSource x0 p0
  let targetPattern := sample.initialSeenTarget x0 p0
  have hinit : sample.initialFeedbackState x0 p0 =
      forcedInitialState x0 p0 sourcePattern targetPattern := by
    simp [sourcePattern, targetPattern, initialFeedbackState, initialFeedbackCurrent,
      forcedInitialState]
  obtain ⟨history, hlen, hgood, hstate⟩ := sample.exists_forced_history_of_active
    lam x0 p0 sourcePattern targetPattern hinit m hactive hprior
  have hcount : 1 <
      ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 m).newTarget sample lam).card := by
    omega
  obtain ⟨l₁, l₂, hl₁, hl₂, hne⟩ :=
    sample.exists_distinct_newLabels_of_card_sum_gt_one lam
      (feedbackState sample lam x0 p0 m) hcount
  have hnot : l₁ ∉ history :=
    sample.label_not_mem_history_of_mem_newLabelSet lam x0 p0 sourcePattern targetPattern
      history (feedbackState sample lam x0 p0 m) hstate hl₁
  have hcoord₁ := sample.labelCoordinate_eq_next_of_mem_newLabelSet lam
    (feedbackState sample lam x0 p0 m) hl₁
  have hcoord₂ := sample.labelCoordinate_eq_next_of_mem_newLabelSet lam
    (feedbackState sample lam x0 p0 m) hl₂
  have hcoord_actual :
      (feedbackState sample lam x0 p0 m).labelCoordinate sample lam l₁ =
        (feedbackState sample lam x0 p0 m).labelCoordinate sample lam l₂ :=
    hcoord₁.trans hcoord₂.symm
  have hcoord_scheduled :
      (scheduledState sample lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          sample lam l₁ =
        (scheduledState sample lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          sample lam l₂ := by
    rw [← hstate]
    exact hcoord_actual
  refine ⟨sourcePattern, targetPattern, history, l₁, l₂, ?_, hgood, hnot, hne, ?_,
    hcoord_scheduled⟩
  · simpa [hlen] using hm
  · simpa [hlen] using hstate

end FiniteSample

end OTSelector
