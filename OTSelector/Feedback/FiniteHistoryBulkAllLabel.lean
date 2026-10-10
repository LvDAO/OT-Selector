import OTSelector.Feedback.FiniteHistoryBulkEventTransport

/-!
# Ambient-label bulk event sums for one finite history

The pathwise branch decomposition sums over every source or target label.  The fixed-history
probability theorem naturally sums only over labels outside the terminal seen set.  This file
identifies the two sums: an already-seen ambient label has an empty next-event set.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

private theorem feedbackUnseenSourceLabels_eq_image_filter
    (S : Finset (FeedbackLabel n)) :
    feedbackUnseenSourceLabels S =
      (Finset.univ.filter fun i : Fin n ↦
        (Sum.inl i : FeedbackLabel n) ∈ feedbackUnseenFinset S).image Sum.inl := by
  classical
  ext label
  cases label with
  | inl i => simp [feedbackUnseenSourceLabels]
  | inr j => simp [feedbackUnseenSourceLabels]

private theorem feedbackUnseenTargetLabels_eq_image_filter
    (S : Finset (FeedbackLabel n)) :
    feedbackUnseenTargetLabels S =
      (Finset.univ.filter fun j : Fin n ↦
        (Sum.inr j : FeedbackLabel n) ∈ feedbackUnseenFinset S).image Sum.inr := by
  classical
  ext label
  cases label with
  | inl i => simp [feedbackUnseenTargetLabels]
  | inr j => simp [feedbackUnseenTargetLabels]

theorem sum_inl_eq_sum_feedbackUnseenSourceLabels_of_zero
    (S : Finset (FeedbackLabel n)) (f : FeedbackLabel n → ℝ)
    (hzero : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∉ feedbackUnseenFinset S → f (Sum.inl i) = 0) :
    ∑ i : Fin n, f (Sum.inl i) =
      ∑ label ∈ feedbackUnseenSourceLabels S, f label := by
  classical
  rw [feedbackUnseenSourceLabels_eq_image_filter]
  rw [Finset.sum_image]
  · symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    apply hzero i
    simpa using hnot
  · exact Sum.inl_injective.injOn

theorem sum_inr_eq_sum_feedbackUnseenTargetLabels_of_zero
    (S : Finset (FeedbackLabel n)) (f : FeedbackLabel n → ℝ)
    (hzero : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∉ feedbackUnseenFinset S → f (Sum.inr j) = 0) :
    ∑ j : Fin n, f (Sum.inr j) =
      ∑ label ∈ feedbackUnseenTargetLabels S, f label := by
  classical
  rw [feedbackUnseenTargetLabels_eq_image_filter]
  rw [Finset.sum_image]
  · symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hnot
    apply hzero j
    simpa using hnot
  · exact Sum.inr_injective.injOn

/-- The nested source-rate mass produced by one prescribed finite history. -/
noncomputable def sourceHistoryNestedRateMass
    (width lam x0 p0 s t : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (E : Set (FiniteSample n)) : ℝ :=
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  ∫ seen, ∫ y in Ioc (feedbackBranchBulkStart width lam
      (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) s)
      (feedbackBranchBulkStop width lam
        (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) t),
    ∫ unseen,
      {unseen : feedbackUnseenFinset S → MarkedHeight |
        HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
            lam x0 p0 sourcePattern targetPattern history y ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
        (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam
          (feedbackScheduledStateOfSeen lam x0 p0
            sourcePattern targetPattern history seen) y) unseen
      ∂(feedbackUnseenTupleLaw S) ∂volume
    ∂(feedbackTupleLaw S)

/-- The nested target-rate mass produced by one prescribed finite history. -/
noncomputable def targetHistoryNestedRateMass
    (width lam x0 p0 s t : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (E : Set (FiniteSample n)) : ℝ :=
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  ∫ seen, ∫ y in Ioc (feedbackBranchBulkStart width lam
      (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) s)
      (feedbackBranchBulkStop width lam
        (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) t),
    ∫ unseen,
      {unseen : feedbackUnseenFinset S → MarkedHeight |
        HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
            lam x0 p0 sourcePattern targetPattern history y ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
        (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam
          (feedbackScheduledStateOfSeen lam x0 p0
            sourcePattern targetPattern history seen) y) unseen
      ∂(feedbackUnseenTupleLaw S) ∂volume
    ∂(feedbackTupleLaw S)

theorem finiteSample_sourceBulk_history_allLabel_eventMass_eq_rateMass
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hxr : x0 ≤ r) (hrs : r ≤ s)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    ∑ i : Fin n,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
              feedbackUnseenTuple S sample ∈
                feedbackBulkNextEventSetOfLabel width lam
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history) s t S (Sum.inl i) ∧
              sample ∈ E} =
      sourceHistoryNestedRateMass width lam x0 p0 s t
        sourcePattern targetPattern history E := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let f : FeedbackLabel n → ℝ := fun label ↦
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {sample : FiniteSample n |
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
          feedbackUnseenTuple S sample ∈
            feedbackBulkNextEventSetOfLabel width lam
              (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
              s t S label ∧ sample ∈ E}
  have hzero : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∉ feedbackUnseenFinset S → f (Sum.inl i) = 0 := by
    intro i hi
    simp [f, feedbackBulkNextEventSetOfLabel, hi]
  have hsum := sum_inl_eq_sum_feedbackUnseenSourceLabels_of_zero S f hzero
  have hmain := finiteSample_sourceBulk_history_eventMass_eq_rateMass
    (n := n) (width := width) (r := r) (s := s) (t := t)
    hlam0 hlamHalf sourcePattern targetPattern history hxr hrs E hE hn hwidth
  dsimp only at hmain ⊢
  calc
    ∑ i : Fin n,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
              feedbackUnseenTuple S sample ∈
                feedbackBulkNextEventSetOfLabel width lam
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history) s t S (Sum.inl i) ∧
              sample ∈ E} = ∑ i : Fin n, f (Sum.inl i) := rfl
    _ = ∑ label ∈ feedbackUnseenSourceLabels S, f label := hsum
    _ = sourceHistoryNestedRateMass width lam x0 p0 s t
        sourcePattern targetPattern history E := by
      simpa [f, S, sourceHistoryNestedRateMass] using hmain

theorem finiteSample_targetBulk_history_allLabel_eventMass_eq_rateMass
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hxr : x0 ≤ r) (hrs : r ≤ s)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    ∑ j : Fin n,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
              feedbackUnseenTuple S sample ∈
                feedbackBulkNextEventSetOfLabel width lam
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history) s t S (Sum.inr j) ∧
              sample ∈ E} =
      targetHistoryNestedRateMass width lam x0 p0 s t
        sourcePattern targetPattern history E := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let f : FeedbackLabel n → ℝ := fun label ↦
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {sample : FiniteSample n |
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
          feedbackUnseenTuple S sample ∈
            feedbackBulkNextEventSetOfLabel width lam
              (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
              s t S label ∧ sample ∈ E}
  have hzero : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∉ feedbackUnseenFinset S → f (Sum.inr j) = 0 := by
    intro j hj
    simp [f, feedbackBulkNextEventSetOfLabel, hj]
  have hsum := sum_inr_eq_sum_feedbackUnseenTargetLabels_of_zero S f hzero
  have hmain := finiteSample_targetBulk_history_eventMass_eq_rateMass
    (n := n) (width := width) (r := r) (s := s) (t := t)
    hlam0 hlamHalf sourcePattern targetPattern history hxr hrs E hE hn hwidth
  dsimp only at hmain ⊢
  calc
    ∑ j : Fin n,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
              feedbackUnseenTuple S sample ∈
                feedbackBulkNextEventSetOfLabel width lam
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history) s t S (Sum.inr j) ∧
              sample ∈ E} = ∑ j : Fin n, f (Sum.inr j) := rfl
    _ = ∑ label ∈ feedbackUnseenTargetLabels S, f label := hsum
    _ = targetHistoryNestedRateMass width lam x0 p0 s t
        sourcePattern targetPattern history E := by
      simpa [f, S, targetHistoryNestedRateMass] using hmain

end OTSelector
