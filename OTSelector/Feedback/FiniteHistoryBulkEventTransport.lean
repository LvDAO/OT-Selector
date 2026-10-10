import OTSelector.Feedback.FiniteHistoryBulkProductTransport
import OTSelector.Feedback.FiniteHistoryBulkSeenIntegral

/-!
# Finite-sample event/rate equality on one history index

The seen/unseen section identity is transported back to the canonical finite-sample law and the
finite next-label sum is exchanged with the outer seen integral.  The result is an ordinary
finite-sample event-mass identity for one prescribed history.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

private theorem historyBulkNextEvent_seenSection_integrable
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hxr : x0 ≤ r)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (label : FeedbackLabel n) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    Integrable (fun seen ↦ (feedbackUnseenTupleLaw S).real
      {unseen : feedbackUnseenFinset S → MarkedHeight |
        HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
            lam x0 p0 sourcePattern targetPattern history ∧
          unseen ∈ feedbackBulkNextEventSetOfLabel width lam
            (feedbackScheduledStateOfSeen lam x0 p0
              sourcePattern targetPattern history seen) s t S label ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E})
      (feedbackTupleLaw S) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let : IsProbabilityMeasure (feedbackTupleLaw S) := by
    rw [feedbackTupleLaw]
    infer_instance
  let : IsProbabilityMeasure (feedbackUnseenTupleLaw S) := by
    rw [feedbackUnseenTupleLaw]
    infer_instance
  let C := historyBulkNextEventProductSet width lam x0 p0 s t
    sourcePattern targetPattern history E label
  have hC : MeasurableSet C := by
    simpa [C] using measurableSet_historyBulkNextEventProductSet
      hlam0 hlamHalf sourcePattern targetPattern history hxr E hE label
  have hInt := Measure.integrable_measure_prodMk_left
    (μ := feedbackTupleLaw S) (ν := feedbackUnseenTupleLaw S) hC (by finiteness)
  change Integrable (fun seen ↦ (feedbackUnseenTupleLaw S).real
    ({unseen : feedbackUnseenFinset S → MarkedHeight |
        HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
          lam x0 p0 sourcePattern targetPattern history} ∩
      (feedbackBulkNextEventSetOfLabel width lam
          (feedbackScheduledStateOfSeen lam x0 p0
            sourcePattern targetPattern history seen) s t S label ∩
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          finiteSampleSeenUnseenMerge S seen unseen ∈ E})))
    (feedbackTupleLaw S)
  simpa [C, historyBulkNextEventProductSet, historyBranchProductSet, S] using hInt

theorem finiteSample_sourceBulk_history_eventMass_eq_rateMass
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
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
              feedbackUnseenTuple S sample ∈
                feedbackBulkNextEventSetOfLabel width lam
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history) s t S label ∧
              sample ∈ E} =
      ∫ seen, ∫ y in Ioc (feedbackBranchBulkStart width lam
          (feedbackScheduledStateOfSeen lam x0 p0
            sourcePattern targetPattern history seen) s)
          (feedbackBranchBulkStop width lam
            (feedbackScheduledStateOfSeen lam x0 p0
              sourcePattern targetPattern history seen) t),
        ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam
              (feedbackScheduledStateOfSeen lam x0 p0
                sourcePattern targetPattern history seen) y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume
        ∂(feedbackTupleLaw S) := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  have hInt (label : FeedbackLabel n) : Integrable (fun seen ↦
      (feedbackUnseenTupleLaw S).real
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history ∧
            unseen ∈ feedbackBulkNextEventSetOfLabel width lam
              (feedbackScheduledStateOfSeen lam x0 p0
                sourcePattern targetPattern history seen) s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E})
      (feedbackTupleLaw S) := by
    simpa [S] using historyBulkNextEvent_seenSection_integrable
      hlam0 hlamHalf sourcePattern targetPattern history hxr E hE label
  have hsum := integral_finsetSum (μ := feedbackTupleLaw S)
    (feedbackUnseenSourceLabels S)
    (fun label hlabel ↦ hInt label)
  have hsection := sourceBulk_seenIntegral_eventMass_eq_rateMass
    (n := n) (width := width) (s := s) (t := t)
    hlam0 hlamHalf (sourcePattern := sourcePattern)
    (targetPattern := targetPattern) (history := history)
    hxr hrs E hE hn hwidth
  dsimp only at hsection ⊢
  calc
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
              feedbackUnseenTuple S sample ∈
                feedbackBulkNextEventSetOfLabel width lam
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history) s t S label ∧
              sample ∈ E} =
        ∑ label ∈ feedbackUnseenSourceLabels S, ∫ seen,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                  lam x0 p0 sourcePattern targetPattern history ∧
                unseen ∈ feedbackBulkNextEventSetOfLabel width lam
                  (feedbackScheduledStateOfSeen lam x0 p0
                    sourcePattern targetPattern history seen) s t S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E}
          ∂(feedbackTupleLaw S) := by
            apply Finset.sum_congr rfl
            intro label hlabel
            exact finiteSampleLaw_real_historyBulkNextEvent_eq_seenIntegral
              hlam0 hlamHalf sourcePattern targetPattern history hxr E hE label
    _ = ∫ seen, ∑ label ∈ feedbackUnseenSourceLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                  lam x0 p0 sourcePattern targetPattern history ∧
                unseen ∈ feedbackBulkNextEventSetOfLabel width lam
                  (feedbackScheduledStateOfSeen lam x0 p0
                    sourcePattern targetPattern history seen) s t S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E}
          ∂(feedbackTupleLaw S) := hsum.symm
    _ = _ := by simpa [S] using hsection

theorem finiteSample_targetBulk_history_eventMass_eq_rateMass
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
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
              feedbackUnseenTuple S sample ∈
                feedbackBulkNextEventSetOfLabel width lam
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history) s t S label ∧
              sample ∈ E} =
      ∫ seen, ∫ y in Ioc (feedbackBranchBulkStart width lam
          (feedbackScheduledStateOfSeen lam x0 p0
            sourcePattern targetPattern history seen) s)
          (feedbackBranchBulkStop width lam
            (feedbackScheduledStateOfSeen lam x0 p0
              sourcePattern targetPattern history seen) t),
        ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam
              (feedbackScheduledStateOfSeen lam x0 p0
                sourcePattern targetPattern history seen) y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume
        ∂(feedbackTupleLaw S) := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  have hInt (label : FeedbackLabel n) : Integrable (fun seen ↦
      (feedbackUnseenTupleLaw S).real
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history ∧
            unseen ∈ feedbackBulkNextEventSetOfLabel width lam
              (feedbackScheduledStateOfSeen lam x0 p0
                sourcePattern targetPattern history seen) s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E})
      (feedbackTupleLaw S) := by
    simpa [S] using historyBulkNextEvent_seenSection_integrable
      hlam0 hlamHalf sourcePattern targetPattern history hxr E hE label
  have hsum := integral_finsetSum (μ := feedbackTupleLaw S)
    (feedbackUnseenTargetLabels S)
    (fun label hlabel ↦ hInt label)
  have hsection := targetBulk_seenIntegral_eventMass_eq_rateMass
    (n := n) (width := width) (s := s) (t := t)
    hlam0 hlamHalf (sourcePattern := sourcePattern)
    (targetPattern := targetPattern) (history := history)
    hxr hrs E hE hn hwidth
  dsimp only at hsection ⊢
  calc
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          {sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
              feedbackUnseenTuple S sample ∈
                feedbackBulkNextEventSetOfLabel width lam
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history) s t S label ∧
              sample ∈ E} =
        ∑ label ∈ feedbackUnseenTargetLabels S, ∫ seen,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                  lam x0 p0 sourcePattern targetPattern history ∧
                unseen ∈ feedbackBulkNextEventSetOfLabel width lam
                  (feedbackScheduledStateOfSeen lam x0 p0
                    sourcePattern targetPattern history seen) s t S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E}
          ∂(feedbackTupleLaw S) := by
            apply Finset.sum_congr rfl
            intro label hlabel
            exact finiteSampleLaw_real_historyBulkNextEvent_eq_seenIntegral
              hlam0 hlamHalf sourcePattern targetPattern history hxr E hE label
    _ = ∫ seen, ∑ label ∈ feedbackUnseenTargetLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                  lam x0 p0 sourcePattern targetPattern history ∧
                unseen ∈ feedbackBulkNextEventSetOfLabel width lam
                  (feedbackScheduledStateOfSeen lam x0 p0
                    sourcePattern targetPattern history seen) s t S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E}
          ∂(feedbackTupleLaw S) := hsum.symm
    _ = _ := by simpa [S] using hsection

end OTSelector
