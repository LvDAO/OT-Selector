import OTSelector.Feedback.FiniteHistoryBulkBranchSection
import OTSelector.Feedback.FiniteHistoryBulkEmpty

/-!
# Set-integral event/rate equality on one realized history branch

The clipped bulk interval is used as the measurable set `Ioc start stop`.  This removes the
orientation artefact of `intervalIntegral`: a reversed interval contributes zero on both the
event and rate sides.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

theorem sum_sourceBulkNextEvent_eq_setIntegral_unseenRate_of_historyBranch
    (reference : FiniteSample n) {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0
      sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (hxr : x0 ≤ r)
    (hra : r ≤ feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
      ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
          (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
          (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam terminal y) unseen
        ∂(feedbackUnseenTupleLaw S) ∂volume := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  by_cases hab : feedbackBranchBulkStart width lam terminal s ≤
      feedbackBranchBulkStop width lam terminal t
  · have hmain :=
      sum_sourceBulkNextEvent_eq_intervalIntegral_unseenRate_of_historyBranch
        reference hlam0 hlamHalf href seen hseen rfl rfl hab hxr hra E hE hn hwidth
    dsimp only at hmain ⊢
    rw [intervalIntegral.integral_of_le hab] at hmain
    exact hmain
  · have hstop : feedbackBranchBulkStop width lam terminal t <
        feedbackBranchBulkStart width lam terminal s := lt_of_not_ge hab
    have hevent (label : FeedbackLabel n) :
        feedbackBulkNextEventSetOfLabel width lam terminal s t S label = ∅ :=
      feedbackBulkNextEventSetOfLabel_eq_empty_of_stop_lt_start
        width lam terminal s t S label hwidth hlam0 hlamHalf hstop
    have hIoc : Ioc (feedbackBranchBulkStart width lam terminal s)
        (feedbackBranchBulkStop width lam terminal t) = ∅ :=
      Ioc_feedbackBranchBulkStart_stop_eq_empty_of_stop_lt_start
        width lam terminal s t hstop
    have hevent' (label : FeedbackLabel n) :
        feedbackBulkNextEventSetOfLabel width lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
          s t (feedbackTerminalLabelSet sourcePattern targetPattern history) label = ∅ := by
      simpa [S, terminal] using hevent label
    have hIoc' : Ioc
        (feedbackBranchBulkStart width lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
        (feedbackBranchBulkStop width lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t) = ∅ := by
      simpa [terminal] using hIoc
    dsimp only at ⊢
    simp_rw [hevent']
    rw [hIoc']
    simp

theorem sum_targetBulkNextEvent_eq_setIntegral_unseenRate_of_historyBranch
    (reference : FiniteSample n) {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0
      sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (hxr : x0 ≤ r)
    (hra : r ≤ feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
      ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
          (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
          (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam terminal y) unseen
        ∂(feedbackUnseenTupleLaw S) ∂volume := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  by_cases hab : feedbackBranchBulkStart width lam terminal s ≤
      feedbackBranchBulkStop width lam terminal t
  · have hmain :=
      sum_targetBulkNextEvent_eq_intervalIntegral_unseenRate_of_historyBranch
        reference hlam0 hlamHalf href seen hseen rfl rfl hab hxr hra E hE hn hwidth
    dsimp only at hmain ⊢
    rw [intervalIntegral.integral_of_le hab] at hmain
    exact hmain
  · have hstop : feedbackBranchBulkStop width lam terminal t <
        feedbackBranchBulkStart width lam terminal s := lt_of_not_ge hab
    have hevent (label : FeedbackLabel n) :
        feedbackBulkNextEventSetOfLabel width lam terminal s t S label = ∅ :=
      feedbackBulkNextEventSetOfLabel_eq_empty_of_stop_lt_start
        width lam terminal s t S label hwidth hlam0 hlamHalf hstop
    have hIoc : Ioc (feedbackBranchBulkStart width lam terminal s)
        (feedbackBranchBulkStop width lam terminal t) = ∅ :=
      Ioc_feedbackBranchBulkStart_stop_eq_empty_of_stop_lt_start
        width lam terminal s t hstop
    have hevent' (label : FeedbackLabel n) :
        feedbackBulkNextEventSetOfLabel width lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
          s t (feedbackTerminalLabelSet sourcePattern targetPattern history) label = ∅ := by
      simpa [S, terminal] using hevent label
    have hIoc' : Ioc
        (feedbackBranchBulkStart width lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
        (feedbackBranchBulkStop width lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t) = ∅ := by
      simpa [terminal] using hIoc
    dsimp only at ⊢
    simp_rw [hevent']
    rw [hIoc']
    simp

end OTSelector
