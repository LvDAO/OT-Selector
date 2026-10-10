import OTSelector.Feedback.FiniteHistoryBulkReference
import OTSelector.Feedback.FiniteHistoryBulkRateSection

/-!
# Event/rate equality for one fixed seen tuple on a realized history branch

A non-empty clipped interval supplies a genuine reference sample at its left endpoint.  Promoting
the raw event from the observation coordinate to that endpoint and applying the fixed-section
identity removes the auxiliary witness again.  The result is an equality depending only on the
original realized branch and its fixed seen tuple.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

theorem sum_sourceBulkNextEvent_eq_intervalIntegral_unseenRate_of_historyBranch
    (reference : FiniteSample n) {width lam x0 p0 r s t a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0
      sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (ha : a = feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hb : b = feedbackBranchBulkStop width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (hab : a ≤ b) (hxr : x0 ≤ r) (hra : r ≤ a)
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
      ∫ y in a..b, ∫ unseen,
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
          (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam terminal y) unseen
        ∂(feedbackUnseenTupleLaw S) := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  obtain ⟨unseen₀, hunseen₀, hrefAt, hstateAt, hseenAt⟩ :=
    exists_historyAtCoordinate_finiteSampleSeenUnseenMerge_of_feedbackBranchBulk
      reference width s t a b hlam0 hlamHalf href seen hseen ha hb hab hn hwidth
  let referenceAt := finiteSampleSeenUnseenMerge S seen unseen₀
  have hstateAt' : referenceAt.scheduledState lam x0 p0
      sourcePattern targetPattern history = terminal := by
    simpa [referenceAt, S, terminal] using hstateAt
  have hxa : x0 ≤ a := hxr.trans hra
  have hEa : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] E :=
    measurableSet_rawRevealedFiltration_mono_coordinate
      hlam0 hlamHalf hxr hra E hE
  have haAt : a = feedbackBranchBulkStart width lam
      (referenceAt.scheduledState lam x0 p0 sourcePattern targetPattern history) s := by
    rw [hstateAt']
    exact ha
  have hbAt : b = feedbackBranchBulkStop width lam
      (referenceAt.scheduledState lam x0 p0 sourcePattern targetPattern history) t := by
    rw [hstateAt']
    exact hb
  have hseenAt' : seen = feedbackSeenTuple S referenceAt := by
    simp [referenceAt, S]
  have hmain := sum_sourceBulkNextEvent_eq_intervalIntegral_unseenRateSection
    referenceAt hlam0 hlamHalf haAt hbAt hxa hab
      (by simpa [referenceAt, S] using hrefAt) seen hseenAt' E hEa hn hwidth
  simpa [referenceAt, S, terminal, hstateAt'] using hmain

theorem sum_targetBulkNextEvent_eq_intervalIntegral_unseenRate_of_historyBranch
    (reference : FiniteSample n) {width lam x0 p0 r s t a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0
      sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (ha : a = feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hb : b = feedbackBranchBulkStop width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (hab : a ≤ b) (hxr : x0 ≤ r) (hra : r ≤ a)
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
      ∫ y in a..b, ∫ unseen,
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
          (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam terminal y) unseen
        ∂(feedbackUnseenTupleLaw S) := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  obtain ⟨unseen₀, hunseen₀, hrefAt, hstateAt, hseenAt⟩ :=
    exists_historyAtCoordinate_finiteSampleSeenUnseenMerge_of_feedbackBranchBulk
      reference width s t a b hlam0 hlamHalf href seen hseen ha hb hab hn hwidth
  let referenceAt := finiteSampleSeenUnseenMerge S seen unseen₀
  have hstateAt' : referenceAt.scheduledState lam x0 p0
      sourcePattern targetPattern history = terminal := by
    simpa [referenceAt, S, terminal] using hstateAt
  have hxa : x0 ≤ a := hxr.trans hra
  have hEa : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] E :=
    measurableSet_rawRevealedFiltration_mono_coordinate
      hlam0 hlamHalf hxr hra E hE
  have haAt : a = feedbackBranchBulkStart width lam
      (referenceAt.scheduledState lam x0 p0 sourcePattern targetPattern history) s := by
    rw [hstateAt']
    exact ha
  have hbAt : b = feedbackBranchBulkStop width lam
      (referenceAt.scheduledState lam x0 p0 sourcePattern targetPattern history) t := by
    rw [hstateAt']
    exact hb
  have hseenAt' : seen = feedbackSeenTuple S referenceAt := by
    simp [referenceAt, S]
  have hmain := sum_targetBulkNextEvent_eq_intervalIntegral_unseenRateSection
    referenceAt hlam0 hlamHalf haAt hbAt hxa hab
      (by simpa [referenceAt, S] using hrefAt) seen hseenAt' E hEa hn hwidth
  simpa [referenceAt, S, terminal, hstateAt'] using hmain

end OTSelector
