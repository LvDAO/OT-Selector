import OTSelector.Feedback.FiniteHistoryFluxRate
import OTSelector.Feedback.FiniteHistorySectionConstancy

/-!
# Raw-event weighted flux on a fixed finite-history section

Fix a deterministic coordinate cell and its continuously valued seen tuple.  A raw event known
at the left endpoint is constant on every later next-event section.  Consequently its indicator
can be inserted into the exact unseen-product next-event identities without introducing a
conditional law on a zero-mass exact tuple.

This is the local probability identity used by the predictable-rectangle compensator.  The
outer seen-tuple integration and the finite sum over histories are deliberately left to the next
module.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

theorem measurableSet_rawRevealedFiltration_mono_coordinate
    {lam x0 p0 r a : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxr : x0 ≤ r) (hra : r ≤ a) (B : Set (FiniteSample n))
    (hB : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] B) :
    MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr (hxr.trans hra)⟩] B := by
  have htime :
      (⟨r - x0, sub_nonneg.mpr hxr⟩ : ℝ≥0) ≤
        ⟨a - x0, sub_nonneg.mpr (hxr.trans hra)⟩ := by
    apply NNReal.coe_le_coe.mp
    change r - x0 ≤ a - x0
    linarith
  exact (Filtration.mono
    (FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) htime) B hB

/-! ## A raw event cuts a next-event section into all or nothing -/

theorem rawRevealedEvent_nextEventSection_eq
    (reference : FiniteSample n) {lam x0 p0 a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxa : x0 ≤ a) (hab : a ≤ b)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (B : Set (FiniteSample n))
    (hB : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] B)
    (label : FeedbackLabel n) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    {unseen : feedbackUnseenFinset S → MarkedHeight |
      unseen ∈ feedbackNextEventSetOfLabel lam terminal a b S label ∧
        finiteSampleSeenUnseenMerge S seen unseen ∈ B} =
      if reference ∈ B then
        feedbackNextEventSetOfLabel lam terminal a b S label
      else ∅ := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  change {unseen : feedbackUnseenFinset S → MarkedHeight |
      unseen ∈ feedbackNextEventSetOfLabel lam terminal a b S label ∧
        finiteSampleSeenUnseenMerge S seen unseen ∈ B} =
    if reference ∈ B then
      feedbackNextEventSetOfLabel lam terminal a b S label else ∅
  ext unseen
  by_cases hnext : unseen ∈ feedbackNextEventSetOfLabel lam terminal a b S label
  · have hrectangle :
        unseen ∈ feedbackUnseenRectangularSetAt lam terminal a S :=
      feedbackNextEventSetOfLabel_subset_feedbackUnseenRectangularSetAt
        terminal lam a b S label hlam0 hlamHalf hab hnext
    have hsample : HistoryAtCoordinate
        (finiteSampleSeenUnseenMerge S seen unseen)
        lam x0 p0 sourcePattern targetPattern history a := by
      apply (historyAtCoordinate_finiteSampleSeenUnseenMerge_iff reference
        hlam0 hlamHalf href seen unseen hseen).2
      exact hrectangle
    have htuple : feedbackSeenTuple S reference =
        feedbackSeenTuple S (finiteSampleSeenUnseenMerge S seen unseen) := by
      rw [feedbackSeenTuple_finiteSampleSeenUnseenMerge]
      exact hseen.symm
    have hmem := rawRevealedEvent_mem_iff_of_historyAtCoordinate
      reference (finiteSampleSeenUnseenMerge S seen unseen)
      hlam0 hlamHalf hxa href hsample htuple B hB
    by_cases hrefB : reference ∈ B
    · rw [ite_eq_left hrefB]
      exact iff_of_true ⟨hnext, hmem.mp hrefB⟩ hnext
    · rw [ite_eq_right hrefB]
      exact iff_of_false (fun h ↦ hrefB (hmem.mpr h.2)) (by simp)
  · by_cases hrefB : reference ∈ B
    · rw [ite_eq_left hrefB]
      exact iff_of_false (fun h ↦ hnext h.1) hnext
    · rw [ite_eq_right hrefB]
      exact iff_of_false (fun h ↦ hnext h.1) (by simp)

/-! ## Source and target weighted product-law identities -/

theorem sum_feedbackUnseenTupleLaw_real_sourceNextEventSet_inter_rawEvent_eq_flux
    (reference : FiniteSample n) {lam x0 p0 a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxa : x0 ≤ a) (hab : a ≤ b)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (B : Set (FiniteSample n))
    (hB : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] B)
    (hn : 0 < n)
    (hbulk : ∀ y ∈ Icc a b,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary
            (segmentCurve
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
              ((reference.scheduledState lam x0 p0
                sourcePattern targetPattern history).slope lam) y) y u ∧
          sourceBoundary
            (segmentCurve
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
              ((reference.scheduledState lam x0 p0
                sourcePattern targetPattern history).slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary
            (segmentCurve
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
              ((reference.scheduledState lam x0 p0
                sourcePattern targetPattern history).slope lam) y) y v ∧
          targetBoundary
            (segmentCurve
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
              ((reference.scheduledState lam x0 p0
                sourcePattern targetPattern history).slope lam) y) y v ≤ n)
    (hsource : ∀ y ∈ Icc a b,
      0 < feedbackSourceRemainingRealMassAt lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) y) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackNextEventSetOfLabel lam terminal a b S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ B} =
      if reference ∈ B then
        ∫ y in a..b, feedbackSourceSurvivalLossFluxAt lam terminal y S
      else 0 := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  dsimp only
  by_cases hrefB : reference ∈ B
  · rw [ite_eq_left hrefB]
    calc
      ∑ label ∈ feedbackUnseenSourceLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              unseen ∈ feedbackNextEventSetOfLabel lam terminal a b S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ B} =
          ∑ label ∈ feedbackUnseenSourceLabels S,
            (feedbackUnseenTupleLaw S).real
              (feedbackNextEventSetOfLabel lam terminal a b S label) := by
        apply Finset.sum_congr rfl
        intro label hlabel
        rw [rawRevealedEvent_nextEventSection_eq reference hlam0 hlamHalf
          hxa hab href seen hseen B hB label, ite_eq_left hrefB]
      _ = ∫ y in a..b, feedbackSourceSurvivalLossFluxAt lam terminal y S := by
        exact sum_feedbackUnseenTupleLaw_real_sourceNextEventSetOfLabel_eq_flux
          terminal lam a b S hn hab hlam0 hlamHalf hbulk hsource
  · rw [ite_eq_right hrefB]
    apply Finset.sum_eq_zero
    intro label hlabel
    rw [rawRevealedEvent_nextEventSection_eq reference hlam0 hlamHalf
      hxa hab href seen hseen B hB label, ite_eq_right hrefB]
    simp

theorem sum_feedbackUnseenTupleLaw_real_targetNextEventSet_inter_rawEvent_eq_flux
    (reference : FiniteSample n) {lam x0 p0 a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxa : x0 ≤ a) (hab : a ≤ b)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (B : Set (FiniteSample n))
    (hB : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] B)
    (hn : 0 < n)
    (hbulk : ∀ y ∈ Icc a b,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary
            (segmentCurve
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
              ((reference.scheduledState lam x0 p0
                sourcePattern targetPattern history).slope lam) y) y u ∧
          sourceBoundary
            (segmentCurve
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
              ((reference.scheduledState lam x0 p0
                sourcePattern targetPattern history).slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary
            (segmentCurve
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
              ((reference.scheduledState lam x0 p0
                sourcePattern targetPattern history).slope lam) y) y v ∧
          targetBoundary
            (segmentCurve
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
              (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
              ((reference.scheduledState lam x0 p0
                sourcePattern targetPattern history).slope lam) y) y v ≤ n)
    (htarget : ∀ y ∈ Icc a b,
      0 < feedbackTargetRemainingRealMassAt lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) y) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackNextEventSetOfLabel lam terminal a b S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ B} =
      if reference ∈ B then
        ∫ y in a..b, feedbackTargetSurvivalLossFluxAt lam terminal y S
      else 0 := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  dsimp only
  by_cases hrefB : reference ∈ B
  · rw [ite_eq_left hrefB]
    calc
      ∑ label ∈ feedbackUnseenTargetLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              unseen ∈ feedbackNextEventSetOfLabel lam terminal a b S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ B} =
          ∑ label ∈ feedbackUnseenTargetLabels S,
            (feedbackUnseenTupleLaw S).real
              (feedbackNextEventSetOfLabel lam terminal a b S label) := by
        apply Finset.sum_congr rfl
        intro label hlabel
        rw [rawRevealedEvent_nextEventSection_eq reference hlam0 hlamHalf
          hxa hab href seen hseen B hB label, ite_eq_left hrefB]
      _ = ∫ y in a..b, feedbackTargetSurvivalLossFluxAt lam terminal y S := by
        exact sum_feedbackUnseenTupleLaw_real_targetNextEventSetOfLabel_eq_flux
          terminal lam a b S hn hab hlam0 hlamHalf hbulk htarget
  · rw [ite_eq_right hrefB]
    apply Finset.sum_eq_zero
    intro label hlabel
    rw [rawRevealedEvent_nextEventSection_eq reference hlam0 hlamHalf
      hxa hab href seen hseen B hB label, ite_eq_right hrefB]
    simp

end OTSelector
