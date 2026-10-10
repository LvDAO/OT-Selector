import OTSelector.Feedback.FiniteHistoryBulkSectionFlux

/-!
# Unseen-coordinate integral of a fixed-history bulk rate section

For a fixed timed history and fixed seen tuple, the raw event is constant on every later strict
remaining rectangle.  Integrating the scheduled state rate over the unseen coordinates therefore
produces survival mass times state rate, which is exactly the source or target survival-loss
flux.  This is the rate-side counterpart of `FiniteHistoryBulkSectionFlux`.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

theorem integral_feedbackUnseenTupleLaw_sourceBulkRateSection_eq_flux
    (reference : FiniteSample n) {width lam x0 p0 s t a b y : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (ha : a = feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hb : b = feedbackBranchBulkStop width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (hxa : x0 ≤ a) (hab : a ≤ b)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) (hy : y ∈ Icc a b) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    ∫ unseen,
      {unseen : feedbackUnseenFinset S → MarkedHeight |
        unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
        (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam terminal y) unseen
      ∂(feedbackUnseenTupleLaw S) =
      if reference ∈ E then
        feedbackSourceSurvivalLossFluxAt lam terminal y S
      else 0 := by
  classical
  subst a
  subst b
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  dsimp only
  have hsection := rawRevealedEvent_laterRectangularSection_eq
    reference hlam0 hlamHalf hxa hy.1 href seen hseen E hE
  have hbounds := feedbackBoundary_bounds_on_branchBulkInterval
    width lam terminal s t y hwidth hy
  have hbulkAll : ∀ label ∈ feedbackUnseenFinset S,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary
          (segmentCurve terminal.x terminal.p (terminal.slope lam) y) y u ∧
          sourceBoundary
            (segmentCurve terminal.x terminal.p (terminal.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary
          (segmentCurve terminal.x terminal.p (terminal.slope lam) y) y v ∧
          targetBoundary
            (segmentCurve terminal.x terminal.p (terminal.slope lam) y) y v ≤ n := by
    intro label _hlabel
    exact hbounds
  have hsurvival := feedbackUnseenSurvivalMassAt_eq_feedbackUnseenTupleLaw_real
    hn lam terminal y S hbulkAll
  have hsource := feedbackSourceRemainingRealMassAt_pos_on_branchBulkInterval
    width lam terminal s t y hn hwidth hy
  have hflux := feedbackSourceSurvivalLossFluxAt_eq_stateRate
    reference hn hsource
  by_cases hrefE : reference ∈ E
  · rw [ite_eq_left hrefE]
    rw [hsection, ite_eq_left hrefE]
    rw [integral_indicator_const _
      (measurableSet_feedbackUnseenRectangularSetAt lam terminal y S)]
    simp only [smul_eq_mul]
    rw [← hsurvival]
    exact hflux.symm
  · rw [ite_eq_right hrefE]
    rw [hsection, ite_eq_right hrefE]
    simp

theorem integral_feedbackUnseenTupleLaw_targetBulkRateSection_eq_flux
    (reference : FiniteSample n) {width lam x0 p0 s t a b y : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (ha : a = feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hb : b = feedbackBranchBulkStop width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (hxa : x0 ≤ a) (hab : a ≤ b)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) (hy : y ∈ Icc a b) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    ∫ unseen,
      {unseen : feedbackUnseenFinset S → MarkedHeight |
        unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
        (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam terminal y) unseen
      ∂(feedbackUnseenTupleLaw S) =
      if reference ∈ E then
        feedbackTargetSurvivalLossFluxAt lam terminal y S
      else 0 := by
  classical
  subst a
  subst b
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  dsimp only
  have hsection := rawRevealedEvent_laterRectangularSection_eq
    reference hlam0 hlamHalf hxa hy.1 href seen hseen E hE
  have hbounds := feedbackBoundary_bounds_on_branchBulkInterval
    width lam terminal s t y hwidth hy
  have hbulkAll : ∀ label ∈ feedbackUnseenFinset S,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary
          (segmentCurve terminal.x terminal.p (terminal.slope lam) y) y u ∧
          sourceBoundary
            (segmentCurve terminal.x terminal.p (terminal.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary
          (segmentCurve terminal.x terminal.p (terminal.slope lam) y) y v ∧
          targetBoundary
            (segmentCurve terminal.x terminal.p (terminal.slope lam) y) y v ≤ n := by
    intro label _hlabel
    exact hbounds
  have hsurvival := feedbackUnseenSurvivalMassAt_eq_feedbackUnseenTupleLaw_real
    hn lam terminal y S hbulkAll
  have htarget := feedbackTargetRemainingRealMassAt_pos_on_branchBulkInterval
    width lam terminal s t y hn hwidth hy
  have hflux := feedbackTargetSurvivalLossFluxAt_eq_stateRate
    reference hn htarget
  by_cases hrefE : reference ∈ E
  · rw [ite_eq_left hrefE]
    rw [hsection, ite_eq_left hrefE]
    rw [integral_indicator_const _
      (measurableSet_feedbackUnseenRectangularSetAt lam terminal y S)]
    simp only [smul_eq_mul]
    rw [← hsurvival]
    exact hflux.symm
  · rw [ite_eq_right hrefE]
    rw [hsection, ite_eq_right hrefE]
    simp

theorem sum_sourceBulkNextEvent_eq_intervalIntegral_unseenRateSection
    (reference : FiniteSample n) {width lam x0 p0 s t a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (ha : a = feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hb : b = feedbackBranchBulkStop width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (hxa : x0 ≤ a) (hab : a ≤ b)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] E)
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
  dsimp only
  rw [sum_feedbackUnseenTupleLaw_real_sourceBulkNextEventSet_inter_rawEvent_eq_flux
    reference hlam0 hlamHalf ha hb hxa hab href seen hseen E hE hn hwidth]
  calc
    (if reference ∈ E then
        ∫ y in a..b, feedbackSourceSurvivalLossFluxAt lam terminal y S
      else 0) =
        ∫ y in a..b,
          if reference ∈ E then
            feedbackSourceSurvivalLossFluxAt lam terminal y S else 0 := by
      by_cases hrefE : reference ∈ E <;> simp [hrefE]
    _ = ∫ y in a..b, ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam terminal y) unseen
          ∂(feedbackUnseenTupleLaw S) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyIcc : y ∈ Icc a b := by
        rw [uIcc_of_le hab] at hy
        exact hy
      exact (integral_feedbackUnseenTupleLaw_sourceBulkRateSection_eq_flux
        reference hlam0 hlamHalf ha hb hxa hab href seen hseen E hE
          hn hwidth hyIcc).symm

theorem sum_targetBulkNextEvent_eq_intervalIntegral_unseenRateSection
    (reference : FiniteSample n) {width lam x0 p0 s t a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (ha : a = feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hb : b = feedbackBranchBulkStop width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (hxa : x0 ≤ a) (hab : a ≤ b)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] E)
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
  dsimp only
  rw [sum_feedbackUnseenTupleLaw_real_targetBulkNextEventSet_inter_rawEvent_eq_flux
    reference hlam0 hlamHalf ha hb hxa hab href seen hseen E hE hn hwidth]
  calc
    (if reference ∈ E then
        ∫ y in a..b, feedbackTargetSurvivalLossFluxAt lam terminal y S
      else 0) =
        ∫ y in a..b,
          if reference ∈ E then
            feedbackTargetSurvivalLossFluxAt lam terminal y S else 0 := by
      by_cases hrefE : reference ∈ E <;> simp [hrefE]
    _ = ∫ y in a..b, ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam terminal y) unseen
          ∂(feedbackUnseenTupleLaw S) := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hyIcc : y ∈ Icc a b := by
        rw [uIcc_of_le hab] at hy
        exact hy
      exact (integral_feedbackUnseenTupleLaw_targetBulkRateSection_eq_flux
        reference hlam0 hlamHalf ha hb hxa hab href seen hseen E hE
          hn hwidth hyIcc).symm

end OTSelector
