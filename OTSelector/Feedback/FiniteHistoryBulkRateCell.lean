import OTSelector.Feedback.FeedbackBulkMask
import OTSelector.Feedback.FiniteHistoryBeforePartition

/-!
# Actual bulk rates on arbitrary strict history cells

The core bulk-rate identities are stated with the sample's canonical initial patterns.  A
`HistoryBeforeCoordinate` already forces any prescribed patterns to be those canonical patterns,
so the identities below expose the form needed by the finite history-index partition.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

open FiniteSample

private theorem initialSeenSource_eq_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x) :
    sample.initialSeenSource x0 p0 = sourcePattern := by
  have h := congrArg FeedbackStepState.seenSource hbefore.1.1.1
  simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h

private theorem initialSeenTarget_eq_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x) :
    sample.initialSeenTarget x0 p0 = targetPattern := by
  have h := congrArg FeedbackStepState.seenTarget hbefore.1.1.1
  simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h

theorem safeFeedbackHeightAtElapsed_eq_segmentCurve_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x) :
    safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 u sample =
      segmentCurve
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).p
        ((sample.scheduledState lam x0 p0
          sourcePattern targetPattern history).slope lam) x := by
  let terminal := sample.scheduledState lam x0 p0
    sourcePattern targetPattern history
  have hu0 : u = ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ := by
    apply NNReal.eq
    change (u : ℝ) = x - x0
    dsimp [FiniteSample.elapsedFeedbackCoordinate] at hu
    linarith
  have hsource := initialSeenSource_eq_of_historyBeforeCoordinate sample hbefore
  have htarget := initialSeenTarget_eq_of_historyBeforeCoordinate sample hbefore
  have hbefore' : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x := by
    simpa [hsource, htarget] using hbefore
  have hstate0 := HistoryBeforeCoordinate.feedbackStateAtElapsed_eq_scheduledState
    sample hlam0 hlamHalf hx0x hbefore'
  have hstate : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u = terminal := by
    rw [hu0]
    simpa [terminal, hsource, htarget] using hstate0
  have hheight0 := sample.feedbackHeightAtElapsed_eq_segmentCurve
    hlam0 hlamHalf x0 p0 u
  have hsafe : safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 u sample =
      sample.feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 u := by
    simp [safeFeedbackHeightAtElapsed, hbefore.2]
  calc
    safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 u sample =
        sample.feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 u := hsafe
    _ = segmentCurve
        (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u).x
        (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u).p
        ((sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u).slope lam)
        (x0 + (u : ℝ)) := hheight0
    _ = segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
      rw [hstate]
      congr 1

theorem safeSourceBulkRate_eq_sourceUnclippedStateRateAt_of_historyBeforeCoordinate_stateBulk
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hB : 0 < B)
    (hx0x : x0 < x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x)
    (hbulk : feedbackBulkRegion n B x
      (segmentCurve
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).p
        ((sample.scheduledState lam x0 p0
          sourcePattern targetPattern history).slope lam) x)) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample =
      FeedbackStepState.sourceUnclippedStateRateAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x := by
  have hsource := initialSeenSource_eq_of_historyBeforeCoordinate sample hbefore
  have htarget := initialSeenTarget_eq_of_historyBeforeCoordinate sample hbefore
  have hbefore' : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x := by
    simpa [hsource, htarget] using hbefore
  have hheight :=
    safeFeedbackHeightAtElapsed_eq_segmentCurve_of_historyBeforeCoordinate
      (n := n) (lam := lam) (x0 := x0) (p0 := p0) (x := x)
      (sourcePattern := sourcePattern) (targetPattern := targetPattern)
      (history := history) sample hlam0 hlamHalf hx0x hbefore u hu
  have hbulk' : feedbackBulkRegion n B
      (FiniteSample.elapsedFeedbackCoordinate x0 u)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 u sample) := by
    simpa [hu, hheight] using hbulk
  have hmain :=
    safeSourceBulkRate_eq_sourceUnclippedStateRateAt_of_historyBeforeCoordinate
      sample hlam0 hlamHalf hB hx0x hbefore' u hu hbulk'
  simpa [hsource, htarget] using hmain

theorem safeTargetBulkRate_eq_targetUnclippedStateRateAt_of_historyBeforeCoordinate_stateBulk
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hB : 0 < B)
    (hx0x : x0 < x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x)
    (hbulk : feedbackBulkRegion n B x
      (segmentCurve
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).p
        ((sample.scheduledState lam x0 p0
          sourcePattern targetPattern history).slope lam) x)) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample =
      FeedbackStepState.targetUnclippedStateRateAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x := by
  have hsource := initialSeenSource_eq_of_historyBeforeCoordinate sample hbefore
  have htarget := initialSeenTarget_eq_of_historyBeforeCoordinate sample hbefore
  have hbefore' : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x := by
    simpa [hsource, htarget] using hbefore
  have hheight :=
    safeFeedbackHeightAtElapsed_eq_segmentCurve_of_historyBeforeCoordinate
      (n := n) (lam := lam) (x0 := x0) (p0 := p0) (x := x)
      (sourcePattern := sourcePattern) (targetPattern := targetPattern)
      (history := history) sample hlam0 hlamHalf hx0x hbefore u hu
  have hbulk' : feedbackBulkRegion n B
      (FiniteSample.elapsedFeedbackCoordinate x0 u)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 u sample) := by
    simpa [hu, hheight] using hbulk
  have hmain :=
    safeTargetBulkRate_eq_targetUnclippedStateRateAt_of_historyBeforeCoordinate
      sample hlam0 hlamHalf hB hx0x hbefore' u hu hbulk'
  simpa [hsource, htarget] using hmain

/-- On a prescribed strict history cell, the safe source rate vanishes when the corresponding
affine state lies outside the bulk region. -/
theorem safeSourceBulkRate_eq_zero_of_historyBeforeCoordinate_not_stateBulk
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x)
    (hnotBulk : ¬ feedbackBulkRegion n B x
      (segmentCurve
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).p
        ((sample.scheduledState lam x0 p0
          sourcePattern targetPattern history).slope lam) x)) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample = 0 := by
  have hheight :=
    safeFeedbackHeightAtElapsed_eq_segmentCurve_of_historyBeforeCoordinate
      (n := n) (lam := lam) (x0 := x0) (p0 := p0) (x := x)
      (sourcePattern := sourcePattern) (targetPattern := targetPattern)
      (history := history) sample hlam0 hlamHalf hx0x hbefore u hu
  have hnotActual : ¬ feedbackBulkRegion n B
      (FiniteSample.elapsedFeedbackCoordinate x0 u)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 u sample) := by
    simpa [hu, hheight] using hnotBulk
  simp [safeSourceBulkRate, safeFeedbackBulkMask, hnotActual]

/-- On a prescribed strict history cell, the safe target rate vanishes when the corresponding
affine state lies outside the bulk region. -/
theorem safeTargetBulkRate_eq_zero_of_historyBeforeCoordinate_not_stateBulk
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x)
    (hnotBulk : ¬ feedbackBulkRegion n B x
      (segmentCurve
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).p
        ((sample.scheduledState lam x0 p0
          sourcePattern targetPattern history).slope lam) x)) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample = 0 := by
  have hheight :=
    safeFeedbackHeightAtElapsed_eq_segmentCurve_of_historyBeforeCoordinate
      (n := n) (lam := lam) (x0 := x0) (p0 := p0) (x := x)
      (sourcePattern := sourcePattern) (targetPattern := targetPattern)
      (history := history) sample hlam0 hlamHalf hx0x hbefore u hu
  have hnotActual : ¬ feedbackBulkRegion n B
      (FiniteSample.elapsedFeedbackCoordinate x0 u)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 u sample) := by
    simpa [hu, hheight] using hnotBulk
  simp [safeTargetBulkRate, safeFeedbackBulkMask, hnotActual]

end OTSelector
