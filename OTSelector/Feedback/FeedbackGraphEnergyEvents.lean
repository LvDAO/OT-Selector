import OTSelector.Feedback.FeedbackGraphEnergyProbability
import OTSelector.Feedback.FeedbackBulkBackwardWindow
import OTSelector.Feedback.FeedbackRightIntervalCountsGraph
import OTSelector.Feedback.FeedbackRightIntervalCountsMoment

/-!
# Actual finite-sample events imply linear graph energy

All geometric current, count, and density inputs are discharged from the existing actual
boundary snapshot and finite-grid events.  The remaining two energy thresholds are the genuine
random variables controlled by the proved expectation and conditional expectation estimates.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector.FiniteSample
variable {n : ℕ} (sample : FiniteSample n)

private theorem stoppedGraph_curve_eq_boundaryHeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) :
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve (B + (T : ℝ)) =
      rightBoundaryHeight hlam0 hlamHalf B 0 T sample := by
  rw [sample.stoppedGraph_curve_eq_actualFrozenHeight_of_survival
    hlam0 hlamHalf eta B T hNoTie hstop _ le_rfl]
  exact rightBoundaryFrozenHeight_revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T sample hNoTie

/-- The graph current at the freezing boundary is the rank current used by A1 and A2. -/
theorem stoppedGraphRankCurrent_eq_boundaryRankDiscrepancy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) :
    sample.graphRankCurrent
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ)) =
      RelativeVC.feedbackRankDiscrepancy (feedbackSourceRankArray sample)
        (feedbackTargetRankArray sample) (rightBoundaryHeight hlam0 hlamHalf B 0 T sample)
        (B + (T : ℝ)) := by
  have h := sample.intersectionCurrent_eq_feedbackRankDiscrepancy
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ))
  rw [sample.stoppedGraph_curve_eq_boundaryHeight hlam0 hlamHalf eta B T hNoTie hstop] at h
  exact h

/-- The boundary terminal-rank population is bounded by the actual two unseen populations. -/
theorem stoppedGraphTerminalRankCount_le_boundaryUnseenCounts
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) :
    (sample.graphTerminalRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ)) : ℝ) ≤
      (rightBoundarySourceUnseenCount (revealedSnapshotState
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T)) : ℝ) +
      (rightBoundaryTargetUnseenCount (revealedSnapshotState
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T)) : ℝ) := by
  let graph := sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T
  have hcurve := sample.stoppedGraph_curve_eq_boundaryHeight hlam0 hlamHalf eta B T hNoTie hstop
  have hsource := sample.sourceIntersectionCount_cast_eq_sourceCutCount graph (B + (T : ℝ))
  have htarget := sample.targetIntersectionCount_cast_eq_targetCutCount graph (B + (T : ℝ))
  change graph.curve (B + (T : ℝ)) = _ at hcurve
  rw [hcurve] at hsource htarget
  have hsremain := rightBoundarySourceUnseenCount_actual_eq_safeRemaining
    hlam0 hlamHalf B 0 T sample hNoTie
  have htremain := rightBoundaryTargetUnseenCount_actual_eq_safeRemaining
    hlam0 hlamHalf B 0 T sample hNoTie
  rw [safeSourceRemainingAt_eq_n_sub_sourceCutCount hlam0 hlamHalf B 0 T sample hNoTie] at hsremain
  rw [safeTargetRemainingAt_eq_n_sub_targetCutCount hlam0 hlamHalf B 0 T sample hNoTie] at htremain
  have hcard (v : Fin n → ℝ) :
      ((Finset.univ.filter fun i ↦ v i ≤ B + (T : ℝ)).card : ℝ) +
        (Finset.univ.filter fun i ↦ B + (T : ℝ) < v i).card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i ↦ v i ≤ B + (T : ℝ))
    simp only [not_le, Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  have hs := hcard (sample.sourceIntersection graph)
  have ht := hcard (sample.targetIntersection graph)
  have hcount : (sample.graphTerminalRankCount graph (B + (T : ℝ)) : ℝ) ≤
      (sample.graphSourceRightEndpointCount graph (B + (T : ℝ)) : ℝ) +
        sample.graphTargetRightEndpointCount graph (B + (T : ℝ)) := by
    exact_mod_cast sample.graphTerminalRankCount_le_rightEndpointCounts graph (B + (T : ℝ))
  change (sample.graphTerminalRankCount graph (B + (T : ℝ)) : ℝ) ≤ _
  change (sample.sourceIntersectionCount graph (B + (T : ℝ)) : ℝ) +
    sample.graphSourceRightEndpointCount graph (B + (T : ℝ)) = n at hs
  change (sample.targetIntersectionCount graph (B + (T : ℝ)) : ℝ) +
    sample.graphTargetRightEndpointCount graph (B + (T : ℝ)) = n at ht
  simp only [rightBoundaryHeight, elapsedFeedbackCoordinate] at hsource htarget hsremain htremain
  change (sample.sourceIntersectionCount graph (B + (T : ℝ)) : ℝ) =
    RelativeVC.sourceCutCount (feedbackSourceRankArray sample)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 T sample) (B + (T : ℝ)) at hsource
  change (sample.targetIntersectionCount graph (B + (T : ℝ)) : ℝ) =
    RelativeVC.targetCutCount (feedbackTargetRankArray sample)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 T sample) (B + (T : ℝ)) at htarget
  linarith only [hcount, hs, ht, hsource, htarget, hsremain, htremain]

/-- The actual boundary/grid/bulk events discharge every geometric premise of the linear
energy theorem. -/
theorem stoppedGraphComparisonEnergy_le_linear_of_actual_events
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (eta : ℝ) (B T s r : ℝ≥0)
    {amplitude Kpre Kright L a W gridError : ℝ}
    (hB : (B : ℝ) = amplitude * Real.sqrt n) (hB1 : 1 ≤ (B : ℝ))
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hW : 0 ≤ W)
    (herr0 : 0 ≤ gridError) (herr : gridError + 1 / 4 ≤ Real.sqrt B)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hleftGeneric : sample ∈ leftHeightGenericEvent n)
    (hleft : leftRateExitTime n B sample = (B : WithTop ℝ≥0))
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0))
    (hgeometry : (B : ℝ) + T ≤
      (n : ℝ) - (8 * (L * Real.sqrt B) + 1) - 8 * (a * Real.sqrt B + (gridError + 1 / 4)))
    (hend : s + r < T) (hstart : (T : ℝ) - W ≤ s)
    (hbacklog : L ≤ CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2) * (r : ℝ))
    (hbulk : sample ∉ bulkBackwardWindowBadEvent hlam0 hlamHalf eta B T s r)
    (hmoment : rightBoundaryMomentGood lam ((B : ℝ) + T) B L
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T))
    (hgrid : rightBoundaryIntervalGridGood n lam ((B : ℝ) + T) (1 / 8) gridError
      (fun _ ↦ (n : ℝ) - (8 * (L * Real.sqrt B) + 1))
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T) sample)
    (hcurrentH : |rightBoundaryFrozenCurrent lam ((B : ℝ) + T)
      ((n : ℝ) - (8 * (L * Real.sqrt B) + 1))
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T) sample| ≤ a * Real.sqrt B)
    (hpre : feedbackPreRightEnergy hlam0 hlamHalf eta B T sample ≤ Kpre * n)
    (hright : rightBoundaryFrozenEnergy lam ((B : ℝ) + T) ((n : ℝ) + 2 * B)
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T) sample ≤ Kright * (B : ℝ) ^ 2) :
    sample.graphComparisonEnergy
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ≤
      feedbackGraphEnergyLinearConstant amplitude Kpre Kright L a W * n := by
  let graph := sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T
  have hconstant := sample.stoppedGraph_curve_eq_actualFrozenHeight_of_survival
    hlam0 hlamHalf eta B T hNoTie hstop
  have hcurrentR : |sample.graphRankCurrent graph ((B : ℝ) + T)| ≤ L := by
    rw [sample.stoppedGraphRankCurrent_eq_boundaryRankDiscrepancy
      hlam0 hlamHalf eta B T hNoTie hstop,
      ← rightBoundaryUnseenGap_eq_rankDiscrepancy hlam0 hlamHalf B 0 T sample hNoTie]
    exact hmoment.2.2.1
  have hwindow := stoppedGraph_backwardWindows_of_not_bulkBackwardWindowBadEvent
    hlam0 hlamHalf eta B T s r W sample hNoTie hstop hend hstart
    (hcurrentR.trans hbacklog) hbulk
  have hdensity : sample.GraphIntervalLowerDensity graph ((B : ℝ) + T)
      ((n : ℝ) - (8 * (L * Real.sqrt B) + 1)) (1 / 8) (gridError + 1 / 4) := by
    have hd := hgrid.graphIntervalLowerDensity sample graph (by norm_num) herr0
      (by positivity) (by nlinarith [mul_nonneg hL (Real.sqrt_nonneg (B : ℝ))]) hconstant
    norm_num at hd
    exact hd
  have hRH : (B : ℝ) + T ≤ (n : ℝ) - (8 * (L * Real.sqrt B) + 1) := by
    have hrest : 0 ≤ 8 * (a * Real.sqrt B + (gridError + 1 / 4)) := by positivity
    linarith
  have hcurrentH' : |sample.graphRankCurrent graph
      ((n : ℝ) - (8 * (L * Real.sqrt B) + 1))| ≤ a * Real.sqrt B := by
    rw [sample.graphRankCurrent_eq_actualFrozenCurrent_of_constant_tail
      hlam0 hlamHalf B 0 T graph hNoTie hconstant _ hRH]
    exact hcurrentH
  have hcount : (sample.graphTerminalRankCount graph ((B : ℝ) + T) : ℝ) ≤ 4 * B := by
    have hn := sample.stoppedGraphTerminalRankCount_le_boundaryUnseenCounts
      hlam0 hlamHalf eta B T hNoTie hstop
    linarith [hmoment.1.2, hmoment.2.1.2]
  exact sample.stoppedGraphComparisonEnergy_le_linear_of_actual_controls
    hlam0 hlamHalf hn eta B T hB hB1 hL ha hW (by positivity) herr hNoTie hleftGeneric hleft
    hstop hgeometry hdensity hwindow.1 hwindow.2 hcurrentR hcurrentH' hmoment.2.2.2.1 hcount hpre hright

end OTSelector.FiniteSample
