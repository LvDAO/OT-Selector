import OTSelector.Feedback.RankEnergyOccupation
import OTSelector.Feedback.FeedbackGraphFrozenOccupation
import OTSelector.Feedback.FeedbackLeftPrefixEnergy
import OTSelector.Feedback.FeedbackInitialRankGapEnergy
import OTSelector.Feedback.FeedbackBulkEnergy

/-!
# Two-cut assembly of the actual graph comparison energy

The first cut separates the bulk from the frozen continuation. Edges crossing it retain an
explicit prefix contribution. A second cut separates the right retained suffixes from terminal
edges. The latter remain available for the existing terminal-window geometry.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector.FiniteSample
variable {n : ℕ} (sample : FiniteSample n)

noncomputable def graphLeftPrefixEnergy {lam : ℝ} (graph : FeedbackGraph lam) (B : ℝ) : ℝ :=
  ∑ r : Fin n, (min (sample.graphTargetIntersectionAtRank graph r) B -
    min (sample.graphSourceIntersectionAtRank graph r) B) ^ 2

noncomputable def graphLeftBoundaryRetainedSuffixEnergy {lam : ℝ}
    (graph : FeedbackGraph lam) (B H : ℝ) : ℝ :=
  ∑ r : Fin n, if sample.GraphLeftBoundaryRetainedRank graph B H r then
    (max 0 (sample.graphTargetIntersectionAtRank graph r - B) -
      max 0 (sample.graphSourceIntersectionAtRank graph r - B)) ^ 2 else 0

/-- Prefixes left of a cut of the edges which actually cross that cut. -/
noncomputable def graphCrossingPrefixEnergy {lam : ℝ} (graph : FeedbackGraph lam) (R : ℝ) : ℝ :=
  ∑ r ∈ sample.graphCrossingRankSet graph R,
    (R - sample.graphRankLeftEndpoint graph r) ^ 2

theorem graphLeftBoundaryRetainedRankEnergy_le_prefix_add_suffix {lam : ℝ}
    (graph : FeedbackGraph lam) (B H : ℝ) :
    sample.graphLeftBoundaryRetainedRankEnergy graph B H ≤
      2 * sample.graphLeftPrefixEnergy graph B +
        2 * sample.graphLeftBoundaryRetainedSuffixEnergy graph B H := by
  unfold graphLeftBoundaryRetainedRankEnergy graphLeftPrefixEnergy
    graphLeftBoundaryRetainedSuffixEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : sample.GraphLeftBoundaryRetainedRank graph B H r
  · simp only [hr, ite_true, graphSameRankGap]
    exact leftPrefix_rank_gap_sq_le_prefix_add_suffix _ _ _
  · simp only [hr, ite_false, mul_zero, add_zero]
    positivity

theorem graphRightTerminalRankEnergy_eq_terminalEnergy {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) :
    sample.graphRightTerminalRankEnergy graph H = sample.graphTerminalEnergy graph H := by
  simp only [graphRightTerminalRankEnergy, graphTerminalEnergy,
    graphTerminalRankSet, Finset.sum_filter]

private theorem graphSameRankGap_sq_eq_endpoint_gap_sq {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) :
    sample.graphSameRankGap graph r ^ 2 =
      (sample.graphRankRightEndpoint graph r - sample.graphRankLeftEndpoint graph r) ^ 2 := by
  rw [graphRankRightEndpoint, graphRankLeftEndpoint, max_sub_min_eq_abs, sq_abs]
  unfold graphSameRankGap
  ring

/-- Every edge ending between the two cuts is split at the first cut. The omitted left prefix
of a crossing edge is charged explicitly, rather than dropped by a retained-gap convention. -/
theorem graphRightTerminalRankEnergy_le_two_cut_parts {lam : ℝ}
    (graph : FeedbackGraph lam) {R H : ℝ} (hRH : R ≤ H) :
    sample.graphRightTerminalRankEnergy graph R ≤
      2 * sample.graphCrossingPrefixEnergy graph R +
        2 * sample.graphRightRetainedSuffixEnergy graph R H +
          sample.graphRightTerminalRankEnergy graph H := by
  unfold graphRightTerminalRankEnergy graphCrossingPrefixEnergy
    graphRightRetainedSuffixEnergy graphCrossingRankSet graphRightRetainedRankSet
  rw [Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r _
  by_cases hR : R < sample.graphRankRightEndpoint graph r
  · by_cases hH : H < sample.graphRankRightEndpoint graph r
    · simp only [GraphRightTerminalRank, hR, hH, ite_true,
        not_le_of_gt hH, and_false, ite_false, mul_zero, add_zero]
      exact le_add_of_nonneg_left (by positivity)
    · have hHr : sample.graphRankRightEndpoint graph r ≤ H := le_of_not_gt hH
      simp only [GraphRightTerminalRank, hR, hH, hHr, and_true,
        ite_true, ite_false, add_zero]
      rw [sample.graphSameRankGap_sq_eq_endpoint_gap_sq]
      by_cases hleft : sample.graphRankLeftEndpoint graph r ≤ R
      · rw [ite_eq_left hleft, max_eq_left hleft]
        nlinarith [sq_nonneg ((R - sample.graphRankLeftEndpoint graph r) -
          (sample.graphRankRightEndpoint graph r - R))]
      · rw [ite_eq_right hleft, max_eq_right (le_of_not_ge hleft)]
        simp only [mul_zero, zero_add]
        nlinarith [sq_nonneg (sample.graphRankRightEndpoint graph r -
          sample.graphRankLeftEndpoint graph r)]
  · have hH : ¬H < sample.graphRankRightEndpoint graph r :=
      not_lt_of_ge ((le_of_not_gt hR).trans hRH)
    simp only [GraphRightTerminalRank, hR, hH, and_false, false_and,
      ite_false, mul_zero, zero_add]
    exact le_rfl

/-- Full finite comparison energy, split at the left boundary, bulk/right boundary, and
terminal cut, with every crossing contribution retained. -/
theorem graphComparisonEnergy_le_two_cut_assembly {lam : ℝ}
    (graph : FeedbackGraph lam) (hn : 0 < n) (B : ℝ) {R H : ℝ} (hRH : R ≤ H) :
    sample.graphComparisonEnergy graph ≤
      2 * sample.graphLeftPrefixEnergy graph B +
      2 * sample.graphLeftBoundaryRetainedSuffixEnergy graph B R +
      sample.graphBulkRetainedRankEnergy graph B R +
      2 * sample.graphCrossingPrefixEnergy graph R +
      2 * sample.graphRightRetainedSuffixEnergy graph R H +
      sample.graphTerminalEnergy graph H := by
  rw [sample.graphComparisonEnergy_eq_sameRankGapEnergy graph hn,
    sample.graphSameRankGapEnergy_eq_three_regions graph B R]
  have hleft := sample.graphLeftBoundaryRetainedRankEnergy_le_prefix_add_suffix graph B R
  have hright := sample.graphRightTerminalRankEnergy_le_two_cut_parts graph hRH
  rw [sample.graphRightTerminalRankEnergy_eq_terminalEnergy graph H] at hright
  linarith

/-- Sufficient backward-window counts at the bulk/right boundary control the entire omitted
prefix by crossing multiplicity times the squared window length. -/
theorem graphCrossingPrefixEnergy_le_count_mul_window_sq {lam : ℝ}
    (graph : FeedbackGraph lam) (R W : ℝ) (hW : 0 ≤ W)
    (hsource : sample.graphCrossingRankCount graph R ≤
      sample.graphSourceBackwardWindowCount graph R W)
    (htarget : sample.graphCrossingRankCount graph R ≤
      sample.graphTargetBackwardWindowCount graph R W) :
    sample.graphCrossingPrefixEnergy graph R ≤
      (sample.graphCrossingRankCount graph R : ℝ) * W ^ 2 := by
  unfold graphCrossingPrefixEnergy graphCrossingRankCount
  calc
    _ ≤ ∑ _r ∈ sample.graphCrossingRankSet graph R, W ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      have hleft := sample.graphCrossingRank_leftEndpoint_ge_of_backward_windows
        graph R W hW hsource htarget r hr
      have hcut : sample.graphRankLeftEndpoint graph r ≤ R := (Finset.mem_filter.mp hr).2.1
      exact (sq_le_sq₀ (sub_nonneg.mpr hcut) hW).mpr (by linarith)
    _ = _ := by simp [nsmul_eq_mul]

/-- Combined deterministic bound consuming physical interval density and the actual backward
window count conditions. No matching-energy bound is assumed. -/
theorem graphComparisonEnergy_le_occupation_and_boundary_parts {lam : ℝ}
    (graph : FeedbackGraph lam) (hn : 0 < n) (B : ℝ) {R H c error W : ℝ}
    (hRH : R ≤ H) (hc : 0 < c) (herr : 0 ≤ error) (hW : 0 ≤ W)
    (hdensity : sample.GraphIntervalLowerDensity graph R H c error)
    (hsource : sample.graphCrossingRankCount graph R ≤
      sample.graphSourceBackwardWindowCount graph R W)
    (htarget : sample.graphCrossingRankCount graph R ≤
      sample.graphTargetBackwardWindowCount graph R W) :
    sample.graphComparisonEnergy graph ≤
      2 * sample.graphLeftPrefixEnergy graph B +
      2 * sample.graphLeftBoundaryRetainedSuffixEnergy graph B R +
      sample.graphBulkRetainedRankEnergy graph B R +
      2 * |sample.graphRankCurrent graph R| * W ^ 2 +
      (8 / c) * (∫ x in Icc R H, sample.graphRankCurrent graph x ^ 2) +
      (8 / c ^ 2) * (sample.graphTerminalRankCount graph R : ℝ) * error ^ 2 +
      sample.graphTerminalEnergy graph H := by
  have hall := sample.graphComparisonEnergy_le_two_cut_assembly graph hn B hRH
  have hp := sample.graphCrossingPrefixEnergy_le_count_mul_window_sq graph R W hW hsource htarget
  rw [sample.graphCrossingRankCount_cast_eq_abs_current] at hp
  have hs := sample.graphRightRetainedSuffixEnergy_le_occupation graph hc herr hdensity
  simp only [div_eq_mul_inv] at hs ⊢
  nlinarith only [hall, hp, hs]

private theorem capped_time_toNNReal_eq_max (T : ℝ≥0)
    (tau : FiniteSample n → WithTop ℝ≥0) (x : ℝ)
    (htau : tau sample = (Real.toNNReal x : WithTop ℝ≥0)) (hx : x ≤ T) :
    (CountingProcess.cappedStoppingValue T tau sample : ℝ) = max 0 x := by
  have hcap : CountingProcess.cappedStoppingValue T tau sample = Real.toNNReal x := by
    apply WithTop.coe_injective
    rw [CountingProcess.coe_cappedStoppingValue, htau,
      min_eq_left (WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hx))]
  rw [hcap, Real.coe_toNNReal', max_comm]

/-- On a rank retained by the actual bulk stop, the initial stopped gaps give exactly its
suffix after the left boundary. -/
theorem initialStoppedGaps_sq_sum_eq_horizon_left_suffix
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0))
    (hr : sample.GraphLeftBoundaryRetainedRank
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) B (B + (T : ℝ)) r) :
    sourceInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample ^ 2 +
      targetInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample ^ 2 =
      (max 0 (sample.graphTargetIntersectionAtRank
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r - B) -
        max 0 (sample.graphSourceIntersectionAtRank
          (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r - B)) ^ 2 := by
  let s := sample.graphSourceIntersectionAtRank
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r
  let t := sample.graphTargetIntersectionAtRank
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r
  have hsH : s ≤ B + (T : ℝ) := (max_le_iff.mp hr.2).1
  have htH : t ≤ B + (T : ℝ) := (max_le_iff.mp hr.2).2
  have hsTime : sourceFullRankEventTime hlam0 hlamHalf B r sample =
      (Real.toNNReal (s - B) : WithTop ℝ≥0) := by
    rw [sourceFullRankEventTime_eq_toNNReal_sourceIntersection_sub_B
      hlam0 hlamHalf B r sample hNoTie]
    congr 2
    exact congrArg (fun x : ℝ ↦ x - B)
      (sample.graphSourceIntersectionAtRank_horizon_eq_raw_of_horizon_le_right
        hlam0 hlamHalf B T r hsH).symm
  have htTime : targetFullRankEventTime hlam0 hlamHalf B r sample =
      (Real.toNNReal (t - B) : WithTop ℝ≥0) := by
    rw [targetFullRankEventTime_eq_toNNReal_targetIntersection_sub_B
      hlam0 hlamHalf B r sample hNoTie]
    congr 2
    exact congrArg (fun x : ℝ ↦ x - B)
      (sample.graphTargetIntersectionAtRank_horizon_eq_raw_of_horizon_le_right
        hlam0 hlamHalf B T r htH).symm
  have hsCap := sample.capped_time_toNNReal_eq_max T _ (s - B) hsTime (by linarith)
  have htCap := sample.capped_time_toNNReal_eq_max T _ (t - B) htTime (by linarith)
  have hsT : sourceFullRankEventTime hlam0 hlamHalf B r sample ≤ (T : WithTop ℝ≥0) := by
    rw [hsTime, WithTop.coe_le_coe]
    exact Real.toNNReal_le_iff_le_coe.mpr (by linarith)
  have htT : targetFullRankEventTime hlam0 hlamHalf B r sample ≤ (T : WithTop ℝ≥0) := by
    rw [htTime, WithTop.coe_le_coe]
    exact Real.toNNReal_le_iff_le_coe.mpr (by linarith)
  have hsZero : sourceFullRankEventTime hlam0 hlamHalf B r sample = 0 ↔ s ≤ B := by
    rw [hsTime]
    simp only [WithTop.coe_eq_zero, Real.toNNReal_eq_zero, sub_nonpos]
  have htZero : targetFullRankEventTime hlam0 hlamHalf B r sample = 0 ↔ t ≤ B := by
    rw [htTime]
    simp only [WithTop.coe_eq_zero, Real.toNNReal_eq_zero, sub_nonpos]
  have hsPos : 0 < sourceFullRankEventTime hlam0 hlamHalf B r sample ↔ B < s := by
    rw [hsTime]
    simp only [WithTop.coe_pos, Real.toNNReal_pos, sub_pos]
  have htPos : 0 < targetFullRankEventTime hlam0 hlamHalf B r sample ↔ B < t := by
    rw [htTime]
    simp only [WithTop.coe_pos, Real.toNNReal_pos, sub_pos]
  change _ = (max 0 (t - B) - max 0 (s - B)) ^ 2
  simp only [sourceInitialStoppedFullRankGap, targetInitialStoppedFullRankGap,
    hstop, hsT, htT, and_true, hsZero, htZero, hsPos, htPos, hsCap, htCap]
  have hmin : s ≤ B ∨ t ≤ B := min_le_iff.mp hr.1
  rcases hmin with hs | ht
  · by_cases ht : t ≤ B
    · simp [hs, ht, not_lt_of_ge hs, not_lt_of_ge ht]
    · simp [hs, ht, not_lt_of_ge hs, lt_of_not_ge ht]
  · by_cases hs : s ≤ B
    · simp [hs, ht, not_lt_of_ge hs, not_lt_of_ge ht]
    · simp [hs, ht, not_lt_of_ge ht, lt_of_not_ge hs]

/-- The actual retained left suffix is dominated by the already controlled initial-gap
random variable, on the genuine A1 survival event. -/
theorem horizon_leftRetainedSuffixEnergy_le_initialStoppedEnergy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) :
    sample.graphLeftBoundaryRetainedSuffixEnergy
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) B (B + (T : ℝ)) ≤
      (∑ r : Fin n, sourceInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample ^ 2) +
        ∑ r : Fin n, targetInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample ^ 2 := by
  rw [graphLeftBoundaryRetainedSuffixEnergy, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : sample.GraphLeftBoundaryRetainedRank
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) B (B + (T : ℝ)) r
  · rw [ite_eq_left hr]
    exact (sample.initialStoppedGaps_sq_sum_eq_horizon_left_suffix
      hlam0 hlamHalf eta B T r hNoTie hstop hr).symm.le
  · rw [ite_eq_right hr]
    positivity

/-- The actual initial-crossing suffix energy already controlled by the initial current law. -/
noncomputable def feedbackInitialSuffixEnergy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  (∑ r : Fin n, sourceInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample ^ 2) +
    ∑ r : Fin n, targetInitialStoppedFullRankGap hlam0 hlamHalf eta B T r sample ^ 2

/-- A genuine random majorant for every edge ending before the frozen right continuation. -/
noncomputable def feedbackPreRightEnergy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta : ℝ) (B T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  2 * stoppedLeftPrefixEnergy B sample +
    2 * feedbackInitialSuffixEnergy hlam0 hlamHalf eta B T sample +
      feedbackBulkInteriorEnergy hlam0 hlamHalf eta B T sample

theorem feedbackPreRightEnergy_nonneg
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta : ℝ) (B T : ℝ≥0) : 0 ≤ feedbackPreRightEnergy hlam0 hlamHalf eta B T sample := by
  unfold feedbackPreRightEnergy stoppedLeftPrefixEnergy CountingProcess.stoppedRankGapEnergy
    feedbackInitialSuffixEnergy feedbackBulkInteriorEnergy
  positivity

/-- Actual first-stage energy expectation; all three probabilistic inputs are instantiated. -/
theorem feedbackPreRightEnergy_integrable_and_integral_le
    {lam eta : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) {B : ℝ≥0} (hB : 0 < B) (hBquarter : 4 * (B : ℝ) ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) :
    Integrable (feedbackPreRightEnergy (n := n) hlam0.le (by linarith) eta B T)
      (finiteSampleLaw n) ∧
    (∫ sample : FiniteSample n,
      feedbackPreRightEnergy hlam0.le (by linarith) eta B T sample ∂(finiteSampleLaw n)) ≤
      8 * (1 / CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2 +
        2 / CountingProcess.lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2) *
          ((B : ℝ) + (B : ℝ) ^ 2) +
      2 * ((2 * (B : ℝ) + 5 * (B : ℝ) * Real.sqrt B) /
        CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2 +
          4 * (n : ℝ) / CountingProcess.lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2) +
      (6 / CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2) *
        ((2 * (B : ℝ) + 5 * (B : ℝ) * Real.sqrt B +
          (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) +
        4 * (n : ℝ) / CountingProcess.lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  have hBn : (B : ℝ) ≤ n := by nlinarith [B.2]
  have hleft := stoppedLeftPrefixEnergy_integrable_and_integral_le hn hB hBquarter
  have hinitial := source_targetInitialStoppedFullRankGap_sq_sum_integrable_and_integral_le
    hlam0 hlam hn (show 0 < (B : ℝ) from hB) hBn heta0 hetaSmall T
  have hbulk := feedbackBulkInteriorEnergy_integrable_and_integral_le
    hlam0 hlam hn (show 0 < (B : ℝ) from hB) hBn heta0 hetaSmall T
  have hinit : Integrable (feedbackInitialSuffixEnergy (n := n) hlam0.le (by linarith) eta B T)
      (finiteSampleLaw n) := hinitial.1
  refine ⟨((hleft.1.const_mul 2).add (hinit.const_mul 2)).add hbulk.1, ?_⟩
  change (∫ sample : FiniteSample n,
    (2 * stoppedLeftPrefixEnergy B sample +
      2 * feedbackInitialSuffixEnergy hlam0.le (by linarith) eta B T sample) +
      feedbackBulkInteriorEnergy hlam0.le (by linarith) eta B T sample ∂(finiteSampleLaw n)) ≤ _
  have hsum : Integrable (fun sample : FiniteSample n ↦
      2 * stoppedLeftPrefixEnergy B sample +
        2 * feedbackInitialSuffixEnergy hlam0.le (by linarith) eta B T sample)
        (finiteSampleLaw n) := (hleft.1.const_mul 2).add (hinit.const_mul 2)
  rw [integral_add hsum hbulk.1,
    integral_add (hleft.1.const_mul 2) (hinit.const_mul 2), integral_const_mul, integral_const_mul]
  have hi := hinitial.2
  change (∫ sample : FiniteSample n,
    feedbackInitialSuffixEnergy hlam0.le (by linarith) eta B T sample ∂(finiteSampleLaw n)) ≤ _ at hi
  linarith [hleft.2, hbulk.2]

/-- Actual stopped-continuation comparison energy, using the already integrable first-stage
majorant. The remaining inputs concern physical right interval counts and a boundary window. -/
theorem stoppedGraphComparisonEnergy_le_preRight_and_rightOccupation
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (eta : ℝ) (B T : ℝ≥0) {H c error W : ℝ}
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hleftGeneric : sample ∈ leftHeightGenericEvent n)
    (hleft : leftRateExitTime n B sample = (B : WithTop ℝ≥0))
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0))
    (hRH : (B : ℝ) + T ≤ H) (hc : 0 < c) (herr : 0 ≤ error) (hW : 0 ≤ W)
    (hdensity : sample.GraphIntervalLowerDensity
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
      ((B : ℝ) + T) H c error)
    (hsource : sample.graphCrossingRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) ≤
      sample.graphSourceBackwardWindowCount
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) W)
    (htarget : sample.graphCrossingRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) ≤
      sample.graphTargetBackwardWindowCount
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) W) :
    let graph := sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T
    sample.graphComparisonEnergy graph ≤
      feedbackPreRightEnergy hlam0 hlamHalf eta B T sample +
      2 * |sample.graphRankCurrent graph ((B : ℝ) + T)| * W ^ 2 +
      (8 / c) * (∫ x in Icc ((B : ℝ) + T) H, sample.graphRankCurrent graph x ^ 2) +
      (8 / c ^ 2) * (sample.graphTerminalRankCount graph ((B : ℝ) + T) : ℝ) * error ^ 2 +
      sample.graphTerminalEnergy graph H := by
  let graph := sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T
  have hgraph := sample.stoppedContinuationFeedbackGraph_eq_horizon hlam0 hlamHalf eta B T hstop
  have hprefix : sample.graphLeftPrefixEnergy graph B = stoppedLeftPrefixEnergy B sample := by
    dsimp [graph]
    rw [hgraph]
    exact (stoppedLeftPrefixEnergy_eq_graph_prefix_of_survival
      hlam0 hlamHalf B T hleftGeneric hleft).symm
  have hinitial : sample.graphLeftBoundaryRetainedSuffixEnergy graph B ((B : ℝ) + T) ≤
      feedbackInitialSuffixEnergy hlam0 hlamHalf eta B T sample := by
    dsimp [graph]
    rw [hgraph]
    exact sample.horizon_leftRetainedSuffixEnergy_le_initialStoppedEnergy
      hlam0 hlamHalf eta B T hNoTie hstop
  have hbulk := feedbackBulkInteriorEnergy_eq_stoppedGraphBulk_of_survival
    hlam0 hlamHalf eta B T sample hNoTie hstop
  have hall := sample.graphComparisonEnergy_le_occupation_and_boundary_parts
    graph hn B hRH hc herr hW hdensity hsource htarget
  rw [hprefix, ← hbulk] at hall
  dsimp only [feedbackPreRightEnergy]
  linarith

/-- Open-interval density supplies the closed backward windows required by terminal geometry. -/
theorem graphBackwardWindows_of_intervalLowerDensity
    {lam : ℝ} (graph : FeedbackGraph lam) {R H c error W : ℝ}
    (hdensity : sample.GraphIntervalLowerDensity graph R H c error)
    (hW : 0 ≤ W) (hRW : R ≤ H - W)
    (hcurrent : |sample.graphRankCurrent graph H| ≤ c * W - error) :
    sample.graphCrossingRankCount graph H ≤ sample.graphSourceBackwardWindowCount graph H W ∧
      sample.graphCrossingRankCount graph H ≤ sample.graphTargetBackwardWindowCount graph H W := by
  have hd := hdensity (H - W) H hRW (by linarith) le_rfl
  have hs : sample.graphSourceOpenIntervalCount graph (H - W) H ≤
      sample.graphSourceBackwardWindowCount graph H W := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1.le, hi.2.le⟩
  have ht : sample.graphTargetOpenIntervalCount graph (H - W) H ≤
      sample.graphTargetBackwardWindowCount graph H W := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1.le, hi.2.le⟩
  constructor
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [sample.graphCrossingRankCount_cast_eq_abs_current]
    have hsR : (sample.graphSourceOpenIntervalCount graph (H - W) H : ℝ) ≤
        sample.graphSourceBackwardWindowCount graph H W := by exact_mod_cast hs
    linarith [hd.1]
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [sample.graphCrossingRankCount_cast_eq_abs_current]
    have htR : (sample.graphTargetOpenIntervalCount graph (H - W) H : ℝ) ≤
        sample.graphTargetBackwardWindowCount graph H W := by exact_mod_cast ht
    linarith [hd.2]

/-- A single current bound and the already available right density control all terminal ranks.
The count is taken at the earlier boundary, so no new terminal-count upper-tail estimate is needed. -/
theorem graphTerminalEnergy_le_of_density_and_current
    {lam : ℝ} (graph : FeedbackGraph lam) {R q H c error W : ℝ}
    (hconstant : ∀ x, R ≤ x → graph.curve x = q)
    (hRH : R ≤ H) (hH : H ≤ (n : ℝ) + 2 * |q|)
    (hdensity : sample.GraphIntervalLowerDensity graph R H c error)
    (hW : 0 ≤ W) (hRW : R ≤ H - W)
    (hcurrent : |sample.graphRankCurrent graph H| ≤ c * W - error) :
    sample.graphTerminalEnergy graph H ≤
      (sample.graphTerminalRankCount graph R : ℝ) * ((n : ℝ) + 2 * |q| - H + W) ^ 2 := by
  have hw := sample.graphBackwardWindows_of_intervalLowerDensity graph hdensity hW hRW hcurrent
  apply sample.graphTerminalEnergy_le_of_count_le_of_maxGap_le
    graph H ((n : ℝ) + 2 * |q| - H + W) (sample.graphTerminalRankCount graph R)
  · apply Finset.card_le_card
    intro r hr
    simp only [graphTerminalRankSet, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact hRH.trans_lt hr
  · exact sample.graphTerminalMaxAbsGap_le_of_crossing_windows_and_endpoint_bound
      graph H W ((n : ℝ) + 2 * |q|) hW hH
      (sample.graphRankRightEndpoint_le_of_constant_tail graph R q hconstant (hRH.trans hH))
      hw.1 hw.2
  · linarith

/-- The actual graph energy is bounded by the two genuine random energies already carrying
expectation estimates, and explicit boundary/window errors. -/
theorem stoppedGraphComparisonEnergy_le_actual_energies
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (eta : ℝ) (B T : ℝ≥0) {H c error W V L Q M : ℝ}
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hleftGeneric : sample ∈ leftHeightGenericEvent n)
    (hleft : leftRateExitTime n B sample = (B : WithTop ℝ≥0))
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0))
    (hRH : (B : ℝ) + T ≤ H) (hHn : H ≤ n)
    (hc : 0 < c) (herr : 0 ≤ error) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hRV : (B : ℝ) + T ≤ H - V)
    (hdensity : sample.GraphIntervalLowerDensity
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
      ((B : ℝ) + T) H c error)
    (hsource : sample.graphCrossingRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) ≤
      sample.graphSourceBackwardWindowCount
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) W)
    (htarget : sample.graphCrossingRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) ≤
      sample.graphTargetBackwardWindowCount
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) W)
    (hcurrentR : |sample.graphRankCurrent
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T)| ≤ L)
    (hcurrentH : |sample.graphRankCurrent
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) H| ≤ c * V - error)
    (hq : |actualRightTailFrozenHeight hlam0 hlamHalf B 0 T sample| ≤ Q)
    (hcount : (sample.graphTerminalRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) : ℝ) ≤ M) :
    sample.graphComparisonEnergy
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ≤
      feedbackPreRightEnergy hlam0 hlamHalf eta B T sample + 2 * L * W ^ 2 +
      (8 / c) * rightBoundaryFrozenEnergy lam ((B : ℝ) + T) ((n : ℝ) + 2 * B)
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T) sample +
      M * ((8 / c ^ 2) * error ^ 2 + ((n : ℝ) + 2 * Q - H + V) ^ 2) := by
  let graph := sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T
  let q := actualRightTailFrozenHeight hlam0 hlamHalf B 0 T sample
  have hq0 : 0 ≤ Q := (abs_nonneg _).trans hq
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans hcount
  have hall := sample.stoppedGraphComparisonEnergy_le_preRight_and_rightOccupation
    hlam0 hlamHalf hn eta B T hNoTie hleftGeneric hleft hstop hRH hc herr hW
    hdensity hsource htarget
  have hocc := sample.stoppedGraph_rightOccupation_le_actualFrozenEnergy
    hlam0 hlamHalf eta B T
    (show H ≤ (n : ℝ) + 2 * (B : ℝ) from
      hHn.trans (le_add_of_nonneg_right (by positivity))) hNoTie hstop
  have hterm := sample.graphTerminalEnergy_le_of_density_and_current graph
    (sample.stoppedGraph_curve_eq_actualFrozenHeight_of_survival
      hlam0 hlamHalf eta B T hNoTie hstop) hRH
    (show H ≤ (n : ℝ) + 2 * |q| by linarith [abs_nonneg q])
    hdensity hV hRV hcurrentH
  have hwidth : ((n : ℝ) + 2 * |q| - H + V) ^ 2 ≤
      ((n : ℝ) + 2 * Q - H + V) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith [abs_nonneg q])
    dsimp [q]
    linarith
  have hterminal : sample.graphTerminalEnergy graph H ≤
      M * ((n : ℝ) + 2 * Q - H + V) ^ 2 :=
    hterm.trans (mul_le_mul hcount hwidth (sq_nonneg _) hM0)
  have hcross := mul_le_mul_of_nonneg_right hcurrentR
    (show 0 ≤ 2 * W ^ 2 by positivity)
  have herror := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ (8 / c ^ 2) * error ^ 2 by positivity)
  have henergy := mul_le_mul_of_nonneg_left hocc (show 0 ≤ 8 / c by positivity)
  dsimp only [graph] at hterminal
  dsimp only at hall
  nlinarith only [hall, hterminal, hcross, herror, henergy]

end OTSelector.FiniteSample
