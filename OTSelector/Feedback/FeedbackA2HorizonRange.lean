import OTSelector.Feedback.StoppedContinuationGraph
import OTSelector.Gauge.GraphFeedbackLocalization

/-!
# Actual range control for horizon and stopped feedback graphs

Bulk survival gives the strict shear bound before `T`, and continuity closes it at `T`.
Constant endpoint extension then gives a bound on the whole real line.  The public stopped-graph
result derives bulk survival from the actual A1, global-cut, and stopped-current good events; it
does not consume the old full-horizon current event or assume the target range conclusion.
-/

open Set
open scoped BigOperators NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-- The normalized deterministic-horizon feedback curve. -/
noncomputable def normalizedHorizonFeedbackCurve
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) : ℝ → ℝ :=
  normalizedCurveOfGraph (sample.horizonFeedbackGraph hlam0 hlamHalf B T) n

/-- The normalized unconditioned stopped-continuation feedback curve. -/
noncomputable def normalizedStoppedContinuationFeedbackCurve
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) : ℝ → ℝ :=
  normalizedCurveOfGraph
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) n

/-- Bulk survival and continuity bound the safe feedback height on the closed horizon. -/
theorem abs_safeFeedbackHeightAtElapsed_le_of_horizon_le_bulkExit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) {T : ℝ≥0}
    (hbulk : (T : WithTop ℝ≥0) ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample)
    {t : ℝ≥0} (ht : t ≤ T) :
    |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample| ≤ B / 8 := by
  by_cases htT : t < T
  · have htExit : (t : WithTop ℝ≥0) <
        safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
      (WithTop.coe_lt_coe.mpr htT).trans_le hbulk
    exact (feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B B 0 t sample htExit).2.2
  have hteq : t = T := le_antisymm ht (le_of_not_gt htT)
  subst t
  by_cases hT0 : T = 0
  · subst T
    have hzero :
        safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 0 sample = 0 := by
      by_cases hNoTie : sample.NoFeedbackTies lam B 0
      · rw [sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
          hlam0 hlamHalf B 0 0 hNoTie]
        simpa using sample.feedbackCurve_at_x0 hlam0 hlamHalf B 0
      · simp [safeFeedbackHeightAtElapsed, hNoTie]
    rw [hzero, abs_zero]
    exact div_nonneg hB.le (by norm_num)
  let height : ℝ≥0 → ℝ := fun s ↦
    safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 s sample
  let closedRange : Set ℝ≥0 := {s | |height s| ≤ B / 8}
  have hclosed : IsClosed closedRange := by
    exact isClosed_le
      (safeFeedbackHeightAtElapsed_continuous hlam0 hlamHalf B 0 sample).abs
      continuous_const
  have hsubset : Iio T ⊆ closedRange := by
    intro s hs
    have hsExit : (s : WithTop ℝ≥0) <
        safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
      (WithTop.coe_lt_coe.mpr hs).trans_le hbulk
    exact (feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B B 0 s sample hsExit).2.2
  have hnonempty : (Iio T : Set ℝ≥0).Nonempty := by
    refine ⟨0, ?_⟩
    exact pos_iff_ne_zero.mpr hT0
  have hTclosure : T ∈ closure (Iio T : Set ℝ≥0) := by
    rw [closure_Iio' hnonempty]
    exact mem_Iic.mpr le_rfl
  exact closure_minimal hsubset hclosed hTclosure

/-- No ties transfers the safe closed-horizon height bound to the horizon graph, whose two
exterior pieces are constant. -/
theorem abs_horizonFeedbackGraph_curve_le_of_horizon_le_bulkExit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) {T : ℝ≥0}
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hbulk : (T : WithTop ℝ≥0) ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample)
    (x : ℝ) :
    |(sample.horizonFeedbackGraph hlam0 hlamHalf B T).curve x| ≤ B / 8 := by
  by_cases hleft : x ≤ B
  · rw [sample.horizonFeedbackGraph_curve_eq_left hlam0 hlamHalf B T hleft, abs_zero]
    exact div_nonneg hB.le (by norm_num)
  by_cases hright : B + (T : ℝ) ≤ x
  · rw [sample.horizonFeedbackGraph_curve_eq_right hlam0 hlamHalf B T hright]
    rw [← sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
      hlam0 hlamHalf B 0 T hNoTie]
    exact sample.abs_safeFeedbackHeightAtElapsed_le_of_horizon_le_bulkExit
      hlam0 hlamHalf hB hbulk le_rfl
  · have hBx : B ≤ x := (lt_of_not_ge hleft).le
    have hxRight : x ≤ B + (T : ℝ) := (lt_of_not_ge hright).le
    let t : ℝ≥0 := ⟨x - B, sub_nonneg.mpr hBx⟩
    have ht : t ≤ T := by
      exact_mod_cast (show x - B ≤ (T : ℝ) by linarith)
    rw [sample.horizonFeedbackGraph_curve_eq_of_mem
      hlam0 hlamHalf B T ⟨hBx, hxRight⟩]
    have hsafe := sample.abs_safeFeedbackHeightAtElapsed_le_of_horizon_le_bulkExit
      hlam0 hlamHalf hB hbulk ht
    rw [sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
      hlam0 hlamHalf B 0 t hNoTie] at hsafe
    have hxt : B + (t : ℝ) = x := by
      change B + (x - B) = x
      ring
    rw [hxt] at hsafe
    exact hsafe

/-- The normalized horizon graph lies in `[-1,1]` once bulk survival is known. -/
theorem normalizedHorizonFeedbackCurve_mem_Icc_of_horizon_le_bulkExit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) {B : ℝ} (hB : 0 < B) {T : ℝ≥0}
    (hscale : B / 8 ≤ (n : ℝ))
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hbulk : (T : WithTop ℝ≥0) ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample) :
    ∀ z, sample.normalizedHorizonFeedbackCurve hlam0 hlamHalf B T z ∈
      Icc (-1 : ℝ) 1 := by
  intro z
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcurve := sample.abs_horizonFeedbackGraph_curve_le_of_horizon_le_bulkExit
    hlam0 hlamHalf hB hNoTie hbulk ((n : ℝ) * z)
  have habs : |sample.normalizedHorizonFeedbackCurve hlam0 hlamHalf B T z| ≤ 1 := by
    unfold normalizedHorizonFeedbackCurve normalizedCurveOfGraph normalizedGraph rescaleGraph
    rw [abs_div, abs_of_pos hnR]
    exact (div_le_one hnR).2 (hcurve.trans hscale)
  exact abs_le.mp habs

/-- The public stopped A2 good event gives the all-real normalized horizon range. -/
theorem normalizedHorizonFeedbackCurve_mem_Icc_of_actualGood
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n) (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hscale : B / 8 ≤ (n : ℝ))
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num))
        eta amplitude globalQ endpointQ B T R) :
    ∀ z, sample.normalizedHorizonFeedbackCurve
      hlam0.le (hlam.trans (by norm_num)) B T z ∈
      Icc (-1 : ℝ) 1 := by
  have hn0 : 0 < n := by omega
  have hA1 : sample ∈ feedbackA1GoodEvent n lam B 0 := by
    by_contra hbad
    apply hgood
    exact Or.inr (Or.inr (Or.inl hbad))
  have hbulk := feedbackA2StoppedGoodEvent.horizon_le_safeFeedbackBulkExitTime
    sample hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood
  exact sample.normalizedHorizonFeedbackCurve_mem_Icc_of_horizon_le_bulkExit
    hlam0.le (hlam.trans (by norm_num)) hn0 hB hscale
    (feedbackA1GoodEvent.noFeedbackTies hA1) hbulk

/-- On the same public stopped A2 good event, the normalized stopped graph lies in `[-1,1]`. -/
theorem normalizedStoppedContinuationFeedbackCurve_mem_Icc_of_actualGood
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n) (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hscale : B / 8 ≤ (n : ℝ))
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num))
        eta amplitude globalQ endpointQ B T R) :
    ∀ z, sample.normalizedStoppedContinuationFeedbackCurve
      hlam0.le (hlam.trans (by norm_num)) eta B T z ∈ Icc (-1 : ℝ) 1 := by
  have hgraph := feedbackA2StoppedGoodEvent.stoppedContinuationFeedbackGraph_eq_horizon
    sample hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood
  intro z
  rw [normalizedStoppedContinuationFeedbackCurve, hgraph]
  exact sample.normalizedHorizonFeedbackCurve_mem_Icc_of_actualGood
    hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hscale hgood z

/-- Actual stopped-graph FGL2 with range discharged by the A1/global-cut/stopped-current good
event. -/
theorem euclideanOptimizer_stoppedFeedbackEnergy_le_of_actualGood_of_comparisonEnergy
    {lam C : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n) (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hscale : B / 8 ≤ (n : ℝ))
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num))
        eta amplitude globalQ endpointQ B T R)
    (hcomparison :
      ∑ i, (sample.targetIntersection
            (sample.stoppedContinuationFeedbackGraph
              hlam0.le (hlam.trans (by norm_num)) eta B T)
            (sample.graphFeedbackComparisonAssignment
              (sample.stoppedContinuationFeedbackGraph
                hlam0.le (hlam.trans (by norm_num)) eta B T) i) -
          sample.sourceIntersection
            (sample.stoppedContinuationFeedbackGraph
              hlam0.le (hlam.trans (by norm_num)) eta B T) i) ^ 2 ≤
        C * (n : ℝ)) :
    ∑ i, (sample.targetIntersection
          (sample.stoppedContinuationFeedbackGraph
            hlam0.le (hlam.trans (by norm_num)) eta B T)
          (sample.euclideanOptimizer i) -
        sample.sourceIntersection
          (sample.stoppedContinuationFeedbackGraph
            hlam0.le (hlam.trans (by norm_num)) eta B T) i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
          (C * (n : ℝ)) := by
  let hlamHalf : lam < 1 / 2 := hlam.trans (by norm_num)
  let graph := sample.stoppedContinuationFeedbackGraph hlam0.le hlamHalf eta B T
  have hn0 : 0 < n := by omega
  have hrange : ∀ z, normalizedCurveOfGraph graph n z ∈ Icc (-1 : ℝ) 1 := by
    simpa only [graph, normalizedStoppedContinuationFeedbackCurve] using
      sample.normalizedStoppedContinuationFeedbackCurve_mem_Icc_of_actualGood
        hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hscale hgood
  exact sample.euclideanOptimizer_graphEnergy_le_of_comparisonEnergy
    graph hlam hn0 hrange hcomparison

end FiniteSample

end OTSelector
