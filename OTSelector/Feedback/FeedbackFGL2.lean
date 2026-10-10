import OTSelector.Feedback.FeedbackGraphEnergyTail
import OTSelector.Feedback.FeedbackGraphEnergyAsymptotic
import OTSelector.Feedback.FeedbackRightBoundaryAsymptotic
import OTSelector.Feedback.FeedbackI4

/-!
# Finite-sample FGL2 for the actual stopped feedback graph

The graph uses the standard square-root buffer and the deterministic A2 horizon.  All energy
probabilities below refer to the original finite-sample law and the original Euclidean optimizer.
-/

open Filter MeasureTheory Set
open scoped BigOperators NNReal Topology

namespace OTSelector.FiniteSample

/-- The actual graph used simultaneously for finite energy localization and I4. -/
noncomputable def feedbackFGL2Graph {n : ℕ} (sample : FiniteSample n)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (amplitude : ℝ) :
    FeedbackGraph lam :=
  sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf (feedbackA2AsymptoticEta lam)
    (feedbackA2AsymptoticBuffer amplitude n) (feedbackA2AsymptoticHorizon amplitude n)

/-- Squared rank-scale displacement of the actual Euclidean optimizer through the same graph. -/
noncomputable def feedbackFGL2OptimizerEnergy {n : ℕ} (sample : FiniteSample n)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (amplitude : ℝ) : ℝ :=
  ∑ i, (sample.targetIntersection (sample.feedbackFGL2Graph hlam0 hlamHalf amplitude)
      (sample.euclideanOptimizer i) -
    sample.sourceIntersection (sample.feedbackFGL2Graph hlam0 hlamHalf amplitude) i) ^ 2

private theorem exists_positive_div_small (V : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ V / K < ε := by
  have hlim : Tendsto (fun K : ℝ ↦ V / K) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := V)).mul tendsto_inv_atTop_zero
  exact ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (eventually_lt_nhds hε))).exists

/-- The closed A2 range event transfers comparison energy to the actual optimizer. -/
theorem eventually_feedbackFGL2OptimizerEnergy_le_of_A2Good_of_comparisonEnergy
    {lam amplitude globalQ endpointQ C : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hglobalQ : 0 < globalQ) (hcoefficient : 8 * (globalQ + 33) < amplitude) :
    ∀ᶠ n : ℕ in atTop, ∀ sample : FiniteSample n,
      sample ∈ feedbackA2AsymptoticGoodEvent hlam0 hlam amplitude globalQ endpointQ n →
      sample.graphComparisonEnergy
        (sample.feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude) ≤ C * n →
      sample.feedbackFGL2OptimizerEnergy hlam0.le (hlam.trans (by norm_num)) amplitude ≤
        (quadraticUpperConstant lam /
          (euclideanCurvatureLower * quadraticLowerConstant' lam)) * (C * n) := by
  have hamp : 0 < amplitude := by linarith
  filter_upwards [eventually_feedbackA2Asymptotic_horizon_geometry hamp,
    eventually_feedbackA2Asymptotic_regularity_inequalities hlam0 hamp,
    eventually_feedbackA2Asymptotic_threshold hcoefficient] with n hn hreg hthreshold
  intro sample hgood henergy
  exact sample.euclideanOptimizer_stoppedFeedbackEnergy_le_of_actualGood_of_comparisonEnergy
    hlam0 hlam hn.1 hn.2.1 hn.2.2.1 (feedbackA2AsymptoticEta_pos hlam0).le
    hn.2.2.2.1.le hreg.1 hreg.2 hthreshold hn.2.2.2.2.2 hgood henergy

/-- Fixed parameters make both the A2 bad probability and the actual comparison-energy
probability arbitrarily small.  Every tail term is supplied by an original-law estimate. -/
theorem exists_feedbackFGL2_comparison_parameters
    {lam δ : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hδ : 0 < δ) :
    ∃ globalQ endpointQ amplitude C : ℝ,
      0 < globalQ ∧ 1 ≤ endpointQ ∧ 8 * (globalQ + 33) < amplitude ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2AsymptoticBadEvent hlam0 hlam amplitude globalQ endpointQ n) < δ ∧
        (finiteSampleLaw n : Measure (FiniteSample n)).real {sample |
          C * n < sample.graphComparisonEnergy
            (sample.feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)} < δ := by
  let ε := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨globalQ, endpointQ, amplitude, L, hglobalQ, hendpointQ, hcoefficient, hL, hgood⟩ :=
    exists_feedbackRightBoundaryAsymptotic_parameters_bad_probability_lt hlam0 hlam hε
  have hamp : 0 < amplitude := by linarith
  obtain ⟨Kpre, hKpre, hpre⟩ :=
    exists_positive_div_small (feedbackPreRightEnergyLinearConstant lam amplitude) hε
  obtain ⟨Kright, hKright, hright⟩ :=
    exists_positive_div_small (3 * (4 + (17 * L) ^ 2)) hε
  obtain ⟨Kcurrent, hKcurrent, hcurrent⟩ :=
    exists_positive_div_small (4 + (17 * L) ^ 2) hε
  let a := Real.sqrt Kcurrent
  have ha : 0 < a := Real.sqrt_pos.mpr hKcurrent
  have hcurrent' : (4 + (17 * L) ^ 2) / a ^ 2 < ε := by
    simpa only [a, Real.sq_sqrt hKcurrent.le] using hcurrent
  obtain ⟨r, hr, hbacklog, hbulk⟩ := exists_bulk_window_small_failure L hε
  let W : ℝ := 2 * (r : ℝ)
  let C := feedbackGraphEnergyLinearConstant amplitude Kpre Kright L a W
  have hC : 0 < C := by
    dsimp only [C, feedbackGraphEnergyLinearConstant]
    positivity
  refine ⟨globalQ, endpointQ, amplitude, C, hglobalQ, hendpointQ, hcoefficient, hC, ?_⟩
  filter_upwards [hgood, eventually_feedbackA2Asymptotic_horizon_geometry hamp,
    eventually_feedbackA2Asymptotic_regularity_inequalities hlam0 hamp,
    eventually_feedbackA2Asymptotic_threshold hcoefficient,
    eventually_feedback_buffer_quarter amplitude,
    eventually_feedbackRightDensityError_le_sqrt_buffer hamp,
    eventually_feedbackRight_energy_geometry hamp hL.le ha.le,
    eventually_feedback_horizon_gt hamp W,
    (tendsto_feedback_energy_remainder hamp).eventually (eventually_lt_nhds hε)]
      with n hgoodn hgeom hreg hthreshold hquarter herror hterminal hlong hremainder
  let B : ℝ≥0 := ⟨amplitude * Real.sqrt n, mul_nonneg hamp.le (Real.sqrt_nonneg _)⟩
  let T := feedbackA2AsymptoticHorizon amplitude n
  let s : ℝ≥0 := T - 2 * r
  have hboundary : (B : ℝ) + T = (n : ℝ) - B := hgeom.2.2.2.1
  have hlong' : 2 * r < T := by exact_mod_cast hlong
  have hT : 0 < T := (by positivity : (0 : ℝ≥0) ≤ 2 * r).trans_lt hlong'
  have hs : (s : ℝ) = (T : ℝ) - 2 * (r : ℝ) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using NNReal.coe_sub hlong'.le
  have hend : s + r < T := by
    change (s : ℝ) + (r : ℝ) < (T : ℝ)
    rw [hs]
    have hrR : 0 < (r : ℝ) := hr
    linarith
  have hstart : (T : ℝ) - W ≤ s := by dsimp only [W]; rw [hs]
  have hgeometry : (B : ℝ) + T ≤ (n : ℝ) - (8 * (L * Real.sqrt B) + 1) -
      8 * (a * Real.sqrt B + (60 * Real.log n + 1 / 4)) := by
    have ht : 8 * (L * Real.sqrt B) + 1 +
        8 * (a * Real.sqrt B + (60 * Real.log n + 1 / 4)) ≤ (B : ℝ) := hterminal.2.2
    linarith
  have henergy := measureReal_stoppedGraphComparisonEnergy_tail_le (endpointQ := endpointQ)
    hlam0 hlam hgeom.1 hamp B T s r (feedbackA2AsymptoticRadius n)
    rfl hterminal.1 hquarter hboundary hT
    (feedbackA2AsymptoticEta_pos hlam0).le (feedbackA2AsymptoticEta_small hlam0)
    hreg.1 hreg.2 hthreshold hL.le ha (by dsimp [W]; positivity) hr hKpre hKright
    herror.2 hgeometry hend hstart hbacklog
  change (finiteSampleLaw n : Measure (FiniteSample n)).real {sample |
      C * n < sample.graphComparisonEnergy
        (sample.feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)} ≤
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      (feedbackA2AsymptoticBadEvent hlam0 hlam amplitude globalQ endpointQ n) +
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      (feedbackRightBoundaryAsymptoticMomentGoodEvent
        hlam0.le (hlam.trans (by norm_num)) amplitude L n)ᶜ +
    4 * Real.exp (-(amplitude * Real.sqrt n) / 8) + 16 / (n : ℝ) ^ 3 +
    2 * Real.exp (-CountingProcess.lowerOccupationDecayRate ((1 : ℝ) / 2) * (r : ℝ)) +
    feedbackPreRightEnergyLinearConstant lam amplitude / Kpre +
    3 * (4 + (17 * L) ^ 2) / Kright + (4 + (17 * L) ^ 2) / a ^ 2 at henergy
  dsimp only [ε] at hgoodn hremainder hbulk hpre hright hcurrent'
  exact ⟨by linarith [hgoodn.1], by linarith [hgoodn.1, hgoodn.2]⟩

/-- The actual increasing comparison assignment has an arbitrarily small linear energy tail
for a fixed choice of square-root buffer amplitude and energy constant. -/
theorem exists_feedbackFGL2_comparison_energy_bound
    {lam δ : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hδ : 0 < δ) :
    ∃ amplitude C : ℝ, 0 < amplitude ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (finiteSampleLaw n : Measure (FiniteSample n)).real {sample |
          C * n < sample.graphComparisonEnergy
            (sample.feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)} < δ := by
  obtain ⟨globalQ, endpointQ, amplitude, C, hglobalQ, _, hcoefficient, hC, htail⟩ :=
    exists_feedbackFGL2_comparison_parameters hlam0 hlam hδ
  exact ⟨amplitude, C, by linarith, hC, htail.mono fun _ hn ↦ hn.2⟩

/-- Actual finite-sample FGL2: after choosing a square-root buffer amplitude and one energy
constant, the Euclidean optimizer's graph displacement has an arbitrarily small linear tail. -/
theorem exists_feedbackFGL2_optimizer_energy_bound
    {lam δ : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hδ : 0 < δ) :
    ∃ amplitude C : ℝ, 0 < amplitude ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (finiteSampleLaw n : Measure (FiniteSample n)).real {sample |
          C * n < sample.feedbackFGL2OptimizerEnergy
            hlam0.le (hlam.trans (by norm_num)) amplitude} < δ := by
  obtain ⟨globalQ, endpointQ, amplitude, C, hglobalQ, hendpointQ, hcoefficient, hC, htail⟩ :=
    exists_feedbackFGL2_comparison_parameters hlam0 hlam (show 0 < δ / 2 by positivity)
  have hamp : 0 < amplitude := by linarith
  let ratio := quadraticUpperConstant lam /
    (euclideanCurvatureLower * quadraticLowerConstant' lam)
  have hratio : 0 < ratio := by
    apply div_pos
    · unfold quadraticUpperConstant
      positivity
    · exact mul_pos euclideanCurvatureLower_pos (quadraticLowerConstant'_pos hlam0.le hlam)
  refine ⟨amplitude, ratio * C, hamp, mul_pos hratio hC, ?_⟩
  filter_upwards [htail,
    eventually_feedbackFGL2OptimizerEnergy_le_of_A2Good_of_comparisonEnergy
      (C := C) (endpointQ := endpointQ) hlam0 hlam hglobalQ hcoefficient]
    with n hn htransfer
  have hsubset : {sample : FiniteSample n |
      (ratio * C) * n < sample.feedbackFGL2OptimizerEnergy
        hlam0.le (hlam.trans (by norm_num)) amplitude} ⊆
      feedbackA2AsymptoticBadEvent hlam0 hlam amplitude globalQ endpointQ n ∪
      {sample | C * n < sample.graphComparisonEnergy
        (sample.feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)} := by
    intro sample hlarge
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot
    have hbound := htransfer sample hnot.1 hnot.2
    change _ ≤ ratio * (C * n) at hbound
    rw [← mul_assoc] at hbound
    exact (not_lt_of_ge hbound) hlarge
  have h0 := measureReal_mono (μ := (finiteSampleLaw n : Measure (FiniteSample n))) hsubset
  have h1 := measureReal_union_le (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (feedbackA2AsymptoticBadEvent hlam0 hlam amplitude globalQ endpointQ n)
    {sample | C * n < sample.graphComparisonEnergy
      (sample.feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude)}
  linarith [hn.1, hn.2]

/-- I4 holds for exactly the graph used in the energy theorems: each fixed normalized envelope
threshold has zero probability for all sufficiently large rows. -/
theorem eventually_feedbackFGL2Graph_supAbs_tail_eq_zero
    {lam amplitude ε : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hamp : 0 < amplitude) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw n : Measure (FiniteSample n)).real {sample |
        ε ≤ graphSupAbs (normalizedCurveOfGraph
          (sample.feedbackFGL2Graph hlam0 hlamHalf amplitude) n)} = 0 := by
  exact eventually_normalizedStoppedContinuationFeedbackCurve_supAbs_tail_eq_zero
    hlam0 hlamHalf hamp (fun _ ↦ feedbackA2AsymptoticEta lam)
    (feedbackA2AsymptoticHorizon amplitude) hε

/-- FGL2 and I4 use the same actual graph and the same amplitude.  The graph is Lipschitz
by its `FeedbackGraph` type; its normalized uniform envelope vanishes under the actual row laws. -/
theorem exists_feedbackFGL2_optimizer_energy_bound_and_I4
    {lam δ : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hδ : 0 < δ) :
    ∃ amplitude C : ℝ, 0 < amplitude ∧ 0 < C ∧
      (∀ᶠ n : ℕ in atTop,
        (finiteSampleLaw n : Measure (FiniteSample n)).real {sample |
          C * n < sample.feedbackFGL2OptimizerEnergy
            hlam0.le (hlam.trans (by norm_num)) amplitude} < δ) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (finiteSampleLaw n : Measure (FiniteSample n)).real {sample |
          ε ≤ graphSupAbs (normalizedCurveOfGraph
            (sample.feedbackFGL2Graph hlam0.le (hlam.trans (by norm_num)) amplitude) n)} = 0 := by
  obtain ⟨amplitude, C, hamp, hC, henergy⟩ :=
    exists_feedbackFGL2_optimizer_energy_bound hlam0 hlam hδ
  exact ⟨amplitude, C, hamp, hC, henergy, fun _ hε ↦
    eventually_feedbackFGL2Graph_supAbs_tail_eq_zero
      hlam0.le (hlam.trans (by norm_num)) hamp hε⟩

end OTSelector.FiniteSample
