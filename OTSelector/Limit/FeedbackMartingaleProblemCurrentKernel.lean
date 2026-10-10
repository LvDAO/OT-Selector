import OTSelector.Limit.FeedbackMartingaleProblemCurrentApproximation

/-!
# Exact one-jump expectations for current indicators

The marked holding kernel factors into its exponential waiting law and its marked jump law.
Forgetting the mark gives the actual two-neighbor current kernel, so a current indicator has
an explicit truncated first-jump expectation and a uniformly bounded generator.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- The birth-death generator applied to the indicator of current `k`, at current `j`. -/
noncomputable def feedbackCurrentIndicatorGenerator (lam : ℝ) (k j : ℤ) : ℝ :=
  birthRate lam j * (feedbackCurrentIndicator k (j + 1) - feedbackCurrentIndicator k j) +
    deathRate lam j * (feedbackCurrentIndicator k (j - 1) - feedbackCurrentIndicator k j)

/-- Changing the current changes its indicator by at most one. -/
theorem norm_feedbackCurrentIndicator_sub_le_one (k i j : ℤ) :
    ‖feedbackCurrentIndicator k i - feedbackCurrentIndicator k j‖ ≤ 1 := by
  unfold feedbackCurrentIndicator
  split_ifs <;> norm_num

/-- The indicator generator is bounded by the total jump rate. -/
theorem norm_feedbackCurrentIndicatorGenerator_le_rate {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k j : ℤ) :
    ‖feedbackCurrentIndicatorGenerator lam k j‖ ≤ totalJumpRate lam j := by
  unfold feedbackCurrentIndicatorGenerator totalJumpRate
  calc
    _ ≤ ‖birthRate lam j * (feedbackCurrentIndicator k (j + 1) - feedbackCurrentIndicator k j)‖ +
        ‖deathRate lam j * (feedbackCurrentIndicator k (j - 1) - feedbackCurrentIndicator k j)‖ :=
      norm_add_le _ _
    _ = birthRate lam j * ‖feedbackCurrentIndicator k (j + 1) - feedbackCurrentIndicator k j‖ +
        deathRate lam j * ‖feedbackCurrentIndicator k (j - 1) - feedbackCurrentIndicator k j‖ := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (birthRate_nonneg hlam0 hlam j),
        Real.norm_of_nonneg (deathRate_nonneg hlam0 hlam j)]
    _ ≤ birthRate lam j * 1 + deathRate lam j * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_feedbackCurrentIndicator_sub_le_one _ _ _)
        (birthRate_nonneg hlam0 hlam j))
        (mul_le_mul_of_nonneg_left (norm_feedbackCurrentIndicator_sub_le_one _ _ _)
          (deathRate_nonneg hlam0 hlam j))
    _ = _ := by ring

/-- A uniform bound suitable for integration over an arbitrary initial-current law. -/
theorem norm_feedbackCurrentIndicatorGenerator_le {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k j : ℤ) :
    ‖feedbackCurrentIndicatorGenerator lam k j‖ ≤ 3 := by
  have hr := (totalJumpRate_bounds hlam0 j).2
  have hg := norm_feedbackCurrentIndicatorGenerator_le_rate hlam0 hlam k j
  linarith

private theorem integrable_indicator_difference (μ : Measure ℤ) [IsFiniteMeasure μ]
    (k j : ℤ) :
    Integrable (fun i ↦ feedbackCurrentIndicator k i - feedbackCurrentIndicator k j) μ :=
  Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    (Eventually.of_forall fun i ↦ norm_feedbackCurrentIndicator_sub_le_one k i j)

/-- The exact expected indicator increment under the unmarked neighboring-current kernel. -/
theorem integral_feedbackJumpKernel_currentIndicator {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k j : ℤ) :
    (∫ i, feedbackCurrentIndicator k i - feedbackCurrentIndicator k j ∂feedbackJumpKernel lam j) =
      feedbackCurrentIndicatorGenerator lam k j / totalJumpRate lam j := by
  change (∫ i, feedbackCurrentIndicator k i - feedbackCurrentIndicator k j ∂
    (ENNReal.ofReal (jumpUpProbability lam j) • Measure.dirac (j + 1) +
      ENNReal.ofReal (jumpDownProbability lam j) • Measure.dirac (j - 1))) = _
  rw [integral_add_measure
    ((integrable_indicator_difference (Measure.dirac (j + 1)) k j).smul_measure
      ENNReal.ofReal_ne_top)
    ((integrable_indicator_difference (Measure.dirac (j - 1)) k j).smul_measure
      ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (jumpUpProbability_nonneg hlam0 hlam j),
    ENNReal.toReal_ofReal (jumpDownProbability_nonneg hlam0 hlam j)]
  simp only [smul_eq_mul, jumpUpProbability, jumpDownProbability,
    feedbackCurrentIndicatorGenerator]
  ring

/-- Forgetting the physical mark preserves the same exact expected current increment. -/
theorem integral_feedbackMarkedJumpKernel_currentIndicator {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k j : ℤ) :
    (∫ z, feedbackCurrentIndicator k z.2 - feedbackCurrentIndicator k j
      ∂feedbackMarkedJumpKernel lam j) =
      feedbackCurrentIndicatorGenerator lam k j / totalJumpRate lam j := by
  have hm : Measurable (fun i : ℤ ↦ feedbackCurrentIndicator k i - feedbackCurrentIndicator k j) :=
    measurable_of_countable _
  calc
    _ = ∫ i, feedbackCurrentIndicator k i - feedbackCurrentIndicator k j
        ∂(feedbackMarkedJumpKernel lam j).map Prod.snd :=
      (integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable).symm
    _ = _ := by
      rw [feedbackMarkedJumpKernel_map_current hlam0 hlam,
        integral_feedbackJumpKernel_currentIndicator hlam0 hlam]

/-- The exponential probability that the first physical wait has ended by `t`. -/
theorem integral_feedbackHoldingKernel_indicator_le {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (j : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s, if s ≤ t then (1 : ℝ) else 0 ∂feedbackHoldingKernel lam j) =
      1 - Real.exp (-totalJumpRate lam j * t) := by
  let := isProbabilityMeasure_expMeasure (totalJumpRate_pos hlam0 hlam j)
  change (∫ s, (Iic t).indicator (fun _ ↦ (1 : ℝ)) s
    ∂expMeasure (totalJumpRate lam j)) = _
  rw [integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one,
    ← cdf_eq_real, cdf_expMeasure_eq (totalJumpRate_pos hlam0 hlam j), ite_eq_left ht, neg_mul]

/-- Exact first-jump indicator expectation under the actual full marked holding kernel. -/
theorem integral_feedbackMarkedHoldingKernel_currentIndicator {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k j : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ z, if z.1 ≤ t then feedbackCurrentIndicator k z.2.2 - feedbackCurrentIndicator k j else 0
      ∂feedbackMarkedHoldingKernel lam j) =
      ((1 - Real.exp (-totalJumpRate lam j * t)) / totalJumpRate lam j) *
        feedbackCurrentIndicatorGenerator lam k j := by
  let := feedbackHoldingKernel_isMarkov hlam0 hlam
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  have hfun : (fun z : FeedbackMarkedStep ↦ if z.1 ≤ t then
      feedbackCurrentIndicator k z.2.2 - feedbackCurrentIndicator k j else 0) =
      (fun z : FeedbackMarkedStep ↦ (if z.1 ≤ t then (1 : ℝ) else 0) *
        (feedbackCurrentIndicator k z.2.2 - feedbackCurrentIndicator k j)) := by
    funext z
    split_ifs <;> simp
  rw [hfun]
  change (∫ z : FeedbackMarkedStep, (if z.1 ≤ t then (1 : ℝ) else 0) *
    (feedbackCurrentIndicator k z.2.2 - feedbackCurrentIndicator k j)
    ∂(feedbackHoldingKernel lam j).prod (feedbackMarkedJumpKernel lam j)) = _
  rw [integral_prod_mul (fun s : ℝ ↦ if s ≤ t then (1 : ℝ) else 0)
    (fun z : UnitMark × ℤ ↦ feedbackCurrentIndicator k z.2 - feedbackCurrentIndicator k j),
    integral_feedbackHoldingKernel_indicator_le hlam0 hlam j t ht,
    integral_feedbackMarkedJumpKernel_currentIndicator hlam0 hlam k j]
  ring

end OTSelector.Limit
