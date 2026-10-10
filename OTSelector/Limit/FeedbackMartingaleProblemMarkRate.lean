import OTSelector.Limit.FeedbackRegenerationMarks
import OTSelector.Feedback.FeedbackMarkedMean
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Agreement of spatial mark compensators with the actual jump kernel

The conditional geometric-mark means used by the finite spatial martingales reproduce the
source and target mark-rate measures of the actual infinite feedback process. Summing the two
colors gives the total rate times its marked jump-kernel expectation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BoundedContinuousFunction

namespace OTSelector.Limit

/-- The finite spatial source mark mean uses exactly the actual source mark-rate measure. -/
theorem integral_sourceMarkRateMeasure_eq_markMean {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (ψ : UnitMark → ℝ) :
    (∫ u, ψ u ∂sourceMarkRateMeasure lam k) =
      birthRate lam k * sourceFeedbackMarkMean (lam * currentSign k) ψ := by
  rw [sourceMarkRateMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp_rw [ENNReal.toReal_ofReal (sourceMarkDensity_nonneg hlam0 hlam k _), smul_eq_mul]
    have hd : (1 - lam * currentSign k / 2) ≠ 0 := by
      rcases k with (n | n)
      · rcases n with (_ | n)
        · norm_num [currentSign]
        · simp only [currentSign]
          linarith
      · simp only [currentSign]
        linarith
    unfold sourceFeedbackMarkMean
    rw [show birthRate lam k = 1 - lam * currentSign k / 2 by unfold birthRate; ring]
    change (∫ u : UnitMark, sourceMarkDensity lam k u * ψ u ∂volume) =
      (1 - lam * currentSign k / 2) *
        ((∫ u : UnitMark, ψ u * sourceMarkedFactor (lam * currentSign k) u ∂volume) /
          (1 - lam * currentSign k / 2))
    rw [mul_div_cancel₀ _ hd]
    apply integral_congr_ae
    filter_upwards with u
    simp only [sourceMarkDensity, sourceMarkedFactor]
    ring
  · exact ENNReal.measurable_ofReal.comp (by unfold sourceMarkDensity; fun_prop)
  · exact Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top

/-- The finite spatial target mark mean uses exactly the actual target mark-rate measure. -/
theorem integral_targetMarkRateMeasure_eq_markMean {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (ψ : UnitMark → ℝ) :
    (∫ u, ψ u ∂targetMarkRateMeasure lam k) =
      deathRate lam k * targetFeedbackMarkMean (lam * currentSign k) ψ := by
  rw [targetMarkRateMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp_rw [ENNReal.toReal_ofReal (targetMarkDensity_nonneg hlam0 hlam k _), smul_eq_mul]
    have hd : (1 + 3 * (lam * currentSign k) / 2) ≠ 0 := by
      rcases k with (n | n)
      · rcases n with (_ | n)
        · norm_num [currentSign]
        · simp only [currentSign]
          linarith
      · simp only [currentSign]
        linarith
    unfold targetFeedbackMarkMean
    rw [show deathRate lam k = 1 + 3 * (lam * currentSign k) / 2 by unfold deathRate; ring]
    change (∫ u : UnitMark, targetMarkDensity lam k u * ψ u ∂volume) =
      (1 + 3 * (lam * currentSign k) / 2) *
        ((∫ u : UnitMark, ψ u * targetMarkedFactor (lam * currentSign k) u ∂volume) /
          (1 + 3 * (lam * currentSign k) / 2))
    rw [mul_div_cancel₀ _ hd]
    apply integral_congr_ae
    filter_upwards with u
    simp only [targetMarkDensity, targetMarkedFactor]
    ring
  · exact ENNReal.measurable_ofReal.comp (by unfold targetMarkDensity; fun_prop)
  · exact Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top

/-- A test of the marked next current splits into the exact two spatial mark compensator rates. -/
theorem totalJumpRate_mul_integral_feedbackMarkedJumpKernel {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) (ψ : (UnitMark × ℤ) →ᵇ ℝ) :
    totalJumpRate lam k * (∫ z, ψ z ∂feedbackMarkedJumpKernel lam k) =
      birthRate lam k * sourceFeedbackMarkMean (lam * currentSign k) (fun u ↦ ψ (u, k + 1)) +
        deathRate lam k * targetFeedbackMarkMean (lam * currentSign k) (fun u ↦ ψ (u, k - 1)) := by
  have : IsFiniteMeasure (sourceMarkRateMeasure lam k) :=
    ⟨by rw [sourceMarkRateMeasure_univ hlam0 hlam]; exact ENNReal.ofReal_lt_top⟩
  have : IsFiniteMeasure (targetMarkRateMeasure lam k) :=
    ⟨by rw [targetMarkRateMeasure_univ hlam0 hlam]; exact ENNReal.ofReal_lt_top⟩
  have hint (μ : Measure (UnitMark × ℤ)) [IsFiniteMeasure μ] : Integrable ψ μ :=
    Integrable.of_bound ψ.continuous.measurable.aestronglyMeasurable ‖ψ‖
      (Filter.Eventually.of_forall fun z ↦ ψ.norm_coe_le_norm z)
  change totalJumpRate lam k * (∫ z, ψ z ∂
    (ENNReal.ofReal (totalJumpRate lam k))⁻¹ •
      ((sourceMarkRateMeasure lam k).map (fun u ↦ (u, k + 1)) +
        (targetMarkRateMeasure lam k).map (fun u ↦ (u, k - 1)))) = _
  rw [integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (totalJumpRate_pos hlam0 hlam k).le, smul_eq_mul,
    integral_add_measure (hint _) (hint _),
    integral_map measurable_prodMk_right.aemeasurable ψ.continuous.measurable.aestronglyMeasurable,
    integral_map measurable_prodMk_right.aemeasurable ψ.continuous.measurable.aestronglyMeasurable,
    ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (totalJumpRate_pos hlam0 hlam k)), one_mul,
    integral_sourceMarkRateMeasure_eq_markMean hlam0 hlam,
    integral_targetMarkRateMeasure_eq_markMean hlam0 hlam]

end OTSelector.Limit
