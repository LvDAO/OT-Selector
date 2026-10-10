import OTSelector.Limit.FeedbackMartingaleProblemCurrentKernel
import OTSelector.Limit.FeedbackInvariantUniqueness

/-!
# Identifying a current law from its zero generator means

The indicator-generator equations are the actual singleton mass balance equations. A
probability measure on the integer currents has summable, normalized singleton masses, so
proved uniqueness of feedback balance identifies the entire current measure.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- Integrating a current indicator reads the real mass of that singleton. -/
theorem integral_feedbackCurrentIndicator_singleton (ρ : Measure ℤ) (k : ℤ) :
    (∫ j, feedbackCurrentIndicator k j ∂ρ) = ρ.real {k} := by
  have heq : feedbackCurrentIndicator k = ({k} : Set ℤ).indicator (fun _ ↦ (1 : ℝ)) := by
    funext j
    by_cases hj : j = k <;> simp [feedbackCurrentIndicator, hj]
  rw [heq, integral_indicator_const _ (measurableSet_singleton k), smul_eq_mul, mul_one]

private theorem rate_mul_indicator (f : ℤ → ℝ) (k j : ℤ) :
    f j * feedbackCurrentIndicator k j = f k * feedbackCurrentIndicator k j := by
  by_cases hj : j = k
  · subst j
    rfl
  · simp only [feedbackCurrentIndicator, ite_eq_right hj, mul_zero]

private theorem generator_eq_indicator_combination (lam : ℝ) (k j : ℤ) :
    feedbackCurrentIndicatorGenerator lam k j =
      birthRate lam (k - 1) * feedbackCurrentIndicator (k - 1) j +
        deathRate lam (k + 1) * feedbackCurrentIndicator (k + 1) j -
        totalJumpRate lam k * feedbackCurrentIndicator k j := by
  have hup : feedbackCurrentIndicator k (j + 1) = feedbackCurrentIndicator (k - 1) j := by
    simp only [feedbackCurrentIndicator, show j + 1 = k ↔ j = k - 1 by omega]
  have hdown : feedbackCurrentIndicator k (j - 1) = feedbackCurrentIndicator (k + 1) j := by
    simp only [feedbackCurrentIndicator, show j - 1 = k ↔ j = k + 1 by omega]
  rw [feedbackCurrentIndicatorGenerator, hup, hdown, mul_sub, mul_sub,
    rate_mul_indicator (birthRate lam) (k - 1), rate_mul_indicator (deathRate lam) (k + 1),
    rate_mul_indicator (birthRate lam) k, rate_mul_indicator (deathRate lam) k, totalJumpRate]
  ring

/-- The generator integral is exactly incoming singleton flux minus outgoing singleton flux. -/
theorem integral_feedbackCurrentIndicatorGenerator (lam : ℝ) (ρ : Measure ℤ)
    [IsFiniteMeasure ρ] (k : ℤ) :
    (∫ j, feedbackCurrentIndicatorGenerator lam k j ∂ρ) =
      ρ.real {k - 1} * birthRate lam (k - 1) +
        ρ.real {k + 1} * deathRate lam (k + 1) -
        ρ.real {k} * totalJumpRate lam k := by
  have hint (i : ℤ) : Integrable (feedbackCurrentIndicator i) ρ :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
      (Eventually.of_forall fun j ↦ norm_feedbackCurrentIndicator_le i j)
  have hu : Integrable (fun j ↦ birthRate lam (k - 1) * feedbackCurrentIndicator (k - 1) j) ρ :=
    (hint (k - 1)).const_mul _
  have hd : Integrable (fun j ↦ deathRate lam (k + 1) * feedbackCurrentIndicator (k + 1) j) ρ :=
    (hint (k + 1)).const_mul _
  have ho : Integrable (fun j ↦ totalJumpRate lam k * feedbackCurrentIndicator k j) ρ :=
    (hint k).const_mul _
  have hui : Integrable (fun j ↦
      birthRate lam (k - 1) * feedbackCurrentIndicator (k - 1) j +
        deathRate lam (k + 1) * feedbackCurrentIndicator (k + 1) j) ρ := hu.add hd
  simp_rw [generator_eq_indicator_combination]
  rw [integral_sub hui ho, integral_add hu hd]
  simp only [integral_const_mul, integral_feedbackCurrentIndicator_singleton]
  ring

/-- A probability current law with zero indicator-generator means is the explicit invariant law. -/
theorem eq_invariantCurrentMeasure_of_integral_generator_zero {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (ρ : Measure ℤ) [IsProbabilityMeasure ρ]
    (hgen : ∀ k : ℤ, ∫ j, feedbackCurrentIndicatorGenerator lam k j ∂ρ = 0) :
    ρ = invariantCurrentMeasure lam := by
  let p : ℤ → ℝ := fun k ↦ ρ.real {k}
  have hatoms : (∑' k : ℤ, ρ {k}) = 1 := by
    simpa only [indicator_univ, measure_univ] using
      (Measure.tsum_indicator_apply_singleton ρ univ MeasurableSet.univ)
  have hp : Summable p :=
    ENNReal.summable_toReal (by rw [hatoms]; exact ENNReal.one_ne_top)
  have hnorm : ∑' k, p k = 1 := by
    change (∑' k : ℤ, (ρ {k}).toReal) = 1
    rw [← ENNReal.tsum_toReal_eq (fun k ↦ measure_ne_top ρ {k}), hatoms, ENNReal.toReal_one]
  have hbal (k : ℤ) : p k * (birthRate lam k + deathRate lam k) =
      p (k - 1) * birthRate lam (k - 1) + p (k + 1) * deathRate lam (k + 1) := by
    have hk := hgen k
    rw [integral_feedbackCurrentIndicatorGenerator] at hk
    change p (k - 1) * birthRate lam (k - 1) + p (k + 1) * deathRate lam (k + 1) -
      p k * (birthRate lam k + deathRate lam k) = 0 at hk
    linarith
  have heq := feedback_invariantMass_unique hlam0 hlam hp hnorm hbal
  apply Measure.ext_of_singleton
  intro k
  rw [invariantCurrentMeasure, withDensity_apply _ (measurableSet_singleton k), lintegral_singleton]
  simp only [Measure.count_singleton, mul_one]
  rw [← heq]
  exact (ENNReal.ofReal_toReal (measure_ne_top ρ {k})).symm

end OTSelector.Limit
