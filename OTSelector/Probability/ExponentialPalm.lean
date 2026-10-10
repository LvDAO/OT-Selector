import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Exponential occupation and the age/residual law

Weight a rate-`r` exponential interval by Lebesgue occupation inside that interval. The change of
coordinates `(length, age) ↦ (age, length - age)` sends this measure to `r⁻¹` times the product of
two rate-`r` exponential laws. Multiplication by `r` therefore gives independent exponential age
and residual lifetime. Independence is a conclusion of the explicit density calculation.

This is the analytic identity used by Palm inversion. Identifying the actual stationary renewal
process with this occupation measure remains a separate P2/P3 step.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector

private theorem map_withDensity_comp_of_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {T : α → β} (hT : MeasurePreserving T μ ν)
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ T)).map T = ν.withDensity f := by
  refine Measure.ext_of_lintegral _ fun φ hφ ↦ ?_
  rw [lintegral_map hφ hT.measurable]
  change (∫⁻ a, (φ ∘ T) a ∂μ.withDensity (f ∘ T)) = ∫⁻ a, φ a ∂ν.withDensity f
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp hT.measurable) (hφ.comp hT.measurable),
    lintegral_withDensity_eq_lintegral_mul _ hf hφ]
  exact hT.lintegral_comp (hf.mul hφ)

private theorem measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) :=
  (measurable_exponentialPDFReal r).ennreal_ofReal

private theorem exponentialPDF_mul_of_nonneg {r s t : ℝ} (hr : 0 < r)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    exponentialPDF r s * exponentialPDF r t =
      ENNReal.ofReal r * exponentialPDF r (s + t) := by
  rw [exponentialPDF_of_nonneg hs, exponentialPDF_of_nonneg ht,
    exponentialPDF_of_nonneg (add_nonneg hs ht),
    ← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul hr.le]
  congr 1
  calc
    (r * Real.exp (-(r * s))) * (r * Real.exp (-(r * t))) =
        r * (r * (Real.exp (-(r * s)) * Real.exp (-(r * t)))) := by ring
    _ = r * (r * Real.exp (-(r * (s + t)))) := by
      rw [← Real.exp_add]
      congr 3
      ring

private theorem exponentialOccupation_density {r : ℝ} (hr : 0 < r) (p : ℝ × ℝ) :
    ({q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1}.indicator
      (fun q ↦ exponentialPDF r q.1)) p =
      (ENNReal.ofReal r)⁻¹ * (exponentialPDF r p.2 * exponentialPDF r (p.1 - p.2)) := by
  by_cases h : p ∈ {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1}
  · rw [Set.indicator_of_mem h,
      exponentialPDF_mul_of_nonneg hr h.1 (sub_nonneg.mpr h.2)]
    have hsum : p.2 + (p.1 - p.2) = p.1 := by ring
    rw [hsum, ENNReal.inv_mul_cancel_left (ne_of_gt (ENNReal.ofReal_pos.mpr hr))
      ENNReal.ofReal_ne_top]
  · rw [Set.indicator_of_notMem h]
    by_cases ht : 0 ≤ p.2
    · have hz : p.1 - p.2 < 0 := sub_neg.mpr (lt_of_not_ge (fun hz ↦ h ⟨ht, hz⟩))
      simp [exponentialPDF_of_neg hz]
    · simp [exponentialPDF_of_neg (lt_of_not_ge ht)]

/-- Lebesgue occupation of a rate-`r` exponential interval, before normalization by the rate. -/
noncomputable def exponentialOccupationMeasure (r : ℝ) : Measure (ℝ × ℝ) :=
  ((expMeasure r).prod volume).restrict {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1}

/-- The actual occupation measure transforms into the product exponential age/residual law,
with total mass `r⁻¹`. No independence or renewal inversion is assumed. -/
theorem exponentialOccupationMeasure_map_age_residual {r : ℝ} (hr : 0 < r) :
    (exponentialOccupationMeasure r).map (fun p ↦ (p.2, p.1 - p.2)) =
      (ENNReal.ofReal r)⁻¹ • (expMeasure r).prod (expMeasure r) := by
  have hS : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hpdf := measurable_exponentialPDF r
  have hprod : Measurable (fun p : ℝ × ℝ ↦ exponentialPDF r p.1 *
      exponentialPDF r p.2) := (hpdf.comp measurable_fst).mul (hpdf.comp measurable_snd)
  have hexp : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  unfold exponentialOccupationMeasure
  rw [hexp, prod_withDensity_left hpdf, restrict_withDensity hS, ← withDensity_indicator hS]
  have hdensity :
      {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1}.indicator (fun p ↦ exponentialPDF r p.1) =
        (fun p : ℝ × ℝ ↦ (ENNReal.ofReal r)⁻¹ *
          (exponentialPDF r p.1 * exponentialPDF r p.2)) ∘
          (fun p ↦ (p.2, p.1 - p.2)) := by
    funext p
    exact exponentialOccupation_density hr p
  have hw : Measurable (fun p : ℝ × ℝ ↦ (ENNReal.ofReal r)⁻¹ *
      (exponentialPDF r p.1 * exponentialPDF r p.2)) := measurable_const.mul hprod
  rw [hdensity, map_withDensity_comp_of_measurePreserving
    (measurePreserving_prod_sub_swap volume volume) hw,
    prod_withDensity hpdf hpdf]
  exact withDensity_smul _ hprod

/-- Normalized exponential interval occupation gives independent exponential age and residual
lifetime, both with the original rate. -/
theorem normalized_exponentialOccupationMeasure_map_age_residual {r : ℝ} (hr : 0 < r) :
    (ENNReal.ofReal r • exponentialOccupationMeasure r).map (fun p ↦ (p.2, p.1 - p.2)) =
      (expMeasure r).prod (expMeasure r) := by
  rw [Measure.map_smul, exponentialOccupationMeasure_map_age_residual hr, smul_smul,
    ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top,
    one_smul]

/-- Rate normalization turns exponential interval occupation into a probability measure. -/
theorem isProbabilityMeasure_normalized_exponentialOccupationMeasure {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (ENNReal.ofReal r • exponentialOccupationMeasure r) := by
  let := isProbabilityMeasure_expMeasure hr
  have : IsProbabilityMeasure
      ((ENNReal.ofReal r • exponentialOccupationMeasure r).map
        (fun p ↦ (p.2, p.1 - p.2))) := by
    rw [normalized_exponentialOccupationMeasure_map_age_residual hr]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map (fun p : ℝ × ℝ ↦ (p.2, p.1 - p.2))

/-- An independent auxiliary variable keeps its original law under the age/residual change of
coordinates, and remains independent of the two resulting exponential variables. -/
theorem normalized_exponentialOccupationMeasure_prod_map_age_residual
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν] {r : ℝ} (hr : 0 < r) :
    ((ENNReal.ofReal r • exponentialOccupationMeasure r).prod ν).map
        (fun p ↦ ((p.1.2, p.1.1 - p.1.2), p.2)) =
      ((expMeasure r).prod (expMeasure r)).prod ν := by
  let := isProbabilityMeasure_normalized_exponentialOccupationMeasure hr
  change ((ENNReal.ofReal r • exponentialOccupationMeasure r).prod ν).map
    (Prod.map (fun p ↦ (p.2, p.1 - p.2)) id) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    normalized_exponentialOccupationMeasure_map_age_residual hr, Measure.map_id]

end OTSelector
