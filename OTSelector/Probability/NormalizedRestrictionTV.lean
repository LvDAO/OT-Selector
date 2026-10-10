import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Normalized restriction integrals

This file provides the small analytic layer needed when a finite product law is restricted to a
moving positive-mass rectangle.  The normalization is written as an ordinary set integral divided
by the set mass.  This avoids introducing a kernel or a regular-conditional-distribution
interface.

The two public results say that these normalized integrals are measurable in a measurable
parameter and continuous when the moving-set indicators converge almost everywhere.  The latter
is the total-variation input used by the finite-history right-boundary argument.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace OTSelector

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The integral of `f` under `μ` restricted to `s` and normalized by its real mass.  A null set
uses the harmless value zero. -/
noncomputable def normalizedRestrictionIntegral
    (μ : Measure β) (s : Set β) (f : β → ℝ) : ℝ :=
  (μ.real s)⁻¹ * ∫ x in s, f x ∂μ

/- The normalized set integral is the ordinary integral under the conditioned measure. -/
theorem integral_cond_eq_normalizedRestrictionIntegral
    (μ : Measure β) (s : Set β) (f : β → ℝ) :
    ∫ x, f x ∂(ProbabilityTheory.cond μ s) =
      normalizedRestrictionIntegral μ s f := by
  rw [ProbabilityTheory.cond, integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  rfl

/-- A normalized restriction average inherits a uniform bound from its integrand, including the
zero-mass fallback branch. -/
theorem norm_normalizedRestrictionIntegral_le_of_norm_le_const
    (μ : Measure β) [IsFiniteMeasure μ] (s : Set β) (f : β → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ s, ‖f x‖ ≤ C) :
    ‖normalizedRestrictionIntegral μ s f‖ ≤ C := by
  by_cases hmass : μ.real s = 0
  · simp [normalizedRestrictionIntegral, hmass, hC]
  · have hmassPos : 0 < μ.real s := lt_of_le_of_ne measureReal_nonneg (Ne.symm hmass)
    have hint : ‖∫ x in s, f x ∂μ‖ ≤ C * μ.real s :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top μ s) hbound
    rw [normalizedRestrictionIntegral, norm_mul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hmassPos]
    calc
      (μ.real s)⁻¹ * ‖∫ x in s, f x ∂μ‖ ≤
          (μ.real s)⁻¹ * (C * μ.real s) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hmassPos.le)
      _ = C := by field_simp

/-- A jointly measurable moving set and integrand give a measurable normalized restriction
integral. -/
theorem stronglyMeasurable_normalizedRestrictionIntegral
    (μ : Measure β) [IsFiniteMeasure μ]
    (C : Set (α × β)) (hC : MeasurableSet C)
    (f : α → β → ℝ)
    (hf : StronglyMeasurable fun p : α × β ↦ f p.1 p.2) :
    StronglyMeasurable fun a ↦
      normalizedRestrictionIntegral μ {b | (a, b) ∈ C} (f a) := by
  have hmass : StronglyMeasurable fun a ↦ μ.real {b | (a, b) ∈ C} :=
    (measurable_measure_prodMk_left hC).ennreal_toReal.stronglyMeasurable
  have hint : StronglyMeasurable fun a ↦ ∫ b in {b | (a, b) ∈ C}, f a b ∂μ := by
    convert (hf.indicator hC).integral_prod_right' (ν := μ) using 1
    ext a
    simp_rw [← Set.indicator_comp_right]
    exact (integral_indicator ((measurable_prodMk_left (x := a)) hC)).symm
  exact hmass.measurable.inv.stronglyMeasurable.mul hint

/-- Normalized restrictions are continuous under almost-everywhere convergence of their set
indicators.  The integrand is allowed to vary as well, under a common integrable bound. -/
theorem tendsto_normalizedRestrictionIntegral_of_ae
    (μ : Measure β) [IsFiniteMeasure μ]
    (s : ℕ → Set β) (s0 : Set β)
    (hs : ∀ k, MeasurableSet (s k)) (hs0 : MeasurableSet s0)
    (f : ℕ → β → ℝ) (f0 : β → ℝ)
    (hf : ∀ k, AEStronglyMeasurable (f k) μ)
    (hf0 : AEStronglyMeasurable f0 μ)
    (bound : β → ℝ)
    (hbound : ∀ k, ∀ᵐ x ∂μ, ‖f k x‖ ≤ bound x)
    (hboundInt : Integrable bound μ)
    (hmem : ∀ᵐ x ∂μ, ∀ᶠ k in atTop, (x ∈ s k ↔ x ∈ s0))
    (hfun : ∀ᵐ x ∂μ, Tendsto (fun k ↦ f k x) atTop (𝓝 (f0 x)))
    (hpos : μ.real s0 ≠ 0) :
    Tendsto (fun k ↦ normalizedRestrictionIntegral μ (s k) (f k)) atTop
      (𝓝 (normalizedRestrictionIntegral μ s0 f0)) := by
  let F : ℕ → β → ℝ := fun k ↦ (s k).indicator (f k)
  let F0 : β → ℝ := s0.indicator f0
  have hFmeas : ∀ k, AEStronglyMeasurable (F k) μ := fun k ↦
    (hf k).indicator (hs k)
  have hF0meas : AEStronglyMeasurable F0 μ := hf0.indicator hs0
  have hFbound : ∀ k, ∀ᵐ x ∂μ, ‖F k x‖ ≤ bound x := by
    intro k
    filter_upwards [hbound k] with x hx
    by_cases hxs : x ∈ s k
    · simpa [F, hxs] using hx
    · simpa [F, hxs] using (norm_nonneg (f k x)).trans hx
  have hFtendsto : ∀ᵐ x ∂μ, Tendsto (fun k ↦ F k x) atTop (𝓝 (F0 x)) := by
    filter_upwards [hmem, hfun] with x hxmem hxfun
    rcases (eventually_atTop.1 hxmem) with ⟨K, hK⟩
    by_cases hxs0 : x ∈ s0
    · have heq : ∀ᶠ k in atTop, F k x = f k x := by
        filter_upwards [eventually_ge_atTop K] with k hk
        have hxsk : x ∈ s k := (hK k hk).2 hxs0
        simp [F, hxsk]
      have hF0 : F0 x = f0 x := by simp [F0, hxs0]
      rw [hF0]
      exact Tendsto.congr' (Filter.EventuallyEq.symm heq) hxfun
    · have heq : ∀ k ≥ K, F k x = 0 := by
        intro k hk
        have hxsk : x ∉ s k := fun h ↦ hxs0 ((hK k hk).1 h)
        simp [F, hxsk]
      have hF0 : F0 x = 0 := by simp [F0, hxs0]
      rw [hF0]
      exact tendsto_atTop_of_eventually_const heq
  have hInt : Tendsto (fun k ↦ ∫ x, F k x ∂μ) atTop (𝓝 (∫ x, F0 x ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence bound
      (Filter.Eventually.of_forall hFmeas) (Filter.Eventually.of_forall hFbound)
      hboundInt hFtendsto
  have hMass : Tendsto (fun k ↦ μ.real (s k)) atTop (𝓝 (μ.real s0)) :=
    (ENNReal.tendsto_toReal (measure_ne_top μ s0)).comp
      (tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop hs0 hs hmem)
  have hInv : Tendsto (fun k ↦ (μ.real (s k))⁻¹) atTop (𝓝 (μ.real s0)⁻¹) :=
    hMass.inv₀ hpos
  have hSetInt : Tendsto (fun k ↦ ∫ x in s k, f k x ∂μ) atTop
      (𝓝 (∫ x in s0, f0 x ∂μ)) := by
    have hseq : (fun k ↦ ∫ x, F k x ∂μ) = fun k ↦ ∫ x in s k, f k x ∂μ := by
      funext k
      exact integral_indicator (hs k)
    have hlim : (∫ x, F0 x ∂μ) = ∫ x in s0, f0 x ∂μ :=
      integral_indicator hs0
    simpa [hseq, hlim] using hInt
  simpa only [normalizedRestrictionIntegral] using hInv.mul hSetInt

end OTSelector
