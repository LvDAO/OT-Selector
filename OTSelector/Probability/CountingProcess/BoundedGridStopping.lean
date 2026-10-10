import OTSelector.Probability.CountingProcess.Closure

/-!
# Optional sampling for bounded predictable transforms on finite stopping grids

This file extends the finite-grid optional-sampling wrappers of `GridStopping` from bounded
finite-range predictable transforms to bounded predictable transforms.  The closure theorem needs
the accumulated intensity to be integrable at every deterministic endpoint, so that hypothesis is
kept explicit in both wrappers below.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Optional sampling of a compensated bounded-predictable transform at one finite-valued
stopping time. -/
theorem HasPredictableIntensity.stoppedValue_compensatedIntegral_boundedPredictable_finiteRange
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedPredictable ℱ H)
    (hAint : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτ_range : (Set.range τ).Finite) :
    stoppedValue (compensatedIntegral N Λ H) τ =ᵐ[μ]
      μ[compensatedIntegral N Λ H T | hτ.measurableSpace] :=
  (hΛ.martingale_of_boundedPredictable hH hAint)
    |>.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      hτ hτ_le hτ_range.countable

/-- Optional sampling between two finite-valued stopping times for a compensated
bounded-predictable transform. -/
theorem HasPredictableIntensity.stoppedValue_compensatedIntegral_boundedPredictable_finiteRange_pair
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedPredictable ℱ H)
    (hAint : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    stoppedValue (compensatedIntegral N Λ H) σ =ᵐ[μ]
      μ[stoppedValue (compensatedIntegral N Λ H) τ | hσ.measurableSpace] :=
  (hΛ.martingale_of_boundedPredictable hH hAint)
    |>.stoppedValue_ae_eq_condExp_of_le_of_countable_range
      hτ hσ hστ hτ_le hτ_range.countable hσ_range.countable

end OTSelector.CountingProcess
