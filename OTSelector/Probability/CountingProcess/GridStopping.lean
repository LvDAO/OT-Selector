import OTSelector.Probability.CountingProcess.Exponential

/-!
# Optional sampling on finite stopping grids

Mathlib's continuous-time optional-sampling theorem applies to bounded stopping times whose
ranges are countable.  This file specializes that theorem to the actual martingales supplied by
`HasPredictableIntensity`.  Finite stopping grids are sufficient here and make the countability
premise explicit.

These results do not assert that `countingExponential` is a martingale.  Applying them to a
product-weighted exponential driver still requires a separately proved bounded-simple
predictable left weight.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Optional sampling of a compensated bounded-simple transform at one finite-valued stopping
time. -/
theorem HasPredictableIntensity.stoppedValue_compensatedIntegral_finiteRange
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedSimplePredictable ℱ H)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτ_range : (Set.range τ).Finite) :
    stoppedValue (compensatedIntegral N Λ H) τ =ᵐ[μ]
      μ[compensatedIntegral N Λ H T | hτ.measurableSpace] :=
  (hΛ.martingale hH).stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτ_le hτ_range.countable

/-- Optional sampling between two finite-valued stopping times for a compensated bounded-simple
transform. -/
theorem HasPredictableIntensity.stoppedValue_compensatedIntegral_finiteRange_pair
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedSimplePredictable ℱ H)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    stoppedValue (compensatedIntegral N Λ H) σ =ᵐ[μ]
      μ[stoppedValue (compensatedIntegral N Λ H) τ | hσ.measurableSpace] :=
  (hΛ.martingale hH).stoppedValue_ae_eq_condExp_of_le_of_countable_range
    hτ hσ hστ hτ_le hτ_range.countable hσ_range.countable

/-- Finite-grid optional sampling for the unweighted exponential driver. -/
theorem HasPredictableIntensity.stoppedValue_exponentialDriver_finiteRange
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ θ : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hθ : IsBoundedSimplePredictable ℱ θ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτ_range : (Set.range τ).Finite) :
    stoppedValue (exponentialDriver N Λ θ) τ =ᵐ[μ]
      μ[exponentialDriver N Λ θ T | hτ.measurableSpace] :=
  (hΛ.exponentialDriver_martingale hθ).stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτ_le hτ_range.countable

/-- Finite-grid optional sampling for a product-weighted exponential driver.  The left weight is
required to be genuinely bounded, finite-valued, and predictable. -/
theorem HasPredictableIntensity.stoppedValue_weightedExponentialDriver_finiteRange
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ L θ : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hL : IsBoundedSimplePredictable ℱ L)
    (hθ : IsBoundedSimplePredictable ℱ θ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτ_range : (Set.range τ).Finite) :
    stoppedValue (weightedExponentialDriver N Λ L θ) τ =ᵐ[μ]
      μ[weightedExponentialDriver N Λ L θ T | hτ.measurableSpace] :=
  (hΛ.weightedExponentialDriver_martingale hL hθ)
    |>.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      hτ hτ_le hτ_range.countable

end OTSelector.CountingProcess
