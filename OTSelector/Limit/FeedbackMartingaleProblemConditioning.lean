import OTSelector.Limit.FeedbackMartingaleProblemStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.ConditionalProbability

/-!
# Initial-event conditioning and bounded stopping for the spatial martingale problem

An event already known at the starting cut may be imposed before optional stopping. The
restriction step is a direct application of mathlib's conditional-expectation restriction
theorem; the continuous-time stopping step reuses the finite-right-grid proof.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace OTSelector.Limit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}

/-- Conditioning on an initial event preserves the original martingale under the restricted
measure. This does not require that the initial sigma-algebra be trivial. -/
theorem martingale_restrict_initial (hM : Martingale M ℱ μ) {A : Set Ω}
    (hA : MeasurableSet[ℱ 0] A) : Martingale M ℱ (μ.restrict A) := by
  refine ⟨hM.stronglyAdapted, fun s t hst ↦ ?_⟩
  exact (condExp_restrict_ae_eq_restrict (ℱ.le s) (ℱ.mono (show (0 : ℝ≥0) ≤ s from zero_le) A hA)
    (hM.integrable t)).trans (ae_restrict_of_ae (hM.condExp_ae_eq hst))

/-- Optional stopping tested by every event known at the starting cut. -/
theorem setIntegral_martingale_stopping_initial
    (hM : Martingale M ℱ μ) {A : Set Ω} (hA : MeasurableSet[ℱ 0] A)
    {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℝ≥0))
    (hτT : ∀ ω, τ ω ≤ T)
    (hRight : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    {D : Ω → ℝ} (hD : Integrable D μ)
    (hBound : ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M s ω‖ ≤ D ω) :
    ∫ ω in A, M (τ ω) ω ∂μ = ∫ ω in A, M 0 ω ∂μ :=
  integral_martingale_stopping_of_integrable_bound (martingale_restrict_initial hM hA)
    hτ hτT (ae_restrict_of_ae hRight) hD.integrableOn (ae_restrict_of_ae hBound)

/-- Normalizing an initial-event restriction gives the same stopped expectation identity.
Nonzero event probability is only needed when using the resulting measure as a probability law. -/
theorem integral_cond_martingale_stopping_initial
    (hM : Martingale M ℱ μ) {A : Set Ω} (hA : MeasurableSet[ℱ 0] A)
    {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℝ≥0))
    (hτT : ∀ ω, τ ω ≤ T)
    (hRight : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    {D : Ω → ℝ} (hD : Integrable D μ)
    (hBound : ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M s ω‖ ≤ D ω) :
    ∫ ω, M (τ ω) ω ∂μ[|A] = ∫ ω, M 0 ω ∂μ[|A] := by
  simp only [ProbabilityTheory.cond, integral_smul_measure]
  rw [setIntegral_martingale_stopping_initial hM hA hτ hτT hRight hD hBound]

end OTSelector.Limit
