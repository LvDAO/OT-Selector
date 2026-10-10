import OTSelector.Probability.CountingProcess.FiniteEventIntensity
import OTSelector.Probability.CountingProcess.FiniteEventIntensitySideConditions
import OTSelector.Probability.CountingProcess.FiniteEventRectangleMeasureBridge
import OTSelector.Probability.CountingProcess.FiniteEventUsualRectangle

/-!
# Finite-event intensities from raw rectangle identities

This file composes the raw-to-usual rectangle lift, the conversion from real rectangle
integrals to predictable measures, and the finite-event measure-extension theorem.  The input is
an actual count-increment identity on the raw filtration; no martingale or intensity conclusion
is assumed.
-/

open Set
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A raw-filtration count-increment identity for a finite family of event times determines its
predictable intensity in the usual augmentation. -/
theorem hasPredictableIntensity_of_finiteEvent_raw_countIncrement
    {m : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F₀ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop ℝ≥0)
    (hξ : ∀ i, IsStoppingTime (usualAugmentation F₀ μ) (ξ i))
    (hpos : ∀ i ω, ξ i ω = ⊤ ∨ (0 : WithTop ℝ≥0) < ξ i ω)
    (hdist : ∀ ω i j, ξ i ω ≠ ⊤ → ξ j ω ≠ ⊤ → ξ i ω = ξ j ω → i = j)
    (Λ : ℝ≥0 → Ω → ℝ)
    (hΛpred : IsStronglyPredictable (usualAugmentation F₀ μ) Λ)
    {C : ℝ} (hC : 0 ≤ C)
    (hΛnonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛupper : ∀ u ω, Λ u ω ≤ C)
    (hΛint : ∀ t ω,
      IntegrableOn (fun u ↦ Λ u ω) (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hΛprod : Integrable (Function.uncurry Λ) (timeMeasure.prod μ))
    (hRaw : ∀ {s t : ℝ≥0}, s ≤ t → ∀ E : Set Ω, MeasurableSet[F₀ s] E →
      (∫ ω in E,
        ((finiteEventCountTop ξ t ω : ℝ) - finiteEventCountTop ξ s ω) ∂μ) =
        ∫ ω in E, ∫ u in Ioc s t, Λ u ω ∂timeMeasure ∂μ) :
    HasPredictableIntensity μ (usualAugmentation F₀ μ)
      (fun t ω ↦ finiteEventCountTop ξ t ω) Λ := by
  let F := usualAugmentation F₀ μ
  have hUsual : ∀ {s t : ℝ≥0}, s ≤ t → ∀ E : Set Ω,
      MeasurableSet[F s] E →
        (∫ ω in E,
          ((finiteEventCountTop ξ t ω : ℝ) - finiteEventCountTop ξ s ω) ∂μ) =
          ∫ ω in E, ∫ u in Ioc s t, Λ u ω ∂timeMeasure ∂μ := by
    intro s t hst E hE
    exact finiteEventCountTop_increment_setIntegral_eq_of_usualAugmentation
      μ F₀ ξ hξ Λ hΛpred hC hΛnonneg hΛupper hΛint hRaw hst E
        (by simpa only [F] using hE)
  have hRect : ∀ {T : ℝ≥0}, 0 < T → ∀ s : ℝ≥0, s < T → ∀ E : Set Ω,
      MeasurableSet[F s] E →
        finiteEventJumpMeasure μ F ξ hξ T (Ioc s T ×ˢ E) =
          finiteHorizonIntensityMeasure μ F Λ T (Ioc s T ×ˢ E) := by
    intro T hT s hsT E hE
    exact finiteEvent_rectangle_measures_eq_of_countIncrement
      μ F ξ hξ hdist Λ hΛpred hΛnonneg hΛprod hsT.le hE
        (hUsual hsT.le E hE)
  apply hasPredictableIntensity_of_finiteEvent_rectangle_measures
    μ F ξ hξ hpos hdist Λ hΛpred hΛnonneg hΛint hRect
  · intro H hH T
    rcases hH.2.2 with ⟨D, hD, hHbound⟩
    exact finiteEvent_product_integrable_of_global_rate_integrable
      μ F hΛprod hD hH hHbound hΛnonneg
  · intro H hH t ω
    rcases hH.2.2 with ⟨D, hD, hHbound⟩
    exact finiteEvent_pathProduct_integrable_of_bounded
      F hΛpred hΛnonneg hΛint hD hH hHbound t ω
  · intro H hH
    exact (finiteEvent_countingIntegral_sideConditions μ F ξ hξ hdist hH).1
  · intro H hH t
    exact (finiteEvent_countingIntegral_sideConditions μ F ξ hξ hdist hH).2 t
  · intro H hH
    rcases hH.2.2 with ⟨D, hD, hHbound⟩
    have hPath := finiteEvent_pathProduct_integrable_of_bounded
      F hΛpred hΛnonneg hΛint hD hH hHbound
    have hProd := finiteEvent_product_integrable_of_global_rate_integrable
      μ F hΛprod hD hH hHbound hΛnonneg
    exact (finiteEvent_integratedIntensity_sideConditions
      μ F hΛpred hH hPath hProd).1
  · intro H hH t
    rcases hH.2.2 with ⟨D, hD, hHbound⟩
    have hPath := finiteEvent_pathProduct_integrable_of_bounded
      F hΛpred hΛnonneg hΛint hD hH hHbound
    have hProd := finiteEvent_product_integrable_of_global_rate_integrable
      μ F hΛprod hD hH hHbound hΛnonneg
    exact (finiteEvent_integratedIntensity_sideConditions
      μ F hΛpred hH hPath hProd).2 t

end OTSelector.CountingProcess
