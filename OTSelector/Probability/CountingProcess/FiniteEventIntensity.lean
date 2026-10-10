import OTSelector.Probability.CountingProcess.FiniteEventCompensator
import OTSelector.Probability.CountingProcess.FiniteHorizonMeasureExtension
import OTSelector.Probability.CountingProcess.RectangleExtension

/-!
# From finite-event rectangle measures to predictable intensity

This file contains the final measure-to-martingale bridge for a finite family of event
times.  The input is deliberately a low-level equality of the jump and candidate
intensity measures on predictable rectangles.  The only process facts supplied by a
caller are the ordinary adaptedness and integrability facts needed by the conditional
expectation uniqueness theorem; no martingale or intensity statement is used as an
assumption.

The extra integrability hypotheses are explicit because the current `Core` interface
uses Bochner conditional expectation.  They are the usual measurability/integrability
side conditions for the counting and accumulated-intensity processes.
-/

open Filter Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Pathwise additivity of the accumulated intensity -/

omit [MeasurableSpace Ω] in
private theorem integratedIntensity_sub_eq_setIntegral_Ioc
    {Λ H : NNReal → Ω → ℝ} {ω : Ω} {s t : NNReal} (hst : s ≤ t)
    (hInt : IntegrableOn (fun u ↦ H u ω * Λ u ω)
      (Ioc (0 : NNReal) t) timeMeasure) :
    (∫ u in Ioc s t, H u ω * Λ u ω ∂timeMeasure) =
      integratedIntensity Λ H t ω - integratedIntensity Λ H s ω := by
  have h0s : Ioc (0 : NNReal) s ⊆ Ioc (0 : NNReal) t := by
    intro u hu
    exact ⟨hu.1, hu.2.trans hst⟩
  have hst' : Ioc s t ⊆ Ioc (0 : NNReal) t := by
    intro u hu
    exact ⟨lt_of_le_of_lt bot_le hu.1, hu.2⟩
  have hInt0s : IntegrableOn (fun u ↦ H u ω * Λ u ω)
      (Ioc (0 : NNReal) s) timeMeasure := hInt.mono_set h0s
  have hIntst : IntegrableOn (fun u ↦ H u ω * Λ u ω)
      (Ioc s t) timeMeasure := hInt.mono_set hst'
  have hadd :
      (∫ u in Ioc (0 : NNReal) t, H u ω * Λ u ω ∂timeMeasure) =
        (∫ u in Ioc (0 : NNReal) s, H u ω * Λ u ω ∂timeMeasure) +
          ∫ u in Ioc s t, H u ω * Λ u ω ∂timeMeasure := by
    rw [← Ioc_union_Ioc_eq_Ioc (show (0 : NNReal) ≤ s from bot_le) hst]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      hInt0s hIntst
  have hzero : integratedIntensity Λ H 0 ω = 0 := by
    simp [integratedIntensity]
  unfold integratedIntensity at hadd ⊢
  linarith

/-! ## Equality of the finite-horizon measures -/

theorem finiteEventJumpMeasure_eq_intensityMeasure_of_rectangle_measures
    {m : Nat} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i))
    (hpos : ∀ i ω, ξ i ω = ⊤ ∨ (0 : WithTop NNReal) < ξ i ω)
    (Λ : NNReal → Ω → ℝ)
    {T : NNReal} (hT : 0 < T)
    (hrect : ∀ s : NNReal, s < T → ∀ B : Set Ω,
      MeasurableSet[F s] B →
        finiteEventJumpMeasure μ F ξ hξ T (Ioc s T ×ˢ B) =
          finiteHorizonIntensityMeasure μ F Λ T (Ioc s T ×ˢ B)) :
    finiteEventJumpMeasure μ F ξ hξ T =
      finiteHorizonIntensityMeasure μ F Λ T := by
  apply measure_eq_on_predictable_of_eq_finiteHorizon_rectangles F T hT
    (finiteEventJumpMeasure_eq_restrict_finiteHorizon μ F ξ hξ T hpos)
    (finiteHorizonIntensityMeasure_eq_restrict μ F Λ T)
  intro s hs B hB
  exact hrect s hs B hB

/-! ## The generic rectangle-to-intensity theorem -/

/--
From low-level predictable-rectangle measure identities, obtain the operational
`HasPredictableIntensity` conclusion for the finite-event count.

The rectangle hypothesis is an equality of ordinary measures, not a renamed martingale
or intensity assumption.  The `hCount*` and `hAccumulated*` arguments expose only the
adaptedness and Bochner-integrability side conditions needed by
`martingale_of_all_setIntegral_eq_of_isFiniteMeasure`.
-/
theorem hasPredictableIntensity_of_finiteEvent_rectangle_measures
    {m : Nat} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i))
    (hpos : ∀ i ω, ξ i ω = ⊤ ∨ (0 : WithTop NNReal) < ξ i ω)
    (hdist : ∀ ω j l, ξ j ω ≠ ⊤ → ξ l ω ≠ ⊤ → ξ j ω = ξ l ω → j = l)
    (Λ : NNReal → Ω → ℝ)
    (hΛ : IsStronglyPredictable F Λ)
    (hΛ_nonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛ_int : ∀ t ω, IntegrableOn (fun s ↦ Λ s ω)
      (Ioc (0 : NNReal) t) timeMeasure)
    (hrect : ∀ {T : NNReal}, 0 < T → ∀ s : NNReal, s < T → ∀ B : Set Ω,
      MeasurableSet[F s] B →
        finiteEventJumpMeasure μ F ξ hξ T (Ioc s T ×ˢ B) =
          finiteHorizonIntensityMeasure μ F Λ T (Ioc s T ×ˢ B))
    (hProd : ∀ H, IsBoundedSimplePredictable F H → ∀ _T : NNReal,
      Integrable (fun z : NNReal × Ω => Λ z.1 z.2 * H z.1 z.2)
        (timeMeasure.prod μ))
    (hPathProd : ∀ H, IsBoundedSimplePredictable F H → ∀ t ω,
      IntegrableOn (fun s ↦ H s ω * Λ s ω)
        (Ioc (0 : NNReal) t) timeMeasure)
    (hCountAdapted : ∀ H, IsBoundedSimplePredictable F H →
      StronglyAdapted F (fun t ω ↦ countingIntegral
        (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω))
    (hCountIntegrable : ∀ H, IsBoundedSimplePredictable F H → ∀ t,
      Integrable (countingIntegral
        (fun u ω' ↦ finiteEventCountTop ξ u ω') H t) μ)
    (hAccumulatedAdapted : ∀ H, IsBoundedSimplePredictable F H →
      StronglyAdapted F (fun t ω ↦ integratedIntensity Λ H t ω))
    (hAccumulatedIntegrable : ∀ H, IsBoundedSimplePredictable F H → ∀ t,
      Integrable (integratedIntensity Λ H t) μ) :
    HasPredictableIntensity μ F
      (fun t ω ↦ finiteEventCountTop ξ t ω) Λ := by
  have hMeasureEq : ∀ T : NNReal, 0 < T →
      finiteEventJumpMeasure μ F ξ hξ T =
        finiteHorizonIntensityMeasure μ F Λ T := by
    intro T hT
    apply finiteEventJumpMeasure_eq_intensityMeasure_of_rectangle_measures
      μ F ξ hξ hpos Λ hT
    intro s hs B hB
    exact hrect hT s hs B hB

  have hRectangleIntegral : ∀ (H : NNReal → Ω → ℝ),
      IsBoundedSimplePredictable F H → ∀ {s t : NNReal}, s < t →
      ∀ B : Set Ω, MeasurableSet[F s] B →
      (∫ ω in B, (countingIntegral
          (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω -
        countingIntegral
          (fun u ω' ↦ finiteEventCountTop ξ u ω') H s ω) ∂μ) =
        ∫ ω in B, (integratedIntensity Λ H t ω -
          integratedIntensity Λ H s ω) ∂μ := by
    intro H hH s t hst B hB
    have ht : 0 < t := lt_of_le_of_lt bot_le hst
    have hst_le : s ≤ t := hst.le
    have hJump := finiteEventJumpMeasure_rectangle_setIntegral_eq_countingIncrement
      μ F ξ hξ hdist hst_le hB hH
    have hIntensity := finiteHorizonIntensityMeasure_rectangle_setIntegral_eq
      μ F Λ hΛ hΛ_nonneg (s := s) (t := t) (T := t) le_rfl hB hH
        (hProd H hH t)
    have hMeasure := hMeasureEq t ht
    have hMeasureIntegral :
        (∫ z in predictableRectangle s t B,
          H z.1 z.2 ∂finiteEventJumpMeasure μ F ξ hξ t) =
          ∫ z in predictableRectangle s t B,
            H z.1 z.2 ∂finiteHorizonIntensityMeasure μ F Λ t := by
      rw [hMeasure]
    have hInner :
        (∫ ω in B, ∫ u in Ioc s t, H u ω * Λ u ω ∂timeMeasure ∂μ) =
          ∫ ω in B, (integratedIntensity Λ H t ω -
            integratedIntensity Λ H s ω) ∂μ := by
      apply setIntegral_congr_fun (F.le s B hB)
      intro ω hω
      simpa using integratedIntensity_sub_eq_setIntegral_Ioc hst_le
        (hPathProd H hH t ω)
    calc
      (∫ ω in B, countingIntegral
          (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω -
        countingIntegral
          (fun u ω' ↦ finiteEventCountTop ξ u ω') H s ω ∂μ) =
          ∫ z in predictableRectangle s t B,
            H z.1 z.2 ∂finiteEventJumpMeasure μ F ξ hξ t := hJump.symm
      _ = ∫ z in predictableRectangle s t B,
            H z.1 z.2 ∂finiteHorizonIntensityMeasure μ F Λ t :=
        hMeasureIntegral
      _ = ∫ ω in B, ∫ u in Ioc s t, H u ω * Λ u ω ∂timeMeasure ∂μ :=
        hIntensity
      _ = ∫ ω in B, (integratedIntensity Λ H t ω -
            integratedIntensity Λ H s ω) ∂μ := hInner

  refine ⟨hΛ, hΛ_nonneg, hΛ_int, ?_⟩
  intro H hH
  have hAdapted : StronglyAdapted F
      (compensatedIntegral
        (fun t ω ↦ finiteEventCountTop ξ t ω) Λ H) := by
    change StronglyAdapted F (fun t ω ↦
      countingIntegral (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω -
        integratedIntensity Λ H t ω)
    exact (hCountAdapted H hH).sub (hAccumulatedAdapted H hH)
  apply martingale_of_all_setIntegral_eq_of_isFiniteMeasure hAdapted
  intro t
  change Integrable (fun ω ↦
    countingIntegral (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω -
      integratedIntensity Λ H t ω) μ
  exact (hCountIntegrable H hH t).sub (hAccumulatedIntegrable H hH t)
  intro s t hst B hB
  by_cases hEq : s = t
  · subst t
    rfl
  · have hlt : s < t := lt_of_le_of_ne hst hEq
    have hRect := hRectangleIntegral H hH hlt B hB
    have hCountS : Integrable (countingIntegral
        (fun u ω' ↦ finiteEventCountTop ξ u ω') H s) (μ.restrict B) :=
      (hCountIntegrable H hH s).mono_measure Measure.restrict_le_self
    have hCountT : Integrable (countingIntegral
        (fun u ω' ↦ finiteEventCountTop ξ u ω') H t) (μ.restrict B) :=
      (hCountIntegrable H hH t).mono_measure Measure.restrict_le_self
    have hAccumS : Integrable (integratedIntensity Λ H s) (μ.restrict B) :=
      (hAccumulatedIntegrable H hH s).mono_measure Measure.restrict_le_self
    have hAccumT : Integrable (integratedIntensity Λ H t) (μ.restrict B) :=
      (hAccumulatedIntegrable H hH t).mono_measure Measure.restrict_le_self
    have hRect' :
        (∫ ω in B, countingIntegral
            (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω ∂μ) -
          ∫ ω in B, countingIntegral
            (fun u ω' ↦ finiteEventCountTop ξ u ω') H s ω ∂μ =
        (∫ ω in B, integratedIntensity Λ H t ω ∂μ) -
          ∫ ω in B, integratedIntensity Λ H s ω ∂μ := by
      have hCountSub :
          (∫ ω in B, countingIntegral
              (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω -
            countingIntegral
              (fun u ω' ↦ finiteEventCountTop ξ u ω') H s ω ∂μ) =
            (∫ ω in B, countingIntegral
              (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω ∂μ) -
              ∫ ω in B, countingIntegral
                (fun u ω' ↦ finiteEventCountTop ξ u ω') H s ω ∂μ := by
        exact integral_sub' hCountT hCountS
      have hAccumSub :
          (∫ ω in B, integratedIntensity Λ H t ω -
            integratedIntensity Λ H s ω ∂μ) =
            (∫ ω in B, integratedIntensity Λ H t ω ∂μ) -
              ∫ ω in B, integratedIntensity Λ H s ω ∂μ := by
        exact integral_sub' hAccumT hAccumS
      linarith [hRect, hCountSub, hAccumSub]
    change (∫ ω, (countingIntegral
        (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω -
      integratedIntensity Λ H t ω) ∂μ.restrict B) =
      ∫ ω, (countingIntegral
        (fun u ω' ↦ finiteEventCountTop ξ u ω') H s ω -
      integratedIntensity Λ H s ω) ∂μ.restrict B
    have hLeft :
        (∫ ω in B, countingIntegral
            (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω -
          integratedIntensity Λ H t ω ∂μ) =
          (∫ ω in B, countingIntegral
            (fun u ω' ↦ finiteEventCountTop ξ u ω') H t ω ∂μ) -
            ∫ ω in B, integratedIntensity Λ H t ω ∂μ := by
      exact integral_sub' hCountT hAccumT
    have hRight :
        (∫ ω in B, countingIntegral
            (fun u ω' ↦ finiteEventCountTop ξ u ω') H s ω -
          integratedIntensity Λ H s ω ∂μ) =
          (∫ ω in B, countingIntegral
            (fun u ω' ↦ finiteEventCountTop ξ u ω') H s ω ∂μ) -
            ∫ ω in B, integratedIntensity Λ H s ω ∂μ := by
      exact integral_sub' hCountS hAccumS
    rw [hLeft, hRight]
    linarith [hRect']

end OTSelector.CountingProcess
