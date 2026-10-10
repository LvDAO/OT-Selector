import OTSelector.Probability.CountingProcess.FiniteEventCompensator

/-!
# Real rectangle identities as predictable-measure identities

The finite-history calculation naturally produces an equality of real set integrals.  The
finite-event intensity theorem consumes equality of the corresponding predictable measures.
This file supplies the measure-theoretic conversion.  Global integrability of the candidate
rate is used only to prove that its finite-horizon density measure is finite on the rectangle.
-/

open Set
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory

namespace OTSelector.CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A globally integrable nonnegative predictable density makes the constant-one function
integrable for every finite-horizon candidate intensity measure. -/
theorem finiteHorizonIntensityMeasure_integrable_one_of_global
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (Λ : NNReal → Ω → ℝ)
    (hΛ : IsStronglyPredictable F Λ)
    (hΛ_nonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛprod : Integrable (Function.uncurry Λ) (timeMeasure.prod μ))
    (T : NNReal) :
    Integrable (fun _ : NNReal × Ω ↦ (1 : ℝ))
      (finiteHorizonIntensityMeasure μ F Λ T) := by
  let R : Set (NNReal × Ω) := Ioc (0 : NNReal) T ×ˢ (univ : Set Ω)
  let ν : @Measure (NNReal × Ω) F.predictable :=
    (predictableTimeSampleMeasure μ F).restrict R
  let ρ : NNReal × Ω → ENNReal := fun z ↦ ENNReal.ofReal (Λ z.1 z.2)
  have hΛtrim : Integrable (Function.uncurry Λ)
      (predictableTimeSampleMeasure μ F) :=
    hΛprod.trim (predictable_le_prod F) hΛ
  have hΛν : Integrable (Function.uncurry Λ) ν :=
    hΛtrim.mono_measure Measure.restrict_le_self
  have hρ : Measurable[F.predictable] ρ := by
    exact hΛ.measurable.ennreal_ofReal
  have hρtop : ∀ᵐ z ∂ν, ρ z < ∞ :=
    ae_of_all _ fun z ↦ ENNReal.ofReal_lt_top
  have hone : Integrable (fun _ : NNReal × Ω ↦ (1 : ℝ)) (ν.withDensity ρ) := by
    rw [integrable_withDensity_iff hρ hρtop]
    convert hΛν using 1
    funext z
    simp [ρ, Function.uncurry, ENNReal.toReal_ofReal (hΛ_nonneg z.1 z.2)]
  simpa [finiteHorizonIntensityMeasure, R, ν, ρ] using hone

/-- Every predictable set has finite mass under a finite-horizon intensity measure whose
density is globally integrable. -/
theorem finiteHorizonIntensityMeasure_apply_ne_top_of_global
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (Λ : NNReal → Ω → ℝ)
    (hΛ : IsStronglyPredictable F Λ)
    (hΛ_nonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛprod : Integrable (Function.uncurry Λ) (timeMeasure.prod μ))
    (T : NNReal) (P : Set (NNReal × Ω)) :
    finiteHorizonIntensityMeasure μ F Λ T P ≠ ∞ := by
  let ν := finiteHorizonIntensityMeasure μ F Λ T
  have hone : Integrable (fun _ : NNReal × Ω ↦ (1 : ℝ)) ν := by
    exact finiteHorizonIntensityMeasure_integrable_one_of_global
      μ F Λ hΛ hΛ_nonneg hΛprod T
  let : IsFiniteMeasure ν :=
    (integrable_const_iff_isFiniteMeasure one_ne_zero).mp hone
  exact (measure_lt_top ν P).ne

/-- Convert a real count-increment/rate identity on one predictable rectangle into equality of
the finite-event jump measure and the finite-horizon intensity measure on that rectangle. -/
theorem finiteEvent_rectangle_measures_eq_of_countIncrement
    {m : Nat} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i))
    (hdist : ∀ ω i j, ξ i ω ≠ ⊤ → ξ j ω ≠ ⊤ →
      ξ i ω = ξ j ω → i = j)
    (Λ : NNReal → Ω → ℝ)
    (hΛ : IsStronglyPredictable F Λ)
    (hΛ_nonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛprod : Integrable (Function.uncurry Λ) (timeMeasure.prod μ))
    {s T : NNReal} (hsT : s ≤ T)
    {E : Set Ω} (hE : MeasurableSet[F s] E)
    (hInc :
      (∫ ω in E, ((finiteEventCountTop ξ T ω : ℝ) -
          (finiteEventCountTop ξ s ω : ℝ)) ∂μ) =
        ∫ ω in E, ∫ u in Ioc s T, Λ u ω ∂timeMeasure ∂μ) :
    finiteEventJumpMeasure μ F ξ hξ T (Ioc s T ×ˢ E) =
      finiteHorizonIntensityMeasure μ F Λ T (Ioc s T ×ˢ E) := by
  let P : Set (NNReal × Ω) := predictableRectangle s T E
  have hP : MeasurableSet[F.predictable] P :=
    measurableSet_predictableRectangle hE
  have hone := boundedSimplePredictable_one F
  have hprodOne : Integrable
      (fun z : NNReal × Ω ↦ Λ z.1 z.2 * (1 : ℝ))
      (timeMeasure.prod μ) := by
    convert hΛprod using 1
    funext z
    simp [Function.uncurry]
  have hjump := finiteEventJumpMeasure_rectangle_setIntegral_eq_countingIncrement
    μ F ξ hξ hdist hsT hE hone
  have hjumpReal :
      (finiteEventJumpMeasure μ F ξ hξ T).real P =
        ∫ ω in E, ((finiteEventCountTop ξ T ω : ℝ) -
          (finiteEventCountTop ξ s ω : ℝ)) ∂μ := by
    simpa [P, setIntegral_const, smul_eq_mul] using hjump
  have hintensity := finiteHorizonIntensityMeasure_rectangle_setIntegral_eq
    μ F Λ hΛ hΛ_nonneg (s := s) (t := T) (T := T) le_rfl hE hone hprodOne
  have hintensityReal :
      (finiteHorizonIntensityMeasure μ F Λ T).real P =
        ∫ ω in E, ∫ u in Ioc s T, Λ u ω ∂timeMeasure ∂μ := by
    simpa [P, setIntegral_const, smul_eq_mul] using hintensity
  have hjump_ne : finiteEventJumpMeasure μ F ξ hξ T P ≠ ∞ :=
    (measure_lt_top _ _).ne
  have hintensity_ne : finiteHorizonIntensityMeasure μ F Λ T P ≠ ∞ :=
    finiteHorizonIntensityMeasure_apply_ne_top_of_global
      μ F Λ hΛ hΛ_nonneg hΛprod T P
  apply (measureReal_eq_measureReal_iff hjump_ne hintensity_ne).mp
  exact hjumpReal.trans (hInc.trans hintensityReal.symm)

end OTSelector.CountingProcess
