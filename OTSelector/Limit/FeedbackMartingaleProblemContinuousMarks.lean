import OTSelector.Limit.FeedbackMartingaleProblemFirstJump
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Continuous mark tests suffice for first-jump identification

The finite spatial martingales use continuous bounded geometric-mark tests. After stopping,
mathlib's finite-measure uniqueness theorem upgrades these tests to the mark rectangles used
by the existing exponential holding-law proof.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace OTSelector.Limit

/-- Continuous bounded mark tests in the stopped compensator equations determine the full
marked holding law. No measurable-indicator martingale hypothesis is needed. -/
theorem markedWaitingLaw_eq_of_continuous_compensator
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [HasOuterApproxClosed E]
    [BorelSpace E] (ν : Measure (ℝ × E)) [IsFiniteMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] {r : ℝ} (hr : 0 < r)
    (hcomp : ∀ t, 0 ≤ t → ∀ ψ : E →ᵇ ℝ,
      (∫ z in Iic t ×ˢ (univ : Set E), ψ z.2 ∂ν) =
        r * (∫ u, ψ u ∂π) * ∫ s in 0..t, 1 - ν.real (Iic s ×ˢ univ)) :
    ν = (expMeasure r).prod π := by
  apply markedWaitingLaw_eq_of_compensator ν π hr
  intro t ht B hB
  have hmass : ν.real (Iic t ×ˢ (univ : Set E)) =
      r * ∫ s in 0..t, 1 - ν.real (Iic s ×ˢ univ) := by
    have h := hcomp t ht (BoundedContinuousFunction.const E 1)
    simpa only [BoundedContinuousFunction.const_apply, integral_const,
      MeasureTheory.Measure.real, measureReal_def, smul_eq_mul, mul_one,
      measure_univ, ENNReal.toReal_one, one_mul, Measure.restrict_apply_univ] using h
  let νt : Measure E := (ν.restrict (Iic t ×ˢ (univ : Set E))).map Prod.snd
  have : IsFiniteMeasure (ENNReal.ofReal (ν.real (Iic t ×ˢ (univ : Set E))) • π) :=
    Measure.smul_finite π ENNReal.ofReal_ne_top
  have hsliceeq : νt = ENNReal.ofReal (ν.real (Iic t ×ˢ (univ : Set E))) • π := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro ψ
    rw [show νt = (ν.restrict (Iic t ×ˢ (univ : Set E))).map Prod.snd from rfl, integral_map measurable_snd.aemeasurable ψ.continuous.measurable.aestronglyMeasurable,
      integral_smul_measure, ENNReal.toReal_ofReal measureReal_nonneg, smul_eq_mul]
    rw [hcomp t ht ψ, hmass]
    ring
  have heq : ν (Iic t ×ˢ B) =
      ENNReal.ofReal (ν.real (Iic t ×ˢ (univ : Set E))) * π B := by
    calc
      _ = νt B := by
        rw [show νt = (ν.restrict (Iic t ×ˢ (univ : Set E))).map Prod.snd from rfl, Measure.map_apply measurable_snd hB,
          Measure.restrict_apply (measurable_snd hB)]
        congr 1
        ext z
        simp [and_comm]
      _ = _ := by rw [hsliceeq, Measure.smul_apply, smul_eq_mul]
  have hre := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal measureReal_nonneg] at hre
  change ν.real (Iic t ×ˢ B) = ν.real (Iic t ×ˢ (univ : Set E)) * π.real B at hre
  rw [hre, hmass]
  ring

end OTSelector.Limit
