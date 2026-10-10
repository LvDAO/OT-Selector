import OTSelector.Limit.FeedbackMarkedHolding
import OTSelector.Limit.FeedbackMartingaleProblemSurvival

/-!
# The first marked jump from its compensator equations

The finite measure of attained first jumps is identified by its stopped count compensators.
Its total mass is not assumed to be one: the equations themselves exclude an infinite wait.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OTSelector.Limit

private theorem measure_restrict_prod_map_fst {E : Type*} [MeasurableSpace E]
    (ν : Measure (ℝ × E)) {A : Set ℝ} {B : Set E}
    (hA : MeasurableSet A) (_hB : MeasurableSet B) :
    ((ν.restrict (univ ×ˢ B)).map Prod.fst) A = ν (A ×ˢ B) := by
  rw [Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA)]
  congr 1
  ext p
  simp

/-- Finite marked waiting laws are determined by half-line and mark rectangles. -/
theorem markedWaitingLaw_ext {E : Type*} [MeasurableSpace E]
    (μ ν : Measure (ℝ × E)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t B, MeasurableSet B → μ (Iic t ×ˢ B) = ν (Iic t ×ˢ B)) : μ = ν := by
  apply Measure.ext_prod
  intro A B hA hB
  have heq : (μ.restrict (univ ×ˢ B)).map Prod.fst =
      (ν.restrict (univ ×ˢ B)).map Prod.fst := by
    apply Measure.ext_of_Iic
    intro t
    rw [measure_restrict_prod_map_fst _ measurableSet_Iic hB,
      measure_restrict_prod_map_fst _ measurableSet_Iic hB]
    exact h t B hB
  have := congrArg (fun m : Measure ℝ ↦ m A) heq
  simpa only [measure_restrict_prod_map_fst _ hA hB] using this

/-- The stopped first-count equations determine both the exponential wait and the mark law.
The input measure records only attained first jumps and is merely finite; the conclusion also
proves that its mass is one, so an infinite waiting time has zero probability. -/
theorem markedWaitingLaw_eq_of_compensator {E : Type*} [MeasurableSpace E]
    (ν : Measure (ℝ × E)) [IsFiniteMeasure ν] (π : Measure E) [IsProbabilityMeasure π]
    {r : ℝ} (hr : 0 < r)
    (hcomp : ∀ t, 0 ≤ t → ∀ B, MeasurableSet B →
      ν.real (Iic t ×ˢ B) = r * π.real B *
        ∫ s in 0..t, 1 - ν.real (Iic s ×ˢ univ)) :
    ν = (expMeasure r).prod π := by
  let F : ℝ → ℝ := fun t ↦ ν.real (Iic t ×ˢ univ)
  have hmono : Monotone F := by
    intro s t hst
    exact measureReal_mono (Set.prod_mono (Iic_subset_Iic.mpr hst) Subset.rfl)
  have hInt (t : ℝ) : IntervalIntegrable (fun s ↦ 1 - F s) volume 0 t :=
    intervalIntegrable_const.sub hmono.intervalIntegrable
  have hS (t : ℝ) (ht : 0 ≤ t) :
      1 - F t = 1 - r * ∫ s in 0..t, 1 - F s := by
    have hc := hcomp t ht univ MeasurableSet.univ
    simpa only [probReal_univ, mul_one] using congrArg (fun a : ℝ ↦ 1 - a) hc
  have hexp (t : ℝ) (ht : 0 ≤ t) : 1 - F t = Real.exp (-r * t) :=
    survival_eq_exp_of_locally_integrable (fun s _ ↦ hInt s) hS ht
  have hz : ν (Iic 0 ×ˢ (univ : Set E)) = 0 := by
    have hc := hcomp 0 le_rfl univ MeasurableSet.univ
    simp only [intervalIntegral.integral_same, mul_zero] at hc
    exact ((ENNReal.toReal_eq_zero_iff _).mp hc).resolve_right (measure_ne_top ν _)
  let := isProbabilityMeasure_expMeasure hr
  apply markedWaitingLaw_ext
  intro t B hB
  apply (measureReal_eq_measureReal_iff).mp
  change ν.real (Iic t ×ˢ B) = (((expMeasure r).prod π) (Iic t ×ˢ B)).toReal
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  change ν.real (Iic t ×ˢ B) = (expMeasure r).real (Iic t) * π.real B
  rw [← cdf_eq_real, cdf_expMeasure_eq hr]
  by_cases ht : 0 ≤ t
  · rw [ite_eq_left ht, hcomp t ht B hB]
    have he := hS t ht
    have he' := hexp t ht
    change r * π.real B * (∫ s in 0..t, 1 - F s) =
      (1 - Real.exp (-(r * t))) * π.real B
    rw [neg_mul] at he'
    have hrate : r * (∫ s in 0..t, 1 - F s) = 1 - Real.exp (-(r * t)) := by
      linarith
    calc
      _ = (r * (∫ s in 0..t, 1 - F s)) * π.real B := by ring
      _ = _ := by rw [hrate]
  · rw [ite_eq_right ht, zero_mul]
    have hzero : ν (Iic t ×ˢ B) = 0 := measure_mono_null
      (Set.prod_mono (Iic_subset_Iic.mpr (le_of_not_ge ht)) (subset_univ B)) hz
    simp [measureReal_def, hzero]

/-- At a fixed feedback current, the first-jump compensators identify the actual holding and
marked nearest-neighbor transition kernel. -/
theorem feedbackMarkedHoldingKernel_eq_of_compensator {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (ν : Measure FeedbackMarkedStep) [IsFiniteMeasure ν]
    (hcomp : ∀ t, 0 ≤ t → ∀ B : Set (UnitMark × ℤ), MeasurableSet B →
      ν.real (Iic t ×ˢ B) = totalJumpRate lam k *
        (feedbackMarkedJumpKernel lam k).real B *
          ∫ s in 0..t, 1 - ν.real (Iic s ×ˢ univ)) :
    ν = feedbackMarkedHoldingKernel lam k := by
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  exact markedWaitingLaw_eq_of_compensator ν (feedbackMarkedJumpKernel lam k)
    (totalJumpRate_pos hlam0 hlam k) hcomp

end OTSelector.Limit
