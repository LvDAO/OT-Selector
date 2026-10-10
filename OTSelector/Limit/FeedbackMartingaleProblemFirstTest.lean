import OTSelector.Limit.FeedbackMartingaleProblemCount
import OTSelector.Limit.FeedbackMartingaleProblemContinuousMarks

/-!
# Continuous-test first-jump compensation

This is the expectation form consumed after stopping the original spatial marked-count
martingales. The jump time may be infinite; only attained jumps enter its finite measure.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BoundedContinuousFunction

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- A continuous mark test compensated only while the first jump has not occurred. -/
noncomputable def firstJumpTestCompensator (r : ℝ) (π : Measure E) (τ : Ω → ℝ≥0∞)
    (J : Ω → E) (ψ : E → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (if τ ω ≤ ENNReal.ofReal t then ψ (J ω) else 0) -
    r * (∫ u, ψ u ∂π) * ∫ s in 0..(t : ℝ), if ENNReal.ofReal s < τ ω then 1 else 0

/-- First-jump test compensation is integrable on every finite horizon. -/
theorem integrable_firstJumpTestCompensator [TopologicalSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] {τ : Ω → ℝ≥0∞} {J : Ω → E}
    (hτ : Measurable τ) (hJ : Measurable J) (r : ℝ) (π : Measure E)
    (ψ : E →ᵇ ℝ) (t : ℝ≥0) :
    Integrable (firstJumpTestCompensator r π τ J ψ t) μ := by
  have hc : Integrable (fun ω ↦ if τ ω ≤ ENNReal.ofReal t then ψ (J ω) else 0) μ := by
    apply Integrable.of_bound
      ((ψ.continuous.measurable.comp hJ).ite
        (measurableSet_le hτ measurable_const) measurable_const).aestronglyMeasurable ‖ψ‖
    exact Eventually.of_forall fun ω ↦ by
      split_ifs
      · exact ψ.norm_coe_le_norm _
      · simp
  have hm : Measurable (fun p : ℝ × Ω ↦
      if ENNReal.ofReal p.1 < τ p.2 then (1 : ℝ) else 0) :=
    measurable_const.ite (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
      (hτ.comp measurable_snd)) measurable_const
  have hi : Integrable (fun p : ℝ × Ω ↦
      if ENNReal.ofReal p.1 < τ p.2 then (1 : ℝ) else 0)
      ((volume.restrict (Ioc 0 (t : ℝ))).prod μ) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (Eventually.of_forall fun p ↦ by split_ifs <;> norm_num)
  have hocc : Integrable (fun ω ↦ ∫ s in 0..(t : ℝ),
      if ENNReal.ofReal s < τ ω then (1 : ℝ) else 0) μ := by
    convert hi.integral_prod_right using 1
    funext ω
    exact intervalIntegral.integral_of_le t.property
  exact hc.sub (hocc.const_mul (r * ∫ u, ψ u ∂π))

/-- Integration over the finite attained-jump measure is the actual stopped jump test. -/
theorem integral_attainedFirstJumpLaw_Iic (μ : Measure Ω)
    {τ : Ω → ℝ≥0∞} {J : Ω → E} (hτ : Measurable τ) (hJ : Measurable J)
    {t : ℝ} (ht : 0 ≤ t) {ψ : E → ℝ} (hψ : Measurable ψ) :
    (∫ z in Iic t ×ˢ (univ : Set E), ψ z.2 ∂attainedFirstJumpLaw μ τ J) =
      ∫ ω, if τ ω ≤ ENNReal.ofReal t then ψ (J ω) else 0 ∂μ := by
  have hS : MeasurableSet (Iic t ×ˢ (univ : Set E)) :=
    measurableSet_Iic.prod MeasurableSet.univ
  have hfin : MeasurableSet {ω | τ ω ≠ ∞} := (hτ (measurableSet_singleton ∞)).compl
  have htest : Measurable ((Iic t ×ˢ (univ : Set E)).indicator (fun z : ℝ × E ↦ ψ z.2)) :=
    (hψ.comp measurable_snd).indicator hS
  rw [← integral_indicator hS, attainedFirstJumpLaw,
    integral_map (hτ.ennreal_toReal.prodMk hJ).aemeasurable htest.aestronglyMeasurable,
    ← integral_indicator hfin]
  apply integral_congr_ae
  filter_upwards with ω
  by_cases hf : τ ω ≠ ∞
  · have htau : (τ ω).toReal ≤ t ↔ τ ω ≤ ENNReal.ofReal t :=
      (ENNReal.le_ofReal_iff_toReal_le hf ht).symm
    simp [hf, Set.indicator_apply, htau]
  · have htop : τ ω = ∞ := not_ne_iff.mp hf
    simp [htop]

/-- Zero expectations of continuous-test first-jump compensation identify the full waiting and
mark law. This only uses the expectation consequences of stopping, not a stopped-martingale
hypothesis. -/
theorem attainedFirstJumpLaw_eq_of_continuous_zero_mean
    [TopologicalSpace E] [HasOuterApproxClosed E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : Ω → ℝ≥0∞} {J : Ω → E} (hτ : Measurable τ) (hJ : Measurable J)
    (π : Measure E) [IsProbabilityMeasure π] {r : ℝ} (hr : 0 < r)
    (hmean : ∀ (ψ : E →ᵇ ℝ) t,
      (∫ ω, firstJumpTestCompensator r π τ J ψ t ω ∂μ) = 0) :
    attainedFirstJumpLaw μ τ J = (expMeasure r).prod π := by
  apply markedWaitingLaw_eq_of_continuous_compensator _ π hr
  intro t ht ψ
  let tNN : ℝ≥0 := Real.toNNReal t
  have htNN : (tNN : ℝ) = t := Real.coe_toNNReal t ht
  have hc : Integrable (fun ω ↦ if τ ω ≤ ENNReal.ofReal t then ψ (J ω) else 0) μ := by
    apply Integrable.of_bound
      ((ψ.continuous.measurable.comp hJ).ite
        (measurableSet_le hτ measurable_const) measurable_const).aestronglyMeasurable ‖ψ‖
    exact Eventually.of_forall fun ω ↦ by
      split_ifs
      · exact ψ.norm_coe_le_norm _
      · simp
  have hiocc : Integrable (fun ω ↦ r * (∫ u, ψ u ∂π) *
      ∫ s in 0..t, if ENNReal.ofReal s < τ ω then (1 : ℝ) else 0) μ := by
    have := hc.sub (integrable_firstJumpTestCompensator μ hτ hJ r π ψ tNN)
    convert this using 1
    funext ω
    simp only [Pi.sub_apply, firstJumpTestCompensator, htNN]
    ring
  have hi := hmean ψ tNN
  simp only [firstJumpTestCompensator, htNN] at hi
  rw [integral_sub hc hiocc, integral_const_mul, integral_firstJump_survival μ hτ] at hi
  rw [integral_attainedFirstJumpLaw_Iic μ hτ hJ ht ψ.continuous.measurable]
  have hs (s : ℝ) (hs0 : 0 ≤ s) :
      μ.real {ω | ENNReal.ofReal s < τ ω} =
        1 - (attainedFirstJumpLaw μ τ J).real (Iic s ×ˢ (univ : Set E)) := by
    simp only [measureReal_def]
    rw [attainedFirstJumpLaw_Iic μ hτ hJ hs0 MeasurableSet.univ]
    simp only [mem_univ, and_true]
    have he : {ω | ENNReal.ofReal s < τ ω} = {ω | τ ω ≤ ENNReal.ofReal s}ᶜ := by
      ext ω
      simp
    rw [he]
    exact probReal_compl_eq_one_sub (measurableSet_le hτ measurable_const)
  have hiS : (∫ s in 0..t, μ.real {ω | ENNReal.ofReal s < τ ω}) =
      ∫ s in 0..t, 1 - (attainedFirstJumpLaw μ τ J).real (Iic s ×ˢ (univ : Set E)) := by
    apply intervalIntegral.integral_congr
    intro s hs'
    exact hs s ((uIcc_of_le ht ▸ hs').1)
  rw [hiS] at hi
  linarith

end OTSelector.Limit
