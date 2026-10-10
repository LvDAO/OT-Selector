import OTSelector.Limit.FeedbackMartingaleProblemStoppingPair
import OTSelector.Limit.FeedbackMartingaleProblemFirstTest
import Mathlib.Probability.ConditionalProbability

/-!
# Conditional first-jump tests after an observed stopping time

The original marked-count martingales may be tested between two bounded stopping coordinates
on every event revealed at the earlier one. A deterministic stopped increment readout then
identifies a restarted first-jump law, without assuming a Markov property at the stopping time.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace OTSelector.Limit

/-- Identifying the attained-jump measure with a probability law also rules out an infinite
wait, and therefore identifies the unrestricted measurable waiting-time/mark readout. -/
theorem ae_finite_and_map_eq_of_attainedFirstJumpLaw_eq
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {τ : Ω → ℝ≥0∞} {J : Ω → E}
    (hτ : Measurable τ) (hJ : Measurable J)
    (ν : Measure (ℝ × E)) [IsProbabilityMeasure ν]
    (heq : attainedFirstJumpLaw μ τ J = ν) :
    (∀ᵐ ω ∂μ, τ ω ≠ ∞) ∧ μ.map (fun ω ↦ ((τ ω).toReal, J ω)) = ν := by
  have hu : attainedFirstJumpLaw μ τ J univ = 1 := by rw [heq]; exact measure_univ
  rw [attainedFirstJumpLaw, Measure.map_apply (hτ.ennreal_toReal.prodMk hJ)
    MeasurableSet.univ] at hu
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter] at hu
  have hf : ∀ᵐ ω ∂μ, τ ω ≠ ∞ :=
    (mem_ae_iff_prob_eq_one ((hτ (measurableSet_singleton ∞)).compl)).mpr hu
  refine ⟨hf, ?_⟩
  have hr : μ.restrict {ω | τ ω ≠ ∞} = μ := Measure.restrict_eq_self_of_ae_mem hf
  exact (congrArg (fun m : Measure Ω ↦ m.map (fun ω ↦ ((τ ω).toReal, J ω))) hr).symm.trans heq

/-- A right-continuous adapted process evaluated at a bounded stopping coordinate is integrable
when its paths have an integrable envelope on that time interval. -/
theorem integrable_stopping_eval_of_rightContinuous
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : StronglyAdapted ℱ M) {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℝ≥0))
    (hτT : ∀ ω, τ ω ≤ T)
    (hRight : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    {D : Ω → ℝ} (hD : Integrable D μ)
    (hBound : ∀ᵐ ω ∂μ, ∀ s, s ≤ T → ‖M s ω‖ ≤ D ω) :
    Integrable (fun ω ↦ M (τ ω) ω) μ := by
  have hm : AEStronglyMeasurable (fun ω ↦ M (τ ω) ω) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n ω ↦ M (CountingProcess.rightGrid (n + 1) (τ ω)) ω)
    · intro n
      exact (CountingProcess.stronglyMeasurable_eval_finiteRange hM
        (CountingProcess.IsStoppingTime.rightGridApprox hτ (n + 1) (by omega))
        (CountingProcess.finiteRange_rightGrid_of_le (n + 1) (by omega) hτT)).aestronglyMeasurable
    · filter_upwards [hRight] with ω hω
      apply (hω (τ ω)).tendsto.comp
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨CountingProcess.tendsto_rightGrid_succ (τ ω),
        Eventually.of_forall fun n ↦ CountingProcess.le_rightGrid (n + 1) (τ ω) (by omega)⟩
  apply hD.mono' hm
  filter_upwards [hBound] with ω hω
  exact hω (τ ω) (hτT ω)

/-- Optional sampling on the actual stopped history determines a restarted first jump.
The only readout premise equates a pathwise increment of the original martingale to its
first-jump count minus occupation. It does not assert a conditional jump kernel. -/
theorem attainedFirstJumpLaw_cond_eq_of_stopping_pair_readout
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E] [HasOuterApproxClosed E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {τ : Ω → ℝ≥0∞} {J : Ω → E} (hτ : Measurable τ) (hJ : Measurable J)
    (π : Measure E) [IsProbabilityMeasure π] {r : ℝ} (hr : 0 < r)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0))
    (ρ : ℝ≥0 → Ω → ℝ≥0)
    (hρ : ∀ t, IsStoppingTime ℱ fun ω ↦ (ρ t ω : WithTop ℝ≥0))
    (hσρ : ∀ t ω, σ ω ≤ ρ t ω)
    (hρBound : ∀ t, ∃ T, ∀ ω, ρ t ω ≤ T)
    (M : (E →ᵇ ℝ) → ℝ≥0 → Ω → ℝ)
    (hM : ∀ ψ, Martingale (M ψ) ℱ μ)
    (hRight : ∀ ψ, ∀ᵐ ω ∂μ, ∀ t,
      ContinuousWithinAt (fun s ↦ M ψ s ω) (Ici t) t)
    (hEnvelope : ∀ ψ T, ∃ D : Ω → ℝ, Integrable D μ ∧
      ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M ψ s ω‖ ≤ D ω)
    {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) (hA0 : μ A ≠ 0)
    (hreadout : ∀ ψ t, (fun ω ↦ M ψ (ρ t ω) ω - M ψ (σ ω) ω)
      =ᵐ[μ.restrict A] firstJumpTestCompensator r π τ J ψ t) :
    attainedFirstJumpLaw μ[|A] τ J = (expMeasure r).prod π := by
  let := cond_isProbabilityMeasure (μ := μ) hA0
  apply attainedFirstJumpLaw_eq_of_continuous_zero_mean μ[|A] hτ hJ π hr
  intro ψ t
  obtain ⟨T, hT⟩ := hρBound t
  obtain ⟨D, hD, hbound⟩ := hEnvelope ψ T
  have hb : ∀ᵐ ω ∂μ, ∀ s, s ≤ T → ‖M ψ s ω‖ ≤ D ω := by
    filter_upwards [hbound] with ω hω
    exact fun s hs ↦ hω s (hs.trans (le_add_of_nonneg_right zero_le))
  have hiρ := integrable_stopping_eval_of_rightContinuous (hM ψ).stronglyAdapted
    (hρ t) hT (hRight ψ) hD hb
  have hiσ := integrable_stopping_eval_of_rightContinuous (hM ψ).stronglyAdapted
    hσ (fun ω ↦ (hσρ t ω).trans (hT ω)) (hRight ψ) hD hb
  have host := setIntegral_martingale_stopping_pair_of_integrable_bound
    (hM ψ) hσ (hρ t) (hσρ t) hT (hRight ψ) hD hbound hA
  simp only [ProbabilityTheory.cond, integral_smul_measure]
  rw [← integral_congr_ae (hreadout ψ t), integral_sub hiρ.integrableOn hiσ.integrableOn,
    host, sub_self, smul_zero]

end OTSelector.Limit
