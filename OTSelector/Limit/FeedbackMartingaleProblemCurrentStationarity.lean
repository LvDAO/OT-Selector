import OTSelector.Limit.FeedbackMartingaleProblemCurrentMean
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Stationary current generator balance from the actual marked martingale problem

The single-jump response has derivative equal to the birth-death generator. The actual
multi-event error is quadratic, and reroot stationarity makes the complete current response
zero. Thus every singleton generator has zero expectation under the true root-current law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit
open PointProcess

private theorem holding_response_slope {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t : ℝ ↦ ((1 - Real.exp (-r * t)) / r) / t)
      (𝓝[>] 0) (𝓝 1) := by
  have he : HasDerivAt (fun t : ℝ ↦ Real.exp (-r * t)) (-r) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (-r)).exp) using 1 <;> simp
  have hd : HasDerivAt (fun t : ℝ ↦ (1 - Real.exp (-r * t)) / r) 1 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub he).div_const r using 1 <;>
      first | rfl | simp [hr.ne']
  simpa only [zero_add, mul_zero, Real.exp_zero, sub_self, zero_div, sub_zero,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

private theorem holding_response_ratio_bounds {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    0 ≤ ((1 - Real.exp (-r * t)) / r) / t ∧
      ((1 - Real.exp (-r * t)) / r) / t ≤ 1 := by
  have hexp : Real.exp (-r * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  refine ⟨div_nonneg (div_nonneg (sub_nonneg.mpr hexp) hr.le) ht.le, ?_⟩
  apply (div_le_iff₀ ht).mpr
  apply (div_le_iff₀ hr).mpr
  have hh := Real.add_one_le_exp (-r * t)
  nlinarith

/-- The derivative at zero of the genuine first-jump response, integrated over any finite
initial current law, is the actual generator expectation. -/
theorem tendsto_integral_feedbackCurrentIndicator_response
    (ρ : Measure ℤ) [IsFiniteMeasure ρ] {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    Tendsto (fun t : ℝ ↦
      (∫ j, ((1 - Real.exp (-totalJumpRate lam j * t)) / totalJumpRate lam j) *
        feedbackCurrentIndicatorGenerator lam k j ∂ρ) / t)
      (𝓝[>] 0) (𝓝 (∫ j, feedbackCurrentIndicatorGenerator lam k j ∂ρ)) := by
  have hh := tendsto_integral_filter_of_dominated_convergence (μ := ρ) (l := 𝓝[>] (0 : ℝ))
    (f := fun j ↦ feedbackCurrentIndicatorGenerator lam k j)
    (F := fun t j ↦ (((1 - Real.exp (-totalJumpRate lam j * t)) / totalJumpRate lam j) / t) *
      feedbackCurrentIndicatorGenerator lam k j)
    (fun _ ↦ (3 : ℝ))
    (Eventually.of_forall fun _ ↦ (measurable_of_countable _).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · convert hh using 1
    funext t
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall fun j ↦ by ring
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact Eventually.of_forall fun j ↦ by
      have hb := holding_response_ratio_bounds (totalJumpRate_pos hlam0 hlam j) ht
      rw [norm_mul, Real.norm_of_nonneg hb.1]
      exact (mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)).trans
        (by simpa using norm_feedbackCurrentIndicatorGenerator_le hlam0 hlam k j)
  · exact Eventually.of_forall fun j ↦ by
      simpa using (holding_response_slope (totalJumpRate_pos hlam0 hlam j)).mul_const
        (feedbackCurrentIndicatorGenerator lam k j)

section OriginalMartingaleProblem
variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
  (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
  (hroot : Measurable[ℱ 0] (fun ω ↦ (e ω).path.rootCurrent))
  (htest : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0),
    Measurable[ℱ t] (fun ω ↦ LocalConfiguration.firstEventTestCount
      (feedbackEnvironmentTwoColor (e ω)) b ψ t))
  (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
  (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
    Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
  (hstationary : ∀ a : ℝ, (μ.map e).map (FeedbackEnvironment.reroot a) = μ.map e)

include he hlam0 hlam hroot htest hsimple hM hstationary in
/-- Stationarity forces the actual first-jump response to be of quadratic order. -/
theorem norm_integral_feedbackCurrentIndicator_response_le (k : ℤ) (t : ℝ≥0) :
    ‖∫ j, ((1 - Real.exp (-totalJumpRate lam j * (t : ℝ))) / totalJumpRate lam j) *
      feedbackCurrentIndicatorGenerator lam k j ∂(μ.map (fun ω ↦ (e ω).path.rootCurrent))‖ ≤
        9 * (t : ℝ) ^ 2 := by
  have hcur : Integrable (fun ω ↦ feedbackCurrentIndicator k (feedbackEnvironmentCurrent (e ω) t)) μ :=
    Integrable.of_bound
      (((measurable_of_countable (feedbackCurrentIndicator k)).comp
        (measurable_feedbackEnvironmentCurrent.comp (f := fun ω ↦ ((t : ℝ), e ω))
          (measurable_const.prodMk he))).aestronglyMeasurable) 1
      (Eventually.of_forall fun _ ↦ norm_feedbackCurrentIndicator_le _ _)
  have hini : Integrable (fun ω ↦ feedbackCurrentIndicator k (e ω).path.rootCurrent) μ :=
    Integrable.of_bound
      (((measurable_of_countable (feedbackCurrentIndicator k)).comp
        (FeedbackEnvironment.measurable_rootCurrent.comp he)).aestronglyMeasurable) 1
      (Eventually.of_forall fun _ ↦ norm_feedbackCurrentIndicator_le _ _)
  have hfirst : Integrable (fun ω ↦ feedbackFirstCurrentIndicator k t (e ω)) μ :=
    Integrable.of_bound ((measurable_feedbackFirstCurrentIndicator k t).comp he).aestronglyMeasurable 1
      (Eventually.of_forall fun _ ↦ by
        unfold feedbackFirstCurrentIndicator
        split_ifs <;> exact norm_feedbackCurrentIndicator_le _ _)
  have hstat : (∫ ω, feedbackCurrentIndicator k (feedbackEnvironmentCurrent (e ω) t) ∂μ) =
      ∫ ω, feedbackCurrentIndicator k (e ω).path.rootCurrent ∂μ := by
    let f := fun e : FeedbackEnvironment ↦ feedbackCurrentIndicator k e.path.rootCurrent
    have hf : Measurable f := (measurable_of_countable (feedbackCurrentIndicator k)).comp
      FeedbackEnvironment.measurable_rootCurrent
    have hr : Measurable (FeedbackEnvironment.reroot (t : ℝ)) :=
      FeedbackEnvironment.measurable_uncurry_reroot.comp
        (f := fun e : FeedbackEnvironment ↦ ((t : ℝ), e)) (measurable_const.prodMk measurable_id)
    have hh := congrArg (fun ν : Measure FeedbackEnvironment ↦ ∫ x, f x ∂ν) (hstationary t)
    rw [integral_map hr.aemeasurable hf.aestronglyMeasurable] at hh
    have hfr : Measurable (fun x ↦ f (FeedbackEnvironment.reroot (t : ℝ) x)) := hf.comp hr
    rw [integral_map he.aemeasurable hfr.aestronglyMeasurable,
      integral_map he.aemeasurable hf.aestronglyMeasurable] at hh
    exact hh
  rw [← integral_feedbackFirstCurrentIndicator_sub_initial μ ℱ e he hlam0 hlam
    hroot htest hsimple hM k t, integral_sub hfirst hini, ← hstat, norm_sub_rev]
  have hh := norm_integral_feedbackCurrentIndicator_sub_first_le μ ℱ e he hlam0 hlam
    htest hsimple hM k t
  rwa [integral_sub hcur hfirst] at hh

include he hlam0 hlam hroot htest hsimple hM hstationary in
/-- Every singleton has zero expected generator under the true stationary root-current law.
Stationarity is a separate premise on the actual reroot map, not an ENV identification premise. -/
theorem integral_feedbackCurrentIndicatorGenerator_eq_zero (k : ℤ) :
    (∫ j, feedbackCurrentIndicatorGenerator lam k j
      ∂(μ.map (fun ω ↦ (e ω).path.rootCurrent))) = 0 := by
  let ρ := μ.map (fun ω ↦ (e ω).path.rootCurrent)
  have hρ : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map
    (FeedbackEnvironment.measurable_rootCurrent.comp he).aemeasurable
  have ht := tendsto_integral_feedbackCurrentIndicator_response ρ hlam0 hlam k
  have hz : Tendsto (fun t : ℝ ↦
      (∫ j, ((1 - Real.exp (-totalJumpRate lam j * t)) / totalJumpRate lam j) *
        feedbackCurrentIndicatorGenerator lam k j ∂ρ) / t)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t : ℝ ↦ 9 * t) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hh := norm_integral_feedbackCurrentIndicator_response_le μ ℱ e he hlam0 hlam
        hroot htest hsimple hM hstationary k ⟨t, ht.le⟩
      rw [norm_div, Real.norm_of_nonneg ht.le]
      apply (div_le_iff₀ ht).mpr
      convert hh using 1 <;> first | rfl | { change 9 * t * t = 9 * t ^ 2; ring }
    · have hlim : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hlim.const_mul 9
  exact tendsto_nhds_unique ht hz

end OriginalMartingaleProblem
end OTSelector.Limit
