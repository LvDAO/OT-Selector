import OTSelector.PointProcess.MatchingSceneStationarity

/-!
# Passing local residual expectations through scene-law limits

A uniform second moment controls the truncation error of a real observable. The actual scene
continuous-mapping theorem then permits almost-everywhere continuous counting observables.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace OTSelector.Probability

private noncomputable def realClip (R : ℝ) (hR : 0 ≤ R) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x ↦ max (-R) (min R x), continuous_const.max (continuous_const.min continuous_id)⟩
    (2 * R) (fun x y ↦ by
      rw [Real.dist_eq, abs_le]
      change -(2 * R) ≤ max (-R) (min R x) - max (-R) (min R y) ∧
        max (-R) (min R x) - max (-R) (min R y) ≤ 2 * R
      have hx0 := le_max_left (-R) (min R x)
      have hy0 := le_max_left (-R) (min R y)
      have hx1 : max (-R) (min R x) ≤ R := max_le (by linarith) (min_le_left _ _)
      have hy1 : max (-R) (min R y) ≤ R := max_le (by linarith) (min_le_left _ _)
      constructor <;> linarith)

private theorem abs_sub_realClip_le_sq_div {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |x - realClip R hR.le x| ≤ x ^ 2 / R := by
  change |x - max (-R) (min R x)| ≤ _
  by_cases hx : x ≤ R
  · rw [min_eq_right hx]
    by_cases hx' : -R ≤ x
    · simp only [max_eq_right hx', sub_self, abs_zero]
      positivity
    · have hx'' : x < -R := lt_of_not_ge hx'
      rw [max_eq_left hx''.le, abs_of_nonpos (by linarith)]
      apply (le_div_iff₀ hR).mpr
      nlinarith [sq_nonneg (x + R)]
  · have hx' : R < x := lt_of_not_ge hx
    rw [min_eq_left hx'.le, max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    apply (le_div_iff₀ hR).mpr
    nlinarith [sq_nonneg (x - R)]

private theorem integrable_id_of_integrable_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsq : Integrable (fun x : ℝ ↦ x ^ 2) μ) : Integrable (fun x : ℝ ↦ x) μ := by
  apply ((integrable_const (1 : ℝ)).add hsq).mono' measurable_id.aestronglyMeasurable
  filter_upwards with x
  simp only [Real.norm_eq_abs, Pi.add_apply, id_eq]
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

private theorem norm_integral_sub_realClip_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsq : Integrable (fun x : ℝ ↦ x ^ 2) μ) {C R : ℝ}
    (hC : (∫ x : ℝ, x ^ 2 ∂μ) ≤ C) (hR : 0 < R) :
    ‖(∫ x : ℝ, x ∂μ) - ∫ x : ℝ, realClip R hR.le x ∂μ‖ ≤ C / R := by
  have hi := integrable_id_of_integrable_sq μ hsq
  have hc := (realClip R hR.le).integrable μ
  rw [← integral_sub hi hc]
  calc
    _ ≤ ∫ x : ℝ, ‖x - realClip R hR.le x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, x ^ 2 / R ∂μ := integral_mono (hi.sub hc).norm
      (hsq.div_const R) (fun x ↦ by
        simpa only [Real.norm_eq_abs] using abs_sub_realClip_le_sq_div hR x)
    _ = (∫ x : ℝ, x ^ 2 ∂μ) / R := integral_div _ _
    _ ≤ C / R := div_le_div_of_nonneg_right hC hR.le

/-- Real weak limits with a uniform second moment preserve first moments. -/
theorem tendsto_integral_id_of_probability_tendsto_of_sq_bound
    {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hlim : Tendsto μ atTop (𝓝 ν)) {C : ℝ} (hC : 0 ≤ C)
    (hsq : ∀ i, Integrable (fun x : ℝ ↦ x ^ 2) (μ i : Measure ℝ))
    (hbound : ∀ i, (∫ x : ℝ, x ^ 2 ∂(μ i : Measure ℝ)) ≤ C) :
    Tendsto (fun i ↦ ∫ x : ℝ, x ∂(μ i : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, x ∂(ν : Measure ℝ))) := by
  have hmoment : (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂(ν : Measure ℝ)) ≤ ENNReal.ofReal C := by
    apply PointProcess.lintegral_ofReal_le_of_probability_tendsto hlim
      (show Continuous (fun x : ℝ ↦ x ^ 2) from continuous_id.pow 2)
    apply Eventually.of_forall
    intro i
    rw [← ofReal_integral_eq_lintegral_ofReal (hsq i) (ae_of_all _ fun x ↦ sq_nonneg x)]
    exact ENNReal.ofReal_le_ofReal (hbound i)
  have hνsq : Integrable (fun x : ℝ ↦ x ^ 2) (ν : Measure ℝ) := by
    refine ⟨(measurable_id.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ sq_nonneg x)]
    exact hmoment.trans_lt ENNReal.ofReal_lt_top
  have hνbound : (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) ≤ C := by
    rw [← ofReal_integral_eq_lintegral_ofReal hνsq (ae_of_all _ fun x ↦ sq_nonneg x)] at hmoment
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmoment
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun x : ℝ ↦ sq_nonneg x)),
      ENNReal.toReal_ofReal hC] using hh
  rw [Metric.tendsto_atTop]
  intro ε hε
  let R : ℝ := 4 * (C + 1) / ε
  have hR : 0 < R := div_pos (by positivity) hε
  have htail : C / R < ε / 4 := by
    apply (div_lt_iff₀ hR).mpr
    dsimp [R]
    have heq : ε / 4 * (4 * (C + 1) / ε) = C + 1 := by field_simp
    rw [heq]
    linarith
  have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim (realClip R hR.le)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hc (ε / 2) (by linarith)
  refine ⟨N, fun i hi ↦ ?_⟩
  have hμtail := norm_integral_sub_realClip_le (μ i : Measure ℝ) (hsq i) (hbound i) hR
  have hνtail := norm_integral_sub_realClip_le (ν : Measure ℝ) hνsq hνbound hR
  have hmiddle := hN i hi
  rw [Real.dist_eq] at hmiddle ⊢
  rw [Real.norm_eq_abs] at hμtail hνtail
  calc
    _ ≤ |(∫ x : ℝ, x ∂(μ i : Measure ℝ)) -
        ∫ x : ℝ, realClip R hR.le x ∂(μ i : Measure ℝ)| +
        |(∫ x : ℝ, realClip R hR.le x ∂(μ i : Measure ℝ)) -
          ∫ x : ℝ, realClip R hR.le x ∂(ν : Measure ℝ)| +
        |(∫ x : ℝ, realClip R hR.le x ∂(ν : Measure ℝ)) -
          ∫ x : ℝ, x ∂(ν : Measure ℝ)| := by
      have h₁ := abs_sub_le (∫ x : ℝ, x ∂(μ i : Measure ℝ))
        (∫ x : ℝ, realClip R hR.le x ∂(μ i : Measure ℝ))
        (∫ x : ℝ, x ∂(ν : Measure ℝ))
      have h₂ := abs_sub_le (∫ x : ℝ, realClip R hR.le x ∂(μ i : Measure ℝ))
        (∫ x : ℝ, realClip R hR.le x ∂(ν : Measure ℝ))
        (∫ x : ℝ, x ∂(ν : Measure ℝ))
      linarith
    _ < ε := by rw [abs_sub_comm (∫ x : ℝ, realClip R hR.le x ∂(ν : Measure ℝ))]; linarith

end OTSelector.Probability

namespace OTSelector.PointProcess.MatchingScene

/-- Actual local counting residuals may pass through scene limits when their second moments
are uniformly controlled and their discontinuity cuts have zero limiting probability. -/
theorem tendsto_integral_of_ae_continuousAt_of_sq_bound
    (μ : ℕ → ProbabilityMeasure MatchingScene) {ν : ProbabilityMeasure MatchingScene}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun i ↦ (μ i : Measure MatchingScene)))
    {f : MatchingScene → ℝ} (hf : Measurable f)
    (hcont : ∀ᵐ scene ∂(ν : Measure MatchingScene), ContinuousAt f scene)
    {C : ℝ} (hC : 0 ≤ C)
    (hsq : ∀ i, Integrable (fun scene ↦ f scene ^ 2) (μ i : Measure MatchingScene))
    (hbound : ∀ i, (∫ scene, f scene ^ 2 ∂(μ i : Measure MatchingScene)) ≤ C) :
    Tendsto (fun i ↦ ∫ scene, f scene ∂(μ i : Measure MatchingScene)) atTop
      (𝓝 (∫ scene, f scene ∂(ν : Measure MatchingScene))) := by
  have hm := tendsto_map_of_ae_continuousAt μ hlim htight hf hcont
  have hmeasSq : Measurable (fun x : ℝ ↦ x ^ 2) := measurable_id.pow_const 2
  have hmeasId : Measurable (fun x : ℝ ↦ x) := measurable_id
  have hi (i : ℕ) : Integrable (fun x : ℝ ↦ x ^ 2)
      ((μ i).map hf.aemeasurable : Measure ℝ) := by
    rw [ProbabilityMeasure.toMeasure_map]
    exact (integrable_map_measure hmeasSq.aestronglyMeasurable
      hf.aemeasurable).mpr (hsq i)
  have hb (i : ℕ) : (∫ x : ℝ, x ^ 2 ∂((μ i).map hf.aemeasurable : Measure ℝ)) ≤ C := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map hf.aemeasurable
      hmeasSq.aestronglyMeasurable]
    exact hbound i
  have h := Probability.tendsto_integral_id_of_probability_tendsto_of_sq_bound hm hC hi hb
  simpa only [ProbabilityMeasure.toMeasure_map,
    integral_map hf.aemeasurable hmeasId.aestronglyMeasurable] using h

end OTSelector.PointProcess.MatchingScene
