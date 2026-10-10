import OTSelector.Feedback.FeedbackEnvironmentCountableTests
import OTSelector.Feedback.FeedbackMarkedEnvironmentResidual
import OTSelector.PointProcess.CountingKernel
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Countable geometric mark tests determine the actual ENV residuals -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology NNReal ENNReal BoundedContinuousFunction
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.Limit
open PointProcess

/-- Joint environment measurability follows from its actual counting kernel and drift. -/
theorem measurable_feedbackEnvironmentMarkedCompensator_markTest
    (lam : ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) :
    Measurable (feedbackEnvironmentMarkedCompensator lam b ψ t) := by
  have hf : StronglyMeasurable ((LocalConfiguration.spatialIoc 0 t).indicator
      (fun p : MatchingPoint ↦ ψ p.2)) :=
    ((ψ.continuous.measurable.comp measurable_snd).indicator
      (LocalConfiguration.measurableSet_spatialIoc 0 t)).stronglyMeasurable
  have hm : Measurable (fun cfg : LocalConfiguration matchingPointBase ↦
      ∫p in LocalConfiguration.spatialIoc 0 t, ψ p.2 ∂LocalConfiguration.countingMeasure cfg) := by
    simpa only [LocalConfiguration.countingKernel_apply,
      integral_indicator (LocalConfiguration.measurableSet_spatialIoc 0 t)] using
      (hf.integral_kernel (κ := LocalConfiguration.countingKernel)).measurable
  exact (hm.comp ((measurable_pi_apply b).comp measurable_feedbackEnvironmentTwoColor)).sub
    (measurable_integral_feedbackEnvironmentMarkRate_current lam b ψ t)

/-- A pathwise envelope uses only the actual local point count. -/
theorem norm_feedbackEnvironmentMarkedCompensator_le_count
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1/2)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) (e : FeedbackEnvironment) :
    ‖feedbackEnvironmentMarkedCompensator lam b ψ t e‖ ≤
      ‖ψ‖*((LocalConfiguration.spatialCount (feedbackEnvironmentTwoColor e b) 0 t : ℝ)+2*(t:ℝ)) := by
  have hc := LocalConfiguration.norm_firstEventTestCount_le (feedbackEnvironmentTwoColor e) b ψ
    (le_refl (t:ℝ))
  have hd : ‖∫u in (0:ℝ)..(t:ℝ), feedbackEnvironmentMarkRate lam b ψ
      (feedbackEnvironmentCurrent e u)‖ ≤ 2*‖ψ‖*(t:ℝ) := by
    simpa only [sub_zero, NNReal.abs_eq] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := (t:ℝ))
        (fun u _ ↦ norm_feedbackEnvironmentMarkRate_le_two_mul hlam0 hlam b ψ ψ.continuous
          (norm_nonneg ψ) (fun v ↦ ψ.norm_coe_le_norm v) (feedbackEnvironmentCurrent e u))
  exact ((norm_sub_le _ _).trans (add_le_add hc hd)).trans_eq (by ring)

private theorem tendsto_integral_bounded_marks (μ : Measure UnitMark) [IsFiniteMeasure μ]
    {ψ : ℕ → UnitMark →ᵇ ℝ} {φ : UnitMark →ᵇ ℝ} {C : ℝ}
    (hC : ∀k, ‖ψ k‖ ≤ C) (hlim : ∀v, Tendsto (fun k ↦ ψ k v) atTop (𝓝 (φ v))) :
    Tendsto (fun k ↦ ∫v, ψ k v ∂μ) atTop (𝓝 (∫v, φ v ∂μ)) :=
  tendsto_integral_of_dominated_convergence (fun _ ↦ C)
    (fun k ↦ (ψ k).continuous.measurable.aestronglyMeasurable) (integrable_const _)
    (fun k ↦ Eventually.of_forall fun v ↦ ((ψ k).norm_coe_le_norm v).trans (hC k))
    (Eventually.of_forall hlim)

/-- The actual marked birth/death rates are continuous under bounded pointwise mark limits. -/
theorem tendsto_feedbackEnvironmentMarkRate_of_bounded_marks
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) (b : Bool) (j : ℤ)
    {ψ : ℕ → UnitMark →ᵇ ℝ} {φ : UnitMark →ᵇ ℝ} {C : ℝ}
    (hC : ∀k, ‖ψ k‖ ≤ C) (hlim : ∀v, Tendsto (fun k ↦ ψ k v) atTop (𝓝 (φ v))) :
    Tendsto (fun k ↦ feedbackEnvironmentMarkRate lam b (ψ k) j) atTop
      (𝓝 (feedbackEnvironmentMarkRate lam b φ j)) := by
  cases b
  · let : IsFiniteMeasure (targetMarkRateMeasure lam j) :=
      ⟨by rw [targetMarkRateMeasure_univ hlam0 hlam]; exact ENNReal.ofReal_lt_top⟩
    simpa only [integral_targetMarkRateMeasure_eq_markMean hlam0 hlam,
      feedbackEnvironmentMarkRate, Bool.false_eq_true, ite_false] using
      tendsto_integral_bounded_marks (targetMarkRateMeasure lam j) hC hlim
  · let : IsFiniteMeasure (sourceMarkRateMeasure lam j) :=
      ⟨by rw [sourceMarkRateMeasure_univ hlam0 hlam]; exact ENNReal.ofReal_lt_top⟩
    simpa only [integral_sourceMarkRateMeasure_eq_markMean hlam0 hlam,
      feedbackEnvironmentMarkRate, ite_true] using
      tendsto_integral_bounded_marks (sourceMarkRateMeasure lam j) hC hlim

/-- Counts and drift in the original environment both respect bounded pointwise mark limits. -/
theorem tendsto_feedbackEnvironmentMarkedCompensator_of_bounded_marks
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2) (b : Bool) (t : ℝ≥0)
    (e : FeedbackEnvironment) {ψ : ℕ → UnitMark →ᵇ ℝ} {φ : UnitMark →ᵇ ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀k, ‖ψ k‖ ≤ C)
    (hlim : ∀v, Tendsto (fun k ↦ ψ k v) atTop (𝓝 (φ v))) :
    Tendsto (fun k ↦ feedbackEnvironmentMarkedCompensator lam b (ψ k) t e) atTop
      (𝓝 (feedbackEnvironmentMarkedCompensator lam b φ t e)) := by
  have hcount : Tendsto (fun k ↦ LocalConfiguration.firstEventTestCount
      (feedbackEnvironmentTwoColor e) b (ψ k) t) atTop
      (𝓝 (LocalConfiguration.firstEventTestCount (feedbackEnvironmentTwoColor e) b φ t)) := by
    let μ := (LocalConfiguration.countingMeasure (feedbackEnvironmentTwoColor e b)).restrict
      (LocalConfiguration.spatialIoc 0 t)
    let : IsFiniteMeasure μ := ⟨by
      rw [Measure.restrict_apply_univ]
      exact LocalConfiguration.countingMeasure_lt_top_of_isBounded _
        (LocalConfiguration.isBounded_spatialIoc 0 t)⟩
    exact tendsto_integral_of_dominated_convergence (μ := μ) (fun _ ↦ C)
      (fun k ↦ ((ψ k).continuous.measurable.comp measurable_snd).aestronglyMeasurable)
      (integrable_const _)
      (fun k ↦ Eventually.of_forall fun p ↦ ((ψ k).norm_coe_le_norm p.2).trans (hC k))
      (Eventually.of_forall fun p ↦ hlim p.2)
  have hdrift : Tendsto (fun k ↦ ∫u in (0:ℝ)..(t:ℝ), feedbackEnvironmentMarkRate lam b (ψ k)
      (feedbackEnvironmentCurrent e u)) atTop
      (𝓝 (∫u in (0:ℝ)..(t:ℝ), feedbackEnvironmentMarkRate lam b φ (feedbackEnvironmentCurrent e u))) := by
    have hint (g : ℝ → ℝ) : (∫u in (0:ℝ)..(t:ℝ), g u) = ∫u in Ioc (0:ℝ) (t:ℝ), g u :=
      intervalIntegral.integral_of_le t.2
    simp only [hint]
    exact tendsto_integral_of_dominated_convergence (fun _ ↦ 2*C)
      (fun k ↦ ((measurable_feedbackEnvironmentMarkRate_current lam b (ψ k)).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable) (integrable_const _)
      (fun k ↦ Eventually.of_forall fun u ↦ norm_feedbackEnvironmentMarkRate_le_two_mul
        hlam0.le hlam b (ψ k) (ψ k).continuous hC0
        (fun v ↦ ((ψ k).norm_coe_le_norm v).trans (hC k)) (feedbackEnvironmentCurrent e u))
      (Eventually.of_forall fun u ↦ tendsto_feedbackEnvironmentMarkRate_of_bounded_marks
        hlam0 hlam b (feedbackEnvironmentCurrent e u) hC hlim)
  exact hcount.sub hdrift

/-- Countably many original marked residual identities imply every bounded continuous mark
identity. The only probability input beyond the countable identities is integrability of
the genuine local counts, supplied in the limit by the proved count-square bounds. -/
theorem integral_markedIncrement_eq_zero_of_countable_marks
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (e : Ω → FeedbackEnvironment) (he : Measurable e) (b : Bool) (s t : ℝ≥0)
    (hs : Integrable (fun ω ↦ (LocalConfiguration.spatialCount (feedbackEnvironmentTwoColor (e ω) b) 0 s : ℝ)) μ)
    (ht : Integrable (fun ω ↦ (LocalConfiguration.spatialCount (feedbackEnvironmentTwoColor (e ω) b) 0 t : ℝ)) μ)
    {G : Ω → ℝ} (hG : Measurable G) {A : ℝ} (hA : 0 ≤ A) (hGb : ∀ω, ‖G ω‖ ≤ A)
    (h : ∀i : ℕ × ℕ, (∫ω, G ω *
      (feedbackEnvironmentMarkedCompensator lam b (countableEnvironmentMarkTest i) t (e ω) -
       feedbackEnvironmentMarkedCompensator lam b (countableEnvironmentMarkTest i) s (e ω)) ∂μ) = 0)
    (φ : UnitMark →ᵇ ℝ) : (∫ω, G ω *
      (feedbackEnvironmentMarkedCompensator lam b φ t (e ω) -
       feedbackEnvironmentMarkedCompensator lam b φ s (e ω)) ∂μ) = 0 := by
  obtain ⟨m,u,hu⟩ := Probability.exists_countableBoundedTest_tendsto UnitMark φ
  let ψ : ℕ → UnitMark →ᵇ ℝ := fun k ↦ countableEnvironmentMarkTest (m,u k)
  have hm (k) : ‖ψ k‖ ≤ (m:ℝ) := (BoundedContinuousFunction.norm_le (Nat.cast_nonneg m)).mpr
    (fun v ↦ Probability.norm_countableBoundedTest_apply_le UnitMark (m,u k) v)
  have hp (v) : Tendsto (fun k ↦ ψ k v) atTop (𝓝 (φ v)) :=
    (continuous_eval_const v).tendsto φ.toContinuousMap |>.comp hu
  let N (r : ℝ≥0) (ω : Ω) : ℝ :=
    LocalConfiguration.spatialCount (feedbackEnvironmentTwoColor (e ω) b) 0 r
  have hbound (k) (r : ℝ≥0) (ω) :
      ‖feedbackEnvironmentMarkedCompensator lam b (ψ k) r (e ω)‖ ≤ (m:ℝ)*(N r ω+2*(r:ℝ)) := by
    apply (norm_feedbackEnvironmentMarkedCompensator_le_count hlam0.le hlam b (ψ k) r (e ω)).trans
    apply mul_le_mul_of_nonneg_right (hm k)
    have hn : 0 ≤ N r ω := by
      dsimp [N]
      exact_mod_cast (LocalConfiguration.spatialCount_nonneg
        (feedbackEnvironmentTwoColor (e ω) b) 0 r)
    exact add_nonneg hn (mul_nonneg (by norm_num) r.2)
  have hconv := tendsto_integral_of_dominated_convergence
    (fun ω ↦ A*((m:ℝ)*(N t ω+2*(t:ℝ))+(m:ℝ)*(N s ω+2*(s:ℝ))))
    (fun k ↦ (hG.mul (((measurable_feedbackEnvironmentMarkedCompensator_markTest lam b (ψ k) t).comp he).sub
      ((measurable_feedbackEnvironmentMarkedCompensator_markTest lam b (ψ k) s).comp he))).aestronglyMeasurable)
    ((((ht.add (integrable_const _)).const_mul (m:ℝ)).add
      ((hs.add (integrable_const _)).const_mul (m:ℝ))).const_mul A)
    (fun k ↦ Eventually.of_forall fun ω ↦ by
      simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, norm_mul]
      exact mul_le_mul (hGb ω) ((norm_sub_le _ _).trans (add_le_add (hbound k t ω) (hbound k s ω)))
        (norm_nonneg _) hA)
    (Eventually.of_forall fun ω ↦ tendsto_const_nhds.mul
      ((tendsto_feedbackEnvironmentMarkedCompensator_of_bounded_marks hlam0 hlam b t (e ω)
        (Nat.cast_nonneg m) hm hp).sub
       (tendsto_feedbackEnvironmentMarkedCompensator_of_bounded_marks hlam0 hlam b s (e ω)
        (Nat.cast_nonneg m) hm hp)))
  exact tendsto_nhds_unique hconv (by simpa only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, ψ, h] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0)))

/-- A genuine first count moment supplies integrability of every original marked compensator. -/
theorem integrable_feedbackEnvironmentMarkedCompensator_of_count
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1/2)
    (e : Ω → FeedbackEnvironment) (he : Measurable e) (b : Bool) (t : ℝ≥0)
    (hcount : Integrable (fun ω ↦
      (LocalConfiguration.spatialCount (feedbackEnvironmentTwoColor (e ω) b) 0 t : ℝ)) μ)
    (ψ : UnitMark →ᵇ ℝ) :
    Integrable (fun ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) μ := by
  apply ((hcount.add (integrable_const (2*(t:ℝ)))).const_mul ‖ψ‖).mono'
    (((measurable_feedbackEnvironmentMarkedCompensator_markTest lam b ψ t).comp he).aestronglyMeasurable)
  exact Eventually.of_forall fun ω ↦ norm_feedbackEnvironmentMarkedCompensator_le_count
    hlam0 hlam b ψ t (e ω)

end OTSelector.Limit
