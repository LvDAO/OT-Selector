import OTSelector.PointProcess.MatchingSceneMomentConvergence
import OTSelector.PointProcess.MatchingSceneMartingaleObservable
import OTSelector.PointProcess.CountingKernel
import OTSelector.Feedback.FeedbackMarkedEnvironmentCylinder
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Passing actual past-cylinder marked residuals to a scene-law limit

The past cylinder is globally continuous in the actual scene topology. Its marked compensator
is continuous at scenes with vacant observation endpoints. The genuine closed-window aggregate
count controls the residual square, so the existing second-moment continuous-mapping theorem
passes its expectation to the weak limit. The square-moment hypothesis is on point counts,
not on the residual to be proved.
-/

open MeasureTheory ProbabilityTheory Set Filter Function Topology
open scoped Classical BigOperators ENNReal NNReal CompactlySupported BoundedContinuousFunction
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance residualPointTopology :
    TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase

/-- A finite canonical environment cylinder is globally continuous on actual scenes. -/
theorem continuous_environmentPastCylinder {ns nt : ℕ}
    (fs : Fin ns → C_c(MatchingPoint, ℝ)) (ft : Fin nt → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ) :
    Continuous (fun scene : MatchingScene ↦
      environmentPastCylinder fs ft H (Matching.feedbackSceneEnvironment scene)) := by
  exact H.continuous.comp
    ((continuous_pi fun i ↦ (LocalConfiguration.continuous_testIntegral (fs i)).comp
      continuous_source).prodMk
      ((continuous_pi fun j ↦ (LocalConfiguration.continuous_testIntegral (ft j)).comp
        continuous_target).prodMk
        ((continuous_of_discreteTopology : Continuous (fun k : ℤ ↦ (k : ℝ))).comp
          continuous_rootCurrent)))

/-- Actual marked counts are measurable in the full scene, without a simplicity premise. -/
theorem measurable_firstEventTestCount (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ) :
    Measurable (fun scene : MatchingScene ↦ LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene)) b ψ t) := by
  have hf : StronglyMeasurable ((LocalConfiguration.spatialIoc 0 t).indicator
      (fun p : MatchingPoint ↦ ψ p.2)) :=
    ((ψ.continuous.measurable.comp measurable_snd).indicator
      (LocalConfiguration.measurableSet_spatialIoc 0 t)).stronglyMeasurable
  have hm : Measurable (fun cfg : LocalConfiguration matchingPointBase ↦
      ∫ p in LocalConfiguration.spatialIoc 0 t, ψ p.2 ∂LocalConfiguration.countingMeasure cfg) := by
    simpa only [LocalConfiguration.countingKernel_apply,
      integral_indicator (LocalConfiguration.measurableSet_spatialIoc 0 t)] using
      (hf.integral_kernel (κ := LocalConfiguration.countingKernel)).measurable
  cases b
  · exact hm.comp measurable_target
  · exact hm.comp measurable_source

/-- The true marked compensator is a measurable scene observable. -/
theorem measurable_feedbackEnvironmentMarkedCompensator (lam : ℝ) (b : Bool)
    (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) :
    Measurable (fun scene : MatchingScene ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene)) :=
  (measurable_firstEventTestCount b ψ t).sub
    ((Limit.measurable_integral_feedbackEnvironmentMarkRate_current lam b ψ t).comp
      Matching.measurable_feedbackSceneEnvironment)

/-- The same canonical past test and future marked residual as in the original finite model. -/
noncomputable def pastMarkedResidual (lam : ℝ) {ns nt : ℕ}
    (fs : Fin ns → C_c(MatchingPoint, ℝ)) (ft : Fin nt → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ)
    (t : ℝ≥0) (scene : MatchingScene) : ℝ :=
  environmentPastCylinder fs ft H (Matching.feedbackSceneEnvironment scene) *
    Limit.feedbackEnvironmentMarkedCompensator lam b ψ t (Matching.feedbackSceneEnvironment scene)

theorem measurable_pastMarkedResidual (lam : ℝ) {ns nt : ℕ}
    (fs : Fin ns → C_c(MatchingPoint, ℝ)) (ft : Fin nt → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) :
    Measurable (pastMarkedResidual lam fs ft H b ψ t) :=
  ((measurable_environmentPastCylinder fs ft H).comp
    Matching.measurable_feedbackSceneEnvironment).mul
    (measurable_feedbackEnvironmentMarkedCompensator lam b ψ t)

theorem continuousAt_pastMarkedResidual (lam : ℝ) {ns nt : ℕ}
    (fs : Fin ns → C_c(MatchingPoint, ℝ)) (ft : Fin nt → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ) (b : Bool) (ψ : UnitMark →ᵇ ℝ)
    (t : ℝ≥0) {scene : MatchingScene} (h0 : scene.VacantCut 0) (ht : scene.VacantCut t) :
    ContinuousAt (pastMarkedResidual lam fs ft H b ψ t) scene :=
  (continuous_environmentPastCylinder fs ft H).continuousAt.mul
    (continuousAt_feedbackEnvironmentMarkedCompensator lam b ψ.continuous t h0 ht)

/-- The actual aggregate counting mass in a closed spatial window, retaining all multiplicities. -/
noncomputable def closedAggregateMass (R : ℝ) (scene : MatchingScene) : ℝ≥0∞ :=
  LocalConfiguration.countingMeasure scene.source (Icc (-R) R ×ˢ (univ : Set UnitMark)) +
    LocalConfiguration.countingMeasure scene.target (Icc (-R) R ×ˢ (univ : Set UnitMark))

/-- Its finite real value, used solely to bound the real marked residual. -/
noncomputable def closedAggregateCount (R : ℝ) (scene : MatchingScene) : ℝ :=
  (closedAggregateMass R scene).toReal

theorem closedAggregateMass_ne_top (R : ℝ) (scene : MatchingScene) :
    closedAggregateMass R scene ≠ ∞ := by
  have hK : IsCompact (Icc (-R) R ×ˢ (univ : Set UnitMark)) := isCompact_Icc.prod isCompact_univ
  exact ENNReal.add_ne_top.mpr
    ⟨(LocalConfiguration.countingMeasure_lt_top_of_isBounded scene.source hK.isBounded).ne,
      (LocalConfiguration.countingMeasure_lt_top_of_isBounded scene.target hK.isBounded).ne⟩

theorem measurable_closedAggregateMass (R : ℝ) : Measurable (closedAggregateMass R) := by
  have hK : MeasurableSet (Icc (-R) R ×ˢ (univ : Set UnitMark)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  exact ((Measure.measurable_coe hK).comp
    (LocalConfiguration.measurable_countingMeasure.comp measurable_source)).add
    ((Measure.measurable_coe hK).comp
      (LocalConfiguration.measurable_countingMeasure.comp measurable_target))

theorem measurable_closedAggregateCount (R : ℝ) : Measurable (closedAggregateCount R) :=
  (measurable_closedAggregateMass R).ennreal_toReal

theorem closedAggregateCount_nonneg (R : ℝ) (scene : MatchingScene) :
    0 ≤ closedAggregateCount R scene := ENNReal.toReal_nonneg

theorem ofReal_sq_closedAggregateCount (R : ℝ) (scene : MatchingScene) :
    ENNReal.ofReal (closedAggregateCount R scene ^ 2) = closedAggregateMass R scene ^ 2 := by
  rw [ENNReal.ofReal_pow (closedAggregateCount_nonneg R scene)]
  simp only [closedAggregateCount, ENNReal.ofReal_toReal (closedAggregateMass_ne_top R scene)]

private theorem color_count_le_closedAggregateCount (scene : MatchingScene) (b : Bool)
    {R : ℝ} {t : ℝ≥0} (htR : (t:ℝ) ≤ R) :
    (LocalConfiguration.spatialCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ) ≤
      closedAggregateCount R scene := by
  have hR : 0 ≤ R := t.2.trans htR
  have hsub : LocalConfiguration.spatialIoc 0 t ⊆ Icc (-R) R ×ˢ (univ : Set UnitMark) := by
    intro p hp
    exact ⟨⟨by linarith [hp.1], hp.2.trans htR⟩, mem_univ _⟩
  rw [LocalConfiguration.spatialCount_cast]
  apply ENNReal.toReal_mono (closedAggregateMass_ne_top R scene)
  cases b
  · exact (measure_mono hsub).trans (le_add_left (le_refl _))
  · exact (measure_mono hsub).trans (le_add_right (le_refl _))

/-- The true residual is bounded by a closed-window count and a deterministic drift term. -/
theorem norm_pastMarkedResidual_le {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) {R : ℝ} (htR : (t:ℝ) ≤ R)
    (scene : MatchingScene) :
    ‖pastMarkedResidual lam fs ft H b ψ t scene‖ ≤
      (‖H‖*‖ψ‖) * (closedAggregateCount R scene + 2*(t:ℝ)) := by
  let e := Matching.feedbackSceneEnvironment scene
  have hcount := (LocalConfiguration.norm_firstEventTestCount_le
    (Limit.feedbackEnvironmentTwoColor e) b ψ (le_refl (t:ℝ))).trans
    (mul_le_mul_of_nonneg_left (color_count_le_closedAggregateCount scene b htR) (norm_nonneg ψ))
  have hdrift : ‖∫ s in (0:ℝ)..(t:ℝ), Limit.feedbackEnvironmentMarkRate lam b ψ
      (Limit.feedbackEnvironmentCurrent e s)‖ ≤ 2*‖ψ‖*(t:ℝ) := by
    simpa only [sub_zero, NNReal.abs_eq] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := (t:ℝ))
        (fun s _ ↦ Limit.norm_feedbackEnvironmentMarkRate_le_two_mul hlam0 hlamHalf b ψ
          ψ.continuous (norm_nonneg ψ) (fun v ↦ ψ.norm_coe_le_norm v)
          (Limit.feedbackEnvironmentCurrent e s))
  have hm : ‖Limit.feedbackEnvironmentMarkedCompensator lam b ψ t e‖ ≤
      ‖ψ‖ * (closedAggregateCount R scene + 2*(t:ℝ)) := by
    exact (norm_sub_le _ _).trans ((add_le_add hcount hdrift).trans_eq (by ring))
  rw [pastMarkedResidual, norm_mul]
  exact (mul_le_mul (norm_environmentPastCylinder_le fs ft H e) hm (norm_nonneg _) (norm_nonneg H)).trans_eq
    (by ring)

/-- The square bound is derived from the actual count, rather than supplied as a residual premise. -/
theorem sq_pastMarkedResidual_le {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) {R : ℝ} (htR : (t:ℝ) ≤ R)
    (scene : MatchingScene) :
    pastMarkedResidual lam fs ft H b ψ t scene ^ 2 ≤
      2*(‖H‖*‖ψ‖)^2 * (closedAggregateCount R scene ^ 2 + 4*(t:ℝ)^2) := by
  have h := norm_pastMarkedResidual_le hlam0 hlamHalf fs ft H b ψ t htR scene
  have hA : 0 ≤ ‖H‖*‖ψ‖ := mul_nonneg (norm_nonneg H) (norm_nonneg ψ)
  have hN := closedAggregateCount_nonneg R scene
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Real.norm_eq_abs, sq_abs] at hs
  calc
    _ ≤ ((‖H‖*‖ψ‖) * (closedAggregateCount R scene + 2*(t:ℝ)))^2 := hs
    _ ≤ 2*(‖H‖*‖ψ‖)^2 * (closedAggregateCount R scene ^ 2 + 4*(t:ℝ)^2) := by
      nlinarith [sq_nonneg ((‖H‖*‖ψ‖) * (closedAggregateCount R scene - 2*(t:ℝ)))]

/-- A finite closed-count second moment gives the real integrable square and its same bound. -/
theorem integrable_sq_closedAggregateCount_of_bound (P : Measure MatchingScene)
    (R : ℝ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : (∫⁻ scene, closedAggregateMass R scene ^ 2 ∂P) ≤ C) :
    Integrable (fun scene ↦ closedAggregateCount R scene ^ 2) P ∧
      (∫ scene, closedAggregateCount R scene ^ 2 ∂P) ≤ C.toReal := by
  have hi : Integrable (fun scene ↦ closedAggregateCount R scene ^ 2) P := by
    refine ⟨((measurable_closedAggregateCount R).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all P fun scene ↦ sq_nonneg _)]
    simp_rw [ofReal_sq_closedAggregateCount]
    exact hbound.trans_lt (lt_top_iff_ne_top.mpr hC)
  refine ⟨hi, ?_⟩
  have hb : ENNReal.ofReal (∫ scene, closedAggregateCount R scene ^ 2 ∂P) ≤ C := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all P fun scene ↦ sq_nonneg _)]
    simpa only [ofReal_sq_closedAggregateCount] using hbound
  have hh := ENNReal.toReal_mono hC hb
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun scene ↦ sq_nonneg (closedAggregateCount R scene)))] using hh

/-- The residual square is integrable and uniformly bounded using only a true count-square bound. -/
theorem integrable_sq_pastMarkedResidual_of_count_bound
    (P : Measure MatchingScene) [IsProbabilityMeasure P]
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) {R : ℝ} (htR : (t:ℝ) ≤ R)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : (∫⁻ scene, closedAggregateMass R scene ^ 2 ∂P) ≤ C) :
    Integrable (fun scene ↦ pastMarkedResidual lam fs ft H b ψ t scene ^ 2) P ∧
      (∫ scene, pastMarkedResidual lam fs ft H b ψ t scene ^ 2 ∂P) ≤
        2*(‖H‖*‖ψ‖)^2 * (C.toReal + 4*(t:ℝ)^2) := by
  obtain ⟨hNi,hNb⟩ := integrable_sq_closedAggregateCount_of_bound P R hC hbound
  have hdom : Integrable (fun scene ↦
      2*(‖H‖*‖ψ‖)^2 * (closedAggregateCount R scene ^ 2 + 4*(t:ℝ)^2)) P :=
    (hNi.add (integrable_const _)).const_mul _
  have hi : Integrable (fun scene ↦ pastMarkedResidual lam fs ft H b ψ t scene ^ 2) P := by
    apply hdom.mono' ((measurable_pastMarkedResidual lam fs ft H b ψ t).pow_const 2).aestronglyMeasurable
    filter_upwards with scene
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
      sq_pastMarkedResidual_le hlam0 hlamHalf fs ft H b ψ t htR scene
  refine ⟨hi, (integral_mono hi hdom (sq_pastMarkedResidual_le hlam0 hlamHalf fs ft H b ψ t htR)).trans ?_⟩
  rw [integral_const_mul, integral_add hNi (integrable_const _)]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  exact mul_le_mul_of_nonneg_left (add_le_add hNb le_rfl) (by positivity)

/-- Actual scene weak convergence preserves a canonical marked residual expectation whenever
the same genuine closed-window second moment is uniformly bounded. -/
theorem tendsto_integral_pastMarkedResidual_of_closed_count_sq_bound
    (μ : ℕ → ProbabilityMeasure MatchingScene) {ν : ProbabilityMeasure MatchingScene}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun k ↦ (μ k : Measure MatchingScene)))
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) {R : ℝ} (htR : (t:ℝ) ≤ R)
    (hcuts : ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.VacantCut 0 ∧ scene.VacantCut t)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcount : ∀ k, (∫⁻ scene, closedAggregateMass R scene ^ 2 ∂(μ k : Measure MatchingScene)) ≤ C) :
    Tendsto (fun k ↦ ∫ scene, pastMarkedResidual lam fs ft H b ψ t scene ∂(μ k : Measure MatchingScene))
      atTop (𝓝 (∫ scene, pastMarkedResidual lam fs ft H b ψ t scene ∂(ν : Measure MatchingScene))) := by
  have hsq (k : ℕ) := integrable_sq_pastMarkedResidual_of_count_bound (μ k : Measure MatchingScene)
    hlam0 hlamHalf fs ft H b ψ t htR hC (hcount k)
  exact tendsto_integral_of_ae_continuousAt_of_sq_bound μ hlim htight
    (measurable_pastMarkedResidual lam fs ft H b ψ t)
    (hcuts.mono fun scene hs ↦ continuousAt_pastMarkedResidual lam fs ft H b ψ t hs.1 hs.2)
    (by positivity) (fun k ↦ (hsq k).1) (fun k ↦ (hsq k).2)

/-- The limiting residual is genuinely integrable. The same count-square bound also controls
its square in the limit, so the final zero integral is an ordinary finite expectation. -/
theorem integrable_pastMarkedResidual_limit_of_closed_count_sq_bound
    (μ : ℕ → ProbabilityMeasure MatchingScene) {ν : ProbabilityMeasure MatchingScene}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun k ↦ (μ k : Measure MatchingScene)))
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) {R : ℝ} (htR : (t:ℝ) ≤ R)
    (hcuts : ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.VacantCut 0 ∧ scene.VacantCut t)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcount : ∀ k, (∫⁻ scene, closedAggregateMass R scene ^ 2 ∂(μ k : Measure MatchingScene)) ≤ C) :
    Integrable (fun scene ↦ pastMarkedResidual lam fs ft H b ψ t scene ^ 2) (ν : Measure MatchingScene) ∧
      Integrable (pastMarkedResidual lam fs ft H b ψ t) (ν : Measure MatchingScene) := by
  let D := 2*(‖H‖*‖ψ‖)^2 * (C.toReal + 4*(t:ℝ)^2)
  have hm := measurable_pastMarkedResidual lam fs ft H b ψ t
  have hpow : Measurable (fun x : ℝ ↦ ENNReal.ofReal (x^2)) :=
    (measurable_id.pow_const 2).ennreal_ofReal
  have hcontSq : Continuous (fun x : ℝ ↦ x^2) := continuous_id.pow 2
  have hmap := tendsto_map_of_ae_continuousAt μ hlim htight hm
    (hcuts.mono fun scene hs ↦ continuousAt_pastMarkedResidual lam fs ft H b ψ t hs.1 hs.2)
  have hmoment : (∫⁻ x : ℝ, ENNReal.ofReal (x^2)
      ∂(ν.map hm.aemeasurable : Measure ℝ)) ≤ ENNReal.ofReal D := by
    apply lintegral_ofReal_le_of_probability_tendsto hmap hcontSq
    apply Eventually.of_forall
    intro k
    have hsq := integrable_sq_pastMarkedResidual_of_count_bound (μ k : Measure MatchingScene)
      hlam0 hlamHalf fs ft H b ψ t htR hC (hcount k)
    rw [ProbabilityMeasure.toMeasure_map,
      lintegral_map hpow hm,
      ← ofReal_integral_eq_lintegral_ofReal hsq.1
        (ae_of_all _ fun scene ↦ sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hsq.2
  rw [ProbabilityMeasure.toMeasure_map,
    lintegral_map hpow hm] at hmoment
  have hi : Integrable (fun scene ↦ pastMarkedResidual lam fs ft H b ψ t scene ^ 2)
      (ν : Measure MatchingScene) := by
    refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun scene ↦ sq_nonneg _)]
    exact hmoment.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  apply ((integrable_const (1:ℝ)).add hi).mono' hm.aestronglyMeasurable
  filter_upwards with scene
  simp only [Pi.add_apply, Real.norm_eq_abs]
  nlinarith [sq_nonneg (|pastMarkedResidual lam fs ft H b ψ t scene| - 1),
    sq_abs (pastMarkedResidual lam fs ft H b ψ t scene)]

/-- Vanishing original residual averages therefore give the actual limiting martingale-test
identity, without an assumed residual second moment or limiting martingale problem. -/
theorem integral_pastMarkedResidual_eq_zero_of_closed_count_sq_bound
    (μ : ℕ → ProbabilityMeasure MatchingScene) {ν : ProbabilityMeasure MatchingScene}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun k ↦ (μ k : Measure MatchingScene)))
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) {R : ℝ} (htR : (t:ℝ) ≤ R)
    (hcuts : ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.VacantCut 0 ∧ scene.VacantCut t)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcount : ∀ k, (∫⁻ scene, closedAggregateMass R scene ^ 2 ∂(μ k : Measure MatchingScene)) ≤ C)
    (hzero : Tendsto (fun k ↦ ∫ scene, pastMarkedResidual lam fs ft H b ψ t scene
      ∂(μ k : Measure MatchingScene)) atTop (𝓝 0)) :
    (∫ scene, pastMarkedResidual lam fs ft H b ψ t scene ∂(ν : Measure MatchingScene)) = 0 :=
  tendsto_nhds_unique
    (tendsto_integral_pastMarkedResidual_of_closed_count_sq_bound μ hlim htight
      hlam0 hlamHalf fs ft H b ψ t htR hcuts hC hcount) hzero

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.FiniteSample
open PointProcess
variable {n : ℕ} {lam : ℝ}

/-- The actual finite spatial residual is exactly the integral of the limiting observable
against the original finite optimizer root law, including the physical `B` shift. -/
theorem integral_pastMarkedResidual_rootedSceneLaw_eq
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) {a d : ℝ} (had : a ≤ d)
    (sample : FiniteSample n) :
    (∫ scene, MatchingScene.pastMarkedResidual lam fs ft H b ψ t scene
      ∂sample.rootedMatchingSceneLaw
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
        sample.euclideanOptimizer (B+a) (B+d)) =
      environmentPastMarkedSpatialResidual hlam0 hlamHalf eta B T fs ft H b ψ t a d sample := by
  let f := fun z : ℝ ↦ MatchingScene.pastMarkedResidual lam fs ft H b ψ t
    (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T z)
  rw [sample.integral_rootedMatchingSceneLaw _ _ (by linarith)
    _ (MatchingScene.measurable_pastMarkedResidual lam fs ft H b ψ t)]
  change (B+d-(B+a))⁻¹ * ∫ z in (B+a)..(B+d), f z = _
  rw [show B+d-(B+a) = d-a by ring]
  have hshift := intervalIntegral.integral_comp_add_left f B (a := a) (b := d)
  rw [← hshift, intervalIntegral.integral_of_le had]
  rfl

end OTSelector.FiniteSample
