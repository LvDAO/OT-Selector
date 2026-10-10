import OTSelector.Feedback.FeedbackMarkedEnvironmentResidual

/-! # Spatial averages of the original finite environment compensator -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal Topology
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.FiniteSample
open PointProcess CountingProcess
variable {n : ℕ} {lam : ℝ}

private theorem measurable_environment_reroot_fixed (e : FeedbackEnvironment) :
    Measurable (fun z : ℝ ↦ FeedbackEnvironment.reroot z e) :=
  FeedbackEnvironment.measurable_uncurry_reroot.comp
    (f := fun z : ℝ ↦ (z,e)) (measurable_id.prodMk measurable_const)

/-- The actual environment viewed from a varying root is measurable even for a fixed arbitrary
assignment; no measurable-choice property of the optimizer is needed for this spatial section. -/
theorem measurable_feedbackEnvironment_rootedMatchingScene
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n) :
    Measurable (fun z ↦ Matching.feedbackSceneEnvironment (sample.rootedMatchingScene graph σ z)) := by
  let e := Matching.feedbackSceneEnvironment (sample.rootedMatchingScene graph σ 0)
  have h : Measurable (fun z : ℝ ↦ FeedbackEnvironment.reroot z e) :=
    measurable_environment_reroot_fixed e
  convert h using 1
  funext z
  have heq := congrArg Matching.feedbackSceneEnvironment (sample.reroot_rootedMatchingScene graph σ 0 z)
  change FeedbackEnvironment.reroot z e = Matching.feedbackSceneEnvironment
    (sample.rootedMatchingScene graph σ (0+z)) at heq
  simpa only [zero_add] using heq.symm

/-- The true compensator of a finite rooted scene is a measurable function of its physical root. -/
theorem measurable_environmentMarkedCompensator_rootedScene
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    (b : Bool) (ψ : UnitMark → ℝ) (t : ℝ≥0) :
    Measurable (fun z ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment (sample.rootedMatchingScene graph σ z))) := by
  have hm : Measurable (fun z ↦ LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment
        (sample.rootedMatchingScene graph σ z))) b ψ t) := by
    cases b
    · change Measurable (fun z ↦ ∫ p in LocalConfiguration.spatialIoc 0 (t:ℝ), ψ p.2
        ∂LocalConfiguration.countingMeasure (LocalConfiguration.ofTuple _ (sample.rootedTargetPoint graph z)))
      simp_rw [LocalConfiguration.markedWindow_ofTuple]
      apply Finset.measurable_sum
      intro i _
      change Measurable (fun z : ℝ ↦ if 0 < sample.targetIntersection graph i-z ∧
        sample.targetIntersection graph i-z ≤ (t:ℝ) then ψ (sample.targetMark i) else 0)
      exact Measurable.ite ((measurableSet_lt measurable_const (measurable_const.sub measurable_id)).inter
        (measurableSet_le (measurable_const.sub measurable_id) measurable_const)) measurable_const measurable_const
    · change Measurable (fun z ↦ ∫ p in LocalConfiguration.spatialIoc 0 (t:ℝ), ψ p.2
        ∂LocalConfiguration.countingMeasure (LocalConfiguration.ofTuple _ (sample.rootedSourcePoint graph z)))
      simp_rw [LocalConfiguration.markedWindow_ofTuple]
      apply Finset.measurable_sum
      intro i _
      change Measurable (fun z : ℝ ↦ if 0 < sample.sourceIntersection graph i-z ∧
        sample.sourceIntersection graph i-z ≤ (t:ℝ) then ψ (sample.sourceMark i) else 0)
      exact Measurable.ite ((measurableSet_lt measurable_const (measurable_const.sub measurable_id)).inter
        (measurableSet_le (measurable_const.sub measurable_id) measurable_const)) measurable_const measurable_const
  exact hm.sub ((Limit.measurable_integral_feedbackEnvironmentMarkRate_current lam b ψ t).comp
    (sample.measurable_feedbackEnvironment_rootedMatchingScene graph σ))

/-- The spatial residual used by a selected original finite sample. Roots are physical `B+x`,
with `x` an elapsed coordinate and `G x` a bounded past observation. -/
noncomputable def environmentMarkedSpatialAverage
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    (b : Bool) (ψ : UnitMark → ℝ) (G : ℝ≥0 → FiniteSample n → ℝ)
    (t : ℝ≥0) (a d : ℝ) (sample : FiniteSample n) : ℝ :=
  (d-a)⁻¹ * ∫ x in Ioc a d, G x.toNNReal sample *
    Limit.feedbackEnvironmentMarkedCompensator lam b ψ t (Matching.feedbackSceneEnvironment
      (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+x)))

/-- The same average of the already established true stopped marked martingale. -/
noncomputable def finiteMarkedSpatialAverage
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    (b : Bool) (ψ : UnitMark → ℝ) (G : ℝ≥0 → FiniteSample n → ℝ)
    (t : ℝ≥0) (a d : ℝ) (sample : FiniteSample n) : ℝ :=
  (d-a)⁻¹ * ∫ x in Ioc a d, Probability.spatialWindowResidual
    (safeColorSpatialMarkedCompensator hlam0 hlamHalf eta B T b ψ) G t x sample

private theorem norm_spatialAverage_sub_le
    {X Y : ℝ → ℝ} (hXm : Measurable X) (hYm : Measurable Y)
    {a d K E : ℝ} (had : a < d) (hY : ∀x, ‖Y x‖ ≤ K)
    (hE : ∀x ∈ Ioc a d, ‖X x-Y x‖ ≤ E) :
    ‖(d-a)⁻¹*(∫x in Ioc a d, X x) - (d-a)⁻¹*(∫x in Ioc a d, Y x)‖ ≤ E := by
  have hiY : IntegrableOn Y (Ioc a d) volume :=
    (integrableOn_const (C := K) (measure_Ioc_lt_top.ne)).mono' hYm.aestronglyMeasurable
      (ae_of_all _ hY)
  have hiD : IntegrableOn (fun x ↦ X x-Y x) (Ioc a d) volume :=
    (integrableOn_const (C := E) (measure_Ioc_lt_top.ne)).mono'
      (hXm.sub hYm).aestronglyMeasurable ((ae_restrict_mem measurableSet_Ioc).mono hE)
  have hiX : IntegrableOn X (Ioc a d) volume := by
    exact (hiD.add hiY).congr (ae_of_all _ fun x ↦ sub_add_cancel (X x) (Y x))
  rw [← mul_sub, ← integral_sub hiX hiY, norm_mul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sub_pos.mpr had))]
  calc
    _ ≤ (d-a)⁻¹ * (E*(d-a)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr had.le))
      simpa only [Real.volume_real_Ioc, max_eq_left (sub_nonneg.mpr had.le)] using
        norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hE
    _ = E := by field_simp [ne_of_gt (sub_pos.mpr had)]

/-- On the same original survival and VC event, spatial averaging preserves the small true
drift error. There is no fixed-eta approximation of the limiting rate. -/
theorem norm_environmentMarkedSpatialAverage_sub_finite_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (hn : 4 ≤ n)
    {eta eps B C A : ℝ} (heps : 0 ≤ eps) (hepsSmall : eps*(2+lam) ≤ lam) (hB : 0 < B)
    (T t : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample ∈ feedbackA1GoodEvent n lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    {a d : ℝ} (ha : 0 ≤ a) (had : a < d) (hd : d+(t:ℝ) < T)
    (hsqrt : 4*(33280:ℝ)^2*Real.log n ≤ eps^2*(13*B/16))
    (hlinear : 2*(33280:ℝ)*Real.log n ≤ eps*(13*B/16))
    (b : Bool) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hC : 0 ≤ C) (hbound : ∀v, ‖ψ v‖ ≤ C)
    (G : ℝ≥0 → FiniteSample n → ℝ) (hGm : Measurable (Function.uncurry G))
    (hA : 0 ≤ A) (hGb : ∀u ω, ‖G u ω‖ ≤ A) :
    ‖environmentMarkedSpatialAverage hlam0 hlamHalf eta B T b ψ G t a d sample -
      finiteMarkedSpatialAverage hlam0 hlamHalf eta B T b ψ G t a d sample‖ ≤
        2*A*C*eps*(t:ℝ) := by
  let M := safeColorSpatialMarkedCompensator (n := n) hlam0 hlamHalf eta B T b ψ
  have hn0 : 0 < n := by omega
  have hMm : Measurable (Function.uncurry M) := by
    cases b
    · exact measurable_uncurry_safeTargetSpatialMarkedCompensator hlam0 hlamHalf hn0 hB eta B 0 T ψ hψ hC hbound
    · exact measurable_uncurry_safeSourceSpatialMarkedCompensator hlam0 hlamHalf hn0 hB eta B 0 T ψ hψ hC hbound
  let D := (n:ℝ)*C+C*feedbackBulkRateCap n B*T
  have hMb : ∀u ω, ‖M u ω‖ ≤ D := by
    cases b
    · exact norm_safeTargetSpatialMarkedCompensator_le hlam0 hlamHalf hn0 hB eta B 0 T ψ hψ hC hbound
    · exact norm_safeSourceSpatialMarkedCompensator_le hlam0 hlamHalf hn0 hB eta B 0 T ψ hψ hC hbound
  have hmG : Measurable (fun x : ℝ ↦ G x.toNNReal sample) :=
    hGm.comp (measurable_real_toNNReal.prodMk measurable_const)
  have hmM : Measurable (fun x : ℝ ↦ M x.toNNReal sample) :=
    hMm.comp (measurable_real_toNNReal.prodMk measurable_const)
  have hmMt : Measurable (fun x : ℝ ↦ M (x.toNNReal+t) sample) :=
    hMm.comp ((measurable_real_toNNReal.add_const t).prodMk measurable_const)
  have hYm : Measurable (fun x ↦ Probability.spatialWindowResidual M G t x sample) :=
    Measurable.ite (measurableSet_le measurable_const measurable_id)
      (hmG.mul (hmMt.sub hmM)) measurable_const
  have hYb (x : ℝ) : ‖Probability.spatialWindowResidual M G t x sample‖ ≤ A*(2*D) := by
    unfold Probability.spatialWindowResidual Probability.pastWindowResidual
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (hGb _ _) ((norm_sub_le _ _).trans (by linarith [hMb (x.toNNReal+t) sample, hMb x.toNNReal sample]))
        (norm_nonneg _) hA
    · simp only [norm_zero]
      dsimp [D]
      have hc := feedbackBulkRateCap_nonneg n B
      positivity
  have hXm : Measurable (fun x : ℝ ↦ G x.toNNReal sample *
      Limit.feedbackEnvironmentMarkedCompensator lam b ψ t (Matching.feedbackSceneEnvironment
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+x)))) :=
    hmG.mul ((sample.measurable_environmentMarkedCompensator_rootedScene
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) sample.euclideanOptimizer b ψ t).comp
      (measurable_const.add measurable_id))
  apply norm_spatialAverage_sub_le hXm hYm had hYb
  intro x hx
  have hx0 : 0 ≤ x := ha.trans hx.1.le
  have hxt : x.toNNReal+t < T := by
    exact_mod_cast (show (x.toNNReal:ℝ)+(t:ℝ) < (T:ℝ) by rw [Real.coe_toNNReal x hx0]; linarith [hx.2])
  have herr := norm_environmentMarkedCompensator_stoppedScene_sub_martingale_increment_le
    hlam0 hlamHalf hn heps hepsSmall hB T x.toNNReal t sample hgood hstop hxt
    hsqrt hlinear b ψ hψ hC hbound
  rw [Real.coe_toNNReal x hx0] at herr
  simp only [Probability.spatialWindowResidual, ite_eq_left hx0, Probability.pastWindowResidual]
  rw [← mul_sub, norm_mul]
  exact (mul_le_mul (hGb _ _) herr (norm_nonneg _) hA).trans_eq (by ring)

end OTSelector.FiniteSample
