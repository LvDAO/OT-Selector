import OTSelector.PointProcess.MatchingSceneReroot
import OTSelector.PointProcess.FiniteMatchingTail

/-!
# Uniform-root laws of concrete finite matching scenes

These laws average a fixed original sample over its physical observation interval. They are
the laws used after choosing samples with bounded optimizer energy; no conditioning of the
finite feedback process is involved.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

set_option maxHeartbeats 800000

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} {lam : ℝ} (sample : FiniteSample n) (graph : FeedbackGraph lam)

/-- Every fixed finite sample gives a measurable scene as its spatial root varies. -/
theorem measurable_rootedMatchingScene (σ : Assignment n) :
    Measurable (sample.rootedMatchingScene graph σ) := by
  have h := MatchingScene.measurable_uncurry_reroot.comp
    (measurable_id.prodMk (measurable_const (a := sample.rootedMatchingScene graph σ 0)))
  simpa only [Function.comp_def, reroot_rootedMatchingScene, zero_add, id_eq] using h

/-- The actual rooted law of a fixed finite assignment, with the original sampled marks. -/
noncomputable def rootedMatchingSceneLaw (σ : Assignment n) (a b : ℝ) : Measure MatchingScene :=
  (Probability.spatialRootLaw a b).map (sample.rootedMatchingScene graph σ)

theorem rootedMatchingSceneLaw_isProbability (σ : Assignment n) {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (sample.rootedMatchingSceneLaw graph σ a b) := by
  let := Probability.spatialRootLaw_isProbability hab
  exact Measure.isProbabilityMeasure_map (sample.measurable_rootedMatchingScene graph σ).aemeasurable

theorem integral_rootedMatchingSceneLaw (σ : Assignment n) {a b : ℝ} (hab : a ≤ b)
    (f : MatchingScene → ℝ) (hf : Measurable f) :
    (∫ scene, f scene ∂sample.rootedMatchingSceneLaw graph σ a b) =
      (b - a)⁻¹ * ∫ z in a..b, f (sample.rootedMatchingScene graph σ z) := by
  rw [rootedMatchingSceneLaw,
    integral_map (sample.measurable_rootedMatchingScene graph σ).aemeasurable
      hf.aestronglyMeasurable, Probability.integral_spatialRootLaw hab]

theorem lintegral_rootedMatchingSceneLaw (σ : Assignment n) (a b : ℝ)
    (f : MatchingScene → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ scene, f scene ∂sample.rootedMatchingSceneLaw graph σ a b) =
      (ENNReal.ofReal (b - a))⁻¹ *
        ∫⁻ z in Ioc a b, f (sample.rootedMatchingScene graph σ z) := by
  rw [rootedMatchingSceneLaw, lintegral_map hf (sample.measurable_rootedMatchingScene graph σ),
    Probability.spatialRootLaw, ProbabilityTheory.cond, lintegral_smul_measure, Real.volume_Ioc]
  rfl

/-- Spatial stationarity has an explicit vanishing boundary error already for each fixed sample. -/
theorem norm_integral_rootedMatchingSceneLaw_reroot_sub_le (σ : Assignment n)
    {a b C : ℝ} (hab : a < b) (f : MatchingScene → ℝ) (hf : Measurable f)
    (hbound : ∀ scene, ‖f scene‖ ≤ C) (t : ℝ) :
    ‖(∫ scene, f (MatchingScene.reroot t scene)
        ∂sample.rootedMatchingSceneLaw graph σ a b) -
      ∫ scene, f scene ∂sample.rootedMatchingSceneLaw graph σ a b‖ ≤
        2 * C * |t| / (b - a) := by
  have hr : Measurable (MatchingScene.reroot t) :=
    (MatchingScene.rerootMeasurableEquiv t).measurable
  have hfr : Measurable (fun scene ↦ f (MatchingScene.reroot t scene)) := hf.comp hr
  rw [rootedMatchingSceneLaw,
    integral_map (sample.measurable_rootedMatchingScene graph σ).aemeasurable
      hfr.aestronglyMeasurable,
    integral_map (sample.measurable_rootedMatchingScene graph σ).aemeasurable
      hf.aestronglyMeasurable]
  simp_rw [sample.reroot_rootedMatchingScene graph]
  exact Probability.norm_integral_spatialRootLaw_shift_sub_le
    (hf.comp (sample.measurable_rootedMatchingScene graph σ))
    (fun z ↦ hbound _) hab t

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.FiniteMatching

variable {n : ℕ}

/-- Root-current occupation is controlled by the actual sum of edge lengths. -/
theorem setIntegral_abs_assignmentCrossingCurrent_le (source target : Fin n → ℝ)
    (σ : Assignment n) (I : Set ℝ) :
    (∫ z in I, |(assignmentCrossingCurrent source target σ z : ℝ)|) ≤
      ∑ i, |target (σ i) - source i| := by
  have hdom (z : ℝ) : |(assignmentCrossingCurrent source target σ z : ℝ)| ≤
      ∑ i, |(crossingSign (source i) (target (σ i)) z : ℝ)| := by
    simp only [assignmentCrossingCurrent, Int.cast_sum]
    exact Finset.abs_sum_le_sum_abs _ _
  have hi : Integrable (fun z : ℝ ↦ ∑ i, |(crossingSign (source i) (target (σ i)) z : ℝ)|) :=
    integrable_finsetSum _ fun i _ ↦ integrable_abs_crossingSign _ _
  have hmeas : Measurable (fun z : ℝ ↦ |(assignmentCrossingCurrent source target σ z : ℝ)|) := by
    apply (measurable_of_countable (fun k : ℤ ↦ |(k : ℝ)|)).comp
    apply Finset.measurable_sum
    intro i _
    exact (measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const).sub
      (measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const)
  have hc : Integrable (fun z : ℝ ↦ |(assignmentCrossingCurrent source target σ z : ℝ)|) := by
    apply hi.mono' hmeas.aestronglyMeasurable
    filter_upwards with z
    simpa only [Real.norm_eq_abs, abs_abs] using hdom z
  calc
    _ ≤ ∫ z, |(assignmentCrossingCurrent source target σ z : ℝ)| :=
      setIntegral_le_integral hc (ae_of_all _ fun z ↦ abs_nonneg _)
    _ ≤ ∫ z, ∑ i, |(crossingSign (source i) (target (σ i)) z : ℝ)| :=
      integral_mono hc hi hdom
    _ = ∑ i, |target (σ i) - source i| := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_abs_crossingSign _ _)]
      simp_rw [integral_abs_crossingSign]

/-- A linear bound on squared assignment energy gives linear root-current occupation. -/
theorem setIntegral_abs_assignmentCrossingCurrent_le_energy (source target : Fin n → ℝ)
    (σ : Assignment n) (I : Set ℝ) :
    (∫ z in I, |(assignmentCrossingCurrent source target σ z : ℝ)|) ≤
      ((n : ℝ) + ∑ i, (target (σ i) - source i) ^ 2) / 2 := by
  apply (setIntegral_abs_assignmentCrossingCurrent_le source target σ I).trans
  have h (i : Fin n) : |target (σ i) - source i| ≤
      (1 + (target (σ i) - source i) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|target (σ i) - source i| - 1),
      sq_abs (target (σ i) - source i)]
  calc
    _ ≤ ∑ i, (1 + (target (σ i) - source i) ^ 2) / 2 :=
      Finset.sum_le_sum (fun i _ ↦ h i)
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]; simp

end OTSelector.PointProcess.FiniteMatching
