import OTSelector.PointProcess.FiniteMatchingSceneLaw
import OTSelector.PointProcess.LocalConfigurationTightness

/-!
# Uniform local counting moments of fixed-sample scene laws

Each endpoint can be seen inside a radius-`A` root window for a set of roots of length `2 A`.
Thus source, target, and edge local counts have uniform first moments after spatial averaging,
independently of the original sample and its chosen assignment.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace OTSelector.PointProcess.FiniteMatching

variable {n : ℕ}

private theorem shifted_mem_interval (x z A : ℝ) :
    x - z ∈ Icc (-A) A ↔ z ∈ Icc (x - A) (x + A) := by
  simp only [mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem lintegral_rootWindow_indicator_sum (x : Fin n → ℝ) {A : ℝ} (_hA : 0 ≤ A) :
    (∫⁻ z : ℝ, ∑ i, (if x i - z ∈ Icc (-A) A then (1 : ℝ≥0∞) else 0)) =
      (n : ℝ≥0∞) * ENNReal.ofReal (2 * A) := by
  simp_rw [shifted_mem_interval]
  rw [lintegral_finsetSum]
  · have h (i : Fin n) :
        (∫⁻ z : ℝ, if z ∈ Icc (x i - A) (x i + A) then (1 : ℝ≥0∞) else 0) =
          ENNReal.ofReal (2 * A) := by
      have hi := lintegral_indicator_const (μ := (volume : Measure ℝ))
        (s := Icc (x i - A) (x i + A)) measurableSet_Icc (1 : ℝ≥0∞)
      simpa only [Set.indicator_apply, one_mul, Real.volume_Icc,
        show x i + A - (x i - A) = 2 * A by ring] using hi
    simp_rw [h]
    simp
  · intro i _
    exact measurable_const.ite measurableSet_Icc measurable_const

end OTSelector.PointProcess.FiniteMatching

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} {lam : ℝ} (sample : FiniteSample n) (graph : FeedbackGraph lam)

private theorem lintegral_rooted_endpoint_count_le
    (endpoint : Fin n → MatchingPoint) (a b : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    (∫⁻ z in Ioc a b,
      (∑ i, Measure.dirac ((endpoint i).1 - z, (endpoint i).2))
        (Icc (-A) A ×ˢ (univ : Set UnitMark))) ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (2 * A) := by
  have heq (z : ℝ) :
      (∑ i, Measure.dirac ((endpoint i).1 - z, (endpoint i).2))
        (Icc (-A) A ×ˢ (univ : Set UnitMark)) =
        ∑ i, (if (endpoint i).1 - z ∈ Icc (-A) A then (1 : ℝ≥0∞) else 0) := by
    rw [Measure.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Measure.dirac_apply' _ (measurableSet_Icc.prod MeasurableSet.univ)]
    simp only [Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true, Pi.one_apply]
  simp_rw [heq]
  exact (setLIntegral_le_lintegral _ _).trans_eq
    (FiniteMatching.lintegral_rootWindow_indicator_sum (fun i ↦ (endpoint i).1) hA)

theorem lintegral_rootedMatchingSceneLaw_source_count_le (σ : Assignment n)
    (a b : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    (∫⁻ scene, LocalConfiguration.countingMeasure scene.source
      (Icc (-A) A ×ˢ (univ : Set UnitMark))
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
        (ENNReal.ofReal (b - a))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (2 * A)) := by
  have hm : Measurable (fun scene : MatchingScene ↦ LocalConfiguration.countingMeasure scene.source
      (Icc (-A) A ×ˢ (univ : Set UnitMark))) :=
    (Measure.measurable_coe (measurableSet_Icc.prod MeasurableSet.univ)).comp
      (LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_source)
  rw [sample.lintegral_rootedMatchingSceneLaw graph σ a b _ hm]
  simp_rw [sample.countingMeasure_rootedMatchingScene_source graph]
  gcongr
  exact lintegral_rooted_endpoint_count_le
    (fun i ↦ (sample.sourceIntersection graph i, sample.sourceMark i)) a b hA

theorem lintegral_rootedMatchingSceneLaw_target_count_le (σ : Assignment n)
    (a b : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    (∫⁻ scene, LocalConfiguration.countingMeasure scene.target
      (Icc (-A) A ×ˢ (univ : Set UnitMark))
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
        (ENNReal.ofReal (b - a))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (2 * A)) := by
  have hm : Measurable (fun scene : MatchingScene ↦ LocalConfiguration.countingMeasure scene.target
      (Icc (-A) A ×ˢ (univ : Set UnitMark))) :=
    (Measure.measurable_coe (measurableSet_Icc.prod MeasurableSet.univ)).comp
      (LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_target)
  rw [sample.lintegral_rootedMatchingSceneLaw graph σ a b _ hm]
  simp_rw [sample.countingMeasure_rootedMatchingScene_target graph]
  gcongr
  exact lintegral_rooted_endpoint_count_le
    (fun i ↦ (sample.targetIntersection graph i, sample.targetMark i)) a b hA

private theorem pointBall_subset_window (A : ℝ) :
    Metric.ball matchingPointBase A ⊆ Icc (-A) A ×ˢ (univ : Set UnitMark) := by
  intro p hp
  have hp' : |p.1| < A := by
    have hh := (le_max_left (dist p.1 matchingPointBase.1)
      (dist p.2 matchingPointBase.2)).trans_lt hp
    simpa only [matchingPointBase, Real.dist_eq, sub_zero] using hh
  exact ⟨abs_le.mp hp'.le, mem_univ _⟩

theorem lintegral_rootedMatchingSceneLaw_source_ball_le (σ : Assignment n)
    (a b : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    (∫⁻ scene, LocalConfiguration.countingMeasure scene.source (Metric.ball matchingPointBase A)
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
        (ENNReal.ofReal (b - a))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (2 * A)) :=
  (lintegral_mono (fun _ ↦ measure_mono (pointBall_subset_window A))).trans
    (sample.lintegral_rootedMatchingSceneLaw_source_count_le graph σ a b hA)

theorem lintegral_rootedMatchingSceneLaw_target_ball_le (σ : Assignment n)
    (a b : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    (∫⁻ scene, LocalConfiguration.countingMeasure scene.target (Metric.ball matchingPointBase A)
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
        (ENNReal.ofReal (b - a))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (2 * A)) :=
  (lintegral_mono (fun _ ↦ measure_mono (pointBall_subset_window A))).trans
    (sample.lintegral_rootedMatchingSceneLaw_target_count_le graph σ a b hA)

/-- Every observed edge contributes one distinct finite source label, with its multiplicity. -/
theorem countingMeasure_rootedMatchingScene_edges_ball_le_source_window
    (σ : Assignment n) (z A : ℝ) :
    LocalConfiguration.countingMeasure (sample.rootedMatchingScene graph σ z).edges
        (Metric.ball (matchingPointBase, matchingPointBase) A) ≤
      LocalConfiguration.countingMeasure (sample.rootedMatchingScene graph σ z).source
        (Icc (-A) A ×ˢ (univ : Set UnitMark)) := by
  classical
  rw [sample.countingMeasure_rootedMatchingScene_edges graph,
    sample.countingMeasure_rootedMatchingScene_source graph]
  simp only [Measure.finsetSum_apply]
  apply Finset.sum_le_sum
  intro i _
  rw [Measure.dirac_apply' _ Metric.isOpen_ball.measurableSet,
    Measure.dirac_apply' _ (measurableSet_Icc.prod MeasurableSet.univ)]
  simp only [Set.indicator_apply, Pi.one_apply]
  change (if (sample.rootedSourcePoint graph z i,
      sample.rootedTargetPoint graph z (σ i)) ∈
        Metric.ball (matchingPointBase, matchingPointBase) A then (1 : ℝ≥0∞) else 0) ≤
      if sample.rootedSourcePoint graph z i ∈ Icc (-A) A ×ˢ (univ : Set UnitMark)
        then 1 else 0
  by_cases hp : (sample.rootedSourcePoint graph z i,
      sample.rootedTargetPoint graph z (σ i)) ∈
        Metric.ball (matchingPointBase, matchingPointBase) A
  · have hp' : sample.rootedSourcePoint graph z i ∈ Metric.ball matchingPointBase A :=
      (le_max_left (dist (sample.rootedSourcePoint graph z i) matchingPointBase)
        (dist (sample.rootedTargetPoint graph z (σ i)) matchingPointBase)).trans_lt hp
    have hs := pointBall_subset_window A hp'
    simp [hp, hs]
  · simp [hp]

theorem lintegral_rootedMatchingSceneLaw_edges_ball_le (σ : Assignment n)
    (a b : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    (∫⁻ scene, LocalConfiguration.countingMeasure scene.edges
      (Metric.ball (matchingPointBase, matchingPointBase) A)
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
        (ENNReal.ofReal (b - a))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (2 * A)) := by
  have he : Measurable (fun scene : MatchingScene ↦ LocalConfiguration.countingMeasure scene.edges
      (Metric.ball (matchingPointBase, matchingPointBase) A)) :=
    (Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp
      (LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_edges)
  have hs : Measurable (fun scene : MatchingScene ↦ LocalConfiguration.countingMeasure scene.source
      (Icc (-A) A ×ˢ (univ : Set UnitMark))) :=
    (Measure.measurable_coe (measurableSet_Icc.prod MeasurableSet.univ)).comp
      (LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_source)
  apply le_trans ?_ (sample.lintegral_rootedMatchingSceneLaw_source_count_le graph σ a b hA)
  rw [sample.lintegral_rootedMatchingSceneLaw graph σ a b _ he,
    sample.lintegral_rootedMatchingSceneLaw graph σ a b _ hs]
  gcongr with z
  exact sample.countingMeasure_rootedMatchingScene_edges_ball_le_source_window graph σ z A

end OTSelector.FiniteSample
