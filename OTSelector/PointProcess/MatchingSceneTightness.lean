import OTSelector.PointProcess.FiniteMatchingSceneCounts
import OTSelector.PointProcess.MatchingSceneTransportFlux

/-!
# Tightness of the actual fixed-sample matching laws

Local endpoint counts, squared assignment energy and the graph Lipschitz bound control all
four scene coordinates. In particular energy already controls the root-current coordinate.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators Classical ENNReal NNReal

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.FeedbackPath

theorem isTightMeasureSet_of_lipschitz_and_current_moment
    (S : Set (Measure FeedbackPath)) (L : ℝ≥0) (B : ℝ≥0∞) (hB : B ≠ ∞)
    (hlip : ∀ μ ∈ S, ∀ᵐ p ∂μ, LipschitzWith L p.graphHeight)
    (hmoment : ∀ μ ∈ S, ∫⁻ p, (p.rootCurrent.natAbs : ℝ≥0∞) ∂μ ≤ B) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hεtop : ε = ∞
  · exact ⟨∅, isCompact_empty, by simp [hεtop]⟩
  obtain ⟨J, hJ⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hB hε.ne')
  have hratio : B / ((J + 1 : ℕ) : ℝ≥0∞) ≤ ε := by
    apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
    rw [mul_comm]
    apply (ENNReal.div_le_iff hε.ne' hεtop).mp
    exact hJ.le.trans (by exact_mod_cast Nat.le_succ J)
  let K : Set FeedbackPath := coordinates ⁻¹'
    (GraphHeight.lipschitzSet L ×ˢ Icc (-(J : ℤ)) J)
  have hK : IsCompact K := isClosedEmbedding_coordinates.isCompact_preimage
    ((GraphHeight.isCompact_lipschitzSet L).prod (Set.finite_Icc _ _).isCompact)
  refine ⟨K, hK, fun μ hμ ↦ ?_⟩
  have hsub : Kᶜ ≤ᵐ[μ] {p | J < p.rootCurrent.natAbs} := by
    filter_upwards [hlip μ hμ] with p hp hnot
    apply lt_of_not_ge
    intro hle
    apply hnot
    refine ⟨hp, abs_le.mp ?_⟩
    change |p.rootCurrent| ≤ (J : ℤ)
    rw [← Int.natCast_natAbs]
    exact_mod_cast hle
  have hmeas : Measurable (fun p : FeedbackPath ↦ (p.rootCurrent.natAbs : ℝ≥0∞)) :=
    (measurable_of_countable (fun k : ℤ ↦ (k.natAbs : ℝ≥0∞))).comp
      continuous_rootCurrent.measurable
  have hset : {p : FeedbackPath | J < p.rootCurrent.natAbs} =
      {p | ((J + 1 : ℕ) : ℝ≥0∞) ≤ (p.rootCurrent.natAbs : ℝ≥0∞)} := by
    ext p
    simp only [mem_ofPred_eq, Nat.cast_le]
    omega
  apply (measure_mono_ae hsub).trans
  rw [hset]
  exact (meas_ge_le_lintegral_div hmeas.aemeasurable (by simp) (by simp)).trans
    ((ENNReal.div_le_div_right (hmoment μ hμ) _).trans hratio)

end OTSelector.PointProcess.FeedbackPath

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance tightnessPointTopology :
    TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase
noncomputable local instance tightnessEdgeTopology :
    TopologicalSpace (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueTopology (matchingPointBase, matchingPointBase)
local instance : BorelSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueBorelSpace
local instance : BorelSpace (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueBorelSpace
local instance : T2Space (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueT2Space
local instance : T2Space (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueT2Space

/-- Tightness of the four actual coordinate marginals gives tightness of scene laws. -/
theorem isTightMeasureSet_of_coordinates (S : Set (Measure MatchingScene))
    (hs : IsTightMeasureSet (Measure.map source '' S))
    (ht : IsTightMeasureSet (Measure.map target '' S))
    (he : IsTightMeasureSet (Measure.map edges '' S))
    (hp : IsTightMeasureSet (Measure.map path '' S)) : IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hs ht he hp ⊢
  intro ε hε
  have hδ : 0 < ε / 2 / 2 := ENNReal.div_pos
    (ENNReal.div_pos hε.ne' (by norm_num)).ne' (by norm_num)
  obtain ⟨Ks, hKs, hbs⟩ := hs _ hδ
  obtain ⟨Kt, hKt, hbt⟩ := ht _ hδ
  obtain ⟨Ke, hKe, hbe⟩ := he _ hδ
  obtain ⟨Kp, hKp, hbp⟩ := hp _ hδ
  let K : Set MatchingScene := {scene | scene.source ∈ Ks ∧ scene.target ∈ Kt ∧
    scene.edges ∈ Ke ∧ scene.path ∈ Kp}
  refine ⟨K, isCompact_coordinates_preimage hKs hKt hKe hKp, fun μ hμ ↦ ?_⟩
  have hsub : Kᶜ ⊆ (source ⁻¹' Ksᶜ ∪ target ⁻¹' Ktᶜ) ∪
      (edges ⁻¹' Keᶜ ∪ path ⁻¹' Kpᶜ) := by
    intro scene hscene
    simp only [K, mem_compl_iff, mem_ofPred_eq] at hscene
    simp only [mem_union, mem_preimage, mem_compl_iff]
    tauto
  have hmap {X : Type} [MeasurableSpace X] (f : MatchingScene → X)
      (hf : Measurable f) {A : Set X} (hA : MeasurableSet A)
      (hb : ∀ ν ∈ Measure.map f '' S, ν A ≤ ε / 2 / 2) :
      μ (f ⁻¹' A) ≤ ε / 2 / 2 := by
    rw [← Measure.map_apply hf hA]
    exact hb _ (mem_image_of_mem _ hμ)
  calc
    μ Kᶜ ≤ μ ((source ⁻¹' Ksᶜ ∪ target ⁻¹' Ktᶜ) ∪
        (edges ⁻¹' Keᶜ ∪ path ⁻¹' Kpᶜ)) := measure_mono hsub
    _ ≤ (μ (source ⁻¹' Ksᶜ) + μ (target ⁻¹' Ktᶜ)) +
        (μ (edges ⁻¹' Keᶜ) + μ (path ⁻¹' Kpᶜ)) :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ ≤ (ε / 2 / 2 + ε / 2 / 2) + (ε / 2 / 2 + ε / 2 / 2) := by
      have hpath : μ (path ⁻¹' Kpᶜ) ≤ ε / 2 / 2 := by
        rw [← Measure.map_apply measurable_path hKp.measurableSet.compl]
        exact hbp _ (mem_image_of_mem _ hμ)
      exact
      add_le_add
        (add_le_add (hmap source measurable_source hKs.measurableSet.compl hbs)
          (hmap target measurable_target hKt.measurableSet.compl hbt))
        (add_le_add (hmap edges measurable_edges hKe.measurableSet.compl hbe)
          hpath)
    _ = ε := by simp only [ENNReal.add_halves]

/-- Uniform local counting moments, a common graph bound and a root-current moment suffice. -/
theorem isTightMeasureSet_of_moments {ι : Type*} (μ : ι → Measure MatchingScene)
    (b : ℕ → ℝ≥0∞) (hb : ∀ k, b k ≠ ∞) (L : ℝ≥0) (B : ℝ≥0∞) (hB : B ≠ ∞)
    (hs : ∀ i k, ∫⁻ scene, LocalConfiguration.countingMeasure scene.source
      (Metric.ball matchingPointBase ((k + 1 : ℕ) : ℝ)) ∂μ i ≤ b k)
    (ht : ∀ i k, ∫⁻ scene, LocalConfiguration.countingMeasure scene.target
      (Metric.ball matchingPointBase ((k + 1 : ℕ) : ℝ)) ∂μ i ≤ b k)
    (he : ∀ i k, ∫⁻ scene, LocalConfiguration.countingMeasure scene.edges
      (Metric.ball (matchingPointBase, matchingPointBase) ((k + 1 : ℕ) : ℝ)) ∂μ i ≤ b k)
    (hlip : ∀ i, ∀ᵐ scene ∂μ i, LipschitzWith L scene.path.graphHeight)
    (hcurrent : ∀ i, ∫⁻ scene, (scene.path.rootCurrent.natAbs : ℝ≥0∞) ∂μ i ≤ B) :
    IsTightMeasureSet (range μ) := by
  apply isTightMeasureSet_of_coordinates
  · simpa only [range_comp'] using
      LocalConfiguration.isTightMeasureSet_map_of_lintegral_countingMeasure_ball_le
        μ (fun _ ↦ source) (fun _ ↦ measurable_source) b hb hs
  · simpa only [range_comp'] using
      LocalConfiguration.isTightMeasureSet_map_of_lintegral_countingMeasure_ball_le
        μ (fun _ ↦ target) (fun _ ↦ measurable_target) b hb ht
  · simpa only [range_comp'] using
      LocalConfiguration.isTightMeasureSet_map_of_lintegral_countingMeasure_ball_le
        μ (fun _ ↦ edges) (fun _ ↦ measurable_edges) b hb he
  · apply FeedbackPath.isTightMeasureSet_of_lipschitz_and_current_moment _ L B hB
    · rintro _ ⟨ν, ⟨i, rfl⟩, rfl⟩
      exact (ae_map_iff measurable_path.aemeasurable
        ((GraphHeight.isClosed_lipschitzSet L).measurableSet.preimage
          FeedbackPath.continuous_graphHeight.measurable)).mpr (hlip i)
    · rintro _ ⟨ν, ⟨i, rfl⟩, rfl⟩
      rw [lintegral_map]
      · exact hcurrent i
      · exact (measurable_of_countable (fun k : ℤ ↦ (k.natAbs : ℝ≥0∞))).comp
          FeedbackPath.continuous_rootCurrent.measurable
      · exact measurable_path

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.FiniteSample

open PointProcess

variable {n : ℕ} {lam : ℝ}

/-- The actual root-current first moment is bounded directly by squared assignment energy. -/
theorem lintegral_rootedMatchingSceneLaw_current_le (sample : FiniteSample n)
    (graph : FeedbackGraph lam) (σ : Assignment n) {a b : ℝ} (hab : a < b) :
    (∫⁻ scene, (scene.path.rootCurrent.natAbs : ℝ≥0∞)
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
      ENNReal.ofReal ((b - a)⁻¹ * (((n : ℝ) + ∑ i,
        (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2) / 2)) := by
  have hc : Measurable (fun scene : MatchingScene ↦ |(scene.path.rootCurrent : ℝ)|) :=
    (measurable_of_countable (fun k : ℤ ↦ |(k : ℝ)|)).comp
      MatchingScene.continuous_rootCurrent.measurable
  have hcast (scene : MatchingScene) : (scene.path.rootCurrent.natAbs : ℝ≥0∞) =
      ENNReal.ofReal |(scene.path.rootCurrent : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast, ENNReal.ofReal_natCast]
  simp_rw [hcast]
  have hi : Integrable (fun z ↦ ∑ i, |(crossingSign (sample.sourceIntersection graph i)
      (sample.targetIntersection graph (σ i)) z : ℝ)|) :=
    integrable_finsetSum _ (fun i _ ↦ FiniteMatching.integrable_abs_crossingSign _ _)
  have hd (z : ℝ) : |((sample.rootedMatchingScene graph σ z).path.rootCurrent : ℝ)| ≤
      ∑ i, |(crossingSign (sample.sourceIntersection graph i)
        (sample.targetIntersection graph (σ i)) z : ℝ)| := by
    rw [sample.rootedMatchingScene_rootCurrent_eq_crossingCurrent graph σ z]
    simp only [assignmentCrossingCurrent, Int.cast_sum]
    exact Finset.abs_sum_le_sum_abs _ _
  apply (sample.lintegral_rootedMatchingSceneLaw_le_of_integrable_domination graph σ hab
    hc (fun _ ↦ abs_nonneg _) hi hd).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
  rw [integral_finsetSum _ (fun i _ ↦ FiniteMatching.integrable_abs_crossingSign _ _)]
  simp_rw [FiniteMatching.integral_abs_crossingSign]
  have h (i : Fin n) : |sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i| ≤
      (1 + (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|sample.targetIntersection graph (σ i) -
      sample.sourceIntersection graph i| - 1),
      sq_abs (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i)]
  calc
    _ ≤ ∑ i, (1 + (sample.targetIntersection graph (σ i) -
        sample.sourceIntersection graph i) ^ 2) / 2 := Finset.sum_le_sum (fun i _ ↦ h i)
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]; simp

/-- Normalize a finite population count by its actual rooting-window length. -/
theorem root_count_factor_le {n : ℕ} {a b A ρ : ℝ}
    (hab : a < b) (hA : 0 ≤ A) (hn : (n : ℝ) ≤ ρ * (b - a)) :
    (ENNReal.ofReal (b - a))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (2 * A)) ≤
      ENNReal.ofReal (2 * A * ρ) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hab),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_nonneg.mpr hab.le))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = 2 * A * ((n : ℝ) / (b - a)) := by ring
    _ ≤ 2 * A * ρ := mul_le_mul_of_nonneg_left
      ((div_le_iff₀ (sub_pos.mpr hab)).mpr hn) (by positivity)

/-- Tightness is obtained for actual fixed-sample root laws from the two deterministic bounds
that are available on the original high-probability good samples. -/
theorem isTightMeasureSet_rootedMatchingSceneLaw {ι : Type*} {N : ι → ℕ}
    (sample : ∀ i, FiniteSample (N i)) (graph : ι → FeedbackGraph lam)
    (σ : ∀ i, Assignment (N i)) (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    {ρ C : ℝ} (hcount : ∀ i, (N i : ℝ) ≤ ρ * (b i - a i))
    (henergy : ∀ i, (∑ j, ((sample i).targetIntersection (graph i) (σ i j) -
      (sample i).sourceIntersection (graph i) j) ^ 2) ≤ C * (b i - a i)) :
    IsTightMeasureSet (range fun i ↦
      (sample i).rootedMatchingSceneLaw (graph i) (σ i) (a i) (b i)) := by
  apply MatchingScene.isTightMeasureSet_of_moments _
    (fun k ↦ ENNReal.ofReal (2 * ((k + 1 : ℕ) : ℝ) * ρ))
    (fun _ ↦ ENNReal.ofReal_ne_top) (Real.toNNReal lam)
    (ENNReal.ofReal ((ρ + C) / 2)) ENNReal.ofReal_ne_top
  · intro i k
    exact ((sample i).lintegral_rootedMatchingSceneLaw_source_ball_le (graph i) (σ i)
      (a i) (b i) (by positivity)).trans (root_count_factor_le (hab i) (by positivity) (hcount i))
  · intro i k
    exact ((sample i).lintegral_rootedMatchingSceneLaw_target_ball_le (graph i) (σ i)
      (a i) (b i) (by positivity)).trans (root_count_factor_le (hab i) (by positivity) (hcount i))
  · intro i k
    exact ((sample i).lintegral_rootedMatchingSceneLaw_edges_ball_le (graph i) (σ i)
      (a i) (b i) (by positivity)).trans (root_count_factor_le (hab i) (by positivity) (hcount i))
  · intro i
    rw [rootedMatchingSceneLaw]
    apply (ae_map_iff ((sample i).measurable_rootedMatchingScene (graph i) (σ i)).aemeasurable
      ((GraphHeight.isClosed_lipschitzSet (Real.toNNReal lam)).measurableSet.preimage
        MatchingScene.continuous_graphHeight.measurable)).mpr
    apply ae_of_all
    intro z
    apply LipschitzWith.of_dist_le'
    intro x y
    change |(graph i).curve (x + z) - (graph i).curve z -
      ((graph i).curve (y + z) - (graph i).curve z)| ≤ _
    rw [sub_sub_sub_cancel_right]
    simpa only [Real.dist_eq, abs_sub_comm, add_sub_add_right_eq_sub] using
      (graph i).lipschitz (x + z) (y + z)
  · intro i
    apply ((sample i).lintegral_rootedMatchingSceneLaw_current_le (graph i) (σ i) (hab i)).trans
    apply ENNReal.ofReal_le_ofReal
    have hsum := add_le_add (hcount i) (henergy i)
    rw [← add_mul] at hsum
    have hdiv := (div_le_iff₀ (sub_pos.mpr (hab i))).mpr hsum
    calc
      _ = (((N i : ℝ) + ∑ j, ((sample i).targetIntersection (graph i) (σ i j) -
          (sample i).sourceIntersection (graph i) j) ^ 2) / (b i - a i)) / 2 := by ring
      _ ≤ (ρ + C) / 2 := div_le_div_of_nonneg_right hdiv (by norm_num)

end OTSelector.FiniteSample
