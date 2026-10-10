import OTSelector.PointProcess.MatchingSceneCollisionSupport
import OTSelector.PointProcess.MatchingSceneTightness

/-!
# Fixed-cut vacancy and stationarity before environment identification

For each fixed finite sample, uniform rooting bounds the mean number of either colour in an
interval by its length times the population/root-length ratio. Continuous compact cutoffs pass
this estimate to any weak limit. Shrinking a cutoff proves that every fixed cut is vacant almost
everywhere. The actual scene rerooting theorem then gives stationarity without an identified
environment marginal, intensity formula, or prior stationarity assumption.
-/

open MeasureTheory Set Filter Function Topology
open scoped Classical BigOperators ENNReal CompactlySupported
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.FiniteSample
open PointProcess
variable {n : ℕ} {lam : ℝ}

private theorem lintegral_rooted_endpoint_center_count_le
    (endpoint : Fin n → MatchingPoint) (a b x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z in Ioc a b,
      (∑ i, Measure.dirac ((endpoint i).1-z, (endpoint i).2))
        (Icc (x-r) (x+r) ×ˢ (univ : Set UnitMark))) ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (2*r) := by
  have heq (z : ℝ) :
      (∑ i, Measure.dirac ((endpoint i).1-z, (endpoint i).2))
        (Icc (x-r) (x+r) ×ˢ (univ : Set UnitMark)) =
      ∑ i, if ((endpoint i).1-x)-z ∈ Icc (-r) r then (1 : ℝ≥0∞) else 0 := by
    rw [Measure.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Measure.dirac_apply' _ (measurableSet_Icc.prod MeasurableSet.univ)]
    simp only [Set.indicator_apply, mem_prod, mem_univ, and_true, Pi.one_apply]
    congr 1
    apply propext
    simp only [mem_Icc]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simp_rw [heq]
  exact (setLIntegral_le_lintegral _ _).trans_eq
    (FiniteMatching.lintegral_rootWindow_indicator_sum (fun i ↦ (endpoint i).1-x) hr)

/-- The actual source count bound is uniform in the observation-window centre. -/
theorem lintegral_rootedMatchingSceneLaw_source_center_count_le
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    (a b x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ scene, LocalConfiguration.countingMeasure scene.source
      (Icc (x-r) (x+r) ×ˢ (univ : Set UnitMark))
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
      (ENNReal.ofReal (b-a))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (2*r)) := by
  have hm : Measurable (fun scene : MatchingScene ↦ LocalConfiguration.countingMeasure scene.source
      (Icc (x-r) (x+r) ×ˢ (univ : Set UnitMark))) :=
    (Measure.measurable_coe (measurableSet_Icc.prod MeasurableSet.univ)).comp
      (LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_source)
  rw [sample.lintegral_rootedMatchingSceneLaw graph σ a b _ hm]
  simp_rw [sample.countingMeasure_rootedMatchingScene_source graph]
  gcongr
  exact lintegral_rooted_endpoint_center_count_le
    (fun i ↦ (sample.sourceIntersection graph i, sample.sourceMark i)) a b x hr

/-- The identical root-length estimate holds for the actual target points. -/
theorem lintegral_rootedMatchingSceneLaw_target_center_count_le
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    (a b x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ scene, LocalConfiguration.countingMeasure scene.target
      (Icc (x-r) (x+r) ×ˢ (univ : Set UnitMark))
      ∂sample.rootedMatchingSceneLaw graph σ a b) ≤
      (ENNReal.ofReal (b-a))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (2*r)) := by
  have hm : Measurable (fun scene : MatchingScene ↦ LocalConfiguration.countingMeasure scene.target
      (Icc (x-r) (x+r) ×ˢ (univ : Set UnitMark))) :=
    (Measure.measurable_coe (measurableSet_Icc.prod MeasurableSet.univ)).comp
      (LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_target)
  rw [sample.lintegral_rootedMatchingSceneLaw graph σ a b _ hm]
  simp_rw [sample.countingMeasure_rootedMatchingScene_target graph]
  gcongr
  exact lintegral_rooted_endpoint_center_count_le
    (fun i ↦ (sample.targetIntersection graph i, sample.targetMark i)) a b x hr

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance cutVacancyPointTopology :
    TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase

/-- Continuous nonnegative tests transfer first-moment window bounds to fixed-cut vacancy.
The configuration map can be either colour; no simple-point or environment-law input is used. -/
theorem ae_no_points_at_cut_of_weak_window_moments
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (cfg : MatchingScene → LocalConfiguration matchingPointBase)
    (hcfg : Continuous cfg) (hcfgm : Measurable cfg) (x ρ : ℝ)
    (hcount : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      (∫⁻ scene, LocalConfiguration.countingMeasure (cfg scene)
        (Icc (x-r) (x+r) ×ˢ (univ : Set UnitMark)) ∂(μ k : Measure MatchingScene)) ≤
        ENNReal.ofReal (2*r*ρ)) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene),
      ∀ p : MatchingPoint, p.1 = x → LocalConfiguration.multiplicity (cfg scene) p = 0 := by
  let K : Set MatchingPoint := {x} ×ˢ univ
  have hK : IsCompact K := isCompact_singleton.prod isCompact_univ
  have hbound (r : ℝ) (hr : 0 < r) :
      (∫⁻ scene, LocalConfiguration.countingMeasure (cfg scene) K
        ∂(ν : Measure MatchingScene)) ≤ ENNReal.ofReal (2*r*ρ) := by
    let U : Set MatchingPoint := Prod.fst ⁻¹' Ioo (x-r) (x+r)
    have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
    have hKU : K ⊆ U := by
      rintro p ⟨hp, _⟩
      change x-r < p.1 ∧ p.1 < x+r
      rw [mem_singleton_iff.mp hp]
      constructor <;> linarith
    obtain ⟨f, hfone, hfc, hfsupp, hf⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    let test : C_c(MatchingPoint, ℝ) := ⟨f, hfc⟩
    have hf0 : ∀ p, 0 ≤ test p := fun p ↦ (hf p).1
    have hf1 : ∀ p, test p ≤ 1 := fun p ↦ (hf p).2
    have hfzero : ∀ p : MatchingPoint, p.1 ∉ Ioo (x-r) (x+r) → test p = 0 := by
      intro p hp
      exact image_eq_zero_of_notMem_tsupport (fun hs ↦ hp (hfsupp hs))
    have htest_le (scene : MatchingScene) :
        ENNReal.ofReal (LocalConfiguration.testIntegral (cfg scene) test) ≤
          LocalConfiguration.countingMeasure (cfg scene)
            (Icc (x-r) (x+r) ×ˢ (univ : Set UnitMark)) := by
      have h := ENNReal.ofReal_le_ofReal
        (LocalConfiguration.testIntegral_le_spatialCount (cfg scene) test hf0 hf1 hfzero)
      rw [LocalConfiguration.spatialCount_cast, ofReal_measureReal
        (LocalConfiguration.countingMeasure_lt_top_of_isBounded (cfg scene)
          (LocalConfiguration.isBounded_spatialIoc (x-r) (x+r))).ne] at h
      apply h.trans (measure_mono ?_)
      intro p hp
      exact ⟨⟨hp.1.le, hp.2⟩, mem_univ _⟩
    have hmoment : (∫⁻ scene, ENNReal.ofReal (LocalConfiguration.testIntegral (cfg scene) test)
        ∂(ν : Measure MatchingScene)) ≤ ENNReal.ofReal (2*r*ρ) := by
      apply lintegral_ofReal_le_of_probability_tendsto hlim
        ((LocalConfiguration.continuous_testIntegral test).comp hcfg)
      filter_upwards [hcount r hr] with k hk
      exact (lintegral_mono htest_le).trans hk
    apply (lintegral_mono (fun scene ↦ ?_)).trans hmoment
    rw [← ofReal_measureReal
      (LocalConfiguration.countingMeasure_lt_top_of_isBounded (cfg scene) hK.isBounded).ne]
    exact ENNReal.ofReal_le_ofReal
      (LocalConfiguration.countingMeasure_real_le_testIntegral (cfg scene) test hK hf0
        (fun p hp ↦ hfone hp))
  have hzero : (∫⁻ scene, LocalConfiguration.countingMeasure (cfg scene) K
      ∂(ν : Measure MatchingScene)) = 0 := by
    have hr : Tendsto (fun j : ℕ ↦ (1:ℝ)/((j:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hseq : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (2*((1:ℝ)/((j:ℝ)+1))*ρ))
        atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul, ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal ((tendsto_const_nhds.mul hr).mul tendsto_const_nhds)
    apply le_antisymm _ zero_le
    apply ge_of_tendsto hseq
    exact Eventually.of_forall fun j ↦ hbound ((1:ℝ)/((j:ℝ)+1)) (by positivity)
  have hmeas : Measurable (fun scene ↦ LocalConfiguration.countingMeasure (cfg scene) K) :=
    (Measure.measurable_coe hK.measurableSet).comp
      (LocalConfiguration.measurable_countingMeasure.comp hcfgm)
  have hae := (lintegral_eq_zero_iff hmeas).mp hzero
  filter_upwards [hae] with scene hscene
  change LocalConfiguration.countingMeasure (cfg scene) K = 0 at hscene
  intro p hp
  have hle : LocalConfiguration.countingMeasure (cfg scene) {p} ≤
      LocalConfiguration.countingMeasure (cfg scene) K :=
    measure_mono (singleton_subset_iff.mpr ⟨hp, mem_univ _⟩)
  rw [hscene, LocalConfiguration.countingMeasure_singleton] at hle
  exact_mod_cast le_antisymm hle (bot_le : (0 : ℝ≥0∞) ≤ _)

/-- Every fixed cut is vacant in a weak limit of actual uniformly rooted finite scenes, solely
from a bounded population/root-length ratio. In particular no ENV marginal is required. -/
theorem ae_vacantCut_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν)) {ρ : ℝ}
    (hcount : ∀ᶠ k in atTop, (N k : ℝ) ≤ ρ*(b k-a k)) (x : ℝ) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.VacantCut x := by
  have hs : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      ∀ p : MatchingPoint, p.1 = x → LocalConfiguration.multiplicity scene.source p = 0 := by
    apply ae_no_points_at_cut_of_weak_window_moments hlim source continuous_source measurable_source x ρ
    intro r hr
    filter_upwards [hcount] with k hk
    rw [hlaw k]
    exact ((sample k).lintegral_rootedMatchingSceneLaw_source_center_count_le
      (graph k) (assignment k) (a k) (b k) x hr.le).trans
      (FiniteSample.root_count_factor_le (hab k) hr.le hk)
  have ht : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      ∀ p : MatchingPoint, p.1 = x → LocalConfiguration.multiplicity scene.target p = 0 := by
    apply ae_no_points_at_cut_of_weak_window_moments hlim target continuous_target measurable_target x ρ
    intro r hr
    filter_upwards [hcount] with k hk
    rw [hlaw k]
    exact ((sample k).lintegral_rootedMatchingSceneLaw_target_center_count_le
      (graph k) (assignment k) (a k) (b k) x hr.le).trans
      (FiniteSample.root_count_factor_le (hab k) hr.le hk)
  exact hs.and ht

/-- Actual uniformly rooted finite scenes have stationary weak limits before ENV identification.
Cut vacancy is proved from the finite root-count bound, and reroot discontinuities are handled by
the already proved continuity theorem on the vacant-cut support. -/
theorem measurePreserving_reroot_of_rootedMatchingSceneLaw_tendsto_of_count_bound
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    (hwindow : Tendsto (fun k ↦ b k-a k) atTop atTop) {ρ : ℝ}
    (hcount : ∀ᶠ k in atTop, (N k : ℝ) ≤ ρ*(b k-a k)) (t : ℝ) :
    MeasurePreserving (reroot t) (ν : Measure MatchingScene) (ν : Measure MatchingScene) :=
  measurePreserving_reroot_of_rootedMatchingSceneLaw_tendsto
    sample graph assignment a b hab hlaw hlim htight hwindow t
    ((ae_vacantCut_of_rootedMatchingSceneLaw_tendsto sample graph assignment a b hab hlaw hlim hcount 0).and
      (ae_vacantCut_of_rootedMatchingSceneLaw_tendsto sample graph assignment a b hab hlaw hlim hcount t))

end OTSelector.PointProcess.MatchingScene
