import OTSelector.PointProcess.MatchingSceneTransportCrossing
import OTSelector.Matching.FeedbackSceneJoining
import OTSelector.Limit.FeedbackMarkIntensity
import Mathlib.Topology.UrysohnsLemma

/-!
# Spatial stationarity of actual weak limits

Physical rerooting is continuous at scenes with no endpoint at either cut.  The integer current
is treated through actual counting measures, including multiplicities.  This almost-everywhere
continuity and the finite spatial-average boundary estimate transfer stationarity to weak limits.
-/

open MeasureTheory Set Function Filter Topology
open scoped Classical CompactlySupported ENNReal

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.LocalConfiguration

noncomputable local instance stationarityPointTopology :
    TopologicalSpace (LocalConfiguration matchingPointBase) := vagueTopology matchingPointBase

/-- Actual interval counts are continuous at configurations with vacant boundary cuts.
The approximating configurations need not be simple. -/
theorem continuousAt_spatialCount {config : LocalConfiguration matchingPointBase} {a b : ℝ}
    (ha : ∀ p : MatchingPoint, p.1 = a → multiplicity config p = 0)
    (hb : ∀ p : MatchingPoint, p.1 = b → multiplicity config p = 0) :
    ContinuousAt (fun c : LocalConfiguration matchingPointBase ↦ spatialCount c a b) config := by
  by_cases hab : a < b
  · let K : Set MatchingPoint := Icc a b ×ˢ univ
    let U : Set MatchingPoint := Prod.fst ⁻¹' Ioo a b
    have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
    have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
    let L := K ∩ support (multiplicity config)
    have hL : L.Finite :=
      (locallyFiniteSupport_multiplicity config).finite_inter_support_of_isCompact hK
    have hLU : L ⊆ U := by
      rintro p ⟨hp, hm⟩
      refine ⟨lt_of_le_of_ne hp.1.1 ?_, lt_of_le_of_ne hp.1.2 ?_⟩
      · intro h; exact hm (ha p h.symm)
      · intro h; exact hm (hb p h)
    obtain ⟨V, hV, hLV, hVU, hVc⟩ :=
      exists_open_between_and_isCompact_closure hL.isCompact hU hLU
    obtain ⟨f, hfV, hfc, hfU, _⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hVc hU hVU
    let test : C_c(MatchingPoint, ℝ) := ⟨f, hfc⟩
    have hzero : ∀ p ∈ K \ V, multiplicity config p = 0 := by
      intro p hp
      by_contra hm
      exact hp.2 (hLV ⟨hp.1, hm⟩)
    have hevent : ∀ᶠ c in 𝓝 config, ∀ p ∈ K \ V, multiplicity c p = 0 :=
      eventually_no_atoms_on_compact tendsto_id (hK.diff hV) hzero
    have heq (c : LocalConfiguration matchingPointBase)
        (hc : ∀ p ∈ K \ V, multiplicity c p = 0) :
        testIntegral c test = (spatialCount c a b : ℝ) := by
      rw [← integral_countingMeasure, spatialCount_cast,
        ← integral_indicator_one (measurableSet_spatialIoc a b)]
      apply integral_congr_ae
      filter_upwards [ae_mem_multiplicity_support c] with p hp
      by_cases hpK : p ∈ K
      · have hpV : p ∈ V := by
          by_contra hn
          exact hp (hc p ⟨hpK, hn⟩)
        have hpU : p ∈ U := hVU (subset_closure hpV)
        have hpI : p ∈ spatialIoc a b := ⟨hpU.1, hpU.2.le⟩
        change f p = (spatialIoc a b).indicator (fun _ ↦ (1 : ℝ)) p
        simpa only [indicator_of_mem hpI, Pi.one_apply] using hfV (subset_closure hpV)
      · have hpI : p ∉ spatialIoc a b := by
          intro hi
          exact hpK ⟨⟨hi.1.le, hi.2⟩, mem_univ _⟩
        have hpS : p ∉ tsupport f := by
          intro hs
          have hu := hfU hs
          exact hpK ⟨⟨hu.1.le, hu.2.le⟩, mem_univ _⟩
        simp only [indicator_of_notMem hpI]
        exact image_eq_zero_of_notMem_tsupport hpS
    have hreal : ContinuousAt
        (fun c : LocalConfiguration matchingPointBase ↦ (spatialCount c a b : ℝ)) config := by
      have htest := (continuous_testIntegral (base := matchingPointBase) test).continuousAt (x := config)
      exact htest.congr (hevent.mono fun c hc ↦ heq c hc)
    exact Int.isClosedEmbedding_coe_real.isEmbedding.isInducing.continuousAt_iff.mpr hreal
  · have heq : (fun c : LocalConfiguration matchingPointBase ↦ spatialCount c a b) =
        fun _ ↦ 0 := funext fun c ↦ spatialCount_eq_zero_of_le c (le_of_not_gt hab)
    rw [heq]
    exact continuousAt_const

/-- The signed current increment is continuous whenever its two cuts are vacant. -/
theorem continuousAt_orientedCount {config : LocalConfiguration matchingPointBase} {a b : ℝ}
    (ha : ∀ p : MatchingPoint, p.1 = a → multiplicity config p = 0)
    (hb : ∀ p : MatchingPoint, p.1 = b → multiplicity config p = 0) :
    ContinuousAt (fun c : LocalConfiguration matchingPointBase ↦ orientedCount c a b) config :=
  (continuousAt_spatialCount ha hb).sub (continuousAt_spatialCount hb ha)

section Homeomorph
variable {X : Type*} [MetricSpace X] [ProperSpace X] {base : X}

/-- Fixed physical point homeomorphisms preserve vague convergence. -/
theorem continuous_mapHomeomorph (e : X ≃ₜ X) :
    Continuous[vagueTopology base, vagueTopology base] (mapHomeomorph e) := by
  apply continuous_iInf_rng.mpr
  intro f
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, testIntegral_mapHomeomorph] using
    (continuous_testIntegral (base := base) (f.comp e.toCocompactMap))
end Homeomorph

end OTSelector.PointProcess.LocalConfiguration

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance stationarityPointTopology :
    TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase
noncomputable local instance stationarityEdgeTopology :
    TopologicalSpace (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueTopology (matchingPointBase, matchingPointBase)

/-- A cut contains no source or target point, with arbitrary multiplicities allowed elsewhere. -/
def VacantCut (scene : MatchingScene) (x : ℝ) : Prop :=
  (∀ p : MatchingPoint, p.1 = x → LocalConfiguration.multiplicity scene.source p = 0) ∧
  (∀ p : MatchingPoint, p.1 = x → LocalConfiguration.multiplicity scene.target p = 0)

/-- Rerooting is continuous at precisely the continuity configurations needed for spatial limits:
there is no source or target atom at the old or new cut. -/
theorem continuousAt_reroot {scene : MatchingScene} {t : ℝ}
    (h0 : scene.VacantCut 0) (ht : scene.VacantCut t) :
    ContinuousAt (reroot t) scene := by
  apply coordinatesHomeomorph.isEmbedding.isInducing.continuousAt_iff.mpr
  have hs : ContinuousAt (fun s : MatchingScene ↦ LocalConfiguration.translate (-t) s.source) scene :=
    (LocalConfiguration.continuous_translate (-t)).continuousAt.comp
    continuous_source.continuousAt
  have htgt : ContinuousAt (fun s : MatchingScene ↦ LocalConfiguration.translate (-t) s.target) scene :=
    (LocalConfiguration.continuous_translate (-t)).continuousAt.comp
    continuous_target.continuousAt
  have he : ContinuousAt (fun s : MatchingScene ↦
      LocalConfiguration.mapHomeomorph (edgeReroot t) s.edges) scene :=
    (LocalConfiguration.continuous_mapHomeomorph (edgeReroot t)).continuousAt.comp
    continuous_edges.continuousAt
  have hi : ContinuousAt (fun s : MatchingScene ↦ s.currentIncrement 0 t) scene :=
    ((LocalConfiguration.continuousAt_orientedCount h0.1 ht.1).comp
      continuous_source.continuousAt).sub
      ((LocalConfiguration.continuousAt_orientedCount h0.2 ht.2).comp
        continuous_target.continuousAt)
  have hp : ContinuousAt (fun s : MatchingScene ↦ (reroot t s).path) scene := by
    apply FeedbackPath.isEmbedding_coordinates.isInducing.continuousAt_iff.mpr
    exact ((GraphHeight.continuous_reroot t).continuousAt.comp
      continuous_graphHeight.continuousAt).prodMk (continuous_rootCurrent.continuousAt.add hi)
  exact hs.prodMk (htgt.prodMk (he.prodMk hp))

/-- Almost-everywhere continuous measurable maps preserve weak convergence of tight scene laws.
The proof uses the actual scene closed-set Portmanteau theorem; global continuity is unnecessary. -/
theorem tendsto_map_of_ae_continuousAt
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]
    (μ : ℕ → ProbabilityMeasure MatchingScene) {ν : ProbabilityMeasure MatchingScene}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    {f : MatchingScene → Y} (hf : Measurable f)
    (hcont : ∀ᵐ scene ∂(ν : Measure MatchingScene), ContinuousAt f scene) :
    Tendsto (fun n ↦ (μ n).map hf.aemeasurable) atTop
      (𝓝 (ν.map hf.aemeasurable)) := by
  apply MeasureTheory.tendsto_of_forall_isClosed_limsup_le'
  intro F hF
  have hclosed := limsup_measure_closed_le_of_tendsto_of_tight μ hlim htight
    (isClosed_closure (s := f ⁻¹' F))
  have hmeasure : (ν : Measure MatchingScene) (closure (f ⁻¹' F)) =
      (ν : Measure MatchingScene) (f ⁻¹' F) := by
    apply measure_congr
    filter_upwards [hcont] with scene hc
    apply propext
    constructor
    · intro hscene
      have hh := mem_closure_image hc hscene
      exact hF.closure_eq ▸ (closure_mono (image_preimage_subset f F) hh)
    · intro hscene
      exact subset_closure hscene
  simp only [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hf hF.measurableSet] at ⊢
  exact (Filter.limsup_le_limsup (Eventually.of_forall fun n ↦
    measure_mono subset_closure)).trans (hmeasure ▸ hclosed)

/-- Actual physical reroots of tight weak scene laws converge whenever the limiting environment
has no endpoint at either deterministic cut. -/
theorem tendsto_reroot_map_of_vacantCuts
    (μ : ℕ → ProbabilityMeasure MatchingScene) {ν : ProbabilityMeasure MatchingScene}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    (t : ℝ) (hcuts : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      scene.VacantCut 0 ∧ scene.VacantCut t) :
    Tendsto (fun n ↦ (μ n).map (rerootMeasurableEquiv t).measurable.aemeasurable) atTop
      (𝓝 (ν.map (rerootMeasurableEquiv t).measurable.aemeasurable)) := by
  apply tendsto_map_of_ae_continuousAt μ hlim htight
    (rerootMeasurableEquiv t).measurable
  exact hcuts.mono fun scene hs ↦ continuousAt_reroot hs.1 hs.2

/-- The shifted finite laws have the same weak limit as the original laws when the root
window length diverges.  This uses the actual finite boundary estimate, not continuity of reroot. -/
theorem tendsto_reroot_map_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (hwindow : Tendsto (fun k ↦ b k - a k) atTop atTop) (t : ℝ) :
    Tendsto (fun n ↦ (μ n).map (rerootMeasurableEquiv t).measurable.aemeasurable) atTop
      (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hold := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f
  have herr : Tendsto (fun k ↦
      (∫ scene, f (reroot t scene) ∂(μ k : Measure MatchingScene)) -
        ∫ scene, f scene ∂(μ k : Measure MatchingScene)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k ↦ ?_)
      (show Tendsto (fun k ↦ 2 * ‖f‖ * |t| / (b k - a k)) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop hwindow)
    rw [hlaw k]
    exact (sample k).norm_integral_rootedMatchingSceneLaw_reroot_sub_le (graph k)
      (assignment k) (hab k) f f.continuous.measurable f.norm_coe_le_norm t
  have hsum := herr.add hold
  simp only [zero_add, sub_add_cancel] at hsum
  simp only [ProbabilityMeasure.toMeasure_map,
    integral_map (rerootMeasurableEquiv t).measurable.aemeasurable
      f.continuous.measurable.aestronglyMeasurable]
  exact hsum

private theorem ae_no_points_at_cut_of_intensity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (cfg : Ω → LocalConfiguration matchingPointBase) (hm : Measurable cfg)
    (hintensity : P.bind (fun ω ↦ LocalConfiguration.countingMeasure (cfg ω)) =
      (volume : Measure ℝ).prod (volume : Measure UnitMark)) (x : ℝ) :
    ∀ᵐ ω ∂P, ∀ p : MatchingPoint, p.1 = x →
      LocalConfiguration.multiplicity (cfg ω) p = 0 := by
  let K : Set MatchingPoint := {x} ×ˢ univ
  have hK : MeasurableSet K := (measurableSet_singleton x).prod MeasurableSet.univ
  have hkernel : Measurable (fun ω ↦ LocalConfiguration.countingMeasure (cfg ω)) :=
    LocalConfiguration.measurable_countingMeasure.comp hm
  have hzero : (∫⁻ ω, LocalConfiguration.countingMeasure (cfg ω) K ∂P) = 0 := by
    rw [← Measure.bind_apply hK hkernel.aemeasurable, hintensity]
    simp only [K, Measure.prod_prod, measure_singleton, zero_mul]
  have hae := (lintegral_eq_zero_iff ((Measure.measurable_coe hK).comp hkernel)).mp hzero
  filter_upwards [hae] with ω hω
  change LocalConfiguration.countingMeasure (cfg ω) K = 0 at hω
  intro p hp
  have hle : LocalConfiguration.countingMeasure (cfg ω) {p} ≤
      LocalConfiguration.countingMeasure (cfg ω) K :=
    measure_mono (singleton_subset_iff.mpr ⟨hp, mem_univ _⟩)
  rw [hω, LocalConfiguration.countingMeasure_singleton] at hle
  exact_mod_cast le_antisymm hle (bot_le : (0 : ℝ≥0∞) ≤ _)

/-- The actual feedback environment marginal supplies the deterministic-cut continuity support
needed above, through its proved marked intensities. -/
theorem ae_vacantCut_of_feedback_environment_law
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P : Measure MatchingScene)
    (henv : P.map OTSelector.Matching.feedbackSceneEnvironment =
      OTSelector.Limit.feedbackStationaryEnvironmentLaw lam hlam0 hlam) (x : ℝ) :
    ∀ᵐ scene ∂P, scene.VacantCut x := by
  have hs := ae_no_points_at_cut_of_intensity
    (OTSelector.Limit.feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    FeedbackEnvironment.source FeedbackEnvironment.measurable_source
    (OTSelector.Limit.feedbackStationary_source_intensity hlam0 hlam) x
  have ht := ae_no_points_at_cut_of_intensity
    (OTSelector.Limit.feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    FeedbackEnvironment.target FeedbackEnvironment.measurable_target
    (OTSelector.Limit.feedbackStationary_target_intensity hlam0 hlam) x
  rw [← henv] at hs ht
  exact (ae_of_ae_map OTSelector.Matching.measurable_feedbackSceneEnvironment.aemeasurable hs).and
    (ae_of_ae_map OTSelector.Matching.measurable_feedbackSceneEnvironment.aemeasurable ht)

/-- Spatial averages of actual finite samples have stationary weak limits on the deterministic-cut
continuity support. The only scale input is divergence of the actual averaging-window length. -/
theorem measurePreserving_reroot_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    (hwindow : Tendsto (fun k ↦ b k - a k) atTop atTop) (t : ℝ)
    (hcuts : ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.VacantCut 0 ∧ scene.VacantCut t) :
    MeasurePreserving (reroot t) (ν : Measure MatchingScene) (ν : Measure MatchingScene) := by
  have hfirst := tendsto_reroot_map_of_vacantCuts μ hlim htight t hcuts
  have hsecond := tendsto_reroot_map_of_rootedMatchingSceneLaw_tendsto
    sample graph assignment a b hab hlaw hlim hwindow t
  have heq := eq_of_tendsto_of_tendsto hfirst hsecond
  refine ⟨(rerootMeasurableEquiv t).measurable, ?_⟩
  exact congrArg (fun P : ProbabilityMeasure MatchingScene ↦ (P : Measure MatchingScene)) heq

/-- With the actual stationary feedback environment marginal, all fixed physical reroots preserve
the weak scene limit. No stationarity, continuity of reroot, or cut vacancy is assumed separately. -/
theorem measurePreserving_reroot_of_feedback_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    (hwindow : Tendsto (fun k ↦ b k - a k) atTop atTop)
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (henv : (ν : Measure MatchingScene).map OTSelector.Matching.feedbackSceneEnvironment =
      OTSelector.Limit.feedbackStationaryEnvironmentLaw lam hlam0 hlam) (t : ℝ) :
    MeasurePreserving (reroot t) (ν : Measure MatchingScene) (ν : Measure MatchingScene) :=
  measurePreserving_reroot_of_rootedMatchingSceneLaw_tendsto
    sample graph assignment a b hab hlaw hlim htight hwindow t
    ((ae_vacantCut_of_feedback_environment_law hlam0 hlam _ henv 0).and
      (ae_vacantCut_of_feedback_environment_law hlam0 hlam _ henv t))

end OTSelector.PointProcess.MatchingScene
