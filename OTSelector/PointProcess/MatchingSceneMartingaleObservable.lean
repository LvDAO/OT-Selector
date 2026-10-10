import OTSelector.PointProcess.MatchingSceneStationarity
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentRegularity
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Continuity of the actual marked martingale observables

Weighted interval counts are continuous at vacant boundary cuts. Bounded functions of the
actual integer current have continuous time integrals at scenes with a vacant root. The latter
uses compact uniform local constancy away from a small open set of event times; it requires
no first-countability assumption on the vague scene topology.
-/

open MeasureTheory Set Function Filter Topology
open scoped Classical CompactlySupported ENNReal NNReal

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.LocalConfiguration

noncomputable local instance observablePointTopology :
    TopologicalSpace (LocalConfiguration matchingPointBase) := vagueTopology matchingPointBase

/-- Continuous geometric mark tests preserve continuity of actual interval counts. -/
theorem continuousAt_weightedSpatialCount {config : LocalConfiguration matchingPointBase}
    {a b : ℝ} {ψ : UnitMark → ℝ} (hψ : Continuous ψ)
    (ha : ∀ p : MatchingPoint, p.1 = a → multiplicity config p = 0)
    (hb : ∀ p : MatchingPoint, p.1 = b → multiplicity config p = 0) :
    ContinuousAt (fun c : LocalConfiguration matchingPointBase ↦
      ∫ p in spatialIoc a b, ψ p.2 ∂countingMeasure c) config := by
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
    let test : C_c(MatchingPoint, ℝ) :=
      ⟨⟨fun p ↦ f p * ψ p.2, f.continuous.mul (hψ.comp continuous_snd)⟩, HasCompactSupport.mul_right (show HasCompactSupport (fun p ↦ f p) from hfc)⟩
    have hzero : ∀ p ∈ K \ V, multiplicity config p = 0 := by
      intro p hp
      by_contra hm
      exact hp.2 (hLV ⟨hp.1, hm⟩)
    have hevent : ∀ᶠ c in 𝓝 config, ∀ p ∈ K \ V, multiplicity c p = 0 :=
      eventually_no_atoms_on_compact tendsto_id (hK.diff hV) hzero
    have heq (c : LocalConfiguration matchingPointBase)
        (hc : ∀ p ∈ K \ V, multiplicity c p = 0) :
        testIntegral c test = ∫ p in spatialIoc a b, ψ p.2 ∂countingMeasure c := by
      rw [← integral_countingMeasure, ← integral_indicator (measurableSet_spatialIoc a b)]
      apply integral_congr_ae
      filter_upwards [ae_mem_multiplicity_support c] with p hp
      change f p * ψ p.2 = (spatialIoc a b).indicator (fun p ↦ ψ p.2) p
      by_cases hpK : p ∈ K
      · have hpV : p ∈ V := by
          by_contra hn
          exact hp (hc p ⟨hpK, hn⟩)
        have hpU : p ∈ U := hVU (subset_closure hpV)
        have hpI : p ∈ spatialIoc a b := ⟨hpU.1, hpU.2.le⟩
        simp only [hfV (subset_closure hpV), Pi.one_apply, one_mul, indicator_of_mem hpI]
      · have hpI : p ∉ spatialIoc a b := by
          intro hi
          exact hpK ⟨⟨hi.1.le, hi.2⟩, mem_univ _⟩
        have hpS : p ∉ tsupport f := by
          intro hs
          have hu := hfU hs
          exact hpK ⟨⟨hu.1.le, hu.2.le⟩, mem_univ _⟩
        rw [image_eq_zero_of_notMem_tsupport hpS, zero_mul, indicator_of_notMem hpI]
    exact (continuous_testIntegral test).continuousAt.congr
      (hevent.mono fun c hc ↦ heq c hc)
  · have hempty : spatialIoc a b = ∅ := by
      simp [spatialIoc, Ioc_eq_empty_of_le (le_of_not_gt hab)]
    simp only [hempty, setIntegral_empty]
    exact continuousAt_const

/-- A vacant spatial cut has a whole vacant slab, uniformly over the compact mark space. -/
theorem exists_vacant_spatial_slab (config : LocalConfiguration matchingPointBase) {s : ℝ}
    (hs : ∀ p : MatchingPoint, p.1 = s → multiplicity config p = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : MatchingPoint,
      p.1 ∈ Icc (s - δ) (s + δ) → multiplicity config p = 0 := by
  let K : Set MatchingPoint := Icc (s - 1) (s + 1) ×ˢ univ
  let L := K ∩ support (multiplicity config)
  have hL : L.Finite :=
    (locallyFiniteSupport_multiplicity config).finite_inter_support_of_isCompact
      (isCompact_Icc.prod isCompact_univ)
  have hnot : s ∉ Prod.fst '' L := by
    rintro ⟨p, hp, hps⟩
    exact hp.2 (hs p hps)
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp
    ((hL.image Prod.fst).isClosed.isOpen_compl.mem_nhds hnot)
  let δ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  refine ⟨δ, hδ, fun p hp ↦ ?_⟩
  by_contra hm
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hnear : p.1 ∈ Metric.ball s ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hp.1, hp.2]
  apply heps hnear
  exact ⟨p, ⟨⟨⟨by linarith [hp.1], by linarith [hp.2]⟩, mem_univ _⟩, hm⟩, rfl⟩

private theorem spatialCount_eq_zero_of_vacant (config : LocalConfiguration matchingPointBase)
    {a b : ℝ} (h : ∀ p ∈ spatialIoc a b, multiplicity config p = 0) :
    spatialCount config a b = 0 := by
  have hm := (countingMeasure_eq_zero_iff config (measurableSet_spatialIoc a b)).mpr h
  simp [spatialCount, Measure.real, hm]

/-- The count remains locally constant when both the scene and the upper cut move. -/
theorem continuousAt_orientedCount_joint {config : LocalConfiguration matchingPointBase}
    {a s : ℝ} (ha : ∀ p : MatchingPoint, p.1 = a → multiplicity config p = 0)
    (hs : ∀ p : MatchingPoint, p.1 = s → multiplicity config p = 0) :
    ContinuousAt (fun q : LocalConfiguration matchingPointBase × ℝ ↦
      orientedCount q.1 a q.2) (config, s) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_vacant_spatial_slab config hs
  have hevent : ∀ᶠ c in 𝓝 config, ∀ p ∈ Icc (s - δ) (s + δ) ×ˢ (univ : Set UnitMark),
      multiplicity c p = 0 :=
    eventually_no_atoms_on_compact tendsto_id (isCompact_Icc.prod isCompact_univ)
      (fun p hp ↦ hgap p hp.1)
  have hfixed : ContinuousAt (fun q : LocalConfiguration matchingPointBase × ℝ ↦
      orientedCount q.1 a s) (config, s) :=
    (continuousAt_orientedCount ha hs).comp (x := (config, s)) (f := Prod.fst) continuousAt_fst
  apply hfixed.congr
  filter_upwards [continuousAt_fst.eventually hevent,
    continuousAt_snd.eventually (Ioo_mem_nhds (by linarith : s - δ < s)
      (by linarith : s < s + δ))] with q hq ht
  have hst : spatialCount q.1 s q.2 = 0 := by
    apply spatialCount_eq_zero_of_vacant
    intro p hp
    exact hq p ⟨⟨by linarith [hp.1], by linarith [hp.2, ht.2]⟩, mem_univ _⟩
  have hts : spatialCount q.1 q.2 s = 0 := by
    apply spatialCount_eq_zero_of_vacant
    intro p hp
    exact hq p ⟨⟨by linarith [hp.1, ht.1], by linarith [hp.2]⟩, mem_univ _⟩
  rw [orientedCount_add q.1 a s q.2]
  simp [orientedCount, hst, hts]

end OTSelector.PointProcess.LocalConfiguration

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance observablePointTopology :
    TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase

/-- Joint local constancy of the actual integer current at a vacant observation cut. -/
theorem continuousAt_currentAt_joint {scene : MatchingScene} {s : ℝ}
    (h0 : scene.VacantCut 0) (hs : scene.VacantCut s) :
    ContinuousAt (fun q : MatchingScene × ℝ ↦ q.1.currentAt q.2) (scene, s) := by
  have hsource := (LocalConfiguration.continuousAt_orientedCount_joint h0.1 hs.1).comp
    (x := (scene, s)) (f := fun q : MatchingScene × ℝ ↦ (q.1.source, q.2))
    ((continuous_source.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd)
  have htarget := (LocalConfiguration.continuousAt_orientedCount_joint h0.2 hs.2).comp
    (x := (scene, s)) (f := fun q : MatchingScene × ℝ ↦ (q.1.target, q.2))
    ((continuous_target.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd)
  exact (continuous_rootCurrent.continuousAt.comp continuousAt_fst).add (hsource.sub htarget)

/-- Compact sets of vacant cuts have a single neighborhood with exactly the same currents. -/
theorem eventually_currentAt_eq_on_compact {scene : MatchingScene} (h0 : scene.VacantCut 0)
    {K : Set ℝ} (hK : IsCompact K) (hcut : ∀ s ∈ K, scene.VacantCut s) :
    ∀ᶠ scene' in 𝓝 scene, ∀ s ∈ K, scene'.currentAt s = scene.currentAt s := by
  apply hK.eventually_forall_of_forall_eventually
  intro s hs
  have hleft := continuousAt_currentAt_joint h0 (hcut s hs)
  have hbase : ContinuousAt (fun t : ℝ ↦ scene.currentAt t) s :=
    hleft.comp (continuousAt_const.prodMk continuousAt_id)
  have hdiff := hleft.sub (hbase.comp continuousAt_snd)
  have hevent := hdiff.eventually (isOpen_discrete {0} |>.mem_nhds (by simp))
  filter_upwards [hevent] with q hq
  exact sub_eq_zero.mp hq

/-- A scene has only countably many occupied cuts, hence almost every cut is vacant. -/
theorem countable_nonvacantCuts (scene : MatchingScene) : {s | ¬scene.VacantCut s}.Countable := by
  apply ((LocalConfiguration.countable_multiplicity_support scene.source).image Prod.fst |>.union
    ((LocalConfiguration.countable_multiplicity_support scene.target).image Prod.fst)).mono
  intro s hs
  simp only [VacantCut, not_and_or, not_forall, exists_prop] at hs
  rcases hs with ⟨p, hp, hm⟩ | ⟨p, hp, hm⟩
  · exact Or.inl ⟨p, hm, hp⟩
  · exact Or.inr ⟨p, hm, hp⟩

private theorem measurable_currentAt_time (scene : MatchingScene) :
    Measurable scene.currentAt := by
  exact Limit.measurable_feedbackEnvironmentCurrent.comp
    (measurable_id.prodMk (measurable_const (a := Matching.feedbackSceneEnvironment scene)))

/-- The integral of any bounded state function is continuous in the actual vague scene.
Only root vacancy is required; the finitely many event times in the integration window may move. -/
theorem continuousAt_setIntegral_currentAt {scene : MatchingScene} (h0 : scene.VacantCut 0)
    (g : ℤ → ℝ) {C : ℝ} (hbound : ∀ j, ‖g j‖ ≤ C) (a b : ℝ) :
    ContinuousAt (fun scene' : MatchingScene ↦ ∫ s in Icc a b, g (scene'.currentAt s)) scene := by
  have hC : 0 ≤ C := (norm_nonneg (g 0)).trans (hbound 0)
  have hint (scene' : MatchingScene) : IntegrableOn (fun s ↦ g (scene'.currentAt s)) (Icc a b) :=
    (integrable_const C).mono' ((measurable_of_countable g).comp
      (measurable_currentAt_time scene')).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ hbound _)
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hden : 0 < 2 * (C + 1) := by positivity
  have hsmall : 0 < ε / (2 * (C + 1)) := div_pos hε hden
  obtain ⟨U, hbadU, hU, hμU⟩ := Set.exists_isOpen_lt_of_lt
    (μ := volume) {s | ¬scene.VacantCut s} (ENNReal.ofReal (ε / (2 * (C + 1)))) (by
      rw [(countable_nonvacantCuts scene).measure_zero volume]
      exact ENNReal.ofReal_pos.mpr hsmall)
  have hUfin : volume U < ∞ := hμU.trans (ENNReal.ofReal_lt_top)
  have hrealU : volume.real U < ε / (2 * (C + 1)) := by
    exact (ENNReal.toReal_lt_toReal hUfin.ne ENNReal.ofReal_ne_top).mpr hμU |>.trans_eq
      (ENNReal.toReal_ofReal hsmall.le)
  have huniform := eventually_currentAt_eq_on_compact h0 (K := Icc a b \ U) (isCompact_Icc.diff hU)
    (fun s hs ↦ by by_contra hn; exact hs.2 (hbadU hn))
  filter_upwards [huniform] with scene' heq
  rw [dist_eq_norm, ← integral_sub (hint scene') (hint scene)]
  let f : ℝ → ℝ := fun s ↦ g (scene'.currentAt s) - g (scene.currentAt s)
  have hsame : (fun s ↦ f s) =ᵐ[volume.restrict (Icc a b)] U.indicator f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    by_cases hsU : s ∈ U
    · rw [indicator_of_mem hsU]
    · rw [indicator_of_notMem hsU]
      simp only [f, heq s ⟨hs, hsU⟩, sub_self]
  change ‖∫ s in Icc a b, f s‖ < ε
  rw [integral_congr_ae hsame, integral_indicator hU.measurableSet]
  have hboundf (s : ℝ) : ‖f s‖ ≤ 2 * (C + 1) := by
    apply (norm_sub_le _ _).trans
    change ‖g (scene'.currentAt s)‖ + ‖g (scene.currentAt s)‖ ≤ _
    linarith [hbound (scene'.currentAt s), hbound (scene.currentAt s)]
  calc
    ‖∫ s in U, f s ∂volume.restrict (Icc a b)‖ ≤
        2 * (C + 1) * (volume.restrict (Icc a b)).real U :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (fun s _ ↦ hboundf s)
    _ ≤ 2 * (C + 1) * volume.real U := by
      apply mul_le_mul_of_nonneg_left _ hden.le
      rw [measureReal_restrict_apply hU.measurableSet]
      exact measureReal_mono inter_subset_left hUfin.ne
    _ < ε := by
      have hh := mul_lt_mul_of_pos_left hrealU hden
      rwa [mul_div_cancel₀ ε hden.ne'] at hh

/-- The oriented interval version is valid for both orders of the integration endpoints. -/
theorem continuousAt_integral_currentAt {scene : MatchingScene} (h0 : scene.VacantCut 0)
    (g : ℤ → ℝ) {C : ℝ} (hbound : ∀ j, ‖g j‖ ≤ C) (a b : ℝ) :
    ContinuousAt (fun scene' : MatchingScene ↦ ∫ s in a..b, g (scene'.currentAt s)) scene := by
  rcases le_total a b with hab | hba
  · simpa only [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab] using
      continuousAt_setIntegral_currentAt h0 g hbound a b
  · have h := (continuousAt_setIntegral_currentAt h0 g hbound b a).neg
    change ContinuousAt (fun scene' : MatchingScene ↦
      -(∫ s in Icc b a, g (scene'.currentAt s))) scene at h
    simpa only [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_ge hba] using h

/-- The actual source/target marked count, with no atom at either endpoint. -/
theorem continuousAt_firstEventTestCount {scene : MatchingScene} {ψ : UnitMark → ℝ}
    (hψ : Continuous ψ) (b : Bool) {t : ℝ}
    (h0 : scene.VacantCut 0) (ht : scene.VacantCut t) :
    ContinuousAt (fun scene' : MatchingScene ↦ LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene')) b ψ t)
      scene := by
  cases b
  · exact (LocalConfiguration.continuousAt_weightedSpatialCount hψ h0.2 ht.2).comp
      continuous_target.continuousAt
  · exact (LocalConfiguration.continuousAt_weightedSpatialCount hψ h0.1 ht.1).comp
      continuous_source.continuousAt

/-- The concrete marked compensated count is continuous at scenes with vacant root and horizon.
The rate is the original three-valued feedback rate; no continuity or moment premise is assumed
for the compensator itself. -/
theorem continuousAt_feedbackEnvironmentMarkedCompensator {scene : MatchingScene}
    (lam : ℝ) (b : Bool) {ψ : UnitMark → ℝ} (hψ : Continuous ψ) (t : ℝ≥0)
    (h0 : scene.VacantCut 0) (ht : scene.VacantCut t) :
    ContinuousAt (fun scene' : MatchingScene ↦
      Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
        (Matching.feedbackSceneEnvironment scene')) scene :=
  (continuousAt_firstEventTestCount hψ b h0 ht).sub
    (continuousAt_integral_currentAt h0 (Limit.feedbackEnvironmentMarkRate lam b ψ)
      (Limit.norm_feedbackEnvironmentMarkRate_le lam b ψ) 0 t)

end OTSelector.PointProcess.MatchingScene
