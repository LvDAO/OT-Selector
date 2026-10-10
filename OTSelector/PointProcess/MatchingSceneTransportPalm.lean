import OTSelector.PointProcess.MatchingSceneTransport
import OTSelector.PointProcess.RootedCampbell

/-!
# Actual edge Campbell measure and its second moment

Each edge contributes one atom at its source location, marked by its signed displacement.
The unit-window Palm measure is defined from this actual counting kernel. Its full second
moment follows from the deterministic energy bounds of the finite samples and weak convergence.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal Classical

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess.MatchingScene

/-- Actual marked edge occupation: source location and signed target displacement. -/
noncomputable def sourceDisplacementCampbell (P : Measure MatchingScene) : Measure (ℝ × ℝ) :=
  (P ⊗ₘ LocalConfiguration.randomCountingKernel edges measurable_edges).map
    (fun p ↦ (p.2.1.1, p.2.2.1 - p.2.1.1))

/-- The unnormalized source-edge Palm displacement measure in the actual spatial unit window. -/
noncomputable def unitSourceDisplacementPalm (P : Measure MatchingScene) : Measure ℝ :=
  unitWindowPalm (sourceDisplacementCampbell P)

private theorem measurable_locationDisplacement :
    Measurable (fun p : MatchingScene × (MatchingPoint × MatchingPoint) ↦
      (p.2.1.1, p.2.2.1 - p.2.1.1)) :=
  (measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_snd)).sub
      (measurable_fst.comp (measurable_fst.comp measurable_snd)))

/-- Every Palm test is a genuine source-window counting integral, including edge multiplicity. -/
theorem lintegral_unitSourceDisplacementPalm (P : Measure MatchingScene) [SFinite P]
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ d, f d ∂unitSourceDisplacementPalm P) =
      ∫⁻ scene, ∫⁻ e, if e.1.1 ∈ Ioc (0 : ℝ) 1 then f (e.2.1 - e.1.1) else 0
        ∂LocalConfiguration.countingMeasure scene.edges ∂P := by
  rw [unitSourceDisplacementPalm, unitWindowPalm, lintegral_map hf measurable_snd,
    ← lintegral_indicator (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)]
  have hm : Measurable (fun q : ℝ × ℝ ↦ (Ioc (0 : ℝ) 1 ×ˢ univ).indicator
      (fun q : ℝ × ℝ ↦ f q.2) q) :=
    (hf.comp measurable_snd).indicator (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)
  rw [sourceDisplacementCampbell, lintegral_map hm measurable_locationDisplacement]
  rw [Measure.lintegral_compProd]
  · apply lintegral_congr
    intro scene
    apply lintegral_congr
    intro e
    simp only [Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true]
  · exact ((hf.comp measurable_snd).indicator
      (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)).comp measurable_locationDisplacement

/-- A concrete continuous cutoff equals one on the Palm observation window. -/
noncomputable def sourceUnitCutoff (x : MatchingPoint) : ℝ := min 1 (max 0 (2 - |x.1|))

private theorem continuous_sourceUnitCutoff : Continuous sourceUnitCutoff :=
  continuous_const.min (continuous_const.max (continuous_const.sub continuous_fst.abs))

private theorem sourceUnitCutoff_nonneg (x : MatchingPoint) : 0 ≤ sourceUnitCutoff x :=
  le_min zero_le_one (le_max_left _ _)

private theorem sourceUnitCutoff_le_one (x : MatchingPoint) : sourceUnitCutoff x ≤ 1 :=
  min_le_left _ _

private theorem sourceUnitCutoff_eq_zero (x : MatchingPoint) (hx : 2 < |x.1|) :
    sourceUnitCutoff x = 0 := by
  simp only [sourceUnitCutoff, max_eq_left (by linarith : 2 - |x.1| ≤ 0),
    min_eq_right zero_le_one]

private theorem sourceUnitCutoff_eq_one (x : MatchingPoint) (hx : x.1 ∈ Ioc (0 : ℝ) 1) :
    sourceUnitCutoff x = 1 := by
  have h : (1 : ℝ) ≤ max 0 (2 - |x.1|) := by
    rw [abs_of_pos hx.1]
    exact (by linarith [hx.2] : (1 : ℝ) ≤ 2 - x.1).trans (le_max_right _ _)
  exact min_eq_left h

/-- The Palm second moment is bounded by the actual continuous source-window energy. -/
theorem lintegral_unitSourceDisplacementPalm_sq_le (P : Measure MatchingScene) [SFinite P] :
    (∫⁻ d, ENNReal.ofReal (d ^ 2) ∂unitSourceDisplacementPalm P) ≤
      ∫⁻ scene, ∫⁻ e, ENNReal.ofReal (sourceUnitCutoff e.1 * (e.2.1 - e.1.1) ^ 2)
        ∂LocalConfiguration.countingMeasure scene.edges ∂P := by
  have h := lintegral_unitSourceDisplacementPalm P (measurable_id.pow_const 2).ennreal_ofReal
  simp only [id_eq] at h
  rw [h]
  apply lintegral_mono
  intro scene
  apply lintegral_mono
  intro e
  dsimp only
  split_ifs with h
  · rw [sourceUnitCutoff_eq_one _ h, one_mul]
  · exact zero_le

/-- The actual Palm displacement measure of a weak limit has a full second moment when the
underlying fixed finite samples have a uniform energy per root-interval length. -/
theorem unitSourceDisplacementPalm_secondMoment_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν)) {C : ℝ}
    (henergy : ∀ᶠ k in atTop, (∑ i,
      ((sample k).targetIntersection (graph k) (assignment k i) -
        (sample k).sourceIntersection (graph k) i) ^ 2) ≤ C * (b k - a k)) :
    (∫⁻ d, ENNReal.ofReal (d ^ 2) ∂unitSourceDisplacementPalm (ν : Measure MatchingScene)) ≤
      ENNReal.ofReal (4 * C) := by
  apply (lintegral_unitSourceDisplacementPalm_sq_le (ν : Measure MatchingScene)).trans
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
    lintegral_sourceWeightedEnergy_of_rootedMatchingSceneLaw_tendsto
      sample graph assignment a b hab hlaw hμ henergy continuous_sourceUnitCutoff
      sourceUnitCutoff_nonneg sourceUnitCutoff_le_one (by norm_num : (0 : ℝ) ≤ 2)
      sourceUnitCutoff_eq_zero

end OTSelector.PointProcess.MatchingScene
