import OTSelector.Matching.FeedbackProjectiveLaw
import OTSelector.PointProcess.MatchingSceneTransport
import Mathlib.MeasureTheory.Group.Integral

/-!
# Reading empirical mark pairs from actual rooted scene laws

A continuous source window averages genuine finite matching edges over the physical root
interval. The resulting weights differ from the original block indicator only near the two
block endpoints. Compact edge tests and conservation of total source mass identify the limiting
mark average with the actual source Palm coupling.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped ENNReal BigOperators Classical CompactlySupported

namespace OTSelector.PointProcess
open OTSelector.Matching OTSelector.Limit

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

/-- Physical-root weight assigned to a source at `x` by a continuous observation window. -/
noncomputable def sourceRootWindowWeight (φ : C_c(ℝ, ℝ)) (a b x : ℝ) : ℝ :=
  ∫ z in Ioc a b, φ (x - z)

/-- A genuine normalized source observation window exists with fixed support radius one. -/
theorem exists_unit_sourceObservationWindow :
    ∃ φ : C_c(ℝ, ℝ), (∀ x, 0 ≤ φ x) ∧ (∫ x, φ x) = 1 ∧
      ∀ x, 1 < |x| → φ x = 0 := by
  let f := LocalConfiguration.distanceTent (0 : ℝ) 1
  have h0 (x : ℝ) : 0 ≤ f x := le_max_left _ _
  have hi : 0 < ∫ x, f x := f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    f.hasCompactSupport h0 (x := 0) (by simp [f])
  refine ⟨(∫ x, f x)⁻¹ • f, ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg (inv_nonneg.mpr hi.le) (h0 x)
  · change (∫ x, (∫ y, f y)⁻¹ * f x) = 1
    rw [integral_const_mul, inv_mul_cancel₀ hi.ne']
  · intro x hx
    change (∫ y, f y)⁻¹ * max 0 (1 - dist x 0) = 0
    rw [Real.dist_eq, sub_zero, max_eq_left (by linarith), mul_zero]

theorem sourceRootWindowWeight_nonneg (φ : C_c(ℝ, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    (a b x : ℝ) : 0 ≤ sourceRootWindowWeight φ a b x :=
  integral_nonneg (fun z ↦ hφ (x - z))

theorem sourceRootWindowWeight_le_one (φ : C_c(ℝ, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    (hunit : (∫ x, φ x) = 1) (a b x : ℝ) : sourceRootWindowWeight φ a b x ≤ 1 := by
  have hi : Integrable (fun z ↦ φ (x - z)) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).comp_sub_left x
  exact (setIntegral_le_integral hi (ae_of_all _ fun z ↦ hφ (x - z))).trans_eq
    ((integral_sub_left_eq_self φ volume x).trans hunit)

/-- Away from the two boundary strips, continuous root averaging equals the original block
indicator exactly. -/
theorem sourceRootWindowWeight_eq_indicator (φ : C_c(ℝ, ℝ))
    (hunit : (∫ x, φ x) = 1) {A a b x : ℝ} (_hA : 0 ≤ A)
    (hsupport : ∀ z, A < |z| → φ z = 0)
    (ha : A < |x - a|) (hb : A < |x - b|) :
    sourceRootWindowWeight φ a b x = if x ∈ Ioc a b then 1 else 0 := by
  by_cases hx : x ∈ Ioc a b
  · rw [ite_eq_left hx, sourceRootWindowWeight,
      setIntegral_eq_integral_of_forall_compl_eq_zero, integral_sub_left_eq_self, hunit]
    intro z hz
    apply hsupport
    have hxa : A < x - a := by rwa [abs_of_pos (sub_pos.mpr hx.1)] at ha
    have hbx : A < b - x := by rw [abs_of_nonpos (sub_nonpos.mpr hx.2)] at hb; linarith
    by_contra h
    have hh := abs_le.mp (le_of_not_gt h)
    exact hz ⟨by linarith [hh.2], by linarith [hh.1]⟩
  · rw [ite_eq_right hx]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro z hz
    apply hsupport
    by_contra h
    have hh := abs_le.mp (le_of_not_gt h)
    have hxa : a < x := by
      by_contra hxa
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt hxa))] at ha
      linarith [hz.1, hh.1]
    have hxb : x ≤ b := by
      by_contra hxb
      rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hxb))] at hb
      linarith [hz.2, hh.2]
    exact hx ⟨hxa, hxb⟩

/-- The deterministic boundary error is at most one per source in either boundary strip. -/
theorem abs_sourceRootWindowWeight_sub_indicator_le (φ : C_c(ℝ, ℝ))
    (hφ : ∀ x, 0 ≤ φ x) (hunit : (∫ x, φ x) = 1) {A : ℝ} (hA : 0 ≤ A)
    (hsupport : ∀ z, A < |z| → φ z = 0) (a b x : ℝ) :
    |sourceRootWindowWeight φ a b x - (if x ∈ Ioc a b then 1 else 0)| ≤
      if |x - a| ≤ A ∨ |x - b| ≤ A then 1 else 0 := by
  by_cases hb : |x - a| ≤ A ∨ |x - b| ≤ A
  · rw [ite_eq_left hb]
    have h0 := sourceRootWindowWeight_nonneg φ hφ a b x
    have h1 := sourceRootWindowWeight_le_one φ hφ hunit a b x
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · rw [ite_eq_right hb, sourceRootWindowWeight_eq_indicator φ hunit hA hsupport
      (lt_of_not_ge (fun h ↦ hb (Or.inl h))) (lt_of_not_ge (fun h ↦ hb (Or.inr h))), sub_self, abs_zero]

namespace MatchingScene

/-- Mean actual edge measure in source-location and original mark-pair coordinates. -/
noncomputable def sourceMarkCampbell (P : Measure MatchingScene) : Measure (ℝ × (UnitMark × UnitMark)) :=
  (feedbackSceneEdgeIntensity P).map (fun e ↦ (e.1.1, (e.1.2, e.2.2)))

private theorem measurable_sourceMarkCoordinates :
    Measurable (fun e : MatchingPoint × MatchingPoint ↦ (e.1.1, (e.1.2, e.2.2))) :=
  measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd.snd)

theorem sourceMarkCampbell_unitWindow (P : Measure MatchingScene) :
    unitWindowPalm (sourceMarkCampbell P) = feedbackProjectiveLaw P := by
  ext B hB
  rw [unitWindowPalm_apply _ hB, sourceMarkCampbell,
    Measure.map_apply measurable_sourceMarkCoordinates (measurableSet_Ioc.prod hB),
    feedbackProjectiveLaw, Measure.map_apply (measurable_fst.snd.prodMk measurable_snd.snd) hB,
    Measure.restrict_apply ((measurable_fst.snd.prodMk measurable_snd.snd) hB)]
  congr 1
  ext e
  exact and_comm

/-- The genuine edge Campbell measure factors using its original unit-source Palm law. -/
theorem sourceMarkCampbell_eq_volume_prod {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (henv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂P, scene.IsSimplePerfectMatching)
    (hstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P) :
    sourceMarkCampbell P = (volume : Measure ℝ).prod (feedbackProjectiveLaw P) := by
  have hp := feedbackProjectiveLaw_isProbability hlam0 hlam P henv hperfect
  have hunit : sourceMarkCampbell P (Ioc 0 1 ×ˢ univ) < ∞ := by
    rw [← unitWindowPalm_apply _ MeasurableSet.univ, sourceMarkCampbell_unitWindow]
    exact measure_lt_top _ _
  rw [← sourceMarkCampbell_unitWindow]
  apply campbell_eq_volume_prod_palm _ _ hunit
  intro t
  apply (measurable_sourceMarkCoordinates.measurePreserving (feedbackSceneEdgeIntensity P)).of_semiconj
    (measurePreserving_feedbackSceneEdgeIntensity P hstat (-t))
  · intro e
    ext <;> simp [MatchingScene.edgeReroot_apply, add_comm]
  · exact (measurable_const.add measurable_fst).prodMk measurable_snd

/-- Any normalized nonnegative continuous source window reads exactly the same actual Palm
mark test as the sharp unit window. -/
theorem lintegral_sourceMarkWindow_eq_projective {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (henv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂P, scene.IsSimplePerfectMatching)
    (hstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P)
    (φ : C_c(ℝ, ℝ)) (hφ : ∀ x, 0 ≤ φ x) (hunit : (∫ x, φ x) = 1)
    (ψ : C(UnitMark × UnitMark, ℝ)) :
    (∫⁻ scene, ∫⁻ e, ENNReal.ofReal (φ e.1.1 * ψ (e.1.2, e.2.2))
      ∂LocalConfiguration.countingMeasure scene.edges ∂P) =
      ∫⁻ m, ENNReal.ofReal (ψ m) ∂feedbackProjectiveLaw P := by
  have hp := feedbackProjectiveLaw_isProbability hlam0 hlam P henv hperfect
  have hN : Measurable (fun scene : MatchingScene ↦ LocalConfiguration.countingMeasure scene.edges) :=
    LocalConfiguration.measurable_countingMeasure.comp measurable_edges
  have hF : Measurable (fun z : ℝ × (UnitMark × UnitMark) ↦ ENNReal.ofReal (φ z.1 * ψ z.2)) :=
    ((φ.continuous.measurable.comp measurable_fst).mul (ψ.measurable.comp measurable_snd)).ennreal_ofReal
  have hE : Measurable (fun e : MatchingPoint × MatchingPoint ↦
      ENNReal.ofReal (φ e.1.1 * ψ (e.1.2, e.2.2))) := hF.comp measurable_sourceMarkCoordinates
  have hφi : Integrable (fun x : ℝ ↦ φ x) volume :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hφnn : (∫⁻ x, ENNReal.ofReal (φ x)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hφi (ae_of_all _ hφ), hunit]
    simp
  rw [← Measure.lintegral_bind hN.aemeasurable hE.aemeasurable]
  change (∫⁻ e, ENNReal.ofReal (φ e.1.1 * ψ (e.1.2, e.2.2)) ∂feedbackSceneEdgeIntensity P) = _
  rw [← lintegral_map hF measurable_sourceMarkCoordinates]
  change (∫⁻ z, ENNReal.ofReal (φ z.1 * ψ z.2) ∂sourceMarkCampbell P) = _
  rw [sourceMarkCampbell_eq_volume_prod hlam0 hlam P henv hperfect hstat,
    lintegral_prod _ hF.aemeasurable]
  simp_rw [ENNReal.ofReal_mul (hφ _), lintegral_const_mul _ (ψ.measurable.ennreal_ofReal)]
  rw [lintegral_mul_const (f := fun x : ℝ ↦ ENNReal.ofReal (φ x)) _
    φ.continuous.measurable.ennreal_ofReal, hφnn, one_mul]

end MatchingScene
end OTSelector.PointProcess

namespace OTSelector.FiniteSample
open PointProcess

variable {n : ℕ} {lam : ℝ} (sample : FiniteSample n) (graph : FeedbackGraph lam)

/-- The genuine original mark-pair average with weights obtained by averaging physical roots. -/
noncomputable def rootAveragedMarks (σ : Assignment n) (φ : C_c(ℝ, ℝ))
    (ψ : UnitMark × UnitMark → ℝ) (a b : ℝ) : ℝ :=
  (b - a)⁻¹ * ∑ i, sourceRootWindowWeight φ a b (sample.sourceIntersection graph i) *
    ψ (sample.sourceMark i, sample.targetMark (σ i))

/-- The original finite mark-pair sum restricted by the actual source-intersection block. -/
noncomputable def sourceBlockMarks (σ : Assignment n) (ψ : UnitMark × UnitMark → ℝ)
    (a b : ℝ) : ℝ :=
  (b - a)⁻¹ * ∑ i, if sample.sourceIntersection graph i ∈ Ioc a b then
    ψ (sample.sourceMark i, sample.targetMark (σ i)) else 0

theorem rootAveragedMarks_nonneg (σ : Assignment n) (φ : C_c(ℝ, ℝ))
    (hφ : ∀ x, 0 ≤ φ x) (ψ : UnitMark × UnitMark → ℝ) (hψ : ∀ m, 0 ≤ ψ m)
    {a b : ℝ} (hab : a ≤ b) : 0 ≤ sample.rootAveragedMarks graph σ φ ψ a b :=
  mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hab)) (Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (sourceRootWindowWeight_nonneg φ hφ a b _) (hψ _))

/-- Finite-sample Campbell/Fubini identity: all marks and partners are the original sample's. -/
theorem lintegral_rootedMatchingSceneLaw_sourceMarkWindow (σ : Assignment n)
    (φ : C_c(ℝ, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
    (ψ : C(UnitMark × UnitMark, ℝ)) (hψ : ∀ m, 0 ≤ ψ m) {a b : ℝ} (hab : a < b) :
    (∫⁻ scene, ∫⁻ e, ENNReal.ofReal (φ e.1.1 * ψ (e.1.2, e.2.2))
      ∂LocalConfiguration.countingMeasure scene.edges ∂sample.rootedMatchingSceneLaw graph σ a b) =
      ENNReal.ofReal (sample.rootAveragedMarks graph σ φ ψ a b) := by
  have hE : Measurable (fun e : MatchingPoint × MatchingPoint ↦
      ENNReal.ofReal (φ e.1.1 * ψ (e.1.2, e.2.2))) :=
    ((φ.continuous.measurable.comp measurable_fst.fst).mul
      (ψ.measurable.comp (measurable_fst.snd.prodMk measurable_snd.snd))).ennreal_ofReal
  have hN : Measurable (fun scene : MatchingScene ↦
      ∫⁻ e, ENNReal.ofReal (φ e.1.1 * ψ (e.1.2, e.2.2))
        ∂LocalConfiguration.countingMeasure scene.edges) :=
    (Measure.measurable_lintegral hE).comp
      (LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_edges)
  rw [sample.lintegral_rootedMatchingSceneLaw graph σ a b _ hN]
  simp_rw [sample.countingMeasure_rootedMatchingScene_edges graph, lintegral_finsetSum_measure,
    lintegral_dirac' _ hE, rootedSourcePoint, rootedTargetPoint]
  rw [lintegral_finsetSum]
  · have heq (i : Fin n) : (∫⁻ z in Ioc a b, ENNReal.ofReal
        (φ (sample.sourceIntersection graph i - z) * ψ (sample.sourceMark i, sample.targetMark (σ i)))) =
        ENNReal.ofReal (sourceRootWindowWeight φ a b (sample.sourceIntersection graph i) *
          ψ (sample.sourceMark i, sample.targetMark (σ i))) := by
      have hi : Integrable (fun z : ℝ ↦ φ (sample.sourceIntersection graph i - z) *
          ψ (sample.sourceMark i, sample.targetMark (σ i))) (volume.restrict (Ioc a b)) :=
        (((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).comp_sub_left _).mul_const _).integrableOn
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun z ↦ mul_nonneg (hφ _) (hψ _)), integral_mul_const]
      rfl
    simp_rw [heq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦
      mul_nonneg (sourceRootWindowWeight_nonneg φ hφ a b _) (hψ _)), rootAveragedMarks,
      ENNReal.ofReal_mul (inv_nonneg.mpr (sub_nonneg.mpr hab.le)), ENNReal.ofReal_inv_of_pos (sub_pos.mpr hab)]
  · intro i _
    exact ((φ.continuous.measurable.comp (measurable_const.sub measurable_id)).mul_const _).ennreal_ofReal

/-- Only genuine source points in the two boundary strips affect the difference between
root-averaged and original block mark sums. -/
theorem abs_rootAveragedMarks_sub_sourceBlockMarks_le (σ : Assignment n)
    (φ : C_c(ℝ, ℝ)) (hφ : ∀ x, 0 ≤ φ x) (hunit : (∫ x, φ x) = 1)
    {A M a b : ℝ} (hA : 0 ≤ A) (_hM : 0 ≤ M) (hab : a ≤ b)
    (hsupport : ∀ z, A < |z| → φ z = 0)
    (ψ : UnitMark × UnitMark → ℝ) (hψ : ∀ m, |ψ m| ≤ M) :
    |sample.rootAveragedMarks graph σ φ ψ a b - sample.sourceBlockMarks graph σ ψ a b| ≤
      (b - a)⁻¹ * M * ∑ i, (if |sample.sourceIntersection graph i - a| ≤ A ∨
        |sample.sourceIntersection graph i - b| ≤ A then (1 : ℝ) else 0) := by
  have heq : sample.rootAveragedMarks graph σ φ ψ a b - sample.sourceBlockMarks graph σ ψ a b =
      (b - a)⁻¹ * ∑ i, (sourceRootWindowWeight φ a b (sample.sourceIntersection graph i) -
        (if sample.sourceIntersection graph i ∈ Ioc a b then 1 else 0)) *
        ψ (sample.sourceMark i, sample.targetMark (σ i)) := by
    rw [rootAveragedMarks, sourceBlockMarks, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [heq, abs_mul, abs_of_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hab))]
  calc
    _ ≤ (b - a)⁻¹ * ∑ i, |(sourceRootWindowWeight φ a b (sample.sourceIntersection graph i) -
        (if sample.sourceIntersection graph i ∈ Ioc a b then 1 else 0)) *
        ψ (sample.sourceMark i, sample.targetMark (σ i))| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (b - a)⁻¹ * ∑ i, (if |sample.sourceIntersection graph i - a| ≤ A ∨
        |sample.sourceIntersection graph i - b| ≤ A then (1 : ℝ) else 0) * M := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (abs_sourceRootWindowWeight_sub_indicator_le φ hφ hunit hA hsupport a b _)
        (hψ _) (abs_nonneg _) (by split_ifs <;> norm_num)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem rootAveragedMarks_sub (σ : Assignment n) (φ : C_c(ℝ, ℝ))
    (ψ χ : UnitMark × UnitMark → ℝ) (a b : ℝ) :
    sample.rootAveragedMarks graph σ φ (fun m ↦ ψ m - χ m) a b =
      sample.rootAveragedMarks graph σ φ ψ a b - sample.rootAveragedMarks graph σ φ χ a b := by
  simp only [rootAveragedMarks, mul_sub, Finset.sum_sub_distrib]

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene
open OTSelector.Matching OTSelector.Limit

/-- Actual compact edge truncations transfer every eventual upper bound on a finite-sample
source mark average. Increasing those truncations retains partners at every finite distance. -/
theorem projective_integral_le_of_rootAveragedMarks_le
    {N : ℕ → ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (sample : ∀ k, FiniteSample (N k)) (graph : ℕ → FeedbackGraph lam)
    (assignment : ∀ k, Assignment (N k)) (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (henv : (ν : Measure MatchingScene).map feedbackSceneEnvironment =
      feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.IsSimplePerfectMatching)
    (hstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) (ν : Measure MatchingScene) ν)
    (φ : C_c(ℝ, ℝ)) (hφ : ∀ x, 0 ≤ φ x) (hunit : (∫ x, φ x) = 1)
    (ψ : C(UnitMark × UnitMark, ℝ)) (hψ : ∀ m, 0 ≤ ψ m)
    {C : ℝ} (hbound : ∀ᶠ k in atTop,
      (sample k).rootAveragedMarks (graph k) (assignment k) φ ψ (a k) (b k) ≤ C) :
    (∫ m, ψ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene)) ≤ C := by
  have hC : 0 ≤ C := by
    obtain ⟨k, hk⟩ := hbound.exists
    exact ((sample k).rootAveragedMarks_nonneg (graph k) (assignment k) φ hφ ψ hψ (hab k).le).trans hk
  have hp := feedbackProjectiveLaw_isProbability hlam0 hlam (ν : Measure MatchingScene) henv hperfect
  have hψi : Integrable ψ (feedbackProjectiveLaw (ν : Measure MatchingScene)) :=
    ψ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ψ)
  have hw : Continuous (fun e : MatchingPoint × MatchingPoint ↦ φ e.1.1 * ψ (e.1.2, e.2.2)) :=
    (φ.continuous.comp continuous_fst.fst).mul
      (ψ.continuous.comp (continuous_fst.snd.prodMk continuous_snd.snd))
  have hw0 (e : MatchingPoint × MatchingPoint) : 0 ≤ φ e.1.1 * ψ (e.1.2, e.2.2) :=
    mul_nonneg (hφ _) (hψ _)
  have hnn : (∫⁻ scene, ∫⁻ e, ENNReal.ofReal (φ e.1.1 * ψ (e.1.2, e.2.2))
      ∂LocalConfiguration.countingMeasure scene.edges ∂(ν : Measure MatchingScene)) ≤ ENNReal.ofReal C := by
    apply lintegral_countingWeight_le_of_compactTest_bounds _ hw hw0
    intro r
    apply lintegral_edgeTest_le_of_tendsto hlim
    filter_upwards [hbound] with k hk
    rw [hlaw k]
    calc
      _ ≤ ∫⁻ scene, ∫⁻ e, ENNReal.ofReal (φ e.1.1 * ψ (e.1.2, e.2.2))
          ∂LocalConfiguration.countingMeasure scene.edges
          ∂(sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k) := by
        apply lintegral_mono
        intro scene
        dsimp only
        rw [LocalConfiguration.lintegral_countingWeight_eq_iSup_test _ hw hw0]
        exact le_iSup (fun r : ℕ ↦ ENNReal.ofReal (LocalConfiguration.testIntegral scene.edges
          (LocalConfiguration.compactWeightTest (fun e : MatchingPoint × MatchingPoint ↦
            φ e.1.1 * ψ (e.1.2, e.2.2)) hw r))) r
      _ = ENNReal.ofReal ((sample k).rootAveragedMarks (graph k) (assignment k) φ ψ (a k) (b k)) :=
        (sample k).lintegral_rootedMatchingSceneLaw_sourceMarkWindow (graph k) (assignment k)
          φ hφ ψ hψ (hab k)
      _ ≤ _ := ENNReal.ofReal_le_ofReal hk
  rw [lintegral_sourceMarkWindow_eq_projective hlam0 hlam (ν : Measure MatchingScene)
    henv hperfect hstat φ hφ hunit ψ,
    ← ofReal_integral_eq_lintegral_ofReal hψi (ae_of_all _ hψ)] at hnn
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hnn

/-- Conservation of actual source-window mass upgrades the compact-test lower bounds to
convergence of every bounded continuous mark-pair test. No empirical mark limit is an input. -/
theorem tendsto_rootAveragedMarks
    {N : ℕ → ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (sample : ∀ k, FiniteSample (N k)) (graph : ℕ → FeedbackGraph lam)
    (assignment : ∀ k, Assignment (N k)) (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (henv : (ν : Measure MatchingScene).map feedbackSceneEnvironment =
      feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.IsSimplePerfectMatching)
    (hstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) (ν : Measure MatchingScene) ν)
    (φ : C_c(ℝ, ℝ)) (hφ : ∀ x, 0 ≤ φ x) (hunit : (∫ x, φ x) = 1)
    (hmass : Tendsto (fun k ↦ (sample k).rootAveragedMarks (graph k) (assignment k) φ
      (fun _ ↦ 1) (a k) (b k)) atTop (𝓝 1))
    (ψ : C(UnitMark × UnitMark, ℝ)) (hψ0 : ∀ m, 0 ≤ ψ m) (hψ1 : ∀ m, ψ m ≤ 1) :
    Tendsto (fun k ↦ (sample k).rootAveragedMarks (graph k) (assignment k) φ ψ (a k) (b k))
      atTop (𝓝 (∫ m, ψ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene))) := by
  have hp := feedbackProjectiveLaw_isProbability hlam0 hlam (ν : Measure MatchingScene) henv hperfect
  have hlower (χ : C(UnitMark × UnitMark, ℝ)) (hχ : ∀ m, 0 ≤ χ m) (c : ℝ)
      (hc : c < ∫ m, χ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene)) :
      ∀ᶠ k in atTop, c < (sample k).rootAveragedMarks (graph k) (assignment k) φ χ (a k) (b k) := by
    by_contra hn
    have hf : ∃ᶠ k in atTop,
        (sample k).rootAveragedMarks (graph k) (assignment k) φ χ (a k) (b k) ≤ c := by
      simpa only [not_eventually, not_lt] using hn
    obtain ⟨s, hs, hseq⟩ := extraction_of_frequently_atTop hf
    have hle := projective_integral_le_of_rootAveragedMarks_le hlam0 hlam
      (fun k ↦ sample (s k)) (fun k ↦ graph (s k)) (fun k ↦ assignment (s k))
      (a ∘ s) (b ∘ s) (fun k ↦ hab (s k)) (fun k ↦ hlaw (s k))
      (hlim.comp hs.tendsto_atTop) henv hperfect hstat φ hφ hunit χ hχ
      (Eventually.of_forall hseq)
    exact (not_le_of_gt hc) hle
  let χ : C(UnitMark × UnitMark, ℝ) := 1 - ψ
  have hχ : ∀ m, 0 ≤ χ m := fun m ↦ sub_nonneg.mpr (hψ1 m)
  have hψi : Integrable ψ (feedbackProjectiveLaw (ν : Measure MatchingScene)) :=
    ψ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace ψ)
  have hχmean : (∫ m, χ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene)) =
      1 - ∫ m, ψ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene) := by
    change (∫ m, 1 - ψ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene)) = _
    rw [integral_sub (integrable_const 1) hψi]
    simp
  have hχavg (k : ℕ) : (sample k).rootAveragedMarks (graph k) (assignment k) φ χ (a k) (b k) =
      (sample k).rootAveragedMarks (graph k) (assignment k) φ (fun _ ↦ 1) (a k) (b k) -
        (sample k).rootAveragedMarks (graph k) (assignment k) φ ψ (a k) (b k) :=
    (sample k).rootAveragedMarks_sub (graph k) (assignment k) φ (fun _ ↦ 1) ψ (a k) (b k)
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact hlower ψ hψ0 c hc
  · intro d hd
    let I := ∫ m, ψ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene)
    let ε := (d - I) / 3
    have hε : 0 < ε := by dsimp [ε, I]; linarith
    have hm := hmass.eventually (gt_mem_nhds (show (1 : ℝ) < 1 + ε by linarith))
    have hlow := hlower χ hχ (1 - I - ε) (by rw [hχmean]; dsimp [I]; linarith)
    filter_upwards [hm, hlow] with k hk hkχ
    rw [hχavg] at hkχ
    dsimp [ε] at hk hkχ
    change (sample k).rootAveragedMarks (graph k) (assignment k) φ ψ (a k) (b k) < d
    linarith

/-- The original physical source-block mark average converges to the actual projective law.
The only counting inputs are the original source density and the vanishing normalized number
of sources in fixed-width boundary strips. -/
theorem tendsto_sourceBlockMarks
    {N : ℕ → ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (sample : ∀ k, FiniteSample (N k)) (graph : ℕ → FeedbackGraph lam)
    (assignment : ∀ k, Assignment (N k)) (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (henv : (ν : Measure MatchingScene).map feedbackSceneEnvironment =
      feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.IsSimplePerfectMatching)
    (hstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) (ν : Measure MatchingScene) ν)
    (φ : C_c(ℝ, ℝ)) (hφ : ∀ x, 0 ≤ φ x) (hunit : (∫ x, φ x) = 1)
    {A : ℝ} (hA : 0 ≤ A) (hsupport : ∀ z, A < |z| → φ z = 0)
    (hcount : Tendsto (fun k ↦ (sample k).sourceBlockMarks (graph k) (assignment k)
      (fun _ ↦ 1) (a k) (b k)) atTop (𝓝 1))
    (hboundary : Tendsto (fun k ↦ (b k - a k)⁻¹ * ∑ i,
      (if |(sample k).sourceIntersection (graph k) i - a k| ≤ A ∨
        |(sample k).sourceIntersection (graph k) i - b k| ≤ A then (1 : ℝ) else 0)) atTop (𝓝 0))
    (ψ : C(UnitMark × UnitMark, ℝ)) (hψ0 : ∀ m, 0 ≤ ψ m) (hψ1 : ∀ m, ψ m ≤ 1) :
    Tendsto (fun k ↦ (sample k).sourceBlockMarks (graph k) (assignment k) ψ (a k) (b k))
      atTop (𝓝 (∫ m, ψ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene))) := by
  have herr (χ : UnitMark × UnitMark → ℝ) (hχ : ∀ m, |χ m| ≤ 1) :
      Tendsto (fun k ↦ (sample k).rootAveragedMarks (graph k) (assignment k) φ χ (a k) (b k) -
        (sample k).sourceBlockMarks (graph k) (assignment k) χ (a k) (b k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hboundary
    intro k
    simpa only [Real.norm_eq_abs, mul_one] using
      (sample k).abs_rootAveragedMarks_sub_sourceBlockMarks_le (graph k) (assignment k)
        φ hφ hunit hA (by norm_num : (0 : ℝ) ≤ 1) (hab k).le hsupport χ hχ
  have hmass : Tendsto (fun k ↦ (sample k).rootAveragedMarks (graph k) (assignment k) φ
      (fun _ ↦ 1) (a k) (b k)) atTop (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using (herr (fun _ ↦ 1) (by simp)).add hcount
  have hweighted := tendsto_rootAveragedMarks hlam0 hlam sample graph assignment a b hab
    hlaw hlim henv hperfect hstat φ hφ hunit hmass ψ hψ0 hψ1
  have hdiff := herr ψ (fun m ↦ by rw [abs_of_nonneg (hψ0 m)]; exact hψ1 m)
  simpa only [sub_sub_cancel, sub_zero] using hweighted.sub hdiff

/-- Direct finite-sample readout for every continuous real mark test. The observation window
is constructed internally, so only source block density and unit-width boundary counts remain. -/
theorem tendsto_empiricalSourceBlockMarks
    {N : ℕ → ℕ} {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (sample : ∀ k, FiniteSample (N k)) (graph : ℕ → FeedbackGraph lam)
    (assignment : ∀ k, Assignment (N k)) (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (henv : (ν : Measure MatchingScene).map feedbackSceneEnvironment =
      feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.IsSimplePerfectMatching)
    (hstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) (ν : Measure MatchingScene) ν)
    (hcount : Tendsto (fun k ↦ (sample k).sourceBlockMarks (graph k) (assignment k)
      (fun _ ↦ 1) (a k) (b k)) atTop (𝓝 1))
    (hboundary : Tendsto (fun k ↦ (b k - a k)⁻¹ * ∑ i,
      (if |(sample k).sourceIntersection (graph k) i - a k| ≤ 1 ∨
        |(sample k).sourceIntersection (graph k) i - b k| ≤ 1 then (1 : ℝ) else 0)) atTop (𝓝 0))
    (ψ : C(UnitMark × UnitMark, ℝ)) :
    Tendsto (fun k ↦ (sample k).sourceBlockMarks (graph k) (assignment k) ψ (a k) (b k))
      atTop (𝓝 (∫ m, ψ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene))) := by
  obtain ⟨φ, hφ, hunit, hsupport⟩ := exists_unit_sourceObservationWindow
  let M : ℝ := 1 + ‖ψ‖
  have hM : 0 < M := by dsimp [M]; positivity
  let χ : C(UnitMark × UnitMark, ℝ) :=
    ⟨fun m ↦ (ψ m + M) / (2 * M), (ψ.continuous.add continuous_const).div_const _⟩
  have hnorm (m : UnitMark × UnitMark) : |ψ m| ≤ ‖ψ‖ := ψ.norm_coe_le_norm m
  have hχ0 (m : UnitMark × UnitMark) : 0 ≤ χ m := by
    change 0 ≤ (ψ m + M) / (2 * M)
    apply div_nonneg _ (by positivity)
    have := (abs_le.mp (hnorm m)).1
    dsimp [M]
    linarith
  have hχ1 (m : UnitMark × UnitMark) : χ m ≤ 1 := by
    change (ψ m + M) / (2 * M) ≤ 1
    apply (div_le_iff₀ (by positivity : 0 < 2 * M)).mpr
    have := (abs_le.mp (hnorm m)).2
    dsimp [M]
    linarith
  have hχeq (m : UnitMark × UnitMark) : ψ m = 2 * M * χ m - M := by
    change ψ m = 2 * M * ((ψ m + M) / (2 * M)) - M
    field_simp
    ring
  have hc := tendsto_sourceBlockMarks hlam0 hlam sample graph assignment a b hab
    hlaw hlim henv hperfect hstat φ hφ hunit (by norm_num : (0 : ℝ) ≤ 1) hsupport
    hcount hboundary χ hχ0 hχ1
  have hblock (k : ℕ) : (sample k).sourceBlockMarks (graph k) (assignment k) ψ (a k) (b k) =
      (2 * M) * (sample k).sourceBlockMarks (graph k) (assignment k) χ (a k) (b k) -
        M * (sample k).sourceBlockMarks (graph k) (assignment k) (fun _ ↦ 1) (a k) (b k) := by
    simp only [FiniteSample.sourceBlockMarks]
    have hsum : (∑ i, if (sample k).sourceIntersection (graph k) i ∈ Ioc (a k) (b k) then
        ψ ((sample k).sourceMark i, (sample k).targetMark (assignment k i)) else 0) =
        2 * M * (∑ i, if (sample k).sourceIntersection (graph k) i ∈ Ioc (a k) (b k) then
          χ ((sample k).sourceMark i, (sample k).targetMark (assignment k i)) else 0) -
        M * (∑ i, if (sample k).sourceIntersection (graph k) i ∈ Ioc (a k) (b k) then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs
      · simpa only [mul_one] using hχeq ((sample k).sourceMark i, (sample k).targetMark (assignment k i))
      · ring
    rw [hsum]
    ring
  have hp := feedbackProjectiveLaw_isProbability hlam0 hlam (ν : Measure MatchingScene) henv hperfect
  have hχi : Integrable χ (feedbackProjectiveLaw (ν : Measure MatchingScene)) :=
    χ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace χ)
  have hmean : (∫ m, ψ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene)) =
      (2 * M) * (∫ m, χ m ∂feedbackProjectiveLaw (ν : Measure MatchingScene)) - M := by
    rw [integral_congr_ae (ae_of_all _ hχeq), integral_sub (hχi.const_mul _) (integrable_const M),
      integral_const_mul]
    simp
  have hh := (hc.const_mul (2 * M)).sub (hcount.const_mul M)
  simpa only [mul_one, ← hblock, ← hmean] using hh

end OTSelector.PointProcess.MatchingScene
