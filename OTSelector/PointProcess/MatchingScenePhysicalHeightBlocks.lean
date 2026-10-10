import OTSelector.PointProcess.MatchingScenePhysicalBlocks

/-!
# Replacing graph blocks by the original physical height blocks

The exact intersection displacement and the same global VC event bound the labels whose block
membership changes. Their original heights lie in two shrinking boundary strips. The resulting
error vanishes for every bounded mark test, without another empirical-law hypothesis.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators Topology NNReal

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector

private def zeroBlockGraph : FeedbackGraph 0 where
  curve := fun _ ↦ 0
  lam_nonneg := le_rfl
  lam_lt_half := by norm_num
  lipschitz := by intro x y; simp

namespace FiniteSample

private theorem sourceIntersection_zeroBlockGraph {n : ℕ} (sample : FiniteSample n) (i : Fin n) :
    sample.sourceIntersection zeroBlockGraph i = (n : ℝ) * sample.sourceHeight i := by
  have h := sample.sourceIntersection_spec zeroBlockGraph i
  simpa [sourcePhase, zeroBlockGraph] using h.symm

/-- The original mark-pair average whose source height belongs to a physical interval. -/
noncomputable def sourceHeightBlockMarks {n : ℕ} (sample : FiniteSample n) (σ : Assignment n)
    (ψ : UnitMark × UnitMark → ℝ) (u v : ℝ) : ℝ :=
  ((n : ℝ) * (v - u))⁻¹ * ∑ i, if (sample.sourceHeight i : ℝ) ∈ Ioc u v then
    ψ (sample.sourceMark i, sample.targetMark (σ i)) else 0

private theorem sourceHeightBlockMarks_eq_zeroBlockGraph {n : ℕ} (sample : FiniteSample n)
    (hn : 0 < n) (σ : Assignment n) (ψ : UnitMark × UnitMark → ℝ) (u v : ℝ) :
    sample.sourceHeightBlockMarks σ ψ u v =
      sample.sourceBlockMarks zeroBlockGraph σ ψ ((n : ℝ) * u) ((n : ℝ) * v) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  simp only [sourceHeightBlockMarks, sourceBlockMarks, sourceIntersection_zeroBlockGraph,
    mem_Ioc, mul_lt_mul_iff_right₀ hnR, mul_le_mul_iff_right₀ hnR, mul_sub]

private theorem near_boundary_of_membership_ne {x y a b G : ℝ} (hxy : |x - y| ≤ G)
    (hne : ¬(x ∈ Ioc a b ↔ y ∈ Ioc a b)) : |y - a| ≤ G ∨ |y - b| ≤ G := by
  have hxy' := abs_le.mp hxy
  by_cases hx : x ∈ Ioc a b
  · have hy : y ∉ Ioc a b := fun hy ↦ hne ⟨fun _ ↦ hy, fun _ ↦ hx⟩
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hy
    rcases hy with hy | hy
    · left; rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    · right; rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  · have hy : y ∈ Ioc a b := by
      by_contra hy
      exact hne (iff_of_false hx hy)
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · left; rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    · right; rw [abs_le]; constructor <;> linarith [hy.1, hy.2]

/-- Only labels within the coordinate displacement of the original block boundaries can
contribute to the difference of two genuine block sums. -/
theorem abs_sourceBlockMarks_sub_le_boundary_count {n : ℕ} {lam lam' : ℝ}
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (base : FeedbackGraph lam')
    (σ : Assignment n) {G M a b : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hclose : ∀ i, |sample.sourceIntersection graph i - sample.sourceIntersection base i| ≤ G)
    (ψ : UnitMark × UnitMark → ℝ) (hψ : ∀ m, |ψ m| ≤ M) :
    |sample.sourceBlockMarks base σ ψ a b - sample.sourceBlockMarks graph σ ψ a b| ≤
      (b - a)⁻¹ * M * ∑ i,
        (if |sample.sourceIntersection base i - a| ≤ G ∨
          |sample.sourceIntersection base i - b| ≤ G then (1 : ℝ) else 0) := by
  rw [sourceBlockMarks, sourceBlockMarks, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul, abs_of_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hab))]
  calc
    _ ≤ (b - a)⁻¹ * ∑ i, |(if sample.sourceIntersection base i ∈ Ioc a b then
        ψ (sample.sourceMark i, sample.targetMark (σ i)) else 0) -
      (if sample.sourceIntersection graph i ∈ Ioc a b then
        ψ (sample.sourceMark i, sample.targetMark (σ i)) else 0)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (b - a)⁻¹ * ∑ i, M *
        (if |sample.sourceIntersection base i - a| ≤ G ∨
          |sample.sourceIntersection base i - b| ≤ G then (1 : ℝ) else 0) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      by_cases hnear : |sample.sourceIntersection base i - a| ≤ G ∨
          |sample.sourceIntersection base i - b| ≤ G
      · rw [ite_eq_left hnear, mul_one]
        split_ifs <;> simp only [sub_self, sub_zero, zero_sub, abs_zero, abs_neg]
        all_goals first | exact hM | exact hψ (sample.sourceMark i, sample.targetMark (σ i))
      · have heq : sample.sourceIntersection graph i ∈ Ioc a b ↔
            sample.sourceIntersection base i ∈ Ioc a b := by
          by_contra hh
          exact hnear (near_boundary_of_membership_ne (hclose i) hh)
        simp only [ite_eq_right hnear, heq, sub_self, abs_zero, mul_zero, le_refl]
    _ = _ := by rw [← Finset.mul_sum]; ring

private theorem sum_boundary_radius_le {n : ℕ} (sample : FiniteSample n)
    (graph : FeedbackGraph 0) {c G D : ℝ} (hG : 0 ≤ G)
    (ha : |(sample.sourceIntersectionCount graph (c - G - 1) : ℝ) - (c - G - 1)| ≤ D)
    (hb : |(sample.sourceIntersectionCount graph (c + G) : ℝ) - (c + G)| ≤ D) :
    (∑ i, if |sample.sourceIntersection graph i - c| ≤ G then (1 : ℝ) else 0) ≤
      2 * G + 1 + 2 * D := by
  have hle : (∑ i, if |sample.sourceIntersection graph i - c| ≤ G then (1 : ℝ) else 0) ≤
      ∑ i, if sample.sourceIntersection graph i ∈ Ioc (c - G - 1) (c + G)
        then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi hj hj
    · exact le_rfl
    · exfalso
      have hh := abs_le.mp hi
      exact hj ⟨by linarith [hh.1], by linarith [hh.2]⟩
    · norm_num
    · exact le_rfl
  have hh := sample.abs_sum_sourceBlockIndicator_sub_length_le graph
    (by linarith : c - G - 1 ≤ c + G) ha hb
  linarith [(abs_le.mp hh).2]

private theorem sum_boundary_radius_union_le {n : ℕ} (sample : FiniteSample n)
    {a b G D : ℝ} (hG : 0 ≤ G)
    (ha : |(sample.sourceIntersectionCount zeroBlockGraph (a - G - 1) : ℝ) -
      (a - G - 1)| ≤ D)
    (ha' : |(sample.sourceIntersectionCount zeroBlockGraph (a + G) : ℝ) - (a + G)| ≤ D)
    (hb : |(sample.sourceIntersectionCount zeroBlockGraph (b - G - 1) : ℝ) -
      (b - G - 1)| ≤ D)
    (hb' : |(sample.sourceIntersectionCount zeroBlockGraph (b + G) : ℝ) - (b + G)| ≤ D) :
    (∑ i, if |sample.sourceIntersection zeroBlockGraph i - a| ≤ G ∨
      |sample.sourceIntersection zeroBlockGraph i - b| ≤ G then (1 : ℝ) else 0) ≤
        4 * G + 2 + 4 * D := by
  have hle : (∑ i, if |sample.sourceIntersection zeroBlockGraph i - a| ≤ G ∨
      |sample.sourceIntersection zeroBlockGraph i - b| ≤ G then (1 : ℝ) else 0) ≤
      (∑ i, if |sample.sourceIntersection zeroBlockGraph i - a| ≤ G then (1 : ℝ) else 0) +
        ∑ i, if |sample.sourceIntersection zeroBlockGraph i - b| ≤ G then (1 : ℝ) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp_all
  linarith [sum_boundary_radius_le sample zeroBlockGraph hG ha ha',
    sum_boundary_radius_le sample zeroBlockGraph hG hb hb']

/-- Uniformly bounded mark tests have vanishing error when the actual graph-intersection block
is replaced by the original physical-height block. -/
theorem tendsto_feedbackFGL2_heightBlock_sub_sourceBlock
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (sample : ∀ k, FiniteSample (N k))
    {lam amplitude q u v : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hamp : 0 < amplitude) (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hNoTie : ∀ k, (sample k).NoFeedbackTies lam (amplitude * Real.sqrt (N k)) 0)
    (hgood : ∀ k, sample k ∈ feedbackA2GlobalCutGoodEvent q (N k))
    (assignment : ∀ k, Assignment (N k)) (ψ : UnitMark × UnitMark → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hψ : ∀ m, |ψ m| ≤ M) :
    Tendsto (fun k ↦ (sample k).sourceHeightBlockMarks (assignment k) ψ u v -
      (sample k).sourceBlockMarks ((sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude)
        (assignment k) ψ ((N k : ℝ) * u) ((N k : ℝ) * v)) atTop (𝓝 0) := by
  let G k := amplitude * Real.sqrt (N k) / 8
  let D k := (q + 32) * Real.sqrt (N k)
  let W k := (N k : ℝ) * v - (N k : ℝ) * u
  have hEW : Tendsto (fun k ↦ (W k)⁻¹ * M * (4 * G k + 2 + 4 * D k)) atTop (𝓝 0) := by
    have h1 := (tendsto_sqrt_nat_div_nat.comp hN).const_mul
      (M * (amplitude / 2 + 4 * (q + 32)) / (v - u))
    have h2 := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hN)).const_mul (2 * M / (v - u))
    convert h1.add h2 using 1
    · funext k
      simp only [G, D, W, Function.comp_def, ← mul_sub, div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  apply squeeze_zero_norm' _ hEW
  filter_upwards [hN.eventually (eventually_feedbackFGL2_physicalBlock_geometry
    (amplitude := amplitude) hu hv)] with k hk
  have hnR : 0 < (N k : ℝ) := by exact_mod_cast hk.1
  have hG : 0 ≤ G k := by dsimp [G]; positivity
  have hw : 0 < W k := by dsimp [W]; nlinarith
  let graph := (sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude
  have hgraph (x : ℝ) : |graph.curve x| ≤ G k :=
    (sample k).abs_stoppedContinuationFeedbackGraph_curve_le hlam0 hlamHalf _
      (mul_pos hamp (Real.sqrt_pos.mpr hnR)) _ (hNoTie k) x
  have hc (x : ℝ) (hx : x ∈ Icc 0 (N k : ℝ)) :
      |((sample k).sourceIntersectionCount zeroBlockGraph x : ℝ) - x| ≤ D k := by
    simpa only [zero_div, add_zero] using (sample k).abs_sourceIntersectionCount_sub_cut_le
      zeroBlockGraph hk.1 (hgood k) (G := 0) (by intro y; simp [zeroBlockGraph])
      hx.1 (by simpa using hx.2)
  have hgu : G k ≤ (N k : ℝ) * u - 2 := hk.2.1
  have hgv : (N k : ℝ) * v + 2 + G k ≤ N k := hk.2.2
  have hab : (N k : ℝ) * u ≤ (N k : ℝ) * v :=
    mul_le_mul_of_nonneg_left huv.le hnR.le
  have hstrip := sum_boundary_radius_union_le (sample k) hG
    (a := (N k : ℝ) * u) (b := (N k : ℝ) * v)
    (hc _ ⟨by linarith, by linarith⟩) (hc _ ⟨by linarith, by linarith⟩)
    (hc _ ⟨by linarith, by linarith⟩) (hc _ ⟨by linarith, by linarith⟩)
  have hclose (i : Fin (N k)) : |(sample k).sourceIntersection graph i -
      (sample k).sourceIntersection zeroBlockGraph i| ≤ G k := by
    rw [sourceIntersection_zeroBlockGraph]
    exact (sample k).abs_sourceIntersection_sub_rankHeight_le graph hgraph i
  rw [Real.norm_eq_abs, sourceHeightBlockMarks_eq_zeroBlockGraph (sample k) hk.1]
  exact ((sample k).abs_sourceBlockMarks_sub_le_boundary_count graph zeroBlockGraph
    (assignment k) hab hM hclose ψ hψ).trans
      (mul_le_mul_of_nonneg_left hstrip (mul_nonneg (inv_nonneg.mpr hw.le) hM))

/-- Actual weak scene convergence identifies the mark average on the original physical-height
block. Both the count limits and the height replacement are proved from the original good events. -/
theorem tendsto_feedbackFGL2_sourceHeightBlockMarks
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (hNpos : ∀ k, 0 < N k)
    (sample : ∀ k, FiniteSample (N k))
    {lam amplitude q u v : ℝ} (hlam0 : 0 < lam) (hlamHalf : lam < 1 / 2)
    (hamp : 0 < amplitude) (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hNoTie : ∀ k, (sample k).NoFeedbackTies lam (amplitude * Real.sqrt (N k)) 0)
    (hgood : ∀ k, sample k ∈ feedbackA2GlobalCutGoodEvent q (N k))
    (assignment : ∀ k, Assignment (N k))
    {μ : ℕ → ProbabilityMeasure PointProcess.MatchingScene}
    {ν : ProbabilityMeasure PointProcess.MatchingScene}
    (hlaw : ∀ k, (μ k : Measure PointProcess.MatchingScene) =
      (sample k).rootedMatchingSceneLaw
        ((sample k).feedbackFGL2Graph hlam0.le hlamHalf amplitude) (assignment k)
        ((N k : ℝ) * u) ((N k : ℝ) * v))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (henv : (ν : Measure PointProcess.MatchingScene).map Matching.feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 hlamHalf)
    (hperfect : ∀ᵐ scene ∂(ν : Measure PointProcess.MatchingScene), scene.IsSimplePerfectMatching)
    (hstat : ∀ t : ℝ, MeasurePreserving (PointProcess.MatchingScene.reroot t)
      (ν : Measure PointProcess.MatchingScene) ν)
    (ψ : C(UnitMark × UnitMark, ℝ)) :
    Tendsto (fun k ↦ (sample k).sourceHeightBlockMarks (assignment k) ψ u v) atTop
      (𝓝 (∫ m, ψ m ∂Matching.feedbackProjectiveLaw (ν : Measure PointProcess.MatchingScene))) := by
  have hd := tendsto_feedbackFGL2_heightBlock_sub_sourceBlock hN sample hlam0.le hlamHalf
    hamp hu huv hv hNoTie hgood assignment ψ (norm_nonneg ψ) (fun m ↦ ψ.norm_coe_le_norm m)
  have hg := tendsto_feedbackFGL2_sourceBlockMarks hN hNpos sample hlam0 hlamHalf
    hamp hu huv hv hNoTie hgood assignment hlaw hlim henv hperfect hstat ψ
  simpa only [sub_add_cancel, zero_add] using hd.add hg

end FiniteSample
end OTSelector
