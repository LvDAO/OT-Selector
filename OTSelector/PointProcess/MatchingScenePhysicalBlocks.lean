import OTSelector.PointProcess.MatchingSceneEmpiricalMarks
import OTSelector.Feedback.FeedbackFGL2

/-!
# Physical block counts from the original global VC event

For the same stopped graph used by FGL2, the actual global VC event and the pathwise I4 bound
force unit source density on every fixed interior macroscopic block. Sources in fixed-width
boundary strips have vanishing normalized count. No additional empirical LLN is assumed.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators Topology NNReal

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.FiniteSample

variable {n : ℕ} {lam : ℝ} (sample : FiniteSample n) (graph : FeedbackGraph lam)

/-- The actual source intersection differs from its original rank height by at most the
uniform graph envelope. -/
theorem abs_sourceIntersection_sub_rankHeight_le {G : ℝ}
    (hgraph : ∀ x, |graph.curve x| ≤ G) (i : Fin n) :
    |sample.sourceIntersection graph i - (n : ℝ) * sample.sourceHeight i| ≤ G := by
  have hi := sample.sourceIntersection_spec graph i
  change (n : ℝ) * sample.sourceHeight i +
    sample.sourceSlope i * graph.curve (sample.sourceIntersection graph i) = _ at hi
  rw [show sample.sourceIntersection graph i - (n : ℝ) * sample.sourceHeight i =
    sample.sourceSlope i * graph.curve (sample.sourceIntersection graph i) by linarith,
    abs_mul, abs_of_nonneg (sample.sourceSlope_mem i).1]
  have hG : 0 ≤ G := (abs_nonneg (graph.curve 0)).trans (hgraph 0)
  exact (mul_le_mul_of_nonneg_left (hgraph _) (sample.sourceSlope_mem i).1).trans
    (by simpa using mul_le_mul_of_nonneg_right (sample.sourceSlope_mem i).2 hG)

/-- Half-space VC control is the cumulative count estimate for the actual graph intersections. -/
theorem abs_sourceIntersectionCount_sub_cut_le {q G x : ℝ} (hn : 0 < n)
    (hgood : sample ∈ feedbackA2GlobalCutGoodEvent q n)
    (hgraph : ∀ y, |graph.curve y| ≤ G) (hx0 : G ≤ x) (hxn : x + G ≤ n) :
    |(sample.sourceIntersectionCount graph x : ℝ) - x| ≤
      (q + 32) * Real.sqrt n + G / 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hG : 0 ≤ G := (abs_nonneg (graph.curve x)).trans (hgraph x)
  have hsections (u : UnitMark) : |graph.curve x * (1 - (u : ℝ))| ≤ G := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr u.property.2)]
    exact (mul_le_mul_of_nonneg_right (hgraph x)
      (sub_nonneg.mpr u.property.2)).trans (by nlinarith [u.property.1])
  have hmass := RelativeVC.rankStripLaw_real_sourceCut (p := graph.curve x) hnR
    (fun u ↦ by linarith [(abs_le.mp (hsections u)).2])
    (fun u ↦ by linarith [(abs_le.mp (hsections u)).1])
  have hdef := (RelativeVC.abs_sourceCutDefect_le_globalSourceCutSup
    (rankStripLaw n : Measure (ℝ × UnitMark)) (feedbackSourceRankArray sample)
    (graph.curve x) x).trans (feedbackA2GlobalCutGoodEvent.source_bound hgood)
  rw [RelativeVC.sourceCutDefect, hmass, mul_div_cancel₀ _ hnR.ne'] at hdef
  change |RelativeVC.sourceCutCount (fun i ↦ sample.rankSourcePoint i)
    (graph.curve x) x - (x - graph.curve x / 2)| ≤ _ at hdef
  rw [← sample.sourceIntersectionCount_cast_eq_sourceCutCount graph x] at hdef
  calc
    |(sample.sourceIntersectionCount graph x : ℝ) - x| ≤
        |(sample.sourceIntersectionCount graph x : ℝ) - (x - graph.curve x / 2)| +
          |graph.curve x / 2| := by
      have heq : (sample.sourceIntersectionCount graph x : ℝ) - x =
          ((sample.sourceIntersectionCount graph x : ℝ) - (x - graph.curve x / 2)) -
            graph.curve x / 2 := by ring
      rw [heq]
      exact abs_sub _ _
    _ ≤ (q + 32) * Real.sqrt n + G / 2 := by
      apply add_le_add hdef
      simpa only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
        div_le_div_of_nonneg_right (hgraph x) (by norm_num : (0 : ℝ) ≤ 2)

/-- A finite interval count is the exact difference of its cumulative counts. -/
theorem sum_sourceBlockIndicator_eq {a b : ℝ} (hab : a ≤ b) :
    (∑ i, if sample.sourceIntersection graph i ∈ Ioc a b then (1 : ℝ) else 0) =
      (sample.sourceIntersectionCount graph b : ℝ) -
        sample.sourceIntersectionCount graph a := by
  have hcount (x : ℝ) : (sample.sourceIntersectionCount graph x : ℝ) =
      ∑ i, if sample.sourceIntersection graph i ≤ x then (1 : ℝ) else 0 := by
    simp only [sourceIntersectionCount, Nat.cast_sum, Finset.card_filter]
    simp
  rw [hcount, hcount, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mem_Ioc]
  split_ifs <;> simp_all <;> linarith

/-- Cumulative errors give the actual interval-count error without assumptions on labels or ties. -/
theorem abs_sum_sourceBlockIndicator_sub_length_le {a b E : ℝ} (hab : a ≤ b)
    (ha : |(sample.sourceIntersectionCount graph a : ℝ) - a| ≤ E)
    (hb : |(sample.sourceIntersectionCount graph b : ℝ) - b| ≤ E) :
    |(∑ i, if sample.sourceIntersection graph i ∈ Ioc a b then (1 : ℝ) else 0) -
      (b - a)| ≤ 2 * E := by
  rw [sample.sum_sourceBlockIndicator_eq graph hab]
  calc
    |(sample.sourceIntersectionCount graph b : ℝ) - sample.sourceIntersectionCount graph a -
        (b - a)| = |((sample.sourceIntersectionCount graph b : ℝ) - b) -
          ((sample.sourceIntersectionCount graph a : ℝ) - a)| := by congr 1; ring
    _ ≤ |(sample.sourceIntersectionCount graph b : ℝ) - b| +
        |(sample.sourceIntersectionCount graph a : ℝ) - a| := abs_sub _ _
    _ ≤ 2 * E := by linarith

/-- A closed unit-width boundary strip fits in a half-open interval of length three. -/
theorem sum_sourceBoundaryIndicator_le {c E : ℝ}
    (ha : |(sample.sourceIntersectionCount graph (c - 2) : ℝ) - (c - 2)| ≤ E)
    (hb : |(sample.sourceIntersectionCount graph (c + 1) : ℝ) - (c + 1)| ≤ E) :
    (∑ i, if |sample.sourceIntersection graph i - c| ≤ 1 then (1 : ℝ) else 0) ≤
      3 + 2 * E := by
  have hle : (∑ i, if |sample.sourceIntersection graph i - c| ≤ 1 then (1 : ℝ) else 0) ≤
      ∑ i, if sample.sourceIntersection graph i ∈ Ioc (c - 2) (c + 1) then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi hj hj
    · exact le_rfl
    · exfalso
      have hh := abs_le.mp hi
      exact hj ⟨by linarith [hh.1], by linarith [hh.2]⟩
    · norm_num
    · exact le_rfl
  have herr := sample.abs_sum_sourceBlockIndicator_sub_length_le graph
    (by linarith : c - 2 ≤ c + 1) ha hb
  linarith [(abs_le.mp herr).2]

/-- Both boundary strips are bounded by the sum of their individual counts. -/
theorem sum_sourceBoundaryUnionIndicator_le {a b E : ℝ}
    (ha : |(sample.sourceIntersectionCount graph (a - 2) : ℝ) - (a - 2)| ≤ E)
    (ha' : |(sample.sourceIntersectionCount graph (a + 1) : ℝ) - (a + 1)| ≤ E)
    (hb : |(sample.sourceIntersectionCount graph (b - 2) : ℝ) - (b - 2)| ≤ E)
    (hb' : |(sample.sourceIntersectionCount graph (b + 1) : ℝ) - (b + 1)| ≤ E) :
    (∑ i, if |sample.sourceIntersection graph i - a| ≤ 1 ∨
      |sample.sourceIntersection graph i - b| ≤ 1 then (1 : ℝ) else 0) ≤ 6 + 4 * E := by
  have hle : (∑ i, if |sample.sourceIntersection graph i - a| ≤ 1 ∨
      |sample.sourceIntersection graph i - b| ≤ 1 then (1 : ℝ) else 0) ≤
      (∑ i, if |sample.sourceIntersection graph i - a| ≤ 1 then (1 : ℝ) else 0) +
        ∑ i, if |sample.sourceIntersection graph i - b| ≤ 1 then (1 : ℝ) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> simp_all
  linarith [sample.sum_sourceBoundaryIndicator_le graph ha ha',
    sample.sum_sourceBoundaryIndicator_le graph hb hb']

end OTSelector.FiniteSample

namespace OTSelector

/-- The elementary normalization used by all physical block errors. -/
theorem tendsto_sqrt_nat_div_nat :
    Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ) / n) atTop (𝓝 0) := by
  have heq (n : ℕ) : Real.sqrt (n : ℝ) / n = (Real.sqrt (n : ℝ))⁻¹ := by
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hs : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
      field_simp
      exact Real.sq_sqrt (Nat.cast_nonneg n)
  simp_rw [heq]
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Every fixed interior macroscopic window and its unit boundary strips lie inside the
population formula's valid region for the actual square-root I4 envelope. -/
theorem eventually_feedbackFGL2_physicalBlock_geometry {amplitude u v : ℝ}
    (hu : 0 < u) (hv : v < 1) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧
      amplitude * Real.sqrt n / 8 ≤ (n : ℝ) * u - 2 ∧
      (n : ℝ) * v + 2 + amplitude * Real.sqrt n / 8 ≤ n := by
  have hlim : Tendsto (fun n : ℕ ↦ (amplitude * Real.sqrt n / 8 + 2) / n)
      atTop (𝓝 0) := by
    have h1 := tendsto_sqrt_nat_div_nat.const_mul (amplitude / 8)
    have h2 := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 : ℝ)
    have heq : (fun n : ℕ ↦ (amplitude * Real.sqrt n / 8 + 2) / n) =
        (fun n : ℕ ↦ amplitude / 8 * (Real.sqrt n / n) + 2 * (n : ℝ)⁻¹) := by
      funext n
      ring
    rw [heq]
    simpa only [Function.comp_def, mul_zero, add_zero] using h1.add h2
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    hlim.eventually (gt_mem_nhds hu), hlim.eventually (gt_mem_nhds (sub_pos.mpr hv))]
    with n hn hleft hright
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hl := (div_lt_iff₀ hnR).mp hleft
  have hr := (div_lt_iff₀ hnR).mp hright
  exact ⟨hn, by linarith, by nlinarith⟩

namespace FiniteSample

/-- Actual FGL2 graph cumulative counts on a fixed interior block, uniformly in its cuts. -/
theorem eventually_feedbackFGL2_physicalBlock_cumulative_bound
    {lam amplitude q u v : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hamp : 0 < amplitude) (hu : 0 < u) (hv : v < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ sample : FiniteSample n,
      sample.NoFeedbackTies lam (amplitude * Real.sqrt n) 0 →
      sample ∈ feedbackA2GlobalCutGoodEvent q n →
      ∀ x ∈ Icc ((n : ℝ) * u - 2) ((n : ℝ) * v + 2),
        |(sample.sourceIntersectionCount
          (sample.feedbackFGL2Graph hlam0 hlamHalf amplitude) x : ℝ) - x| ≤
            (q + 32 + amplitude / 16) * Real.sqrt n := by
  filter_upwards [eventually_feedbackFGL2_physicalBlock_geometry (amplitude := amplitude) hu hv]
    with n hn
  intro sample hNoTie hgood x hx
  have hgraph : ∀ x, |(sample.feedbackFGL2Graph hlam0 hlamHalf amplitude).curve x| ≤
      amplitude * Real.sqrt n / 8 := by
    intro x
    exact sample.abs_stoppedContinuationFeedbackGraph_curve_le hlam0 hlamHalf _
      (mul_pos hamp (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn.1))) _ hNoTie x
  have h := sample.abs_sourceIntersectionCount_sub_cut_le
    (sample.feedbackFGL2Graph hlam0 hlamHalf amplitude) hn.1 hgood hgraph
    (hn.2.1.trans hx.1) (by linarith [hx.2, hn.2.2])
  convert h using 1
  ring

/-- The source block density and its normalized unit-boundary count converge on actual
FGL2 graphs. The assumptions are the original VC good event and the original no-tie event. -/
theorem tendsto_feedbackFGL2_sourceBlock_counts
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (sample : ∀ k, FiniteSample (N k))
    {lam amplitude q u v : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hamp : 0 < amplitude) (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hNoTie : ∀ k, (sample k).NoFeedbackTies lam (amplitude * Real.sqrt (N k)) 0)
    (hgood : ∀ k, sample k ∈ feedbackA2GlobalCutGoodEvent q (N k))
    (assignment : ∀ k, Assignment (N k)) :
    Tendsto (fun k ↦ (sample k).sourceBlockMarks
      ((sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude) (assignment k)
      (fun _ ↦ 1) ((N k : ℝ) * u) ((N k : ℝ) * v)) atTop (𝓝 1) ∧
    Tendsto (fun k ↦ ((N k : ℝ) * v - (N k : ℝ) * u)⁻¹ * ∑ i,
      (if |(sample k).sourceIntersection
          ((sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude) i - (N k : ℝ) * u| ≤ 1 ∨
        |(sample k).sourceIntersection
          ((sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude) i - (N k : ℝ) * v| ≤ 1
        then (1 : ℝ) else 0)) atTop (𝓝 0) := by
  let E (k : ℕ) := (q + 32 + amplitude / 16) * Real.sqrt (N k)
  let W (k : ℕ) := (N k : ℝ) * v - (N k : ℝ) * u
  have hEW : Tendsto (fun k ↦ E k / W k) atTop (𝓝 0) := by
    have h := (tendsto_sqrt_nat_div_nat.comp hN).const_mul
      ((q + 32 + amplitude / 16) / (v - u))
    convert h using 1
    · funext k
      dsimp [E, W]
      simp only [← mul_sub, div_eq_mul_inv, mul_inv_rev]
      ring
    · simp
  have hIW : Tendsto (fun k ↦ (W k)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hN)).mul_const (v - u)⁻¹
    convert h using 1
    · funext k
      dsimp [W]
      rw [← mul_sub, mul_inv_rev]
      ring
    · simp
  have hev := hN.eventually (eventually_feedbackFGL2_physicalBlock_cumulative_bound
    (q := q) hlam0 hlamHalf hamp hu hv)
  have hpositive := hN.eventually (eventually_gt_atTop (0 : ℕ))
  have hbound : ∀ᶠ k in atTop,
      |(sample k).sourceBlockMarks ((sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude)
        (assignment k) (fun _ ↦ 1) ((N k : ℝ) * u) ((N k : ℝ) * v) - 1| ≤
          2 * (E k / W k) ∧
      ((N k : ℝ) * v - (N k : ℝ) * u)⁻¹ * ∑ i,
        (if |(sample k).sourceIntersection
            ((sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude) i - (N k : ℝ) * u| ≤ 1 ∨
          |(sample k).sourceIntersection
            ((sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude) i - (N k : ℝ) * v| ≤ 1
          then (1 : ℝ) else 0) ≤ 6 * (W k)⁻¹ + 4 * (E k / W k) := by
    filter_upwards [hev, hpositive] with k hk hn
    have hnR : 0 < (N k : ℝ) := by exact_mod_cast hn
    have hw : 0 < W k := by dsimp [W]; nlinarith
    let graph := (sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude
    have hc (x : ℝ) (hx : x ∈ Icc ((N k : ℝ) * u - 2) ((N k : ℝ) * v + 2)) :
        |((sample k).sourceIntersectionCount graph x : ℝ) - x| ≤ E k :=
      hk (sample k) (hNoTie k) (hgood k) x hx
    have hab : (N k : ℝ) * u ≤ (N k : ℝ) * v :=
      mul_le_mul_of_nonneg_left huv.le hnR.le
    have hm := (sample k).abs_sum_sourceBlockIndicator_sub_length_le graph hab
      (hc _ ⟨by linarith, by linarith⟩) (hc _ ⟨by linarith, by linarith⟩)
    have hb := (sample k).sum_sourceBoundaryUnionIndicator_le graph
      (a := (N k : ℝ) * u) (b := (N k : ℝ) * v)
      (hc _ ⟨le_rfl, by linarith⟩) (hc _ ⟨by linarith, by linarith⟩)
      (hc _ ⟨by linarith, by linarith⟩) (hc _ ⟨by linarith, by linarith⟩)
    constructor
    · change |(W k)⁻¹ * (∑ i, if (sample k).sourceIntersection graph i ∈
          Ioc ((N k : ℝ) * u) ((N k : ℝ) * v) then (1 : ℝ) else 0) - 1| ≤ _
      rw [show (W k)⁻¹ * (∑ i, if (sample k).sourceIntersection graph i ∈
          Ioc ((N k : ℝ) * u) ((N k : ℝ) * v) then (1 : ℝ) else 0) - 1 =
        ((∑ i, if (sample k).sourceIntersection graph i ∈
          Ioc ((N k : ℝ) * u) ((N k : ℝ) * v) then (1 : ℝ) else 0) - W k) / W k by
            field_simp]
      rw [abs_div, abs_of_pos hw]
      exact (div_le_div_of_nonneg_right hm hw.le).trans_eq (by ring)
    · have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hw.le)
      exact hh.trans_eq (by ring)
  constructor
  · have hz : Tendsto (fun k ↦ (sample k).sourceBlockMarks
        ((sample k).feedbackFGL2Graph hlam0 hlamHalf amplitude) (assignment k) (fun _ ↦ 1)
        ((N k : ℝ) * u) ((N k : ℝ) * v) - 1) atTop (𝓝 0) := by
      apply squeeze_zero_norm' (hbound.mono fun k hk ↦ hk.1)
      simpa using hEW.const_mul 2
    simpa only [sub_add_cancel, zero_add] using hz.add_const 1
  · refine squeeze_zero' ?_ (hbound.mono fun k hk ↦ hk.2) ?_
    · filter_upwards [] with k
      exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr
        (mul_le_mul_of_nonneg_left huv.le (Nat.cast_nonneg (N k)))))
          (Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num)
    · simpa using (hIW.const_mul 6).add (hEW.const_mul 4)

/-- The original graph-intersection block mark average follows from actual scene convergence:
its two counting inputs are now consequences of the original finite-sample good events. -/
theorem tendsto_feedbackFGL2_sourceBlockMarks
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
    (hperfect : ∀ᵐ scene ∂(ν : Measure PointProcess.MatchingScene),
      scene.IsSimplePerfectMatching)
    (hstat : ∀ t : ℝ, MeasurePreserving (PointProcess.MatchingScene.reroot t)
      (ν : Measure PointProcess.MatchingScene) ν)
    (ψ : C(UnitMark × UnitMark, ℝ)) :
    Tendsto (fun k ↦ (sample k).sourceBlockMarks
      ((sample k).feedbackFGL2Graph hlam0.le hlamHalf amplitude) (assignment k) ψ
      ((N k : ℝ) * u) ((N k : ℝ) * v)) atTop
      (𝓝 (∫ m, ψ m ∂Matching.feedbackProjectiveLaw (ν : Measure PointProcess.MatchingScene))) := by
  obtain ⟨hcount, hboundary⟩ := tendsto_feedbackFGL2_sourceBlock_counts hN sample
    hlam0.le hlamHalf hamp hu huv hv hNoTie hgood assignment
  exact PointProcess.MatchingScene.tendsto_empiricalSourceBlockMarks hlam0 hlamHalf sample
    (fun k ↦ (sample k).feedbackFGL2Graph hlam0.le hlamHalf amplitude) assignment
    (fun k ↦ (N k : ℝ) * u) (fun k ↦ (N k : ℝ) * v)
    (fun k ↦ mul_lt_mul_of_pos_left huv (Nat.cast_pos.mpr (hNpos k)))
    hlaw hlim henv hperfect hstat hcount hboundary ψ

end FiniteSample
end OTSelector
