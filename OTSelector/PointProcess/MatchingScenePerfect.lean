import OTSelector.PointProcess.MatchingSceneTopology
import OTSelector.PointProcess.MatchingLocalLimit
import OTSelector.PointProcess.LocalConfigurationIntegral
import OTSelector.Matching.ZeroCutSurgery

/-!
# Perfectness of actual finite matching limits

Compactly supported edge tests are dominated by endpoint tests for every finite assignment.
This inequality passes through actual vague convergence and controls multiplicities and
uniqueness of partners. Bounded partner sequences then retain their actual matching edges.
-/

open MeasureTheory Set Function Filter Topology
open scoped BigOperators Classical CompactlySupported

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess
namespace LocalConfiguration

/-- Actual finite tuple tests are the finite sum over their original labels, with multiplicities. -/
theorem testIntegral_ofTuple {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} (base : X) (points : Fin n → X) (f : C_c(X, ℝ)) :
    testIntegral (ofTuple base points) f = ∑ i, f (points i) := by
  rw [← integral_countingMeasure, countingMeasure_ofTuple,
    integral_finsetSum_measure (fun i _ ↦ integrable_dirac (by simp))]
  simp only [integral_dirac]

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [ProperSpace X] [ProperSpace Y] {baseX : X} {baseY : Y}

/-- The edge test is compared to an endpoint test only on its compact support. -/
def ProjectedTestDomination (edges : LocalConfiguration baseX)
    (vertices : LocalConfiguration baseY) (π : X → Y) : Prop :=
  ∀ (f : C_c(X, ℝ)) (g : C_c(Y, ℝ)),
    (∀ x, f x ≤ g (π x)) → testIntegral edges f ≤ testIntegral vertices g

/-- Every limit edge multiplicity is bounded by the multiplicity of its actual endpoint. -/
theorem multiplicity_le_of_projectedTestDomination
    {edges : LocalConfiguration baseX} {vertices : LocalConfiguration baseY} {π : X → Y}
    (hπ : ∀ x y, dist (π x) (π y) ≤ dist x y)
    (hdom : ProjectedTestDomination edges vertices π) (x : X) :
    multiplicity edges x ≤ multiplicity vertices (π x) := by
  obtain ⟨r, hr, hiso⟩ := exists_isolating_ball vertices vertices (π x)
  have htest := hdom (distanceTent x r) (distanceTent (π x) r) (fun y ↦ by
    simp only [distanceTent_apply]
    exact max_le_max_left 0 (sub_le_sub_left (hπ y x) r))
  rw [testIntegral_distanceTent_of_isolated vertices hr
    (fun y hy hyx ↦ (hiso y hy hyx).1)] at htest
  have hlo := testSummand_le_testIntegral edges
    (fun y ↦ show 0 ≤ distanceTent x r y from le_max_left _ _) x
  have hx : testSummand edges (distanceTent x r) x = (multiplicity edges x : ℝ) * r := by
    simp [testSummand, hr.le]
  rw [hx] at hlo
  have hmul := hlo.trans htest
  have hreal : (multiplicity edges x : ℝ) ≤ multiplicity vertices (π x) :=
    (mul_le_mul_iff_left₀ hr).mp hmul
  exact_mod_cast hreal

/-- A simple endpoint cannot support two distinct limit edge atoms. -/
theorem injOn_of_projectedTestDomination
    {edges : LocalConfiguration baseX} {vertices : LocalConfiguration baseY} {π : X → Y}
    (hπ : ∀ x y, dist (π x) (π y) ≤ dist x y)
    (hdom : ProjectedTestDomination edges vertices π)
    (hsimple : ∀ y, multiplicity vertices y ≤ 1) :
    Set.InjOn π (support (multiplicity edges)) := by
  intro x hx y hy hxy
  by_contra hne
  have hd : 0 < dist x y := dist_pos.mpr hne
  obtain ⟨R, hR, hiso⟩ := exists_isolating_ball vertices vertices (π x)
  let r := min R (dist x y / 3)
  have hr : 0 < r := lt_min hR (by positivity)
  have hrR : r ≤ R := min_le_left _ _
  have hrd : 2 * r < dist x y := by have := min_le_right R (dist x y / 3); dsimp [r]; linarith
  let f : C_c(X, ℝ) := distanceTent x r + distanceTent y r
  have hf0 (z : X) : 0 ≤ f z := add_nonneg (le_max_left _ _) (le_max_left _ _)
  have hbound (z : X) : f z ≤ distanceTent (π x) r (π z) := by
    have hxπ : distanceTent x r z ≤ distanceTent (π x) r (π z) := by
      simp only [distanceTent_apply]
      exact max_le_max_left 0 (sub_le_sub_left (hπ z x) r)
    have hyπ : distanceTent y r z ≤ distanceTent (π x) r (π z) := by
      rw [hxy]
      simp only [distanceTent_apply]
      exact max_le_max_left 0 (sub_le_sub_left (hπ z y) r)
    by_cases hxz : dist z x < r
    · have hzy : r ≤ dist z y := by
        have ht := dist_triangle x z y
        rw [dist_comm x z] at ht
        linarith
      have hzero : distanceTent y r z = 0 := max_eq_left (sub_nonpos.mpr hzy)
      simpa only [f, CompactlySupportedContinuousMap.add_apply, hzero, add_zero] using hxπ
    · have hzero : distanceTent x r z = 0 := max_eq_left (sub_nonpos.mpr (le_of_not_gt hxz))
      simpa only [f, CompactlySupportedContinuousMap.add_apply, hzero, zero_add] using hyπ
  have hupper := hdom f (distanceTent (π x) r) hbound
  rw [testIntegral_distanceTent_of_isolated vertices hr
    (fun z hz hzx ↦ (hiso z (hz.trans_le hrR) hzx).1)] at hupper
  have hlow := pair_testSummand_le_testIntegral edges hf0 hne
  have hx1 : (1 : ℝ) ≤ multiplicity edges x := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx
  have hy1 : (1 : ℝ) ≤ multiplicity edges y := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hy
  have hfx : r ≤ f x := by
    simp only [f, CompactlySupportedContinuousMap.add_apply, distanceTent_apply, dist_self,
      sub_zero, max_eq_right hr.le]
    linarith [le_max_left (0 : ℝ) (r - dist x y)]
  have hfy : r ≤ f y := by
    simp only [f, CompactlySupportedContinuousMap.add_apply, distanceTent_apply, dist_self,
      sub_zero, max_eq_right hr.le]
    linarith [le_max_left (0 : ℝ) (r - dist y x)]
  have hm : (multiplicity vertices (π x) : ℝ) ≤ 1 := by exact_mod_cast hsimple (π x)
  unfold testSummand at hlow
  nlinarith [mul_le_mul_of_nonneg_right hx1 (hf0 x),
    mul_le_mul_of_nonneg_right hy1 (hf0 y)]

noncomputable local instance perfectConfigTopology : TopologicalSpace (LocalConfiguration baseX) := vagueTopology baseX

/-- A converging sequence of actual atoms cannot disappear at a finite limit point. -/
theorem multiplicity_ne_zero_of_tendsto_atoms
    {ι : Type*} {l : Filter ι} [l.NeBot] {c : ι → LocalConfiguration baseX}
    {limit : LocalConfiguration baseX} (hc : Tendsto c l (𝓝 limit))
    {point : ι → X} {x : X} (hp : Tendsto point l (𝓝 x))
    (ha : ∀ᶠ i in l, multiplicity (c i) (point i) ≠ 0) : multiplicity limit x ≠ 0 := by
  intro hz
  obtain ⟨r, hr, hzero⟩ := eventually_no_atom_near_of_tendsto hc hz
  have hnear := hp.eventually (Metric.ball_mem_nhds x hr)
  have hfalse : ∀ᶠ i in l, False := by
    filter_upwards [ha, hzero, hnear] with i hai hzi hni
    exact hai (hzi _ hni)
  exact hfalse.exists.elim (fun _ hi ↦ hi)

end LocalConfiguration

namespace MatchingScene

noncomputable local instance perfectPointTopology : TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase
noncomputable local instance perfectEdgeTopology : TopologicalSpace
    (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueTopology (matchingPointBase, matchingPointBase)

/-- Endpoint tests dominate edge tests in a genuine finite-assignment limit. -/
theorem source_test_domination_of_rootedMatchingScene_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] {N : ι → ℕ}
    (sample : (k : ι) → FiniteSample (N k)) {lam : ℝ}
    (graph : ι → FeedbackGraph lam) (assignment : (k : ι) → Assignment (N k))
    (root : ι → ℝ) {limit : MatchingScene}
    (hscene : Tendsto (fun k ↦ (sample k).rootedMatchingScene (graph k) (assignment k) (root k))
      l (𝓝 limit)) :
    LocalConfiguration.ProjectedTestDomination limit.edges limit.source Prod.fst := by
  intro f g hfg
  apply le_of_tendsto_of_tendsto
    (((LocalConfiguration.continuous_testIntegral f).comp continuous_edges).tendsto limit |>.comp hscene)
    (((LocalConfiguration.continuous_testIntegral g).comp continuous_source).tendsto limit |>.comp hscene)
  apply Eventually.of_forall
  intro k
  change LocalConfiguration.testIntegral (LocalConfiguration.ofTuple _
    (fun i ↦ ((sample k).rootedSourcePoint (graph k) (root k) i,
      (sample k).rootedTargetPoint (graph k) (root k) (assignment k i)))) f ≤
    LocalConfiguration.testIntegral (LocalConfiguration.ofTuple _
      ((sample k).rootedSourcePoint (graph k) (root k))) g
  rw [LocalConfiguration.testIntegral_ofTuple, LocalConfiguration.testIntegral_ofTuple]
  exact Finset.sum_le_sum (fun i _ ↦ hfg _)

/-- The same limit inequality holds for target tests, using the actual target permutation. -/
theorem target_test_domination_of_rootedMatchingScene_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] {N : ι → ℕ}
    (sample : (k : ι) → FiniteSample (N k)) {lam : ℝ}
    (graph : ι → FeedbackGraph lam) (assignment : (k : ι) → Assignment (N k))
    (root : ι → ℝ) {limit : MatchingScene}
    (hscene : Tendsto (fun k ↦ (sample k).rootedMatchingScene (graph k) (assignment k) (root k))
      l (𝓝 limit)) :
    LocalConfiguration.ProjectedTestDomination limit.edges limit.target Prod.snd := by
  intro f g hfg
  apply le_of_tendsto_of_tendsto
    (((LocalConfiguration.continuous_testIntegral f).comp continuous_edges).tendsto limit |>.comp hscene)
    (((LocalConfiguration.continuous_testIntegral g).comp continuous_target).tendsto limit |>.comp hscene)
  apply Eventually.of_forall
  intro k
  change LocalConfiguration.testIntegral (LocalConfiguration.ofTuple _
    (fun i ↦ ((sample k).rootedSourcePoint (graph k) (root k) i,
      (sample k).rootedTargetPoint (graph k) (root k) (assignment k i)))) f ≤
    LocalConfiguration.testIntegral (LocalConfiguration.ofTuple _
      ((sample k).rootedTargetPoint (graph k) (root k))) g
  rw [LocalConfiguration.testIntegral_ofTuple, LocalConfiguration.testIntegral_ofTuple,
    ← Equiv.sum_comp (assignment k) (fun i ↦ g ((sample k).rootedTargetPoint (graph k) (root k) i))]
  exact Finset.sum_le_sum (fun i _ ↦ hfg _)

/-- Edge atoms occur with multiplicity one, have actual endpoints, and do not share an endpoint. -/
structure IsSimplePartialMatching (scene : MatchingScene) : Prop where
  simple_edges : ∀ e, LocalConfiguration.multiplicity scene.edges e ≤ 1
  endpoints : ∀ e, LocalConfiguration.multiplicity scene.edges e ≠ 0 →
    LocalConfiguration.multiplicity scene.source e.1 ≠ 0 ∧
    LocalConfiguration.multiplicity scene.target e.2 ≠ 0
  source_injective : Set.InjOn Prod.fst (support (LocalConfiguration.multiplicity scene.edges))
  target_injective : Set.InjOn Prod.snd (support (LocalConfiguration.multiplicity scene.edges))

/-- Simple endpoint limits force genuine simple partial matching geometry, without any
assumption about the existence or uniqueness of partners in the limit. -/
theorem isSimplePartialMatching_of_rootedMatchingScene_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] {N : ι → ℕ}
    (sample : (k : ι) → FiniteSample (N k)) {lam : ℝ}
    (graph : ι → FeedbackGraph lam) (assignment : (k : ι) → Assignment (N k))
    (root : ι → ℝ) {limit : MatchingScene}
    (hscene : Tendsto (fun k ↦ (sample k).rootedMatchingScene (graph k) (assignment k) (root k))
      l (𝓝 limit))
    (hsource : ∀ x, LocalConfiguration.multiplicity limit.source x ≤ 1)
    (htarget : ∀ x, LocalConfiguration.multiplicity limit.target x ≤ 1) :
    IsSimplePartialMatching limit := by
  have hs := source_test_domination_of_rootedMatchingScene_tendsto sample graph assignment root hscene
  have ht := target_test_domination_of_rootedMatchingScene_tendsto sample graph assignment root hscene
  have hp₁ (e f : MatchingPoint × MatchingPoint) : dist e.1 f.1 ≤ dist e f := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hp₂ (e f : MatchingPoint × MatchingPoint) : dist e.2 f.2 ≤ dist e f := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hms := LocalConfiguration.multiplicity_le_of_projectedTestDomination hp₁ hs
  have hmt := LocalConfiguration.multiplicity_le_of_projectedTestDomination hp₂ ht
  refine ⟨fun e ↦ (hms e).trans (hsource e.1), ?_,
    LocalConfiguration.injOn_of_projectedTestDomination hp₁ hs hsource,
    LocalConfiguration.injOn_of_projectedTestDomination hp₂ ht htarget⟩
  intro e he
  constructor
  · exact fun hz ↦ he (Nat.eq_zero_of_le_zero (hz ▸ hms e))
  · exact fun hz ↦ he (Nat.eq_zero_of_le_zero (hz ▸ hmt e))

/-- An actual partner remaining in a compact set has a subsequence that survives as a limit edge. -/
theorem exists_partner_of_compact_approx
    {scene : ℕ → MatchingScene} {limit : MatchingScene}
    (hscene : Tendsto scene atTop (𝓝 limit))
    {point : ℕ → MatchingPoint} {x : MatchingPoint} (hp : Tendsto point atTop (𝓝 x))
    {K : Set MatchingPoint} (hK : IsCompact K)
    (hpartner : ∀ᶠ n in atTop, ∃ y ∈ K,
      LocalConfiguration.multiplicity (scene n).edges (point n, y) ≠ 0) :
    ∃ y ∈ K, LocalConfiguration.multiplicity limit.edges (x, y) ≠ 0 := by
  let P (n : ℕ) (y : MatchingPoint) := y ∈ K ∧
    LocalConfiguration.multiplicity (scene n).edges (point n, y) ≠ 0
  let partner (n : ℕ) := if h : ∃ y, P n y then Classical.choose h else matchingPointBase
  have hgood : ∀ᶠ n in atTop, P n (partner n) := by
    filter_upwards [hpartner] with n hn
    dsimp only [partner]
    rw [dite_eq_left hn]
    exact Classical.choose_spec hn
  obtain ⟨y, hy, φ, hφ, hlim⟩ := hK.isSeqCompact.subseq_of_frequently_in
    ((hgood.mono fun _ h ↦ h.1).frequently)
  refine ⟨y, hy, ?_⟩
  apply LocalConfiguration.multiplicity_ne_zero_of_tendsto_atoms
    (((continuous_edges.tendsto limit).comp hscene).comp hφ.tendsto_atTop)
    ((hp.comp hφ.tendsto_atTop).prodMk_nhds hlim)
  exact (hφ.tendsto_atTop.eventually hgood).mono fun _ h ↦ h.2

/-- Bounded physical target coordinates form a genuine compact marked-point set. -/
theorem isCompact_partnerWindow (B : ℝ) :
    IsCompact {y : MatchingPoint | |y.1| ≤ B} := by
  have heq : {y : MatchingPoint | |y.1| ≤ B} = Icc (-B) B ×ˢ (univ : Set UnitMark) := by
    ext y
    simp [abs_le]
  rw [heq]
  exact isCompact_Icc.prod isCompact_univ

/-- A simple source atom retains a partner when its actual finite partners obey a fixed cutoff. -/
theorem exists_source_partner_of_uniform_cutoff
    {N : ℕ → ℕ} (sample : (k : ℕ) → FiniteSample (N k)) {lam : ℝ}
    (graph : ℕ → FeedbackGraph lam) (assignment : (k : ℕ) → Assignment (N k))
    (root : ℕ → ℝ) {limit : MatchingScene}
    (hscene : Tendsto (fun k ↦ (sample k).rootedMatchingScene (graph k) (assignment k) (root k))
      atTop (𝓝 limit)) {x : MatchingPoint}
    (hx : LocalConfiguration.multiplicity limit.source x = 1) {A B : ℝ} (hA : |x.1| < A)
    (hcutoff : ∀ᶠ k in atTop, ∀ i : Fin (N k),
      |((sample k).rootedSourcePoint (graph k) (root k) i).1| < A →
      |((sample k).rootedTargetPoint (graph k) (root k) (assignment k i)).1| ≤ B) :
    ∃ y, LocalConfiguration.multiplicity limit.edges (x, y) ≠ 0 := by
  have hs := (continuous_source.tendsto limit).comp hscene
  obtain ⟨r, hr, point, hp, hlocal⟩ := LocalConfiguration.exists_atom_tendsto_of_simple hs hx
  have hnear : ∀ᶠ k in atTop, |(point k).1| < A :=
    hp.fst_nhds.abs.eventually (gt_mem_nhds hA)
  apply Exists.imp (fun _ h ↦ h.2)
    (exists_partner_of_compact_approx hscene hp (isCompact_partnerWindow B) ?_)
  filter_upwards [hlocal, hnear, hcutoff] with k hk hpk hck
  have hpoint : LocalConfiguration.multiplicity (LocalConfiguration.ofTuple matchingPointBase
      ((sample k).rootedSourcePoint (graph k) (root k))) (point k) ≠ 0 := by
    have hpk1 : LocalConfiguration.multiplicity (LocalConfiguration.ofTuple matchingPointBase
        ((sample k).rootedSourcePoint (graph k) (root k))) (point k) = 1 := hk.2.1
    rw [hpk1]
    norm_num
  obtain ⟨i, hi⟩ := (LocalConfiguration.multiplicity_ofTuple_ne_zero_iff _ _).mp hpoint
  refine ⟨(sample k).rootedTargetPoint (graph k) (root k) (assignment k i), ?_, ?_⟩
  · exact hck i (hi ▸ hpk)
  · apply (LocalConfiguration.multiplicity_ofTuple_ne_zero_iff _ _).mpr
    exact ⟨i, by simp only [hi]⟩

/-- The reverse version retains a source partner of a converging target atom. -/
theorem exists_reverse_partner_of_compact_approx
    {scene : ℕ → MatchingScene} {limit : MatchingScene}
    (hscene : Tendsto scene atTop (𝓝 limit))
    {point : ℕ → MatchingPoint} {x : MatchingPoint} (hp : Tendsto point atTop (𝓝 x))
    {K : Set MatchingPoint} (hK : IsCompact K)
    (hpartner : ∀ᶠ n in atTop, ∃ y ∈ K,
      LocalConfiguration.multiplicity (scene n).edges (y, point n) ≠ 0) :
    ∃ y ∈ K, LocalConfiguration.multiplicity limit.edges (y, x) ≠ 0 := by
  let P (n : ℕ) (y : MatchingPoint) := y ∈ K ∧
    LocalConfiguration.multiplicity (scene n).edges (y, point n) ≠ 0
  let partner (n : ℕ) := if h : ∃ y, P n y then Classical.choose h else matchingPointBase
  have hgood : ∀ᶠ n in atTop, P n (partner n) := by
    filter_upwards [hpartner] with n hn
    dsimp only [partner]
    rw [dite_eq_left hn]
    exact Classical.choose_spec hn
  obtain ⟨y, hy, φ, hφ, hlim⟩ := hK.isSeqCompact.subseq_of_frequently_in
    ((hgood.mono fun _ h ↦ h.1).frequently)
  refine ⟨y, hy, ?_⟩
  apply LocalConfiguration.multiplicity_ne_zero_of_tendsto_atoms
    (((continuous_edges.tendsto limit).comp hscene).comp hφ.tendsto_atTop)
    (hlim.prodMk_nhds (hp.comp hφ.tendsto_atTop))
  exact (hφ.tendsto_atTop.eventually hgood).mono fun _ h ↦ h.2

/-- Fixed actual inverse-partner cutoffs retain a source for each simple target atom. -/
theorem exists_target_partner_of_uniform_cutoff
    {N : ℕ → ℕ} (sample : (k : ℕ) → FiniteSample (N k)) {lam : ℝ}
    (graph : ℕ → FeedbackGraph lam) (assignment : (k : ℕ) → Assignment (N k))
    (root : ℕ → ℝ) {limit : MatchingScene}
    (hscene : Tendsto (fun k ↦ (sample k).rootedMatchingScene (graph k) (assignment k) (root k))
      atTop (𝓝 limit)) {x : MatchingPoint}
    (hx : LocalConfiguration.multiplicity limit.target x = 1) {A B : ℝ} (hA : |x.1| < A)
    (hcutoff : ∀ᶠ k in atTop, ∀ i : Fin (N k),
      |((sample k).rootedTargetPoint (graph k) (root k) i).1| < A →
      |((sample k).rootedSourcePoint (graph k) (root k) ((assignment k).symm i)).1| ≤ B) :
    ∃ y, LocalConfiguration.multiplicity limit.edges (y, x) ≠ 0 := by
  have ht := (continuous_target.tendsto limit).comp hscene
  obtain ⟨r, hr, point, hp, hlocal⟩ := LocalConfiguration.exists_atom_tendsto_of_simple ht hx
  have hnear : ∀ᶠ k in atTop, |(point k).1| < A :=
    hp.fst_nhds.abs.eventually (gt_mem_nhds hA)
  apply Exists.imp (fun _ h ↦ h.2)
    (exists_reverse_partner_of_compact_approx hscene hp (isCompact_partnerWindow B) ?_)
  filter_upwards [hlocal, hnear, hcutoff] with k hk hpk hck
  have hpoint : LocalConfiguration.multiplicity (LocalConfiguration.ofTuple matchingPointBase
      ((sample k).rootedTargetPoint (graph k) (root k))) (point k) ≠ 0 := by
    have hpk1 : LocalConfiguration.multiplicity (LocalConfiguration.ofTuple matchingPointBase
        ((sample k).rootedTargetPoint (graph k) (root k))) (point k) = 1 := hk.2.1
    rw [hpk1]
    norm_num
  obtain ⟨i, hi⟩ := (LocalConfiguration.multiplicity_ofTuple_ne_zero_iff _ _).mp hpoint
  refine ⟨(sample k).rootedSourcePoint (graph k) (root k) ((assignment k).symm i), ?_, ?_⟩
  · exact hck i (hi ▸ hpk)
  · apply (LocalConfiguration.multiplicity_ofTuple_ne_zero_iff _ _).mpr
    exact ⟨(assignment k).symm i, by simp only [Equiv.apply_symm_apply, hi]⟩

/-- A simple perfect matching is read from the actual edge and endpoint atoms. -/
structure IsSimplePerfectMatching (scene : MatchingScene) : Prop extends IsSimplePartialMatching scene where
  source_exists : ∀ x, LocalConfiguration.multiplicity scene.source x ≠ 0 →
    ∃ y, LocalConfiguration.multiplicity scene.edges (x, y) ≠ 0
  target_exists : ∀ y, LocalConfiguration.multiplicity scene.target y ≠ 0 →
    ∃ x, LocalConfiguration.multiplicity scene.edges (x, y) ≠ 0

/-- Actual finite partner cutoffs supply perfectness in a convergent scene sequence. This is
only the deterministic compactness step; probability estimates must supply these cutoffs. -/
theorem isSimplePerfectMatching_of_rootedMatchingScene_tendsto_cutoffs
    {N : ℕ → ℕ} (sample : (k : ℕ) → FiniteSample (N k)) {lam : ℝ}
    (graph : ℕ → FeedbackGraph lam) (assignment : (k : ℕ) → Assignment (N k))
    (root : ℕ → ℝ) {limit : MatchingScene}
    (hscene : Tendsto (fun k ↦ (sample k).rootedMatchingScene (graph k) (assignment k) (root k))
      atTop (𝓝 limit))
    (hsource : ∀ x, LocalConfiguration.multiplicity limit.source x ≤ 1)
    (htarget : ∀ x, LocalConfiguration.multiplicity limit.target x ≤ 1)
    (hcutoff : ∀ A : ℝ, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ i : Fin (N k),
      (|((sample k).rootedSourcePoint (graph k) (root k) i).1| < A →
        |((sample k).rootedTargetPoint (graph k) (root k) (assignment k i)).1| ≤ B) ∧
      (|((sample k).rootedTargetPoint (graph k) (root k) i).1| < A →
        |((sample k).rootedSourcePoint (graph k) (root k) ((assignment k).symm i)).1| ≤ B)) :
    IsSimplePerfectMatching limit := by
  refine { isSimplePartialMatching_of_rootedMatchingScene_tendsto sample graph assignment root
    hscene hsource htarget with source_exists := ?_, target_exists := ?_ }
  · intro x hx
    have hx1 : LocalConfiguration.multiplicity limit.source x = 1 := by
      have := hsource x
      omega
    obtain ⟨B, hB⟩ := hcutoff (|x.1| + 1)
    exact exists_source_partner_of_uniform_cutoff sample graph assignment root hscene hx1
      (by linarith) (hB.mono fun _ h i ↦ (h i).1)
  · intro y hy
    have hy1 : LocalConfiguration.multiplicity limit.target y = 1 := by
      have := htarget y
      omega
    obtain ⟨B, hB⟩ := hcutoff (|y.1| + 1)
    exact exists_target_partner_of_uniform_cutoff sample graph assignment root hscene hy1
      (by linarith) (hB.mono fun _ h i ↦ (h i).2)

/-- Source labels are the actual source atoms, retaining both position and mark. -/
abbrev SourceAtom (scene : MatchingScene) :=
  {x : MatchingPoint // LocalConfiguration.multiplicity scene.source x ≠ 0}

/-- Target labels are the actual target atoms. -/
abbrev TargetAtom (scene : MatchingScene) :=
  {y : MatchingPoint // LocalConfiguration.multiplicity scene.target y ≠ 0}

/-- The unique actual partner of a source atom, chosen from the actual edge configuration. -/
noncomputable def sourcePartner {scene : MatchingScene} (h : IsSimplePerfectMatching scene)
    (x : SourceAtom scene) : TargetAtom scene :=
  ⟨Classical.choose (h.source_exists x x.property),
    (h.endpoints _ (Classical.choose_spec (h.source_exists x x.property))).2⟩

theorem sourcePartner_edge {scene : MatchingScene} (h : IsSimplePerfectMatching scene)
    (x : SourceAtom scene) : LocalConfiguration.multiplicity scene.edges (x.val, (sourcePartner h x).val) ≠ 0 :=
  Classical.choose_spec (h.source_exists x x.property)

/-- Actual edge geometry gives a bijection of actual source and target atoms. -/
noncomputable def atomAssignment {scene : MatchingScene} (h : IsSimplePerfectMatching scene) :
    SourceAtom scene ≃ TargetAtom scene :=
  Equiv.ofBijective (sourcePartner h) (by
    constructor
    · intro x y heq
      apply Subtype.ext
      have he := h.target_injective (sourcePartner_edge h x) (sourcePartner_edge h y)
        (congrArg Subtype.val heq)
      exact congrArg Prod.fst he
    · intro y
      obtain ⟨x, hx⟩ := h.target_exists y y.property
      have hxs := (h.endpoints _ hx).1
      refine ⟨⟨x, hxs⟩, ?_⟩
      apply Subtype.ext
      have he := h.source_injective (sourcePartner_edge h ⟨x, hxs⟩) hx rfl
      exact congrArg Prod.snd he)

/-- The assignment is precisely the scene's edge relation. -/
theorem atomAssignment_edge {scene : MatchingScene} (h : IsSimplePerfectMatching scene)
    (x : SourceAtom scene) :
    LocalConfiguration.multiplicity scene.edges (x.val, (atomAssignment h x).val) ≠ 0 :=
  sourcePartner_edge h x

/-- The actual atom bijection directly supplies the spatial matching used by disagreement paths. -/
noncomputable def spatialMatching {scene : MatchingScene} (h : IsSimplePerfectMatching scene) :
    OTSelector.Matching.SpatialMatching (SourceAtom scene) (TargetAtom scene) where
  source x := x.val.1
  target y := y.val.1
  assignment := atomAssignment h

/-- The endpoint inequalities form a closed set in the actual scene topology. -/
def HasEndpointTestDomination (scene : MatchingScene) : Prop :=
  LocalConfiguration.ProjectedTestDomination scene.edges scene.source Prod.fst ∧
    LocalConfiguration.ProjectedTestDomination scene.edges scene.target Prod.snd

theorem isClosed_hasEndpointTestDomination : IsClosed {scene | HasEndpointTestDomination scene} := by
  have hs : IsClosed {scene : MatchingScene |
      LocalConfiguration.ProjectedTestDomination scene.edges scene.source Prod.fst} := by
    simp only [LocalConfiguration.ProjectedTestDomination, ofPred_forall]
    exact isClosed_iInter fun f ↦ isClosed_iInter fun g ↦ isClosed_iInter fun _ ↦
      isClosed_le ((LocalConfiguration.continuous_testIntegral f).comp continuous_edges)
        ((LocalConfiguration.continuous_testIntegral g).comp continuous_source)
  have ht : IsClosed {scene : MatchingScene |
      LocalConfiguration.ProjectedTestDomination scene.edges scene.target Prod.snd} := by
    simp only [LocalConfiguration.ProjectedTestDomination, ofPred_forall]
    exact isClosed_iInter fun f ↦ isClosed_iInter fun g ↦ isClosed_iInter fun _ ↦
      isClosed_le ((LocalConfiguration.continuous_testIntegral f).comp continuous_edges)
        ((LocalConfiguration.continuous_testIntegral g).comp continuous_target)
  exact hs.inter ht

/-- Every original finite assignment satisfies the closed endpoint inequalities. -/
theorem hasEndpointTestDomination_rootedMatchingScene {n : ℕ} (sample : FiniteSample n)
    {lam : ℝ} (graph : FeedbackGraph lam) (assignment : Assignment n) (root : ℝ) :
    HasEndpointTestDomination (sample.rootedMatchingScene graph assignment root) := by
  exact ⟨source_test_domination_of_rootedMatchingScene_tendsto
    (l := (atTop : Filter ℕ)) (fun _ ↦ sample) (fun _ ↦ graph) (fun _ ↦ assignment)
    (fun _ ↦ root) tendsto_const_nhds,
    target_test_domination_of_rootedMatchingScene_tendsto
    (l := (atTop : Filter ℕ)) (fun _ ↦ sample) (fun _ ↦ graph) (fun _ ↦ assignment)
    (fun _ ↦ root) tendsto_const_nhds⟩

/-- The actual source atom labels are locally finite in physical coordinate. -/
theorem finite_sourceAtoms_window (scene : MatchingScene) (a b : ℝ) :
    {x : SourceAtom scene | x.val.1 ∈ Icc a b}.Finite := by
  have hK : IsCompact (Icc a b ×ˢ (univ : Set UnitMark)) := isCompact_Icc.prod isCompact_univ
  have hfin := (LocalConfiguration.locallyFiniteSupport_multiplicity scene.source).finite_inter_support_of_isCompact hK
  apply (hfin.preimage (Subtype.val_injective.injOn)).subset
  intro x hx
  exact ⟨⟨hx, mem_univ _⟩, x.property⟩

/-- The actual target atom labels have the same physical local finiteness. -/
theorem finite_targetAtoms_window (scene : MatchingScene) (a b : ℝ) :
    {y : TargetAtom scene | y.val.1 ∈ Icc a b}.Finite := by
  have hK : IsCompact (Icc a b ×ˢ (univ : Set UnitMark)) := isCompact_Icc.prod isCompact_univ
  have hfin := (LocalConfiguration.locallyFiniteSupport_multiplicity scene.target).finite_inter_support_of_isCompact hK
  apply (hfin.preimage (Subtype.val_injective.injOn)).subset
  intro y hy
  exact ⟨⟨hy, mem_univ _⟩, y.property⟩

end MatchingScene
end OTSelector.PointProcess
