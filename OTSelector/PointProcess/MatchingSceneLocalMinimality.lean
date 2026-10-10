import OTSelector.PointProcess.MatchingSceneTransportCurrent
import OTSelector.Matching.FeedbackSceneJoiningEnergy
import Mathlib.Topology.ClusterPt

/-!
# Local minimality of actual weak Euclidean-optimizer limits

Closed tail supports of the original finite rooted scenes carry the limiting probability law.
Every point in that support is approached by an actual optimizer net with sample size tending
to infinity. The proved finite replacement and gauge-limit theorem then gives all local
replacement inequalities. No coupling, atom correspondence, or limiting optimality is assumed.
-/

open MeasureTheory Set Function Filter Topology
open scoped BigOperators Classical ENNReal

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance localMinimalityEdgeTopology : TopologicalSpace
    (LocalConfiguration (matchingPointBase, matchingPointBase)) := LocalConfiguration.vagueTopology _

/-- A convergent net of original optimizer scenes inherits all finite quadratic replacements.
The height hypothesis is the normalized absolute finite graph height appearing in the exact
Euclidean gauge, rather than a hypothesis on the limiting matching. -/
theorem locally_minimizing_of_rootedEuclideanScene_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] {N : ι → ℕ}
    (sample : ∀ k, FiniteSample (N k)) {lam : ℝ} (graph : ι → FeedbackGraph lam)
    (root : ι → ℝ) {limit : MatchingScene}
    (hscene : Tendsto (fun k ↦ (sample k).rootedEuclideanScene (graph k) (root k)) l (𝓝 limit))
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hscale : Tendsto (fun k ↦ (N k : ℝ)) l atTop)
    (hheight : Tendsto (fun k ↦ (graph k).curve (root k) / N k) l (𝓝 0))
    (hp : IsSimplePerfectMatching limit) :
    (spatialMatching hp).IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost limit.path.graphHeight i.val j.val) := by
  intro rows tau
  let e : Fin (Fintype.card rows) ≃ rows := (Fintype.equivFin rows).symm
  let edges (i : Fin (Fintype.card rows)) : MatchingPoint × MatchingPoint :=
    ((e i).val.val, (atomAssignment hp (e i).val).val)
  let tau' : Equiv.Perm (Fin (Fintype.card rows)) := (e.trans tau).trans e.symm
  have hinj : Injective edges := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Prod.fst hij
  have hsimple (i : Fin (Fintype.card rows)) : LocalConfiguration.multiplicity limit.edges (edges i) = 1 :=
    Nat.le_antisymm (hp.simple_edges _) (Nat.one_le_iff_ne_zero.mpr (atomAssignment_edge hp _))
  let W : ℝ := 1 + ∑ i, (|(edges i).1.1| + |(edges i).2.1|)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hinside (i : Fin (Fintype.card rows)) :
      (edges i).1.1 ∈ Ioo (-W) W ∧ (edges i).2.1 ∈ Ioo (-W) W := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦
      add_nonneg (abs_nonneg (edges j).1.1) (abs_nonneg (edges j).2.1)) (Finset.mem_univ i)
    have hs : |(edges i).1.1| < W := by dsimp [W]; linarith [abs_nonneg (edges i).2.1]
    have ht : |(edges i).2.1| < W := by dsimp [W]; linarith [abs_nonneg (edges i).1.1]
    exact ⟨abs_lt.mp hs, abs_lt.mp ht⟩
  have hcurve : Tendsto (fun k ↦
      ((sample k).rootedEuclideanScene (graph k) (root k)).path.graphHeight.toContinuousMap)
      l (𝓝 limit.path.graphHeight.toContinuousMap) :=
    (ContinuousMapZero.isEmbedding_toContinuousMap.continuous.tendsto
      limit.path.graphHeight).comp ((continuous_graphHeight.tendsto limit).comp hscene)
  have hg : TendstoUniformlyOn
      (fun k x ↦ (graph k).curve (root k + x) - (graph k).curve (root k))
      limit.path.graphHeight l (Icc (-W) W) := by
    have h := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hcurve
      (Icc (-W) W) isCompact_Icc
    convert h using 1
    · funext k x
      change (graph k).curve (root k + x) - (graph k).curve (root k) =
        (graph k).curve (x + root k) - (graph k).curve (root k)
      rw [add_comm]
    · funext x
      rfl
  have hineq := quadratic_finite_replacement_of_rootedEuclideanScene_tendsto
    sample graph root ((continuous_edges.tendsto limit).comp hscene) hinj hsimple hW
    hlam0 hlam (map_continuous _) hscale hheight hg hinside tau'
  change (∑ i : rows, markedQuadraticCost limit.path.graphHeight i.val.val
      (atomAssignment hp i.val).val) ≤
    ∑ i : rows, markedQuadraticCost limit.path.graphHeight i.val.val
      (atomAssignment hp (tau i).val).val
  rw [← e.sum_comp, ← e.sum_comp]
  simpa only [edges, tau', Equiv.trans_apply, Equiv.apply_symm_apply] using hineq

private abbrev RootIndex (a b : ℕ → ℝ) := {p : ℕ × ℝ // p.2 ∈ Ioc (a p.1) (b p.1)}

private noncomputable def optimizerRootMap {N : ℕ → ℕ} {lam : ℝ}
    (sample : ∀ k, FiniteSample (N k)) (graph : ℕ → FeedbackGraph lam)
    (a b : ℕ → ℝ) (p : RootIndex a b) : MatchingScene :=
  (sample p.val.1).rootedEuclideanScene (graph p.val.1) p.val.2

private def optimizerTailSupport {N : ℕ → ℕ} {lam : ℝ}
    (sample : ∀ k, FiniteSample (N k)) (graph : ℕ → FeedbackGraph lam)
    (a b : ℕ → ℝ) (m : ℕ) : Set MatchingScene :=
  closure (optimizerRootMap sample graph a b '' {p : RootIndex a b | m ≤ p.val.1})

/-- Tail closures yield an actual optimizer net even when the full scene topology has not
been equipped with a global metric. -/
private theorem exists_optimizer_root_filter {N : ℕ → ℕ} {lam : ℝ}
    (sample : ∀ k, FiniteSample (N k)) (graph : ℕ → FeedbackGraph lam)
    (a b : ℕ → ℝ) {scene : MatchingScene}
    (hscene : ∀ m, scene ∈ optimizerTailSupport sample graph a b m) :
    ∃ l : Filter (RootIndex a b), l.NeBot ∧
      Tendsto (fun p ↦ p.val.1) l atTop ∧
      Tendsto (optimizerRootMap sample graph a b) l (𝓝 scene) := by
  let F : Filter (RootIndex a b) := Filter.comap (fun p ↦ p.val.1) atTop
  let f := optimizerRootMap sample graph a b
  have hcluster : ClusterPt scene (Filter.map f F) := by
    have hb := ((atTop_basis.comap (fun p : RootIndex a b ↦ p.val.1)).map f)
    apply hb.clusterPt_iff_forall_mem_closure.mpr
    intro m hm
    exact hscene m
  let l : Filter (RootIndex a b) := F ⊓ Filter.comap f (𝓝 scene)
  have hl : l.NeBot := by
    apply neBot_inf_comap_iff_map.mpr
    simpa only [ClusterPt, inf_comm] using hcluster
  refine ⟨l, hl, ?_, ?_⟩
  · exact tendsto_comap.mono_left inf_le_left
  · exact tendsto_comap.mono_left inf_le_right

private theorem ae_optimizer_tail_support {N : ℕ → ℕ} {lam : ℝ}
    (sample : ∀ k, FiniteSample (N k)) (graph : ℕ → FeedbackGraph lam)
    (a b : ℕ → ℝ)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (sample k).euclideanOptimizer (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene))) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), ∀ m, scene ∈ optimizerTailSupport sample graph a b m := by
  apply ae_all_iff.mpr
  intro m
  have hclosed : IsClosed (optimizerTailSupport sample graph a b m) := isClosed_closure
  rw [ae_iff]
  change (ν : Measure MatchingScene) (optimizerTailSupport sample graph a b m)ᶜ = 0
  apply le_antisymm _ zero_le
  apply measure_compl_closed_le_of_tendsto_of_tight hμ htight hclosed
  filter_upwards [eventually_ge_atTop m] with k hk
  rw [hlaw k, FiniteSample.rootedMatchingSceneLaw, Measure.map_apply
    ((sample k).measurable_rootedMatchingScene (graph k) (sample k).euclideanOptimizer)
    hclosed.measurableSet.compl]
  have hset : (sample k).rootedMatchingScene (graph k) (sample k).euclideanOptimizer ⁻¹'
      (optimizerTailSupport sample graph a b m)ᶜ ∩ Ioc (a k) (b k) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    apply hz.1
    apply subset_closure
    exact ⟨⟨(k, z), hz.2⟩, hk, rfl⟩
  rw [Probability.spatialRootLaw, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply (hclosed.measurableSet.compl.preimage
      ((sample k).measurable_rootedMatchingScene (graph k) (sample k).euclideanOptimizer)),
    hset, measure_empty, smul_zero]

/-- The actual weak limit law is almost surely locally minimizing for the original quadratic
limit gauge. All root values are averaged in their original finite sample; uniform normalized
height control is a deterministic input supplied by the finite feedback bounds. -/
theorem ae_locally_minimizing_of_rootedEuclideanSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (a b : ℕ → ℝ)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (sample k).euclideanOptimizer (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    (hscale : Tendsto (fun k ↦ (N k : ℝ)) atTop atTop)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ z ∈ Ioc (a k) (b k),
      |(graph k).curve z / N k| < ε) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), ∀ hp : IsSimplePerfectMatching scene,
      (spatialMatching hp).IsLocallyMinimizing
        (fun i j ↦ markedQuadraticCost scene.path.graphHeight i.val j.val) := by
  filter_upwards [ae_optimizer_tail_support sample graph a b hlaw hμ htight] with scene hscene hp
  obtain ⟨l, hl, hindex, hscene'⟩ := exists_optimizer_root_filter sample graph a b hscene
  let : l.NeBot := hl
  have hh : Tendsto (fun p : RootIndex a b ↦ (graph p.val.1).curve p.val.2 / N p.val.1)
      l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hindex.eventually (hheight ε hε)] with p hp
    simpa only [Real.dist_eq, sub_zero] using hp p.val.2 p.property
  exact locally_minimizing_of_rootedEuclideanScene_tendsto
    (fun p : RootIndex a b ↦ sample p.val.1) (fun p ↦ graph p.val.1) (fun p ↦ p.val.2)
    hscene' hlam0 hlam (hscale.comp hindex) hh hp

/-- The four actual geometric fields required by the feedback-scene uniqueness argument follow
from a fixed-energy optimizer sequence and the true endpoint environment properties. -/
theorem ae_feedbackSceneEnergyCandidate_of_rootedEuclideanSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (sample k).euclideanOptimizer (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    (hscale : Tendsto (fun k ↦ (N k : ℝ)) atTop atTop)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ z ∈ Ioc (a k) (b k),
      |(graph k).curve z / N k| < ε) {C ρ : ℝ}
    (henergy : ∀ᶠ k in atTop, (∑ i,
      ((sample k).targetIntersection (graph k) ((sample k).euclideanOptimizer i) -
        (sample k).sourceIntersection (graph k) i) ^ 2) ≤ C * (b k - a k))
    (hcount : ∀ᶠ k in atTop, (N k : ℝ) ≤ ρ * (b k - a k))
    (hzero : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      (∀ x : SourceAtom scene, x.val.1 ≠ 0) ∧ (∀ y : TargetAtom scene, y.val.1 ≠ 0))
    (hsimple : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      (∀ p, LocalConfiguration.multiplicity scene.source p ≤ 1) ∧
      (∀ p, LocalConfiguration.multiplicity scene.target p ≤ 1)) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), OTSelector.Matching.FeedbackSceneEnergyCandidate lam scene := by
  have hp := ae_isSimplePerfectMatching_of_rootedMatchingSceneLaw_tendsto
    sample graph (fun k ↦ (sample k).euclideanOptimizer) a b hab hlaw hμ htight henergy hsimple
  have hc := ae_current_eq_currentAt_of_rootedMatchingSceneLaw_tendsto
    sample graph (fun k ↦ (sample k).euclideanOptimizer) a b hab hlaw hμ henergy hcount hzero hsimple
  have hm := ae_locally_minimizing_of_rootedEuclideanSceneLaw_tendsto
    sample graph a b hlam0 hlam hlaw hμ htight hscale hheight
  filter_upwards [hp, hc, hm] with scene hp hc hm
  exact ⟨hp, (hc hp).2, (hc hp).1, hm hp⟩

end OTSelector.PointProcess.MatchingScene
