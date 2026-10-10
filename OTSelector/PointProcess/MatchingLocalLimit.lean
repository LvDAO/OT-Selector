import OTSelector.PointProcess.LocalConfigurationAtomLimit
import OTSelector.PointProcess.FiniteMatchingScene
import OTSelector.Gauge.GraphFeedbackLocalization
import OTSelector.Gauge.LocalLimitCost
import Mathlib.Logic.Equiv.Fintype

/-!
# Finite permutation replacements and local limits of the actual optimizer

Finite atom correspondence supplies genuine optimizer edges.  A permutation of their
targets extends to a permutation of the original finite assignment, and the exact
row/column gauge preserves its optimality.
-/

open Function Set Filter Topology
open scoped BigOperators Classical ENNReal

namespace OTSelector

/-- A finite permutation of targets on selected rows is an admissible competitor for
the original full assignment.  The complement is kept fixed by an actual extended permutation. -/
theorem OptimalAssignment.finite_replacement
    {n : ℕ} {J : Type*} [Fintype J] {cost : Fin n → Fin n → ℝ}
    {sigma : Assignment n} (hopt : OptimalAssignment cost sigma)
    (selected : J ↪ Fin n) (tau : Equiv.Perm J) :
    (∑ j, cost (selected j) (sigma (selected j))) ≤
      ∑ j, cost (selected j) (sigma (selected (tau j))) := by
  let P := tau.viaFintypeEmbedding selected
  have hglobal := hopt (P.trans sigma)
  have hdiff : assignmentCost cost (P.trans sigma) - assignmentCost cost sigma =
      ∑ j, (cost (selected j) (sigma (selected (tau j))) -
        cost (selected j) (sigma (selected j))) := by
    unfold assignmentCost
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ i ∈ Finset.univ.image selected,
          (cost i ((P.trans sigma) i) - cost i (sigma i)) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hnot : i ∉ range selected := by simpa using hi
        have hPi : P i = i := tau.viaFintypeEmbedding_apply_notMem_range selected hnot
        simp [Equiv.trans_apply, hPi]
      _ = _ := by
        rw [Finset.sum_image (by exact selected.injective.injOn)]
        apply Finset.sum_congr rfl
        intro j _
        simp [P, Equiv.trans_apply]
  rw [Finset.sum_sub_distrib] at hdiff
  linarith

namespace PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {base : X}

/-- Nonzero multiplicity in an actual finite tuple means that one of its labels is present. -/
theorem multiplicity_ofTuple_ne_zero_iff {n : ℕ} (points : Fin n → X) (x : X) :
    multiplicity (ofTuple base points) x ≠ 0 ↔ ∃ i, points i = x := by
  have heq := countingMeasure_singleton (ofTuple base points) x
  rw [countingMeasure_ofTuple, MeasureTheory.Measure.finsetSum_apply] at heq
  have hz : (multiplicity (ofTuple base points) x : ℝ≥0∞) = 0 ↔
      ∀ i, points i ≠ x := by
    rw [← heq]
    rw [Finset.sum_eq_zero_iff]
    simp only [Finset.mem_univ, forall_const]
    apply forall_congr'
    intro i
    by_cases hi : points i = x <;>
      simp [MeasureTheory.Measure.dirac_apply', hi]
  simpa only [Nat.cast_eq_zero, not_forall, not_not] using not_congr hz

section Proper

variable [ProperSpace X]

noncomputable local instance matchingLocalLimitTopology :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base

/-- Corresponding limit atoms in genuine finite clouds come from distinct original labels.
The original cloud size may vary, and no labeling correspondence is assumed. -/
theorem exists_finite_tuple_atoms_tendsto
    {ι J : Type*} [Finite J] {l : Filter ι} {N : ι → ℕ}
    {cloud : (k : ι) → Fin (N k) → X} {limit : LocalConfiguration base}
    (hc : Tendsto (fun k ↦ ofTuple base (cloud k)) l (𝓝 limit))
    {points : J → X} (hinj : Injective points)
    (hsimple : ∀ j, multiplicity limit (points j) = 1) :
    ∃ approx : ι → J → X, (∀ j, Tendsto (fun k ↦ approx k j) l (𝓝 (points j))) ∧
      ∀ᶠ k in l, ∃ selected : J ↪ Fin (N k), ∀ j, cloud k (selected j) = approx k j := by
  obtain ⟨p, hp, hgood⟩ := exists_finite_atoms_tendsto hc hinj hsimple
  refine ⟨p, hp, hgood.mono ?_⟩
  intro k hk
  have hex (j : J) : ∃ i, cloud k i = p k j := by
    apply (multiplicity_ofTuple_ne_zero_iff (cloud k) (p k j)).1
    rw [hk.2 j]
    norm_num
  choose selected hs using hex
  have hi : Injective selected := by
    intro i j hij
    apply hk.1
    rw [← hs i, ← hs j, hij]
  exact ⟨⟨selected, hi⟩, hs⟩

end Proper

end PointProcess.LocalConfiguration

namespace FiniteSample

/-- The actual Euclidean optimizer obeys every finite replacement inequality after rooting
and rescaling its exact feedback gauge. -/
theorem euclideanOptimizer_local_replacement
    {n : ℕ} (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)
    (hn : 0 < n) {J : Type*} [Fintype J] (selected : J ↪ Fin n)
    (tau : Equiv.Perm J) (root : ℝ) :
    (∑ j, localEuclideanCost n (graph.curve root / n)
      (fun x ↦ graph.curve (root + x) - graph.curve root)
      (sample.sourceIntersection graph (selected j) - root)
      (sample.targetIntersection graph (sample.euclideanOptimizer (selected j)) - root)
      (sample.sourceSlope (selected j))
      (sample.targetSlope (sample.euclideanOptimizer (selected j)))) ≤
    ∑ j, localEuclideanCost n (graph.curve root / n)
      (fun x ↦ graph.curve (root + x) - graph.curve root)
      (sample.sourceIntersection graph (selected j) - root)
      (sample.targetIntersection graph (sample.euclideanOptimizer (selected (tau j))) - root)
      (sample.sourceSlope (selected j))
      (sample.targetSlope (sample.euclideanOptimizer (selected (tau j)))) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hopt := feedbackGaugedOptimizer sample
    (sample.normalizedSourceIntersectionOfGraph graph)
    (sample.normalizedTargetIntersectionOfGraph graph) (normalizedCurveOfGraph graph n)
    (normalizedCurveOfGraph_continuous graph hn)
    (sample.normalizedSourceIntersectionOfGraph_equation graph hn)
    (sample.normalizedTargetIntersectionOfGraph_equation graph hn)
    sample.euclideanOptimizer_isOptimal
  have hreplace := hopt.finite_replacement selected tau
  have hscaled := mul_le_mul_of_nonneg_left hreplace (sq_nonneg (n : ℝ))
  simp only [Finset.mul_sum] at hscaled
  have hnorm : normalizedCurveOfGraph graph n =
      (fun z ↦ graph.curve ((n : ℝ) * z) / n) := rfl
  simp only [feedbackGaugedCost, hnorm, normalizedSourceIntersectionOfGraph,
    normalizedTargetIntersectionOfGraph] at hscaled
  simp_rw [localEuclideanCost_eq_rooted_gauge hnR]
  have hcancel (x : ℝ) : root + (x - root) = x := by ring
  simpa only [hcancel] using hscaled

end FiniteSample

namespace PointProcess

/-- The quadratic gauge for physical source and target marks. -/
noncomputable def markedQuadraticCost (g : ℝ → ℝ) (source target : MatchingPoint) : ℝ :=
  quadraticCost g source.1 target.1 (1 - source.2) (1 + target.2)

/-- The actual rescaled Euclidean gauge for physical source and target marks. -/
noncomputable def markedLocalEuclideanCost (n h : ℝ) (g : ℝ → ℝ)
    (source target : MatchingPoint) : ℝ :=
  localEuclideanCost n h g source.1 target.1 (1 - source.2) (1 + target.2)

private def costParameters (source target : MatchingPoint) : ℝ × ℝ × ℝ × ℝ :=
  (source.1, target.1, 1 - source.2, 1 + target.2)

private theorem costParameters_mem_window {W : ℝ} (source target : MatchingPoint)
    (hs : source.1 ∈ Icc (-W) W) (ht : target.1 ∈ Icc (-W) W) :
    costParameters source target ∈ localCostWindow W := by
  refine ⟨hs, ht, ?_, ?_⟩
  · constructor <;> dsimp [costParameters] <;>
      linarith [source.2.property.1, source.2.property.2]
  · constructor <;> dsimp [costParameters] <;>
      linarith [target.2.property.1, target.2.property.2]

/-- Evaluating the actual cost on convergent marked vertices needs only the geometric graph
convergence assumptions already present in the uniform gauge theorem. -/
theorem tendsto_markedLocalEuclideanCost
    {ι : Type*} {l : Filter ι} {n h : ι → ℝ} {g : ι → ℝ → ℝ}
    {G : ℝ → ℝ} {W M lam : ℝ} {s t : ι → MatchingPoint} {s0 t0 : MatchingPoint}
    (hn : Tendsto n l atTop) (hh : Tendsto h l (𝓝 0))
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hg : ∀ k, Continuous (g k)) (hG : Continuous G)
    (hLip : ∀ k, ScalarLipschitz lam (g k))
    (hgM : ∀ k x, x ∈ Icc (-W) W → |g k x| ≤ M)
    (hGM : ∀ x ∈ Icc (-W) W, |G x| ≤ M)
    (hconv : TendstoUniformlyOn g G l (Icc (-W) W))
    (hs : Tendsto s l (𝓝 s0)) (ht : Tendsto t l (𝓝 t0))
    (hsW : s0.1 ∈ Ioo (-W) W) (htW : t0.1 ∈ Ioo (-W) W) :
    Tendsto (fun k ↦ markedLocalEuclideanCost (n k) (h k) (g k) (s k) (t k))
      l (𝓝 (markedQuadraticCost G s0 t0)) := by
  have hparam : Continuous (fun p : MatchingPoint × MatchingPoint ↦
      costParameters p.1 p.2) := by unfold costParameters; fun_prop
  have hp := (hparam.tendsto (s0, t0)).comp (hs.prodMk_nhds ht)
  have hpw : Tendsto (fun k ↦ costParameters (s k) (t k))
      l (𝓝[localCostWindow W] (costParameters s0 t0)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨hp, ?_⟩
    filter_upwards [hs.fst_nhds.eventually (Ioo_mem_nhds hsW.1 hsW.2),
      ht.fst_nhds.eventually (Ioo_mem_nhds htW.1 htW.2)] with k hsk htk
    exact costParameters_mem_window (s k) (t k) ⟨hsk.1.le, hsk.2.le⟩ ⟨htk.1.le, htk.2.le⟩
  exact tendsto_localEuclideanCost_of_vertices
    (p := fun k ↦ costParameters (s k) (t k)) (q := costParameters s0 t0)
    hn hh hW hM hlam0 hlam hg hG hLip hgM hGM hconv
    (costParameters_mem_window s0 t0 ⟨hsW.1.le, hsW.2.le⟩ ⟨htW.1.le, htW.2.le⟩) hpw

noncomputable local instance matchingLocalLimitEdgeTopology :
    TopologicalSpace (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueTopology _

/-- Local optimality passes from the original Euclidean optimizers to every finite family
of distinct simple limit edges.  Original finite labels are recovered from vague convergence;
neither an atom correspondence nor a limiting optimality assertion is assumed. -/
theorem quadratic_finite_replacement_of_rootedEuclideanScene_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot] {N : ι → ℕ}
    (sample : (k : ι) → FiniteSample (N k)) {lam : ℝ}
    (graph : ι → FeedbackGraph lam) (root : ι → ℝ)
    {limit : LocalConfiguration (matchingPointBase, matchingPointBase)}
    (hscene : Tendsto (fun k ↦ ((sample k).rootedEuclideanScene (graph k) (root k)).edges)
      l (𝓝 limit))
    {m : ℕ} {edges : Fin m → MatchingPoint × MatchingPoint}
    (hinj : Injective edges) (hsimple : ∀ j, LocalConfiguration.multiplicity limit (edges j) = 1)
    {G : ℝ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8) (hG : Continuous G)
    (hscale : Tendsto (fun k ↦ (N k : ℝ)) l atTop)
    (hheight : Tendsto (fun k ↦ (graph k).curve (root k) / N k) l (𝓝 0))
    (hgraph : TendstoUniformlyOn
      (fun k x ↦ (graph k).curve (root k + x) - (graph k).curve (root k))
      G l (Icc (-W) W))
    (hinside : ∀ j, (edges j).1.1 ∈ Ioo (-W) W ∧ (edges j).2.1 ∈ Ioo (-W) W)
    (tau : Equiv.Perm (Fin m)) :
    (∑ j, markedQuadraticCost G (edges j).1 (edges j).2) ≤
      ∑ j, markedQuadraticCost G (edges j).1 (edges (tau j)).2 := by
  let g (k : ι) (x : ℝ) := (graph k).curve (root k + x) - (graph k).curve (root k)
  let cloud (k : ι) (i : Fin (N k)) :=
    ((sample k).rootedSourcePoint (graph k) (root k) i,
      (sample k).rootedTargetPoint (graph k) (root k) ((sample k).euclideanOptimizer i))
  have hc : Tendsto (fun k ↦ LocalConfiguration.ofTuple
      (matchingPointBase, matchingPointBase) (cloud k)) l (𝓝 limit) := hscene
  obtain ⟨approx, happrox, hselected⟩ :=
    LocalConfiguration.exists_finite_tuple_atoms_tendsto hc hinj hsimple
  have hLip (k : ι) : ScalarLipschitz lam (g k) := by
    intro x y
    have hh := (graph k).lipschitz (root k + x) (root k + y)
    simpa only [g, sub_sub_sub_cancel_right, add_sub_add_left_eq_sub] using hh
  have hg (k : ι) : Continuous (g k) := by
    have hh : LipschitzWith (Real.toNNReal lam) (g k) := by
      apply LipschitzWith.of_dist_le'
      intro x y
      simpa only [Real.dist_eq, Real.toNNReal_of_nonneg hlam0, abs_sub_comm] using hLip k x y
    exact hh.continuous
  have hgM (k : ι) (x : ℝ) (hx : x ∈ Icc (-W) W) : |g k x| ≤ lam * W := by
    have hh := hLip k 0 x
    have hz : g k 0 = 0 := by simp [g]
    rw [hz, sub_zero, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (abs_le.2 hx) hlam0)
  have hGM (x : ℝ) (hx : x ∈ Icc (-W) W) : |G x| ≤ lam * W :=
    le_of_tendsto ((hgraph.tendsto_at hx).abs) (Eventually.of_forall (fun k ↦ hgM k x hx))
  have hlim (i j : Fin m) :
      Tendsto (fun k ↦ markedLocalEuclideanCost (N k)
        ((graph k).curve (root k) / N k) (g k) (approx k i).1 (approx k j).2)
        l (𝓝 (markedQuadraticCost G (edges i).1 (edges j).2)) :=
    tendsto_markedLocalEuclideanCost hscale hheight hW (mul_nonneg hlam0 hW)
      hlam0 hlam hg hG hLip hgM hGM hgraph
      (happrox i).fst_nhds (happrox j).snd_nhds (hinside i).1 (hinside j).2
  have hineq : ∀ᶠ k in l,
      (∑ j, markedLocalEuclideanCost (N k) ((graph k).curve (root k) / N k)
        (g k) (approx k j).1 (approx k j).2) ≤
      ∑ j, markedLocalEuclideanCost (N k) ((graph k).curve (root k) / N k)
        (g k) (approx k j).1 (approx k (tau j)).2 := by
    filter_upwards [hselected, hscale.eventually_gt_atTop 0] with k ⟨selected, hs⟩ hnk
    have hn : 0 < N k := by exact_mod_cast hnk
    have hf := (sample k).euclideanOptimizer_local_replacement
      (graph k) hn selected tau (root k)
    change (∑ j, markedLocalEuclideanCost (N k) ((graph k).curve (root k) / N k)
      (g k) (cloud k (selected j)).1 (cloud k (selected j)).2) ≤
      ∑ j, markedLocalEuclideanCost (N k) ((graph k).curve (root k) / N k)
      (g k) (cloud k (selected j)).1 (cloud k (selected (tau j))).2 at hf
    simpa only [hs] using hf
  exact le_of_tendsto_of_tendsto (tendsto_finsetSum _ (fun j _ ↦ hlim j j))
    (tendsto_finsetSum _ (fun j _ ↦ hlim j (tau j))) hineq

end PointProcess

end OTSelector
