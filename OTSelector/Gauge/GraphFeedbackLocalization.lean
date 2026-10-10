import OTSelector.Gauge.FeedbackLocalization

/-!
# Feedback localization for an arbitrary finite feedback graph

This module separates the normalized intersection and FGL2 algebra from the particular graph
construction.  It applies equally to the full recursive graph, the deterministic-horizon graph,
and the stopped continuation graph.  The graph chosen by an actual theorem therefore remains
visible in its statement.
-/

open Set
open scoped BigOperators

namespace OTSelector

variable {n : ℕ} {lam : ℝ}

/-- Macroscopic normalization `gamma(z) = graph.curve (n z) / n`. -/
noncomputable def normalizedCurveOfGraph (graph : FeedbackGraph lam) (n : ℕ) : ℝ → ℝ :=
  normalizedGraph (fun _ : ℕ ↦ graph.curve) n

theorem normalizedCurveOfGraph_lipschitz
    (graph : FeedbackGraph lam) (hn : 0 < n) :
    RealLipschitz lam (normalizedCurveOfGraph graph n) := by
  exact normalizedGraph_lipschitz hn graph.lipschitz

theorem normalizedCurveOfGraph_continuous
    (graph : FeedbackGraph lam) (hn : 0 < n) :
    Continuous (normalizedCurveOfGraph graph n) := by
  have hLip : LipschitzWith (Real.toNNReal lam) (normalizedCurveOfGraph graph n) := by
    apply LipschitzWith.of_dist_le'
    intro x y
    simpa only [Real.dist_eq, Real.toNNReal_of_nonneg graph.lam_nonneg, abs_sub_comm] using
      normalizedCurveOfGraph_lipschitz graph hn x y
  exact hLip.continuous

namespace FiniteSample

variable (sample : FiniteSample n)

/-- A source intersection of `graph`, divided by the row size. -/
noncomputable def normalizedSourceIntersectionOfGraph
    (graph : FeedbackGraph lam) (i : Fin n) : ℝ :=
  sample.sourceIntersection graph i / (n : ℝ)

/-- A target intersection of `graph`, divided by the row size. -/
noncomputable def normalizedTargetIntersectionOfGraph
    (graph : FeedbackGraph lam) (j : Fin n) : ℝ :=
  sample.targetIntersection graph j / (n : ℝ)

theorem normalizedSourceIntersectionOfGraph_equation
    (graph : FeedbackGraph lam) (hn : 0 < n) :
    SourceIntersectionEquation sample
      (sample.normalizedSourceIntersectionOfGraph graph)
      (normalizedCurveOfGraph graph n) := by
  intro i
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hspec := sample.sourceIntersection_spec graph i
  unfold normalizedSourceIntersectionOfGraph normalizedCurveOfGraph normalizedGraph rescaleGraph
  rw [show (n : ℝ) * (sample.sourceIntersection graph i / (n : ℝ)) =
      sample.sourceIntersection graph i by field_simp]
  simp only [sourcePhase] at hspec
  field_simp [hnR]
  nlinarith

theorem normalizedTargetIntersectionOfGraph_equation
    (graph : FeedbackGraph lam) (hn : 0 < n) :
    TargetIntersectionEquation sample
      (sample.normalizedTargetIntersectionOfGraph graph)
      (normalizedCurveOfGraph graph n) := by
  intro j
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hspec := sample.targetIntersection_spec graph j
  unfold normalizedTargetIntersectionOfGraph normalizedCurveOfGraph normalizedGraph rescaleGraph
  rw [show (n : ℝ) * (sample.targetIntersection graph j / (n : ℝ)) =
      sample.targetIntersection graph j by field_simp]
  simp only [targetPhase] at hspec
  field_simp [hnR]
  nlinarith

/-- Increasing matching of the normalized source and target intersections of `graph`. -/
noncomputable def graphFeedbackComparisonAssignment
    (graph : FeedbackGraph lam) : Assignment n :=
  increasingAssignment
    (sample.normalizedSourceIntersectionOfGraph graph)
    (sample.normalizedTargetIntersectionOfGraph graph)

/-- Generic normalized finite FGL2 transfer for an explicitly chosen feedback graph. -/
theorem euclideanOptimizer_normalizedGraphEnergy_le
    (graph : FeedbackGraph lam) (hlam : lam < 1 / 8) (hn : 0 < n)
    (hrange : ∀ z, normalizedCurveOfGraph graph n z ∈ Icc (-1 : ℝ) 1)
    (tau : Assignment n) :
    ∑ i, (sample.normalizedTargetIntersectionOfGraph graph (sample.euclideanOptimizer i) -
        sample.normalizedSourceIntersectionOfGraph graph i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
        ∑ i, (sample.normalizedTargetIntersectionOfGraph graph (tau i) -
          sample.normalizedSourceIntersectionOfGraph graph i) ^ 2 := by
  exact feedback_finite_energy_transfer sample
    (sample.normalizedSourceIntersectionOfGraph graph)
    (sample.normalizedTargetIntersectionOfGraph graph)
    (normalizedCurveOfGraph graph n)
    (normalizedCurveOfGraph_continuous graph hn)
    (normalizedCurveOfGraph_lipschitz graph hn)
    graph.lam_nonneg hlam hrange
    (sample.normalizedSourceIntersectionOfGraph_equation graph hn)
    (sample.normalizedTargetIntersectionOfGraph_equation graph hn)
    sample.euclideanOptimizer_isOptimal

/-- Generic normalized FGL2 transfer with increasing graph matching as comparison. -/
theorem euclideanOptimizer_normalizedGraphEnergy_le_increasing
    (graph : FeedbackGraph lam) (hlam : lam < 1 / 8) (hn : 0 < n)
    (hrange : ∀ z, normalizedCurveOfGraph graph n z ∈ Icc (-1 : ℝ) 1) :
    ∑ i, (sample.normalizedTargetIntersectionOfGraph graph (sample.euclideanOptimizer i) -
        sample.normalizedSourceIntersectionOfGraph graph i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
        ∑ i, (sample.normalizedTargetIntersectionOfGraph graph
            (sample.graphFeedbackComparisonAssignment graph i) -
          sample.normalizedSourceIntersectionOfGraph graph i) ^ 2 := by
  exact sample.euclideanOptimizer_normalizedGraphEnergy_le graph hlam hn hrange
    (sample.graphFeedbackComparisonAssignment graph)

/-- Rank-scale generic FGL2 transfer with increasing graph matching as comparison. -/
theorem euclideanOptimizer_graphEnergy_le_increasing
    (graph : FeedbackGraph lam) (hlam : lam < 1 / 8) (hn : 0 < n)
    (hrange : ∀ z, normalizedCurveOfGraph graph n z ∈ Icc (-1 : ℝ) 1) :
    ∑ i, (sample.targetIntersection graph (sample.euclideanOptimizer i) -
        sample.sourceIntersection graph i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
        ∑ i, (sample.targetIntersection graph
            (sample.graphFeedbackComparisonAssignment graph i) -
          sample.sourceIntersection graph i) ^ 2 := by
  have hnormalized :=
    sample.euclideanOptimizer_normalizedGraphEnergy_le_increasing graph hlam hn hrange
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnSq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hnormalized hnSq
  have hoptimizerScale :
      (n : ℝ) ^ 2 *
          ∑ i, (sample.normalizedTargetIntersectionOfGraph graph
                (sample.euclideanOptimizer i) -
              sample.normalizedSourceIntersectionOfGraph graph i) ^ 2 =
        ∑ i, (sample.targetIntersection graph (sample.euclideanOptimizer i) -
          sample.sourceIntersection graph i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [normalizedSourceIntersectionOfGraph, normalizedTargetIntersectionOfGraph,
      div_sub_div_same]
    field_simp [hnR]
  have hcomparisonScale :
      (n : ℝ) ^ 2 *
          ∑ i, (sample.normalizedTargetIntersectionOfGraph graph
                (sample.graphFeedbackComparisonAssignment graph i) -
              sample.normalizedSourceIntersectionOfGraph graph i) ^ 2 =
        ∑ i, (sample.targetIntersection graph
              (sample.graphFeedbackComparisonAssignment graph i) -
            sample.sourceIntersection graph i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [normalizedSourceIntersectionOfGraph, normalizedTargetIntersectionOfGraph,
      div_sub_div_same]
    field_simp [hnR]
  calc
    ∑ i, (sample.targetIntersection graph (sample.euclideanOptimizer i) -
        sample.sourceIntersection graph i) ^ 2 =
        (n : ℝ) ^ 2 *
          ∑ i, (sample.normalizedTargetIntersectionOfGraph graph
                (sample.euclideanOptimizer i) -
              sample.normalizedSourceIntersectionOfGraph graph i) ^ 2 := hoptimizerScale.symm
    _ ≤ (n : ℝ) ^ 2 *
        ((quadraticUpperConstant lam /
            (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
          ∑ i, (sample.normalizedTargetIntersectionOfGraph graph
                (sample.graphFeedbackComparisonAssignment graph i) -
              sample.normalizedSourceIntersectionOfGraph graph i) ^ 2) := hscaled
    _ = (quadraticUpperConstant lam /
          (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
        ∑ i, (sample.targetIntersection graph
              (sample.graphFeedbackComparisonAssignment graph i) -
            sample.sourceIntersection graph i) ^ 2 := by
      calc
        (n : ℝ) ^ 2 *
            ((quadraticUpperConstant lam /
                (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
              ∑ i, (sample.normalizedTargetIntersectionOfGraph graph
                    (sample.graphFeedbackComparisonAssignment graph i) -
                  sample.normalizedSourceIntersectionOfGraph graph i) ^ 2) =
            (quadraticUpperConstant lam /
                (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
              ((n : ℝ) ^ 2 *
                ∑ i, (sample.normalizedTargetIntersectionOfGraph graph
                      (sample.graphFeedbackComparisonAssignment graph i) -
                    sample.normalizedSourceIntersectionOfGraph graph i) ^ 2) := by ring
        _ = _ := by rw [hcomparisonScale]

/-- Insert an actual comparison-energy bound into the generic rank-scale transfer. -/
theorem euclideanOptimizer_graphEnergy_le_of_comparisonEnergy
    (graph : FeedbackGraph lam) {C : ℝ} (hlam : lam < 1 / 8) (hn : 0 < n)
    (hrange : ∀ z, normalizedCurveOfGraph graph n z ∈ Icc (-1 : ℝ) 1)
    (hcomparison :
      ∑ i, (sample.targetIntersection graph
            (sample.graphFeedbackComparisonAssignment graph i) -
          sample.sourceIntersection graph i) ^ 2 ≤ C * (n : ℝ)) :
    ∑ i, (sample.targetIntersection graph (sample.euclideanOptimizer i) -
        sample.sourceIntersection graph i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) * (C * (n : ℝ)) := by
  have htransfer := sample.euclideanOptimizer_graphEnergy_le_increasing graph hlam hn hrange
  have hupper0 : 0 ≤ quadraticUpperConstant lam := by
    dsimp [quadraticUpperConstant]
    nlinarith [graph.lam_nonneg]
  have hlower0 : 0 ≤ euclideanCurvatureLower * quadraticLowerConstant' lam :=
    mul_nonneg euclideanCurvatureLower_pos.le
      (quadraticLowerConstant'_pos graph.lam_nonneg hlam).le
  exact htransfer.trans
    (mul_le_mul_of_nonneg_left hcomparison (div_nonneg hupper0 hlower0))

end FiniteSample

end OTSelector
