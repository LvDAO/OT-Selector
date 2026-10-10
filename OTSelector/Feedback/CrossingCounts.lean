import OTSelector.Feedback.Intersections
import OTSelector.Feedback.CutMass

/-!
# Crossing counts on a feedback graph

This file is the deterministic bridge between the unique intersection coordinates and the
half-space count API.  The two sample arrays are represented by their rank-scale points, so the
membership statements below are exactly the source/target swept-set predicates.  No probabilistic
or bundled proof interface is used here.
-/

open Set
open scoped BigOperators

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)

/-! ## Swept-set membership -/

/-- A source rank point lies in the swept set exactly after its graph intersection. -/
theorem rankSourcePoint_mem_sourceSwept_iff (i : Fin n) (x : ℝ) :
    sample.rankSourcePoint i ∈ sourceSwept graph.curve x ↔
      sample.sourceIntersection graph i ≤ x := by
  simpa [sourceSwept, rankSourcePoint, sourcePhase, sourceSlope, mul_comm] using
    (sample.sourceIntersection_le_iff graph i x).symm

/-- A target rank point lies in the swept set exactly after its graph intersection. -/
theorem rankTargetPoint_mem_targetSwept_iff (j : Fin n) (x : ℝ) :
    sample.rankTargetPoint j ∈ targetSwept graph.curve x ↔
      sample.targetIntersection graph j ≤ x := by
  simpa [targetSwept, rankTargetPoint, targetPhase, targetSlope, mul_comm] using
    (sample.targetIntersection_le_iff graph j x).symm

/-! ## Half-space count conversion -/

private theorem sampleErrorSum_false_target_eq_card_filter
    {m : ℕ} (h : Concept (ℝ × UnitMark) Bool)
    (xs : Fin m → ℝ × UnitMark) :
    RelativeVC.sampleErrorSum h RelativeVC.falseCutTarget xs =
      (Finset.card (Finset.univ.filter fun i ↦ h (xs i) = true) : ℝ) := by
  classical
  simp only [RelativeVC.sampleErrorSum, RelativeVC.falseCutTarget]
  have hloss : ∀ b : Bool,
      zeroOneLoss Bool b false = if b = true then (1 : ℝ) else 0 := by
    intro b
    cases b <;> norm_num [zeroOneLoss]
  simp_rw [hloss]
  exact Finset.sum_boole (R := ℝ) (fun i : Fin m ↦ h (xs i) = true) Finset.univ

theorem sourceIntersectionCount_cast_eq_sourceCutCount (x : ℝ) :
    (sample.sourceIntersectionCount graph x : ℝ) =
      RelativeVC.sourceCutCount (fun i ↦ sample.rankSourcePoint i)
        (graph.curve x) x := by
  classical
  rw [RelativeVC.sourceCutCount,
    sampleErrorSum_false_target_eq_card_filter]
  apply congrArg (fun k : ℕ ↦ (k : ℝ))
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [RelativeVC.sourceCutEval_eq_true_iff_swept]
  exact (sample.rankSourcePoint_mem_sourceSwept_iff graph i x).symm

theorem targetIntersectionCount_cast_eq_targetCutCount (x : ℝ) :
    (sample.targetIntersectionCount graph x : ℝ) =
      RelativeVC.targetCutCount (fun j ↦ sample.rankTargetPoint j)
        (graph.curve x) x := by
  classical
  rw [RelativeVC.targetCutCount,
    sampleErrorSum_false_target_eq_card_filter]
  apply congrArg (fun k : ℕ ↦ (k : ℝ))
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [RelativeVC.targetCutEval_eq_true_iff_swept]
  exact (sample.rankTargetPoint_mem_targetSwept_iff graph j x).symm

/-! ## Current identity -/

theorem intersectionCurrent_eq_feedbackRankDiscrepancy (x : ℝ) :
    (sample.sourceIntersectionCount graph x : ℝ) -
        (sample.targetIntersectionCount graph x : ℝ) =
      RelativeVC.feedbackRankDiscrepancy
        (fun i ↦ sample.rankSourcePoint i) (fun j ↦ sample.rankTargetPoint j)
          (graph.curve x) x := by
  rw [RelativeVC.feedbackRankDiscrepancy,
    sample.sourceIntersectionCount_cast_eq_sourceCutCount graph x,
    sample.targetIntersectionCount_cast_eq_targetCutCount graph x]

end FiniteSample

end OTSelector
