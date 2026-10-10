import OTSelector.Feedback.FeedbackRightIntervalCountsActual
import OTSelector.Feedback.RankEnergyOccupation

/-!
# Frozen interval counts give density for the actual constant-tail graph

Every frozen crossing after the freezing coordinate solves the graph intersection equation.
The count of unseen such labels is therefore bounded by the full graph interval count.  This
comparison needs neither genericity nor equality of the seen-label populations.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace OTSelector.FiniteSample

variable {n : ℕ}

private theorem sourceIntervalCount_eq_groupCount
    (lam xR s t : ℝ) (boundary : RevealedSnapshot n) (sample : FiniteSample n) :
    rightBoundarySourceIntervalCount lam xR s t boundary sample =
      FiniteIntervalCounts.groupCount
        (Finset.univ.filter fun i : Fin n ↦ i ∉ (revealedSnapshotState boundary).seenSource)
        (fun i ↦ sample.sourcePhase i (rightBoundaryFrozenHeight lam xR boundary)) (Ioo s t) := by
  simp only [rightBoundarySourceIntervalCount, FiniteIntervalCounts.groupCount,
    Finset.sum_filter, RelativeVC.indicatorReal, Set.indicator_apply, Pi.one_apply, ite_and]

private theorem targetIntervalCount_eq_groupCount
    (lam xR s t : ℝ) (boundary : RevealedSnapshot n) (sample : FiniteSample n) :
    rightBoundaryTargetIntervalCount lam xR s t boundary sample =
      FiniteIntervalCounts.groupCount
        (Finset.univ.filter fun i : Fin n ↦ i ∉ (revealedSnapshotState boundary).seenTarget)
        (fun i ↦ sample.targetPhase i (rightBoundaryFrozenHeight lam xR boundary)) (Ioo s t) := by
  simp only [rightBoundaryTargetIntervalCount, FiniteIntervalCounts.groupCount,
    Finset.sum_filter, RelativeVC.indicatorReal, Set.indicator_apply, Pi.one_apply, ite_and]

/-- The measurable finite-grid event controls all open intervals in its physical window. -/
theorem rightBoundaryIntervalGridGood.interval_counts_lower
    {N : ℕ} {lam xR c r : ℝ} {hi : RevealedSnapshot n → ℝ}
    {boundary : RevealedSnapshot n} {sample : FiniteSample n}
    (hgood : rightBoundaryIntervalGridGood N lam xR c r hi boundary sample)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hxR : 0 ≤ xR) (hhi : hi boundary ≤ N)
    {s t : ℝ} (hRs : xR ≤ s) (hst : s ≤ t) (hth : t ≤ hi boundary) :
    c * (t - s) - (r + 2 * c) ≤ rightBoundarySourceIntervalCount lam xR s t boundary sample ∧
    c * (t - s) - (r + 2 * c) ≤ rightBoundaryTargetIntervalCount lam xR s t boundary sample := by
  have hsgrid : FiniteIntervalCounts.groupGridGood N
      (Finset.univ.filter fun i : Fin n ↦ i ∉ (revealedSnapshotState boundary).seenSource)
      id xR (hi boundary) c r
      (fun i ↦ sample.sourcePhase i (rightBoundaryFrozenHeight lam xR boundary)) := by
    intro a b hRa hab hbh
    simpa only [preimage_id, ← sourceIntervalCount_eq_groupCount] using
      (hgood a b hRa hab hbh).1
  have htgrid : FiniteIntervalCounts.groupGridGood N
      (Finset.univ.filter fun i : Fin n ↦ i ∉ (revealedSnapshotState boundary).seenTarget)
      id xR (hi boundary) c r
      (fun i ↦ sample.targetPhase i (rightBoundaryFrozenHeight lam xR boundary)) := by
    intro a b hRa hab hbh
    simpa only [preimage_id, ← targetIntervalCount_eq_groupCount] using
      (hgood a b hRa hab hbh).2
  constructor
  · simpa only [preimage_id, ← sourceIntervalCount_eq_groupCount] using
      FiniteIntervalCounts.groupCount_Ioo_lower_of_groupGridGood hc hr hxR hhi hsgrid hRs hst hth
  · simpa only [preimage_id, ← targetIntervalCount_eq_groupCount] using
      FiniteIntervalCounts.groupCount_Ioo_lower_of_groupGridGood hc hr hxR hhi htgrid hRs hst hth

/-- Unseen source crossings inside a constant tail are genuine graph intersections. -/
theorem rightBoundarySourceIntervalCount_le_graphOpenCount
    (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)
    (xR : ℝ) (boundary : RevealedSnapshot n)
    (hconstant : ∀ x, xR ≤ x → graph.curve x = rightBoundaryFrozenHeight lam xR boundary)
    {s t : ℝ} (hRs : xR ≤ s) :
    rightBoundarySourceIntervalCount lam xR s t boundary sample ≤
      (sample.graphSourceOpenIntervalCount graph s t : ℝ) := by
  simp only [rightBoundarySourceIntervalCount, Finset.sum_boole, graphSourceOpenIntervalCount]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hphase : sample.sourcePhase i (rightBoundaryFrozenHeight lam xR boundary) =
      sample.sourceIntersection graph i := by
    apply sample.sourceIntersection_unique graph i
    rw [hconstant _ (hRs.trans hi.2.1.le)]
  simpa only [hphase, mem_Ioo] using hi.2

/-- Target counterpart of the same deterministic comparison. -/
theorem rightBoundaryTargetIntervalCount_le_graphOpenCount
    (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)
    (xR : ℝ) (boundary : RevealedSnapshot n)
    (hconstant : ∀ x, xR ≤ x → graph.curve x = rightBoundaryFrozenHeight lam xR boundary)
    {s t : ℝ} (hRs : xR ≤ s) :
    rightBoundaryTargetIntervalCount lam xR s t boundary sample ≤
      (sample.graphTargetOpenIntervalCount graph s t : ℝ) := by
  simp only [rightBoundaryTargetIntervalCount, Finset.sum_boole, graphTargetOpenIntervalCount]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hphase : sample.targetPhase i (rightBoundaryFrozenHeight lam xR boundary) =
      sample.targetIntersection graph i := by
    apply sample.targetIntersection_unique graph i
    rw [hconstant _ (hRs.trans hi.2.1.le)]
  simpa only [hphase, mem_Ioo] using hi.2

/-- The finite-grid certificate supplies the full deterministic density input for rank energy. -/
theorem rightBoundaryIntervalGridGood.graphIntervalLowerDensity
    (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)
    {N : ℕ} {xR c r : ℝ} {hi : RevealedSnapshot n → ℝ} {boundary : RevealedSnapshot n}
    (hgood : rightBoundaryIntervalGridGood N lam xR c r hi boundary sample)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hxR : 0 ≤ xR) (hhi : hi boundary ≤ N)
    (hconstant : ∀ x, xR ≤ x → graph.curve x = rightBoundaryFrozenHeight lam xR boundary) :
    sample.GraphIntervalLowerDensity graph xR (hi boundary) c (r + 2 * c) := by
  intro s t hRs hst hth
  have h := hgood.interval_counts_lower hc hr hxR hhi hRs hst hth
  exact ⟨h.1.trans (sample.rightBoundarySourceIntervalCount_le_graphOpenCount
    graph xR boundary hconstant hRs), h.2.trans
      (sample.rightBoundaryTargetIntervalCount_le_graphOpenCount graph xR boundary hconstant hRs)⟩

end OTSelector.FiniteSample
