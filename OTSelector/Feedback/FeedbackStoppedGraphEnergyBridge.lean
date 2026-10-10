import OTSelector.Feedback.FeedbackA2HorizonRange
import OTSelector.Feedback.StoppedRankGapEnergy

/-!
# Same-rank energy for the stopped feedback graph

This file keeps the graph in every deterministic definition.  In particular, the intersection
arrays below can be instantiated with the raw recursive graph, the deterministic-horizon graph,
or the stopped-continuation graph without identifying any two of them.

The first part identifies the comparison assignment from `GraphFeedbackLocalization` with the
same-rank gaps of the sorted, rank-scale intersection arrays.  The second part partitions those
ranks into left-boundary retained, bulk-retained, and right-terminal classes.  Terminal status is
determined by the right endpoint, exactly as in `(1.40)`.  Thus an edge crossing both cut
coordinates is terminal rather than left-boundary.
-/

open Set
open scoped BigOperators Classical NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-! ## Sorted graph intersections and the comparison assignment -/

/-- The source intersection at zero-based increasing rank `r`. -/
noncomputable def graphSourceIntersectionAtRank {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) : ℝ :=
  let source := fun i : Fin n ↦ sample.sourceIntersection graph i
  source (Tuple.sort source r)

/-- The target intersection at zero-based increasing rank `r`. -/
noncomputable def graphTargetIntersectionAtRank {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) : ℝ :=
  let target := fun j : Fin n ↦ sample.targetIntersection graph j
  target (Tuple.sort target r)

/-- The signed target-minus-source gap at the same increasing rank. -/
noncomputable def graphSameRankGap {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) : ℝ :=
  sample.graphTargetIntersectionAtRank graph r -
    sample.graphSourceIntersectionAtRank graph r

/-- The displacement of the explicit comparison assignment at a source label. -/
noncomputable def graphComparisonDisplacement {lam : ℝ}
    (graph : FeedbackGraph lam) (i : Fin n) : ℝ :=
  sample.targetIntersection graph (sample.graphFeedbackComparisonAssignment graph i) -
    sample.sourceIntersection graph i

/-- Total squared energy of the explicit graph comparison assignment. -/
noncomputable def graphComparisonEnergy {lam : ℝ}
    (graph : FeedbackGraph lam) : ℝ :=
  ∑ i, sample.graphComparisonDisplacement graph i ^ 2

/-- Total squared energy of the increasing same-rank gaps. -/
noncomputable def graphSameRankGapEnergy {lam : ℝ}
    (graph : FeedbackGraph lam) : ℝ :=
  ∑ r, sample.graphSameRankGap graph r ^ 2

theorem graphSourceIntersectionAtRank_monotone {lam : ℝ}
    (graph : FeedbackGraph lam) :
    Monotone (sample.graphSourceIntersectionAtRank graph) := by
  change Monotone ((fun i : Fin n ↦ sample.sourceIntersection graph i) ∘
    Tuple.sort (fun i : Fin n ↦ sample.sourceIntersection graph i))
  exact Tuple.monotone_sort (fun i : Fin n ↦ sample.sourceIntersection graph i)

theorem graphTargetIntersectionAtRank_monotone {lam : ℝ}
    (graph : FeedbackGraph lam) :
    Monotone (sample.graphTargetIntersectionAtRank graph) := by
  change Monotone ((fun j : Fin n ↦ sample.targetIntersection graph j) ∘
    Tuple.sort (fun j : Fin n ↦ sample.targetIntersection graph j))
  exact Tuple.monotone_sort (fun j : Fin n ↦ sample.targetIntersection graph j)

/-- Sorting the normalized source array gives the same sorted rank-scale values. -/
theorem sourceIntersection_normalizedSort_eq_atRank {lam : ℝ}
    (graph : FeedbackGraph lam) (hn : 0 < n) (r : Fin n) :
    sample.sourceIntersection graph
        (Tuple.sort (sample.normalizedSourceIntersectionOfGraph graph) r) =
      sample.graphSourceIntersectionAtRank graph r := by
  let source := fun i : Fin n ↦ sample.sourceIntersection graph i
  let normalized := sample.normalizedSourceIntersectionOfGraph graph
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnormalized : Monotone (normalized ∘ Tuple.sort normalized) :=
    Tuple.monotone_sort normalized
  have hsource : Monotone (source ∘ Tuple.sort normalized) := by
    intro i j hij
    have hle := hnormalized hij
    change source (Tuple.sort normalized i) / (n : ℝ) ≤
      source (Tuple.sort normalized j) / (n : ℝ) at hle
    exact (div_le_div_iff_of_pos_right hnReal).mp hle
  have hvalues : source ∘ Tuple.sort normalized = source ∘ Tuple.sort source :=
    Tuple.unique_monotone hsource (Tuple.monotone_sort source)
  exact congrFun hvalues r

/-- Sorting the normalized target array gives the same sorted rank-scale values. -/
theorem targetIntersection_normalizedSort_eq_atRank {lam : ℝ}
    (graph : FeedbackGraph lam) (hn : 0 < n) (r : Fin n) :
    sample.targetIntersection graph
        (Tuple.sort (sample.normalizedTargetIntersectionOfGraph graph) r) =
      sample.graphTargetIntersectionAtRank graph r := by
  let target := fun j : Fin n ↦ sample.targetIntersection graph j
  let normalized := sample.normalizedTargetIntersectionOfGraph graph
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnormalized : Monotone (normalized ∘ Tuple.sort normalized) :=
    Tuple.monotone_sort normalized
  have htarget : Monotone (target ∘ Tuple.sort normalized) := by
    intro i j hij
    have hle := hnormalized hij
    change target (Tuple.sort normalized i) / (n : ℝ) ≤
      target (Tuple.sort normalized j) / (n : ℝ) at hle
    exact (div_le_div_iff_of_pos_right hnReal).mp hle
  have hvalues : target ∘ Tuple.sort normalized = target ∘ Tuple.sort target :=
    Tuple.unique_monotone htarget (Tuple.monotone_sort target)
  exact congrFun hvalues r

/-- The comparison assignment sends the normalized source rank index to the same target rank. -/
theorem graphFeedbackComparisonAssignment_apply_normalizedSourceSort {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) :
    sample.graphFeedbackComparisonAssignment graph
        (Tuple.sort (sample.normalizedSourceIntersectionOfGraph graph) r) =
      Tuple.sort (sample.normalizedTargetIntersectionOfGraph graph) r := by
  exact increasingAssignment_apply_sourceSort
    (sample.normalizedSourceIntersectionOfGraph graph)
    (sample.normalizedTargetIntersectionOfGraph graph) r

/-- At increasing rank `r`, comparison displacement is exactly the same-rank intersection gap. -/
theorem graphComparisonDisplacement_normalizedSourceSort {lam : ℝ}
    (graph : FeedbackGraph lam) (hn : 0 < n) (r : Fin n) :
    sample.graphComparisonDisplacement graph
        (Tuple.sort (sample.normalizedSourceIntersectionOfGraph graph) r) =
      sample.graphSameRankGap graph r := by
  rw [graphComparisonDisplacement, graphSameRankGap,
    sample.graphFeedbackComparisonAssignment_apply_normalizedSourceSort graph r,
    sample.sourceIntersection_normalizedSort_eq_atRank graph hn r,
    sample.targetIntersection_normalizedSort_eq_atRank graph hn r]

/-- Exact finite-sum identity between assignment energy and same-rank gap energy. -/
theorem graphComparisonEnergy_eq_sameRankGapEnergy {lam : ℝ}
    (graph : FeedbackGraph lam) (hn : 0 < n) :
    sample.graphComparisonEnergy graph = sample.graphSameRankGapEnergy graph := by
  let sourceOrder := Tuple.sort (sample.normalizedSourceIntersectionOfGraph graph)
  have hreindex := Equiv.sum_comp sourceOrder
    (fun i : Fin n ↦ sample.graphComparisonDisplacement graph i ^ 2)
  rw [graphComparisonEnergy, graphSameRankGapEnergy, ← hreindex]
  apply Finset.sum_congr rfl
  intro r _
  rw [sample.graphComparisonDisplacement_normalizedSourceSort graph hn r]

/-! ## Left, retained-bulk, and terminal ranks -/

/-- The coordinate at which a same-rank edge starts. -/
noncomputable def graphRankLeftEndpoint {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) : ℝ :=
  min (sample.graphSourceIntersectionAtRank graph r)
    (sample.graphTargetIntersectionAtRank graph r)

/-- The coordinate at which a same-rank edge ends. -/
noncomputable def graphRankRightEndpoint {lam : ℝ}
    (graph : FeedbackGraph lam) (r : Fin n) : ℝ :=
  max (sample.graphSourceIntersectionAtRank graph r)
    (sample.graphTargetIntersectionAtRank graph r)

/-- Left-boundary retained ranks start at or before `B` and end by the retained horizon `H`. -/
def GraphLeftBoundaryRetainedRank {lam : ℝ} (graph : FeedbackGraph lam)
    (B H : ℝ) (r : Fin n) : Prop :=
  sample.graphRankLeftEndpoint graph r ≤ B ∧
    sample.graphRankRightEndpoint graph r ≤ H

/-- Bulk-retained ranks start after `B` and end no later than the retained horizon `H`. -/
def GraphBulkRetainedRank {lam : ℝ} (graph : FeedbackGraph lam)
    (B H : ℝ) (r : Fin n) : Prop :=
  B < sample.graphRankLeftEndpoint graph r ∧
    sample.graphRankRightEndpoint graph r ≤ H

/-- Right-terminal ranks are exactly those whose right endpoint is strictly beyond `H`. -/
def GraphRightTerminalRank {lam : ℝ} (graph : FeedbackGraph lam)
    (H : ℝ) (r : Fin n) : Prop :=
  H < sample.graphRankRightEndpoint graph r

/-- The three rank classes are exhaustive. -/
theorem graphRank_classification {lam : ℝ} (graph : FeedbackGraph lam)
    (B H : ℝ) (r : Fin n) :
    sample.GraphLeftBoundaryRetainedRank graph B H r ∨
      sample.GraphBulkRetainedRank graph B H r ∨
        sample.GraphRightTerminalRank graph H r := by
  by_cases hright : sample.graphRankRightEndpoint graph r ≤ H
  · by_cases hleft : sample.graphRankLeftEndpoint graph r ≤ B
    · exact Or.inl ⟨hleft, hright⟩
    · exact Or.inr (Or.inl ⟨lt_of_not_ge hleft, hright⟩)
  · exact Or.inr (Or.inr (lt_of_not_ge hright))

/-- No rank belongs to two of the three classes. -/
theorem graphRank_classification_pairwise {lam : ℝ}
    (graph : FeedbackGraph lam) (B H : ℝ) (r : Fin n) :
    ¬(sample.GraphLeftBoundaryRetainedRank graph B H r ∧
        sample.GraphBulkRetainedRank graph B H r) ∧
      ¬(sample.GraphLeftBoundaryRetainedRank graph B H r ∧
        sample.GraphRightTerminalRank graph H r) ∧
      ¬(sample.GraphBulkRetainedRank graph B H r ∧
        sample.GraphRightTerminalRank graph H r) := by
  constructor
  · rintro ⟨hleft, hbulk⟩
    exact (not_lt_of_ge hleft.1) hbulk.1
  constructor
  · rintro ⟨hleft, hright⟩
    exact (not_lt_of_ge hleft.2) hright
  · rintro ⟨hbulk, hright⟩
    exact (not_lt_of_ge hbulk.2) hright

/-- This class is definitionally the paper's terminal condition `H < r(e)`. -/
theorem graphRightTerminalRank_iff {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) (r : Fin n) :
    sample.GraphRightTerminalRank graph H r ↔
      H < sample.graphRankRightEndpoint graph r := by
  rfl

/-- Squared gap energy assigned to the left-boundary retained ranks. -/
noncomputable def graphLeftBoundaryRetainedRankEnergy {lam : ℝ}
    (graph : FeedbackGraph lam) (B H : ℝ) : ℝ :=
  ∑ r, if sample.GraphLeftBoundaryRetainedRank graph B H r then
    sample.graphSameRankGap graph r ^ 2 else 0

/-- Squared gap energy assigned to the ranks retained through the bulk horizon. -/
noncomputable def graphBulkRetainedRankEnergy {lam : ℝ}
    (graph : FeedbackGraph lam) (B H : ℝ) : ℝ :=
  ∑ r, if sample.GraphBulkRetainedRank graph B H r then
    sample.graphSameRankGap graph r ^ 2 else 0

/-- Squared gap energy assigned to the remaining right-terminal ranks. -/
noncomputable def graphRightTerminalRankEnergy {lam : ℝ}
    (graph : FeedbackGraph lam) (H : ℝ) : ℝ :=
  ∑ r, if sample.GraphRightTerminalRank graph H r then
    sample.graphSameRankGap graph r ^ 2 else 0

/-- Exact energy decomposition over the disjoint exhaustive rank classification. -/
theorem graphSameRankGapEnergy_eq_three_regions {lam : ℝ}
    (graph : FeedbackGraph lam) (B H : ℝ) :
    sample.graphSameRankGapEnergy graph =
      sample.graphLeftBoundaryRetainedRankEnergy graph B H +
        sample.graphBulkRetainedRankEnergy graph B H +
          sample.graphRightTerminalRankEnergy graph H := by
  rw [graphSameRankGapEnergy, graphLeftBoundaryRetainedRankEnergy,
    graphBulkRetainedRankEnergy, graphRightTerminalRankEnergy,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hright : sample.graphRankRightEndpoint graph r ≤ H
  · by_cases hleft : sample.graphRankLeftEndpoint graph r ≤ B
    · simp [GraphLeftBoundaryRetainedRank, GraphBulkRetainedRank,
        GraphRightTerminalRank, hleft, hright, not_lt_of_ge hright]
    · have hB : B < sample.graphRankLeftEndpoint graph r := lt_of_not_ge hleft
      simp [GraphLeftBoundaryRetainedRank, GraphBulkRetainedRank,
        GraphRightTerminalRank, hleft, hB, hright, not_lt_of_ge hright]
  · have hH : H < sample.graphRankRightEndpoint graph r := lt_of_not_ge hright
    simp [GraphLeftBoundaryRetainedRank, GraphBulkRetainedRank,
      GraphRightTerminalRank, hright, hH]

/-! ## Raw-to-horizon intersection transport below the retained cut -/

/-- Up to the deterministic right cut, the horizon curve is the raw recursive curve. -/
theorem horizonFeedbackGraph_curve_eq_feedbackCurve_of_le_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) {x : ℝ} (hx : x ≤ B + (T : ℝ)) :
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T).curve x =
      feedbackCurve sample lam B 0 x := by
  by_cases hleft : x ≤ B
  · rw [sample.horizonFeedbackGraph_curve_eq_left
      hlam0 hlamHalf B T hleft]
    simp [feedbackCurve, hleft]
  · exact sample.horizonFeedbackGraph_curve_eq_of_mem
      hlam0 hlamHalf B T ⟨le_of_not_ge hleft, hx⟩

/-- A raw source intersection at or before the cut is unchanged by horizon freezing. -/
theorem sourceIntersection_horizon_eq_raw_of_raw_le_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (i : Fin n)
    (hraw : sample.sourceIntersection
      (sample.feedbackGraph hlam0 hlamHalf B 0) i ≤ B + (T : ℝ)) :
    sample.sourceIntersection (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i =
      sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i := by
  symm
  apply sample.sourceIntersection_unique
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i
  rw [sample.horizonFeedbackGraph_curve_eq_feedbackCurve_of_le_right
    hlam0 hlamHalf B T hraw]
  exact sample.sourceIntersection_spec
    (sample.feedbackGraph hlam0 hlamHalf B 0) i

/-- A horizon source intersection below the cut is also the corresponding raw intersection. -/
theorem sourceIntersection_horizon_eq_raw_of_horizon_le_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (i : Fin n)
    (hhorizon : sample.sourceIntersection
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i ≤ B + (T : ℝ)) :
    sample.sourceIntersection (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i =
      sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i := by
  apply sample.sourceIntersection_unique
    (sample.feedbackGraph hlam0 hlamHalf B 0) i
  change sample.sourcePhase i
      (feedbackCurve sample lam B 0
        (sample.sourceIntersection
          (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i)) =
    sample.sourceIntersection (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i
  rw [← sample.horizonFeedbackGraph_curve_eq_feedbackCurve_of_le_right
    hlam0 hlamHalf B T hhorizon]
  exact sample.sourceIntersection_spec
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i

/-- A raw target intersection at or before the cut is unchanged by horizon freezing. -/
theorem targetIntersection_horizon_eq_raw_of_raw_le_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (j : Fin n)
    (hraw : sample.targetIntersection
      (sample.feedbackGraph hlam0 hlamHalf B 0) j ≤ B + (T : ℝ)) :
    sample.targetIntersection (sample.horizonFeedbackGraph hlam0 hlamHalf B T) j =
      sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) j := by
  symm
  apply sample.targetIntersection_unique
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T) j
  rw [sample.horizonFeedbackGraph_curve_eq_feedbackCurve_of_le_right
    hlam0 hlamHalf B T hraw]
  exact sample.targetIntersection_spec
    (sample.feedbackGraph hlam0 hlamHalf B 0) j

/-- A horizon target intersection below the cut is also the corresponding raw intersection. -/
theorem targetIntersection_horizon_eq_raw_of_horizon_le_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (j : Fin n)
    (hhorizon : sample.targetIntersection
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) j ≤ B + (T : ℝ)) :
    sample.targetIntersection (sample.horizonFeedbackGraph hlam0 hlamHalf B T) j =
      sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) j := by
  apply sample.targetIntersection_unique
    (sample.feedbackGraph hlam0 hlamHalf B 0) j
  change sample.targetPhase j
      (feedbackCurve sample lam B 0
        (sample.targetIntersection
          (sample.horizonFeedbackGraph hlam0 hlamHalf B T) j)) =
    sample.targetIntersection (sample.horizonFeedbackGraph hlam0 hlamHalf B T) j
  rw [← sample.horizonFeedbackGraph_curve_eq_feedbackCurve_of_le_right
    hlam0 hlamHalf B T hhorizon]
  exact sample.targetIntersection_spec
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T) j

private theorem sortedValue_eq_of_agree_below
    {valuesRaw valuesHorizon : Fin n → ℝ} (r : Fin n) {H : ℝ}
    (hrank : valuesRaw (Tuple.sort valuesRaw r) ≤ H)
    (hraw : ∀ i, valuesRaw i ≤ H → valuesHorizon i = valuesRaw i)
    (hhorizon : ∀ i, valuesHorizon i ≤ H →
      valuesHorizon i = valuesRaw i) :
    valuesHorizon (Tuple.sort valuesHorizon r) =
      valuesRaw (Tuple.sort valuesRaw r) := by
  have hsublevel : ∀ {x : ℝ}, x ≤ H → ∀ i,
      valuesHorizon i ≤ x ↔ valuesRaw i ≤ x := by
    intro x hx i
    constructor
    · intro hi
      rw [hhorizon i (hi.trans hx)] at hi
      exact hi
    · intro hi
      rw [hraw i (hi.trans hx)]
      exact hi
  have hcard : ∀ {x : ℝ}, x ≤ H →
      (Finset.univ.filter fun i ↦ valuesHorizon i ≤ x).card =
        (Finset.univ.filter fun i ↦ valuesRaw i ≤ x).card := by
    intro x hx
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsublevel hx i
  have hrawCount : r.val <
      (Finset.univ.filter fun i ↦
        valuesRaw i ≤ valuesRaw (Tuple.sort valuesRaw r)).card :=
    (CountingProcess.tupleSort_apply_le_iff_lt_card valuesRaw r _).mp le_rfl
  have hhorizonCount : r.val <
      (Finset.univ.filter fun i ↦
        valuesHorizon i ≤ valuesRaw (Tuple.sort valuesRaw r)).card := by
    rw [hcard hrank]
    exact hrawCount
  have hhorizonLe : valuesHorizon (Tuple.sort valuesHorizon r) ≤
      valuesRaw (Tuple.sort valuesRaw r) :=
    (CountingProcess.tupleSort_apply_le_iff_lt_card valuesHorizon r _).mpr
      hhorizonCount
  have hhorizonRank : valuesHorizon (Tuple.sort valuesHorizon r) ≤ H :=
    hhorizonLe.trans hrank
  have hhorizonOwnCount : r.val <
      (Finset.univ.filter fun i ↦
        valuesHorizon i ≤ valuesHorizon (Tuple.sort valuesHorizon r)).card :=
    (CountingProcess.tupleSort_apply_le_iff_lt_card valuesHorizon r _).mp le_rfl
  have hrawOwnCount : r.val <
      (Finset.univ.filter fun i ↦
        valuesRaw i ≤ valuesHorizon (Tuple.sort valuesHorizon r)).card := by
    rw [← hcard hhorizonRank]
    exact hhorizonOwnCount
  have hrawLe : valuesRaw (Tuple.sort valuesRaw r) ≤
      valuesHorizon (Tuple.sort valuesHorizon r) :=
    (CountingProcess.tupleSort_apply_le_iff_lt_card valuesRaw r _).mpr hrawOwnCount
  exact le_antisymm hhorizonLe hrawLe

/-- Every raw source order statistic through the cut equals the horizon order statistic. -/
theorem graphSourceIntersectionAtRank_horizon_eq_raw_of_raw_le_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hraw : sample.graphSourceIntersectionAtRank
      (sample.feedbackGraph hlam0 hlamHalf B 0) r ≤ B + (T : ℝ)) :
    sample.graphSourceIntersectionAtRank
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r =
      sample.graphSourceIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r := by
  unfold graphSourceIntersectionAtRank at hraw ⊢
  refine sortedValue_eq_of_agree_below
    (valuesRaw := fun i ↦ sample.sourceIntersection
      (sample.feedbackGraph hlam0 hlamHalf B 0) i)
    (valuesHorizon := fun i ↦ sample.sourceIntersection
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i)
    r hraw ?_ ?_
  · intro i hi
    exact sample.sourceIntersection_horizon_eq_raw_of_raw_le_right
      hlam0 hlamHalf B T i hi
  · intro i hi
    exact sample.sourceIntersection_horizon_eq_raw_of_horizon_le_right
      hlam0 hlamHalf B T i hi

/-- Every raw target order statistic through the cut equals the horizon order statistic. -/
theorem graphTargetIntersectionAtRank_horizon_eq_raw_of_raw_le_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hraw : sample.graphTargetIntersectionAtRank
      (sample.feedbackGraph hlam0 hlamHalf B 0) r ≤ B + (T : ℝ)) :
    sample.graphTargetIntersectionAtRank
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r =
      sample.graphTargetIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r := by
  unfold graphTargetIntersectionAtRank at hraw ⊢
  refine sortedValue_eq_of_agree_below
    (valuesRaw := fun j ↦ sample.targetIntersection
      (sample.feedbackGraph hlam0 hlamHalf B 0) j)
    (valuesHorizon := fun j ↦ sample.targetIntersection
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) j)
    r hraw ?_ ?_
  · intro j hj
    exact sample.targetIntersection_horizon_eq_raw_of_raw_le_right
      hlam0 hlamHalf B T j hj
  · intro j hj
    exact sample.targetIntersection_horizon_eq_raw_of_horizon_le_right
      hlam0 hlamHalf B T j hj

/-- Every horizon source order statistic through the cut equals the raw order statistic. -/
theorem graphSourceIntersectionAtRank_horizon_eq_raw_of_horizon_le_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hhorizon : sample.graphSourceIntersectionAtRank
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r ≤ B + (T : ℝ)) :
    sample.graphSourceIntersectionAtRank
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r =
      sample.graphSourceIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r := by
  unfold graphSourceIntersectionAtRank at hhorizon ⊢
  symm
  refine sortedValue_eq_of_agree_below
    (valuesRaw := fun i ↦ sample.sourceIntersection
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) i)
    (valuesHorizon := fun i ↦ sample.sourceIntersection
      (sample.feedbackGraph hlam0 hlamHalf B 0) i)
    r hhorizon ?_ ?_
  · intro i hi
    exact (sample.sourceIntersection_horizon_eq_raw_of_horizon_le_right
      hlam0 hlamHalf B T i hi).symm
  · intro i hi
    exact (sample.sourceIntersection_horizon_eq_raw_of_raw_le_right
      hlam0 hlamHalf B T i hi).symm

/-- Every horizon target order statistic through the cut equals the raw order statistic. -/
theorem graphTargetIntersectionAtRank_horizon_eq_raw_of_horizon_le_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hhorizon : sample.graphTargetIntersectionAtRank
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r ≤ B + (T : ℝ)) :
    sample.graphTargetIntersectionAtRank
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r =
      sample.graphTargetIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r := by
  unfold graphTargetIntersectionAtRank at hhorizon ⊢
  symm
  refine sortedValue_eq_of_agree_below
    (valuesRaw := fun j ↦ sample.targetIntersection
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) j)
    (valuesHorizon := fun j ↦ sample.targetIntersection
      (sample.feedbackGraph hlam0 hlamHalf B 0) j)
    r hhorizon ?_ ?_
  · intro j hj
    exact (sample.targetIntersection_horizon_eq_raw_of_horizon_le_right
      hlam0 hlamHalf B T j hj).symm
  · intro j hj
    exact (sample.targetIntersection_horizon_eq_raw_of_raw_le_right
      hlam0 hlamHalf B T j hj).symm

/-! ## Label interface for the abstract stopped-gap energy -/

/-- A pointwise identification of the two oriented stopped-gap labels with the retained graph
gap gives the exact energy identification required by
`stoppedRankGapEnergy_integrable_and_integral_le`. This theorem is deterministic and has no
intensity premise. -/
theorem stoppedRankGapEnergy_eq_graphBulkRetainedRankEnergy_of_pointwise
    {lam : ℝ} (graph : FeedbackGraph lam) (B H : ℝ)
    (Xplus Xminus : Fin n → FiniteSample n → ℝ)
    (hpoint : ∀ r,
      Xplus r sample ^ 2 + Xminus r sample ^ 2 =
        if sample.GraphBulkRetainedRank graph B H r then
          sample.graphSameRankGap graph r ^ 2 else 0) :
    CountingProcess.stoppedRankGapEnergy Xplus Xminus sample =
      sample.graphBulkRetainedRankEnergy graph B H := by
  rw [CountingProcess.stoppedRankGapEnergy, graphBulkRetainedRankEnergy,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ ↦ hpoint r

/-- The two existing deterministic tail inclusions, packaged with exactly the raw stopped-gap
labels used by the graph-energy identity below.  No intensity is selected here. -/
theorem rawStoppedFullRankGap_tail_inputs
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) :
    (∀ (r : Fin n) (q : ℝ≥0),
      {omega : FiniteSample n |
        (q : ℝ) < sourceInteriorStoppedFullRankGap
          hlam0 hlamHalf eta B B 0 T r omega} ⊆
        {omega | CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
          sourceInteriorA1StartBacklog
            hlam0 hlamHalf eta B T r omega} ∪
          CountingProcess.stoppedLowerOccupationEvent
            (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0)
            (feedbackFullRankStart hlam0 hlamHalf B T r)
            (safeFeedbackA1StopTime
              (n := n) hlam0 hlamHalf eta B B 0 T)
            (CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2)) q) ∧
      (∀ (r : Fin n) (q : ℝ≥0),
        {omega : FiniteSample n |
          (q : ℝ) < targetInteriorStoppedFullRankGap
            hlam0 hlamHalf eta B B 0 T r omega} ⊆
          {omega | CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2) * (q : ℝ) <
            targetInteriorA1StartBacklog
              hlam0 hlamHalf eta B T r omega} ∪
            CountingProcess.stoppedLowerOccupationEvent
              (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
              (feedbackFullRankStart hlam0 hlamHalf B T r)
              (safeFeedbackA1StopTime
                (n := n) hlam0 hlamHalf eta B B 0 T)
              (CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2)) q) := by
  constructor
  · intro r q
    exact sourceInteriorStoppedFullRankGap_tail_subset_startGated
      (n := n) hlam0 hlamHalf eta B T q r
  · intro r q
    exact targetInteriorStoppedFullRankGap_tail_subset_startGated
      (n := n) hlam0 hlamHalf eta B T q r

/-! ## Raw stopped-gap labels on retained ranks -/

@[simp]
theorem graphSourceIntersectionAtRank_feedbackGraph
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    sample.graphSourceIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r =
      sourceIntersectionOrderStatistic hlam0 hlamHalf B 0 sample r := by
  rfl

@[simp]
theorem graphTargetIntersectionAtRank_feedbackGraph
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    sample.graphTargetIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r =
      targetIntersectionOrderStatistic hlam0 hlamHalf B 0 sample r := by
  rfl

theorem sourceFullRankEventTime_eq_graphSourceElapsed_of_gt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hB : B < sample.graphSourceIntersectionAtRank
      (sample.feedbackGraph hlam0 hlamHalf B 0) r) :
    sourceFullRankEventTime hlam0 hlamHalf B r sample =
      WithTop.some (⟨sample.graphSourceIntersectionAtRank
          (sample.feedbackGraph hlam0 hlamHalf B 0) r - B,
        sub_nonneg.mpr hB.le⟩ : ℝ≥0) := by
  rw [sourceFullRankEventTime_eq_toNNReal_sourceIntersection_sub_B
    hlam0 hlamHalf B r sample hNoTie]
  rw [← sample.graphSourceIntersectionAtRank_feedbackGraph
    hlam0 hlamHalf B r]
  apply WithTop.coe_eq_coe.mpr
  apply Subtype.ext
  exact Real.coe_toNNReal _ (sub_nonneg.mpr hB.le)

theorem targetFullRankEventTime_eq_graphTargetElapsed_of_gt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hB : B < sample.graphTargetIntersectionAtRank
      (sample.feedbackGraph hlam0 hlamHalf B 0) r) :
    targetFullRankEventTime hlam0 hlamHalf B r sample =
      WithTop.some (⟨sample.graphTargetIntersectionAtRank
          (sample.feedbackGraph hlam0 hlamHalf B 0) r - B,
        sub_nonneg.mpr hB.le⟩ : ℝ≥0) := by
  rw [targetFullRankEventTime_eq_toNNReal_targetIntersection_sub_B
    hlam0 hlamHalf B r sample hNoTie]
  rw [← sample.graphTargetIntersectionAtRank_feedbackGraph
    hlam0 hlamHalf B r]
  apply WithTop.coe_eq_coe.mpr
  apply Subtype.ext
  exact Real.coe_toNNReal _ (sub_nonneg.mpr hB.le)

/-- On a retained source-first raw rank, the source-oriented stopped label is the raw graph gap
and the target-oriented label vanishes. -/
theorem rawStoppedFullRankGaps_eq_of_source_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hsourceB : B < sample.graphSourceIntersectionAtRank
      (sample.feedbackGraph hlam0 hlamHalf B 0) r)
    (hsourceTarget : sample.graphSourceIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r <
      sample.graphTargetIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r)
    (htargetH : sample.graphTargetIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r ≤ B + (T : ℝ))
    (hstop : safeFeedbackA1StopTime
      hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0)) :
    sourceInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample =
          sample.graphTargetIntersectionAtRank
              (sample.feedbackGraph hlam0 hlamHalf B 0) r -
            sample.graphSourceIntersectionAtRank
              (sample.feedbackGraph hlam0 hlamHalf B 0) r ∧
      targetInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample = 0 := by
  let sourceValue := sample.graphSourceIntersectionAtRank
    (sample.feedbackGraph hlam0 hlamHalf B 0) r
  let targetValue := sample.graphTargetIntersectionAtRank
    (sample.feedbackGraph hlam0 hlamHalf B 0) r
  let sourceElapsed : ℝ≥0 := ⟨sourceValue - B, sub_nonneg.mpr hsourceB.le⟩
  have htargetB : B < targetValue := hsourceB.trans hsourceTarget
  let targetElapsed : ℝ≥0 := ⟨targetValue - B, sub_nonneg.mpr htargetB.le⟩
  have hsourceTime : sourceFullRankEventTime hlam0 hlamHalf B r sample =
      (sourceElapsed : WithTop ℝ≥0) := by
    exact sample.sourceFullRankEventTime_eq_graphSourceElapsed_of_gt
      hlam0 hlamHalf B r hNoTie hsourceB
  have htargetTime : targetFullRankEventTime hlam0 hlamHalf B r sample =
      (targetElapsed : WithTop ℝ≥0) := by
    exact sample.targetFullRankEventTime_eq_graphTargetElapsed_of_gt
      hlam0 hlamHalf B r hNoTie htargetB
  have helapsedLt : sourceElapsed < targetElapsed := by
    apply NNReal.coe_lt_coe.mp
    change sourceValue - B < targetValue - B
    exact sub_lt_sub_right hsourceTarget B
  have htargetElapsedT : targetElapsed ≤ T := by
    apply NNReal.coe_le_coe.mp
    change targetValue - B ≤ (T : ℝ)
    linarith
  have hsourceFirst : sample ∈
      sourceFirstFullRankEvent hlam0 hlamHalf B r := by
    change sourceFullRankEventTime hlam0 hlamHalf B r sample <
      targetFullRankEventTime hlam0 hlamHalf B r sample
    rw [hsourceTime, htargetTime]
    exact WithTop.coe_lt_coe.mpr helapsedLt
  have hsourcePositive : (0 : WithTop ℝ≥0) <
      sourceFullRankEventTime hlam0 hlamHalf B r sample := by
    rw [hsourceTime]
    apply WithTop.coe_lt_coe.mpr
    apply NNReal.coe_lt_coe.mp
    change 0 < sourceValue - B
    exact sub_pos.mpr hsourceB
  have htargetStop : targetFullRankEventTime hlam0 hlamHalf B r sample ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample := by
    rw [htargetTime, hstop]
    exact WithTop.coe_le_coe.mpr htargetElapsedT
  have hsourceCap : CountingProcess.cappedStoppingValue T
      (sourceFullRankEventTime hlam0 hlamHalf B r) sample = sourceElapsed := by
    apply WithTop.coe_eq_coe.mp
    rw [CountingProcess.coe_cappedStoppingValue, hsourceTime]
    exact min_eq_left (WithTop.coe_le_coe.mpr (helapsedLt.le.trans htargetElapsedT))
  have htargetCap : CountingProcess.cappedStoppingValue T
      (targetFullRankEventTime hlam0 hlamHalf B r) sample = targetElapsed := by
    apply WithTop.coe_eq_coe.mp
    rw [CountingProcess.coe_cappedStoppingValue, htargetTime]
    exact min_eq_left (WithTop.coe_le_coe.mpr htargetElapsedT)
  constructor
  · rw [sourceInteriorStoppedFullRankGap,
      ite_eq_left ⟨hsourceFirst, hsourcePositive, htargetStop⟩,
      htargetCap, hsourceCap]
    change targetValue - B - (sourceValue - B) = targetValue - sourceValue
    ring
  · rw [targetInteriorStoppedFullRankGap, ite_eq_right]
    intro htargetFirst
    have hsourceOrder : sourceFullRankEventTime hlam0 hlamHalf B r sample <
        targetFullRankEventTime hlam0 hlamHalf B r sample := hsourceFirst
    have htargetOrder : targetFullRankEventTime hlam0 hlamHalf B r sample <
        sourceFullRankEventTime hlam0 hlamHalf B r sample := htargetFirst.1
    exact (not_lt_of_ge hsourceOrder.le) htargetOrder

/-- Symmetric retained target-first identification. -/
theorem rawStoppedFullRankGaps_eq_of_target_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (htargetB : B < sample.graphTargetIntersectionAtRank
      (sample.feedbackGraph hlam0 hlamHalf B 0) r)
    (htargetSource : sample.graphTargetIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r <
      sample.graphSourceIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r)
    (hsourceH : sample.graphSourceIntersectionAtRank
        (sample.feedbackGraph hlam0 hlamHalf B 0) r ≤ B + (T : ℝ))
    (hstop : safeFeedbackA1StopTime
      hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0)) :
    sourceInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample = 0 ∧
      targetInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample =
          sample.graphSourceIntersectionAtRank
              (sample.feedbackGraph hlam0 hlamHalf B 0) r -
            sample.graphTargetIntersectionAtRank
              (sample.feedbackGraph hlam0 hlamHalf B 0) r := by
  let sourceValue := sample.graphSourceIntersectionAtRank
    (sample.feedbackGraph hlam0 hlamHalf B 0) r
  let targetValue := sample.graphTargetIntersectionAtRank
    (sample.feedbackGraph hlam0 hlamHalf B 0) r
  let targetElapsed : ℝ≥0 := ⟨targetValue - B, sub_nonneg.mpr htargetB.le⟩
  have hsourceB : B < sourceValue := htargetB.trans htargetSource
  let sourceElapsed : ℝ≥0 := ⟨sourceValue - B, sub_nonneg.mpr hsourceB.le⟩
  have hsourceTime : sourceFullRankEventTime hlam0 hlamHalf B r sample =
      (sourceElapsed : WithTop ℝ≥0) := by
    exact sample.sourceFullRankEventTime_eq_graphSourceElapsed_of_gt
      hlam0 hlamHalf B r hNoTie hsourceB
  have htargetTime : targetFullRankEventTime hlam0 hlamHalf B r sample =
      (targetElapsed : WithTop ℝ≥0) := by
    exact sample.targetFullRankEventTime_eq_graphTargetElapsed_of_gt
      hlam0 hlamHalf B r hNoTie htargetB
  have helapsedLt : targetElapsed < sourceElapsed := by
    apply NNReal.coe_lt_coe.mp
    change targetValue - B < sourceValue - B
    exact sub_lt_sub_right htargetSource B
  have hsourceElapsedT : sourceElapsed ≤ T := by
    apply NNReal.coe_le_coe.mp
    change sourceValue - B ≤ (T : ℝ)
    linarith
  have htargetFirst : sample ∈
      targetFirstFullRankEvent hlam0 hlamHalf B r := by
    change targetFullRankEventTime hlam0 hlamHalf B r sample <
      sourceFullRankEventTime hlam0 hlamHalf B r sample
    rw [htargetTime, hsourceTime]
    exact WithTop.coe_lt_coe.mpr helapsedLt
  have htargetPositive : (0 : WithTop ℝ≥0) <
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
    rw [htargetTime]
    apply WithTop.coe_lt_coe.mpr
    apply NNReal.coe_lt_coe.mp
    change 0 < targetValue - B
    exact sub_pos.mpr htargetB
  have hsourceStop : sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample := by
    rw [hsourceTime, hstop]
    exact WithTop.coe_le_coe.mpr hsourceElapsedT
  have hsourceCap : CountingProcess.cappedStoppingValue T
      (sourceFullRankEventTime hlam0 hlamHalf B r) sample = sourceElapsed := by
    apply WithTop.coe_eq_coe.mp
    rw [CountingProcess.coe_cappedStoppingValue, hsourceTime]
    exact min_eq_left (WithTop.coe_le_coe.mpr hsourceElapsedT)
  have htargetCap : CountingProcess.cappedStoppingValue T
      (targetFullRankEventTime hlam0 hlamHalf B r) sample = targetElapsed := by
    apply WithTop.coe_eq_coe.mp
    rw [CountingProcess.coe_cappedStoppingValue, htargetTime]
    exact min_eq_left (WithTop.coe_le_coe.mpr (helapsedLt.le.trans hsourceElapsedT))
  constructor
  · rw [sourceInteriorStoppedFullRankGap, ite_eq_right]
    intro hsourceFirst
    have htargetOrder : targetFullRankEventTime hlam0 hlamHalf B r sample <
        sourceFullRankEventTime hlam0 hlamHalf B r sample := htargetFirst
    have hsourceOrder : sourceFullRankEventTime hlam0 hlamHalf B r sample <
        targetFullRankEventTime hlam0 hlamHalf B r sample := hsourceFirst.1
    exact (not_lt_of_ge htargetOrder.le) hsourceOrder
  · rw [targetInteriorStoppedFullRankGap,
      ite_eq_left ⟨htargetFirst, htargetPositive, hsourceStop⟩,
      hsourceCap, htargetCap]
    change sourceValue - B - (targetValue - B) = sourceValue - targetValue
    ring

/-- An active source-first stopped label is a bulk-retained horizon rank. -/
theorem horizon_bulkRetained_of_sourceStoppedFullRankGap_active
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime
      hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hactive : sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r ∧
      (0 : WithTop ℝ≥0) < sourceFullRankEventTime hlam0 hlamHalf B r sample ∧
      targetFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample) :
    sample.GraphBulkRetainedRank
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) B (B + (T : ℝ)) r := by
  let sourceValue := sample.graphSourceIntersectionAtRank
    (sample.feedbackGraph hlam0 hlamHalf B 0) r
  let targetValue := sample.graphTargetIntersectionAtRank
    (sample.feedbackGraph hlam0 hlamHalf B 0) r
  have hsourceTime := sourceFullRankEventTime_eq_toNNReal_sourceIntersection_sub_B
    hlam0 hlamHalf B r sample hNoTie
  have htargetTime := targetFullRankEventTime_eq_toNNReal_targetIntersection_sub_B
    hlam0 hlamHalf B r sample hNoTie
  rw [← sample.graphSourceIntersectionAtRank_feedbackGraph
    hlam0 hlamHalf B r] at hsourceTime
  rw [← sample.graphTargetIntersectionAtRank_feedbackGraph
    hlam0 hlamHalf B r] at htargetTime
  have hsourcePositive := hactive.2.1
  rw [hsourceTime] at hsourcePositive
  have hsourceNNPositive : 0 < Real.toNNReal (sourceValue - B) :=
    WithTop.coe_lt_coe.mp hsourcePositive
  have hsourceB : B < sourceValue := by
    exact sub_pos.mp (Real.toNNReal_pos.mp hsourceNNPositive)
  have htimeOrder := hactive.1
  change sourceFullRankEventTime hlam0 hlamHalf B r sample <
    targetFullRankEventTime hlam0 hlamHalf B r sample at htimeOrder
  rw [hsourceTime, htargetTime] at htimeOrder
  have hNNOrder : Real.toNNReal (sourceValue - B) <
      Real.toNNReal (targetValue - B) := WithTop.coe_lt_coe.mp htimeOrder
  have htargetNNPositive : 0 < Real.toNNReal (targetValue - B) :=
    hsourceNNPositive.trans hNNOrder
  have htargetB : B < targetValue := by
    exact sub_pos.mp (Real.toNNReal_pos.mp htargetNNPositive)
  have hrealOrder : (Real.toNNReal (sourceValue - B) : ℝ) <
      Real.toNNReal (targetValue - B) := by
    exact_mod_cast hNNOrder
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hsourceB.le),
    Real.coe_toNNReal _ (sub_nonneg.mpr htargetB.le)] at hrealOrder
  have hsourceTarget : sourceValue < targetValue := by linarith
  have htargetStop := hactive.2.2
  rw [htargetTime, hstop] at htargetStop
  have htargetNNLe : Real.toNNReal (targetValue - B) ≤ T :=
    WithTop.coe_le_coe.mp htargetStop
  have htargetRealLe : (Real.toNNReal (targetValue - B) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast htargetNNLe
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr htargetB.le)] at htargetRealLe
  have htargetH : targetValue ≤ B + (T : ℝ) := by linarith
  have hsourceH : sourceValue ≤ B + (T : ℝ) :=
    hsourceTarget.le.trans htargetH
  have hsourceEq :=
    sample.graphSourceIntersectionAtRank_horizon_eq_raw_of_raw_le_right
      hlam0 hlamHalf B T r hsourceH
  have htargetEq :=
    sample.graphTargetIntersectionAtRank_horizon_eq_raw_of_raw_le_right
      hlam0 hlamHalf B T r htargetH
  rw [GraphBulkRetainedRank, graphRankLeftEndpoint, graphRankRightEndpoint,
    hsourceEq, htargetEq]
  exact ⟨lt_min hsourceB htargetB, max_le hsourceH htargetH⟩

/-- An active target-first stopped label is a bulk-retained horizon rank. -/
theorem horizon_bulkRetained_of_targetStoppedFullRankGap_active
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime
      hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hactive : sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r ∧
      (0 : WithTop ℝ≥0) < targetFullRankEventTime hlam0 hlamHalf B r sample ∧
      sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
        safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample) :
    sample.GraphBulkRetainedRank
      (sample.horizonFeedbackGraph hlam0 hlamHalf B T) B (B + (T : ℝ)) r := by
  let sourceValue := sample.graphSourceIntersectionAtRank
    (sample.feedbackGraph hlam0 hlamHalf B 0) r
  let targetValue := sample.graphTargetIntersectionAtRank
    (sample.feedbackGraph hlam0 hlamHalf B 0) r
  have hsourceTime := sourceFullRankEventTime_eq_toNNReal_sourceIntersection_sub_B
    hlam0 hlamHalf B r sample hNoTie
  have htargetTime := targetFullRankEventTime_eq_toNNReal_targetIntersection_sub_B
    hlam0 hlamHalf B r sample hNoTie
  rw [← sample.graphSourceIntersectionAtRank_feedbackGraph
    hlam0 hlamHalf B r] at hsourceTime
  rw [← sample.graphTargetIntersectionAtRank_feedbackGraph
    hlam0 hlamHalf B r] at htargetTime
  have htargetPositive := hactive.2.1
  rw [htargetTime] at htargetPositive
  have htargetNNPositive : 0 < Real.toNNReal (targetValue - B) :=
    WithTop.coe_lt_coe.mp htargetPositive
  have htargetB : B < targetValue := by
    exact sub_pos.mp (Real.toNNReal_pos.mp htargetNNPositive)
  have htimeOrder := hactive.1
  change targetFullRankEventTime hlam0 hlamHalf B r sample <
    sourceFullRankEventTime hlam0 hlamHalf B r sample at htimeOrder
  rw [htargetTime, hsourceTime] at htimeOrder
  have hNNOrder : Real.toNNReal (targetValue - B) <
      Real.toNNReal (sourceValue - B) := WithTop.coe_lt_coe.mp htimeOrder
  have hsourceNNPositive : 0 < Real.toNNReal (sourceValue - B) :=
    htargetNNPositive.trans hNNOrder
  have hsourceB : B < sourceValue := by
    exact sub_pos.mp (Real.toNNReal_pos.mp hsourceNNPositive)
  have hrealOrder : (Real.toNNReal (targetValue - B) : ℝ) <
      Real.toNNReal (sourceValue - B) := by
    exact_mod_cast hNNOrder
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr htargetB.le),
    Real.coe_toNNReal _ (sub_nonneg.mpr hsourceB.le)] at hrealOrder
  have htargetSource : targetValue < sourceValue := by linarith
  have hsourceStop := hactive.2.2
  rw [hsourceTime, hstop] at hsourceStop
  have hsourceNNLe : Real.toNNReal (sourceValue - B) ≤ T :=
    WithTop.coe_le_coe.mp hsourceStop
  have hsourceRealLe : (Real.toNNReal (sourceValue - B) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hsourceNNLe
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hsourceB.le)] at hsourceRealLe
  have hsourceH : sourceValue ≤ B + (T : ℝ) := by linarith
  have htargetH : targetValue ≤ B + (T : ℝ) :=
    htargetSource.le.trans hsourceH
  have hsourceEq :=
    sample.graphSourceIntersectionAtRank_horizon_eq_raw_of_raw_le_right
      hlam0 hlamHalf B T r hsourceH
  have htargetEq :=
    sample.graphTargetIntersectionAtRank_horizon_eq_raw_of_raw_le_right
      hlam0 hlamHalf B T r htargetH
  rw [GraphBulkRetainedRank, graphRankLeftEndpoint, graphRankRightEndpoint,
    hsourceEq, htargetEq]
  exact ⟨lt_min hsourceB htargetB, max_le hsourceH htargetH⟩

/-- At every rank, the two raw oriented stopped labels carry exactly the bulk-retained
horizon-graph gap energy. -/
theorem rawStoppedFullRankGaps_sq_sum_eq_horizon_bulkRetained
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (r : Fin n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime
      hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0)) :
    sourceInteriorStoppedFullRankGap
          hlam0 hlamHalf eta B B 0 T r sample ^ 2 +
        targetInteriorStoppedFullRankGap
          hlam0 hlamHalf eta B B 0 T r sample ^ 2 =
      if sample.GraphBulkRetainedRank
          (sample.horizonFeedbackGraph hlam0 hlamHalf B T)
          B (B + (T : ℝ)) r then
        sample.graphSameRankGap
          (sample.horizonFeedbackGraph hlam0 hlamHalf B T) r ^ 2
      else 0 := by
  let raw := sample.feedbackGraph hlam0 hlamHalf B 0
  let horizon := sample.horizonFeedbackGraph hlam0 hlamHalf B T
  by_cases hbulk : sample.GraphBulkRetainedRank horizon B (B + (T : ℝ)) r
  · rw [ite_eq_left hbulk]
    have hsourceHorizonB : B < sample.graphSourceIntersectionAtRank horizon r :=
      (lt_min_iff.mp hbulk.1).1
    have htargetHorizonB : B < sample.graphTargetIntersectionAtRank horizon r :=
      (lt_min_iff.mp hbulk.1).2
    have hsourceHorizonH : sample.graphSourceIntersectionAtRank horizon r ≤
        B + (T : ℝ) := (max_le_iff.mp hbulk.2).1
    have htargetHorizonH : sample.graphTargetIntersectionAtRank horizon r ≤
        B + (T : ℝ) := (max_le_iff.mp hbulk.2).2
    have hsourceEq :=
      sample.graphSourceIntersectionAtRank_horizon_eq_raw_of_horizon_le_right
        hlam0 hlamHalf B T r hsourceHorizonH
    have htargetEq :=
      sample.graphTargetIntersectionAtRank_horizon_eq_raw_of_horizon_le_right
        hlam0 hlamHalf B T r htargetHorizonH
    have hsourceB : B < sample.graphSourceIntersectionAtRank raw r := by
      rw [← hsourceEq]
      exact hsourceHorizonB
    have htargetB : B < sample.graphTargetIntersectionAtRank raw r := by
      rw [← htargetEq]
      exact htargetHorizonB
    have hsourceH : sample.graphSourceIntersectionAtRank raw r ≤ B + (T : ℝ) := by
      rw [← hsourceEq]
      exact hsourceHorizonH
    have htargetH : sample.graphTargetIntersectionAtRank raw r ≤ B + (T : ℝ) := by
      rw [← htargetEq]
      exact htargetHorizonH
    have hsourceTimePositive : (0 : WithTop ℝ≥0) <
        sourceFullRankEventTime hlam0 hlamHalf B r sample := by
      rw [sample.sourceFullRankEventTime_eq_graphSourceElapsed_of_gt
        hlam0 hlamHalf B r hNoTie hsourceB]
      exact WithTop.coe_lt_coe.mpr (NNReal.coe_lt_coe.mp (sub_pos.mpr hsourceB))
    have hnotBothZero : ¬
        (sourceFullRankEventTime hlam0 hlamHalf B r sample = 0 ∧
          targetFullRankEventTime hlam0 hlamHalf B r sample = 0) := by
      rintro ⟨hsourceZero, _⟩
      exact (ne_of_gt hsourceTimePositive) hsourceZero
    have htimeNe :=
      sourceFullRankEventTime_ne_targetFullRankEventTime_of_not_both_zero
        hlam0 hlamHalf B r sample hNoTie hnotBothZero
    have hvalueNe : sample.graphSourceIntersectionAtRank raw r ≠
        sample.graphTargetIntersectionAtRank raw r := by
      intro hvalueEq
      apply htimeNe
      rw [sample.sourceFullRankEventTime_eq_graphSourceElapsed_of_gt
          hlam0 hlamHalf B r hNoTie hsourceB,
        sample.targetFullRankEventTime_eq_graphTargetElapsed_of_gt
          hlam0 hlamHalf B r hNoTie htargetB]
      apply WithTop.coe_eq_coe.mpr
      apply Subtype.ext
      change sample.graphSourceIntersectionAtRank raw r - B =
        sample.graphTargetIntersectionAtRank raw r - B
      rw [hvalueEq]
    rcases lt_or_gt_of_ne hvalueNe with hsourceTarget | htargetSource
    · obtain ⟨hsourceGap, htargetGap⟩ :=
        sample.rawStoppedFullRankGaps_eq_of_source_lt
          hlam0 hlamHalf eta B T r hNoTie hsourceB hsourceTarget htargetH hstop
      rw [hsourceGap, htargetGap, graphSameRankGap, hsourceEq, htargetEq]
      ring
    · obtain ⟨hsourceGap, htargetGap⟩ :=
        sample.rawStoppedFullRankGaps_eq_of_target_lt
          hlam0 hlamHalf eta B T r hNoTie htargetB htargetSource hsourceH hstop
      rw [hsourceGap, htargetGap, graphSameRankGap, hsourceEq, htargetEq]
      ring
  · rw [ite_eq_right hbulk]
    have hsourceGap : sourceInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample = 0 := by
      rw [sourceInteriorStoppedFullRankGap, ite_eq_right]
      intro hactive
      apply hbulk
      exact sample.horizon_bulkRetained_of_sourceStoppedFullRankGap_active
        hlam0 hlamHalf eta B T r hNoTie hstop hactive
    have htargetGap : targetInteriorStoppedFullRankGap
        hlam0 hlamHalf eta B B 0 T r sample = 0 := by
      rw [targetInteriorStoppedFullRankGap, ite_eq_right]
      intro hactive
      apply hbulk
      exact sample.horizon_bulkRetained_of_targetStoppedFullRankGap_active
        hlam0 hlamHalf eta B T r hNoTie hstop hactive
    rw [hsourceGap, htargetGap]
    norm_num

/-- The abstract stopped-rank energy of the actual raw labels is exactly the deterministic
horizon graph's bulk-retained same-rank energy. -/
theorem rawStoppedRankGapEnergy_eq_horizonBulkRetainedRankEnergy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime
      hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0)) :
    CountingProcess.stoppedRankGapEnergy
        (sourceInteriorStoppedFullRankGap
          (n := n) hlam0 hlamHalf eta B B 0 T)
        (targetInteriorStoppedFullRankGap
          (n := n) hlam0 hlamHalf eta B B 0 T) sample =
      sample.graphBulkRetainedRankEnergy
        (sample.horizonFeedbackGraph hlam0 hlamHalf B T) B (B + (T : ℝ)) := by
  apply sample.stoppedRankGapEnergy_eq_graphBulkRetainedRankEnergy_of_pointwise
  intro r
  exact sample.rawStoppedFullRankGaps_sq_sum_eq_horizon_bulkRetained
    hlam0 hlamHalf eta B T r hNoTie hstop

/-! ## Actual-good-event transport from stopped to horizon graph -/

/-- On the actual stopped A2 good event, the raw stopped-rank energy is exactly the horizon
graph's bulk-retained same-rank energy. -/
theorem feedbackA2StoppedGoodEvent.rawStoppedRankGapEnergy_eq_horizonBulk
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n) (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num))
        eta amplitude globalQ endpointQ B T R) :
    CountingProcess.stoppedRankGapEnergy
        (sourceInteriorStoppedFullRankGap
          (n := n) hlam0.le (hlam.trans (by norm_num)) eta B B 0 T)
        (targetInteriorStoppedFullRankGap
          (n := n) hlam0.le (hlam.trans (by norm_num)) eta B B 0 T) sample =
      sample.graphBulkRetainedRankEnergy
        (sample.horizonFeedbackGraph
          hlam0.le (hlam.trans (by norm_num)) B T)
        B (B + (T : ℝ)) := by
  have hA1 : sample ∈ feedbackA1GoodEvent n lam B 0 := by
    by_contra hbad
    apply hgood
    exact Or.inr (Or.inr (Or.inl hbad))
  have hNoTie := feedbackA1GoodEvent.noFeedbackTies hA1
  have hstop := feedbackA2StoppedGoodEvent.safeFeedbackA1StopTime_eq_horizon
    sample hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood
  exact sample.rawStoppedRankGapEnergy_eq_horizonBulkRetainedRankEnergy
    hlam0.le (hlam.trans (by norm_num)) eta B T hNoTie hstop

/-- The same exact raw energy is the bulk-retained energy of the actual stopped-continuation
graph; this is the stopped-graph version used after `(1.39e)`. -/
theorem feedbackA2StoppedGoodEvent.rawStoppedRankGapEnergy_eq_stoppedGraphBulk
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n) (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num))
        eta amplitude globalQ endpointQ B T R) :
    CountingProcess.stoppedRankGapEnergy
        (sourceInteriorStoppedFullRankGap
          (n := n) hlam0.le (hlam.trans (by norm_num)) eta B B 0 T)
        (targetInteriorStoppedFullRankGap
          (n := n) hlam0.le (hlam.trans (by norm_num)) eta B B 0 T) sample =
      sample.graphBulkRetainedRankEnergy
        (sample.stoppedContinuationFeedbackGraph
          hlam0.le (hlam.trans (by norm_num)) eta B T)
        B (B + (T : ℝ)) := by
  have hgraph :=
    feedbackA2StoppedGoodEvent.stoppedContinuationFeedbackGraph_eq_horizon
      sample hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood
  rw [hgraph]
  exact feedbackA2StoppedGoodEvent.rawStoppedRankGapEnergy_eq_horizonBulk
    sample hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood

/-- On the actual stopped A2 good event, all graph-side intersection, rank-gap, and energy data
transport from the stopped-continuation graph to the deterministic-horizon graph. -/
theorem feedbackA2StoppedGoodEvent.stoppedGraph_data_eq_horizon
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n) (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num))
        eta amplitude globalQ endpointQ B T R) :
    let stopped := sample.stoppedContinuationFeedbackGraph
      hlam0.le (hlam.trans (by norm_num)) eta B T
    let horizon := sample.horizonFeedbackGraph
      hlam0.le (hlam.trans (by norm_num)) B T
    (∀ i, sample.sourceIntersection stopped i =
        sample.sourceIntersection horizon i) ∧
      (∀ j, sample.targetIntersection stopped j =
        sample.targetIntersection horizon j) ∧
      (∀ r, sample.graphSourceIntersectionAtRank stopped r =
        sample.graphSourceIntersectionAtRank horizon r) ∧
      (∀ r, sample.graphTargetIntersectionAtRank stopped r =
        sample.graphTargetIntersectionAtRank horizon r) ∧
      (∀ r, sample.graphSameRankGap stopped r =
        sample.graphSameRankGap horizon r) ∧
      sample.graphComparisonEnergy stopped = sample.graphComparisonEnergy horizon ∧
      sample.graphSameRankGapEnergy stopped = sample.graphSameRankGapEnergy horizon ∧
      sample.graphLeftBoundaryRetainedRankEnergy stopped B (B + (T : ℝ)) =
        sample.graphLeftBoundaryRetainedRankEnergy horizon B (B + (T : ℝ)) ∧
      sample.graphBulkRetainedRankEnergy stopped B (B + (T : ℝ)) =
        sample.graphBulkRetainedRankEnergy horizon B (B + (T : ℝ)) ∧
      sample.graphRightTerminalRankEnergy stopped (B + (T : ℝ)) =
        sample.graphRightTerminalRankEnergy horizon (B + (T : ℝ)) := by
  have hgraph :=
    feedbackA2StoppedGoodEvent.stoppedContinuationFeedbackGraph_eq_horizon
      sample hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood
  dsimp only
  rw [hgraph]
  exact ⟨fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl,
    fun _ ↦ rfl, rfl, rfl, rfl, rfl, rfl⟩

end FiniteSample

end OTSelector
