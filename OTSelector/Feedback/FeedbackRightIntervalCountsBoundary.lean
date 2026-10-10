import OTSelector.Feedback.FeedbackRightIntervalCounts
import OTSelector.Probability.FiniteIntervalCountsProduct
import OTSelector.Feedback.FeedbackRightIntensityRawRectangleSnapshot
import OTSelector.Feedback.FeedbackRightIntensityConditionalLaw

/-!
# Interval-count certificates retaining the actual right-boundary snapshot

The interval counts below retain the boundary's unseen membership pattern.  Their integer-grid
certificate is jointly measurable in the snapshot and the completed finite sample, as required
by the exact conditional law under the original finite-sample measure.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace OTSelector
namespace FiniteSample

variable {n : ℕ}

/-- Unseen source labels with frozen crossing coordinate strictly inside an interval. -/
noncomputable def rightBoundarySourceIntervalCount
    (lam xR s t : ℝ) (boundary : RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  ∑ i : Fin n, if i ∉ (revealedSnapshotState boundary).seenSource ∧
      completed.sourcePhase i (rightBoundaryFrozenHeight lam xR boundary) ∈ Ioo s t
    then 1 else 0

/-- Symmetric open-interval count for the target labels. -/
noncomputable def rightBoundaryTargetIntervalCount
    (lam xR s t : ℝ) (boundary : RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  ∑ i : Fin n, if i ∉ (revealedSnapshotState boundary).seenTarget ∧
      completed.targetPhase i (rightBoundaryFrozenHeight lam xR boundary) ∈ Ioo s t
    then 1 else 0

theorem measurable_rightBoundarySourceIntervalCount (lam xR s t : ℝ) :
    Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
      rightBoundarySourceIntervalCount lam xR s t p.1 p.2 := by
  classical
  unfold rightBoundarySourceIntervalCount
  apply Finset.measurable_sum
  intro i _
  have hphase : Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
      p.2.sourcePhase i (rightBoundaryFrozenHeight lam xR p.1) := by
    unfold sourcePhase sourceSlope
    fun_prop
  have hseen : MeasurableSet {p : RevealedSnapshot n × FiniteSample n |
      i ∈ (revealedSnapshotState p.1).seenSource} :=
    (FeedbackStepState.measurable_seenSource.comp
      (measurable_revealedSnapshotState.comp measurable_fst)) (measurableSet_mem_finset i)
  exact Measurable.ite (hseen.compl.inter (hphase measurableSet_Ioo))
    measurable_const measurable_const

theorem measurable_rightBoundaryTargetIntervalCount (lam xR s t : ℝ) :
    Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
      rightBoundaryTargetIntervalCount lam xR s t p.1 p.2 := by
  classical
  unfold rightBoundaryTargetIntervalCount
  apply Finset.measurable_sum
  intro i _
  have hphase : Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
      p.2.targetPhase i (rightBoundaryFrozenHeight lam xR p.1) := by
    unfold targetPhase targetSlope
    fun_prop
  have hseen : MeasurableSet {p : RevealedSnapshot n × FiniteSample n |
      i ∈ (revealedSnapshotState p.1).seenTarget} :=
    (FeedbackStepState.measurable_seenTarget.comp
      (measurable_revealedSnapshotState.comp measurable_fst)) (measurableSet_mem_finset i)
  exact Measurable.ite (hseen.compl.inter (hphase measurableSet_Ioo))
    measurable_const measurable_const

/-- Both colors satisfy the lower-count inequality at every integer pair in the tail window. -/
def rightBoundaryIntervalGridGood (N : ℕ) (lam xR c r : ℝ)
    (hi : RevealedSnapshot n → ℝ) (boundary : RevealedSnapshot n)
    (completed : FiniteSample n) : Prop :=
  ∀ a b : Fin (N + 1), xR ≤ (a.val : ℝ) → (a.val : ℝ) ≤ b.val →
    (b.val : ℝ) ≤ hi boundary →
    c * ((b.val : ℝ) - a.val) - r ≤
      rightBoundarySourceIntervalCount lam xR a.val b.val boundary completed ∧
    c * ((b.val : ℝ) - a.val) - r ≤
      rightBoundaryTargetIntervalCount lam xR a.val b.val boundary completed

theorem measurableSet_rightBoundaryIntervalGridGood
    (N : ℕ) (lam xR c r : ℝ) {hi : RevealedSnapshot n → ℝ} (hhi : Measurable hi) :
    MeasurableSet {p : RevealedSnapshot n × FiniteSample n |
      rightBoundaryIntervalGridGood N lam xR c r hi p.1 p.2} := by
  simp only [rightBoundaryIntervalGridGood, ofPred_forall]
  refine MeasurableSet.iInter fun (a : Fin (N + 1)) ↦
    MeasurableSet.iInter fun (b : Fin (N + 1)) ↦ ?_
  refine MeasurableSet.iInter fun _ ↦ MeasurableSet.iInter fun _ ↦ ?_
  have hbound : MeasurableSet {p : RevealedSnapshot n × FiniteSample n |
      (b.val : ℝ) ≤ hi p.1} :=
    measurableSet_le measurable_const (hhi.comp measurable_fst)
  have hs : MeasurableSet {p : RevealedSnapshot n × FiniteSample n |
      c * ((b.val : ℝ) - a.val) - r ≤
        rightBoundarySourceIntervalCount lam xR a.val b.val p.1 p.2} :=
    measurableSet_le measurable_const
      (measurable_rightBoundarySourceIntervalCount (n := n) lam xR a.val b.val)
  have ht : MeasurableSet {p : RevealedSnapshot n × FiniteSample n |
      c * ((b.val : ℝ) - a.val) - r ≤
        rightBoundaryTargetIntervalCount lam xR a.val b.val p.1 p.2} :=
    measurableSet_le measurable_const
      (measurable_rightBoundaryTargetIntervalCount (n := n) lam xR a.val b.val)
  convert hbound.compl.union (hs.inter ht) using 1
  ext p
  simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_inter_iff]
  tauto

end FiniteSample
namespace RightTail

variable {n : ℕ}

/-- The snapshot source interval count is exactly the count of its unseen source coordinates. -/
theorem sourceIntervalCount_merge_eq_groupCount
    (lam xR s t : ℝ) (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    FiniteSample.rightBoundarySourceIntervalCount lam xR s t
        (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) =
      FiniteIntervalCounts.groupCount (unseenSourceGroup S) unseen
        (sourcePhase n (segmentCurve state.x state.p (state.slope lam) xR) ⁻¹' Ioo s t) := by
  classical
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let phase : FeedbackLabel n → ℝ := fun label ↦ match label with
    | Sum.inl i => (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i q
    | Sum.inr i => (finiteSampleSeenUnseenMerge S seen unseen).targetPhase i q
  have hsum := sum_unseenSourceGroup S (fun label ↦ if phase label ∈ Ioo s t then 1 else 0)
  calc
    FiniteSample.rightBoundarySourceIntervalCount lam xR s t
        (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) =
        ∑ label ∈ unseenSourceGroup S, if phase label ∈ Ioo s t then (1 : ℝ) else 0 := by
      rw [hsum]
      change (∑ i : Fin n, if i ∉ state.seenSource ∧
        (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i q ∈ Ioo s t
        then 1 else 0) = _
      apply Finset.sum_congr rfl
      intro i _
      simp only [phase, hsource, ite_and]
    _ = FiniteIntervalCounts.groupCount (unseenSourceGroup S) unseen
        (sourcePhase n q ⁻¹' Ioo s t) := by
      unfold FiniteIntervalCounts.groupCount
      apply Finset.sum_congr rfl
      intro label hlabel
      have heq := fixedPhase_unseen_eq_mergePhase q S seen unseen label
      change fixedPhase n q (unseenSourceGroup S) label (unseen label) = phase label at heq
      simp only [fixedPhase, ite_eq_left hlabel] at heq
      simp [RelativeVC.indicatorReal, Set.indicator_apply, heq]

/-- The target interval count is the complementary group count in the same product sample. -/
theorem targetIntervalCount_merge_eq_groupCount
    (lam xR s t : ℝ) (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (htarget : ∀ i : Fin n, (Sum.inr i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenTarget)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    FiniteSample.rightBoundaryTargetIntervalCount lam xR s t
        (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) =
      FiniteIntervalCounts.groupCount (unseenSourceGroup S)ᶜ unseen
        (targetPhase n (segmentCurve state.x state.p (state.slope lam) xR) ⁻¹' Ioo s t) := by
  classical
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let phase : FeedbackLabel n → ℝ := fun label ↦ match label with
    | Sum.inl i => (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i q
    | Sum.inr i => (finiteSampleSeenUnseenMerge S seen unseen).targetPhase i q
  have hsum := sum_unseenTargetGroup S (fun label ↦ if phase label ∈ Ioo s t then 1 else 0)
  calc
    FiniteSample.rightBoundaryTargetIntervalCount lam xR s t
        (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) =
        ∑ label ∈ (unseenSourceGroup S)ᶜ, if phase label ∈ Ioo s t then (1 : ℝ) else 0 := by
      rw [hsum]
      change (∑ i : Fin n, if i ∉ state.seenTarget ∧
        (finiteSampleSeenUnseenMerge S seen unseen).targetPhase i q ∈ Ioo s t
        then 1 else 0) = _
      apply Finset.sum_congr rfl
      intro i _
      simp only [phase, htarget, ite_and]
    _ = FiniteIntervalCounts.groupCount (unseenSourceGroup S)ᶜ unseen
        (targetPhase n q ⁻¹' Ioo s t) := by
      unfold FiniteIntervalCounts.groupCount
      apply Finset.sum_congr rfl
      intro label hlabel
      have heq := fixedPhase_unseen_eq_mergePhase q S seen unseen label
      change fixedPhase n q (unseenSourceGroup S) label (unseen label) = phase label at heq
      simp only [fixedPhase, ite_eq_right (Finset.mem_compl.mp hlabel)] at heq
      simp [RelativeVC.indicatorReal, Set.indicator_apply, heq]

end RightTail
end OTSelector
