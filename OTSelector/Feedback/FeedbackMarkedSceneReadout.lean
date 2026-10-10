import OTSelector.Feedback.FeedbackMarkedSpatialAverage
import OTSelector.Feedback.FeedbackBulkBackwardWindow
import OTSelector.Matching.FeedbackSceneJoining
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentRegularity

/-! # Actual finite scenes read the original marked event process -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal Topology
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.LocalConfiguration

/-- Finite marked window counts retain every original label and mark. -/
theorem markedWindow_ofTuple {n : ℕ} (points : Fin n → MatchingPoint)
    (ψ : UnitMark → ℝ) (a b : ℝ) :
    (∫ p in spatialIoc a b, ψ p.2 ∂countingMeasure (ofTuple matchingPointBase points)) =
      ∑ i, if a < (points i).1 ∧ (points i).1 ≤ b then ψ (points i).2 else 0 := by
  rw [countingMeasure_ofTuple, ← integral_indicator (measurableSet_spatialIoc a b),
    integral_finsetSum_measure (fun i _ ↦ integrable_dirac (by simp))]
  simp only [integral_dirac, spatialIoc, mem_preimage, mem_Ioc, indicator_apply]

end OTSelector.PointProcess.LocalConfiguration

namespace OTSelector.FiniteSample
open CountingProcess PointProcess
variable {n : ℕ} {lam : ℝ}

/-- Elapsed seen labels are precisely the actual raw-graph labels behind the cut. -/
theorem feedbackStateAtElapsed_seenSource_eq_intersection_filter
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (x0 p0 : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) :
    (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource =
      Finset.univ.filter (fun i ↦ sample.sourceIntersection
        (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤ x0 + (t : ℝ)) := by
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 t
  have hseen := sample.feedbackState_seenSource_eq_sourceIntersection_filter
    hlam0 hlamHalf x0 p0 (show I.val ≤ 2*n from by omega)
  have hk : sample.feedbackKnot lam x0 p0 I.val ≤ x0 + (t : ℝ) := by
    have hm := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
    have hleft : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 I.val ≤ t := by
      simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    have hh := NNReal.coe_le_coe.mp hleft
    change sample.feedbackKnot lam x0 p0 I.val - x0 ≤ (t : ℝ) at hh
    linarith
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    have him : i ∈ (sample.feedbackState lam x0 p0 I.val).seenSource := hi
    rw [hseen] at him
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp him).2.trans hk⟩
  · have hc := feedbackStateAtElapsed_seenSource_card_eq_sourceIntersectionCount
      sample hlam0 hlamHalf x0 p0 t
    exact le_of_eq hc.symm

/-- The original labelled event time equals the actual raw intersection threshold. -/
theorem sourceEventTime_le_iff_raw_intersection
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (x0 p0 : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam x0 p0) (i : Fin n) :
    sourceEventTime hlam0 hlamHalf x0 p0 i sample ≤ (t : WithTop ℝ≥0) ↔
      x0 < sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ∧
        sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤ x0 + (t : ℝ) := by
  rw [sample.sourceEventTime_le_iff_seen_diff,
    feedbackStateAtElapsed_seenSource_eq_intersection_filter,
    sample.initialSeenSource_eq_sourceIntersection_filter hlam0 hlamHalf x0 p0]
  simp only [hNoTie, true_and, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
    true_and, not_le]
  exact and_comm

/-- Freezing after the cut preserves the individual threshold event. -/
theorem sourceIntersection_stopped_le_iff_raw_of_survival
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    (sample : FiniteSample n)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (i : Fin n) {x : ℝ} (hx : x ≤ B + (T : ℝ)) :
    sample.sourceIntersection (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) i ≤ x ↔
      sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i ≤ x := by
  rw [sample.stoppedContinuationFeedbackGraph_eq_horizon hlam0 hlamHalf eta B T hstop,
    sample.sourceIntersection_le_iff, sample.sourceIntersection_le_iff,
    sample.horizonFeedbackGraph_curve_eq_feedbackCurve_of_le_right hlam0 hlamHalf B T hx]
  rfl

/-- Strict survival identifies each retained labelled event with the frozen-graph intersection. -/
theorem safeSourceBulkEventTime_le_iff_stopped_intersection
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (ht : t < T) (i : Fin n) :
    safeSourceBulkEventTime hlam0 hlamHalf B B 0 i sample ≤ (t : WithTop ℝ≥0) ↔
      B < sample.sourceIntersection (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) i ∧
        sample.sourceIntersection (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) i ≤ B + (t : ℝ) := by
  have hexit : (t : WithTop ℝ≥0) < safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
    apply (WithTop.coe_lt_coe.mpr ht).trans_le
    rw [← hstop]
    exact min_le_left _ _
  have heq : safeSourceBulkEventTime hlam0 hlamHalf B B 0 i sample ≤ (t : WithTop ℝ≥0) ↔
      sourceEventTime hlam0 hlamHalf B 0 i sample ≤ (t : WithTop ℝ≥0) := by
    change thinnedEventTime _ _ _ ≤ _ ↔ _
    rw [thinnedEventTime_le_iff]
    exact ⟨And.right, fun h ↦ ⟨eventAccepted_safeFeedbackBulkMask_source_of_le_of_lt_safeFeedbackBulkExitTime
      hlam0 hlamHalf B B 0 t sample i h hexit, h⟩⟩
  rw [heq, sourceEventTime_le_iff_raw_intersection hlam0 hlamHalf B 0 t sample hNoTie i]
  have hzero := sourceIntersection_stopped_le_iff_raw_of_survival hlam0 hlamHalf eta B T sample hstop i
    (x := B) (by linarith [T.2])
  have ht' := sourceIntersection_stopped_le_iff_raw_of_survival hlam0 hlamHalf eta B T sample hstop i
    (x := B+(t:ℝ)) (by exact add_le_add le_rfl (show (t:ℝ) ≤ T from ht.le))
  simpa only [not_le] using and_congr (not_congr hzero).symm ht'.symm

/-- The real marked scene window is exactly an increment of the actual retained mark sum. -/
theorem firstEventTestCount_source_stoppedScene_eq_markSum_increment
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T s t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (ht : s+t < T) (ψ : UnitMark → ℝ) :
    LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+(s:ℝ))))) true ψ t =
      safeSourceBulkMarkSum hlam0 hlamHalf B B 0 ψ (s+t) sample -
        safeSourceBulkMarkSum hlam0 hlamHalf B B 0 ψ s sample := by
  change (∫ p in LocalConfiguration.spatialIoc 0 (t:ℝ), ψ p.2 ∂LocalConfiguration.countingMeasure
    (LocalConfiguration.ofTuple _ (sample.rootedSourcePoint
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B+(s:ℝ))))) = _
  rw [LocalConfiguration.markedWindow_ofTuple, safeSourceBulkMarkSum,
    finiteEventWeightedSum_sub _ _ (le_add_of_nonneg_right t.2)]
  apply Finset.sum_congr rfl
  intro i _
  have hsT : s < T := (le_add_of_nonneg_right t.2).trans_lt ht
  have hs := safeSourceBulkEventTime_le_iff_stopped_intersection
    hlam0 hlamHalf eta B T s sample hNoTie hstop hsT i
  have hst := safeSourceBulkEventTime_le_iff_stopped_intersection
    hlam0 hlamHalf eta B T (s+t) sample hNoTie hstop ht i
  change (if 0 < sample.sourceIntersection _ i - (B+(s:ℝ)) ∧
      sample.sourceIntersection _ i - (B+(s:ℝ)) ≤ (t:ℝ) then ψ (sample.sourceMark i) else 0) =
    (if (s : WithTop ℝ≥0) < safeSourceBulkEventTime hlam0 hlamHalf B B 0 i sample ∧
      safeSourceBulkEventTime hlam0 hlamHalf B B 0 i sample ≤ ((s+t) : WithTop ℝ≥0)
      then ψ (sample.sourceMark i) else 0)
  simp only [WithTop.coe_add] at hst
  congr 1
  apply propext
  rw [← not_le (a := safeSourceBulkEventTime hlam0 hlamHalf B B 0 i sample)
    (b := (s : WithTop ℝ≥0)), hs, hst, NNReal.coe_add]
  constructor
  · rintro ⟨hleft, hright⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, hle⟩
      linarith
    · linarith [s.2]
    · linarith
  · rintro ⟨hnot, hleft, hright⟩
    constructor <;> push Not at hnot <;> linarith [hnot hleft]

/-- Elapsed seen labels are precisely the actual raw-graph labels behind the cut. -/
theorem feedbackStateAtElapsed_seenTarget_eq_intersection_filter
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (x0 p0 : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) :
    (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget =
      Finset.univ.filter (fun i ↦ sample.targetIntersection
        (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤ x0 + (t : ℝ)) := by
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 t
  have hseen := sample.feedbackState_seenTarget_eq_targetIntersection_filter
    hlam0 hlamHalf x0 p0 (show I.val ≤ 2*n from by omega)
  have hk : sample.feedbackKnot lam x0 p0 I.val ≤ x0 + (t : ℝ) := by
    have hm := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
    have hleft : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 I.val ≤ t := by
      simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    have hh := NNReal.coe_le_coe.mp hleft
    change sample.feedbackKnot lam x0 p0 I.val - x0 ≤ (t : ℝ) at hh
    linarith
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    have him : i ∈ (sample.feedbackState lam x0 p0 I.val).seenTarget := hi
    rw [hseen] at him
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp him).2.trans hk⟩
  · have hc := feedbackStateAtElapsed_seenTarget_card_eq_targetIntersectionCount
      sample hlam0 hlamHalf x0 p0 t
    exact le_of_eq hc.symm

/-- The original labelled event time equals the actual raw intersection threshold. -/
theorem targetEventTime_le_iff_raw_intersection
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (x0 p0 : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam x0 p0) (i : Fin n) :
    targetEventTime hlam0 hlamHalf x0 p0 i sample ≤ (t : WithTop ℝ≥0) ↔
      x0 < sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ∧
        sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤ x0 + (t : ℝ) := by
  rw [sample.targetEventTime_le_iff_seen_diff,
    feedbackStateAtElapsed_seenTarget_eq_intersection_filter,
    sample.initialSeenTarget_eq_targetIntersection_filter hlam0 hlamHalf x0 p0]
  simp only [hNoTie, true_and, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
    true_and, not_le]
  exact and_comm

/-- Freezing after the cut preserves the individual threshold event. -/
theorem targetIntersection_stopped_le_iff_raw_of_survival
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    (sample : FiniteSample n)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (i : Fin n) {x : ℝ} (hx : x ≤ B + (T : ℝ)) :
    sample.targetIntersection (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) i ≤ x ↔
      sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf B 0) i ≤ x := by
  rw [sample.stoppedContinuationFeedbackGraph_eq_horizon hlam0 hlamHalf eta B T hstop,
    sample.targetIntersection_le_iff, sample.targetIntersection_le_iff,
    sample.horizonFeedbackGraph_curve_eq_feedbackCurve_of_le_right hlam0 hlamHalf B T hx]
  rfl

/-- Strict survival identifies each retained labelled event with the frozen-graph intersection. -/
theorem safeTargetBulkEventTime_le_iff_stopped_intersection
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (ht : t < T) (i : Fin n) :
    safeTargetBulkEventTime hlam0 hlamHalf B B 0 i sample ≤ (t : WithTop ℝ≥0) ↔
      B < sample.targetIntersection (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) i ∧
        sample.targetIntersection (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) i ≤ B + (t : ℝ) := by
  have hexit : (t : WithTop ℝ≥0) < safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
    apply (WithTop.coe_lt_coe.mpr ht).trans_le
    rw [← hstop]
    exact min_le_left _ _
  have heq : safeTargetBulkEventTime hlam0 hlamHalf B B 0 i sample ≤ (t : WithTop ℝ≥0) ↔
      targetEventTime hlam0 hlamHalf B 0 i sample ≤ (t : WithTop ℝ≥0) := by
    change thinnedEventTime _ _ _ ≤ _ ↔ _
    rw [thinnedEventTime_le_iff]
    exact ⟨And.right, fun h ↦ ⟨eventAccepted_safeFeedbackBulkMask_target_of_le_of_lt_safeFeedbackBulkExitTime
      hlam0 hlamHalf B B 0 t sample i h hexit, h⟩⟩
  rw [heq, targetEventTime_le_iff_raw_intersection hlam0 hlamHalf B 0 t sample hNoTie i]
  have hzero := targetIntersection_stopped_le_iff_raw_of_survival hlam0 hlamHalf eta B T sample hstop i
    (x := B) (by linarith [T.2])
  have ht' := targetIntersection_stopped_le_iff_raw_of_survival hlam0 hlamHalf eta B T sample hstop i
    (x := B+(t:ℝ)) (by exact add_le_add le_rfl (show (t:ℝ) ≤ T from ht.le))
  simpa only [not_le] using and_congr (not_congr hzero).symm ht'.symm

/-- The real marked scene window is exactly an increment of the actual retained mark sum. -/
theorem firstEventTestCount_target_stoppedScene_eq_markSum_increment
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T s t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (ht : s+t < T) (ψ : UnitMark → ℝ) :
    LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+(s:ℝ))))) false ψ t =
      safeTargetBulkMarkSum hlam0 hlamHalf B B 0 ψ (s+t) sample -
        safeTargetBulkMarkSum hlam0 hlamHalf B B 0 ψ s sample := by
  change (∫ p in LocalConfiguration.spatialIoc 0 (t:ℝ), ψ p.2 ∂LocalConfiguration.countingMeasure
    (LocalConfiguration.ofTuple _ (sample.rootedTargetPoint
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B+(s:ℝ))))) = _
  rw [LocalConfiguration.markedWindow_ofTuple, safeTargetBulkMarkSum,
    finiteEventWeightedSum_sub _ _ (le_add_of_nonneg_right t.2)]
  apply Finset.sum_congr rfl
  intro i _
  have hsT : s < T := (le_add_of_nonneg_right t.2).trans_lt ht
  have hs := safeTargetBulkEventTime_le_iff_stopped_intersection
    hlam0 hlamHalf eta B T s sample hNoTie hstop hsT i
  have hst := safeTargetBulkEventTime_le_iff_stopped_intersection
    hlam0 hlamHalf eta B T (s+t) sample hNoTie hstop ht i
  change (if 0 < sample.targetIntersection _ i - (B+(s:ℝ)) ∧
      sample.targetIntersection _ i - (B+(s:ℝ)) ≤ (t:ℝ) then ψ (sample.targetMark i) else 0) =
    (if (s : WithTop ℝ≥0) < safeTargetBulkEventTime hlam0 hlamHalf B B 0 i sample ∧
      safeTargetBulkEventTime hlam0 hlamHalf B B 0 i sample ≤ ((s+t) : WithTop ℝ≥0)
      then ψ (sample.targetMark i) else 0)
  simp only [WithTop.coe_add] at hst
  congr 1
  apply propext
  rw [← not_le (a := safeTargetBulkEventTime hlam0 hlamHalf B B 0 i sample)
    (b := (s : WithTop ℝ≥0)), hs, hst, NNReal.coe_add]
  constructor
  · rintro ⟨hleft, hright⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, hle⟩
      linarith
    · linarith [s.2]
    · linarith
  · rintro ⟨hnot, hleft, hright⟩
    constructor <;> push Not at hnot <;> linarith [hnot hleft]

/-- The scene current is the original finite cut discrepancy at the translated coordinate. -/
theorem feedbackEnvironmentCurrent_rootedMatchingScene
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n) (z x : ℝ) :
    Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment
      (sample.rootedMatchingScene graph σ z)) x =
      (sample.sourceIntersectionCount graph (z+x) : ℤ) - sample.targetIntersectionCount graph (z+x) := by
  change (MatchingScene.reroot x (sample.rootedMatchingScene graph σ z)).path.rootCurrent = _
  rw [sample.reroot_rootedMatchingScene]
  rfl

/-- On survival, the original finite environment current is the actual post-jump current. -/
theorem feedbackEnvironmentCurrent_stoppedScene_eq_safeCurrentAt
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T u : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hu : u ≤ T) (z x : ℝ) (hzx : z+x = B+(u:ℝ)) :
    Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment
      (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T z)) x =
      safeCurrentAt hlam0 hlamHalf B 0 u sample := by
  rw [stoppedRootedEuclideanScene, rootedEuclideanScene,
    feedbackEnvironmentCurrent_rootedMatchingScene, hzx]
  have hs := sourceFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T u sample hNoTie hstop hu
  have ht := targetFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T u sample hNoTie hstop hu
  change sourceFullCount hlam0 hlamHalf B u sample = sample.sourceIntersectionCount _ _ at hs
  change targetFullCount hlam0 hlamHalf B u sample = sample.targetIntersectionCount _ _ at ht
  rw [← hs, ← ht]
  rw [sourceFullCount_eq_initial_card_add_safeSourceCount,
    targetFullCount_eq_initial_card_add_safeTargetCount, safeCurrentAt_eq_K0_add_counts]
  simp only [Nat.cast_add, safeK0, ite_eq_left hNoTie, initialFeedbackCurrent]
  ring

end OTSelector.FiniteSample

namespace OTSelector.CountingProcess

private theorem marked_timeMeasure_singleton_zero (a : ℝ≥0) :
    timeMeasure ({a} : Set ℝ≥0) = 0 := by
  rw [timeMeasure, Measure.map_apply measurable_real_toNNReal (measurableSet_singleton a)]
  rw [Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton a))]
  have hpre : Real.toNNReal ⁻¹' ({a} : Set ℝ≥0) ∩ Ici (0 : ℝ) = ({(a : ℝ)} : Set ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ici]
    constructor
    · rintro ⟨hxa, hx0⟩
      have hxcoe : Real.toNNReal x = Real.toNNReal (a : ℝ) := by simpa using hxa
      exact (Real.toNNReal_eq_toNNReal_iff hx0 a.2).mp hxcoe
    · intro hxa
      subst x
      exact ⟨Real.toNNReal_coe, a.2⟩
  rw [hpre, Real.volume_singleton]

/-- A finite labelled process has the same left and right count at almost every time. -/
theorem countBefore_finiteEventCountTop_ae_eq {Ω : Type*} {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (ω : Ω) :
    ∀ᵐ t ∂timeMeasure, countBefore (finiteEventCountTop ξ) t ω = finiteEventCountTop ξ t ω := by
  have hi (i : Fin m) : ∀ᵐ t : ℝ≥0 ∂timeMeasure, ξ i ω ≠ (t : WithTop ℝ≥0) := by
    rcases eq_or_ne (ξ i ω) ⊤ with htop | hfin
    · exact ae_of_all _ fun t ↦ by rw [htop]; exact WithTop.top_ne_coe
    · lift ξ i ω to ℝ≥0 using hfin with s hs
      have h : ∀ᵐ t ∂timeMeasure, t ≠ s := by
        apply ae_iff.mpr
        simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using marked_timeMeasure_singleton_zero s
      filter_upwards [h] with t ht
      intro heq
      exact ht (WithTop.coe_injective heq).symm
  filter_upwards [ae_all_iff.mpr hi] with t ht
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  unfold finiteEventCountTop
  congr 1
  apply Finset.filter_congr
  intro i _
  exact lt_iff_le_and_ne.trans (and_iff_left (ht i))

end OTSelector.CountingProcess

namespace OTSelector.FiniteSample
open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- The actual post-current and predictable pre-current differ only at finitely many times. -/
theorem safePreCurrentAt_ae_eq_safeCurrentAt
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (x0 p0 : ℝ) (sample : FiniteSample n) :
    ∀ᵐ t ∂timeMeasure, safePreCurrentAt hlam0 hlamHalf x0 p0 t sample =
      safeCurrentAt hlam0 hlamHalf x0 p0 t sample := by
  filter_upwards [countBefore_finiteEventCountTop_ae_eq
    (fun i ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) sample,
    countBefore_finiteEventCountTop_ae_eq
    (fun i ↦ targetEventTime hlam0 hlamHalf x0 p0 i) sample] with t hs ht
  rw [safeCurrentAt_eq_K0_add_counts]
  change safeK0 lam x0 p0 sample + (countBefore (safeSourceCount hlam0 hlamHalf x0 p0) t sample : ℤ) -
    countBefore (safeTargetCount hlam0 hlamHalf x0 p0) t sample = _
  change countBefore (safeSourceCount hlam0 hlamHalf x0 p0) t sample =
    safeSourceCount hlam0 hlamHalf x0 p0 t sample at hs
  change countBefore (safeTargetCount hlam0 hlamHalf x0 p0) t sample =
    safeTargetCount hlam0 hlamHalf x0 p0 t sample at ht
  rw [hs, ht]

end OTSelector.FiniteSample

namespace OTSelector
/-- The finite and infinite feedback conventions use exactly the same sign. -/
theorem feedbackSlope_intCast (lam : ℝ) (k : ℤ) :
    feedbackSlope lam (k : ℝ) = lam * Limit.currentSign k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => simp [feedbackSlope, Limit.currentSign]
    | succ n =>
      have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      simp [feedbackSlope, Limit.currentSign, Nat.cast_add, Nat.cast_one, hp]
  | negSucc n =>
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [feedbackSlope, Limit.currentSign, Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    rw [ite_eq_right (by linarith), ite_eq_left (by linarith)]
    ring

end OTSelector
