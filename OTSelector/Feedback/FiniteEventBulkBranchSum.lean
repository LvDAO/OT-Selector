import OTSelector.Feedback.FiniteEventBulkHistorySum
import OTSelector.Feedback.FiniteEventBranchPartition
import OTSelector.Feedback.FiniteHistoryNextEventBridge
import OTSelector.Feedback.FiniteHistoryBulkNextEvent
import OTSelector.Feedback.FiniteHistoryRawConstancy

/-!
# Bulk-thinned event sums over finite history branches

This file is the pathwise bridge from the recursive bulk-thinned event bookkeeping to the
finite `HistoryCellIndex` partition.  The time interval in the event-set interface is an
absolute graph coordinate, whereas the event-time interface uses elapsed `ℝ≥0` time; the
conversion is made explicit in `elapsedFeedbackKnot_mem_Ioc_iff_absolute` below.

The module contains only pathwise equalities and finite reindexing statements.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal Topology

namespace OTSelector

variable {n : ℕ}

open FiniteSample

/-! ## Elapsed time versus absolute coordinate -/

private theorem elapsedFeedbackKnot_mem_Ioc_iff_absolute
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (k : ℕ)
    (s t : ℝ≥0) :
    sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k ∈ Ioc s t ↔
      sample.feedbackKnot lam x0 p0 k ∈ Ioc
        (x0 + (s : ℝ)) (x0 + (t : ℝ)) := by
  constructor
  · intro h
    have hs : (s : ℝ) <
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k : ℝ) :=
      NNReal.coe_lt_coe.mpr h.1
    have ht :
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k : ℝ) ≤ (t : ℝ) :=
      NNReal.coe_le_coe.mpr h.2
    rw [FiniteSample.coe_elapsedFeedbackKnot] at hs ht
    constructor <;> linarith
  · intro h
    have hs : (s : ℝ) <
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k : ℝ) := by
      rw [FiniteSample.coe_elapsedFeedbackKnot]
      linarith [h.1]
    have ht :
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k : ℝ) ≤ (t : ℝ) := by
      rw [FiniteSample.coe_elapsedFeedbackKnot]
      linarith [h.2]
    exact ⟨NNReal.coe_lt_coe.mp hs, NNReal.coe_le_coe.mp ht⟩

/-! ## One-step singleton data -/

private theorem source_singleton_data_of_mem
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (i : Fin n)
    (hNoTie : (state.newSource sample lam).card +
      (state.newTarget sample lam).card ≤ 1)
    (hi : i ∈ state.newSource sample lam) :
    state.newSource sample lam = {i} ∧
      state.newTarget sample lam = ∅ ∧
      state.sourceCoordinate sample lam i = state.nextCoordinate sample lam := by
  classical
  have hsource_pos : 0 < (state.newSource sample lam).card :=
    Finset.card_pos.mpr ⟨i, hi⟩
  have hsource_le : (state.newSource sample lam).card ≤ 1 := by omega
  have hsource_card : (state.newSource sample lam).card = 1 := by omega
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hsource_card
  have hik : i = k := by
    have hi' : i ∈ ({k} : Finset (Fin n)) := by
      rw [← hk]
      exact hi
    simpa using hi'
  have hsource : state.newSource sample lam = {i} := by
    simpa [hik] using hk
  have htarget_card : (state.newTarget sample lam).card = 0 := by omega
  have htarget : state.newTarget sample lam = ∅ :=
    Finset.card_eq_zero.mp htarget_card
  have hcoord : state.sourceCoordinate sample lam i = state.nextCoordinate sample lam := by
    exact (Finset.mem_filter.mp (show i ∈
      (Finset.univ \ state.seenSource).filter
        (fun k ↦ state.sourceCoordinate sample lam k = state.nextCoordinate sample lam) by
          simpa only [FeedbackStepState.newSource, hsource] using hi)).2
  exact ⟨hsource, htarget, hcoord⟩

private theorem target_singleton_data_of_mem
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (j : Fin n)
    (hNoTie : (state.newSource sample lam).card +
      (state.newTarget sample lam).card ≤ 1)
    (hj : j ∈ state.newTarget sample lam) :
    state.newSource sample lam = ∅ ∧
      state.newTarget sample lam = {j} ∧
      state.targetCoordinate sample lam j = state.nextCoordinate sample lam := by
  classical
  have htarget_pos : 0 < (state.newTarget sample lam).card :=
    Finset.card_pos.mpr ⟨j, hj⟩
  have htarget_le : (state.newTarget sample lam).card ≤ 1 := by omega
  have htarget_card : (state.newTarget sample lam).card = 1 := by omega
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp htarget_card
  have hjk : j = k := by
    have hj' : j ∈ ({k} : Finset (Fin n)) := by
      rw [← hk]
      exact hj
    simpa using hj'
  have htarget : state.newTarget sample lam = {j} := by
    simpa [hjk] using hk
  have hsource_card : (state.newSource sample lam).card = 0 := by omega
  have hsource : state.newSource sample lam = ∅ :=
    Finset.card_eq_zero.mp hsource_card
  have hcoord : state.targetCoordinate sample lam j = state.nextCoordinate sample lam := by
    exact (Finset.mem_filter.mp (show j ∈
      (Finset.univ \ state.seenTarget).filter
        (fun k ↦ state.targetCoordinate sample lam k = state.nextCoordinate sample lam) by
          simpa only [FeedbackStepState.newTarget, htarget] using hj)).2
  exact ⟨hsource, htarget, hcoord⟩

/-! ## The realized unseen tuple at a branch -/

private theorem historyBranch_unseenRectangularSetAt_terminal
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let state := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
    feedbackUnseenTuple S sample ∈ feedbackUnseenRectangularSetAt lam state state.x S := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let state := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hAt := historyBranch_historyAtCoordinate_terminal sample hlam0 hlamHalf hbranch
  have hremaining : LiesInStateRemainingAt lam state state.x sample := by
    simpa [HistoryAtCoordinate, state] using hAt.2
  have hmerge : finiteSampleSeenUnseenMerge S
      (feedbackSeenTuple S sample) (feedbackUnseenTuple S sample) = sample :=
    finiteSampleSeenUnseenMerge_split S sample
  have hremaining_merge : LiesInStateRemainingAt lam state state.x
      (finiteSampleSeenUnseenMerge S
        (feedbackSeenTuple S sample) (feedbackUnseenTuple S sample)) := by
    rw [hmerge]
    exact hremaining
  have hrect := (liesInStateRemainingAt_finiteSampleSeenUnseenMerge_iff
    lam state state.x S
    (fun i ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
      sample lam x0 p0 sourcePattern targetPattern history i)
    (fun j ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      sample lam x0 p0 sourcePattern targetPattern history j)
    (feedbackSeenTuple S sample) (feedbackUnseenTuple S sample)).mp hremaining_merge
  exact (mem_feedbackUnseenRectangularSetAt_iff lam state state.x S
    (feedbackUnseenTuple S sample)).2 hrect

/-! ## Source next-label indicator on one realized branch -/

theorem historyBranch_source_bulk_indicator_iff
    (sample : FiniteSample n) {lam B x0 p0 : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hgood : sample.NoFeedbackTies lam x0 p0)
    (m : Fin (2 * n)) (index : HistoryCellIndex n)
    (hindex : index.history.length = m.val ∧
      HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history)
    (i : Fin n) {s t : ℝ≥0} (hst : s ≤ t) :
    (i ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
      index.history).newSource sample lam ∧
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
      feedbackBulkRegion n B
        (sample.feedbackKnot lam x0 p0 (m.val + 1))
        (feedbackKnotValue sample lam x0 p0 (m.val + 1))) ↔
      feedbackUnseenTuple
          (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) sample ∈
        feedbackBulkNextEventSetOfLabel B lam
          (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
          (x0 + (s : ℝ)) (x0 + (t : ℝ))
          (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
          (Sum.inl i) := by
  classical
  let S := feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history
  let state := sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history
  let seen := feedbackSeenTuple S sample
  let unseen := feedbackUnseenTuple S sample
  have hbranch := hindex.2
  have hstate : feedbackState sample lam x0 p0 m.val = state := by
    have h := sample.feedbackState_eq_scheduledState_of_history lam x0 p0
      index.sourcePattern index.targetPattern index.history hbranch.1 hbranch.2
    simpa [state, hindex.1] using h
  have hNoTieState : (state.newSource sample lam).card +
      (state.newTarget sample lam).card ≤ 1 := by
    rw [← hstate]
    exact hgood m.val m.isLt
  have hmerge : finiteSampleSeenUnseenMerge S seen unseen = sample := by
    simp [seen, unseen]
  have hrect : unseen ∈ feedbackUnseenRectangularSetAt lam state state.x S := by
    simpa [S, state, seen, unseen] using
      historyBranch_unseenRectangularSetAt_terminal sample hlam0 hlamHalf hbranch
  have habs : x0 + (s : ℝ) ≤ x0 + (t : ℝ) := by
    simpa [add_comm] using add_le_add_left (NNReal.coe_le_coe.mpr hst) x0
  have hnextKnot : sample.feedbackKnot lam x0 p0 (m.val + 1) =
      state.nextCoordinate sample lam := by
    change (feedbackState sample lam x0 p0 (m.val + 1)).x = _
    rw [feedbackState_succ, hstate]
    rfl
  have hnextValue : sample.feedbackKnotValue lam x0 p0 (m.val + 1) =
      segmentCurve state.x state.p (state.slope lam)
        (state.nextCoordinate sample lam) := by
    change (feedbackState sample lam x0 p0 (m.val + 1)).p = _
    rw [feedbackState_succ, hstate]
    rfl
  have htime := elapsedFeedbackKnot_mem_Ioc_iff_absolute sample hlam0 hlamHalf
    x0 p0 (m.val + 1) s t
  have hlabel_mem_iff : (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource := by
    exact mem_feedbackTerminalLabelSet_inl_iff_seenSource
      sample lam x0 p0 index.sourcePattern index.targetPattern index.history i
  by_cases hiS : (Sum.inl i : FeedbackLabel n) ∈ S
  · have hiSeen : i ∈ state.seenSource := hlabel_mem_iff.mp hiS
    have hnotnew : i ∉ state.newSource sample lam := by
      intro hnew
      exact (Finset.disjoint_left.mp
        (FeedbackStepState.newSource_disjoint_seenSource sample lam state)) hnew hiSeen
    have hnot_unseen : (Sum.inl i : FeedbackLabel n) ∉ feedbackUnseenFinset S := by
      simpa [feedbackUnseenFinset] using hiS
    have hempty : feedbackBulkNextEventSetOfLabel B lam state
        (x0 + (s : ℝ)) (x0 + (t : ℝ)) S (Sum.inl i) =
        (∅ : Set (feedbackUnseenFinset S → MarkedHeight)) := by
      simp [feedbackBulkNextEventSetOfLabel, hnot_unseen]
    rw [hempty]
    simp [S, state, hnotnew]
  · let label : feedbackUnseenFinset S :=
      ⟨Sum.inl i, by simp [feedbackUnseenFinset, hiS]⟩
    have hpoint : sample.sourcePoint i = unseen label := by
      have htuple := congrFun
        (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen) label
      rw [hmerge] at htuple
      simp [unseen, feedbackUnseenTuple, feedbackLabelTuple, label]
    have hfixed : feedbackLabelFixedStateCrossing n lam state label (unseen label) =
        state.sourceCoordinate sample lam i := by
      change sourceFixedStateCrossing n lam state (unseen label) =
        state.sourceCoordinate sample lam i
      rw [FeedbackStepState.sourceCoordinate, ← hpoint]
      rfl
    have hbridge := historyBranch_feedbackNextEventSet_source_iff
      sample hlam0 hlamHalf hbranch seen unseen rfl label i rfl habs
    rw [hmerge] at hbridge
    have hsource_bulk_set :
        unseen ∈ feedbackBulkNextEventSet B lam state
            (x0 + (s : ℝ)) (x0 + (t : ℝ)) S label ↔
          unseen ∈ feedbackNextEventSet lam state
            (x0 + (s : ℝ)) (x0 + (t : ℝ)) S label ∧
          feedbackBulkRegion n B
            (feedbackLabelFixedStateCrossing n lam state label (unseen label))
            (segmentCurve state.x state.p (state.slope lam)
              (feedbackLabelFixedStateCrossing n lam state label (unseen label))) := by
      unfold feedbackBulkNextEventSet
      simp [hrect]
    have hwrap :
        unseen ∈ feedbackBulkNextEventSetOfLabel B lam state
            (x0 + (s : ℝ)) (x0 + (t : ℝ)) S (Sum.inl i) ↔
          unseen ∈ feedbackBulkNextEventSet B lam
            state (x0 + (s : ℝ)) (x0 + (t : ℝ)) S label := by
      simp [feedbackBulkNextEventSetOfLabel, feedbackUnseenFinset, hiS, label]
    have hNoTieState' := hNoTieState
    constructor
    · intro h
      obtain ⟨hsource, htime_mem, hbulk⟩ := h
      obtain ⟨hsource_singleton, htarget_empty, hcoord⟩ :=
        source_singleton_data_of_mem sample lam state i hNoTieState hsource
      have hcoord_knot : state.sourceCoordinate sample lam i =
          sample.feedbackKnot lam x0 p0 (m.val + 1) := by
        rw [hcoord, hnextKnot]
      have hcoord_time : state.sourceCoordinate sample lam i ∈
          Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)) := by
        rw [hcoord_knot]
        exact htime.mp htime_mem
      have hnext : unseen ∈ feedbackNextEventSet lam state
          (x0 + (s : ℝ)) (x0 + (t : ℝ)) S label := by
        apply hbridge.mpr
        exact ⟨hcoord_time, by simpa [hmerge] using hsource_singleton,
          by simpa [hmerge] using htarget_empty⟩
      have hbulk' : feedbackBulkRegion n B
          (feedbackLabelFixedStateCrossing n lam state label (unseen label))
          (segmentCurve state.x state.p (state.slope lam)
            (feedbackLabelFixedStateCrossing n lam state label (unseen label))) := by
        simpa [hfixed, hcoord, hnextKnot, hnextValue] using hbulk
      exact hwrap.mpr (hsource_bulk_set.mpr ⟨hnext, hbulk'⟩)
    · intro h
      have hset := hwrap.mp h
      have hnext_bulk := hsource_bulk_set.mp hset
      have hbridge' := hbridge.mp hnext_bulk.1
      have hsource_singleton : state.newSource sample lam = {i} := by
        simpa [hmerge] using hbridge'.2.1
      have htarget_empty : state.newTarget sample lam = ∅ := by
        simpa [hmerge] using hbridge'.2.2
      have hsource : i ∈ state.newSource sample lam := by
        rw [hsource_singleton]
        simp
      obtain ⟨_, _, hcoord⟩ := source_singleton_data_of_mem sample lam state i
        hNoTieState hsource
      have hcoord_knot : state.sourceCoordinate sample lam i =
          sample.feedbackKnot lam x0 p0 (m.val + 1) := by
        rw [hcoord, hnextKnot]
      have htime_mem : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0
          (m.val + 1) ∈ Ioc s t := by
        apply htime.mpr
        rw [← hcoord_knot]
        exact hbridge'.1
      have hcurve_value : segmentCurve state.x state.p (state.slope lam)
          (state.sourceCoordinate sample lam i) =
          feedbackKnotValue sample lam x0 p0 (m.val + 1) := by
        calc
          segmentCurve state.x state.p (state.slope lam)
              (state.sourceCoordinate sample lam i) =
              segmentCurve state.x state.p (state.slope lam)
                (state.nextCoordinate sample lam) := by rw [hcoord]
          _ = feedbackKnotValue sample lam x0 p0 (m.val + 1) := hnextValue.symm
      have hbulk : feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1)) := by
        have hbulk' := hnext_bulk.2
        rw [hfixed, hcoord_knot] at hbulk'
        have hvalue :
            segmentCurve state.x state.p (state.slope lam)
                (sample.feedbackKnot lam x0 p0 (m.val + 1)) =
              feedbackKnotValue sample lam x0 p0 (m.val + 1) := by
          rw [← hcoord_knot, hcurve_value]
        rw [hvalue] at hbulk'
        exact hbulk'
      exact ⟨hsource, htime_mem, hbulk⟩

/-! ## Target next-label indicator on one realized branch -/

theorem historyBranch_target_bulk_indicator_iff
    (sample : FiniteSample n) {lam B x0 p0 : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hgood : sample.NoFeedbackTies lam x0 p0)
    (m : Fin (2 * n)) (index : HistoryCellIndex n)
    (hindex : index.history.length = m.val ∧
      HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history)
    (j : Fin n) {s t : ℝ≥0} (hst : s ≤ t) :
    (j ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
      index.history).newTarget sample lam ∧
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
      feedbackBulkRegion n B
        (sample.feedbackKnot lam x0 p0 (m.val + 1))
        (feedbackKnotValue sample lam x0 p0 (m.val + 1))) ↔
      feedbackUnseenTuple
          (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) sample ∈
        feedbackBulkNextEventSetOfLabel B lam
          (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
          (x0 + (s : ℝ)) (x0 + (t : ℝ))
          (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
          (Sum.inr j) := by
  classical
  let S := feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history
  let state := sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history
  let seen := feedbackSeenTuple S sample
  let unseen := feedbackUnseenTuple S sample
  have hbranch := hindex.2
  have hstate : feedbackState sample lam x0 p0 m.val = state := by
    have h := sample.feedbackState_eq_scheduledState_of_history lam x0 p0
      index.sourcePattern index.targetPattern index.history hbranch.1 hbranch.2
    simpa [state, hindex.1] using h
  have hNoTieState : (state.newSource sample lam).card +
      (state.newTarget sample lam).card ≤ 1 := by
    rw [← hstate]
    exact hgood m.val m.isLt
  have hmerge : finiteSampleSeenUnseenMerge S seen unseen = sample := by
    simp [seen, unseen]
  have hrect : unseen ∈ feedbackUnseenRectangularSetAt lam state state.x S := by
    simpa [S, state, seen, unseen] using
      historyBranch_unseenRectangularSetAt_terminal sample hlam0 hlamHalf hbranch
  have habs : x0 + (s : ℝ) ≤ x0 + (t : ℝ) := by
    simpa [add_comm] using add_le_add_left (NNReal.coe_le_coe.mpr hst) x0
  have hnextKnot : sample.feedbackKnot lam x0 p0 (m.val + 1) =
      state.nextCoordinate sample lam := by
    change (feedbackState sample lam x0 p0 (m.val + 1)).x = _
    rw [feedbackState_succ, hstate]
    rfl
  have hnextValue : sample.feedbackKnotValue lam x0 p0 (m.val + 1) =
      segmentCurve state.x state.p (state.slope lam)
        (state.nextCoordinate sample lam) := by
    change (feedbackState sample lam x0 p0 (m.val + 1)).p = _
    rw [feedbackState_succ, hstate]
    rfl
  have htime := elapsedFeedbackKnot_mem_Ioc_iff_absolute sample hlam0 hlamHalf
    x0 p0 (m.val + 1) s t
  have hlabel_mem_iff : (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget := by
    exact mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      sample lam x0 p0 index.sourcePattern index.targetPattern index.history j
  by_cases hjS : (Sum.inr j : FeedbackLabel n) ∈ S
  · have hjSeen : j ∈ state.seenTarget := hlabel_mem_iff.mp hjS
    have hnotnew : j ∉ state.newTarget sample lam := by
      intro hnew
      exact (Finset.disjoint_left.mp
        (FeedbackStepState.newTarget_disjoint_seenTarget sample lam state)) hnew hjSeen
    have hnot_unseen : (Sum.inr j : FeedbackLabel n) ∉ feedbackUnseenFinset S := by
      simpa [feedbackUnseenFinset] using hjS
    have hempty : feedbackBulkNextEventSetOfLabel B lam state
        (x0 + (s : ℝ)) (x0 + (t : ℝ)) S (Sum.inr j) =
        (∅ : Set (feedbackUnseenFinset S → MarkedHeight)) := by
      simp [feedbackBulkNextEventSetOfLabel, hnot_unseen]
    rw [hempty]
    simp [S, state, hnotnew]
  · let label : feedbackUnseenFinset S :=
      ⟨Sum.inr j, by simp [feedbackUnseenFinset, hjS]⟩
    have hpoint : sample.targetPoint j = unseen label := by
      have htuple := congrFun
        (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen) label
      rw [hmerge] at htuple
      simp [unseen, feedbackUnseenTuple, feedbackLabelTuple, label]
    have hfixed : feedbackLabelFixedStateCrossing n lam state label (unseen label) =
        state.targetCoordinate sample lam j := by
      change targetFixedStateCrossing n lam state (unseen label) =
        state.targetCoordinate sample lam j
      rw [FeedbackStepState.targetCoordinate, ← hpoint]
      rfl
    have hbridge := historyBranch_feedbackNextEventSet_target_iff
      sample hlam0 hlamHalf hbranch seen unseen rfl label j rfl habs
    rw [hmerge] at hbridge
    have htarget_bulk_set :
        unseen ∈ feedbackBulkNextEventSet B lam state
            (x0 + (s : ℝ)) (x0 + (t : ℝ)) S label ↔
          unseen ∈ feedbackNextEventSet lam state
            (x0 + (s : ℝ)) (x0 + (t : ℝ)) S label ∧
          feedbackBulkRegion n B
            (feedbackLabelFixedStateCrossing n lam state label (unseen label))
            (segmentCurve state.x state.p (state.slope lam)
              (feedbackLabelFixedStateCrossing n lam state label (unseen label))) := by
      unfold feedbackBulkNextEventSet
      simp [hrect]
    have hwrap :
        unseen ∈ feedbackBulkNextEventSetOfLabel B lam state
            (x0 + (s : ℝ)) (x0 + (t : ℝ)) S (Sum.inr j) ↔
          unseen ∈ feedbackBulkNextEventSet B lam
            state (x0 + (s : ℝ)) (x0 + (t : ℝ)) S label := by
      simp [feedbackBulkNextEventSetOfLabel, feedbackUnseenFinset, hjS, label]
    constructor
    · intro h
      obtain ⟨htarget, htime_mem, hbulk⟩ := h
      obtain ⟨hsource_empty, htarget_singleton, hcoord⟩ :=
        target_singleton_data_of_mem sample lam state j hNoTieState htarget
      have hcoord_knot : state.targetCoordinate sample lam j =
          sample.feedbackKnot lam x0 p0 (m.val + 1) := by
        rw [hcoord, hnextKnot]
      have hcoord_time : state.targetCoordinate sample lam j ∈
          Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)) := by
        rw [hcoord_knot]
        exact htime.mp htime_mem
      have hnext : unseen ∈ feedbackNextEventSet lam state
          (x0 + (s : ℝ)) (x0 + (t : ℝ)) S label := by
        apply hbridge.mpr
        exact ⟨hcoord_time, by simpa [hmerge] using hsource_empty,
          by simpa [hmerge] using htarget_singleton⟩
      have hbulk' : feedbackBulkRegion n B
          (feedbackLabelFixedStateCrossing n lam state label (unseen label))
          (segmentCurve state.x state.p (state.slope lam)
            (feedbackLabelFixedStateCrossing n lam state label (unseen label))) := by
        simpa [hfixed, hcoord, hnextKnot, hnextValue] using hbulk
      exact hwrap.mpr (htarget_bulk_set.mpr ⟨hnext, hbulk'⟩)
    · intro h
      have hset := hwrap.mp h
      have hnext_bulk := htarget_bulk_set.mp hset
      have hbridge' := hbridge.mp hnext_bulk.1
      have hsource_empty : state.newSource sample lam = ∅ := by
        simpa [hmerge] using hbridge'.2.1
      have htarget_singleton : state.newTarget sample lam = {j} := by
        simpa [hmerge] using hbridge'.2.2
      have htarget : j ∈ state.newTarget sample lam := by
        rw [htarget_singleton]
        simp
      obtain ⟨_, _, hcoord⟩ := target_singleton_data_of_mem sample lam state j
        hNoTieState htarget
      have hcoord_knot : state.targetCoordinate sample lam j =
          sample.feedbackKnot lam x0 p0 (m.val + 1) := by
        rw [hcoord, hnextKnot]
      have htime_mem : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0
          (m.val + 1) ∈ Ioc s t := by
        apply htime.mpr
        rw [← hcoord_knot]
        exact hbridge'.1
      have hcurve_value : segmentCurve state.x state.p (state.slope lam)
          (state.targetCoordinate sample lam j) =
          feedbackKnotValue sample lam x0 p0 (m.val + 1) := by
        calc
          segmentCurve state.x state.p (state.slope lam)
              (state.targetCoordinate sample lam j) =
              segmentCurve state.x state.p (state.slope lam)
                (state.nextCoordinate sample lam) := by rw [hcoord]
          _ = feedbackKnotValue sample lam x0 p0 (m.val + 1) := hnextValue.symm
      have hbulk : feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1)) := by
        have hbulk' := hnext_bulk.2
        rw [hfixed, hcoord_knot] at hbulk'
        have hvalue :
            segmentCurve state.x state.p (state.slope lam)
                (sample.feedbackKnot lam x0 p0 (m.val + 1)) =
              feedbackKnotValue sample lam x0 p0 (m.val + 1) := by
          rw [← hcoord_knot, hcurve_value]
        rw [hvalue] at hbulk'
        exact hbulk'
      exact ⟨htarget, htime_mem, hbulk⟩

/-! ## Branch sums for one recursive step -/

set_option linter.unusedVariables false in
theorem finiteEventBulk_newSource_card_eq_historyCellIndex_sum
    (sample : FiniteSample n) {lam B x0 p0 : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hgood : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n))
    {s t : ℝ≥0} (hst : s ≤ t) :
    (Finset.univ.filter (fun i : Fin n ↦
      i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
        sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
        feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card =
      ∑ index : HistoryCellIndex n, if
        index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history then
        (Finset.univ.filter (fun i : Fin n ↦
          i ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
            index.history).newSource sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card
      else 0 := by
  classical
  let K : Prop :=
    sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
      feedbackBulkRegion n B
        (sample.feedbackKnot lam x0 p0 (m.val + 1))
        (feedbackKnotValue sample lam x0 p0 (m.val + 1))
  have hleft :
      (Finset.univ.filter (fun i : Fin n ↦
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧ K)).card =
        if K then ((feedbackState sample lam x0 p0 m.val).newSource sample lam).card else 0 := by
    by_cases hK : K <;> simp [hK]
  change (Finset.univ.filter (fun i : Fin n ↦
      i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧ K)).card = _
  rw [hleft, feedbackState_newSource_card_eq_sum_historyCellIndex_branch
    sample lam x0 p0 hgood m]
  by_cases hK : K
  · have hK' : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
        feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1)) := by
      simpa [K] using hK
    simp only [ite_eq_left hK]
    apply Fintype.sum_congr
    intro index
    by_cases hindex : index.history.length = m.val ∧
        HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
    · simp [hindex, hK']
    · simp [hindex]
  · have hK' : ¬ (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
        feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1))) := by
      simpa [K] using hK
    simp only [ite_eq_right hK]
    symm
    apply Fintype.sum_eq_zero
    intro index
    by_cases hindex : index.history.length = m.val ∧
        HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
    · rw [ite_eq_left hindex]
      apply Finset.card_eq_zero.mpr
      ext i
      constructor
      · intro hi
        exact (hK' (Finset.mem_filter.mp hi).2.2).elim
      · intro hi
        simp at hi
    · simp [hindex]

set_option linter.unusedVariables false in
theorem finiteEventBulk_newTarget_card_eq_historyCellIndex_sum
    (sample : FiniteSample n) {lam B x0 p0 : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hgood : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n))
    {s t : ℝ≥0} (hst : s ≤ t) :
    (Finset.univ.filter (fun j : Fin n ↦
      j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
        sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
        feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card =
      ∑ index : HistoryCellIndex n, if
        index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history then
        (Finset.univ.filter (fun j : Fin n ↦
          j ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
            index.history).newTarget sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card
      else 0 := by
  classical
  let K : Prop :=
    sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
      feedbackBulkRegion n B
        (sample.feedbackKnot lam x0 p0 (m.val + 1))
        (feedbackKnotValue sample lam x0 p0 (m.val + 1))
  have hleft :
      (Finset.univ.filter (fun j : Fin n ↦
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧ K)).card =
        if K then ((feedbackState sample lam x0 p0 m.val).newTarget sample lam).card else 0 := by
    by_cases hK : K <;> simp [hK]
  change (Finset.univ.filter (fun j : Fin n ↦
      j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧ K)).card = _
  rw [hleft, feedbackState_newTarget_card_eq_sum_historyCellIndex_branch
    sample lam x0 p0 hgood m]
  by_cases hK : K
  · have hK' : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
        feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1)) := by
      simpa [K] using hK
    simp only [ite_eq_left hK]
    apply Fintype.sum_congr
    intro index
    by_cases hindex : index.history.length = m.val ∧
        HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
    · simp [hindex, hK']
    · simp [hindex]
  · have hK' : ¬ (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
        feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1))) := by
      simpa [K] using hK
    simp only [ite_eq_right hK]
    symm
    apply Fintype.sum_eq_zero
    intro index
    by_cases hindex : index.history.length = m.val ∧
        HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
    · rw [ite_eq_left hindex]
      apply Finset.card_eq_zero.mpr
      ext j
      constructor
      · intro hj
        exact (hK' (Finset.mem_filter.mp hj).2.2).elim
      · intro hj
        simp at hj
    · simp [hindex]

/-! ## The same branch sums with the next-label indicators exposed -/

theorem finiteEventBulk_newSource_card_eq_historyCellIndex_nextLabel_sum
    (sample : FiniteSample n) {lam B x0 p0 : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hgood : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n))
    {s t : ℝ≥0} (hst : s ≤ t) :
    (Finset.univ.filter (fun i : Fin n ↦
      i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
        sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
        feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card =
      ∑ index : HistoryCellIndex n, if
        index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history then
        ∑ i : Fin n, if
          feedbackUnseenTuple
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
              (Sum.inl i) then 1 else 0
      else 0 := by
  classical
  rw [finiteEventBulk_newSource_card_eq_historyCellIndex_sum
    sample hlam0 hlamHalf hgood m hst]
  apply Fintype.sum_congr
  intro index
  by_cases hindex : index.history.length = m.val ∧
      HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
  · have hsum :
        (Finset.univ.filter (fun i : Fin n ↦
          i ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
            index.history).newSource sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card =
          ∑ i : Fin n, if
            feedbackUnseenTuple
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) sample ∈
              feedbackBulkNextEventSetOfLabel B lam
                (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
                (x0 + (s : ℝ)) (x0 + (t : ℝ))
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
                (Sum.inl i) then 1 else 0 := by
      calc
        _ = ∑ i : Fin n, if
            i ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
              index.history).newSource sample lam ∧
              sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
              feedbackBulkRegion n B
                (sample.feedbackKnot lam x0 p0 (m.val + 1))
                (feedbackKnotValue sample lam x0 p0 (m.val + 1))
            then 1 else 0 := by
          symm
          exact (Finset.sum_boole (R := ℕ)
            (fun i : Fin n ↦
              i ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                index.history).newSource sample lam ∧
                sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
                feedbackBulkRegion n B
                  (sample.feedbackKnot lam x0 p0 (m.val + 1))
                  (feedbackKnotValue sample lam x0 p0 (m.val + 1)))
            (Finset.univ : Finset (Fin n)))
        _ = ∑ i : Fin n, if
            feedbackUnseenTuple
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) sample ∈
              feedbackBulkNextEventSetOfLabel B lam
                (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
                (x0 + (s : ℝ)) (x0 + (t : ℝ))
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
                (Sum.inl i) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiff := historyBranch_source_bulk_indicator_iff
            (B := B) sample hlam0 hlamHalf hgood m index hindex i hst
          by_cases h :
              i ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                index.history).newSource sample lam ∧
              sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
              feedbackBulkRegion n B
                (sample.feedbackKnot lam x0 p0 (m.val + 1))
                (feedbackKnotValue sample lam x0 p0 (m.val + 1))
          · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
          · rw [ite_eq_right h, ite_eq_right (fun hm ↦ h (hiff.mpr hm))]
    simp only [ite_eq_left hindex]
    exact hsum
  · simp only [ite_eq_right hindex]

theorem finiteEventBulk_newTarget_card_eq_historyCellIndex_nextLabel_sum
    (sample : FiniteSample n) {lam B x0 p0 : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hgood : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n))
    {s t : ℝ≥0} (hst : s ≤ t) :
    (Finset.univ.filter (fun j : Fin n ↦
      j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
        sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
        feedbackBulkRegion n B
          (sample.feedbackKnot lam x0 p0 (m.val + 1))
          (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card =
      ∑ index : HistoryCellIndex n, if
        index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history then
        ∑ j : Fin n, if
          feedbackUnseenTuple
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
              (Sum.inr j) then 1 else 0
      else 0 := by
  classical
  rw [finiteEventBulk_newTarget_card_eq_historyCellIndex_sum
    sample hlam0 hlamHalf hgood m hst]
  apply Fintype.sum_congr
  intro index
  by_cases hindex : index.history.length = m.val ∧
      HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
  · have hsum :
        (Finset.univ.filter (fun j : Fin n ↦
          j ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
            index.history).newTarget sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card =
          ∑ j : Fin n, if
            feedbackUnseenTuple
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) sample ∈
              feedbackBulkNextEventSetOfLabel B lam
                (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
                (x0 + (s : ℝ)) (x0 + (t : ℝ))
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
                (Sum.inr j) then 1 else 0 := by
      calc
        _ = ∑ j : Fin n, if
            j ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
              index.history).newTarget sample lam ∧
              sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
              feedbackBulkRegion n B
                (sample.feedbackKnot lam x0 p0 (m.val + 1))
                (feedbackKnotValue sample lam x0 p0 (m.val + 1))
            then 1 else 0 := by
          symm
          exact (Finset.sum_boole (R := ℕ)
            (fun j : Fin n ↦
              j ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                index.history).newTarget sample lam ∧
                sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
                feedbackBulkRegion n B
                  (sample.feedbackKnot lam x0 p0 (m.val + 1))
                  (feedbackKnotValue sample lam x0 p0 (m.val + 1)))
            (Finset.univ : Finset (Fin n)))
        _ = ∑ j : Fin n, if
            feedbackUnseenTuple
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) sample ∈
              feedbackBulkNextEventSetOfLabel B lam
                (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
                (x0 + (s : ℝ)) (x0 + (t : ℝ))
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
                (Sum.inr j) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hiff := historyBranch_target_bulk_indicator_iff
            (B := B) sample hlam0 hlamHalf hgood m index hindex j hst
          by_cases h :
              j ∈ (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                index.history).newTarget sample lam ∧
              sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
              feedbackBulkRegion n B
                (sample.feedbackKnot lam x0 p0 (m.val + 1))
                (feedbackKnotValue sample lam x0 p0 (m.val + 1))
          · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
          · rw [ite_eq_right h, ite_eq_right (fun hm ↦ h (hiff.mpr hm))]
    simp only [ite_eq_left hindex]
    exact hsum
  · simp only [ite_eq_right hindex]

end OTSelector
