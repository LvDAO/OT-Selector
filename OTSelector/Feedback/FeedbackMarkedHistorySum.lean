import OTSelector.Feedback.FeedbackMarkedEventProcess
import OTSelector.Feedback.FeedbackMarkedRawRectangle

/-!
# Mark sums and the actual finite history partition

The predictable current at a genuine next crossing equals the current of the preceding
recursive state. This identifies the centering in the geometric next-event law with the
predictable centering evaluated at the actual labelled event time.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal Topology

namespace OTSelector.FiniteSample

open CountingProcess

variable {n : ℕ} {lam : ℝ}

theorem countBefore_safeSourceCount_at_nextKnot
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n))
    (hactive : ((sample.feedbackState lam x0 p0 m.val).candidates sample lam).Nonempty) :
    countBefore (safeSourceCount hlam0 hlamHalf x0 p0)
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1)) sample =
      safeSourceCount hlam0 hlamHalf x0 p0
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 m.val) sample := by
  have hstrict : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 m.val <
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) := by
    apply NNReal.coe_lt_coe.mp
    simpa only [coe_elapsedFeedbackKnot, feedbackKnot] using
      sub_lt_sub_right (sample.feedbackState_x_strictMono_step
        hlam0 hlamHalf x0 p0 m.val hactive) x0
  unfold safeSourceCount
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  unfold finiteEventCountTop
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    obtain ⟨_, k, hk, _⟩ := (sample.sourceEventTime_le_iff_exists
      hlam0 hlamHalf x0 p0 i _).mp hi.le
    have heq := sample.sourceEventTime_eq_elapsedFeedbackKnot_of_newSource
      hlam0 hlamHalf x0 p0 hgood i hk
    have hkm : k.val < m.val := by
      by_contra hn
      have hmono := sample.elapsedFeedbackKnot_mono hlam0 hlamHalf x0 p0
        (show m.val + 1 ≤ k.val + 1 by omega)
      rw [heq] at hi
      exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hmono)) hi
    rw [heq]
    exact WithTop.coe_le_coe.mpr (sample.elapsedFeedbackKnot_mono
      hlam0 hlamHalf x0 p0 (by omega))
  · intro hi
    exact hi.trans_lt (WithTop.coe_lt_coe.mpr hstrict)

theorem countBefore_safeTargetCount_at_nextKnot
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n))
    (hactive : ((sample.feedbackState lam x0 p0 m.val).candidates sample lam).Nonempty) :
    countBefore (safeTargetCount hlam0 hlamHalf x0 p0)
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1)) sample =
      safeTargetCount hlam0 hlamHalf x0 p0
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 m.val) sample := by
  have hstrict : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 m.val <
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) := by
    apply NNReal.coe_lt_coe.mp
    simpa only [coe_elapsedFeedbackKnot, feedbackKnot] using
      sub_lt_sub_right (sample.feedbackState_x_strictMono_step
        hlam0 hlamHalf x0 p0 m.val hactive) x0
  unfold safeTargetCount
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  unfold finiteEventCountTop
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    obtain ⟨_, k, hk, _⟩ := (sample.targetEventTime_le_iff_exists
      hlam0 hlamHalf x0 p0 i _).mp hi.le
    have heq := sample.targetEventTime_eq_elapsedFeedbackKnot_of_newTarget
      hlam0 hlamHalf x0 p0 hgood i hk
    have hkm : k.val < m.val := by
      by_contra hn
      have hmono := sample.elapsedFeedbackKnot_mono hlam0 hlamHalf x0 p0
        (show m.val + 1 ≤ k.val + 1 by omega)
      rw [heq] at hi
      exact (not_lt_of_ge (WithTop.coe_le_coe.mpr hmono)) hi
    rw [heq]
    exact WithTop.coe_le_coe.mpr (sample.elapsedFeedbackKnot_mono
      hlam0 hlamHalf x0 p0 (by omega))
  · intro hi
    exact hi.trans_lt (WithTop.coe_lt_coe.mpr hstrict)

/-- At an actual next knot the predictable current is exactly the preceding recursive current. -/
theorem safePreCurrentAt_at_nextKnot
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n))
    (hactive : ((sample.feedbackState lam x0 p0 m.val).candidates sample lam).Nonempty) :
    safePreCurrentAt hlam0 hlamHalf x0 p0
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1)) sample =
      (sample.feedbackState lam x0 p0 m.val).current := by
  unfold safePreCurrentAt leftCurrentOfCounts
  rw [countBefore_safeSourceCount_at_nextKnot sample hlam0 hlamHalf x0 p0 hgood m hactive,
    countBefore_safeTargetCount_at_nextKnot sample hlam0 hlamHalf x0 p0 hgood m hactive,
    ← safeCurrentAt_eq_K0_add_counts]
  simp only [safeCurrentAt, ite_eq_left hgood]
  rw [sample.feedbackStateAtElapsed_at_elapsedFeedbackKnot hlam0 hlamHalf x0 p0
    (Nat.le_of_lt m.isLt)]

theorem safePreFeedbackSlope_at_nextKnot
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n))
    (hactive : ((sample.feedbackState lam x0 p0 m.val).candidates sample lam).Nonempty) :
    safePreFeedbackSlope hlam0 hlamHalf x0 p0
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1)) sample =
      (sample.feedbackState lam x0 p0 m.val).slope lam := by
  unfold safePreFeedbackSlope FeedbackStepState.slope
  rw [safePreCurrentAt_at_nextKnot sample hlam0 hlamHalf x0 p0 hgood m hactive]

/-- A single retained source label is identified in the genuine finite history partition. -/
theorem thinnedSourceEventTime_indicator_eq_sum_history
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0) (i : Fin n)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (if thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history then
          if feedbackUnseenTuple (feedbackTerminalLabelSet index.sourcePattern
              index.targetPattern index.history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
              (Sum.inl i) then 1 else 0
        else 0 := by
  classical
  rw [sample.thinnedSourceEventTime_indicator_eq_sum_newSource_bulk
    hlam0 hlamHalf B x0 p0 hgood i hst]
  apply Finset.sum_congr rfl
  intro m _
  let P := i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
    sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
    feedbackBulkRegion n B (sample.feedbackKnot lam x0 p0 (m.val + 1))
      (feedbackKnotValue sample lam x0 p0 (m.val + 1))
  have hiff (index : HistoryCellIndex n)
      (hi : index.history.length = m.val ∧ HistoryBranch sample lam x0 p0
        index.sourcePattern index.targetPattern index.history) :
      P ↔ feedbackUnseenTuple (feedbackTerminalLabelSet index.sourcePattern
          index.targetPattern index.history) sample ∈
        feedbackBulkNextEventSetOfLabel B lam
          (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
          (x0 + (s : ℝ)) (x0 + (t : ℝ))
          (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
          (Sum.inl i) := by
    have hstate := sample.feedbackState_eq_scheduledState_of_history
      lam x0 p0 index.sourcePattern index.targetPattern index.history hi.2.1 hi.2.2
    rw [hi.1] at hstate
    simpa only [P, hstate] using historyBranch_source_bulk_indicator_iff
      (B := B) sample hlam0 hlamHalf hgood m index hi i hst
  by_cases hp : P
  · obtain ⟨history, hlen, hbranch, _⟩ :=
      sample.exists_historyBranch_of_noFeedbackTies_of_active lam x0 p0 m.isLt hgood
        (sample.candidates_nonempty_of_mem_newSource lam _ i hp.1)
    let idx : HistoryCellIndex n :=
      ⟨sample.initialSeenSource x0 p0, sample.initialSeenTarget x0 p0, history, by omega⟩
    have hidx : idx.history.length = m.val ∧ HistoryBranch sample lam x0 p0
        idx.sourcePattern idx.targetPattern idx.history := ⟨hlen, hbranch⟩
    rw [Fintype.sum_eq_single idx]
    · rw [ite_eq_left hp, ite_eq_left hidx, ite_eq_left ((hiff idx hidx).mp hp)]
    · intro other hne
      have hnot : ¬(other.history.length = m.val ∧ HistoryBranch sample lam x0 p0
          other.sourcePattern other.targetPattern other.history) := by
        intro ho
        exact hne (historyCellIndex_eq_of_noFeedbackTies_of_realized_step
          sample lam x0 p0 hgood m other idx ho hidx)
      exact ite_eq_right hnot
  · rw [ite_eq_right hp]
    symm
    apply Finset.sum_eq_zero
    intro index _
    split_ifs with hi he
    · exact (hp ((hiff index hi).mpr he)).elim
    · rfl
    · rfl

/-- A single retained target label is identified in the genuine finite history partition. -/
theorem thinnedTargetEventTime_indicator_eq_sum_history
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0) (i : Fin n)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (if thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (targetEventTime hlam0 hlamHalf x0 p0 i) sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history then
          if feedbackUnseenTuple (feedbackTerminalLabelSet index.sourcePattern
              index.targetPattern index.history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
              (Sum.inr i) then 1 else 0
        else 0 := by
  classical
  rw [sample.thinnedTargetEventTime_indicator_eq_sum_newTarget_bulk
    hlam0 hlamHalf B x0 p0 hgood i hst]
  apply Finset.sum_congr rfl
  intro m _
  let P := i ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
    sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
    feedbackBulkRegion n B (sample.feedbackKnot lam x0 p0 (m.val + 1))
      (feedbackKnotValue sample lam x0 p0 (m.val + 1))
  have hiff (index : HistoryCellIndex n)
      (hi : index.history.length = m.val ∧ HistoryBranch sample lam x0 p0
        index.sourcePattern index.targetPattern index.history) :
      P ↔ feedbackUnseenTuple (feedbackTerminalLabelSet index.sourcePattern
          index.targetPattern index.history) sample ∈
        feedbackBulkNextEventSetOfLabel B lam
          (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
          (x0 + (s : ℝ)) (x0 + (t : ℝ))
          (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
          (Sum.inr i) := by
    have hstate := sample.feedbackState_eq_scheduledState_of_history
      lam x0 p0 index.sourcePattern index.targetPattern index.history hi.2.1 hi.2.2
    rw [hi.1] at hstate
    simpa only [P, hstate] using historyBranch_target_bulk_indicator_iff
      (B := B) sample hlam0 hlamHalf hgood m index hi i hst
  by_cases hp : P
  · obtain ⟨history, hlen, hbranch, _⟩ :=
      sample.exists_historyBranch_of_noFeedbackTies_of_active lam x0 p0 m.isLt hgood
        (sample.candidates_nonempty_of_mem_newTarget lam _ i hp.1)
    let idx : HistoryCellIndex n :=
      ⟨sample.initialSeenSource x0 p0, sample.initialSeenTarget x0 p0, history, by omega⟩
    have hidx : idx.history.length = m.val ∧ HistoryBranch sample lam x0 p0
        idx.sourcePattern idx.targetPattern idx.history := ⟨hlen, hbranch⟩
    rw [Fintype.sum_eq_single idx]
    · rw [ite_eq_left hp, ite_eq_left hidx, ite_eq_left ((hiff idx hidx).mp hp)]
    · intro other hne
      have hnot : ¬(other.history.length = m.val ∧ HistoryBranch sample lam x0 p0
          other.sourcePattern other.targetPattern other.history) := by
        intro ho
        exact hne (historyCellIndex_eq_of_noFeedbackTies_of_realized_step
          sample lam x0 p0 hgood m other idx ho hidx)
      exact ite_eq_right hnot
  · rw [ite_eq_right hp]
    symm
    apply Finset.sum_eq_zero
    intro index _
    split_ifs with hi he
    · exact (hp ((hiff index hi).mpr he)).elim
    · rfl
    · rfl

/-- The centering at a retained source event is the centering in its actual history law. -/
theorem safePreFeedbackSlope_at_sourceBulkEvent_of_history
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    (m : Fin (2 * n)) (index : HistoryCellIndex n)
    (hindex : index.history.length = m.val ∧ HistoryBranch sample lam x0 p0
      index.sourcePattern index.targetPattern index.history)
    (i : Fin n) {s t : ℝ≥0} (hst : s ≤ t)
    (he : feedbackUnseenTuple (feedbackTerminalLabelSet index.sourcePattern
        index.targetPattern index.history) sample ∈ feedbackBulkNextEventSetOfLabel B lam
      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
      (x0 + (s : ℝ)) (x0 + (t : ℝ))
      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) (Sum.inl i)) :
    safePreFeedbackSlope hlam0 hlamHalf x0 p0
      (finiteEventTimeValue (fun j : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 j)
        sample i) sample =
      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history).slope lam := by
  have hd := (historyBranch_source_bulk_indicator_iff
    (B := B) sample hlam0 hlamHalf hgood m index hindex i hst).mpr he
  have hstate := sample.feedbackState_eq_scheduledState_of_history
    lam x0 p0 index.sourcePattern index.targetPattern index.history hindex.2.1 hindex.2.2
  rw [hindex.1] at hstate
  have hnew : i ∈ (sample.feedbackState lam x0 p0 m.val).newSource sample lam := by
    rw [hstate]
    exact hd.1
  have hacc := (sample.eventAccepted_safeFeedbackBulkMask_source_of_newSource
    hlam0 hlamHalf B x0 p0 hgood i hnew).mpr hd.2.2
  have htime : safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample =
      (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) : WithTop ℝ≥0) := by
    rw [safeSourceBulkEventTime, thinnedEventTime_of_accepted hacc]
    exact sample.sourceEventTime_eq_elapsedFeedbackKnot_of_newSource
      hlam0 hlamHalf x0 p0 hgood i hnew
  have hvalue : finiteEventTimeValue
      (fun j : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 j) sample i =
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) := by
    apply WithTop.coe_injective
    rw [finiteEventTimeValue_coe _ _ _ (by rw [htime]; exact WithTop.coe_ne_top), htime]
  rw [hvalue, safePreFeedbackSlope_at_nextKnot sample hlam0 hlamHalf x0 p0 hgood m
    (sample.candidates_nonempty_of_mem_newSource lam _ i hnew), hstate]

/-- The centering at a retained target event is the centering in its actual history law. -/
theorem safePreFeedbackSlope_at_targetBulkEvent_of_history
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    (m : Fin (2 * n)) (index : HistoryCellIndex n)
    (hindex : index.history.length = m.val ∧ HistoryBranch sample lam x0 p0
      index.sourcePattern index.targetPattern index.history)
    (i : Fin n) {s t : ℝ≥0} (hst : s ≤ t)
    (he : feedbackUnseenTuple (feedbackTerminalLabelSet index.sourcePattern
        index.targetPattern index.history) sample ∈ feedbackBulkNextEventSetOfLabel B lam
      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
      (x0 + (s : ℝ)) (x0 + (t : ℝ))
      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) (Sum.inr i)) :
    safePreFeedbackSlope hlam0 hlamHalf x0 p0
      (finiteEventTimeValue (fun j : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j)
        sample i) sample =
      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history).slope lam := by
  have hd := (historyBranch_target_bulk_indicator_iff
    (B := B) sample hlam0 hlamHalf hgood m index hindex i hst).mpr he
  have hstate := sample.feedbackState_eq_scheduledState_of_history
    lam x0 p0 index.sourcePattern index.targetPattern index.history hindex.2.1 hindex.2.2
  rw [hindex.1] at hstate
  have hnew : i ∈ (sample.feedbackState lam x0 p0 m.val).newTarget sample lam := by
    rw [hstate]
    exact hd.1
  have hacc := (sample.eventAccepted_safeFeedbackBulkMask_target_of_newTarget
    hlam0 hlamHalf B x0 p0 hgood i hnew).mpr hd.2.2
  have htime : safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i sample =
      (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) : WithTop ℝ≥0) := by
    rw [safeTargetBulkEventTime, thinnedEventTime_of_accepted hacc]
    exact sample.targetEventTime_eq_elapsedFeedbackKnot_of_newTarget
      hlam0 hlamHalf x0 p0 hgood i hnew
  have hvalue : finiteEventTimeValue
      (fun j : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j) sample i =
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) := by
    apply WithTop.coe_injective
    rw [finiteEventTimeValue_coe _ _ _ (by rw [htime]; exact WithTop.coe_ne_top), htime]
  rw [hvalue, safePreFeedbackSlope_at_nextKnot sample hlam0 hlamHalf x0 p0 hgood m
    (sample.candidates_nonempty_of_mem_newTarget lam _ i hnew), hstate]

/-- The true source mark minus its predictable conditional mean at the retained crossing. -/
noncomputable def safeSourceBulkCenteredMarkWeight
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (i : Fin n) (sample : FiniteSample n) : ℝ :=
  ψ (sample.sourceMark i) - sourceFeedbackMarkMean
    (safePreFeedbackSlope hlam0 hlamHalf x0 p0
      (finiteEventTimeValue (fun j : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 j)
        sample i) sample) ψ

/-- The actual centered source mark innovation. -/
noncomputable def safeSourceBulkCenteredMarkSum
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) : ℝ≥0 → FiniteSample n → ℝ :=
  finiteEventWeightedSum (fun i ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i)
    (safeSourceBulkCenteredMarkWeight hlam0 hlamHalf B x0 p0 ψ)

/-- Its increment is the finite sum of the actual centered next-event history contributions. -/
theorem safeSourceBulkCenteredMarkSum_sub_eq_history
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
      safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ s sample =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∑ i : Fin n, feedbackCenteredHistoryTerm B lam x0 p0
            (x0 + (s : ℝ)) (x0 + (t : ℝ)) index.sourcePattern index.targetPattern
            index.history (Sum.inl i) ψ sample else 0 := by
  classical
  rw [safeSourceBulkCenteredMarkSum, finiteEventWeightedSum_sub _ _ hst]
  let w := safeSourceBulkCenteredMarkWeight (n := n) hlam0 hlamHalf B x0 p0 ψ
  have hpoint (i : Fin n) := sample.thinnedSourceEventTime_indicator_eq_sum_history
    hlam0 hlamHalf B x0 p0 hgood i hst
  change (∑ i : Fin n, if safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample ∈
      Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then w i sample else 0) = _
  conv_lhs =>
    arg 2
    intro i
    rw [show (if safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then w i sample else 0) =
        w i sample * (if safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) by
      split_ifs <;> simp]
    rw [safeSourceBulkEventTime, hpoint i]
    simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hlen : index.history.length = m.val
  · rw [ite_eq_left hlen]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hbranch : HistoryBranch sample lam x0 p0
        index.sourcePattern index.targetPattern index.history
    · have hidx := And.intro hlen hbranch
      rw [ite_eq_left hidx]
      unfold feedbackCenteredHistoryTerm
      dsimp only
      by_cases he : feedbackUnseenTuple (feedbackTerminalLabelSet index.sourcePattern
          index.targetPattern index.history) sample ∈ feedbackBulkNextEventSetOfLabel B lam
        (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
        (x0 + (s : ℝ)) (x0 + (t : ℝ))
        (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) (Sum.inl i)
      · rw [ite_eq_left he, ite_eq_left ⟨hbranch, he⟩, mul_one]
        dsimp only [w, safeSourceBulkCenteredMarkWeight]
        rw [safePreFeedbackSlope_at_sourceBulkEvent_of_history
          sample hlam0 hlamHalf B x0 p0 hgood m index hidx i hst he]
        rfl
      · rw [ite_eq_right he, ite_eq_right (fun h ↦ he h.2), mul_zero]
    · simp only [feedbackCenteredHistoryTerm, hbranch, and_false, false_and,
        ite_false, mul_zero]
  · rw [ite_eq_right hlen]
    apply Finset.sum_eq_zero
    intro i _
    simp only [hlen, false_and, ite_false, mul_zero]

/-- The true target mark minus its predictable conditional mean at the retained crossing. -/
noncomputable def safeTargetBulkCenteredMarkWeight
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (i : Fin n) (sample : FiniteSample n) : ℝ :=
  ψ (sample.targetMark i) - targetFeedbackMarkMean
    (safePreFeedbackSlope hlam0 hlamHalf x0 p0
      (finiteEventTimeValue (fun j : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j)
        sample i) sample) ψ

/-- The actual centered target mark innovation. -/
noncomputable def safeTargetBulkCenteredMarkSum
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) : ℝ≥0 → FiniteSample n → ℝ :=
  finiteEventWeightedSum (fun i ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i)
    (safeTargetBulkCenteredMarkWeight hlam0 hlamHalf B x0 p0 ψ)

/-- Its increment is the finite sum of the actual centered next-event history contributions. -/
theorem safeTargetBulkCenteredMarkSum_sub_eq_history
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
      safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ s sample =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∑ i : Fin n, feedbackCenteredHistoryTerm B lam x0 p0
            (x0 + (s : ℝ)) (x0 + (t : ℝ)) index.sourcePattern index.targetPattern
            index.history (Sum.inr i) ψ sample else 0 := by
  classical
  rw [safeTargetBulkCenteredMarkSum, finiteEventWeightedSum_sub _ _ hst]
  let w := safeTargetBulkCenteredMarkWeight (n := n) hlam0 hlamHalf B x0 p0 ψ
  have hpoint (i : Fin n) := sample.thinnedTargetEventTime_indicator_eq_sum_history
    hlam0 hlamHalf B x0 p0 hgood i hst
  change (∑ i : Fin n, if safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i sample ∈
      Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then w i sample else 0) = _
  conv_lhs =>
    arg 2
    intro i
    rw [show (if safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then w i sample else 0) =
        w i sample * (if safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) by
      split_ifs <;> simp]
    rw [safeTargetBulkEventTime, hpoint i]
    simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  by_cases hlen : index.history.length = m.val
  · rw [ite_eq_left hlen]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hbranch : HistoryBranch sample lam x0 p0
        index.sourcePattern index.targetPattern index.history
    · have hidx := And.intro hlen hbranch
      rw [ite_eq_left hidx]
      unfold feedbackCenteredHistoryTerm
      dsimp only
      by_cases he : feedbackUnseenTuple (feedbackTerminalLabelSet index.sourcePattern
          index.targetPattern index.history) sample ∈ feedbackBulkNextEventSetOfLabel B lam
        (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history)
        (x0 + (s : ℝ)) (x0 + (t : ℝ))
        (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history) (Sum.inr i)
      · rw [ite_eq_left he, ite_eq_left ⟨hbranch, he⟩, mul_one]
        dsimp only [w, safeTargetBulkCenteredMarkWeight]
        rw [safePreFeedbackSlope_at_targetBulkEvent_of_history
          sample hlam0 hlamHalf B x0 p0 hgood m index hidx i hst he]
        rfl
      · rw [ite_eq_right he, ite_eq_right (fun h ↦ he h.2), mul_zero]
    · simp only [feedbackCenteredHistoryTerm, hbranch, and_false, false_and,
        ite_false, mul_zero]
  · rw [ite_eq_right hlen]
    apply Finset.sum_eq_zero
    intro i _
    simp only [hlen, false_and, ite_false, mul_zero]

end OTSelector.FiniteSample
