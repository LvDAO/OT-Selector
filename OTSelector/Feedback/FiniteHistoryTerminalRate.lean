import OTSelector.Feedback.FeedbackBulkMask
import OTSelector.Feedback.FiniteHistoryBeforePartition
import OTSelector.Feedback.ForcedHistoryLength

/-!
# Vanishing rates after a full finite feedback history

A realized feedback history has no repeated labels.  Hence a realized history of length
`2 * n` contains every source and target label.  This file turns that finite coverage fact
into vanishing terminal unseen counts, fixed-state rates, and safe bulk rates.

No probability or measurability argument is used here.
-/

open Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

namespace FiniteSample

/-- A realized history of maximal possible length contains every feedback label. -/
theorem ForcedHistoryRealizes.mem_of_length_eq_two_mul
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (history : List (FeedbackLabel n))
    (hreal : sample.ForcedHistoryRealizes lam state history)
    (hlength : history.length = 2 * n) (label : FeedbackLabel n) :
    label ∈ history := by
  classical
  have hnodup : history.Nodup := hreal.nodup
  have hcard : history.toFinset.card = Fintype.card (FeedbackLabel n) := by
    rw [List.toFinset_card_of_nodup hnodup, hlength]
    simp [FeedbackLabel, two_mul]
  have hall : history.toFinset = Finset.univ :=
    Finset.eq_univ_of_card history.toFinset hcard
  have hmem : label ∈ history.toFinset := by
    rw [hall]
    simp
  simpa using hmem

end FiniteSample

/-! ## Full terminal seen sets -/

/-- A maximal realized history leaves no unseen source label in its scheduled state. -/
theorem HistoryBranch.scheduledState_seenSource_eq_univ
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (hlength : history.length = 2 * n) :
    (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource =
      Finset.univ := by
  classical
  ext i
  simp only [Finset.mem_univ, iff_true]
  exact FiniteSample.scheduledState_mem_seenSource_of_mem_history
    sample lam x0 p0 sourcePattern targetPattern history i
      (FiniteSample.ForcedHistoryRealizes.mem_of_length_eq_two_mul
        sample lam _ history hbranch.2 hlength (Sum.inl i))

/-- A maximal realized history leaves no unseen target label in its scheduled state. -/
theorem HistoryBranch.scheduledState_seenTarget_eq_univ
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (hlength : history.length = 2 * n) :
    (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget =
      Finset.univ := by
  classical
  ext j
  simp only [Finset.mem_univ, iff_true]
  exact FiniteSample.scheduledState_mem_seenTarget_of_mem_history
    sample lam x0 p0 sourcePattern targetPattern history j
      (FiniteSample.ForcedHistoryRealizes.mem_of_length_eq_two_mul
        sample lam _ history hbranch.2 hlength (Sum.inr j))

theorem HistoryBranch.scheduledState_sourceUnseenCard_eq_zero
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (hlength : history.length = 2 * n) :
    (Finset.univ \
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource).card =
        0 := by
  rw [HistoryBranch.scheduledState_seenSource_eq_univ sample hbranch hlength]
  simp

theorem HistoryBranch.scheduledState_targetUnseenCard_eq_zero
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (hlength : history.length = 2 * n) :
    (Finset.univ \
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget).card =
        0 := by
  rw [HistoryBranch.scheduledState_seenTarget_eq_univ sample hbranch hlength]
  simp

theorem HistoryBranch.scheduledState_sourceCardSub_eq_zero
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (hlength : history.length = 2 * n) :
    n - (sample.scheduledState lam x0 p0
      sourcePattern targetPattern history).seenSource.card = 0 := by
  rw [HistoryBranch.scheduledState_seenSource_eq_univ sample hbranch hlength]
  simp

theorem HistoryBranch.scheduledState_targetCardSub_eq_zero
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (hlength : history.length = 2 * n) :
    n - (sample.scheduledState lam x0 p0
      sourcePattern targetPattern history).seenTarget.card = 0 := by
  rw [HistoryBranch.scheduledState_seenTarget_eq_univ sample hbranch hlength]
  simp

/-! ## Vanishing state and safe bulk rates -/

namespace FeedbackStepState

theorem sourceUnclippedStateRateAt_eq_zero_of_seenSource_eq_univ
    (state : FeedbackStepState n) (lam x : ℝ)
    (hseen : state.seenSource = Finset.univ) :
    state.sourceUnclippedStateRateAt lam x = 0 := by
  simp [sourceUnclippedStateRateAt, hseen]

theorem targetUnclippedStateRateAt_eq_zero_of_seenTarget_eq_univ
    (state : FeedbackStepState n) (lam x : ℝ)
    (hseen : state.seenTarget = Finset.univ) :
    state.targetUnclippedStateRateAt lam x = 0 := by
  simp [targetUnclippedStateRateAt, hseen]

end FeedbackStepState

theorem HistoryBranch.sourceUnclippedStateRateAt_eq_zero_of_full_length
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (hlength : history.length = 2 * n) :
    FeedbackStepState.sourceUnclippedStateRateAt lam
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x = 0 := by
  exact FeedbackStepState.sourceUnclippedStateRateAt_eq_zero_of_seenSource_eq_univ
    _ lam x (HistoryBranch.scheduledState_seenSource_eq_univ sample hbranch hlength)

theorem HistoryBranch.targetUnclippedStateRateAt_eq_zero_of_full_length
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (hlength : history.length = 2 * n) :
    FeedbackStepState.targetUnclippedStateRateAt lam
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x = 0 := by
  exact FeedbackStepState.targetUnclippedStateRateAt_eq_zero_of_seenTarget_eq_univ
    _ lam x (HistoryBranch.scheduledState_seenTarget_eq_univ sample hbranch hlength)

private theorem initialSeenSource_eq_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x) :
    sample.initialSeenSource x0 p0 = sourcePattern := by
  have h := congrArg FeedbackStepState.seenSource hbefore.1.1.1
  simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h

private theorem initialSeenTarget_eq_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x) :
    sample.initialSeenTarget x0 p0 = targetPattern := by
  have h := congrArg FeedbackStepState.seenTarget hbefore.1.1.1
  simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h

/-- At the elapsed time represented by a full strict history, the safe source bulk rate is zero.
This needs no bulk-region or positivity assumption on `B`: the unclipped numerator is already
zero, and both masking and clipping preserve zero. -/
theorem safeSourceBulkRate_eq_zero_of_historyBeforeCoordinate_full_length
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x)
    (hlength : history.length = 2 * n)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample = 0 := by
  have hsource := initialSeenSource_eq_of_historyBeforeCoordinate sample hbefore
  have htarget := initialSeenTarget_eq_of_historyBeforeCoordinate sample hbefore
  have hbefore' : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x := by
    simpa [hsource, htarget] using hbefore
  have hstateRate : FeedbackStepState.sourceUnclippedStateRateAt lam
      (sample.scheduledState lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history) x = 0 :=
    HistoryBranch.sourceUnclippedStateRateAt_eq_zero_of_full_length
      sample hbefore'.1.1 hlength
  have hunclipped : FiniteSample.safeSourceUnclippedRateAt
      hlam0 hlamHalf x0 p0 u sample = 0 :=
    (safeSourceUnclippedRateAt_eq_sourceUnclippedStateRateAt_of_historyBeforeCoordinate
      sample hlam0 hlamHalf hx0x hbefore' u hu).trans hstateRate
  rw [safeSourceBulkRate, hunclipped]
  simp [clipToStrip]

/-- Target analogue of `safeSourceBulkRate_eq_zero_of_historyBeforeCoordinate_full_length`. -/
theorem safeTargetBulkRate_eq_zero_of_historyBeforeCoordinate_full_length
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x)
    (hlength : history.length = 2 * n)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample = 0 := by
  have hsource := initialSeenSource_eq_of_historyBeforeCoordinate sample hbefore
  have htarget := initialSeenTarget_eq_of_historyBeforeCoordinate sample hbefore
  have hbefore' : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x := by
    simpa [hsource, htarget] using hbefore
  have hstateRate : FeedbackStepState.targetUnclippedStateRateAt lam
      (sample.scheduledState lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history) x = 0 :=
    HistoryBranch.targetUnclippedStateRateAt_eq_zero_of_full_length
      sample hbefore'.1.1 hlength
  have hunclipped : FiniteSample.safeTargetUnclippedRateAt
      hlam0 hlamHalf x0 p0 u sample = 0 :=
    (safeTargetUnclippedRateAt_eq_targetUnclippedStateRateAt_of_historyBeforeCoordinate
      sample hlam0 hlamHalf hx0x hbefore' u hu).trans hstateRate
  rw [safeTargetBulkRate, hunclipped]
  simp [clipToStrip]

/-! `HistoryCellIndex` entry points used by the finite strict-cell partition. -/

/-- The stored upper bound turns failure of the strict nonterminal bound into full length. -/
theorem HistoryCellIndex.history_length_eq_two_mul_of_not_lt
    (index : HistoryCellIndex n) (hterminal : ¬ index.history.length < 2 * n) :
    index.history.length = 2 * n := by
  exact Nat.le_antisymm index.history_length_le (not_lt.mp hterminal)

theorem safeSourceBulkRate_eq_zero_of_historyBeforeCell_full_length
    (index : HistoryCellIndex n) (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    (hcell : sample ∈ historyBeforeCell index lam x0 p0 x)
    (hlength : index.history.length = 2 * n)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample = 0 := by
  exact safeSourceBulkRate_eq_zero_of_historyBeforeCoordinate_full_length
    sample hlam0 hlamHalf hx0x hcell hlength u hu

theorem safeTargetBulkRate_eq_zero_of_historyBeforeCell_full_length
    (index : HistoryCellIndex n) (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    (hcell : sample ∈ historyBeforeCell index lam x0 p0 x)
    (hlength : index.history.length = 2 * n)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample = 0 := by
  exact safeTargetBulkRate_eq_zero_of_historyBeforeCoordinate_full_length
    sample hlam0 hlamHalf hx0x hcell hlength u hu

/-- Source terminal-cell entry point phrased as the complement of the strict length bound. -/
theorem safeSourceBulkRate_eq_zero_of_historyBeforeCell_not_lt
    (index : HistoryCellIndex n) (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    (hcell : sample ∈ historyBeforeCell index lam x0 p0 x)
    (hterminal : ¬ index.history.length < 2 * n)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample = 0 := by
  exact safeSourceBulkRate_eq_zero_of_historyBeforeCell_full_length
    index sample hlam0 hlamHalf hx0x hcell
      (HistoryCellIndex.history_length_eq_two_mul_of_not_lt index hterminal) u hu

/-- Target terminal-cell entry point phrased as the complement of the strict length bound. -/
theorem safeTargetBulkRate_eq_zero_of_historyBeforeCell_not_lt
    (index : HistoryCellIndex n) (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    (hcell : sample ∈ historyBeforeCell index lam x0 p0 x)
    (hterminal : ¬ index.history.length < 2 * n)
    (u : ℝ≥0) (hu : FiniteSample.elapsedFeedbackCoordinate x0 u = x) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample = 0 := by
  exact safeTargetBulkRate_eq_zero_of_historyBeforeCell_full_length
    index sample hlam0 hlamHalf hx0x hcell
      (HistoryCellIndex.history_length_eq_two_mul_of_not_lt index hterminal) u hu

end OTSelector
