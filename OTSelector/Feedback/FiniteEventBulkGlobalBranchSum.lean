import OTSelector.Feedback.FiniteEventBulkHistorySum
import OTSelector.Feedback.FiniteEventBulkBranchSum

/-!
# Global bulk-event sums over finite history branches

The thinned finite-event count increment is first decomposed over recursive event steps and then
over the finite history-cell partition at each step.  This file only composes the two pathwise
identities; it contains no probabilistic or compensator assertion.
-/

open Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

open CountingProcess FiniteSample

theorem finiteEventCountThinned_source_sub_eq_historyCellIndex_nextLabel_sum
    (sample : FiniteSample n) {lam B x0 p0 : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hgood : sample.NoFeedbackTies lam x0 p0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample -
      finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n, if
        index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
            index.history then
        ∑ i : Fin n, if
          feedbackUnseenTuple
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                index.history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                index.history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                index.history)
              (Sum.inl i) then 1 else 0
      else 0 := by
  rw [finiteEventCountThinned_source_sub_eq_sum_newSource_bulk_card
    sample hlam0 hlamHalf B x0 p0 hgood hst]
  apply Finset.sum_congr rfl
  intro m hm
  exact finiteEventBulk_newSource_card_eq_historyCellIndex_nextLabel_sum
    sample hlam0 hlamHalf hgood m hst

theorem finiteEventCountThinned_target_sub_eq_historyCellIndex_nextLabel_sum
    (sample : FiniteSample n) {lam B x0 p0 : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hgood : sample.NoFeedbackTies lam x0 p0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample -
      finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n, if
        index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
            index.history then
        ∑ j : Fin n, if
          feedbackUnseenTuple
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                index.history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                index.history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                index.history)
              (Sum.inr j) then 1 else 0
      else 0 := by
  rw [finiteEventCountThinned_target_sub_eq_sum_newTarget_bulk_card
    sample hlam0 hlamHalf B x0 p0 hgood hst]
  apply Finset.sum_congr rfl
  intro m hm
  exact finiteEventBulk_newTarget_card_eq_historyCellIndex_nextLabel_sum
    sample hlam0 hlamHalf hgood m hst

end OTSelector
