import OTSelector.Feedback.FiniteHistoryBulkWitness
import OTSelector.Feedback.FiniteHistoryBulkInterval
import OTSelector.Feedback.FiniteHistoryProductSection

/-!
# A realized reference in a non-empty bulk section

The bulk witness is chosen in the timed unseen rectangle at the left endpoint of a
non-empty clipped bulk interval.  The canonical seen/unseen merge then realizes the
same forced history at that coordinate.  This is a deterministic construction: there
is no conditional-law, certificate, `sorry`, or axiom in this module.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## Left-endpoint bulk reference -/

/-- A non-empty clipped bulk interval contains a canonical unseen witness whose merge is
    a coordinate cell at the left endpoint.  The merge keeps the prescribed seen tuple and
    has the same scheduled state as the reference terminal state. -/
theorem exists_historyAtCoordinate_finiteSampleSeenUnseenMerge_of_feedbackBranchBulk
    (reference : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (width s t a b : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (ha : a = feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hb : b = feedbackBranchBulkStop width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (hab : a ≤ b)
    (hn : 0 < n) (hwidth : 0 < width) :
    ∃ unseen : feedbackUnseenFinset
        (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight,
      unseen ∈ feedbackUnseenRectangularSetAt lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) a
        (feedbackTerminalLabelSet sourcePattern targetPattern history) ∧
      HistoryAtCoordinate
        (finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
        lam x0 p0 sourcePattern targetPattern history a ∧
      (finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen).scheduledState
        lam x0 p0 sourcePattern targetPattern history =
        reference.scheduledState lam x0 p0 sourcePattern targetPattern history ∧
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history)
        (finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen) = seen := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hterminal_le_a : terminal.x ≤ a := by
    rw [ha]
    exact feedbackBranchBulkStart_ge_state width lam terminal s
  have hbulk : feedbackBulkRegion n width a
      (segmentCurve terminal.x terminal.p (terminal.slope lam) a) := by
    apply feedbackBulkRegion_on_branchBulkInterval width lam terminal s t a hwidth
    constructor
    · exact ha.symm.le
    · calc
        a ≤ b := hab
        _ = feedbackBranchBulkStop width lam terminal t := hb
  have hnonempty := feedbackUnseenRectangularSetAt_nonempty_of_feedbackBulkRegion
    terminal width lam a S hn hwidth hlam0 hlamHalf hbulk
  rcases hnonempty with ⟨unseen, hunseen⟩
  let merged := finiteSampleSeenUnseenMerge S seen unseen
  have hseenTuple : feedbackSeenTuple S reference = feedbackSeenTuple S merged := by
    rw [feedbackSeenTuple_finiteSampleSeenUnseenMerge]
    exact hseen.symm
  have hremainingAt : LiesInStateRemainingAt lam terminal a merged := by
    apply (liesInStateRemainingAt_finiteSampleSeenUnseenMerge_iff lam terminal a S
      (fun i ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
        reference lam x0 p0 sourcePattern targetPattern history i)
      (fun j ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
        reference lam x0 p0 sourcePattern targetPattern history j)
      seen unseen).2
    exact (mem_feedbackUnseenRectangularSetAt_iff lam terminal a S unseen).1 hunseen
  have hbranchMerged : HistoryBranch merged lam x0 p0 sourcePattern targetPattern history := by
    apply (historyBranch_iff_liesInStateRemaining_of_seenTuple_eq
      reference merged hlam0 hlamHalf href hseenTuple).2
    exact hremainingAt.liesInStateRemaining merged hlam0 hlamHalf terminal hterminal_le_a
  have hscheduled : merged.scheduledState lam x0 p0 sourcePattern targetPattern history = terminal := by
    symm
    exact scheduledState_eq_of_feedbackSeenTuple_eq reference merged lam x0 p0
      sourcePattern targetPattern history hseenTuple
  have hcoordinate : HistoryAtCoordinate merged lam x0 p0
      sourcePattern targetPattern history a := by
    change HistoryBranch merged lam x0 p0 sourcePattern targetPattern history ∧
      (merged.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ a ∧
      LiesInStateRemainingAt lam
        (merged.scheduledState lam x0 p0 sourcePattern targetPattern history) a merged
    refine ⟨hbranchMerged, ?_, ?_⟩
    · rw [hscheduled]
      exact hterminal_le_a
    · rw [hscheduled]
      exact hremainingAt
  refine ⟨unseen, hunseen, ?_, ?_, ?_⟩
  · simpa [merged] using hcoordinate
  · simpa [merged] using hscheduled
  · simp

end OTSelector
