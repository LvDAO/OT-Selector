import OTSelector.Feedback.FiniteHistoryProductSection

/-!
# Timed history cells from a realized branch

For a fixed seen tuple, a realized terminal branch already determines the scheduled state.
Consequently, at every later coordinate the canonical seen/unseen merge is a history cell exactly
when its unseen tuple lies in the corresponding timed remaining rectangle.  The reference sample
need not itself remain in the same cell at the later coordinate.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

/-- A realized branch and its terminal seen tuple identify every later timed history section. -/
theorem historyAtCoordinate_finiteSampleSeenUnseenMerge_iff_of_historyBranch
    (reference : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (unseen : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (hterminalx :
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x) :
    HistoryAtCoordinate
        (finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
        lam x0 p0 sourcePattern targetPattern history x ↔
      unseen ∈ feedbackUnseenRectangularSetAt lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) x
        (feedbackTerminalLabelSet sourcePattern targetPattern history) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  let sample := finiteSampleSeenUnseenMerge S seen unseen
  have htuple : feedbackSeenTuple S reference = feedbackSeenTuple S sample := by
    rw [feedbackSeenTuple_finiteSampleSeenUnseenMerge]
    exact hseen.symm
  have hstateEq : sample.scheduledState lam x0 p0 sourcePattern targetPattern history =
      terminal := by
    symm
    exact scheduledState_eq_of_feedbackSeenTuple_eq reference sample lam x0 p0
      sourcePattern targetPattern history htuple
  have hremaining_iff : LiesInStateRemainingAt lam terminal x sample ↔
      unseen ∈ feedbackUnseenRectangularSetAt lam terminal x S := by
    rw [mem_feedbackUnseenRectangularSetAt_iff]
    apply liesInStateRemainingAt_finiteSampleSeenUnseenMerge_iff
    · intro i
      exact (mem_feedbackTerminalLabelSet_inl_iff_seenSource
        reference lam x0 p0 sourcePattern targetPattern history i)
    · intro j
      exact (mem_feedbackTerminalLabelSet_inr_iff_seenTarget
        reference lam x0 p0 sourcePattern targetPattern history j)
  change HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x ↔ _
  constructor
  · intro hsample
    change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x ∧
      LiesInStateRemainingAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x sample at hsample
    apply hremaining_iff.mp
    simpa [terminal, hstateEq] using hsample.2.2
  · intro hunseen
    have hremainingAt : LiesInStateRemainingAt lam terminal x sample :=
      hremaining_iff.mpr hunseen
    have hremainingTerminal : LiesInStateRemaining lam terminal sample :=
      hremainingAt.liesInStateRemaining sample hlam0 hlamHalf terminal hterminalx
    have hbranchSample :
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history :=
      (historyBranch_iff_liesInStateRemaining_of_seenTuple_eq
        reference sample hlam0 hlamHalf href htuple).2 hremainingTerminal
    change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x ∧
      LiesInStateRemainingAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x sample
    refine ⟨hbranchSample, ?_, ?_⟩
    · simpa [terminal, ← hstateEq] using hterminalx
    · simpa [terminal, ← hstateEq] using hremainingAt

/-- Set form of `historyAtCoordinate_finiteSampleSeenUnseenMerge_iff_of_historyBranch`. -/
theorem historyAtCoordinate_finiteSampleSeenUnseenMerge_set_eq_of_historyBranch
    (reference : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (hterminalx :
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x) :
    {unseen : feedbackUnseenFinset
        (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight |
      HistoryAtCoordinate
        (finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
        lam x0 p0 sourcePattern targetPattern history x} =
      feedbackUnseenRectangularSetAt lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) x
        (feedbackTerminalLabelSet sourcePattern targetPattern history) := by
  ext unseen
  exact historyAtCoordinate_finiteSampleSeenUnseenMerge_iff_of_historyBranch
    reference hlam0 hlamHalf href seen unseen hseen hterminalx

end OTSelector
