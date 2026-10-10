import OTSelector.Feedback.FiniteHistoryCoverage
import OTSelector.Feedback.FiniteHistoryAt
import OTSelector.Feedback.RevealedHistory

/-!
# Revealed snapshots on a finite-history section

On a fixed labelled history, the terminal seen tuple contains exactly the marked points exposed
by the scheduled terminal state.  Hence the scheduled revealed snapshot factors through that
finite tuple.  This deterministic factorization is the bridge needed before passing from the
seen/unseen Fubini identity to events in the raw revealed filtration.

The history-coverage bridge then identifies the scheduled terminal state with the actual elapsed
state at the observation coordinate, so the same factorization holds for the actual snapshot.
-/

namespace OTSelector

variable {n : ℕ}

private theorem maskedSourceArray_scheduled_eq_of_feedbackSeenTuple_eq
    (reference sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    let state := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    FiniteSample.maskedSourceArray reference state =
      FiniteSample.maskedSourceArray sample state := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let state := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  funext i
  by_cases hi : i ∈ state.seenSource
  · have hiS : (Sum.inl i : FeedbackLabel n) ∈ S := by
      exact (mem_feedbackTerminalLabelSet_inl_iff_seenSource
        reference lam x0 p0 sourcePattern targetPattern history i).2 hi
    have hpoint := congrFun htuple (⟨Sum.inl i, hiS⟩ : S)
    simpa [state, FiniteSample.maskedSourceArray, FiniteSample.maskedSourcePoint,
      hi, feedbackSeenTuple, feedbackLabelTuple, feedbackLabelPoint] using hpoint
  · simp [state, FiniteSample.maskedSourceArray, FiniteSample.maskedSourcePoint, hi]

private theorem maskedTargetArray_scheduled_eq_of_feedbackSeenTuple_eq
    (reference sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    let state := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    FiniteSample.maskedTargetArray reference state =
      FiniteSample.maskedTargetArray sample state := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let state := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  funext j
  by_cases hj : j ∈ state.seenTarget
  · have hjS : (Sum.inr j : FeedbackLabel n) ∈ S := by
      exact (mem_feedbackTerminalLabelSet_inr_iff_seenTarget
        reference lam x0 p0 sourcePattern targetPattern history j).2 hj
    have hpoint := congrFun htuple (⟨Sum.inr j, hjS⟩ : S)
    simpa [state, FiniteSample.maskedTargetArray, FiniteSample.maskedTargetPoint,
      hj, feedbackSeenTuple, feedbackLabelTuple, feedbackLabelPoint] using hpoint
  · simp [state, FiniteSample.maskedTargetArray, FiniteSample.maskedTargetPoint, hj]

/-- The scheduled revealed snapshot on a fixed history is determined by its terminal seen tuple.
-/
theorem revealedSnapshotFromState_scheduled_eq_of_feedbackSeenTuple_eq
    (reference sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    FiniteSample.revealedSnapshotFromState reference
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) =
      FiniteSample.revealedSnapshotFromState sample
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) := by
  have hstate := scheduledState_eq_of_feedbackSeenTuple_eq
    reference sample lam x0 p0 sourcePattern targetPattern history htuple
  rw [← hstate]
  have hsource := maskedSourceArray_scheduled_eq_of_feedbackSeenTuple_eq
    reference sample lam x0 p0 sourcePattern targetPattern history htuple
  have htarget := maskedTargetArray_scheduled_eq_of_feedbackSeenTuple_eq
    reference sample lam x0 p0 sourcePattern targetPattern history htuple
  simp only [FiniteSample.revealedSnapshotFromState]
  rw [hsource, htarget]

/-- A fixed history cell with the same terminal seen tuple has the same actual revealed snapshot.
-/
theorem revealedSnapshotAtElapsed_eq_of_historyAtCoordinate
    (reference sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history x)
    (hsample : HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x⟩ =
      sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x⟩ := by
  have hrefInitial :
      reference.initialFeedbackState x0 p0 =
        FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern :=
    href.1.1
  have hsampleInitial :
      sample.initialFeedbackState x0 p0 =
        FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern :=
    hsample.1.1
  have hrefSource : reference.initialSeenSource x0 p0 = sourcePattern := by
    have h := congrArg FeedbackStepState.seenSource hrefInitial
    simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h
  have hrefTarget : reference.initialSeenTarget x0 p0 = targetPattern := by
    have h := congrArg FeedbackStepState.seenTarget hrefInitial
    simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h
  have hsampleSource : sample.initialSeenSource x0 p0 = sourcePattern := by
    have h := congrArg FeedbackStepState.seenSource hsampleInitial
    simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h
  have hsampleTarget : sample.initialSeenTarget x0 p0 = targetPattern := by
    have h := congrArg FeedbackStepState.seenTarget hsampleInitial
    simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h
  have hrefActual :
      HistoryAtCoordinate reference lam x0 p0
        (reference.initialSeenSource x0 p0) (reference.initialSeenTarget x0 p0) history x := by
    rw [hrefSource, hrefTarget]
    exact href
  have hsampleActual :
      HistoryAtCoordinate sample lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x := by
    rw [hsampleSource, hsampleTarget]
    exact hsample
  have hrefState := HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
    reference hlam0 hlamHalf hx0x history hrefActual
  have hsampleState := HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
    sample hlam0 hlamHalf hx0x history hsampleActual
  have hsched := revealedSnapshotFromState_scheduled_eq_of_feedbackSeenTuple_eq
    reference sample lam x0 p0 sourcePattern targetPattern history htuple
  simpa [FiniteSample.revealedSnapshotAtElapsed, hrefState, hsampleState, hrefSource, hrefTarget,
    hsampleSource, hsampleTarget] using hsched

end OTSelector
