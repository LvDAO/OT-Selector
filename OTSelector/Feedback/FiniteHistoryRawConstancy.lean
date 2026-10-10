import OTSelector.Feedback.FiniteHistoryRawEvent

/-!
# Raw revealed-event constancy on finite-history branches

This file records the two deterministic cases used later for predictable rectangles.  A branch
already determines the observed path up to its terminal knot; after the knot, the fixed terminal
remaining condition gives the same conclusion through `HistoryAtCoordinate`.

There is no conditional-law or certificate interface here.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

/-! ## A branch at its terminal coordinate -/

/-- A realized forced history is a coordinate cell at its own scheduled terminal knot. -/
theorem historyBranch_historyAtCoordinate_terminal
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history) :
    HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x := by
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hsource : ∀ i, i ∉ terminal.seenSource →
      sample.sourcePoint i ∈ sourceRawRemainingSet n terminal.p terminal.x := by
    intro i hi
    exact (mem_sourceRawRemainingSet_iff sample terminal lam i).2
      (HistoryBranch.sourcePoint_mem_sourceRemainingSet sample hlam0 hlamHalf hbranch i hi)
  have htarget : ∀ j, j ∉ terminal.seenTarget →
      sample.targetPoint j ∈ targetRawRemainingSet n terminal.p terminal.x := by
    intro j hj
    exact (mem_targetRawRemainingSet_iff sample terminal lam j).2
      (HistoryBranch.targetPoint_mem_targetRemainingSet sample hlam0 hlamHalf hbranch j hj)
  have hremaining : LiesInStateRemainingAt lam terminal terminal.x sample := by
    constructor
    · intro i hi
      simpa [sourceRawRemainingSetAt, segmentCurve, terminal] using hsource i hi
    · intro j hj
      simpa [targetRawRemainingSetAt, segmentCurve, terminal] using htarget j hj
  change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
    terminal.x ≤ terminal.x ∧ LiesInStateRemainingAt lam terminal terminal.x sample
  exact ⟨hbranch, le_rfl, hremaining⟩

private theorem historyBranch_terminal_ge_x0
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history) :
    x0 ≤ (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x := by
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hstate := FiniteSample.feedbackState_eq_scheduledState_of_history sample lam x0 p0
    sourcePattern targetPattern history hbranch.1 hbranch.2
  have hknot : sample.feedbackKnot lam x0 p0 history.length = terminal.x := by
    simpa [FiniteSample.feedbackKnot, terminal] using congrArg FeedbackStepState.x hstate
  have hge := sample.feedbackKnot_ge_x0 hlam0 hlamHalf x0 p0 history.length
  rw [hknot] at hge
  exact hge

/-! ## Constancy before the terminal knot -/

/-- A raw event observed no later than the common terminal knot is constant on two realized
branches with the same terminal seen tuple. -/
theorem rawRevealedEvent_mem_iff_of_historyBranch_before_terminal
    (reference sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (hsample : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample)
    (hxterminal : x ≤
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x)
    (B : Set (FiniteSample n))
    (hB : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x⟩] B) :
    reference ∈ B ↔ sample ∈ B := by
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hterminalEq :
      reference.scheduledState lam x0 p0 sourcePattern targetPattern history =
        sample.scheduledState lam x0 p0 sourcePattern targetPattern history :=
    scheduledState_eq_of_feedbackSeenTuple_eq reference sample lam x0 p0
      sourcePattern targetPattern history htuple
  have hrefTerminal := historyBranch_historyAtCoordinate_terminal reference
    hlam0 hlamHalf href
  have hsampleTerminal' := historyBranch_historyAtCoordinate_terminal sample
    hlam0 hlamHalf hsample
  have hsampleTerminal :
      HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history terminal.x := by
    simpa [terminal, hterminalEq] using hsampleTerminal'
  have hterminalGe : x0 ≤ terminal.x := by
    exact historyBranch_terminal_ge_x0 reference hlam0 hlamHalf href
  have htime :
      (⟨x - x0, sub_nonneg.mpr hx0x⟩ : ℝ≥0) ≤
        ⟨terminal.x - x0, sub_nonneg.mpr hterminalGe⟩ := by
    apply NNReal.coe_le_coe.mp
    change x - x0 ≤ terminal.x - x0
    linarith
  have hBterminal : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨terminal.x - x0, sub_nonneg.mpr hterminalGe⟩] B := by
    exact (Filtration.mono
      (FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) htime) B hB
  exact rawRevealedEvent_mem_iff_of_historyAtCoordinate reference sample
    hlam0 hlamHalf hterminalGe hrefTerminal hsampleTerminal htuple B hBterminal

/-! ## Constancy after the terminal knot -/

/-- If both samples satisfy the same terminal remaining condition at a later coordinate, the raw
event is constant there. -/
theorem rawRevealedEvent_mem_iff_of_historyBranch_after_terminal
    (reference sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (hsample : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample)
    (hterminal :
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x)
    (hrefRemaining : LiesInStateRemainingAt lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) x reference)
    (hsampleRemaining : LiesInStateRemainingAt lam
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x sample)
    (B : Set (FiniteSample n))
    (hB : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x⟩] B) :
    reference ∈ B ↔ sample ∈ B := by
  have hterminalEq :
      reference.scheduledState lam x0 p0 sourcePattern targetPattern history =
        sample.scheduledState lam x0 p0 sourcePattern targetPattern history :=
    scheduledState_eq_of_feedbackSeenTuple_eq reference sample lam x0 p0
      sourcePattern targetPattern history htuple
  have hrefAt :
      HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history x := by
    change HistoryBranch reference lam x0 p0 sourcePattern targetPattern history ∧
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x ∧
        LiesInStateRemainingAt lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) x reference
    exact ⟨href, hterminal, hrefRemaining⟩
  have hsampleAt :
      HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x := by
    change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x ∧
        LiesInStateRemainingAt lam
          (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x sample
    exact ⟨hsample, by simpa [hterminalEq] using hterminal, hsampleRemaining⟩
  exact rawRevealedEvent_mem_iff_of_historyAtCoordinate reference sample
    hlam0 hlamHalf hx0x hrefAt hsampleAt htuple B hB

/-! ## A single branch-constancy interface -/

/-- Unified raw-event constancy: either the observation is before the common terminal knot, or both
samples satisfy the common later remaining condition. -/
theorem rawRevealedEvent_mem_iff_of_historyBranch
    (reference sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (hsample : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample)
    (hcase :
      x ≤ (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x ∨
      ((reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x ∧
        LiesInStateRemainingAt lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) x reference ∧
        LiesInStateRemainingAt lam
          (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x sample))
    (B : Set (FiniteSample n))
    (hB : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x⟩] B) :
    reference ∈ B ↔ sample ∈ B := by
  rcases hcase with hbefore | hafter
  · exact rawRevealedEvent_mem_iff_of_historyBranch_before_terminal reference sample
      hlam0 hlamHalf hx0x href hsample htuple hbefore B hB
  · exact rawRevealedEvent_mem_iff_of_historyBranch_after_terminal reference sample
      hlam0 hlamHalf hx0x href hsample htuple hafter.1 hafter.2.1 hafter.2.2 B hB

end OTSelector
