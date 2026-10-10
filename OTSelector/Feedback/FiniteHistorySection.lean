import OTSelector.Feedback.FiniteHistoryFiberMeasurable
import OTSelector.Feedback.FiniteSampleSplitLaw

/-!
# Seen/unseen sections of a finite feedback history

For a fixed combinatorial history, the terminal seen labels form a finite set.  Samples with the
same tuple on that set agree on every point recorded by the terminal state.  If one such sample
realizes the history, the deterministic fibre identity identifies the entire unseen section with
the product of the strict terminal remaining regions.

This is still a deterministic section statement.  Continuous revealed values are parameters, not
atoms of the revealed sigma-algebra.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## Terminal label set -/

/-- Source and target labels visible after processing a prescribed history. -/
def feedbackTerminalLabelSet (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) : Finset (FeedbackLabel n) :=
  (sourcePattern ∪ FiniteSample.sourceHistorySet history).image
      (fun i ↦ (Sum.inl i : FeedbackLabel n)) ∪
    (targetPattern ∪ FiniteSample.targetHistorySet history).image
      (fun j ↦ (Sum.inr j : FeedbackLabel n))

@[simp]
theorem mem_feedbackTerminalLabelSet_inl
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (i : Fin n) :
    (Sum.inl i : FeedbackLabel n) ∈
        feedbackTerminalLabelSet sourcePattern targetPattern history ↔
      i ∈ sourcePattern ∪ FiniteSample.sourceHistorySet history := by
  simp [feedbackTerminalLabelSet]

@[simp]
theorem mem_feedbackTerminalLabelSet_inr
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (j : Fin n) :
    (Sum.inr j : FeedbackLabel n) ∈
        feedbackTerminalLabelSet sourcePattern targetPattern history ↔
      j ∈ targetPattern ∪ FiniteSample.targetHistorySet history := by
  simp [feedbackTerminalLabelSet]

theorem mem_feedbackTerminalLabelSet_inl_iff_seenSource
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (i : Fin n) :
    (Sum.inl i : FeedbackLabel n) ∈
        feedbackTerminalLabelSet sourcePattern targetPattern history ↔
      i ∈ (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource := by
  rw [FiniteSample.scheduledState_seenSource]
  exact mem_feedbackTerminalLabelSet_inl sourcePattern targetPattern history i

theorem mem_feedbackTerminalLabelSet_inr_iff_seenTarget
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (j : Fin n) :
    (Sum.inr j : FeedbackLabel n) ∈
        feedbackTerminalLabelSet sourcePattern targetPattern history ↔
      j ∈ (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget := by
  rw [FiniteSample.scheduledState_seenTarget]
  exact mem_feedbackTerminalLabelSet_inr sourcePattern targetPattern history j

/-! ## Agreement from the seen tuple -/

/-- Equality of the terminal seen tuple is exactly enough for pointwise terminal agreement. -/
theorem agreesOnStateSeen_of_feedbackSeenTuple_eq
    (reference sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    AgreesOnStateSeen
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
      reference sample := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  constructor
  · intro i hi
    have hiS : (Sum.inl i : FeedbackLabel n) ∈ S := by
      exact (mem_feedbackTerminalLabelSet_inl_iff_seenSource
        reference lam x0 p0 sourcePattern targetPattern history i).2 hi
    have hpoint := congrFun htuple (⟨Sum.inl i, hiS⟩ : S)
    simpa [S, feedbackSeenTuple, feedbackLabelTuple] using hpoint
  · intro j hj
    have hjS : (Sum.inr j : FeedbackLabel n) ∈ S := by
      exact (mem_feedbackTerminalLabelSet_inr_iff_seenTarget
        reference lam x0 p0 sourcePattern targetPattern history j).2 hj
    have hpoint := congrFun htuple (⟨Sum.inr j, hjS⟩ : S)
    simpa [S, feedbackSeenTuple, feedbackLabelTuple] using hpoint

/-! ## Exact history sections -/

/-- In a fixed seen-tuple section containing a realized reference, branch realization is exactly
the terminal remaining-region condition. -/
theorem historyBranch_iff_liesInStateRemaining_of_seenTuple_eq
    (reference sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ↔
      LiesInStateRemaining lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) sample := by
  have hagrees := agreesOnStateSeen_of_feedbackSeenTuple_eq
    reference sample lam x0 p0 sourcePattern targetPattern history htuple
  constructor
  · intro hsample
    have hfibre := finiteHistoryFibre_of_historyBranch_of_agrees
      reference sample hlam0 hlamHalf hsample hagrees
    exact hfibre.2
  · intro hremaining
    exact historyBranch_of_mem_finiteHistoryFibre
      reference sample hlam0 hlamHalf href ⟨hagrees, hremaining⟩

/-- Set form of the exact history-section identity. -/
theorem historyBranch_seenTuple_section_eq_remaining
    (reference : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history) :
    {sample : FiniteSample n |
        feedbackSeenTuple
            (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
          feedbackSeenTuple
            (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∧
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history} =
      {sample : FiniteSample n |
        feedbackSeenTuple
            (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
          feedbackSeenTuple
            (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∧
        LiesInStateRemaining lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) sample} := by
  ext sample
  constructor
  · rintro ⟨htuple, hsample⟩
    exact ⟨htuple,
      (historyBranch_iff_liesInStateRemaining_of_seenTuple_eq
        reference sample hlam0 hlamHalf href htuple).1 hsample⟩
  · rintro ⟨htuple, hremaining⟩
    exact ⟨htuple,
      (historyBranch_iff_liesInStateRemaining_of_seenTuple_eq
        reference sample hlam0 hlamHalf href htuple).2 hremaining⟩

/-! ## One-point factors in the unseen product -/

/-- The strict terminal remaining region attached to one source or target label. -/
def feedbackLabelRemainingSet (terminal : FeedbackStepState n) :
    FeedbackLabel n → Set MarkedHeight
  | Sum.inl _ => sourceRawRemainingSet n terminal.p terminal.x
  | Sum.inr _ => targetRawRemainingSet n terminal.p terminal.x

theorem isOpen_feedbackLabelRemainingSet
    (terminal : FeedbackStepState n) (label : FeedbackLabel n) :
    IsOpen (feedbackLabelRemainingSet terminal label) := by
  cases label with
  | inl i => exact isOpen_sourceRawRemainingSet n terminal.p terminal.x
  | inr j => exact isOpen_targetRawRemainingSet n terminal.p terminal.x

theorem measurableSet_feedbackLabelRemainingSet
    (terminal : FeedbackStepState n) (label : FeedbackLabel n) :
    MeasurableSet (feedbackLabelRemainingSet terminal label) :=
  (isOpen_feedbackLabelRemainingSet terminal label).measurableSet

/-- Every unseen factor of a realized history has positive one-point mass. -/
theorem unitSquareUniform_feedbackLabelRemainingSet_pos
    (reference : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (label : FeedbackLabel n)
    (hlabel : label ∉ feedbackTerminalLabelSet sourcePattern targetPattern history) :
    0 < (unitSquareUniform : Measure MarkedHeight)
      (feedbackLabelRemainingSet
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) label) := by
  let terminal :=
    reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hfibre := HistoryBranch.mem_finiteHistoryFibre
    reference hlam0 hlamHalf href
  change AgreesOnStateSeen terminal reference reference ∧
    LiesInStateRemaining lam terminal reference at hfibre
  cases label with
  | inl i =>
      have hi : i ∉ terminal.seenSource := by
        intro hi
        apply hlabel
        exact (mem_feedbackTerminalLabelSet_inl_iff_seenSource
          reference lam x0 p0 sourcePattern targetPattern history i).2 hi
      simpa [feedbackLabelRemainingSet, terminal] using hfibre.2.source_mass_pos hi
  | inr j =>
      have hj : j ∉ terminal.seenTarget := by
        intro hj
        apply hlabel
        exact (mem_feedbackTerminalLabelSet_inr_iff_seenTarget
          reference lam x0 p0 sourcePattern targetPattern history j).2 hj
      simpa [feedbackLabelRemainingSet, terminal] using hfibre.2.target_mass_pos hj

end OTSelector
