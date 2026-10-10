import OTSelector.Feedback.FiniteHistoryAt
import OTSelector.Feedback.FeedbackTupleCoding

/-!
# Product sections for finite feedback histories

This module is the deterministic bridge from the seen/unseen tuple coding to the terminal
remaining regions.  The merge is always the inverse of the measurable seen/unseen equivalence;
no conditional law interface is introduced here.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## The canonical merge -/

/-- Merge a seen and an unseen tuple through the finite-sample measurable equivalence. -/
noncomputable def finiteSampleSeenUnseenMerge (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) : FiniteSample n :=
  (finiteSampleSeenUnseenMeasurableEquiv S).symm (seen, unseen)

@[simp]
theorem feedbackSeenTuple_finiteSampleSeenUnseenMerge
    (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    feedbackSeenTuple S (finiteSampleSeenUnseenMerge S seen unseen) = seen := by
  have hsplit :=
    (finiteSampleSeenUnseenMeasurableEquiv S).apply_symm_apply (seen, unseen)
  rw [finiteSampleSeenUnseenMeasurableEquiv_apply] at hsplit
  exact congrArg Prod.fst hsplit

@[simp]
theorem feedbackUnseenTuple_finiteSampleSeenUnseenMerge
    (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    feedbackUnseenTuple S (finiteSampleSeenUnseenMerge S seen unseen) = unseen := by
  have hsplit :=
    (finiteSampleSeenUnseenMeasurableEquiv S).apply_symm_apply (seen, unseen)
  rw [finiteSampleSeenUnseenMeasurableEquiv_apply] at hsplit
  exact congrArg Prod.snd hsplit

/-! ## Rectangular unseen regions -/

/-- The product of the strict terminal remaining regions over the unseen labels. -/
def feedbackUnseenRectangularSet (terminal : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) : Set (feedbackUnseenFinset S → MarkedHeight) :=
  Set.univ.pi (fun label ↦ feedbackLabelRemainingSet terminal (label : FeedbackLabel n))

theorem measurableSet_feedbackUnseenRectangularSet
    (terminal : FeedbackStepState n) (S : Finset (FeedbackLabel n)) :
    MeasurableSet (feedbackUnseenRectangularSet terminal S) := by
  exact MeasurableSet.univ_pi fun label ↦ measurableSet_feedbackLabelRemainingSet terminal
    (label : FeedbackLabel n)

theorem mem_feedbackUnseenRectangularSet_iff
    (terminal : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    unseen ∈ feedbackUnseenRectangularSet terminal S ↔
      ∀ label : feedbackUnseenFinset S,
        unseen label ∈ feedbackLabelRemainingSet terminal (label : FeedbackLabel n) := by
  simp [feedbackUnseenRectangularSet]

/-! ## Merge and terminal remaining regions -/

private theorem feedbackUnseenMerge_sourcePoint_eq
    (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (i : Fin n) (hi : (Sum.inl i : FeedbackLabel n) ∉ S) :
    (finiteSampleSeenUnseenMerge S seen unseen).sourcePoint i =
      unseen ⟨Sum.inl i, by simp [feedbackUnseenFinset, hi]⟩ := by
  have htuple := congrFun
    (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen)
    (⟨Sum.inl i, by simp [feedbackUnseenFinset, hi]⟩ : feedbackUnseenFinset S)
  simpa [feedbackUnseenTuple, feedbackLabelTuple] using htuple

private theorem feedbackUnseenMerge_targetPoint_eq
    (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (j : Fin n) (hj : (Sum.inr j : FeedbackLabel n) ∉ S) :
    (finiteSampleSeenUnseenMerge S seen unseen).targetPoint j =
      unseen ⟨Sum.inr j, by simp [feedbackUnseenFinset, hj]⟩ := by
  have htuple := congrFun
    (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen)
    (⟨Sum.inr j, by simp [feedbackUnseenFinset, hj]⟩ : feedbackUnseenFinset S)
  simpa [feedbackUnseenTuple, feedbackLabelTuple] using htuple

/-- The terminal remaining predicate of the canonical merge is exactly the unseen rectangle. -/
theorem liesInStateRemaining_finiteSampleSeenUnseenMerge_iff
    (terminal : FeedbackStepState n) (lam : ℝ)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ terminal.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ terminal.seenTarget)
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    LiesInStateRemaining lam terminal (finiteSampleSeenUnseenMerge S seen unseen) ↔
      ∀ label : feedbackUnseenFinset S,
        unseen label ∈ feedbackLabelRemainingSet terminal (label : FeedbackLabel n) := by
  constructor
  · intro hremaining label
    rcases label with ⟨label, hlabel⟩
    cases label with
    | inl i =>
        have hiS : (Sum.inl i : FeedbackLabel n) ∉ S := by
          simpa [feedbackUnseenFinset] using hlabel
        have hi : i ∉ terminal.seenSource := by
          intro hiSeen
          exact hiS ((hsource i).2 hiSeen)
        have hraw :
            (finiteSampleSeenUnseenMerge S seen unseen).sourcePoint i ∈
              sourceRawRemainingSet n terminal.p terminal.x :=
          (mem_sourceRawRemainingSet_iff
            (finiteSampleSeenUnseenMerge S seen unseen) terminal lam i).2
            (hremaining.1 i hi)
        rw [feedbackUnseenMerge_sourcePoint_eq S seen unseen i hiS] at hraw
        simpa [feedbackLabelRemainingSet] using hraw
    | inr j =>
        have hjS : (Sum.inr j : FeedbackLabel n) ∉ S := by
          simpa [feedbackUnseenFinset] using hlabel
        have hj : j ∉ terminal.seenTarget := by
          intro hjSeen
          exact hjS ((htarget j).2 hjSeen)
        have hraw :
            (finiteSampleSeenUnseenMerge S seen unseen).targetPoint j ∈
              targetRawRemainingSet n terminal.p terminal.x :=
          (mem_targetRawRemainingSet_iff
            (finiteSampleSeenUnseenMerge S seen unseen) terminal lam j).2
            (hremaining.2 j hj)
        rw [feedbackUnseenMerge_targetPoint_eq S seen unseen j hjS] at hraw
        simpa [feedbackLabelRemainingSet] using hraw
  · intro hunseen
    constructor
    · intro i hi
      have hiS : (Sum.inl i : FeedbackLabel n) ∉ S := by
        intro hiMem
        exact hi ((hsource i).1 hiMem)
      have hraw :
          (finiteSampleSeenUnseenMerge S seen unseen).sourcePoint i ∈
            sourceRawRemainingSet n terminal.p terminal.x := by
        have hfactor := hunseen
          (⟨Sum.inl i, by simp [feedbackUnseenFinset, hiS]⟩ : feedbackUnseenFinset S)
        have hfactor' :
            unseen ⟨Sum.inl i, by simp [feedbackUnseenFinset, hiS]⟩ ∈
              sourceRawRemainingSet n terminal.p terminal.x := by
          simpa [feedbackLabelRemainingSet] using hfactor
        rw [← feedbackUnseenMerge_sourcePoint_eq S seen unseen i hiS] at hfactor'
        exact hfactor'
      exact (mem_sourceRawRemainingSet_iff
        (finiteSampleSeenUnseenMerge S seen unseen) terminal lam i).1 hraw
    · intro j hj
      have hjS : (Sum.inr j : FeedbackLabel n) ∉ S := by
        intro hjMem
        exact hj ((htarget j).1 hjMem)
      have hraw :
          (finiteSampleSeenUnseenMerge S seen unseen).targetPoint j ∈
            targetRawRemainingSet n terminal.p terminal.x := by
        have hfactor := hunseen
          (⟨Sum.inr j, by simp [feedbackUnseenFinset, hjS]⟩ : feedbackUnseenFinset S)
        have hfactor' :
            unseen ⟨Sum.inr j, by simp [feedbackUnseenFinset, hjS]⟩ ∈
              targetRawRemainingSet n terminal.p terminal.x := by
          simpa [feedbackLabelRemainingSet] using hfactor
        rw [← feedbackUnseenMerge_targetPoint_eq S seen unseen j hjS] at hfactor'
        exact hfactor'
      exact (mem_targetRawRemainingSet_iff
        (finiteSampleSeenUnseenMerge S seen unseen) terminal lam j).1 hraw

/-! ## Realized reference specialization -/

theorem historyBranch_finiteSampleSeenUnseenMerge_iff
    (reference : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen :
      feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (unseen : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference) :
    HistoryBranch
        (finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
        lam x0 p0 sourcePattern targetPattern history ↔
      ∀ label : feedbackUnseenFinset
        (feedbackTerminalLabelSet sourcePattern targetPattern history),
        unseen label ∈ feedbackLabelRemainingSet
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
          (label : FeedbackLabel n) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  have htuple : feedbackSeenTuple S reference = feedbackSeenTuple S
      (finiteSampleSeenUnseenMerge S seen unseen) := by
    rw [feedbackSeenTuple_finiteSampleSeenUnseenMerge]
    exact hseen.symm
  have hbranch := historyBranch_iff_liesInStateRemaining_of_seenTuple_eq
    reference (finiteSampleSeenUnseenMerge S seen unseen) hlam0 hlamHalf href htuple
  rw [hbranch]
  apply liesInStateRemaining_finiteSampleSeenUnseenMerge_iff
  · intro i
    exact (mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 sourcePattern targetPattern history i)
  · intro j
    exact (mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 sourcePattern targetPattern history j)

theorem unitSquareUniform_feedbackUnseenRectangularSet_factor_pos
    (reference : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (label : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history)) :
    0 < (unitSquareUniform : Measure MarkedHeight)
      (feedbackLabelRemainingSet
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
        (label : FeedbackLabel n)) := by
  apply unitSquareUniform_feedbackLabelRemainingSet_pos reference hlam0 hlamHalf href
  simpa [feedbackUnseenFinset] using label.property

/-! ## Timed-coordinate product sections -/

/-- The product of strict remaining regions at a later coordinate. -/
def feedbackUnseenRectangularSetAt (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) : Set (feedbackUnseenFinset S → MarkedHeight) :=
  Set.univ.pi (fun label ↦
    feedbackLabelRemainingSetAt lam terminal x (label : FeedbackLabel n))

theorem measurableSet_feedbackUnseenRectangularSetAt
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) :
    MeasurableSet (feedbackUnseenRectangularSetAt lam terminal x S) := by
  exact MeasurableSet.univ_pi fun label ↦ measurableSet_feedbackLabelRemainingSetAt lam terminal x
    (label : FeedbackLabel n)

theorem mem_feedbackUnseenRectangularSetAt_iff
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    unseen ∈ feedbackUnseenRectangularSetAt lam terminal x S ↔
      ∀ label : feedbackUnseenFinset S,
        unseen label ∈ feedbackLabelRemainingSetAt lam terminal x
          (label : FeedbackLabel n) := by
  simp [feedbackUnseenRectangularSetAt]

/-- The timed terminal remaining predicate of the canonical merge is exactly the unseen rectangle.
-/
theorem liesInStateRemainingAt_finiteSampleSeenUnseenMerge_iff
    (lam : ℝ) (terminal : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ terminal.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ terminal.seenTarget)
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    LiesInStateRemainingAt lam terminal x (finiteSampleSeenUnseenMerge S seen unseen) ↔
      ∀ label : feedbackUnseenFinset S,
        unseen label ∈ feedbackLabelRemainingSetAt lam terminal x
          (label : FeedbackLabel n) := by
  constructor
  · intro hremaining label
    rcases label with ⟨label, hlabel⟩
    cases label with
    | inl i =>
        have hiS : (Sum.inl i : FeedbackLabel n) ∉ S := by
          simpa [feedbackUnseenFinset] using hlabel
        have hi : i ∉ terminal.seenSource := by
          intro hiSeen
          exact hiS ((hsource i).2 hiSeen)
        have hpoint := hremaining.1 i hi
        rw [feedbackUnseenMerge_sourcePoint_eq S seen unseen i hiS] at hpoint
        simpa [feedbackLabelRemainingSetAt] using hpoint
    | inr j =>
        have hjS : (Sum.inr j : FeedbackLabel n) ∉ S := by
          simpa [feedbackUnseenFinset] using hlabel
        have hj : j ∉ terminal.seenTarget := by
          intro hjSeen
          exact hjS ((htarget j).2 hjSeen)
        have hpoint := hremaining.2 j hj
        rw [feedbackUnseenMerge_targetPoint_eq S seen unseen j hjS] at hpoint
        simpa [feedbackLabelRemainingSetAt] using hpoint
  · intro hunseen
    constructor
    · intro i hi
      have hiS : (Sum.inl i : FeedbackLabel n) ∉ S := by
        intro hiMem
        exact hi ((hsource i).1 hiMem)
      have hfactor := hunseen
        (⟨Sum.inl i, by simp [feedbackUnseenFinset, hiS]⟩ : feedbackUnseenFinset S)
      have hfactor' :
          unseen ⟨Sum.inl i, by simp [feedbackUnseenFinset, hiS]⟩ ∈
            sourceRawRemainingSetAt n lam terminal x := by
        simpa [feedbackLabelRemainingSetAt] using hfactor
      rw [← feedbackUnseenMerge_sourcePoint_eq S seen unseen i hiS] at hfactor'
      exact hfactor'
    · intro j hj
      have hjS : (Sum.inr j : FeedbackLabel n) ∉ S := by
        intro hjMem
        exact hj ((htarget j).1 hjMem)
      have hfactor := hunseen
        (⟨Sum.inr j, by simp [feedbackUnseenFinset, hjS]⟩ : feedbackUnseenFinset S)
      have hfactor' :
          unseen ⟨Sum.inr j, by simp [feedbackUnseenFinset, hjS]⟩ ∈
            targetRawRemainingSetAt n lam terminal x := by
        simpa [feedbackLabelRemainingSetAt] using hfactor
      rw [← feedbackUnseenMerge_targetPoint_eq S seen unseen j hjS] at hfactor'
      exact hfactor'

/-! ## Timed-coordinate realized cells -/

theorem historyAtCoordinate_finiteSampleSeenUnseenMerge_iff
    (reference : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history x)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (unseen : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference) :
    HistoryAtCoordinate
        (finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
        lam x0 p0 sourcePattern targetPattern history x ↔
      unseen ∈ feedbackUnseenRectangularSetAt lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) x
        (feedbackTerminalLabelSet sourcePattern targetPattern history) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  have htuple : feedbackSeenTuple S reference = feedbackSeenTuple S
      (finiteSampleSeenUnseenMerge S seen unseen) := by
    rw [feedbackSeenTuple_finiteSampleSeenUnseenMerge]
    exact hseen.symm
  have hcell := historyAtCoordinate_iff_liesInStateRemainingAt_of_seenTuple_eq
    reference (finiteSampleSeenUnseenMerge S seen unseen) hlam0 hlamHalf href htuple
  rw [hcell]
  rw [mem_feedbackUnseenRectangularSetAt_iff]
  apply liesInStateRemainingAt_finiteSampleSeenUnseenMerge_iff
  · intro i
    exact (mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 sourcePattern targetPattern history i)
  · intro j
    exact (mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 sourcePattern targetPattern history j)

set_option linter.unusedVariables false in
theorem unitSquareUniform_feedbackUnseenRectangularSetAt_factor_pos
    (reference : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history x)
    (label : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history)) :
    0 < (unitSquareUniform : Measure MarkedHeight)
      (feedbackLabelRemainingSetAt lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) x
        (label : FeedbackLabel n)) := by
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  let _ := unitSquareUniform_isOpenPosMeasure
  rcases label with ⟨label, hlabel⟩
  cases label with
  | inl i =>
      have hiS : (Sum.inl i : FeedbackLabel n) ∉
          feedbackTerminalLabelSet sourcePattern targetPattern history := by
        simpa [feedbackUnseenFinset] using hlabel
      have hi : i ∉ terminal.seenSource := by
        intro hiSeen
        exact hiS ((mem_feedbackTerminalLabelSet_inl_iff_seenSource
          reference lam x0 p0 sourcePattern targetPattern history i).2 hiSeen)
      have hpoint : reference.sourcePoint i ∈
          sourceRawRemainingSetAt n lam terminal x := by
        exact href.2.2.1 i hi
      simpa [terminal, feedbackLabelRemainingSetAt] using
        (isOpen_sourceRawRemainingSetAt lam terminal x).measure_pos
          (unitSquareUniform : Measure MarkedHeight)
          ⟨reference.sourcePoint i, hpoint⟩
  | inr j =>
      have hjS : (Sum.inr j : FeedbackLabel n) ∉
          feedbackTerminalLabelSet sourcePattern targetPattern history := by
        simpa [feedbackUnseenFinset] using hlabel
      have hj : j ∉ terminal.seenTarget := by
        intro hjSeen
        exact hjS ((mem_feedbackTerminalLabelSet_inr_iff_seenTarget
          reference lam x0 p0 sourcePattern targetPattern history j).2 hjSeen)
      have hpoint : reference.targetPoint j ∈
          targetRawRemainingSetAt n lam terminal x := by
        exact href.2.2.2 j hj
      simpa [terminal, feedbackLabelRemainingSetAt] using
        (isOpen_targetRawRemainingSetAt lam terminal x).measure_pos
          (unitSquareUniform : Measure MarkedHeight)
          ⟨reference.targetPoint j, hpoint⟩

end OTSelector
