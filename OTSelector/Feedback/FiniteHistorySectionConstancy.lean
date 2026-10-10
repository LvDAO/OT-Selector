import OTSelector.Feedback.FiniteHistoryHazardSection
import OTSelector.Feedback.FiniteHistoryNextEvent
import OTSelector.Feedback.FiniteHistoryRawEvent

/-!
# Constancy and nesting of finite-history sections

This file contains the deterministic set-theoretic facts used when a finite-history cell is
integrated over its seen coordinates.  Later strict remaining rectangles are nested in earlier
ones, a next-event section is contained in the rectangle at its left endpoint, and a raw past event
is constant on such a section.  No conditional-law, compensator, certificate, `sorry`, or axiom is
introduced here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

/-! ## Nested one-label and product remaining regions -/

theorem feedbackLabelRemainingSetAt_subset
    (state : FeedbackStepState n) (lam s t : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t)
    (label : FeedbackLabel n) :
    feedbackLabelRemainingSetAt lam state t label ⊆
      feedbackLabelRemainingSetAt lam state s label := by
  cases label with
  | inl i =>
      exact sourceRawRemainingSetAt_subset state lam s t hlam0 hlamHalf hst
  | inr j =>
      exact targetRawRemainingSetAt_subset state lam s t hlam0 hlamHalf hst

theorem feedbackUnseenRectangularSetAt_subset
    (lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n))
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t) :
    feedbackUnseenRectangularSetAt lam state t S ⊆
      feedbackUnseenRectangularSetAt lam state s S := by
  intro unseen hunseen
  refine (mem_feedbackUnseenRectangularSetAt_iff lam state s S unseen).2 ?_
  intro label
  apply feedbackLabelRemainingSetAt_subset state lam s t hlam0 hlamHalf hst
    (label : FeedbackLabel n)
  exact (mem_feedbackUnseenRectangularSetAt_iff lam state t S unseen).1 hunseen label

/-! ## A later rectangle gives a coordinate cell at every earlier coordinate -/

set_option linter.unusedVariables false in
theorem historyAtCoordinate_finiteSampleSeenUnseenMerge_of_later_rectangle
    (reference : FiniteSample n) {lam x0 p0 a y : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxa : x0 ≤ a) (hay : a ≤ y)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (unseen : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (hunseen : unseen ∈ feedbackUnseenRectangularSetAt lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) y
      (feedbackTerminalLabelSet sourcePattern targetPattern history)) :
    HistoryAtCoordinate
      (finiteSampleSeenUnseenMerge
        (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
      lam x0 p0 sourcePattern targetPattern history a := by
  apply (historyAtCoordinate_finiteSampleSeenUnseenMerge_iff reference
    hlam0 hlamHalf href seen unseen hseen).2
  exact feedbackUnseenRectangularSetAt_subset lam
    (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
    a y (feedbackTerminalLabelSet sourcePattern targetPattern history)
    hlam0 hlamHalf hay hunseen

/-! ## Next-event sections are contained in the left-endpoint rectangle -/

theorem feedbackNextEventSet_subset_feedbackUnseenRectangularSetAt
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t) :
    feedbackNextEventSet lam state s t S label ⊆
      feedbackUnseenRectangularSetAt lam state s S := by
  intro unseen hnext
  refine (mem_feedbackUnseenRectangularSetAt_iff lam state s S unseen).2 ?_
  intro other
  change
    feedbackLabelFixedStateCrossing n lam state label (unseen label) ∈ Ioc s t ∧
      ∀ other' : feedbackUnseenFinset S, other' ≠ label →
        feedbackLabelFixedStateCrossing n lam state label (unseen label) <
          feedbackLabelFixedStateCrossing n lam state other' (unseen other') at hnext
  by_cases heq : other = label
  · subst other
    exact ((mem_feedbackLabelRemainingSetAt_sdiff_iff_crossing_Ioc
      state lam s t label (unseen label) hlam0 hlamHalf hst).2 hnext.1).1
  · have hcross :
        feedbackLabelFixedStateCrossing n lam state label (unseen label) ∈ Ioc s t :=
      hnext.1
    have hlt : s <
        feedbackLabelFixedStateCrossing n lam state other (unseen other) :=
      lt_trans hcross.1 (hnext.2 other heq)
    exact (mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
      state lam other (unseen other) s hlam0 hlamHalf).2 hlt

theorem feedbackNextEventSetOfLabel_subset_feedbackUnseenRectangularSetAt
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t) :
    feedbackNextEventSetOfLabel lam state s t S label ⊆
      feedbackUnseenRectangularSetAt lam state s S := by
  classical
  unfold feedbackNextEventSetOfLabel
  split_ifs with hlabel
  · exact feedbackNextEventSet_subset_feedbackUnseenRectangularSetAt
      state lam s t S ⟨label, hlabel⟩ hlam0 hlamHalf hst
  · exact Set.empty_subset _

/-! ## Raw-event constancy on a later rectangle -/

theorem rawRevealedEvent_laterRectangularSection_eq
    (reference : FiniteSample n) {lam x0 p0 a y : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxa : x0 ≤ a) (hay : a ≤ y)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (B : Set (FiniteSample n))
    (hB : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] B) :
    {unseen : feedbackUnseenFinset
        (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight |
      unseen ∈ feedbackUnseenRectangularSetAt lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) y
        (feedbackTerminalLabelSet sourcePattern targetPattern history) ∧
        finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen ∈ B} =
      if reference ∈ B then
        feedbackUnseenRectangularSetAt lam
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) y
          (feedbackTerminalLabelSet sourcePattern targetPattern history)
      else ∅ := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  change {unseen : feedbackUnseenFinset S → MarkedHeight |
      unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
        finiteSampleSeenUnseenMerge S seen unseen ∈ B} =
    if reference ∈ B then feedbackUnseenRectangularSetAt lam terminal y S else ∅
  ext unseen
  have hseen' :
      feedbackSeenTuple S reference =
        feedbackSeenTuple S (finiteSampleSeenUnseenMerge S seen unseen) := by
    rw [feedbackSeenTuple_finiteSampleSeenUnseenMerge]
    exact hseen.symm
  by_cases hunseen : unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S
  · have hcell := historyAtCoordinate_finiteSampleSeenUnseenMerge_of_later_rectangle
      reference hlam0 hlamHalf hxa hay href seen unseen hseen hunseen
    let sample := finiteSampleSeenUnseenMerge S seen unseen
    have hmem := rawRevealedEvent_mem_iff_of_historyAtCoordinate reference sample
      hlam0 hlamHalf hxa href (by simpa [sample] using hcell) hseen' B hB
    by_cases hreference : reference ∈ B
    · rw [ite_eq_left hreference]
      exact iff_of_true ⟨hunseen, hmem.mp hreference⟩ hunseen
    · rw [ite_eq_right hreference]
      exact iff_of_false (fun h ↦ hreference (hmem.mpr h.2)) (by simp)
  · by_cases hreference : reference ∈ B
    · rw [ite_eq_left hreference]
      exact iff_of_false (fun h ↦ hunseen h.1) (by simp [hunseen])
    · rw [ite_eq_right hreference]
      exact iff_of_false (fun h ↦ hunseen h.1) (by simp)

end OTSelector
