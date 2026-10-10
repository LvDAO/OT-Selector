import OTSelector.Feedback.FiniteHistoryBulkAllLabel
import OTSelector.Feedback.FiniteHistoryBulkProductTransport

/-!
# Measurability of ambient-label bulk events for one finite history

The all-label event identities use the same single-label events as the product-law transport.
This file records their measurability under the canonical finite-sample law by pulling back the
already measurable seen/unseen product event along the measurable split map.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

/-- A fixed-history bulk next-event set is measurable for any ambient feedback label. -/
theorem measurableSet_finiteSample_historyBulkNextEvent
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hxr : x0 ≤ r)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (label : FeedbackLabel n) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    MeasurableSet {sample : FiniteSample n |
      HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
        feedbackUnseenTuple S sample ∈
          feedbackBulkNextEventSetOfLabel width lam
            (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
            s t S label ∧
        sample ∈ E} := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let sampleMap : FiniteSample n →
      (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) :=
    fun sample ↦ (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)
  have hproduct : MeasurableSet
      (historyBulkNextEventProductSet width lam x0 p0 s t
        sourcePattern targetPattern history E label) :=
    measurableSet_historyBulkNextEventProductSet
      hlam0 hlamHalf sourcePattern targetPattern history hxr E hE label
  have hmap : Measurable sampleMap :=
    (measurable_feedbackSeenTuple S).prodMk (measurable_feedbackUnseenTuple S)
  have hpreimage := historyBulkNextEventProductSet_preimage_eq
    (n := n) width lam x0 p0 s t sourcePattern targetPattern history E label
  change sampleMap ⁻¹'
      historyBulkNextEventProductSet width lam x0 p0 s t
        sourcePattern targetPattern history E label = _ at hpreimage
  have hpullback := hproduct.preimage hmap
  rw [hpreimage] at hpullback
  simpa [S] using hpullback

/-- The source-label event appearing in the all-label source sum is measurable. -/
theorem measurableSet_finiteSample_sourceBulk_history_allLabel_event
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hxr : x0 ≤ r)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (i : Fin n) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    MeasurableSet {sample : FiniteSample n |
      HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
        feedbackUnseenTuple S sample ∈
          feedbackBulkNextEventSetOfLabel width lam
            (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
            s t S (Sum.inl i) ∧
        sample ∈ E} := by
  exact measurableSet_finiteSample_historyBulkNextEvent
    hlam0 hlamHalf sourcePattern targetPattern history hxr E hE (Sum.inl i)

/-- The target-label event appearing in the all-label target sum is measurable. -/
theorem measurableSet_finiteSample_targetBulk_history_allLabel_event
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hxr : x0 ≤ r)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (j : Fin n) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    MeasurableSet {sample : FiniteSample n |
      HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
        feedbackUnseenTuple S sample ∈
          feedbackBulkNextEventSetOfLabel width lam
            (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
            s t S (Sum.inr j) ∧
        sample ∈ E} := by
  exact measurableSet_finiteSample_historyBulkNextEvent
    hlam0 hlamHalf sourcePattern targetPattern history hxr E hE (Sum.inr j)

end OTSelector
