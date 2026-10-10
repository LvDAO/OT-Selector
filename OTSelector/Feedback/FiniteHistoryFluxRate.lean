import OTSelector.Feedback.FiniteHistorySurvivalFlux
import OTSelector.Feedback.FeedbackBulkMask
import OTSelector.Feedback.FiniteHistorySection

/-!
# Terminal finite-history flux/rate bridge

This file identifies the finite-product survival flux with the corresponding unclipped
fixed-history state rate.  The only combinatorial input is that the unseen source/target
labels are precisely the complements of the terminal seen source/target labels.
-/

open MeasureTheory Set
open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

private theorem feedbackUnseenSourceLabels_eq_image_compl
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)} :
    feedbackUnseenSourceLabels
        (feedbackTerminalLabelSet sourcePattern targetPattern history) =
      (Finset.univ \ (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource).image
        (fun i : Fin n => (Sum.inl i : FeedbackLabel n)) := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ terminal.seenSource := by
    intro i
    exact mem_feedbackTerminalLabelSet_inl_iff_seenSource
      sample lam x0 p0 sourcePattern targetPattern history i
  ext label
  cases label with
  | inl i =>
      simp [feedbackUnseenSourceLabels, feedbackUnseenFinset,
        FiniteSample.scheduledState_seenSource]
  | inr j =>
      simp [feedbackUnseenSourceLabels, feedbackUnseenFinset]

private theorem feedbackUnseenTargetLabels_eq_image_compl
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)} :
    feedbackUnseenTargetLabels
        (feedbackTerminalLabelSet sourcePattern targetPattern history) =
      (Finset.univ \ (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget).image
        (fun j : Fin n => (Sum.inr j : FeedbackLabel n)) := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ terminal.seenTarget := by
    intro j
    exact mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      sample lam x0 p0 sourcePattern targetPattern history j
  ext label
  cases label with
  | inl i =>
      simp [feedbackUnseenTargetLabels, feedbackUnseenFinset]
  | inr j =>
      simp [feedbackUnseenTargetLabels, feedbackUnseenFinset,
        FiniteSample.scheduledState_seenTarget]

theorem feedbackUnseenSourceCount_eq_card_sub
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)} :
    feedbackUnseenSourceCount
        (feedbackTerminalLabelSet sourcePattern targetPattern history) =
      n - (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource.card := by
  classical
  rw [show feedbackUnseenSourceCount
      (feedbackTerminalLabelSet sourcePattern targetPattern history) =
        (feedbackUnseenSourceLabels
          (feedbackTerminalLabelSet sourcePattern targetPattern history)).card by rfl]
  rw [feedbackUnseenSourceLabels_eq_image_compl (sample := sample)
    (lam := lam) (x0 := x0) (p0 := p0)]
  rw [Finset.card_image_of_injective _ Sum.inl_injective]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

theorem feedbackUnseenTargetCount_eq_card_sub
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)} :
    feedbackUnseenTargetCount
        (feedbackTerminalLabelSet sourcePattern targetPattern history) =
      n - (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget.card := by
  classical
  rw [show feedbackUnseenTargetCount
      (feedbackTerminalLabelSet sourcePattern targetPattern history) =
        (feedbackUnseenTargetLabels
          (feedbackTerminalLabelSet sourcePattern targetPattern history)).card by rfl]
  rw [feedbackUnseenTargetLabels_eq_image_compl (sample := sample)
    (lam := lam) (x0 := x0) (p0 := p0)]
  rw [Finset.card_image_of_injective _ Sum.inr_injective]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

theorem feedbackSourceSurvivalLossFluxAt_eq_stateRate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hn : 0 < n)
    (hsource : 0 < feedbackSourceRemainingRealMassAt lam
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x) :
    feedbackSourceSurvivalLossFluxAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x
        (feedbackTerminalLabelSet sourcePattern targetPattern history) =
      feedbackUnseenSurvivalMassAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x
        (feedbackTerminalLabelSet sourcePattern targetPattern history) *
        FeedbackStepState.sourceUnclippedStateRateAt lam
          (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x := by
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  have hflux := feedbackSourceSurvivalFluxAt_eq hn lam terminal x S hsource
  have hcount := feedbackUnseenSourceCount_eq_card_sub sample (lam := lam) (x0 := x0)
    (p0 := p0) (sourcePattern := sourcePattern) (targetPattern := targetPattern)
    (history := history)
  have hcard_le :
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource.card ≤ n := by
    simpa using Finset.card_le_univ
      ((sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource)
  dsimp [terminal, S] at hflux ⊢
  rw [feedbackSourceSurvivalLossFluxAt, hflux]
  rw [hcount]
  rw [Nat.cast_sub hcard_le]
  simp only [FeedbackStepState.sourceUnclippedStateRateAt,
    feedbackSourceRemainingAreaAt]
  ring

theorem feedbackTargetSurvivalLossFluxAt_eq_stateRate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hn : 0 < n)
    (htarget : 0 < feedbackTargetRemainingRealMassAt lam
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x) :
    feedbackTargetSurvivalLossFluxAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x
        (feedbackTerminalLabelSet sourcePattern targetPattern history) =
      feedbackUnseenSurvivalMassAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x
        (feedbackTerminalLabelSet sourcePattern targetPattern history) *
        FeedbackStepState.targetUnclippedStateRateAt lam
          (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x := by
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  have hflux := feedbackTargetSurvivalFluxAt_eq hn lam terminal x S htarget
  have hcount := feedbackUnseenTargetCount_eq_card_sub sample (lam := lam) (x0 := x0)
    (p0 := p0) (sourcePattern := sourcePattern) (targetPattern := targetPattern)
    (history := history)
  have hcard_le :
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget.card ≤ n := by
    simpa using Finset.card_le_univ
      ((sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget)
  dsimp [terminal, S] at hflux ⊢
  rw [feedbackTargetSurvivalLossFluxAt, hflux]
  rw [hcount]
  rw [Nat.cast_sub hcard_le]
  simp only [FeedbackStepState.targetUnclippedStateRateAt,
    feedbackTargetRemainingAreaAt]
  ring

end OTSelector
