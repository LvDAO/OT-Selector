import OTSelector.Feedback.FiniteHistoryBulkNextEvent
import OTSelector.Feedback.FiniteHistorySectionFlux

/-!
# Raw-event flux on a bulk-restricted fixed-history section

The endpoint-null reduction from `FiniteHistoryBulkNextEvent` is stable under intersection with
an arbitrary raw event.  Combining it with the fixed-section next-event identity gives the exact
source and target survival-loss flux on the clipped branch interval.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

theorem sum_feedbackUnseenTupleLaw_real_sourceBulkNextEventSet_inter_rawEvent_eq_flux
    (reference : FiniteSample n) {width lam x0 p0 s t a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (ha : a = feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hb : b = feedbackBranchBulkStop width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (hxa : x0 ≤ a) (hab : a ≤ b)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
      if reference ∈ E then
        ∫ y in a..b, feedbackSourceSurvivalLossFluxAt lam terminal y S
      else 0 := by
  classical
  subst a
  subst b
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  dsimp only
  have hbase :=
    sum_feedbackUnseenTupleLaw_real_sourceNextEventSet_inter_rawEvent_eq_flux
      reference hlam0 hlamHalf hxa hab href seen hseen E hE hn
        (fun y hy ↦
          feedbackBoundary_bounds_on_branchBulkInterval
            width lam terminal s t y hwidth hy)
        (fun y hy ↦
          feedbackSourceRemainingRealMassAt_pos_on_branchBulkInterval
            width lam terminal s t y hn hwidth hy)
  calc
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
        ∑ label ∈ feedbackUnseenSourceLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              unseen ∈ feedbackNextEventSetOfLabel lam terminal
                (feedbackBranchBulkStart width lam terminal s)
                (feedbackBranchBulkStop width lam terminal t) S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E} := by
      apply Finset.sum_congr rfl
      intro label _hlabel
      let P : Set (feedbackUnseenFinset S → MarkedHeight) :=
        {unseen | finiteSampleSeenUnseenMerge S seen unseen ∈ E}
      have hnext :=
        feedbackBulkNextEventSetOfLabel_ae_eq_branchBulkNextEventSetOfLabel
          width lam terminal s t S label hn hwidth hlam0 hlamHalf hab
      have hinter := ae_eq_set_inter hnext (ae_eq_refl P)
      unfold Measure.real
      apply congrArg ENNReal.toReal
      apply measure_congr
      have hleft :
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
            feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∩ P := by
        ext unseen
        rfl
      have hright :
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackNextEventSetOfLabel lam terminal
              (feedbackBranchBulkStart width lam terminal s)
              (feedbackBranchBulkStop width lam terminal t) S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
            feedbackNextEventSetOfLabel lam terminal
              (feedbackBranchBulkStart width lam terminal s)
              (feedbackBranchBulkStop width lam terminal t) S label ∩ P := by
        ext unseen
        rfl
      rw [hleft, hright]
      exact hinter
    _ = if reference ∈ E then
          ∫ y in feedbackBranchBulkStart width lam terminal s..
            feedbackBranchBulkStop width lam terminal t,
              feedbackSourceSurvivalLossFluxAt lam terminal y S
        else 0 := hbase

theorem sum_feedbackUnseenTupleLaw_real_targetBulkNextEventSet_inter_rawEvent_eq_flux
    (reference : FiniteSample n) {width lam x0 p0 s t a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (ha : a = feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hb : b = feedbackBranchBulkStop width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (hxa : x0 ≤ a) (hab : a ≤ b)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨a - x0, sub_nonneg.mpr hxa⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
      if reference ∈ E then
        ∫ y in a..b, feedbackTargetSurvivalLossFluxAt lam terminal y S
      else 0 := by
  classical
  subst a
  subst b
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  dsimp only
  have hbase :=
    sum_feedbackUnseenTupleLaw_real_targetNextEventSet_inter_rawEvent_eq_flux
      reference hlam0 hlamHalf hxa hab href seen hseen E hE hn
        (fun y hy ↦
          feedbackBoundary_bounds_on_branchBulkInterval
            width lam terminal s t y hwidth hy)
        (fun y hy ↦
          feedbackTargetRemainingRealMassAt_pos_on_branchBulkInterval
            width lam terminal s t y hn hwidth hy)
  calc
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
        ∑ label ∈ feedbackUnseenTargetLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              unseen ∈ feedbackNextEventSetOfLabel lam terminal
                (feedbackBranchBulkStart width lam terminal s)
                (feedbackBranchBulkStop width lam terminal t) S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E} := by
      apply Finset.sum_congr rfl
      intro label _hlabel
      let P : Set (feedbackUnseenFinset S → MarkedHeight) :=
        {unseen | finiteSampleSeenUnseenMerge S seen unseen ∈ E}
      have hnext :=
        feedbackBulkNextEventSetOfLabel_ae_eq_branchBulkNextEventSetOfLabel
          width lam terminal s t S label hn hwidth hlam0 hlamHalf hab
      have hinter := ae_eq_set_inter hnext (ae_eq_refl P)
      unfold Measure.real
      apply congrArg ENNReal.toReal
      apply measure_congr
      have hleft :
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
            feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∩ P := by
        ext unseen
        rfl
      have hright :
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackNextEventSetOfLabel lam terminal
              (feedbackBranchBulkStart width lam terminal s)
              (feedbackBranchBulkStop width lam terminal t) S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
            feedbackNextEventSetOfLabel lam terminal
              (feedbackBranchBulkStart width lam terminal s)
              (feedbackBranchBulkStop width lam terminal t) S label ∩ P := by
        ext unseen
        rfl
      rw [hleft, hright]
      exact hinter
    _ = if reference ∈ E then
          ∫ y in feedbackBranchBulkStart width lam terminal s..
            feedbackBranchBulkStop width lam terminal t,
              feedbackTargetSurvivalLossFluxAt lam terminal y S
        else 0 := hbase

end OTSelector
