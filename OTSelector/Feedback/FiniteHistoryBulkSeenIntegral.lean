import OTSelector.Feedback.FiniteHistoryBulkSeenSection

/-!
# Outer seen-tuple integral for event/rate equality

The fixed-seen event/rate identities remain valid after integrating the seen tuple against its
product law.  No integrability hypothesis is needed: the two outer integrands are pointwise equal.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

theorem sourceBulk_seenIntegral_eventMass_eq_rateMass
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hxr : x0 ≤ r) (hrs : r ≤ s)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    (∫ seen, ∑ label ∈ feedbackUnseenSourceLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history ∧
              unseen ∈ feedbackBulkNextEventSetOfLabel
                width lam (feedbackScheduledStateOfSeen lam x0 p0
                  sourcePattern targetPattern history seen) s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}
      ∂(feedbackTupleLaw S)) =
      ∫ seen, ∫ y in Ioc (feedbackBranchBulkStart width lam
          (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) s)
          (feedbackBranchBulkStop width lam
            (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) t),
        ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam
              (feedbackScheduledStateOfSeen lam x0 p0
                sourcePattern targetPattern history seen) y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume
        ∂(feedbackTupleLaw S) := by
  classical
  dsimp only
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun seen ↦
    sourceBulk_seenSection_eventMass_eq_rateMass
      hlam0 hlamHalf seen hxr hrs E hE hn hwidth

theorem targetBulk_seenIntegral_eventMass_eq_rateMass
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hxr : x0 ≤ r) (hrs : r ≤ s)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    (∫ seen, ∑ label ∈ feedbackUnseenTargetLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history ∧
              unseen ∈ feedbackBulkNextEventSetOfLabel
                width lam (feedbackScheduledStateOfSeen lam x0 p0
                  sourcePattern targetPattern history seen) s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}
      ∂(feedbackTupleLaw S)) =
      ∫ seen, ∫ y in Ioc (feedbackBranchBulkStart width lam
          (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) s)
          (feedbackBranchBulkStop width lam
            (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) t),
        ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam
              (feedbackScheduledStateOfSeen lam x0 p0
                sourcePattern targetPattern history seen) y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume
        ∂(feedbackTupleLaw S) := by
  classical
  dsimp only
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun seen ↦
    targetBulk_seenSection_eventMass_eq_rateMass
      hlam0 hlamHalf seen hxr hrs E hE hn hwidth

end OTSelector
