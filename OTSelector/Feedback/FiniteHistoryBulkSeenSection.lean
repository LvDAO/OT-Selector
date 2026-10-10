import OTSelector.Feedback.FiniteHistoryBranchAtSection
import OTSelector.Feedback.FiniteHistoryBulkBranchSetIntegral
import OTSelector.Feedback.FiniteHistorySeenState

/-!
# Event/rate equality for every fixed seen tuple

The seen tuple remains a genuine outer integration variable.  A section with no realized history
branch contributes zero.  On a nonempty section, a canonical representative fixes the scheduled
state and the fixed-branch set-integral identity applies.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

private theorem historyBranch_of_mem_feedbackBulkNextEventSetOfLabel
    (reference : FiniteSample n) {B lam x0 p0 s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (unseen : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)
    (label : FeedbackLabel n)
    (hmem : unseen ∈ feedbackBulkNextEventSetOfLabel B lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
      s t (feedbackTerminalLabelSet sourcePattern targetPattern history) label) :
    HistoryBranch
      (finiteSampleSeenUnseenMerge
        (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
      lam x0 p0 sourcePattern targetPattern history := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  have hrect : unseen ∈ feedbackUnseenRectangularSetAt lam terminal terminal.x S := by
    unfold feedbackBulkNextEventSetOfLabel at hmem
    split at hmem
    · exact hmem.1.1
    · simp at hmem
  have hAt :=
    (historyAtCoordinate_finiteSampleSeenUnseenMerge_iff_of_historyBranch
      reference hlam0 hlamHalf href seen unseen hseen le_rfl).2 hrect
  exact hAt.1

theorem sourceBulk_seenSection_eventMass_eq_rateMass
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hxr : x0 ≤ r) (hrs : r ≤ s)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := feedbackScheduledStateOfSeen lam x0 p0
      sourcePattern targetPattern history seen
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history ∧
              unseen ∈ feedbackBulkNextEventSetOfLabel
                width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
      ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
          (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history y ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
          (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam terminal y) unseen
        ∂(feedbackUnseenTupleLaw S) ∂volume := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := feedbackScheduledStateOfSeen lam x0 p0
    sourcePattern targetPattern history seen
  by_cases hex : ∃ unseen : feedbackUnseenFinset S → MarkedHeight,
      HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
        lam x0 p0 sourcePattern targetPattern history
  · obtain ⟨unseen₀, href⟩ := hex
    let reference := finiteSampleSeenUnseenMerge S seen unseen₀
    have hseenRef : seen = feedbackSeenTuple S reference := by
      simp [reference]
    have hstate : reference.scheduledState lam x0 p0
        sourcePattern targetPattern history = terminal := by
      simpa [reference, S, terminal] using
        (scheduledState_eq_feedbackScheduledStateOfSeen_of_finiteSampleSeenUnseenMerge
          S seen unseen₀ lam x0 p0 sourcePattern targetPattern history rfl)
    have hra : r ≤ feedbackBranchBulkStart width lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s := by
      rw [hstate]
      exact hrs.trans (feedbackBranchBulkStart_ge_s width lam terminal s)
    have hmain :=
      sum_sourceBulkNextEvent_eq_setIntegral_unseenRate_of_historyBranch
        reference (width := width) (r := r) (s := s) (t := t)
        hlam0 hlamHalf (by simpa [reference, S] using href)
        seen hseenRef hxr hra E hE hn hwidth
    have heventSection (label : FeedbackLabel n) :
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history ∧
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} := by
      ext unseen
      constructor
      · exact fun h ↦ h.2
      · intro h
        refine ⟨?_, h⟩
        apply historyBranch_of_mem_feedbackBulkNextEventSetOfLabel
          reference hlam0 hlamHalf (by simpa [reference, S] using href)
            seen hseenRef unseen label
        simpa [hstate] using h.1
    have hrateSection (y : ℝ)
        (hy : y ∈ Ioc (feedbackBranchBulkStart width lam terminal s)
          (feedbackBranchBulkStop width lam terminal t)) :
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history y ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} := by
      have hterminaly :
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ y := by
        rw [hstate]
        exact (feedbackBranchBulkStart_ge_state width lam terminal s).trans hy.1.le
      ext unseen
      have hiff :=
        historyAtCoordinate_finiteSampleSeenUnseenMerge_iff_of_historyBranch
          reference hlam0 hlamHalf (by simpa [reference, S] using href)
            seen unseen hseenRef hterminaly
      have hiff' :
          HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history y ↔
            unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S := by
        simpa [S, hstate] using hiff
      exact and_congr hiff' Iff.rfl
    dsimp only at hmain ⊢
    calc
      ∑ label ∈ feedbackUnseenSourceLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                  lam x0 p0 sourcePattern targetPattern history ∧
                unseen ∈ feedbackBulkNextEventSetOfLabel
                  width lam terminal s t S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
          ∑ label ∈ feedbackUnseenSourceLabels S,
            (feedbackUnseenTupleLaw S).real
              {unseen : feedbackUnseenFinset S → MarkedHeight |
                unseen ∈ feedbackBulkNextEventSetOfLabel
                    width lam terminal s t S label ∧
                  finiteSampleSeenUnseenMerge S seen unseen ∈ E} := by
            apply Finset.sum_congr rfl
            intro label hlabel
            rw [heventSection label]
      _ = ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
            (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam terminal y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume := by
            simpa [S, hstate] using hmain
      _ = ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
            (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam terminal y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioc
            intro y hy
            dsimp only
            rw [hrateSection y hy]
  · have hnoBranch (unseen : feedbackUnseenFinset S → MarkedHeight) :
        ¬HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
          lam x0 p0 sourcePattern targetPattern history := by
      exact fun h ↦ hex ⟨unseen, h⟩
    dsimp only at ⊢
    calc
      ∑ label ∈ feedbackUnseenSourceLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                  lam x0 p0 sourcePattern targetPattern history ∧
                unseen ∈ feedbackBulkNextEventSetOfLabel
                  width lam terminal s t S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E} = 0 := by
          apply Finset.sum_eq_zero
          intro label hlabel
          have hset :
              {unseen : feedbackUnseenFinset S → MarkedHeight |
                HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                    lam x0 p0 sourcePattern targetPattern history ∧
                  unseen ∈ feedbackBulkNextEventSetOfLabel
                    width lam terminal s t S label ∧
                  finiteSampleSeenUnseenMerge S seen unseen ∈ E} = ∅ := by
            ext unseen
            simp [hnoBranch unseen]
          rw [hset]
          simp
      _ = ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
            (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.sourceUnclippedStateRateAt lam terminal y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume := by
            symm
            apply integral_eq_zero_of_ae
            filter_upwards [] with y
            apply integral_eq_zero_of_ae
            filter_upwards [] with unseen
            have hnoAt : ¬HistoryAtCoordinate
                (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y :=
              fun hAt ↦ hnoBranch unseen hAt.1
            simp [hnoAt]

theorem targetBulk_seenSection_eventMass_eq_rateMass
    {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hxr : x0 ≤ r) (hrs : r ≤ s)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hn : 0 < n) (hwidth : 0 < width) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := feedbackScheduledStateOfSeen lam x0 p0
      sourcePattern targetPattern history seen
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (feedbackUnseenTupleLaw S).real
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history ∧
              unseen ∈ feedbackBulkNextEventSetOfLabel
                width lam terminal s t S label ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
      ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
          (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history y ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
          (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam terminal y) unseen
        ∂(feedbackUnseenTupleLaw S) ∂volume := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := feedbackScheduledStateOfSeen lam x0 p0
    sourcePattern targetPattern history seen
  by_cases hex : ∃ unseen : feedbackUnseenFinset S → MarkedHeight,
      HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
        lam x0 p0 sourcePattern targetPattern history
  · obtain ⟨unseen₀, href⟩ := hex
    let reference := finiteSampleSeenUnseenMerge S seen unseen₀
    have hseenRef : seen = feedbackSeenTuple S reference := by
      simp [reference]
    have hstate : reference.scheduledState lam x0 p0
        sourcePattern targetPattern history = terminal := by
      simpa [reference, S, terminal] using
        (scheduledState_eq_feedbackScheduledStateOfSeen_of_finiteSampleSeenUnseenMerge
          S seen unseen₀ lam x0 p0 sourcePattern targetPattern history rfl)
    have hra : r ≤ feedbackBranchBulkStart width lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s := by
      rw [hstate]
      exact hrs.trans (feedbackBranchBulkStart_ge_s width lam terminal s)
    have hmain :=
      sum_targetBulkNextEvent_eq_setIntegral_unseenRate_of_historyBranch
        reference (width := width) (r := r) (s := s) (t := t)
        hlam0 hlamHalf (by simpa [reference, S] using href)
        seen hseenRef hxr hra E hE hn hwidth
    have heventSection (label : FeedbackLabel n) :
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history ∧
            unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          unseen ∈ feedbackBulkNextEventSetOfLabel
              width lam terminal s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} := by
      ext unseen
      constructor
      · exact fun h ↦ h.2
      · intro h
        refine ⟨?_, h⟩
        apply historyBranch_of_mem_feedbackBulkNextEventSetOfLabel
          reference hlam0 hlamHalf (by simpa [reference, S] using href)
            seen hseenRef unseen label
        simpa [hstate] using h.1
    have hrateSection (y : ℝ)
        (hy : y ∈ Ioc (feedbackBranchBulkStart width lam terminal s)
          (feedbackBranchBulkStop width lam terminal t)) :
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history y ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} := by
      have hterminaly :
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ y := by
        rw [hstate]
        exact (feedbackBranchBulkStart_ge_state width lam terminal s).trans hy.1.le
      ext unseen
      have hiff :=
        historyAtCoordinate_finiteSampleSeenUnseenMerge_iff_of_historyBranch
          reference hlam0 hlamHalf (by simpa [reference, S] using href)
            seen unseen hseenRef hterminaly
      have hiff' :
          HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history y ↔
            unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S := by
        simpa [S, hstate] using hiff
      exact and_congr hiff' Iff.rfl
    dsimp only at hmain ⊢
    calc
      ∑ label ∈ feedbackUnseenTargetLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                  lam x0 p0 sourcePattern targetPattern history ∧
                unseen ∈ feedbackBulkNextEventSetOfLabel
                  width lam terminal s t S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
          ∑ label ∈ feedbackUnseenTargetLabels S,
            (feedbackUnseenTupleLaw S).real
              {unseen : feedbackUnseenFinset S → MarkedHeight |
                unseen ∈ feedbackBulkNextEventSetOfLabel
                    width lam terminal s t S label ∧
                  finiteSampleSeenUnseenMerge S seen unseen ∈ E} := by
            apply Finset.sum_congr rfl
            intro label hlabel
            rw [heventSection label]
      _ = ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
            (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            unseen ∈ feedbackUnseenRectangularSetAt lam terminal y S ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam terminal y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume := by
            simpa [S, hstate] using hmain
      _ = ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
            (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam terminal y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume := by
            apply setIntegral_congr_fun measurableSet_Ioc
            intro y hy
            dsimp only
            rw [hrateSection y hy]
  · have hnoBranch (unseen : feedbackUnseenFinset S → MarkedHeight) :
        ¬HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
          lam x0 p0 sourcePattern targetPattern history := by
      exact fun h ↦ hex ⟨unseen, h⟩
    dsimp only at ⊢
    calc
      ∑ label ∈ feedbackUnseenTargetLabels S,
          (feedbackUnseenTupleLaw S).real
            {unseen : feedbackUnseenFinset S → MarkedHeight |
              HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                  lam x0 p0 sourcePattern targetPattern history ∧
                unseen ∈ feedbackBulkNextEventSetOfLabel
                  width lam terminal s t S label ∧
                finiteSampleSeenUnseenMerge S seen unseen ∈ E} = 0 := by
          apply Finset.sum_eq_zero
          intro label hlabel
          have hset :
              {unseen : feedbackUnseenFinset S → MarkedHeight |
                HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
                    lam x0 p0 sourcePattern targetPattern history ∧
                  unseen ∈ feedbackBulkNextEventSetOfLabel
                    width lam terminal s t S label ∧
                  finiteSampleSeenUnseenMerge S seen unseen ∈ E} = ∅ := by
            ext unseen
            simp [hnoBranch unseen]
          rw [hset]
          simp
      _ = ∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
            (feedbackBranchBulkStop width lam terminal t), ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
            (fun _ ↦ FeedbackStepState.targetUnclippedStateRateAt lam terminal y) unseen
          ∂(feedbackUnseenTupleLaw S) ∂volume := by
            symm
            apply integral_eq_zero_of_ae
            filter_upwards [] with y
            apply integral_eq_zero_of_ae
            filter_upwards [] with unseen
            have hnoAt : ¬HistoryAtCoordinate
                (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 sourcePattern targetPattern history y :=
              fun hAt ↦ hnoBranch unseen hAt.1
            simp [hnoAt]

end OTSelector
