import OTSelector.Feedback.FiniteHistoryBranchFubini
import OTSelector.Feedback.FiniteHistoryBulkJointMeasurable
import OTSelector.Feedback.FiniteHistorySeenState
import OTSelector.Probability.ProductRealSection

/-!
# Product-law transport for one bulk next-event branch

For a fixed finite history and ambient next label, this file identifies the relevant event in
seen/unseen product coordinates, proves its joint measurability, and transports its real mass back
to the canonical finite-sample law.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

/-- One fixed history, bulk next-label event, and raw revealed event in seen/unseen coordinates. -/
def historyBulkNextEventProductSet
    (width lam x0 p0 s t : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (E : Set (FiniteSample n)) (label : FeedbackLabel n) :
    Set ((feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight) ×
      (feedbackUnseenFinset
        (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)) :=
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  historyBranchProductSet lam x0 p0 sourcePattern targetPattern history ∩
    ({parts |
      parts.2 ∈ feedbackBulkNextEventSetOfLabel width lam
        (feedbackScheduledStateOfSeen lam x0 p0
          sourcePattern targetPattern history parts.1) s t S label} ∩
      {parts | finiteSampleSeenUnseenMerge S parts.1 parts.2 ∈ E})

theorem measurableSet_historyBulkNextEventProductSet
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
    MeasurableSet (historyBulkNextEventProductSet width lam x0 p0 s t
      sourcePattern targetPattern history E label) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  have hbranch : MeasurableSet
      (historyBranchProductSet lam x0 p0 sourcePattern targetPattern history) :=
    measurableSet_historyBranchProductSet lam x0 p0 sourcePattern targetPattern history
  have hstate : Measurable (fun parts : (S → MarkedHeight) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦
      feedbackScheduledStateOfSeen lam x0 p0
        sourcePattern targetPattern history parts.1) :=
    (measurable_feedbackScheduledStateOfSeen lam x0 p0
      sourcePattern targetPattern history).comp measurable_fst
  have hpair : Measurable (fun parts : (S → MarkedHeight) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦
      (feedbackScheduledStateOfSeen lam x0 p0
        sourcePattern targetPattern history parts.1, parts.2)) :=
    hstate.prodMk measurable_snd
  have hbulk : MeasurableSet {parts : (S → MarkedHeight) ×
      (feedbackUnseenFinset S → MarkedHeight) |
      parts.2 ∈ feedbackBulkNextEventSetOfLabel width lam
        (feedbackScheduledStateOfSeen lam x0 p0
          sourcePattern targetPattern history parts.1) s t S label} :=
    (measurableSet_feedbackBulkNextEventSetOfLabel_joint
      width lam s t S label hlam0 hlamHalf).preimage hpair
  have hEambient : MeasurableSet E :=
    (FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le
      ⟨r - x0, sub_nonneg.mpr hxr⟩ E hE
  have hmerge : Measurable (fun parts : (S → MarkedHeight) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦
      finiteSampleSeenUnseenMerge S parts.1 parts.2) :=
    measurable_finiteSampleSeenUnseenMerge S
  have hraw : MeasurableSet {parts : (S → MarkedHeight) ×
      (feedbackUnseenFinset S → MarkedHeight) |
      finiteSampleSeenUnseenMerge S parts.1 parts.2 ∈ E} :=
    hEambient.preimage hmerge
  change MeasurableSet
    (historyBranchProductSet lam x0 p0 sourcePattern targetPattern history ∩
      ({parts : (S → MarkedHeight) ×
        (feedbackUnseenFinset S → MarkedHeight) |
        parts.2 ∈ feedbackBulkNextEventSetOfLabel width lam
          (feedbackScheduledStateOfSeen lam x0 p0
            sourcePattern targetPattern history parts.1) s t S label} ∩
        {parts : (S → MarkedHeight) ×
          (feedbackUnseenFinset S → MarkedHeight) |
          finiteSampleSeenUnseenMerge S parts.1 parts.2 ∈ E}))
  exact hbranch.inter (hbulk.inter hraw)

theorem scheduledState_eq_feedbackScheduledStateOfSeen_feedbackSeenTuple
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    sample.scheduledState lam x0 p0 sourcePattern targetPattern history =
      feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history
        (feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  have h :=
    scheduledState_eq_feedbackScheduledStateOfSeen_of_finiteSampleSeenUnseenMerge
      S (feedbackSeenTuple S sample) (feedbackUnseenTuple S sample)
      lam x0 p0 sourcePattern targetPattern history rfl
  simpa [S, finiteSampleSeenUnseenMerge_split] using h

theorem historyBulkNextEventProductSet_preimage_eq
    (width lam x0 p0 s t : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (E : Set (FiniteSample n)) (label : FeedbackLabel n) :
    (fun sample : FiniteSample n ↦
      (feedbackSeenTuple
        (feedbackTerminalLabelSet sourcePattern targetPattern history) sample,
       feedbackUnseenTuple
        (feedbackTerminalLabelSet sourcePattern targetPattern history) sample)) ⁻¹'
      historyBulkNextEventProductSet width lam x0 p0 s t
        sourcePattern targetPattern history E label =
      {sample : FiniteSample n |
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
          feedbackUnseenTuple
              (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∈
            feedbackBulkNextEventSetOfLabel width lam
              (sample.scheduledState lam x0 p0
                sourcePattern targetPattern history) s t
              (feedbackTerminalLabelSet sourcePattern targetPattern history) label ∧
          sample ∈ E} := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  ext sample
  have hstate := scheduledState_eq_feedbackScheduledStateOfSeen_feedbackSeenTuple
    sample lam x0 p0 sourcePattern targetPattern history
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  change
    ((feedbackSeenTuple S sample, feedbackUnseenTuple S sample) ∈
      historyBulkNextEventProductSet width lam x0 p0 s t
        sourcePattern targetPattern history E label) ↔ _
  simp [historyBulkNextEventProductSet, historyBranchProductSet, S,
    finiteSampleSeenUnseenMerge_split, hstate]

theorem finiteSampleLaw_real_historyBulkNextEvent_eq_seenIntegral
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
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample : FiniteSample n |
          HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
            feedbackUnseenTuple S sample ∈
              feedbackBulkNextEventSetOfLabel width lam
                (sample.scheduledState lam x0 p0
                  sourcePattern targetPattern history) s t S label ∧
            sample ∈ E} =
      ∫ seen, (feedbackUnseenTupleLaw S).real
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history ∧
            unseen ∈ feedbackBulkNextEventSetOfLabel width lam
              (feedbackScheduledStateOfSeen lam x0 p0
                sourcePattern targetPattern history seen) s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E}
        ∂(feedbackTupleLaw S) := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let sampleMap : FiniteSample n →
      (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) :=
    fun sample ↦ (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)
  let C := historyBulkNextEventProductSet width lam x0 p0 s t
    sourcePattern targetPattern history E label
  have hC : MeasurableSet C := by
    simpa [C] using measurableSet_historyBulkNextEventProductSet
      hlam0 hlamHalf sourcePattern targetPattern history hxr E hE label
  have hmap : Measure.map sampleMap
      (finiteSampleLaw n : Measure (FiniteSample n)) =
      (feedbackTupleLaw S).prod (feedbackUnseenTupleLaw S) := by
    simpa [sampleMap, feedbackTupleLaw, feedbackUnseenTupleLaw, S] using
      finiteSampleLaw_map_feedbackSeenUnseenTuple (n := n) S
  let : IsProbabilityMeasure (feedbackTupleLaw S) := by
    rw [feedbackTupleLaw]
    infer_instance
  let : IsProbabilityMeasure (feedbackUnseenTupleLaw S) := by
    rw [feedbackUnseenTupleLaw]
    infer_instance
  have htransport := measureReal_preimage_eq_integral_section
    (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (νA := feedbackTupleLaw S) (νB := feedbackUnseenTupleLaw S)
    (f := sampleMap)
    ((measurable_feedbackSeenTuple S).prodMk (measurable_feedbackUnseenTuple S))
    hmap hC
  have hpreimage := historyBulkNextEventProductSet_preimage_eq
    (n := n) width lam x0 p0 s t sourcePattern targetPattern history E label
  change sampleMap ⁻¹' C = _ at hpreimage
  rw [hpreimage] at htransport
  simpa [C, historyBulkNextEventProductSet, historyBranchProductSet, S] using htransport

end OTSelector
