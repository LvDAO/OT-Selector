import OTSelector.Feedback.FeedbackMarkedMean
import OTSelector.Feedback.FiniteHistoryBulkSeenIntegral
import OTSelector.Feedback.FiniteHistoryBulkProductTransport

/-!
# Centered marks on actual finite-history raw rectangles

The actual next-mark law centers each mark by its slope-dependent mean. Raw past events are
constant on a fixed next-event section, so the centered identity survives the past test.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

/-- A raw event known at the left endpoint preserves the zero mean of the selected centered mark. -/
theorem centered_mark_nextEvent_raw_section_integral_eq_zero
    (reference : FiniteSample n) {lam x0 p0 a b : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hxa : x0 ≤ a) (hab : a ≤ b)
    {sourcePattern targetPattern : Finset (Fin n)} {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history a)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
      ⟨a - x0, sub_nonneg.mpr hxa⟩] E)
    (label : feedbackUnseenFinset (feedbackTerminalLabelSet sourcePattern targetPattern history))
    (hn : 0 < n)
    (hbulk : ∀ y ∈ Icc a b,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
          ((reference.scheduledState lam x0 p0 sourcePattern targetPattern history).slope lam) y) y u ∧
        sourceBoundary (segmentCurve
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
          ((reference.scheduledState lam x0 p0 sourcePattern targetPattern history).slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
          ((reference.scheduledState lam x0 p0 sourcePattern targetPattern history).slope lam) y) y v ∧
        targetBoundary (segmentCurve
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
          ((reference.scheduledState lam x0 p0 sourcePattern targetPattern history).slope lam) y) y v ≤ n)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
    (∫ unseen in {unseen : feedbackUnseenFinset S → MarkedHeight |
        unseen ∈ feedbackNextEventSet lam terminal a b S label ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E},
      ψ (unseen label).2 - feedbackLabelMarkMean (n := n) (terminal.slope lam) ψ label
        ∂feedbackUnseenTupleLaw S) = 0 := by
  dsimp only
  have heq := rawRevealedEvent_nextEventSection_eq
    reference hlam0 hlamHalf hxa hab href seen hseen E hE label
  simp only [feedbackNextEventSetOfLabel, dite_eq_left label.property] at heq
  rw [heq]
  split_ifs
  · exact feedbackUnseenTupleLaw_nextEvent_centered_mark_eq_zero
      _ lam a b _ label hn hab hlam0 hlamHalf hbulk ψ hψ
  · simp

/-- Restricting to the actual bulk segment only changes a null endpoint, so a centered mark
still integrates to zero on a bulk next-event section. -/
theorem centered_mark_bulkNextEvent_raw_section_integral_eq_zero
    (reference : FiniteSample n) {width lam x0 p0 s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)} {history : List (FeedbackLabel n)}
    (hxa : x0 ≤ feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (hab : feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s ≤
      feedbackBranchBulkStop width lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) t)
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history
      (feedbackBranchBulkStart width lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s))
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
      ⟨feedbackBranchBulkStart width lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s - x0,
          sub_nonneg.mpr hxa⟩] E)
    (label : feedbackUnseenFinset (feedbackTerminalLabelSet sourcePattern targetPattern history))
    (hn : 0 < n) (hwidth : 0 < width) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
    (∫ unseen in {unseen : feedbackUnseenFinset S → MarkedHeight |
        unseen ∈ feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E},
      ψ (unseen label).2 - feedbackLabelMarkMean (n := n) (terminal.slope lam) ψ label
        ∂feedbackUnseenTupleLaw S) = 0 := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  dsimp only
  have heq := feedbackBulkNextEventSetOfLabel_ae_eq_branchBulkNextEventSetOfLabel
    width lam terminal s t S label hn hwidth hlam0 hlamHalf hab
  have hl : (label : FeedbackLabel n) ∈ feedbackUnseenFinset S := label.property
  simp only [feedbackNextEventSetOfLabel, dite_eq_left hl] at heq
  have hi := ae_eq_set_inter heq
    (ae_eq_refl {unseen | finiteSampleSeenUnseenMerge S seen unseen ∈ E})
  change (∫ unseen in feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∩
      {unseen | finiteSampleSeenUnseenMerge S seen unseen ∈ E},
    ψ (unseen label).2 - feedbackLabelMarkMean (n := n) (terminal.slope lam) ψ label
      ∂feedbackUnseenTupleLaw S) = 0
  rw [setIntegral_congr_set hi]
  exact centered_mark_nextEvent_raw_section_integral_eq_zero
    reference hlam0 hlamHalf hxa hab href seen hseen E hE label hn
    (fun y hy ↦ feedbackBoundary_bounds_on_branchBulkInterval width lam terminal s t y hwidth hy) ψ hψ

/-- Centered marks have zero integral on any realized history branch, including an empty
clipped bulk interval. -/
theorem centered_mark_bulkNextEvent_raw_integral_eq_zero_of_historyBranch
    (reference : FiniteSample n) {width lam x0 p0 r s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)} {history : List (FeedbackLabel n)}
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (hxr : x0 ≤ r)
    (hra : r ≤ feedbackBranchBulkStart width lam
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
      ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (label : feedbackUnseenFinset (feedbackTerminalLabelSet sourcePattern targetPattern history))
    (hn : 0 < n) (hwidth : 0 < width) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
    (∫ unseen in {unseen : feedbackUnseenFinset S → MarkedHeight |
        unseen ∈ feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E},
      ψ (unseen label).2 - feedbackLabelMarkMean (n := n) (terminal.slope lam) ψ label
        ∂feedbackUnseenTupleLaw S) = 0 := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  let a := feedbackBranchBulkStart width lam terminal s
  let b := feedbackBranchBulkStop width lam terminal t
  by_cases hab : a ≤ b
  · obtain ⟨unseen₀, _, hrefAt, hstateAt, _⟩ :=
      exists_historyAtCoordinate_finiteSampleSeenUnseenMerge_of_feedbackBranchBulk
        reference width s t a b hlam0 hlamHalf href seen hseen rfl rfl hab hn hwidth
    let referenceAt := finiteSampleSeenUnseenMerge S seen unseen₀
    have hstateAt' : referenceAt.scheduledState lam x0 p0
        sourcePattern targetPattern history = terminal := by
      simpa [referenceAt, S, terminal] using hstateAt
    have hxa : x0 ≤ a := hxr.trans hra
    have hEa : MeasurableSet[FiniteSample.rawRevealedFiltration (n := n)
        hlam0 hlamHalf x0 p0 ⟨a - x0, sub_nonneg.mpr hxa⟩] E :=
      measurableSet_rawRevealedFiltration_mono_coordinate hlam0 hlamHalf hxr hra E hE
    have hmain := centered_mark_bulkNextEvent_raw_section_integral_eq_zero
      referenceAt (width := width) (x0 := x0) (p0 := p0) (s := s) (t := t)
      hlam0 hlamHalf
      (by simpa [hstateAt'] using hxa)
      (by simpa [hstateAt'] using hab)
      (by
        rw [hstateAt']
        exact hrefAt)
      seen (by simp [referenceAt, S]) E
      (by
        convert hEa using 1
        congr 2
        exact congrArg (fun st ↦ feedbackBranchBulkStart width lam st s - x0) hstateAt') label hn hwidth ψ hψ
    simpa only [hstateAt'] using hmain
  · have hevent := feedbackBulkNextEventSetOfLabel_eq_empty_of_stop_lt_start
      width lam terminal s t S label hwidth hlam0 hlamHalf (lt_of_not_ge hab)
    dsimp only
    change (∫ unseen in {unseen : feedbackUnseenFinset S → MarkedHeight |
        unseen ∈ feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E},
      ψ (unseen label).2 - feedbackLabelMarkMean (n := n) (terminal.slope lam) ψ label
        ∂feedbackUnseenTupleLaw S) = 0
    simp [hevent]

/-- The centered mark identity holds for every seen tuple; impossible histories contribute zero. -/
theorem centered_mark_bulkNextEvent_seenSection_integral_eq_zero
    {width lam x0 p0 r s t : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)} {history : List (FeedbackLabel n)}
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hxr : x0 ≤ r) (hrs : r ≤ s) (E : Set (FiniteSample n))
    (hE : MeasurableSet[FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
      ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (label : feedbackUnseenFinset (feedbackTerminalLabelSet sourcePattern targetPattern history))
    (hn : 0 < n) (hwidth : 0 < width) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := feedbackScheduledStateOfSeen lam x0 p0
      sourcePattern targetPattern history seen
    (∫ unseen in {unseen : feedbackUnseenFinset S → MarkedHeight |
        HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
          lam x0 p0 sourcePattern targetPattern history ∧
        unseen ∈ feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E},
      ψ (unseen label).2 - feedbackLabelMarkMean (n := n) (terminal.slope lam) ψ label
        ∂feedbackUnseenTupleLaw S) = 0 := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen
  by_cases hex : ∃ unseen : feedbackUnseenFinset S → MarkedHeight,
      HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
        lam x0 p0 sourcePattern targetPattern history
  · obtain ⟨unseen₀, href⟩ := hex
    let reference := finiteSampleSeenUnseenMerge S seen unseen₀
    have hseenRef : seen = feedbackSeenTuple S reference := by simp [reference]
    have hstate : reference.scheduledState lam x0 p0
        sourcePattern targetPattern history = terminal := by
      simpa [reference, S, terminal] using
        (scheduledState_eq_feedbackScheduledStateOfSeen_of_finiteSampleSeenUnseenMerge
          S seen unseen₀ lam x0 p0 sourcePattern targetPattern history rfl)
    have hra : r ≤ feedbackBranchBulkStart width lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s := by
      rw [hstate]
      exact hrs.trans (feedbackBranchBulkStart_ge_s width lam terminal s)
    have hmain := centered_mark_bulkNextEvent_raw_integral_eq_zero_of_historyBranch
      reference (width := width) (s := s) (t := t) hlam0 hlamHalf href seen hseenRef
      hxr hra E hE label hn hwidth ψ hψ
    have hevent :
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
            lam x0 p0 sourcePattern targetPattern history ∧
          unseen ∈ feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} =
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          unseen ∈ feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} := by
      ext unseen
      constructor
      · exact fun h ↦ h.2
      · intro h
        refine ⟨?_, h⟩
        have hrect : unseen ∈ feedbackUnseenRectangularSetAt lam terminal terminal.x S := by
          have hm := h.1
          unfold feedbackBulkNextEventSetOfLabel at hm
          split at hm
          · exact hm.1.1
          · simp at hm
        have hAt :=
          (historyAtCoordinate_finiteSampleSeenUnseenMerge_iff_of_historyBranch
            reference hlam0 hlamHalf href seen unseen hseenRef le_rfl).2
              (by simpa [hstate] using hrect)
        exact hAt.1
    dsimp only at hmain ⊢
    rw [hevent]
    simpa only [hstate] using hmain
  · have hevent :
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryBranch (finiteSampleSeenUnseenMerge S seen unseen)
            lam x0 p0 sourcePattern targetPattern history ∧
          unseen ∈ feedbackBulkNextEventSetOfLabel width lam terminal s t S label ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E} = ∅ := by
      ext unseen
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun h ↦ (hex ⟨unseen, h⟩).elim
    dsimp only
    rw [hevent]
    simp

/-- The centered mark on a genuine history/next-label rectangle has zero integral under the
original finite sample law, with any revealed past event. -/
theorem finiteSampleLaw_centered_mark_historyBulkNextEvent_integral_eq_zero
    {width lam x0 p0 r s t Cψ : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n)) (history : List (FeedbackLabel n))
    (hxr : x0 ≤ r) (hrs : r ≤ s) (E : Set (FiniteSample n))
    (hE : MeasurableSet[FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
      ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (label : feedbackUnseenFinset (feedbackTerminalLabelSet sourcePattern targetPattern history))
    (hn : 0 < n) (hwidth : 0 < width) (ψ : UnitMark → ℝ) (hψ : Continuous ψ)
    (hψbound : ∀ u, ‖ψ u‖ ≤ Cψ) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    (∫ sample in {sample : FiniteSample n |
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
          feedbackUnseenTuple S sample ∈ feedbackBulkNextEventSetOfLabel width lam
            (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) s t S label ∧
          sample ∈ E},
      ψ (feedbackUnseenTuple S sample label).2 - feedbackLabelMarkMean (n := n)
        ((sample.scheduledState lam x0 p0 sourcePattern targetPattern history).slope lam)
        ψ label ∂(finiteSampleLaw n : Measure (FiniteSample n))) = 0 := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let P := (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight)
  let sampleMap : FiniteSample n → P :=
    fun sample ↦ (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)
  let C := historyBulkNextEventProductSet width lam x0 p0 s t
    sourcePattern targetPattern history E label
  let w : P → ℝ := fun parts ↦ ψ (parts.2 label).2 - feedbackLabelMarkMean (n := n)
    ((feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history parts.1).slope lam)
    ψ label
  let : IsProbabilityMeasure (feedbackTupleLaw S) := by
    unfold feedbackTupleLaw
    infer_instance
  let : IsProbabilityMeasure (feedbackUnseenTupleLaw S) := by
    unfold feedbackUnseenTupleLaw
    infer_instance
  have hC : MeasurableSet C :=
    measurableSet_historyBulkNextEventProductSet hlam0 hlamHalf
      sourcePattern targetPattern history hxr E hE label
  have hstate : Measurable (fun parts : P ↦ feedbackScheduledStateOfSeen lam x0 p0
      sourcePattern targetPattern history parts.1) :=
    (measurable_feedbackScheduledStateOfSeen lam x0 p0
      sourcePattern targetPattern history).comp measurable_fst
  have hmean := measurable_feedbackLabelMarkMean ψ hψ (label : FeedbackLabel n)
  have hw : Measurable w :=
    (hψ.measurable.comp ((measurable_pi_apply label).comp measurable_snd).snd).sub
      (hmean.comp ((FeedbackStepState.measurable_slope lam).comp hstate))
  have hwbound : ∀ parts, ‖w parts‖ ≤ 2 * Cψ := by
    intro parts
    have hq : |(feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern
        history parts.1).slope lam| ≤ lam := abs_feedbackSlope_le hlam0
    have hb : ‖feedbackLabelMarkMean (n := n)
        ((feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern
          history parts.1).slope lam) ψ label‖ ≤ Cψ :=
      norm_feedbackLabelMarkMean_le hlam0 hlamHalf hq ψ hψ hψbound
        (label : FeedbackLabel n)
    exact (norm_sub_le _ _).trans (by linarith [hψbound (parts.2 label).2])
  have hwi : Integrable w ((feedbackTupleLaw S).prod (feedbackUnseenTupleLaw S)) :=
    Integrable.of_bound hw.aestronglyMeasurable (2 * Cψ)
      (Filter.Eventually.of_forall hwbound)
  have hmapm : Measurable sampleMap :=
    (measurable_feedbackSeenTuple S).prodMk (measurable_feedbackUnseenTuple S)
  have hmap : Measure.map sampleMap (finiteSampleLaw n : Measure (FiniteSample n)) =
      (feedbackTupleLaw S).prod (feedbackUnseenTupleLaw S) := by
    simpa [sampleMap, feedbackTupleLaw, feedbackUnseenTupleLaw, S] using
      finiteSampleLaw_map_feedbackSeenUnseenTuple (n := n) S
  have htransport := integral_map hmapm.aemeasurable
    ((hw.indicator hC).aestronglyMeasurable
      (μ := Measure.map sampleMap (finiteSampleLaw n : Measure (FiniteSample n))))
  rw [hmap, integral_prod _ (hwi.indicator hC)] at htransport
  have hzero : (∫ seen, ∫ unseen, C.indicator w (seen, unseen)
      ∂feedbackUnseenTupleLaw S ∂feedbackTupleLaw S) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with seen
    have hsec : (fun unseen ↦ C.indicator w (seen, unseen)) =
        ((fun unseen ↦ (seen, unseen)) ⁻¹' C).indicator
          (fun unseen ↦ w (seen, unseen)) := by
      funext unseen
      simp only [Set.indicator, Set.mem_preimage]
    have hCm : MeasurableSet ((fun unseen ↦ (seen, unseen)) ⁻¹' C) :=
      hC.preimage (measurable_const.prodMk measurable_id)
    rw [hsec, integral_indicator hCm]
    exact centered_mark_bulkNextEvent_seenSection_integral_eq_zero
      hlam0 hlamHalf seen hxr hrs E hE label hn hwidth ψ hψ
  rw [hzero] at htransport
  have hpre := historyBulkNextEventProductSet_preimage_eq
    width lam x0 p0 s t sourcePattern targetPattern history E label
  have hpreM : MeasurableSet (sampleMap ⁻¹' C) := hC.preimage hmapm
  have hi : (fun sample ↦ C.indicator w (sampleMap sample)) =
      (sampleMap ⁻¹' C).indicator (fun sample ↦ w (sampleMap sample)) := by
    funext sample
    simp only [Set.indicator, Set.mem_preimage]
  rw [hi, integral_indicator hpreM] at htransport
  change sampleMap ⁻¹' C = _ at hpre
  rw [hpre] at htransport
  dsimp only at ⊢
  convert htransport.symm using 1
  apply setIntegral_congr_fun (hpre ▸ hpreM)
  intro sample _
  simp only [w, sampleMap]
  rw [← scheduledState_eq_feedbackScheduledStateOfSeen_feedbackSeenTuple]

/-- The centered contribution of one actual next label on one genuine history branch. -/
noncomputable def feedbackCenteredHistoryTerm (width lam x0 p0 s t : ℝ)
    (sourcePattern targetPattern : Finset (Fin n)) (history : List (FeedbackLabel n))
    (label : FeedbackLabel n) (ψ : UnitMark → ℝ) (sample : FiniteSample n) : ℝ :=
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let state := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  if HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      feedbackUnseenTuple S sample ∈ feedbackBulkNextEventSetOfLabel width lam state s t S label
    then ψ (feedbackLabelPoint label sample).2 - feedbackLabelMarkMean (state.slope lam) ψ label
    else 0

theorem measurable_feedbackCenteredHistoryTerm {width lam x0 p0 s t : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n)) (history : List (FeedbackLabel n))
    (label : FeedbackLabel n) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    Measurable (feedbackCenteredHistoryTerm width lam x0 p0 s t
      sourcePattern targetPattern history label ψ) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let C := historyBulkNextEventProductSet width lam x0 p0 s t
    sourcePattern targetPattern history univ label
  have hC : MeasurableSet C := measurableSet_historyBulkNextEventProductSet
    hlam0 hlamHalf sourcePattern targetPattern history (r := x0) le_rfl univ
      MeasurableSet.univ label
  have hpre := hC.preimage
    ((measurable_feedbackSeenTuple S).prodMk (measurable_feedbackUnseenTuple S))
  rw [historyBulkNextEventProductSet_preimage_eq] at hpre
  simp only [mem_univ, and_true] at hpre
  have hs := (FeedbackStepState.measurable_slope lam).comp
    (FiniteSample.measurable_scheduledState lam x0 p0 sourcePattern targetPattern history)
  exact Measurable.ite hpre
    ((hψ.measurable.comp (measurable_feedbackLabelPoint label).snd).sub
      ((measurable_feedbackLabelMarkMean ψ hψ label).comp hs)) measurable_const

theorem norm_feedbackCenteredHistoryTerm_le {width lam x0 p0 s t Cψ : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n)) (history : List (FeedbackLabel n))
    (label : FeedbackLabel n) (ψ : UnitMark → ℝ) (hψ : Continuous ψ)
    (hC : 0 ≤ Cψ) (hbound : ∀ u, ‖ψ u‖ ≤ Cψ) (sample : FiniteSample n) :
    ‖feedbackCenteredHistoryTerm width lam x0 p0 s t
      sourcePattern targetPattern history label ψ sample‖ ≤ 2 * Cψ := by
  unfold feedbackCenteredHistoryTerm
  dsimp only
  split_ifs
  · have hm := norm_feedbackLabelMarkMean_le
      (q := (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).slope lam)
      hlam0 hlamHalf (abs_feedbackSlope_le (k := ((sample.scheduledState lam x0 p0 sourcePattern
        targetPattern history).current : ℝ)) hlam0) ψ hψ hbound label
    exact (norm_sub_le _ _).trans (by linarith [hbound (feedbackLabelPoint label sample).2])
  · simp only [norm_zero]
    positivity

theorem integrable_feedbackCenteredHistoryTerm {width lam x0 p0 s t Cψ : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n)) (history : List (FeedbackLabel n))
    (label : FeedbackLabel n) (ψ : UnitMark → ℝ) (hψ : Continuous ψ)
    (hC : 0 ≤ Cψ) (hbound : ∀ u, ‖ψ u‖ ≤ Cψ) :
    Integrable (feedbackCenteredHistoryTerm width lam x0 p0 s t
      sourcePattern targetPattern history label ψ) (finiteSampleLaw n) :=
  Integrable.of_bound (measurable_feedbackCenteredHistoryTerm hlam0 hlamHalf
    sourcePattern targetPattern history label ψ hψ).aestronglyMeasurable (2 * Cψ)
    (Filter.Eventually.of_forall (norm_feedbackCenteredHistoryTerm_le hlam0 hlamHalf
      sourcePattern targetPattern history label ψ hψ hC hbound))

/-- Raw past tests annihilate every actual centered next-label contribution. -/
theorem setIntegral_feedbackCenteredHistoryTerm_eq_zero {width lam x0 p0 r s t Cψ : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n)) (history : List (FeedbackLabel n))
    (hxr : x0 ≤ r) (hrs : r ≤ s) (E : Set (FiniteSample n))
    (hE : MeasurableSet[FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
      ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (label : FeedbackLabel n) (hn : 0 < n) (hwidth : 0 < width)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hbound : ∀ u, ‖ψ u‖ ≤ Cψ) :
    (∫ sample in E, feedbackCenteredHistoryTerm width lam x0 p0 s t
      sourcePattern targetPattern history label ψ sample ∂(finiteSampleLaw n)) = 0 := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  by_cases hl : label ∈ feedbackUnseenFinset S
  · have hm := finiteSampleLaw_centered_mark_historyBulkNextEvent_integral_eq_zero
      (t := t) hlam0 hlamHalf sourcePattern targetPattern history hxr hrs E hE ⟨label, hl⟩
      hn hwidth ψ hψ hbound
    let A := {sample : FiniteSample n |
      HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      feedbackUnseenTuple S sample ∈ feedbackBulkNextEventSetOfLabel width lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) s t S label}
    have hA : MeasurableSet A := by
      have hc := measurableSet_historyBulkNextEventProductSet
        (width := width) (p0 := p0) (s := s) (t := t) hlam0 hlamHalf sourcePattern targetPattern history (r := x0) le_rfl univ
          MeasurableSet.univ label
      have hpre := hc.preimage
        ((measurable_feedbackSeenTuple S).prodMk (measurable_feedbackUnseenTuple S))
      rw [historyBulkNextEventProductSet_preimage_eq] at hpre
      simpa only [mem_univ, and_true] using hpre
    have hfun : feedbackCenteredHistoryTerm width lam x0 p0 s t
        sourcePattern targetPattern history label ψ =
        A.indicator (fun sample ↦ ψ (feedbackLabelPoint label sample).2 -
          feedbackLabelMarkMean ((sample.scheduledState lam x0 p0 sourcePattern targetPattern
            history).slope lam) ψ label) := by
      funext sample
      simp only [feedbackCenteredHistoryTerm, Set.indicator, A, S, mem_ofPred_eq]
    rw [hfun, integral_indicator hA, Measure.restrict_restrict hA]
    simpa only [A, S, feedbackLabelTuple, Set.ofPred_and, Set.ofPred_mem_eq, inter_assoc] using hm
  · dsimp only [S] at hl
    have hz : feedbackCenteredHistoryTerm width lam x0 p0 s t
        sourcePattern targetPattern history label ψ = 0 := by
      funext sample
      simp only [feedbackCenteredHistoryTerm, feedbackBulkNextEventSetOfLabel,
        dite_eq_right hl, mem_empty_iff_false, and_false, ite_false, Pi.zero_apply]
    rw [hz]
    exact integral_zero _ _

end OTSelector
