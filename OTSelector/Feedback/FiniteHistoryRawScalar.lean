import OTSelector.Feedback.AdaptiveDeferredDecision
import OTSelector.Feedback.FiniteHistoryBeforePartition
import OTSelector.Feedback.FiniteHistoryRawEvent

/-!
# Scalar assembly over finite raw-history sections

This file assembles scalar set-integral inequalities over the almost-everywhere finite partition
by strict histories.  On each history cell, a raw revealed event has either the whole unseen
rectangle or the empty unseen section, while the continuously valued seen tuple remains the
outer Fubini variable.

The results below do not construct a regular conditional distribution and do not make a claim
about the usual augmentation.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

/-! ## Integrability under seen/unseen coordinates -/

/-- An integrable finite-sample scalar remains integrable after transporting it to the exact
seen/unseen product coordinates. -/
theorem integrable_finiteSampleSeenUnseenMerge
    (S : Finset (FeedbackLabel n)) {f : FiniteSample n → ℝ}
    (hf : Integrable f (finiteSampleLaw n : Measure (FiniteSample n))) :
    Integrable
      (fun parts : (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) ↦
        f (finiteSampleSeenUnseenMerge S parts.1 parts.2))
      ((feedbackTupleLaw S).prod (feedbackUnseenTupleLaw S)) := by
  let e := finiteSampleSeenUnseenMeasurableEquiv S
  have hmap : Measure.map e (finiteSampleLaw n : Measure (FiniteSample n)) =
      (feedbackTupleLaw S).prod (feedbackUnseenTupleLaw S) := by
    change Measure.map
      (fun sample : FiniteSample n ↦
        (feedbackSeenTuple S sample, feedbackUnseenTuple S sample))
      (finiteSampleLaw n : Measure (FiniteSample n)) = _
    simpa [feedbackTupleLaw, feedbackUnseenTupleLaw] using
      finiteSampleLaw_map_feedbackSeenUnseenTuple (n := n) S
  change Integrable (f ∘ e.symm) ((feedbackTupleLaw S).prod (feedbackUnseenTupleLaw S))
  rw [← hmap, integrable_map_equiv]
  have hcomp : (f ∘ e.symm) ∘ e = f := by
    funext sample
    simp
  rw [hcomp]
  exact hf

/-! ## The almost-everywhere finite partition -/

/-- A set integral is the finite sum of its restrictions to the right-continuous history cells.
The proof first uses the strict-history indicator partition and then replaces each strict cell by
its almost-everywhere equal right-continuous cell. -/
theorem setIntegral_eq_sum_historyCell
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    (A : Set (FiniteSample n)) (hA : MeasurableSet A)
    {f : FiniteSample n → ℝ}
    (hf : Integrable f (finiteSampleLaw n : Measure (FiniteSample n))) :
    (∫ sample in A, f sample ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
      ∑ index : HistoryCellIndex n,
        ∫ sample in A ∩ historyCell index lam x0 p0 x,
          f sample ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
  classical
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  have hfA : Integrable (A.indicator f) μ := hf.indicator hA
  have hpart := sum_historyBeforeCell_indicator_one_ae
    (n := n) (p0 := p0) hlam0 hlamHalf hx0x
  calc
    (∫ sample in A, f sample ∂μ) = ∫ sample, A.indicator f sample ∂μ :=
      (integral_indicator hA).symm
    _ = ∫ sample, ∑ index : HistoryCellIndex n,
          (historyBeforeCell index lam x0 p0 x).indicator (A.indicator f) sample ∂μ := by
      apply integral_congr_ae
      filter_upwards [hpart] with sample hsample
      calc
        A.indicator f sample = 1 * A.indicator f sample := (one_mul _).symm
        _ = (∑ index : HistoryCellIndex n,
              (historyBeforeCell index lam x0 p0 x).indicator
                (fun _ ↦ (1 : ℝ)) sample) * A.indicator f sample := by rw [hsample]
        _ = ∑ index : HistoryCellIndex n,
              (historyBeforeCell index lam x0 p0 x).indicator
                (A.indicator f) sample := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro index hindex
          by_cases hcell : sample ∈ historyBeforeCell index lam x0 p0 x <;>
            simp [hcell]
    _ = ∑ index : HistoryCellIndex n, ∫ sample,
          (historyBeforeCell index lam x0 p0 x).indicator (A.indicator f) sample ∂μ := by
      rw [integral_finsetSum (s := (Finset.univ : Finset (HistoryCellIndex n)))
        (fun index hindex ↦ hfA.indicator
          (measurableSet_historyBeforeCell index lam x0 p0 x))]
    _ = ∑ index : HistoryCellIndex n,
          ∫ sample in A ∩ historyBeforeCell index lam x0 p0 x, f sample ∂μ := by
      apply Finset.sum_congr rfl
      intro index hindex
      rw [← integral_indicator
        (hA.inter (measurableSet_historyBeforeCell index lam x0 p0 x))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun sample ↦ by
        by_cases hsampleA : sample ∈ A <;>
          by_cases hsampleCell : sample ∈ historyBeforeCell index lam x0 p0 x <;>
            simp [hsampleA, hsampleCell]
    _ = ∑ index : HistoryCellIndex n,
          ∫ sample in A ∩ historyCell index lam x0 p0 x, f sample ∂μ := by
      apply Finset.sum_congr rfl
      intro index hindex
      apply setIntegral_congr_set
      exact (ae_eq_refl A).inter
        (historyBeforeCell_ae_eq_historyCell index hlam0 hlamHalf hx0x)

/-! ## Cellwise Fubini transport -/

/-- The scalar integral over a raw event inside one history cell is its iterated seen/unseen
section integral.  The seen tuple is the outer integration variable. -/
theorem setIntegral_inter_historyCell_eq_iterated
    {lam x0 p0 x : ℝ}
    (index : HistoryCellIndex n)
    (A : Set (FiniteSample n)) (hA : MeasurableSet A)
    {f : FiniteSample n → ℝ}
    (hf : Integrable f (finiteSampleLaw n : Measure (FiniteSample n))) :
    (∫ sample in A ∩ historyCell index lam x0 p0 x,
        f sample ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
      let S := feedbackTerminalLabelSet
        index.sourcePattern index.targetPattern index.history
      ∫ seen, ∫ unseen,
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 index.sourcePattern index.targetPattern index.history x ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ A}.indicator
          (fun unseen ↦ f (finiteSampleSeenUnseenMerge S seen unseen)) unseen
        ∂(feedbackUnseenTupleLaw S) ∂(feedbackTupleLaw S) := by
  let S := feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history
  let F : (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) → ℝ :=
    fun parts ↦ A.indicator f (finiteSampleSeenUnseenMerge S parts.1 parts.2)
  have hF : Integrable F ((feedbackTupleLaw S).prod (feedbackUnseenTupleLaw S)) := by
    exact integrable_finiteSampleSeenUnseenMerge S (hf.indicator hA)
  have htransport := integral_historyAtCoordinate_eq_iterated
    (n := n) lam x0 p0 index.sourcePattern index.targetPattern index.history x hF
  dsimp only
  calc
    (∫ sample in A ∩ historyCell index lam x0 p0 x,
        f sample ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
        ∫ sample,
          (historyCell index lam x0 p0 x).indicator
            (fun sample ↦ F
              (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)) sample
          ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
      rw [← integral_indicator (hA.inter (measurableSet_historyCell index lam x0 p0 x))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun sample ↦ by
        simp only [F, finiteSampleSeenUnseenMerge_split]
        by_cases hsampleA : sample ∈ A <;>
          by_cases hsampleCell : sample ∈ historyCell index lam x0 p0 x <;>
            simp [hsampleA, hsampleCell]
    _ = ∫ seen, ∫ unseen,
          (historyAtCoordinateProductSet lam x0 p0 index.sourcePattern index.targetPattern
            index.history x).indicator F (seen, unseen)
          ∂(feedbackUnseenTupleLaw S) ∂(feedbackTupleLaw S) := by
      simpa [historyCell, S] using htransport
    _ = ∫ seen, ∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 index.sourcePattern index.targetPattern index.history x ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ A}.indicator
            (fun unseen ↦ f (finiteSampleSeenUnseenMerge S seen unseen)) unseen
          ∂(feedbackUnseenTupleLaw S) ∂(feedbackTupleLaw S) := by
      apply integral_congr_ae
      filter_upwards [] with seen
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun unseen ↦ by
        by_cases hcell : HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
            lam x0 p0 index.sourcePattern index.targetPattern index.history x <;>
          by_cases hsample : finiteSampleSeenUnseenMerge S seen unseen ∈ A <;>
            simp [historyAtCoordinateProductSet, F, S, hcell, hsample]

/-- The unseen integral appearing in the cellwise transport is integrable as a function of the
continuous outer seen tuple. -/
theorem integrable_rawEvent_historySectionIntegral
    {lam x0 p0 x : ℝ}
    (index : HistoryCellIndex n)
    (A : Set (FiniteSample n)) (hA : MeasurableSet A)
    {f : FiniteSample n → ℝ}
    (hf : Integrable f (finiteSampleLaw n : Measure (FiniteSample n))) :
    let S := feedbackTerminalLabelSet
      index.sourcePattern index.targetPattern index.history
    Integrable (fun seen ↦ ∫ unseen,
      {unseen : feedbackUnseenFinset S → MarkedHeight |
        HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
            lam x0 p0 index.sourcePattern index.targetPattern index.history x ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ A}.indicator
        (fun unseen ↦ f (finiteSampleSeenUnseenMerge S seen unseen)) unseen
      ∂(feedbackUnseenTupleLaw S)) (feedbackTupleLaw S) := by
  let S := feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history
  let F : (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) → ℝ :=
    fun parts ↦ A.indicator f (finiteSampleSeenUnseenMerge S parts.1 parts.2)
  let C := historyAtCoordinateProductSet lam x0 p0 index.sourcePattern index.targetPattern
    index.history x
  have hF : Integrable F ((feedbackTupleLaw S).prod (feedbackUnseenTupleLaw S)) := by
    exact integrable_finiteSampleSeenUnseenMerge S (hf.indicator hA)
  have hC : MeasurableSet C := by
    exact measurableSet_historyAtCoordinateProductSet
      lam x0 p0 index.sourcePattern index.targetPattern index.history x
  let : IsProbabilityMeasure (feedbackUnseenTupleLaw S) := by
    rw [feedbackUnseenTupleLaw]
    infer_instance
  have houter := (hF.indicator hC).integral_prod_left
  dsimp only
  convert houter using 1
  funext seen
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun unseen ↦ by
    by_cases hcell : HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
        lam x0 p0 index.sourcePattern index.targetPattern index.history x <;>
      by_cases hsample : finiteSampleSeenUnseenMerge S seen unseen ∈ A <;>
        simp [C, historyAtCoordinateProductSet, F, S, hcell, hsample]

/-! ## Raw-event sections -/

/-- On a realized history section, integrating over a raw revealed event is either integration
over the whole remaining unseen rectangle or zero. -/
theorem rawRevealedEvent_historySection_setIntegral_eq
    (reference : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history x)
    (A : Set (FiniteSample n))
    (hA : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x⟩] A)
    (f : FiniteSample n → ℝ) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
    (∫ unseen,
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryAtCoordinate
              (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
              lam x0 p0 sourcePattern targetPattern history x ∧
            finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen ∈ A}.indicator
          (fun unseen ↦
            f (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)) unseen
        ∂(feedbackUnseenTupleLaw S)) =
      if reference ∈ A then
        ∫ unseen in feedbackUnseenRectangularSetAt lam terminal x S,
          f (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
          ∂(feedbackUnseenTupleLaw S)
      else 0 := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hset := rawRevealedEvent_historySection_eq reference hlam0 hlamHalf hx0x href A hA
  dsimp only at hset ⊢
  rw [hset]
  by_cases hreference : reference ∈ A
  · simp only [ite_eq_left hreference]
    exact integral_indicator
      (measurableSet_feedbackUnseenRectangularSetAt lam terminal x S)
  · simp [hreference]

/-! ## Cellwise and global scalar inequalities -/

/-- A rectangle-section inequality on one history cell implies the corresponding raw-event
set-integral inequality on that cell. -/
theorem setIntegral_inter_historyCell_le_of_historySection_le
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 < x)
    (index : HistoryCellIndex n)
    (A : Set (FiniteSample n))
    (hA : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x.le⟩] A)
    {f g : FiniteSample n → ℝ}
    (hf : Integrable f (finiteSampleLaw n : Measure (FiniteSample n)))
    (hg : Integrable g (finiteSampleLaw n : Measure (FiniteSample n)))
    (hsection : ∀ reference : FiniteSample n,
      reference ∈ historyCell index lam x0 p0 x →
        let S := feedbackTerminalLabelSet
          index.sourcePattern index.targetPattern index.history
        let terminal := reference.scheduledState lam x0 p0
          index.sourcePattern index.targetPattern index.history
        (∫ unseen in feedbackUnseenRectangularSetAt lam terminal x S,
            f (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S)) ≤
          ∫ unseen in feedbackUnseenRectangularSetAt lam terminal x S,
            g (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S)) :
    (∫ sample in A ∩ historyCell index lam x0 p0 x,
        f sample ∂(finiteSampleLaw n : Measure (FiniteSample n))) ≤
      ∫ sample in A ∩ historyCell index lam x0 p0 x,
        g sample ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
  let S := feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history
  have hAambient : MeasurableSet A :=
    (FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le
      ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ A hA
  rw [setIntegral_inter_historyCell_eq_iterated index A hAambient hf,
    setIntegral_inter_historyCell_eq_iterated index A hAambient hg]
  refine integral_mono
    (integrable_rawEvent_historySectionIntegral index A hAambient hf)
    (integrable_rawEvent_historySectionIntegral index A hAambient hg) ?_
  intro seen
  dsimp only
  by_cases hrealized : ∃ unseen : feedbackUnseenFinset S → MarkedHeight,
      HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
        lam x0 p0 index.sourcePattern index.targetPattern index.history x
  · obtain ⟨unseen₀, href⟩ := hrealized
    let reference := finiteSampleSeenUnseenMerge S seen unseen₀
    have hrefCell : reference ∈ historyCell index lam x0 p0 x := href
    have hfSection := rawRevealedEvent_historySection_setIntegral_eq
      reference hlam0 hlamHalf hx0x.le href A hA f
    have hgSection := rawRevealedEvent_historySection_setIntegral_eq
      reference hlam0 hlamHalf hx0x.le href A hA g
    have hle := hsection reference hrefCell
    have hfSection' :
        (∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 index.sourcePattern index.targetPattern index.history x ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ A}.indicator
            (fun unseen ↦ f (finiteSampleSeenUnseenMerge S seen unseen)) unseen
          ∂(feedbackUnseenTupleLaw S)) =
          if reference ∈ A then
            let terminal := reference.scheduledState lam x0 p0
              index.sourcePattern index.targetPattern index.history
            ∫ unseen in feedbackUnseenRectangularSetAt lam terminal x S,
              f (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
              ∂(feedbackUnseenTupleLaw S)
          else 0 := by
      simpa [reference, S] using hfSection
    have hgSection' :
        (∫ unseen,
          {unseen : feedbackUnseenFinset S → MarkedHeight |
            HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                lam x0 p0 index.sourcePattern index.targetPattern index.history x ∧
              finiteSampleSeenUnseenMerge S seen unseen ∈ A}.indicator
            (fun unseen ↦ g (finiteSampleSeenUnseenMerge S seen unseen)) unseen
          ∂(feedbackUnseenTupleLaw S)) =
          if reference ∈ A then
            let terminal := reference.scheduledState lam x0 p0
              index.sourcePattern index.targetPattern index.history
            ∫ unseen in feedbackUnseenRectangularSetAt lam terminal x S,
              g (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
              ∂(feedbackUnseenTupleLaw S)
          else 0 := by
      simpa [reference, S] using hgSection
    by_cases hreferenceA : reference ∈ A
    · rw [hfSection', hgSection']
      simp only [ite_eq_left hreferenceA]
      simpa [reference, S] using hle
    · rw [hfSection', hgSection']
      simp only [ite_eq_right hreferenceA]
      exact le_rfl
  · have hempty :
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 index.sourcePattern index.targetPattern index.history x ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ A} = ∅ := by
      ext unseen
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun hmem ↦ hrealized ⟨unseen, hmem.1⟩
    rw [hempty]
    simp only [indicator_empty', le_refl]

/-- Explicit rectangle-section inequalities for every finite history assemble to the raw
set-integral inequality for every raw revealed event. -/
theorem setIntegral_le_of_historySection_le
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 < x)
    (A : Set (FiniteSample n))
    (hA : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x.le⟩] A)
    {f g : FiniteSample n → ℝ}
    (hf : Integrable f (finiteSampleLaw n : Measure (FiniteSample n)))
    (hg : Integrable g (finiteSampleLaw n : Measure (FiniteSample n)))
    (hsection : ∀ (index : HistoryCellIndex n) (reference : FiniteSample n),
      reference ∈ historyCell index lam x0 p0 x →
        let S := feedbackTerminalLabelSet
          index.sourcePattern index.targetPattern index.history
        let terminal := reference.scheduledState lam x0 p0
          index.sourcePattern index.targetPattern index.history
        (∫ unseen in feedbackUnseenRectangularSetAt lam terminal x S,
            f (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S)) ≤
          ∫ unseen in feedbackUnseenRectangularSetAt lam terminal x S,
            g (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S)) :
    (∫ sample in A, f sample ∂(finiteSampleLaw n : Measure (FiniteSample n))) ≤
      ∫ sample in A, g sample ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
  have hAambient : MeasurableSet A :=
    (FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le
      ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ A hA
  rw [setIntegral_eq_sum_historyCell hlam0 hlamHalf hx0x A hAambient hf,
    setIntegral_eq_sum_historyCell hlam0 hlamHalf hx0x A hAambient hg]
  exact Finset.sum_le_sum fun index hindex ↦
    setIntegral_inter_historyCell_le_of_historySection_le
      hlam0 hlamHalf hx0x index A hA hf hg (hsection index)

end OTSelector
