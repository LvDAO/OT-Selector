import OTSelector.Feedback.FiniteEventBulkCountIntegral
import OTSelector.Feedback.FiniteHistoryBulkRateTransport
import OTSelector.Feedback.FiniteHistoryBulkRatePartition
import OTSelector.Probability.CountingProcess.ShiftedTimeMeasure
import OTSelector.Feedback.FeedbackBulkGlobalIntegrable

/-!
# Raw predictable rectangles for the finite bulk event counts

This file is the finite-history bookkeeping layer between the event-count integral and the safe
bulk rate.  The event side is first split over the finite history indices.  A fixed history is
then transported to elapsed time, the strict history cells are summed only almost everywhere,
and the last finite sum/time-sample swap is justified by the global product integrability of the
safe rate.
-/

open MeasureTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace OTSelector

variable {n : ℕ}

open CountingProcess FiniteSample

/-! ## Elapsed-time cell integrands -/

private noncomputable def sourceHistoryRateCellValue
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (index : HistoryCellIndex n)
    (E : Set (FiniteSample n)) (u : ℝ≥0) (y : ℝ) (sample : FiniteSample n) : ℝ :=
  {sample : FiniteSample n |
      HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern
        index.history y ∧ sample ∈ E}.indicator
    (fun sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample) sample

private noncomputable def targetHistoryRateCellValue
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (index : HistoryCellIndex n)
    (E : Set (FiniteSample n)) (u : ℝ≥0) (y : ℝ) (sample : FiniteSample n) : ℝ :=
  {sample : FiniteSample n |
      HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern
        index.history y ∧ sample ∈ E}.indicator
    (fun sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample) sample

private noncomputable def sourceRawHistoryRateCell
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (index : HistoryCellIndex n)
    (E : Set (FiniteSample n)) (u : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  sourceHistoryRateCellValue hlam0 hlamHalf B x0 p0 index E u (x0 + (u : ℝ)) sample

private noncomputable def targetRawHistoryRateCell
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (index : HistoryCellIndex n)
    (E : Set (FiniteSample n)) (u : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  targetHistoryRateCellValue hlam0 hlamHalf B x0 p0 index E u (x0 + (u : ℝ)) sample

private theorem sourceRawHistoryRateCell_product_integrable
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (index : HistoryCellIndex n) (E : Set (FiniteSample n))
    (hE : MeasurableSet E) :
    Integrable
      (fun z : ℝ≥0 × FiniteSample n ↦
        sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E z.1 z.2)
      (timeMeasure.prod (finiteSampleLaw n : Measure (FiniteSample n))) := by
  let A : Set (ℝ≥0 × FiniteSample n) :=
    {z |
      HistoryBeforeCoordinate z.2 lam x0 p0 index.sourcePattern index.targetPattern
        index.history (x0 + (z.1 : ℝ)) ∧ z.2 ∈ E}
  have hmap : Measurable (fun z : ℝ≥0 × FiniteSample n ↦
      (x0 + (z.1 : ℝ), z.2)) := by
    exact (measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
      measurable_snd
  have hA : MeasurableSet A := by
    change MeasurableSet
      ({z : ℝ≥0 × FiniteSample n |
        HistoryBeforeCoordinate z.2 lam x0 p0 index.sourcePattern index.targetPattern
          index.history (x0 + (z.1 : ℝ))} ∩
        {z : ℝ≥0 × FiniteSample n | z.2 ∈ E})
    exact
      (measurableSet_historyBeforeCoordinate_joint lam x0 p0
        index.sourcePattern index.targetPattern index.history).preimage hmap |>.inter
      (hE.preimage measurable_snd)
  have hprod := safeSourceBulkRate_product_integrable
    (n := n) hlam0 hlamHalf B x0 p0
  have hprodA := hprod.indicator hA
  have hcell_eq :
      (fun z : ℝ≥0 × FiniteSample n ↦
        A.indicator (Function.uncurry
          (safeSourceBulkRate hlam0 hlamHalf B x0 p0)) z) =
        (fun z : ℝ≥0 × FiniteSample n ↦
          sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E z.1 z.2) := by
    funext z
    by_cases hz : z ∈ A
    · have hz' : HistoryBeforeCoordinate z.2 lam x0 p0 index.sourcePattern
          index.targetPattern index.history (x0 + (z.1 : ℝ)) ∧ z.2 ∈ E := hz
      rw [Set.indicator_of_mem hz]
      change safeSourceBulkRate hlam0 hlamHalf B x0 p0 z.1 z.2 = _
      rw [sourceRawHistoryRateCell, sourceHistoryRateCellValue]
      have hz'' : z.2 ∈ {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern
            index.history (x0 + (z.1 : ℝ)) ∧ sample ∈ E} := hz'
      rw [Set.indicator_of_mem hz'']
    · have hz' : ¬ (HistoryBeforeCoordinate z.2 lam x0 p0 index.sourcePattern
          index.targetPattern index.history (x0 + (z.1 : ℝ)) ∧ z.2 ∈ E) := hz
      rw [Set.indicator_of_notMem hz]
      rw [sourceRawHistoryRateCell, sourceHistoryRateCellValue]
      have hz'' : z.2 ∉ {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern
            index.history (x0 + (z.1 : ℝ)) ∧ sample ∈ E} := hz'
      rw [Set.indicator_of_notMem hz'']
  rw [← hcell_eq]
  exact hprodA

private theorem targetRawHistoryRateCell_product_integrable
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (index : HistoryCellIndex n) (E : Set (FiniteSample n))
    (hE : MeasurableSet E) :
    Integrable
      (fun z : ℝ≥0 × FiniteSample n ↦
        targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E z.1 z.2)
      (timeMeasure.prod (finiteSampleLaw n : Measure (FiniteSample n))) := by
  let A : Set (ℝ≥0 × FiniteSample n) :=
    {z |
      HistoryBeforeCoordinate z.2 lam x0 p0 index.sourcePattern index.targetPattern
        index.history (x0 + (z.1 : ℝ)) ∧ z.2 ∈ E}
  have hmap : Measurable (fun z : ℝ≥0 × FiniteSample n ↦
      (x0 + (z.1 : ℝ), z.2)) := by
    exact (measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
      measurable_snd
  have hA : MeasurableSet A := by
    change MeasurableSet
      ({z : ℝ≥0 × FiniteSample n |
        HistoryBeforeCoordinate z.2 lam x0 p0 index.sourcePattern index.targetPattern
          index.history (x0 + (z.1 : ℝ))} ∩
        {z : ℝ≥0 × FiniteSample n | z.2 ∈ E})
    exact
      (measurableSet_historyBeforeCoordinate_joint lam x0 p0
        index.sourcePattern index.targetPattern index.history).preimage hmap |>.inter
      (hE.preimage measurable_snd)
  have hprod := safeTargetBulkRate_product_integrable
    (n := n) hlam0 hlamHalf B x0 p0
  have hprodA := hprod.indicator hA
  have hcell_eq :
      (fun z : ℝ≥0 × FiniteSample n ↦
        A.indicator (Function.uncurry
          (safeTargetBulkRate hlam0 hlamHalf B x0 p0)) z) =
        (fun z : ℝ≥0 × FiniteSample n ↦
          targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E z.1 z.2) := by
    funext z
    by_cases hz : z ∈ A
    · have hz' : HistoryBeforeCoordinate z.2 lam x0 p0 index.sourcePattern
          index.targetPattern index.history (x0 + (z.1 : ℝ)) ∧ z.2 ∈ E := hz
      rw [Set.indicator_of_mem hz]
      change safeTargetBulkRate hlam0 hlamHalf B x0 p0 z.1 z.2 = _
      rw [targetRawHistoryRateCell, targetHistoryRateCellValue]
      have hz'' : z.2 ∈ {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern
            index.history (x0 + (z.1 : ℝ)) ∧ sample ∈ E} := hz'
      rw [Set.indicator_of_mem hz'']
    · have hz' : ¬ (HistoryBeforeCoordinate z.2 lam x0 p0 index.sourcePattern
          index.targetPattern index.history (x0 + (z.1 : ℝ)) ∧ z.2 ∈ E) := hz
      rw [Set.indicator_of_notMem hz]
      rw [targetRawHistoryRateCell, targetHistoryRateCellValue]
      have hz'' : z.2 ∉ {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern
            index.history (x0 + (z.1 : ℝ)) ∧ sample ∈ E} := hz'
      rw [Set.indicator_of_notMem hz'']
  rw [← hcell_eq]
  exact hprodA

private theorem sourceRawHistoryRateCell_section_integrable
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (index : HistoryCellIndex n) (E : Set (FiniteSample n))
    (hE : MeasurableSet E) (u : ℝ≥0) :
    Integrable
      (fun sample : FiniteSample n ↦
        sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  let C : Set (FiniteSample n) :=
    {sample |
      HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern
        index.history (x0 + (u : ℝ)) ∧ sample ∈ E}
  have hC : MeasurableSet C := by
    change MeasurableSet
      (historyBeforeCell index lam x0 p0
          (FiniteSample.elapsedFeedbackCoordinate x0 u) ∩ E)
    exact measurableSet_historyBeforeCell index lam x0 p0 _ |>.inter hE
  have hrate : Measurable (fun sample : FiniteSample n ↦
      safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample) := by
    have hp := safeSourceBulkRate_predictable
      (n := n) hlam0 hlamHalf B x0 p0
    have hp' : StronglyMeasurable
        (Function.uncurry (safeSourceBulkRate hlam0 hlamHalf B x0 p0)) :=
      hp.mono (predictable_le_ambient
        (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0))
    exact hp'.measurable.comp (measurable_const.prodMk measurable_id)
  have hconst : Integrable (fun _ : FiniteSample n ↦ feedbackBulkRateCap n B)
      (finiteSampleLaw n : Measure (FiniteSample n)) := integrable_const _
  have hmain := hconst.mono' (hrate.indicator hC).aestronglyMeasurable
    (Filter.Eventually.of_forall fun sample ↦ by
      by_cases hsample : sample ∈ C
      · rw [Set.indicator_of_mem hsample]
        simpa [Real.norm_eq_abs,
          abs_of_nonneg (safeSourceBulkRate_nonneg hlam0 hlamHalf B x0 p0 u sample),
          abs_of_nonneg (feedbackBulkRateCap_nonneg n B)] using
          safeSourceBulkRate_le_cap hlam0 hlamHalf B x0 p0 u sample
      · simp [Set.indicator_of_notMem hsample,
          feedbackBulkRateCap_nonneg n B])
  simpa [C, sourceRawHistoryRateCell, sourceHistoryRateCellValue] using hmain

private theorem targetRawHistoryRateCell_section_integrable
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (index : HistoryCellIndex n) (E : Set (FiniteSample n))
    (hE : MeasurableSet E) (u : ℝ≥0) :
    Integrable
      (fun sample : FiniteSample n ↦
        targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  let C : Set (FiniteSample n) :=
    {sample |
      HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern
        index.history (x0 + (u : ℝ)) ∧ sample ∈ E}
  have hC : MeasurableSet C := by
    change MeasurableSet
      (historyBeforeCell index lam x0 p0
          (FiniteSample.elapsedFeedbackCoordinate x0 u) ∩ E)
    exact measurableSet_historyBeforeCell index lam x0 p0 _ |>.inter hE
  have hrate : Measurable (fun sample : FiniteSample n ↦
      safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample) := by
    have hp := safeTargetBulkRate_predictable
      (n := n) hlam0 hlamHalf B x0 p0
    have hp' : StronglyMeasurable
        (Function.uncurry (safeTargetBulkRate hlam0 hlamHalf B x0 p0)) :=
      hp.mono (predictable_le_ambient
        (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0))
    exact hp'.measurable.comp (measurable_const.prodMk measurable_id)
  have hconst : Integrable (fun _ : FiniteSample n ↦ feedbackBulkRateCap n B)
      (finiteSampleLaw n : Measure (FiniteSample n)) := integrable_const _
  have hmain := hconst.mono' (hrate.indicator hC).aestronglyMeasurable
    (Filter.Eventually.of_forall fun sample ↦ by
      by_cases hsample : sample ∈ C
      · rw [Set.indicator_of_mem hsample]
        simpa [Real.norm_eq_abs,
          abs_of_nonneg (safeTargetBulkRate_nonneg hlam0 hlamHalf B x0 p0 u sample),
          abs_of_nonneg (feedbackBulkRateCap_nonneg n B)] using
          safeTargetBulkRate_le_cap hlam0 hlamHalf B x0 p0 u sample
      · simp [Set.indicator_of_notMem hsample,
          feedbackBulkRateCap_nonneg n B])
  simpa [C, targetRawHistoryRateCell, targetHistoryRateCellValue] using hmain

/-! ## Absolute-coordinate transport for one history -/

private theorem historyStrictRateIntegral_eq_elapsedCellIntegral
    (rate : ℝ≥0 → FiniteSample n → ℝ) {lam x0 p0 : ℝ} {s t : ℝ≥0}
    (index : HistoryCellIndex n) (E : Set (FiniteSample n)) (hst : s ≤ t) :
    (∫ y in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), ∫ sample,
      {sample : FiniteSample n |
        HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
            index.targetPattern index.history y ∧ sample ∈ E}.indicator
        (fun sample ↦ rate (Real.toNNReal (y - x0)) sample) sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume) =
      ∫ u in Ioc s t, ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
              index.targetPattern index.history (x0 + (u : ℝ)) ∧ sample ∈ E}.indicator
          (fun sample ↦ rate u sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure := by
  have hst' : x0 + (s : ℝ) ≤ x0 + (t : ℝ) := by
    have hstReal : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    simpa [add_comm] using add_le_add_right hstReal x0
  calc
    (∫ y in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
              index.targetPattern index.history y ∧ sample ∈ E}.indicator
          (fun sample ↦ rate (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume) =
      ∫ y in x0 + (s : ℝ)..x0 + (t : ℝ), ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
              index.targetPattern index.history y ∧ sample ∈ E}.indicator
          (fun sample ↦ rate (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) :=
      (intervalIntegral.integral_of_le hst').symm
    _ = ∫ u in Ioc s t, ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
              index.targetPattern index.history (x0 + (u : ℝ)) ∧ sample ∈ E}.indicator
          (fun sample ↦ rate (Real.toNNReal (x0 + (u : ℝ) - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure :=
      (integral_shifted_timeMeasure_eq_intervalIntegral
        (fun y ↦ ∫ sample,
          {sample : FiniteSample n |
            HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
                index.targetPattern index.history y ∧ sample ∈ E}.indicator
            (fun sample ↦ rate (Real.toNNReal (y - x0)) sample) sample
          ∂(finiteSampleLaw n : Measure (FiniteSample n))) x0 s t hst).symm
    _ = ∫ u in Ioc s t, ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
              index.targetPattern index.history (x0 + (u : ℝ)) ∧ sample ∈ E}.indicator
          (fun sample ↦ rate u sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [show x0 + (u : ℝ) - x0 = (u : ℝ) by ring, Real.toNNReal_coe]

private theorem sourceStrictSafeRateIntegral_eq_elapsedCellIntegral
    {lam B x0 p0 : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (index : HistoryCellIndex n) (E : Set (FiniteSample n)) (hst : s ≤ t) :
    (∫ y in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), ∫ sample,
      {sample : FiniteSample n |
        HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
            index.targetPattern index.history y ∧ sample ∈ E}.indicator
        (fun _ ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0
          (Real.toNNReal (y - x0)) sample) sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume) =
      ∫ u in Ioc s t, ∫ sample,
        sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure := by
  calc
    (∫ y in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
              index.targetPattern index.history y ∧ sample ∈ E}.indicator
          (fun _ ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0
            (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume) =
      ∫ y in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
              index.targetPattern index.history y ∧ sample ∈ E}.indicator
          (fun sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0
            (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [] with sample
      by_cases hmem : HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
          index.targetPattern index.history y ∧ sample ∈ E <;> simp [hmem]
    _ = ∫ u in Ioc s t, ∫ sample,
        sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure := by
      simpa only [sourceRawHistoryRateCell, sourceHistoryRateCellValue] using
        historyStrictRateIntegral_eq_elapsedCellIntegral
          (rate := safeSourceBulkRate hlam0 hlamHalf B x0 p0) index E hst

private theorem sourceHistoryNestedRateMass_eq_elapsedCellIntegral
    {lam B x0 p0 : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (index : HistoryCellIndex n) (E : Set (FiniteSample n))
    (hE : MeasurableSet E) (hst : s ≤ t) (hwidth : 0 < B) :
    sourceHistoryNestedRateMass B lam x0 p0
        (x0 + (s : ℝ)) (x0 + (t : ℝ))
        index.sourcePattern index.targetPattern index.history E =
      ∫ u in Ioc s t, ∫ sample,
        sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure := by
  exact (sourceHistoryNestedRateMass_eq_strictSafeRate
    (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0)
    (s := x0 + (s : ℝ)) (t := x0 + (t : ℝ))
    index.sourcePattern index.targetPattern index.history index.history_length_le E hE
    hlam0 hlamHalf hwidth (by
      exact le_add_of_nonneg_right (by exact_mod_cast s.2))).trans
    (sourceStrictSafeRateIntegral_eq_elapsedCellIntegral
      hlam0 hlamHalf index E hst)

private theorem targetStrictSafeRateIntegral_eq_elapsedCellIntegral
    {lam B x0 p0 : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (index : HistoryCellIndex n) (E : Set (FiniteSample n)) (hst : s ≤ t) :
    (∫ y in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), ∫ sample,
      {sample : FiniteSample n |
        HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
            index.targetPattern index.history y ∧ sample ∈ E}.indicator
        (fun _ ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0
          (Real.toNNReal (y - x0)) sample) sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume) =
      ∫ u in Ioc s t, ∫ sample,
        targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure := by
  calc
    (∫ y in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
              index.targetPattern index.history y ∧ sample ∈ E}.indicator
          (fun _ ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0
            (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume) =
      ∫ y in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
              index.targetPattern index.history y ∧ sample ∈ E}.indicator
          (fun sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0
            (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [] with sample
      by_cases hmem : HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
          index.targetPattern index.history y ∧ sample ∈ E <;> simp [hmem]
    _ = ∫ u in Ioc s t, ∫ sample,
        targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure := by
      simpa only [targetRawHistoryRateCell, targetHistoryRateCellValue] using
        historyStrictRateIntegral_eq_elapsedCellIntegral
          (rate := safeTargetBulkRate hlam0 hlamHalf B x0 p0) index E hst

private theorem targetHistoryNestedRateMass_eq_elapsedCellIntegral
    {lam B x0 p0 : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (index : HistoryCellIndex n) (E : Set (FiniteSample n))
    (hE : MeasurableSet E) (hst : s ≤ t) (hwidth : 0 < B) :
    targetHistoryNestedRateMass B lam x0 p0
        (x0 + (s : ℝ)) (x0 + (t : ℝ))
        index.sourcePattern index.targetPattern index.history E =
      ∫ u in Ioc s t, ∫ sample,
        targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure := by
  exact (targetHistoryNestedRateMass_eq_strictSafeRate
    (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0)
    (s := x0 + (s : ℝ)) (t := x0 + (t : ℝ))
    index.sourcePattern index.targetPattern index.history index.history_length_le E hE
    hlam0 hlamHalf hwidth (by
      exact le_add_of_nonneg_right (by exact_mod_cast s.2))).trans
    (targetStrictSafeRateIntegral_eq_elapsedCellIntegral
      hlam0 hlamHalf index E hst)

/-! ## Finite-sum/Fubini helpers -/

set_option linter.unusedVariables false in
private theorem sourceRawHistoryRateCell_sum_eq_sampleOuter
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (E : Set (FiniteSample n)) (hE : MeasurableSet E)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
      if index.history.length = m.val then
        ∫ u in Ioc s t, ∫ sample,
          sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure
      else 0) =
      ∫ sample in E, ∫ u in Ioc s t,
        safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample ∂timeMeasure
          ∂(finiteSampleLaw n) := by
  classical
  let : SFinite timeMeasure := by
    dsimp [timeMeasure]
    infer_instance
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  have hcellProd (index : HistoryCellIndex n) :
      Integrable
        (fun z : ℝ≥0 × FiniteSample n ↦
          sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E z.1 z.2)
        (timeMeasure.prod μ) := by
    simpa [μ] using sourceRawHistoryRateCell_product_integrable
      hlam0 hlamHalf index E hE
  have hcellTime (index : HistoryCellIndex n) :
      Integrable
        (fun u : ℝ≥0 ↦ ∫ sample,
          sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ)
        (timeMeasure.restrict (Ioc s t)) := by
    exact (hcellProd index).integral_prod_left.mono_measure Measure.restrict_le_self
  have hcellSample (index : HistoryCellIndex n) (u : ℝ≥0) :
      Integrable
        (fun sample : FiniteSample n ↦
          sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample) μ := by
    simpa [μ] using sourceRawHistoryRateCell_section_integrable
      hlam0 hlamHalf index E hE u
  have hsumIndex (m : Fin (2 * n)) :
      (∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ u in Ioc s t, ∫ sample,
            sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
              ∂timeMeasure
        else 0) =
        ∫ u in Ioc s t, ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∫ sample,
              sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
          else 0 ∂timeMeasure := by
    symm
    rw [integral_finsetSum (μ := timeMeasure.restrict (Ioc s t))
      (s := (Finset.univ : Finset (HistoryCellIndex n)))
      (fun index hindex ↦ by
        by_cases hlen : index.history.length = m.val
        · simp only [ite_eq_left hlen]
          exact hcellTime index
        · simp only [ite_eq_right hlen]
          exact integrable_zero ℝ≥0 ℝ (timeMeasure.restrict (Ioc s t)))]
    apply Finset.sum_congr rfl
    intro index hindex
    by_cases hlen : index.history.length = m.val <;> simp [hlen]
  have hsumM :
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ u in Ioc s t, ∫ sample,
            sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
              ∂timeMeasure
        else 0) =
      ∫ u in Ioc s t, ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ sample,
            sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
        else 0 ∂timeMeasure := by
    calc
      _ = ∑ m : Fin (2 * n), ∫ u in Ioc s t, ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∫ sample,
              sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
          else 0 ∂timeMeasure := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hsumIndex m
      _ = _ := by
        symm
        rw [integral_finsetSum (μ := timeMeasure.restrict (Ioc s t))
          (s := (Finset.univ : Finset (Fin (2 * n))))
          (fun m hm ↦ by
            refine integrable_finsetSum (μ := timeMeasure.restrict (Ioc s t))
              (s := (Finset.univ : Finset (HistoryCellIndex n))) ?_
            intro index hindex
            by_cases hlen : index.history.length = m.val
            · simp only [ite_eq_left hlen]
              exact hcellTime index
            · simp only [ite_eq_right hlen]
              exact integrable_zero ℝ≥0 ℝ (timeMeasure.restrict (Ioc s t)))]
  rw [hsumM]
  have hsampleSum (u : ℝ≥0) :
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ sample,
            sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
        else 0) =
      ∫ sample, ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
        else 0 ∂μ := by
    calc
      _ = ∑ m : Fin (2 * n), ∫ sample, ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          else 0 ∂μ := by
            apply Finset.sum_congr rfl
            intro m hm
            symm
            rw [integral_finsetSum (μ := μ)
              (s := (Finset.univ : Finset (HistoryCellIndex n)))
              (fun index hindex ↦ by
                by_cases hlen : index.history.length = m.val
                · simp only [ite_eq_left hlen]
                  exact hcellSample index u
                · simp only [ite_eq_right hlen]
                  exact integrable_zero (FiniteSample n) ℝ μ)]
            apply Finset.sum_congr rfl
            intro index hindex
            by_cases hlen : index.history.length = m.val <;> simp [hlen]
      _ = _ := by
        symm
        rw [integral_finsetSum (μ := μ)
          (s := (Finset.univ : Finset (Fin (2 * n))))
          (fun m hm ↦ by
            refine integrable_finsetSum (μ := μ)
              (s := (Finset.univ : Finset (HistoryCellIndex n))) ?_
            intro index hindex
            by_cases hlen : index.history.length = m.val
            · simp only [ite_eq_left hlen]
              exact hcellSample index u
            · simp only [ite_eq_right hlen]
              exact integrable_zero (FiniteSample n) ℝ μ)]
  have hpartition :
      ∀ᵐ u ∂(timeMeasure.restrict (Ioc s t)),
        (∫ sample, ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          else 0 ∂μ) =
        ∫ sample, E.indicator
          (fun sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample) sample ∂μ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    have hu0 : 0 < u := lt_of_le_of_lt bot_le hu.1
    have hpart := sum_step_historyBeforeCell_sourceBulkRate_ae
      (n := n) (B := B) (x0 := x0) (p0 := p0) hlam0 hlamHalf u hu0
    apply integral_congr_ae
    filter_upwards [hpart] with sample hsamp
    by_cases hsample : sample ∈ E
    · have hcell (index : HistoryCellIndex n) :
          sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample =
            (historyBeforeCell index lam x0 p0
              (FiniteSample.elapsedFeedbackCoordinate x0 u)).indicator
              (fun sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample) sample := by
          by_cases hmem : HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
            index.targetPattern index.history (x0 + (u : ℝ))
          · have hmemCell : sample ∈ historyBeforeCell index lam x0 p0
                (FiniteSample.elapsedFeedbackCoordinate x0 u) := by
              change HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
                index.targetPattern index.history (x0 + (u : ℝ))
              exact hmem
            simp [sourceRawHistoryRateCell, sourceHistoryRateCellValue, hsample, hmem,
              hmemCell]
          · have hmemCell : sample ∉ historyBeforeCell index lam x0 p0
                (FiniteSample.elapsedFeedbackCoordinate x0 u) := by
              intro h
              apply hmem
              change HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
                index.targetPattern index.history (x0 + (u : ℝ)) at h
              exact h
            simp [sourceRawHistoryRateCell, sourceHistoryRateCellValue, hsample, hmem,
              hmemCell]
      simp_rw [hcell]
      rw [Set.indicator_of_mem hsample]
      exact hsamp
    · simp [sourceRawHistoryRateCell, sourceHistoryRateCellValue, hsample]
  have hsampleSumAe :
      ∀ᵐ u ∂(timeMeasure.restrict (Ioc s t)),
        (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∫ sample,
              sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
          else 0) =
        ∫ sample, ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          else 0 ∂μ := Filter.Eventually.of_forall hsampleSum
  rw [integral_congr_ae hsampleSumAe, integral_congr_ae hpartition]
  let P : Set (ℝ≥0 × FiniteSample n) := Ioc s t ×ˢ E
  have hP : MeasurableSet P := measurableSet_Ioc.prod hE
  have hprod := safeSourceBulkRate_product_integrable
    (n := n) hlam0 hlamHalf B x0 p0
  have hprodP := hprod.indicator hP
  have htime :
      (∫ u in Ioc s t, ∫ sample, E.indicator
          (fun sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample) sample ∂μ
        ∂timeMeasure) =
        ∫ u in Ioc s t, ∫ sample,
          P.indicator (Function.uncurry
            (safeSourceBulkRate hlam0 hlamHalf B x0 p0)) (u, sample) ∂μ
          ∂timeMeasure := by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    apply integral_congr_ae
    filter_upwards [] with sample
    by_cases hsample : sample ∈ E
    · simp [P, hsample, hu, Function.uncurry_apply_pair]
    · simp [P, hsample]
  have hswap := integral_prod_symm (P.indicator
      (Function.uncurry (safeSourceBulkRate hlam0 hlamHalf B x0 p0))) hprodP
  calc
    _ = ∫ u in Ioc s t, ∫ sample,
        P.indicator (Function.uncurry
          (safeSourceBulkRate hlam0 hlamHalf B x0 p0)) (u, sample) ∂μ
          ∂timeMeasure := htime
    _ =
        ∫ z, P.indicator
          (Function.uncurry (safeSourceBulkRate hlam0 hlamHalf B x0 p0)) z
          ∂(timeMeasure.prod μ) := by
            rw [← integral_indicator measurableSet_Ioc]
            calc
              (∫ u, (Ioc s t).indicator
                  (fun u ↦ ∫ sample,
                    P.indicator (Function.uncurry
                      (safeSourceBulkRate hlam0 hlamHalf B x0 p0)) (u, sample) ∂μ) u
                    ∂timeMeasure) =
                  ∫ u, ∫ sample,
                    P.indicator (Function.uncurry
                      (safeSourceBulkRate hlam0 hlamHalf B x0 p0)) (u, sample) ∂μ
                    ∂timeMeasure := by
                apply integral_congr_ae
                filter_upwards [] with u
                by_cases hu : u ∈ Ioc s t
                · simp [Set.indicator_of_mem hu]
                · simp [P, hu]
              _ = _ := (integral_prod _ hprodP).symm
    _ = ∫ sample, ∫ u, P.indicator
        (Function.uncurry (safeSourceBulkRate hlam0 hlamHalf B x0 p0)) (u, sample)
          ∂timeMeasure ∂μ := hswap
    _ = ∫ sample in E, ∫ u in Ioc s t,
        safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample ∂timeMeasure ∂μ := by
          rw [← integral_indicator hE]
          apply integral_congr_ae
          filter_upwards [] with sample
          by_cases hsample : sample ∈ E
          · rw [Set.indicator_of_mem hsample]
            rw [← integral_indicator measurableSet_Ioc]
            apply integral_congr_ae
            filter_upwards [] with u
            by_cases hu : u ∈ Ioc s t <;>
              simp [P, hsample, hu, Function.uncurry_apply_pair]
          · simp [P, hsample]

set_option linter.unusedVariables false in
private theorem targetRawHistoryRateCell_sum_eq_sampleOuter
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (E : Set (FiniteSample n)) (hE : MeasurableSet E)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
      if index.history.length = m.val then
        ∫ u in Ioc s t, ∫ sample,
          targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂timeMeasure
      else 0) =
      ∫ sample in E, ∫ u in Ioc s t,
        safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample ∂timeMeasure
          ∂(finiteSampleLaw n) := by
  classical
  let : SFinite timeMeasure := by
    dsimp [timeMeasure]
    infer_instance
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  have hcellProd (index : HistoryCellIndex n) :
      Integrable
        (fun z : ℝ≥0 × FiniteSample n ↦
          targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E z.1 z.2)
        (timeMeasure.prod μ) := by
    simpa [μ] using targetRawHistoryRateCell_product_integrable
      hlam0 hlamHalf index E hE
  have hcellTime (index : HistoryCellIndex n) :
      Integrable
        (fun u : ℝ≥0 ↦ ∫ sample,
          targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ)
        (timeMeasure.restrict (Ioc s t)) := by
    exact (hcellProd index).integral_prod_left.mono_measure Measure.restrict_le_self
  have hcellSample (index : HistoryCellIndex n) (u : ℝ≥0) :
      Integrable
        (fun sample : FiniteSample n ↦
          targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample) μ := by
    simpa [μ] using targetRawHistoryRateCell_section_integrable
      hlam0 hlamHalf index E hE u
  have hsumIndex (m : Fin (2 * n)) :
      (∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ u in Ioc s t, ∫ sample,
            targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
              ∂timeMeasure
        else 0) =
        ∫ u in Ioc s t, ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∫ sample,
              targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
          else 0 ∂timeMeasure := by
    symm
    rw [integral_finsetSum (μ := timeMeasure.restrict (Ioc s t))
      (s := (Finset.univ : Finset (HistoryCellIndex n)))
      (fun index hindex ↦ by
        by_cases hlen : index.history.length = m.val
        · simp only [ite_eq_left hlen]
          exact hcellTime index
        · simp only [ite_eq_right hlen]
          exact integrable_zero ℝ≥0 ℝ (timeMeasure.restrict (Ioc s t)))]
    apply Finset.sum_congr rfl
    intro index hindex
    by_cases hlen : index.history.length = m.val <;> simp [hlen]
  have hsumM :
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ u in Ioc s t, ∫ sample,
            targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
              ∂timeMeasure
        else 0) =
      ∫ u in Ioc s t, ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ sample,
            targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
        else 0 ∂timeMeasure := by
    calc
      _ = ∑ m : Fin (2 * n), ∫ u in Ioc s t, ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∫ sample,
              targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
          else 0 ∂timeMeasure := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hsumIndex m
      _ = _ := by
        symm
        rw [integral_finsetSum (μ := timeMeasure.restrict (Ioc s t))
          (s := (Finset.univ : Finset (Fin (2 * n))))
          (fun m hm ↦ by
            refine integrable_finsetSum (μ := timeMeasure.restrict (Ioc s t))
              (s := (Finset.univ : Finset (HistoryCellIndex n))) ?_
            intro index hindex
            by_cases hlen : index.history.length = m.val
            · simp only [ite_eq_left hlen]
              exact hcellTime index
            · simp only [ite_eq_right hlen]
              exact integrable_zero ℝ≥0 ℝ (timeMeasure.restrict (Ioc s t)))]
  rw [hsumM]
  have hsampleSum (u : ℝ≥0) :
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ sample,
            targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
        else 0) =
      ∫ sample, ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
        else 0 ∂μ := by
    calc
      _ = ∑ m : Fin (2 * n), ∫ sample, ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          else 0 ∂μ := by
            apply Finset.sum_congr rfl
            intro m hm
            symm
            rw [integral_finsetSum (μ := μ)
              (s := (Finset.univ : Finset (HistoryCellIndex n)))
              (fun index hindex ↦ by
                by_cases hlen : index.history.length = m.val
                · simp only [ite_eq_left hlen]
                  exact hcellSample index u
                · simp only [ite_eq_right hlen]
                  exact integrable_zero (FiniteSample n) ℝ μ)]
            apply Finset.sum_congr rfl
            intro index hindex
            by_cases hlen : index.history.length = m.val <;> simp [hlen]
      _ = _ := by
        symm
        rw [integral_finsetSum (μ := μ)
          (s := (Finset.univ : Finset (Fin (2 * n))))
          (fun m hm ↦ by
            refine integrable_finsetSum (μ := μ)
              (s := (Finset.univ : Finset (HistoryCellIndex n))) ?_
            intro index hindex
            by_cases hlen : index.history.length = m.val
            · simp only [ite_eq_left hlen]
              exact hcellSample index u
            · simp only [ite_eq_right hlen]
              exact integrable_zero (FiniteSample n) ℝ μ)]
  have hpartition :
      ∀ᵐ u ∂(timeMeasure.restrict (Ioc s t)),
        (∫ sample, ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          else 0 ∂μ) =
        ∫ sample, E.indicator
          (fun sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample) sample ∂μ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    have hu0 : 0 < u := lt_of_le_of_lt bot_le hu.1
    have hpart := sum_step_historyBeforeCell_targetBulkRate_ae
      (n := n) (B := B) (x0 := x0) (p0 := p0) hlam0 hlamHalf u hu0
    apply integral_congr_ae
    filter_upwards [hpart] with sample hsamp
    by_cases hsample : sample ∈ E
    · have hcell (index : HistoryCellIndex n) :
          targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample =
            (historyBeforeCell index lam x0 p0
              (FiniteSample.elapsedFeedbackCoordinate x0 u)).indicator
              (fun sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample) sample := by
          by_cases hmem : HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
            index.targetPattern index.history (x0 + (u : ℝ))
          · have hmemCell : sample ∈ historyBeforeCell index lam x0 p0
                (FiniteSample.elapsedFeedbackCoordinate x0 u) := by
              change HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
                index.targetPattern index.history (x0 + (u : ℝ))
              exact hmem
            simp [targetRawHistoryRateCell, targetHistoryRateCellValue, hsample, hmem,
              hmemCell]
          · have hmemCell : sample ∉ historyBeforeCell index lam x0 p0
                (FiniteSample.elapsedFeedbackCoordinate x0 u) := by
              intro h
              apply hmem
              change HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern
                index.targetPattern index.history (x0 + (u : ℝ)) at h
              exact h
            simp [targetRawHistoryRateCell, targetHistoryRateCellValue, hsample, hmem,
              hmemCell]
      simp_rw [hcell]
      rw [Set.indicator_of_mem hsample]
      exact hsamp
    · simp [targetRawHistoryRateCell, targetHistoryRateCellValue, hsample]
  have hsampleSumAe :
      ∀ᵐ u ∂(timeMeasure.restrict (Ioc s t)),
        (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∫ sample,
              targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
          else 0) =
        ∫ sample, ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample
          else 0 ∂μ := Filter.Eventually.of_forall hsampleSum
  rw [integral_congr_ae hsampleSumAe, integral_congr_ae hpartition]
  let P : Set (ℝ≥0 × FiniteSample n) := Ioc s t ×ˢ E
  have hP : MeasurableSet P := measurableSet_Ioc.prod hE
  have hprod := safeTargetBulkRate_product_integrable
    (n := n) hlam0 hlamHalf B x0 p0
  have hprodP := hprod.indicator hP
  have htime :
      (∫ u in Ioc s t, ∫ sample, E.indicator
          (fun sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample) sample ∂μ
        ∂timeMeasure) =
        ∫ u in Ioc s t, ∫ sample,
          P.indicator (Function.uncurry
            (safeTargetBulkRate hlam0 hlamHalf B x0 p0)) (u, sample) ∂μ
          ∂timeMeasure := by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with u hu
    apply integral_congr_ae
    filter_upwards [] with sample
    by_cases hsample : sample ∈ E
    · simp [P, hsample, hu, Function.uncurry_apply_pair]
    · simp [P, hsample]
  have hswap := integral_prod_symm (P.indicator
      (Function.uncurry (safeTargetBulkRate hlam0 hlamHalf B x0 p0))) hprodP
  calc
    _ = ∫ u in Ioc s t, ∫ sample,
        P.indicator (Function.uncurry
          (safeTargetBulkRate hlam0 hlamHalf B x0 p0)) (u, sample) ∂μ
          ∂timeMeasure := htime
    _ =
        ∫ z, P.indicator
          (Function.uncurry (safeTargetBulkRate hlam0 hlamHalf B x0 p0)) z
          ∂(timeMeasure.prod μ) := by
            rw [← integral_indicator measurableSet_Ioc]
            calc
              (∫ u, (Ioc s t).indicator
                  (fun u ↦ ∫ sample,
                    P.indicator (Function.uncurry
                      (safeTargetBulkRate hlam0 hlamHalf B x0 p0)) (u, sample) ∂μ) u
                    ∂timeMeasure) =
                  ∫ u, ∫ sample,
                    P.indicator (Function.uncurry
                      (safeTargetBulkRate hlam0 hlamHalf B x0 p0)) (u, sample) ∂μ
                    ∂timeMeasure := by
                apply integral_congr_ae
                filter_upwards [] with u
                by_cases hu : u ∈ Ioc s t
                · simp [Set.indicator_of_mem hu]
                · simp [P, hu]
              _ = _ := (integral_prod _ hprodP).symm
    _ = ∫ sample, ∫ u, P.indicator
        (Function.uncurry (safeTargetBulkRate hlam0 hlamHalf B x0 p0)) (u, sample)
          ∂timeMeasure ∂μ := hswap
    _ = ∫ sample in E, ∫ u in Ioc s t,
        safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample ∂timeMeasure ∂μ := by
          rw [← integral_indicator hE]
          apply integral_congr_ae
          filter_upwards [] with sample
          by_cases hsample : sample ∈ E
          · rw [Set.indicator_of_mem hsample]
            rw [← integral_indicator measurableSet_Ioc]
            apply integral_congr_ae
            filter_upwards [] with u
            by_cases hu : u ∈ Ioc s t <;>
              simp [P, hsample, hu, Function.uncurry_apply_pair]
          · simp [P, hsample]

/-! ## Public raw-rectangle identities -/

theorem finiteEventCountThinned_source_sub_setIntegral_eq_rawRectangle
    {lam B x0 p0 : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 s] E)
    (hst : s ≤ t) (hn : 0 < n) (hwidth : 0 < B) :
    (∫ sample in E,
      ((finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample : ℝ) -
        (finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample : ℝ))
      ∂(finiteSampleLaw n)) =
      ∫ sample in E, ∫ u in Ioc s t,
        safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample ∂timeMeasure
          ∂(finiteSampleLaw n) := by
  classical
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  have hxs : x0 ≤ x0 + (s : ℝ) := by
    exact le_add_of_nonneg_right (by exact_mod_cast s.2)
  have hse :
      (⟨(x0 + (s : ℝ)) - x0, sub_nonneg.mpr hxs⟩ : ℝ≥0) = s := by
    ext
    simp
  have hEcount : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨(x0 + (s : ℝ)) - x0, sub_nonneg.mpr hxs⟩] E := by
    rw [hse]
    exact hE
  have hcount := finiteEventCountThinned_source_sub_setIntegral_eq_historyCellIndex_nextLabel_real_sum
    (n := n) (lam := lam) (B := B) (x0 := x0) (p0 := p0)
    (r := x0 + (s : ℝ)) hlam0 hlamHalf hxs E hEcount hst
  have hcountReal :
      (∫ sample in E,
        ((finiteEventCountThinned
            (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample : ℝ) -
          (finiteEventCountThinned
            (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample : ℝ))
        ∂μ) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∑ i : Fin n,
            μ.real {sample : FiniteSample n |
              HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                  index.history ∧
                feedbackUnseenTuple
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) sample ∈
                  feedbackBulkNextEventSetOfLabel B lam
                    (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                      index.history)
                    (x0 + (s : ℝ)) (x0 + (t : ℝ))
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) (Sum.inl i) ∧ sample ∈ E}
        else 0 := by
    calc
      _ = ∫ sample in E,
          (((finiteEventCountThinned
              (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
              (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample -
            finiteEventCountThinned
              (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
              (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample : ℕ) : ℝ))
          ∂μ := by
            apply setIntegral_congr_fun
              ((FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le s E hE)
            intro sample hsample
            exact (Nat.cast_sub (finiteEventCountThinned_mono
              (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
              (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) sample hst)).symm
      _ = _ := by simpa [μ] using hcount
  rw [hcountReal]
  have hmass :
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∑ i : Fin n,
            μ.real {sample : FiniteSample n |
              HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                  index.history ∧
                feedbackUnseenTuple
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) sample ∈
                  feedbackBulkNextEventSetOfLabel B lam
                    (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                      index.history)
                    (x0 + (s : ℝ)) (x0 + (t : ℝ))
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) (Sum.inl i) ∧ sample ∈ E}
        else 0) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          sourceHistoryNestedRateMass B lam x0 p0 (x0 + (s : ℝ)) (x0 + (t : ℝ))
            index.sourcePattern index.targetPattern index.history E
        else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro index hi
    by_cases hlen : index.history.length = m.val
    · simp only [ite_eq_left hlen]
      simpa [μ] using finiteSample_sourceBulk_history_allLabel_eventMass_eq_rateMass
        (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0)
        (r := x0 + (s : ℝ)) (s := x0 + (s : ℝ)) (t := x0 + (t : ℝ))
        hlam0 hlamHalf index.sourcePattern index.targetPattern index.history hxs le_rfl E
        hEcount hn hwidth
    · simp only [ite_eq_right hlen]
  rw [hmass]
  have htransport :
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          sourceHistoryNestedRateMass B lam x0 p0 (x0 + (s : ℝ)) (x0 + (t : ℝ))
            index.sourcePattern index.targetPattern index.history E
        else 0) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ u in Ioc s t, ∫ sample,
            sourceRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
              ∂timeMeasure
        else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro index hi
    by_cases hlen : index.history.length = m.val
    · simp only [ite_eq_left hlen]
      exact sourceHistoryNestedRateMass_eq_elapsedCellIntegral
        hlam0 hlamHalf index E (by simpa [μ] using (show MeasurableSet E from
          (FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le s E hE))
        hst hwidth
    · simp only [ite_eq_right hlen]
  rw [htransport]
  exact sourceRawHistoryRateCell_sum_eq_sampleOuter
    (B := B) (x0 := x0) (p0 := p0) hlam0 hlamHalf E
    (by simpa [μ] using (show MeasurableSet E from
      (FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le s E hE)) hst

theorem finiteEventCountThinned_target_sub_setIntegral_eq_rawRectangle
    {lam B x0 p0 : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 s] E)
    (hst : s ≤ t) (hn : 0 < n) (hwidth : 0 < B) :
    (∫ sample in E,
      ((finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample : ℝ) -
        (finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample : ℝ))
      ∂(finiteSampleLaw n)) =
      ∫ sample in E, ∫ u in Ioc s t,
        safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample ∂timeMeasure
          ∂(finiteSampleLaw n) := by
  classical
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  have hxs : x0 ≤ x0 + (s : ℝ) := by
    exact le_add_of_nonneg_right (by exact_mod_cast s.2)
  have hse :
      (⟨(x0 + (s : ℝ)) - x0, sub_nonneg.mpr hxs⟩ : ℝ≥0) = s := by
    ext
    simp
  have hEcount : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨(x0 + (s : ℝ)) - x0, sub_nonneg.mpr hxs⟩] E := by
    rw [hse]
    exact hE
  have hcount := finiteEventCountThinned_target_sub_setIntegral_eq_historyCellIndex_nextLabel_real_sum
    (n := n) (lam := lam) (B := B) (x0 := x0) (p0 := p0)
    (r := x0 + (s : ℝ)) hlam0 hlamHalf hxs E hEcount hst
  have hcountReal :
      (∫ sample in E,
        ((finiteEventCountThinned
            (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample : ℝ) -
          (finiteEventCountThinned
            (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample : ℝ))
        ∂μ) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∑ j : Fin n,
            μ.real {sample : FiniteSample n |
              HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                  index.history ∧
                feedbackUnseenTuple
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) sample ∈
                  feedbackBulkNextEventSetOfLabel B lam
                    (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                      index.history)
                    (x0 + (s : ℝ)) (x0 + (t : ℝ))
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) (Sum.inr j) ∧ sample ∈ E}
        else 0 := by
    calc
      _ = ∫ sample in E,
          (((finiteEventCountThinned
              (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
              (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample -
            finiteEventCountThinned
              (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
              (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample : ℕ) : ℝ))
          ∂μ := by
            apply setIntegral_congr_fun
              ((FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le s E hE)
            intro sample hsample
            exact (Nat.cast_sub (finiteEventCountThinned_mono
              (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
              (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) sample hst)).symm
      _ = _ := by simpa [μ] using hcount
  rw [hcountReal]
  have hmass :
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∑ j : Fin n,
            μ.real {sample : FiniteSample n |
              HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                  index.history ∧
                feedbackUnseenTuple
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) sample ∈
                  feedbackBulkNextEventSetOfLabel B lam
                    (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                      index.history)
                    (x0 + (s : ℝ)) (x0 + (t : ℝ))
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) (Sum.inr j) ∧ sample ∈ E}
        else 0) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          targetHistoryNestedRateMass B lam x0 p0 (x0 + (s : ℝ)) (x0 + (t : ℝ))
            index.sourcePattern index.targetPattern index.history E
        else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro index hi
    by_cases hlen : index.history.length = m.val
    · simp only [ite_eq_left hlen]
      simpa [μ] using finiteSample_targetBulk_history_allLabel_eventMass_eq_rateMass
        (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0)
        (r := x0 + (s : ℝ)) (s := x0 + (s : ℝ)) (t := x0 + (t : ℝ))
        hlam0 hlamHalf index.sourcePattern index.targetPattern index.history hxs le_rfl E
        hEcount hn hwidth
    · simp only [ite_eq_right hlen]
  rw [hmass]
  have htransport :
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          targetHistoryNestedRateMass B lam x0 p0 (x0 + (s : ℝ)) (x0 + (t : ℝ))
            index.sourcePattern index.targetPattern index.history E
        else 0) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∫ u in Ioc s t, ∫ sample,
            targetRawHistoryRateCell hlam0 hlamHalf B x0 p0 index E u sample ∂μ
              ∂timeMeasure
        else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro index hi
    by_cases hlen : index.history.length = m.val
    · simp only [ite_eq_left hlen]
      exact targetHistoryNestedRateMass_eq_elapsedCellIntegral
        hlam0 hlamHalf index E (by simpa [μ] using (show MeasurableSet E from
          (FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le s E hE))
        hst hwidth
    · simp only [ite_eq_right hlen]
  rw [htransport]
  exact targetRawHistoryRateCell_sum_eq_sampleOuter
    (B := B) (x0 := x0) (p0 := p0) hlam0 hlamHalf E
    (by simpa [μ] using (show MeasurableSet E from
      (FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le s E hE)) hst

end OTSelector
