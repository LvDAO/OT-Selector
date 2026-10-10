import OTSelector.Feedback.FeedbackMarkedHistorySum
import OTSelector.Feedback.FeedbackMarkedMeanMartingale
import OTSelector.Probability.BoundedUsualMartingale
import OTSelector.Probability.SpatialMartingaleAverage

/-!
# Actual finite geometric-mark compensated martingales

The centered next-mark law gives a bounded innovation martingale on the original finite sample
law. Adding the already proved predictable conditional-mean transform gives the compensator
for the true geometric marks. No marked-intensity or martingale premise is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical NNReal Topology

namespace OTSelector.FiniteSample

open CountingProcess

variable {n : ℕ} {lam : ℝ}

theorem safeSourceBulkCenteredMarkSum_eq_markSum_sub_countingIntegral
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample =
      safeSourceBulkMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
        countingIntegral (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
          (fun u sample ↦ sourceFeedbackMarkMean
            (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ) t sample := by
  classical
  have hc := countingIntegral_finiteEventCountTop_eq_sum
    (fun i : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i)
    (fun u sample ↦ sourceFeedbackMarkMean
      (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ)
    sample t (safeSourceBulkEventTime_injective hlam0 hlamHalf B x0 p0 sample)
  change countingIntegral (safeSourceBulkCount hlam0 hlamHalf B x0 p0) _ _ _ = _ at hc
  rw [hc]
  unfold safeSourceBulkCenteredMarkSum safeSourceBulkMarkSum finiteEventWeightedSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (if safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample ≤ ↑t
    then ψ (sample.sourceMark i) - sourceFeedbackMarkMean
      (safePreFeedbackSlope hlam0 hlamHalf x0 p0
        (finiteEventTimeValue (fun j ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 j)
          sample i) sample) ψ else 0) =
    (if safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample ≤ ↑t
      then ψ (sample.sourceMark i) else 0) -
    (if safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample ≤ ↑t
      then sourceFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0
        (finiteEventTimeValue (fun j ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 j)
          sample i) sample) ψ else 0)
  split_ifs <;> ring

theorem safeSourceBulkCenteredMarkSum_stronglyAdapted
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    StronglyAdapted (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ) := by
  have hcount := finiteEvent_countingIntegral_stronglyAdapted
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
    (fun i : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i)
    (safeSourceBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0)
    (safeSourceBulkEventTime_injective hlam0 hlamHalf B x0 p0)
    (sourceFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
      hlam0 hlamHalf x0 p0 ψ hψ hC hbound)
  intro t
  have hsub := (safeSourceBulkMarkSum_stronglyAdapted hlam0 hlamHalf B x0 p0 ψ hψ.measurable t).sub
    (hcount t)
  convert hsub using 1
  funext sample
  exact safeSourceBulkCenteredMarkSum_eq_markSum_sub_countingIntegral
    hlam0 hlamHalf B x0 p0 ψ t sample

theorem norm_safeSourceBulkCenteredMarkSum_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) (t : ℝ≥0) (sample : FiniteSample n) :
    ‖safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample‖ ≤ (n : ℝ) * (2 * C) := by
  apply norm_finiteEventWeightedSum_le _ _ (by positivity)
  intro i sample
  unfold safeSourceBulkCenteredMarkWeight
  have hm : ‖sourceFeedbackMarkMean
      (safePreFeedbackSlope hlam0 hlamHalf x0 p0
        (finiteEventTimeValue (fun j : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 j)
          sample i) sample) ψ‖ ≤ C :=
    norm_sourceFeedbackMarkMean_le hlam0 hlamHalf (abs_feedbackSlope_le hlam0) ψ hψ hbound
  exact (norm_sub_le _ _).trans (by linarith [hbound (sample.sourceMark i)])

/-- The raw rectangle identity follows from the actual finite history disintegration. -/
theorem setIntegral_safeSourceBulkCenteredMarkSum_increment_eq_zero
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C)
    {s t : ℝ≥0} (hst : s ≤ t) (E : Set (FiniteSample n))
    (hE : MeasurableSet[rawRevealedFiltration hlam0 hlamHalf x0 p0 s] E) :
    (∫ sample in E, safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
      safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ s sample
        ∂(finiteSampleLaw n)) = 0 := by
  classical
  let term (index : HistoryCellIndex n) (i : Fin n) := feedbackCenteredHistoryTerm
    B lam x0 p0 (x0 + (s : ℝ)) (x0 + (t : ℝ)) index.sourcePattern
      index.targetPattern index.history (Sum.inl i) ψ
  have hi (index : HistoryCellIndex n) (i : Fin n) :
      Integrable (term index i) ((finiteSampleLaw n : Measure (FiniteSample n)).restrict E) :=
    (integrable_feedbackCenteredHistoryTerm hlam0 hlamHalf index.sourcePattern
      index.targetPattern index.history (Sum.inl i) ψ hψ hC hbound).integrableOn
  have hisum (m : Fin (2 * n)) (index : HistoryCellIndex n) :
      Integrable (fun sample ↦ if index.history.length = m.val then
        ∑ i : Fin n, term index i sample else 0)
        ((finiteSampleLaw n : Measure (FiniteSample n)).restrict E) := by
    split_ifs
    · exact integrable_finsetSum _ (fun i _ ↦ hi index i)
    · exact integrable_const (0 : ℝ)
  have heq : (fun sample ↦ safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
      safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ s sample) =ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n)).restrict E]
      (fun sample ↦ ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then ∑ i : Fin n, term index i sample else 0) := by
    apply ae_restrict_of_ae
    filter_upwards [finiteSampleLaw_noFeedbackTies_ae (n := n) (x0 := x0) (p0 := p0)
      hlam0 hlamHalf] with sample hgood
    exact safeSourceBulkCenteredMarkSum_sub_eq_history
      sample hlam0 hlamHalf B x0 p0 ψ hgood hst
  rw [integral_congr_ae heq,
    integral_finsetSum _ (fun m _ ↦ integrable_finsetSum _ (fun index _ ↦ hisum m index))]
  apply Finset.sum_eq_zero
  intro m _
  rw [integral_finsetSum _ (fun index _ ↦ hisum m index)]
  apply Finset.sum_eq_zero
  intro index _
  by_cases hlen : index.history.length = m.val
  · simp only [ite_eq_left hlen]
    rw [integral_finsetSum _ (fun i _ ↦ hi index i)]
    apply Finset.sum_eq_zero
    intro i _
    have hr : x0 ≤ x0 + (s : ℝ) := le_add_of_nonneg_right s.property
    have hE' : MeasurableSet[rawRevealedFiltration hlam0 hlamHalf x0 p0
        ⟨x0 + (s : ℝ) - x0, sub_nonneg.mpr hr⟩] E := by
      have he : (⟨x0 + (s : ℝ) - x0, sub_nonneg.mpr hr⟩ : ℝ≥0) = s := by
        apply Subtype.ext
        simp
      rw [he]
      exact hE
    exact setIntegral_feedbackCenteredHistoryTerm_eq_zero hlam0 hlamHalf
      index.sourcePattern index.targetPattern index.history hr le_rfl E hE'
      (Sum.inl i) hn hB ψ hψ hbound
  · simp only [ite_eq_right hlen, integral_zero]

/-- A centered geometric-mark innovation is a martingale under the actual finite sample law. -/
theorem safeSourceBulkCenteredMarkSum_martingale
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Martingale (safeSourceBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) (finiteSampleLaw n) := by
  apply OTSelector.Probability.martingale_usualAugmentation_of_bounded_raw
    (finiteSampleLaw n : Measure (FiniteSample n))
    (rawRevealedFiltration hlam0 hlamHalf x0 p0)
  · exact safeSourceBulkCenteredMarkSum_stronglyAdapted
      hlam0 hlamHalf B x0 p0 ψ hψ hC hbound
  · exact norm_safeSourceBulkCenteredMarkSum_le hlam0 hlamHalf B x0 p0 ψ hψ hC hbound
  · exact fun sample t ↦ finiteEventWeightedSum_rightContinuous _ _ sample t
  · intro s t hst E hE
    exact setIntegral_safeSourceBulkCenteredMarkSum_increment_eq_zero
      hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound hst E hE

/-- The actual source geometric-mark sum minus its predictable mark compensator. -/
noncomputable def safeSourceBulkMarkedCompensator
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeSourceBulkMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
    integratedIntensity (safeSourceBulkRate hlam0 hlamHalf B x0 p0)
      (fun u sample ↦ sourceFeedbackMarkMean
        (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ) t sample

/-- The full marked compensation is proved from the original finite law and actual intensity. -/
theorem safeSourceBulkMarkedCompensator_martingale
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Martingale (safeSourceBulkMarkedCompensator hlam0 hlamHalf B x0 p0 ψ)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) (finiteSampleLaw n) := by
  have h := (safeSourceBulkCenteredMarkSum_martingale
    hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound).add
      (safeSourceBulk_markMean_compensated_martingale
        (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB ψ hψ hC hbound)
  convert h using 1
  funext t sample
  simp only [Pi.add_apply, safeSourceBulkMarkedCompensator,
    safeSourceBulkCenteredMarkSum_eq_markSum_sub_countingIntegral, compensatedIntegral]
  ring

theorem safeTargetBulkCenteredMarkSum_eq_markSum_sub_countingIntegral
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample =
      safeTargetBulkMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
        countingIntegral (safeTargetBulkCount hlam0 hlamHalf B x0 p0)
          (fun u sample ↦ targetFeedbackMarkMean
            (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ) t sample := by
  classical
  have hc := countingIntegral_finiteEventCountTop_eq_sum
    (fun i : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i)
    (fun u sample ↦ targetFeedbackMarkMean
      (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ)
    sample t (safeTargetBulkEventTime_injective hlam0 hlamHalf B x0 p0 sample)
  change countingIntegral (safeTargetBulkCount hlam0 hlamHalf B x0 p0) _ _ _ = _ at hc
  rw [hc]
  unfold safeTargetBulkCenteredMarkSum safeTargetBulkMarkSum finiteEventWeightedSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (if safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i sample ≤ ↑t
    then ψ (sample.targetMark i) - targetFeedbackMarkMean
      (safePreFeedbackSlope hlam0 hlamHalf x0 p0
        (finiteEventTimeValue (fun j ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j)
          sample i) sample) ψ else 0) =
    (if safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i sample ≤ ↑t
      then ψ (sample.targetMark i) else 0) -
    (if safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i sample ≤ ↑t
      then targetFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0
        (finiteEventTimeValue (fun j ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j)
          sample i) sample) ψ else 0)
  split_ifs <;> ring

theorem safeTargetBulkCenteredMarkSum_stronglyAdapted
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    StronglyAdapted (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ) := by
  have hcount := finiteEvent_countingIntegral_stronglyAdapted
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
    (fun i : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 i)
    (safeTargetBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0)
    (safeTargetBulkEventTime_injective hlam0 hlamHalf B x0 p0)
    (targetFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
      hlam0 hlamHalf x0 p0 ψ hψ hC hbound)
  intro t
  have hsub := (safeTargetBulkMarkSum_stronglyAdapted hlam0 hlamHalf B x0 p0 ψ hψ.measurable t).sub
    (hcount t)
  convert hsub using 1
  funext sample
  exact safeTargetBulkCenteredMarkSum_eq_markSum_sub_countingIntegral
    hlam0 hlamHalf B x0 p0 ψ t sample

theorem norm_safeTargetBulkCenteredMarkSum_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) (t : ℝ≥0) (sample : FiniteSample n) :
    ‖safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample‖ ≤ (n : ℝ) * (2 * C) := by
  apply norm_finiteEventWeightedSum_le _ _ (by positivity)
  intro i sample
  unfold safeTargetBulkCenteredMarkWeight
  have hm : ‖targetFeedbackMarkMean
      (safePreFeedbackSlope hlam0 hlamHalf x0 p0
        (finiteEventTimeValue (fun j : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j)
          sample i) sample) ψ‖ ≤ C :=
    norm_targetFeedbackMarkMean_le hlam0 hlamHalf (abs_feedbackSlope_le hlam0) ψ hψ hbound
  exact (norm_sub_le _ _).trans (by linarith [hbound (sample.targetMark i)])

/-- The raw rectangle identity follows from the actual finite history disintegration. -/
theorem setIntegral_safeTargetBulkCenteredMarkSum_increment_eq_zero
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C)
    {s t : ℝ≥0} (hst : s ≤ t) (E : Set (FiniteSample n))
    (hE : MeasurableSet[rawRevealedFiltration hlam0 hlamHalf x0 p0 s] E) :
    (∫ sample in E, safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
      safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ s sample
        ∂(finiteSampleLaw n)) = 0 := by
  classical
  let term (index : HistoryCellIndex n) (i : Fin n) := feedbackCenteredHistoryTerm
    B lam x0 p0 (x0 + (s : ℝ)) (x0 + (t : ℝ)) index.sourcePattern
      index.targetPattern index.history (Sum.inr i) ψ
  have hi (index : HistoryCellIndex n) (i : Fin n) :
      Integrable (term index i) ((finiteSampleLaw n : Measure (FiniteSample n)).restrict E) :=
    (integrable_feedbackCenteredHistoryTerm hlam0 hlamHalf index.sourcePattern
      index.targetPattern index.history (Sum.inr i) ψ hψ hC hbound).integrableOn
  have hisum (m : Fin (2 * n)) (index : HistoryCellIndex n) :
      Integrable (fun sample ↦ if index.history.length = m.val then
        ∑ i : Fin n, term index i sample else 0)
        ((finiteSampleLaw n : Measure (FiniteSample n)).restrict E) := by
    split_ifs
    · exact integrable_finsetSum _ (fun i _ ↦ hi index i)
    · exact integrable_const (0 : ℝ)
  have heq : (fun sample ↦ safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
      safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ s sample) =ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n)).restrict E]
      (fun sample ↦ ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then ∑ i : Fin n, term index i sample else 0) := by
    apply ae_restrict_of_ae
    filter_upwards [finiteSampleLaw_noFeedbackTies_ae (n := n) (x0 := x0) (p0 := p0)
      hlam0 hlamHalf] with sample hgood
    exact safeTargetBulkCenteredMarkSum_sub_eq_history
      sample hlam0 hlamHalf B x0 p0 ψ hgood hst
  rw [integral_congr_ae heq,
    integral_finsetSum _ (fun m _ ↦ integrable_finsetSum _ (fun index _ ↦ hisum m index))]
  apply Finset.sum_eq_zero
  intro m _
  rw [integral_finsetSum _ (fun index _ ↦ hisum m index)]
  apply Finset.sum_eq_zero
  intro index _
  by_cases hlen : index.history.length = m.val
  · simp only [ite_eq_left hlen]
    rw [integral_finsetSum _ (fun i _ ↦ hi index i)]
    apply Finset.sum_eq_zero
    intro i _
    have hr : x0 ≤ x0 + (s : ℝ) := le_add_of_nonneg_right s.property
    have hE' : MeasurableSet[rawRevealedFiltration hlam0 hlamHalf x0 p0
        ⟨x0 + (s : ℝ) - x0, sub_nonneg.mpr hr⟩] E := by
      have he : (⟨x0 + (s : ℝ) - x0, sub_nonneg.mpr hr⟩ : ℝ≥0) = s := by
        apply Subtype.ext
        simp
      rw [he]
      exact hE
    exact setIntegral_feedbackCenteredHistoryTerm_eq_zero hlam0 hlamHalf
      index.sourcePattern index.targetPattern index.history hr le_rfl E hE'
      (Sum.inr i) hn hB ψ hψ hbound
  · simp only [ite_eq_right hlen, integral_zero]

/-- A centered geometric-mark innovation is a martingale under the actual finite sample law. -/
theorem safeTargetBulkCenteredMarkSum_martingale
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Martingale (safeTargetBulkCenteredMarkSum hlam0 hlamHalf B x0 p0 ψ)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) (finiteSampleLaw n) := by
  apply OTSelector.Probability.martingale_usualAugmentation_of_bounded_raw
    (finiteSampleLaw n : Measure (FiniteSample n))
    (rawRevealedFiltration hlam0 hlamHalf x0 p0)
  · exact safeTargetBulkCenteredMarkSum_stronglyAdapted
      hlam0 hlamHalf B x0 p0 ψ hψ hC hbound
  · exact norm_safeTargetBulkCenteredMarkSum_le hlam0 hlamHalf B x0 p0 ψ hψ hC hbound
  · exact fun sample t ↦ finiteEventWeightedSum_rightContinuous _ _ sample t
  · intro s t hst E hE
    exact setIntegral_safeTargetBulkCenteredMarkSum_increment_eq_zero
      hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound hst E hE

/-- The actual target geometric-mark sum minus its predictable mark compensator. -/
noncomputable def safeTargetBulkMarkedCompensator
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeTargetBulkMarkSum hlam0 hlamHalf B x0 p0 ψ t sample -
    integratedIntensity (safeTargetBulkRate hlam0 hlamHalf B x0 p0)
      (fun u sample ↦ targetFeedbackMarkMean
        (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ) t sample

/-- The full marked compensation is proved from the original finite law and actual intensity. -/
theorem safeTargetBulkMarkedCompensator_martingale
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Martingale (safeTargetBulkMarkedCompensator hlam0 hlamHalf B x0 p0 ψ)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) (finiteSampleLaw n) := by
  have h := (safeTargetBulkCenteredMarkSum_martingale
    hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound).add
      (safeTargetBulk_markMean_compensated_martingale
        (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB ψ hψ hC hbound)
  convert h using 1
  funext t sample
  simp only [Pi.add_apply, safeTargetBulkMarkedCompensator,
    safeTargetBulkCenteredMarkSum_eq_markSum_sub_countingIntegral, compensatedIntegral]
  ring

end OTSelector.FiniteSample
