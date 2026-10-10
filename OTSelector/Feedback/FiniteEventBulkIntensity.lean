import OTSelector.Feedback.FiniteEventBulkCount
import OTSelector.Feedback.FiniteEventBulkRawRectangle
import OTSelector.Feedback.FeedbackBulkGlobalIntegrable
import OTSelector.Probability.CountingProcess.FiniteEventRawIntensity

/-!
# Actual intensities of the finite bulk feedback counts

The source and target event families are thinned by the same predictable bulk mask used in their
candidate rates.  The raw finite-history rectangle identities therefore instantiate the generic
finite-event intensity theorem without any martingale or intensity premise.
-/

open MeasureTheory Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace OTSelector

open CountingProcess

namespace FiniteSample

variable {n : ℕ}

/-- The actual safe source bulk count has the predictable safe source bulk rate as intensity. -/
theorem safeSourceBulkCount_hasPredictableIntensity
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (hB : 0 < B) :
    HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n))
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeSourceBulkCount hlam0 hlamHalf B x0 p0 t sample)
      (fun t sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample) := by
  have h := hasPredictableIntensity_of_finiteEvent_raw_countIncrement
    (finiteSampleLaw n : Measure (FiniteSample n))
    (rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
    (fun i : Fin n ↦ safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i)
    (fun i ↦ safeSourceBulkEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf B x0 p0 i)
    (fun i sample ↦ safeSourceBulkEventTime_eq_top_or_pos
      (n := n) hlam0 hlamHalf B x0 p0 sample i)
    (safeSourceBulkEventTime_injective (n := n) hlam0 hlamHalf B x0 p0)
    (fun t sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample)
    (safeSourceBulkRate_predictable (n := n) hlam0 hlamHalf B x0 p0)
    (feedbackBulkRateCap_nonneg n B)
    (fun t sample ↦ safeSourceBulkRate_nonneg hlam0 hlamHalf B x0 p0 t sample)
    (fun t sample ↦ safeSourceBulkRate_le_cap hlam0 hlamHalf B x0 p0 t sample)
    (fun t sample ↦ safeSourceBulkRate_integrableOn
      hlam0 hlamHalf B x0 p0 t sample)
    (safeSourceBulkRate_product_integrable hlam0 hlamHalf B x0 p0)
    (fun hst E hE ↦ by
      simpa only [safeSourceBulkEventTime, finiteEventCountThinned] using
        finiteEventCountThinned_source_sub_setIntegral_eq_rawRectangle
          hlam0 hlamHalf E hE hst hn hB)
  simpa only [usualRevealedFiltration, safeSourceBulkCount, finiteEventCountThinned,
    safeSourceBulkEventTime] using h

/-- The actual safe target bulk count has the predictable safe target bulk rate as intensity. -/
theorem safeTargetBulkCount_hasPredictableIntensity
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (hB : 0 < B) :
    HasPredictableIntensity
      (finiteSampleLaw n : Measure (FiniteSample n))
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeTargetBulkCount hlam0 hlamHalf B x0 p0 t sample)
      (fun t sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample) := by
  have h := hasPredictableIntensity_of_finiteEvent_raw_countIncrement
    (finiteSampleLaw n : Measure (FiniteSample n))
    (rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
    (fun j : Fin n ↦ safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j)
    (fun j ↦ safeTargetBulkEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf B x0 p0 j)
    (fun j sample ↦ safeTargetBulkEventTime_eq_top_or_pos
      (n := n) hlam0 hlamHalf B x0 p0 sample j)
    (safeTargetBulkEventTime_injective (n := n) hlam0 hlamHalf B x0 p0)
    (fun t sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample)
    (safeTargetBulkRate_predictable (n := n) hlam0 hlamHalf B x0 p0)
    (feedbackBulkRateCap_nonneg n B)
    (fun t sample ↦ safeTargetBulkRate_nonneg hlam0 hlamHalf B x0 p0 t sample)
    (fun t sample ↦ safeTargetBulkRate_le_cap hlam0 hlamHalf B x0 p0 t sample)
    (fun t sample ↦ safeTargetBulkRate_integrableOn
      hlam0 hlamHalf B x0 p0 t sample)
    (safeTargetBulkRate_product_integrable hlam0 hlamHalf B x0 p0)
    (fun hst E hE ↦ by
      simpa only [safeTargetBulkEventTime, finiteEventCountThinned] using
        finiteEventCountThinned_target_sub_setIntegral_eq_rawRectangle
          hlam0 hlamHalf E hE hst hn hB)
  simpa only [usualRevealedFiltration, safeTargetBulkCount, finiteEventCountThinned,
    safeTargetBulkEventTime] using h

end FiniteSample

end OTSelector
