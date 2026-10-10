import OTSelector.Feedback.FiniteEventBulkIntensity
import OTSelector.Probability.CountingProcess.OccupationTail

/-!
# Conditional occupation bounds for finite bulk-event counts

The generic bounded-stopping lower-occupation estimate specializes directly to the safe source
and target bulk counts, whose predictable intensities are the corresponding safe bulk rates.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace OTSelector

open CountingProcess

namespace FiniteSample

variable {n : ℕ}

/-- The bounded-stopping lower-occupation estimate for the safe source bulk count. -/
theorem safeSourceBulkCount_condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping
    {lam B x0 p0 c₀ : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (hB : 0 < B) (hc₀ : 0 < c₀) {sigma : FiniteSample n → ℝ≥0}
    {tau : FiniteSample n → WithTop ℝ≥0} {S r : ℝ≥0} (hr : 0 < r)
    (hsigma : IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun sample ↦ (sigma sample : WithTop ℝ≥0)))
    (hsigmaS : ∀ sample, sigma sample ≤ S)
    (htau : IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) tau)
    (hLower : ∀ (u : ℝ≥0) sample, (u : WithTop ℝ≥0) ≤ tau sample →
      c₀ ≤ safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample) :
    MeasureTheory.condExp hsigma.measurableSpace
        (finiteSampleLaw n : Measure (FiniteSample n))
        ((stoppedLowerOccupationEvent
          (fun t sample ↦ safeSourceBulkCount hlam0 hlamHalf B x0 p0 t sample)
          sigma tau (lowerOccupationCountRate c₀) r).indicator (fun _ ↦ (1 : ℝ))) ≤ᵐ[
            (finiteSampleLaw n : Measure (FiniteSample n))]
      fun _ ↦ Real.exp (-lowerOccupationDecayRate c₀ * (r : ℝ)) := by
  exact condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping
    (mu := finiteSampleLaw n)
    (F := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
    (N := fun t sample ↦ safeSourceBulkCount hlam0 hlamHalf B x0 p0 t sample)
    (Lambda := fun t sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample)
    (sigma := sigma) (tau := tau) (c₀ := c₀) (C₀ := feedbackBulkRateCap n B)
    (B := S) (r := r) hc₀ (feedbackBulkRateCap_nonneg n B) hr
    (safeSourceBulkCount_isSimpleCountingProcess
      (n := n) hlam0 hlamHalf B x0 p0)
    (safeSourceBulkCount_hasPredictableIntensity
      (n := n) hlam0 hlamHalf hn hB)
    (fun u sample ↦ safeSourceBulkRate_le_cap
      hlam0 hlamHalf B x0 p0 u sample)
    hsigma hsigmaS htau hLower

/-- The bounded-stopping lower-occupation estimate for the safe target bulk count. -/
theorem safeTargetBulkCount_condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping
    {lam B x0 p0 c₀ : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (hB : 0 < B) (hc₀ : 0 < c₀) {sigma : FiniteSample n → ℝ≥0}
    {tau : FiniteSample n → WithTop ℝ≥0} {S r : ℝ≥0} (hr : 0 < r)
    (hsigma : IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun sample ↦ (sigma sample : WithTop ℝ≥0)))
    (hsigmaS : ∀ sample, sigma sample ≤ S)
    (htau : IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) tau)
    (hLower : ∀ (u : ℝ≥0) sample, (u : WithTop ℝ≥0) ≤ tau sample →
      c₀ ≤ safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample) :
    MeasureTheory.condExp hsigma.measurableSpace
        (finiteSampleLaw n : Measure (FiniteSample n))
        ((stoppedLowerOccupationEvent
          (fun t sample ↦ safeTargetBulkCount hlam0 hlamHalf B x0 p0 t sample)
          sigma tau (lowerOccupationCountRate c₀) r).indicator (fun _ ↦ (1 : ℝ))) ≤ᵐ[
            (finiteSampleLaw n : Measure (FiniteSample n))]
      fun _ ↦ Real.exp (-lowerOccupationDecayRate c₀ * (r : ℝ)) := by
  exact condExp_stoppedLowerOccupationEvent_le_explicit_boundedStopping
    (mu := finiteSampleLaw n)
    (F := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
    (N := fun t sample ↦ safeTargetBulkCount hlam0 hlamHalf B x0 p0 t sample)
    (Lambda := fun t sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample)
    (sigma := sigma) (tau := tau) (c₀ := c₀) (C₀ := feedbackBulkRateCap n B)
    (B := S) (r := r) hc₀ (feedbackBulkRateCap_nonneg n B) hr
    (safeTargetBulkCount_isSimpleCountingProcess
      (n := n) hlam0 hlamHalf B x0 p0)
    (safeTargetBulkCount_hasPredictableIntensity
      (n := n) hlam0 hlamHalf hn hB)
    (fun u sample ↦ safeTargetBulkRate_le_cap
      hlam0 hlamHalf B x0 p0 u sample)
    hsigma hsigmaS htau hLower

end FiniteSample

end OTSelector
