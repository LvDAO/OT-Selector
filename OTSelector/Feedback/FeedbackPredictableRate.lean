import OTSelector.Feedback.FeedbackPredictableHeight
import OTSelector.Feedback.FeedbackPredictableState
import OTSelector.Feedback.FeedbackHazard

/-!
# Predictable bulk feedback-rate formulas

This file combines the strictly pre-jump remaining counts, the continuous safe graph height,
and the predictable left current.  The resulting formulas are the algebraic bulk candidates in
`(1.13)--(1.15)`.  Their compensator property is deliberately left to the subsequent
finite-history probability argument.

The remaining masses below are the unclipped affine formulas.  They have their geometric meaning
only while all source and target sections remain inside the rank strip.
-/

open MeasureTheory
open scoped NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Predictable coordinates and affine remaining masses -/

/-- Spatial coordinate corresponding to nonnegative elapsed time. -/
def elapsedFeedbackCoordinate (x0 : ℝ) (t : ℝ≥0) : ℝ :=
  x0 + (t : ℝ)

private theorem elapsedFeedbackCoordinate_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t (_ : FiniteSample n) ↦ elapsedFeedbackCoordinate x0 t) := by
  exact CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    (fun _ ↦ stronglyMeasurable_const)
    (fun _ ↦ continuous_const.add continuous_subtype_val)

/-- Algebraic source remaining mass evaluated on the safe feedback graph. -/
noncomputable def safeSourceUnclippedRemainingMassAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  sourceUnclippedRemainingMass n
    (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
    (elapsedFeedbackCoordinate x0 t)

/-- Algebraic target remaining mass evaluated on the safe feedback graph. -/
noncomputable def safeTargetUnclippedRemainingMassAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  targetUnclippedRemainingMass n
    (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
    (elapsedFeedbackCoordinate x0 t)

theorem safeSourceUnclippedRemainingMassAt_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦
        safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hx := elapsedFeedbackCoordinate_predictable
    (n := n) hlam0 hlamHalf x0 p0
  have hp := safeFeedbackHeightAtElapsed_predictable
    (n := n) hlam0 hlamHalf x0 p0
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × FiniteSample n ↦
      (n : ℝ) - elapsedFeedbackCoordinate x0 z.1 +
        safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 z.1 z.2 / 2)
  exact ((stronglyMeasurable_const.sub hx).add
    (hp.measurable.div_const 2).stronglyMeasurable)

theorem safeTargetUnclippedRemainingMassAt_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦
        safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hx := elapsedFeedbackCoordinate_predictable
    (n := n) hlam0 hlamHalf x0 p0
  have hp := safeFeedbackHeightAtElapsed_predictable
    (n := n) hlam0 hlamHalf x0 p0
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × FiniteSample n ↦
      (n : ℝ) - elapsedFeedbackCoordinate x0 z.1 -
        3 * safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 z.1 z.2 / 2)
  have hthree : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × FiniteSample n ↦
        3 * safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 z.1 z.2) :=
    stronglyMeasurable_const.mul hp
  exact (stronglyMeasurable_const.sub hx).sub
    (hthree.measurable.div_const 2).stronglyMeasurable

/-! ## Residual densities and total rates -/

/-- Predictable left slope of the safe feedback graph. -/
noncomputable def safePreFeedbackSlope
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  feedbackSlope lam (safePreCurrentAt hlam0 hlamHalf x0 p0 t sample : ℝ)

theorem safePreFeedbackSlope_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample) := by
  simpa [safePreFeedbackSlope] using
    (safeFeedbackSlope_predictable (n := n) hlam0 hlamHalf x0 p0)

/-- Source remaining-label density divided by the algebraic source remaining mass. -/
noncomputable def safeSourceUnclippedResidualDensityAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeSourceRemainingBefore hlam0 hlamHalf x0 p0 t sample /
    safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample

/-- Target remaining-label density divided by the algebraic target remaining mass. -/
noncomputable def safeTargetUnclippedResidualDensityAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeTargetRemainingBefore hlam0 hlamHalf x0 p0 t sample /
    safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample

theorem safeSourceUnclippedResidualDensityAt_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦
        safeSourceUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 t sample) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hnum := safeSourceRemainingBefore_predictable
    (n := n) hlam0 hlamHalf x0 p0
  have hden := safeSourceUnclippedRemainingMassAt_predictable
    (n := n) hlam0 hlamHalf x0 p0
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × FiniteSample n ↦
      safeSourceRemainingBefore hlam0 hlamHalf x0 p0 z.1 z.2 /
        safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 z.1 z.2)
  exact (hnum.measurable.div hden.measurable).stronglyMeasurable

theorem safeTargetUnclippedResidualDensityAt_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦
        safeTargetUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 t sample) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hnum := safeTargetRemainingBefore_predictable
    (n := n) hlam0 hlamHalf x0 p0
  have hden := safeTargetUnclippedRemainingMassAt_predictable
    (n := n) hlam0 hlamHalf x0 p0
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × FiniteSample n ↦
      safeTargetRemainingBefore hlam0 hlamHalf x0 p0 z.1 z.2 /
        safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 z.1 z.2)
  exact (hnum.measurable.div hden.measurable).stronglyMeasurable

/-- Source total-rate candidate from the predictable pre-jump quantities. -/
noncomputable def safeSourceUnclippedRateAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  sourceTotalRate
    (safeSourceUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 t sample)
    (safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample)

/-- Target total-rate candidate from the predictable pre-jump quantities. -/
noncomputable def safeTargetUnclippedRateAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  targetTotalRate
    (safeTargetUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 t sample)
    (safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample)

theorem safeSourceUnclippedRateAt_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hr := safeSourceUnclippedResidualDensityAt_predictable
    (n := n) hlam0 hlamHalf x0 p0
  have hq := safePreFeedbackSlope_predictable
    (n := n) hlam0 hlamHalf x0 p0
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × FiniteSample n ↦
      safeSourceUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 z.1 z.2 *
        (1 - safePreFeedbackSlope hlam0 hlamHalf x0 p0 z.1 z.2 / 2))
  have hfactor : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × FiniteSample n ↦
        1 - safePreFeedbackSlope hlam0 hlamHalf x0 p0 z.1 z.2 / 2) :=
    stronglyMeasurable_const.sub (hq.measurable.div_const 2).stronglyMeasurable
  exact hr.mul hfactor

theorem safeTargetUnclippedRateAt_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hr := safeTargetUnclippedResidualDensityAt_predictable
    (n := n) hlam0 hlamHalf x0 p0
  have hq := safePreFeedbackSlope_predictable
    (n := n) hlam0 hlamHalf x0 p0
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × FiniteSample n ↦
      safeTargetUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 z.1 z.2 *
        (1 + 3 * safePreFeedbackSlope hlam0 hlamHalf x0 p0 z.1 z.2 / 2))
  have hthree : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × FiniteSample n ↦
        3 * safePreFeedbackSlope hlam0 hlamHalf x0 p0 z.1 z.2) :=
    stronglyMeasurable_const.mul hq
  have hfactor : StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × FiniteSample n ↦
        1 + 3 * safePreFeedbackSlope hlam0 hlamHalf x0 p0 z.1 z.2 / 2) :=
    stronglyMeasurable_const.add (hthree.measurable.div_const 2).stronglyMeasurable
  exact hr.mul hfactor

end FiniteSample

end OTSelector
