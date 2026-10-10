import OTSelector.Feedback.FeedbackBulkSurvivalRate
import OTSelector.Probability.CountingProcess.FiniteEventCountTop

/-!
# The first feedback residual-regularity exit

The residual path used to define the stopping coordinate is post-jump and right-continuous.
Its denominator is stabilized below by `B / 2`, so the path is total outside the bulk as well.
The predictable residual densities remain pre-jump quantities.  A strict-left limit identifies
them with the left limit of the post-jump path, and closedness of the regularity window transfers
strict survival to the predictable densities.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal Topology

namespace OTSelector

open FiniteSample

variable {n : ℕ}

namespace FiniteSample

/-! ## Post-jump remaining counts and stabilized densities -/

/-- Source labels remaining after all source events attained by `t`. -/
noncomputable def safeSourceRemainingAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeInitialSourceRemainingReal lam x0 p0 sample -
    (safeSourceCount hlam0 hlamHalf x0 p0 t sample : ℝ)

/-- Target labels remaining after all target events attained by `t`. -/
noncomputable def safeTargetRemainingAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeInitialTargetRemainingReal lam x0 p0 sample -
    (safeTargetCount hlam0 hlamHalf x0 p0 t sample : ℝ)

/-- The source affine mass stabilized away from zero. -/
noncomputable def safeSourceStabilizedRemainingMassAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  max (B / 2)
    (safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample)

/-- The target affine mass stabilized away from zero. -/
noncomputable def safeTargetStabilizedRemainingMassAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  max (B / 2)
    (safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample)

/-- Right-continuous post-jump source residual density. -/
noncomputable def safeSourcePostResidualDensityAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeSourceRemainingAt hlam0 hlamHalf x0 p0 t sample /
    safeSourceStabilizedRemainingMassAt hlam0 hlamHalf B x0 p0 t sample

/-- Right-continuous post-jump target residual density. -/
noncomputable def safeTargetPostResidualDensityAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeTargetRemainingAt hlam0 hlamHalf x0 p0 t sample /
    safeTargetStabilizedRemainingMassAt hlam0 hlamHalf B x0 p0 t sample

/-- Stabilized predictable source residual density. -/
noncomputable def safeSourcePreStabilizedResidualDensityAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeSourceRemainingBefore hlam0 hlamHalf x0 p0 t sample /
    safeSourceStabilizedRemainingMassAt hlam0 hlamHalf B x0 p0 t sample

/-- Stabilized predictable target residual density. -/
noncomputable def safeTargetPreStabilizedResidualDensityAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeTargetRemainingBefore hlam0 hlamHalf x0 p0 t sample /
    safeTargetStabilizedRemainingMassAt hlam0 hlamHalf B x0 p0 t sample

/-- The two post-jump stabilized residual densities. -/
noncomputable def safeFeedbackPostResidualPath
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ × ℝ :=
  (safeSourcePostResidualDensityAt hlam0 hlamHalf B x0 p0 t sample,
    safeTargetPostResidualDensityAt hlam0 hlamHalf B x0 p0 t sample)

/-- The two predictable stabilized residual densities. -/
noncomputable def safeFeedbackPreStabilizedResidualPath
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ × ℝ :=
  (safeSourcePreStabilizedResidualDensityAt hlam0 hlamHalf B x0 p0 t sample,
    safeTargetPreStabilizedResidualDensityAt hlam0 hlamHalf B x0 p0 t sample)

private theorem safeSourceRemainingAt_stronglyAdapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeSourceRemainingAt (n := n) hlam0 hlamHalf x0 p0) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hN := safeSourceCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf x0 p0
  have hbefore : IsStronglyPredictable ℱ
      (fun t sample ↦
        (CountingProcess.countBefore
          (safeSourceCount hlam0 hlamHalf x0 p0) t sample : ℝ)) :=
    CountingProcess.stronglyMeasurable_countBefore hN.stronglyAdapted hN.monotone
  have hpre :=
    (safeSourceRemainingBefore_predictable
      (n := n) hlam0 hlamHalf x0 p0).stronglyAdapted
  have hinit : StronglyAdapted ℱ
      (fun _ sample ↦ safeInitialSourceRemainingReal lam x0 p0 sample) := by
    intro t
    convert (hpre.add hbefore.stronglyAdapted) t using 1
    funext sample
    change safeInitialSourceRemainingReal lam x0 p0 sample =
      (safeInitialSourceRemainingReal lam x0 p0 sample -
        (CountingProcess.countBefore
          (safeSourceCount hlam0 hlamHalf x0 p0) t sample : ℝ)) +
        (CountingProcess.countBefore
          (safeSourceCount hlam0 hlamHalf x0 p0) t sample : ℝ)
    exact (sub_add_cancel _ _).symm
  exact hinit.sub (safeSourceCount_stronglyAdapted
    (n := n) hlam0 hlamHalf x0 p0)

private theorem safeTargetRemainingAt_stronglyAdapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeTargetRemainingAt (n := n) hlam0 hlamHalf x0 p0) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hN := safeTargetCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf x0 p0
  have hbefore : IsStronglyPredictable ℱ
      (fun t sample ↦
        (CountingProcess.countBefore
          (safeTargetCount hlam0 hlamHalf x0 p0) t sample : ℝ)) :=
    CountingProcess.stronglyMeasurable_countBefore hN.stronglyAdapted hN.monotone
  have hpre :=
    (safeTargetRemainingBefore_predictable
      (n := n) hlam0 hlamHalf x0 p0).stronglyAdapted
  have hinit : StronglyAdapted ℱ
      (fun _ sample ↦ safeInitialTargetRemainingReal lam x0 p0 sample) := by
    intro t
    convert (hpre.add hbefore.stronglyAdapted) t using 1
    funext sample
    change safeInitialTargetRemainingReal lam x0 p0 sample =
      (safeInitialTargetRemainingReal lam x0 p0 sample -
        (CountingProcess.countBefore
          (safeTargetCount hlam0 hlamHalf x0 p0) t sample : ℝ)) +
        (CountingProcess.countBefore
          (safeTargetCount hlam0 hlamHalf x0 p0) t sample : ℝ)
    exact (sub_add_cancel _ _).symm
  exact hinit.sub (safeTargetCount_stronglyAdapted
    (n := n) hlam0 hlamHalf x0 p0)

private theorem safeSourceStabilizedRemainingMassAt_stronglyAdapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeSourceStabilizedRemainingMassAt
        (n := n) hlam0 hlamHalf B x0 p0) := by
  have hmass :=
    (safeSourceUnclippedRemainingMassAt_predictable
      (n := n) hlam0 hlamHalf x0 p0).stronglyAdapted
  intro t
  exact (Measurable.max measurable_const (hmass t).measurable).stronglyMeasurable

private theorem safeTargetStabilizedRemainingMassAt_stronglyAdapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeTargetStabilizedRemainingMassAt
        (n := n) hlam0 hlamHalf B x0 p0) := by
  have hmass :=
    (safeTargetUnclippedRemainingMassAt_predictable
      (n := n) hlam0 hlamHalf x0 p0).stronglyAdapted
  intro t
  exact (Measurable.max measurable_const (hmass t).measurable).stronglyMeasurable

theorem safeFeedbackPostResidualPath_adapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    Adapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackPostResidualPath (n := n) hlam0 hlamHalf B x0 p0) := by
  have hsource : StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeSourcePostResidualDensityAt
        (n := n) hlam0 hlamHalf B x0 p0) := by
    intro t
    exact ((safeSourceRemainingAt_stronglyAdapted
      (n := n) hlam0 hlamHalf x0 p0 t).measurable.div
        (safeSourceStabilizedRemainingMassAt_stronglyAdapted
          (n := n) hlam0 hlamHalf B x0 p0 t).measurable).stronglyMeasurable
  have htarget : StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeTargetPostResidualDensityAt
        (n := n) hlam0 hlamHalf B x0 p0) := by
    intro t
    exact ((safeTargetRemainingAt_stronglyAdapted
      (n := n) hlam0 hlamHalf x0 p0 t).measurable.div
        (safeTargetStabilizedRemainingMassAt_stronglyAdapted
          (n := n) hlam0 hlamHalf B x0 p0 t).measurable).stronglyMeasurable
  exact fun t ↦ (hsource t).measurable.prodMk (htarget t).measurable

private theorem safeSourceUnclippedRemainingMassAt_continuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) :
    Continuous (fun t : ℝ≥0 ↦
      safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample) := by
  simp only [safeSourceUnclippedRemainingMassAt, sourceUnclippedRemainingMass,
    elapsedFeedbackCoordinate]
  exact (continuous_const.sub
    (continuous_const.add continuous_subtype_val)).add
      ((safeFeedbackHeightAtElapsed_continuous
        hlam0 hlamHalf x0 p0 sample).div_const 2)

private theorem safeTargetUnclippedRemainingMassAt_continuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) :
    Continuous (fun t : ℝ≥0 ↦
      safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample) := by
  simp only [safeTargetUnclippedRemainingMassAt, targetUnclippedRemainingMass,
    elapsedFeedbackCoordinate]
  exact (continuous_const.sub
    (continuous_const.add continuous_subtype_val)).sub
      ((continuous_const.mul (safeFeedbackHeightAtElapsed_continuous
        hlam0 hlamHalf x0 p0 sample)).div_const 2)

private theorem safeSourcePostResidualDensityAt_rightContinuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s ↦ safeSourcePostResidualDensityAt
        hlam0 hlamHalf B x0 p0 s sample) (Ici t) t := by
  have hnum : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ safeSourceRemainingAt
        hlam0 hlamHalf x0 p0 s sample) (Ici t) t :=
    continuousWithinAt_const.sub
      (safeSourceCount_rightContinuous hlam0 hlamHalf x0 p0 sample t)
  have hmass : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ safeSourceUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 s sample) (Ici t) t :=
    (safeSourceUnclippedRemainingMassAt_continuous
      (n := n) hlam0 hlamHalf x0 p0 sample).continuousWithinAt
  have hden : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ safeSourceStabilizedRemainingMassAt
        hlam0 hlamHalf B x0 p0 s sample) (Ici t) t :=
    tendsto_const_nhds.max hmass
  have hden0 : safeSourceStabilizedRemainingMassAt
      hlam0 hlamHalf B x0 p0 t sample ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (by positivity : 0 < B / 2) (le_max_left _ _)
  exact hnum.div hden hden0

private theorem safeTargetPostResidualDensityAt_rightContinuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s ↦ safeTargetPostResidualDensityAt
        hlam0 hlamHalf B x0 p0 s sample) (Ici t) t := by
  have hnum : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ safeTargetRemainingAt
        hlam0 hlamHalf x0 p0 s sample) (Ici t) t :=
    continuousWithinAt_const.sub
      (safeTargetCount_rightContinuous hlam0 hlamHalf x0 p0 sample t)
  have hmass : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ safeTargetUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 s sample) (Ici t) t :=
    (safeTargetUnclippedRemainingMassAt_continuous
      (n := n) hlam0 hlamHalf x0 p0 sample).continuousWithinAt
  have hden : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ safeTargetStabilizedRemainingMassAt
        hlam0 hlamHalf B x0 p0 s sample) (Ici t) t :=
    tendsto_const_nhds.max hmass
  have hden0 : safeTargetStabilizedRemainingMassAt
      hlam0 hlamHalf B x0 p0 t sample ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (by positivity : 0 < B / 2) (le_max_left _ _)
  exact hnum.div hden hden0

theorem safeFeedbackPostResidualPath_rightContinuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s ↦ safeFeedbackPostResidualPath
        hlam0 hlamHalf B x0 p0 s sample) (Ici t) t :=
  (safeSourcePostResidualDensityAt_rightContinuous
    (n := n) hlam0 hlamHalf hB x0 p0 sample t).prodMk
      (safeTargetPostResidualDensityAt_rightContinuous
        (n := n) hlam0 hlamHalf hB x0 p0 sample t)

/-! ## The open regularity exit and its predictable mask -/

/-- The closed square in which both residual densities are `eta`-close to one. -/
def feedbackRegularityRegion (eta : ℝ) : Set (ℝ × ℝ) :=
  {z | 1 - eta ≤ z.1 ∧ z.1 ≤ 1 + eta ∧
    1 - eta ≤ z.2 ∧ z.2 ≤ 1 + eta}

theorem isClosed_feedbackRegularityRegion (eta : ℝ) :
    IsClosed (feedbackRegularityRegion eta) := by
  have h1 : IsClosed {z : ℝ × ℝ | 1 - eta ≤ z.1} :=
    isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {z : ℝ × ℝ | z.1 ≤ 1 + eta} :=
    isClosed_le continuous_fst continuous_const
  have h3 : IsClosed {z : ℝ × ℝ | 1 - eta ≤ z.2} :=
    isClosed_le continuous_const continuous_snd
  have h4 : IsClosed {z : ℝ × ℝ | z.2 ≤ 1 + eta} :=
    isClosed_le continuous_snd continuous_const
  simpa only [feedbackRegularityRegion, Set.ofPred_and] using
    h1.inter (h2.inter (h3.inter h4))

/-- The open complement of the residual regularity square. -/
def feedbackRegularityBadSet (eta : ℝ) : Set (ℝ × ℝ) :=
  (feedbackRegularityRegion eta)ᶜ

theorem isOpen_feedbackRegularityBadSet (eta : ℝ) :
    IsOpen (feedbackRegularityBadSet eta) :=
  (isClosed_feedbackRegularityRegion eta).isOpen_compl

/-- First time the right-continuous post-jump residual path leaves the regularity square. -/
noncomputable def safeFeedbackRegularityExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) : FiniteSample n → WithTop ℝ≥0 :=
  MeasureTheory.hittingAfter
    (safeFeedbackPostResidualPath (n := n) hlam0 hlamHalf B x0 p0)
    (feedbackRegularityBadSet eta) 0

theorem safeFeedbackRegularityExitTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta x0 p0 : ℝ) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackRegularityExitTime
        (n := n) hlam0 hlamHalf eta B x0 p0) := by
  have : Filtration.IsRightContinuous
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) :=
    usualRevealedFiltration_isRightContinuous
      (n := n) hlam0 hlamHalf x0 p0
  simpa only [safeFeedbackRegularityExitTime] using
    CountingProcess.MeasureTheory.Adapted.isStoppingTime_hittingAfter_zero_isOpen_of_rightContinuous
      (safeFeedbackPostResidualPath_adapted
        (n := n) hlam0 hlamHalf B x0 p0)
      (safeFeedbackPostResidualPath_rightContinuous
        (n := n) hlam0 hlamHalf hB x0 p0)
      (isOpen_feedbackRegularityBadSet eta)

/-- The right-closed indicator through the first residual-regularity exit. -/
noncomputable def safeFeedbackRegularityThroughExitMask
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) : ℝ≥0 → FiniteSample n → ℝ :=
  CountingProcess.throughStopMask
    (safeFeedbackRegularityExitTime
      (n := n) hlam0 hlamHalf eta B x0 p0)

theorem safeFeedbackRegularityThroughExitMask_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackRegularityThroughExitMask
        (n := n) hlam0 hlamHalf eta B x0 p0) := by
  simpa only [safeFeedbackRegularityThroughExitMask,
    safeFeedbackRegularityExitTime] using
    CountingProcess.throughStopMask_hittingAfter_zero_predictable_of_rightContinuous
      (safeFeedbackPostResidualPath_adapted
        (n := n) hlam0 hlamHalf B x0 p0)
      (safeFeedbackPostResidualPath_rightContinuous
        (n := n) hlam0 hlamHalf hB x0 p0)
      (isOpen_feedbackRegularityBadSet eta)

theorem safeFeedbackRegularityThroughExitMask_boundedSimplePredictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta x0 p0 : ℝ) :
    CountingProcess.IsBoundedSimplePredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackRegularityThroughExitMask
        (n := n) hlam0 hlamHalf eta B x0 p0) := by
  simpa only [safeFeedbackRegularityThroughExitMask,
    safeFeedbackRegularityExitTime] using
    CountingProcess.throughStopMask_hittingAfter_zero_boundedSimplePredictable_of_rightContinuous
      (safeFeedbackPostResidualPath_adapted
        (n := n) hlam0 hlamHalf B x0 p0)
      (safeFeedbackPostResidualPath_rightContinuous
        (n := n) hlam0 hlamHalf hB x0 p0)
      (isOpen_feedbackRegularityBadSet eta)

/-! ## Strict-left transfer to predictable densities -/

private theorem safeSourcePostResidualDensityAt_tendsto_pre
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    Filter.Tendsto
      (fun s ↦ safeSourcePostResidualDensityAt
        hlam0 hlamHalf B x0 p0 s sample)
      (nhdsWithin t (Iio t : Set ℝ≥0))
      (nhds (safeSourcePreStabilizedResidualDensityAt
        hlam0 hlamHalf B x0 p0 t sample)) := by
  have hcount : Tendsto
      (fun s ↦ (safeSourceCount hlam0 hlamHalf x0 p0 s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (CountingProcess.countBefore
        (safeSourceCount hlam0 hlamHalf x0 p0) t sample : ℝ)) := by
    change Tendsto
      (fun s ↦ (CountingProcess.finiteEventCountTop
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (CountingProcess.countBefore
        (fun s sample' ↦ CountingProcess.finiteEventCountTop
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample')
        t sample : ℝ))
    exact CountingProcess.finiteEventCountTop_tendsto_countBefore_nhdsWithin_Iio
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) sample t
  have hnum : Tendsto
      (fun s : ℝ≥0 ↦ safeInitialSourceRemainingReal lam x0 p0 sample -
        (safeSourceCount hlam0 hlamHalf x0 p0 s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (safeInitialSourceRemainingReal lam x0 p0 sample -
        (CountingProcess.countBefore
          (safeSourceCount hlam0 hlamHalf x0 p0) t sample : ℝ))) :=
    tendsto_const_nhds.sub hcount
  have hmass : Tendsto
      (fun s : ℝ≥0 ↦ safeSourceUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 s sample)
      (nhdsWithin t (Iio t))
      (nhds (safeSourceUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 t sample)) :=
    (safeSourceUnclippedRemainingMassAt_continuous
      (n := n) hlam0 hlamHalf x0 p0 sample).continuousAt.mono_left inf_le_left
  have hden : Tendsto
      (fun s : ℝ≥0 ↦ safeSourceStabilizedRemainingMassAt
        hlam0 hlamHalf B x0 p0 s sample)
      (nhdsWithin t (Iio t))
      (nhds (safeSourceStabilizedRemainingMassAt
        hlam0 hlamHalf B x0 p0 t sample)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 ↦ B / 2)
      (nhdsWithin t (Iio t)) (nhds (B / 2))).max hmass
  have hden0 : safeSourceStabilizedRemainingMassAt
      hlam0 hlamHalf B x0 p0 t sample ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (by positivity : 0 < B / 2) (le_max_left _ _)
  refine Tendsto.congr' (Eventually.of_forall fun s ↦ ?_)
    (hnum.div hden hden0)
  simp only [Pi.div_apply, safeSourcePostResidualDensityAt,
    safeSourceRemainingAt]

private theorem safeTargetPostResidualDensityAt_tendsto_pre
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    Filter.Tendsto
      (fun s ↦ safeTargetPostResidualDensityAt
        hlam0 hlamHalf B x0 p0 s sample)
      (nhdsWithin t (Iio t : Set ℝ≥0))
      (nhds (safeTargetPreStabilizedResidualDensityAt
        hlam0 hlamHalf B x0 p0 t sample)) := by
  have hcount : Tendsto
      (fun s ↦ (safeTargetCount hlam0 hlamHalf x0 p0 s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (CountingProcess.countBefore
        (safeTargetCount hlam0 hlamHalf x0 p0) t sample : ℝ)) := by
    change Tendsto
      (fun s ↦ (CountingProcess.finiteEventCountTop
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (CountingProcess.countBefore
        (fun s sample' ↦ CountingProcess.finiteEventCountTop
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample')
        t sample : ℝ))
    exact CountingProcess.finiteEventCountTop_tendsto_countBefore_nhdsWithin_Iio
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) sample t
  have hnum : Tendsto
      (fun s : ℝ≥0 ↦ safeInitialTargetRemainingReal lam x0 p0 sample -
        (safeTargetCount hlam0 hlamHalf x0 p0 s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (safeInitialTargetRemainingReal lam x0 p0 sample -
        (CountingProcess.countBefore
          (safeTargetCount hlam0 hlamHalf x0 p0) t sample : ℝ))) :=
    tendsto_const_nhds.sub hcount
  have hmass : Tendsto
      (fun s : ℝ≥0 ↦ safeTargetUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 s sample)
      (nhdsWithin t (Iio t))
      (nhds (safeTargetUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 t sample)) :=
    (safeTargetUnclippedRemainingMassAt_continuous
      (n := n) hlam0 hlamHalf x0 p0 sample).continuousAt.mono_left inf_le_left
  have hden : Tendsto
      (fun s : ℝ≥0 ↦ safeTargetStabilizedRemainingMassAt
        hlam0 hlamHalf B x0 p0 s sample)
      (nhdsWithin t (Iio t))
      (nhds (safeTargetStabilizedRemainingMassAt
        hlam0 hlamHalf B x0 p0 t sample)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 ↦ B / 2)
      (nhdsWithin t (Iio t)) (nhds (B / 2))).max hmass
  have hden0 : safeTargetStabilizedRemainingMassAt
      hlam0 hlamHalf B x0 p0 t sample ≠ 0 := by
    apply ne_of_gt
    exact lt_of_lt_of_le (by positivity : 0 < B / 2) (le_max_left _ _)
  refine Tendsto.congr' (Eventually.of_forall fun s ↦ ?_)
    (hnum.div hden hden0)
  simp only [Pi.div_apply, safeTargetPostResidualDensityAt,
    safeTargetRemainingAt]

theorem safeFeedbackPostResidualPath_tendsto_pre
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    Filter.Tendsto
      (fun s ↦ safeFeedbackPostResidualPath
        hlam0 hlamHalf B x0 p0 s sample)
      (nhdsWithin t (Iio t : Set ℝ≥0))
      (nhds (safeFeedbackPreStabilizedResidualPath
        hlam0 hlamHalf B x0 p0 t sample)) :=
  (safeSourcePostResidualDensityAt_tendsto_pre
    (n := n) hlam0 hlamHalf hB x0 p0 sample t).prodMk_nhds
      (safeTargetPostResidualDensityAt_tendsto_pre
        (n := n) hlam0 hlamHalf hB x0 p0 sample t)

theorem feedbackRegularityRegion_of_lt_safeFeedbackRegularityExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta x0 p0 : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackRegularityExitTime hlam0 hlamHalf eta B x0 p0 sample) :
    safeFeedbackPreStabilizedResidualPath
      hlam0 hlamHalf B x0 p0 t sample ∈ feedbackRegularityRegion eta := by
  by_cases ht0 : t = 0
  · subst t
    have hpost := CountingProcess.not_mem_of_lt_hittingAfter_zero
      (u := safeFeedbackPostResidualPath
        (n := n) hlam0 hlamHalf B x0 p0)
      (s := feedbackRegularityBadSet eta) ht
    have hEq : safeFeedbackPreStabilizedResidualPath
        hlam0 hlamHalf B x0 p0 0 sample =
        safeFeedbackPostResidualPath hlam0 hlamHalf B x0 p0 0 sample := by
      simp [safeFeedbackPreStabilizedResidualPath,
        safeFeedbackPostResidualPath, safeSourcePreStabilizedResidualDensityAt,
        safeTargetPreStabilizedResidualDensityAt, safeSourcePostResidualDensityAt,
        safeTargetPostResidualDensityAt, safeSourceRemainingBefore,
        safeTargetRemainingBefore, safeSourceRemainingAt, safeTargetRemainingAt,
        safeSourceCount_zero, safeTargetCount_zero]
    rw [hEq]
    simpa only [feedbackRegularityBadSet, Set.mem_compl_iff, not_not] using hpost
  · have htpos : 0 < t := lt_of_le_of_ne t.2 (Ne.symm ht0)
    let _ : NeBot (nhdsWithin t (Iio t : Set ℝ≥0)) :=
      nhdsWithin_Iio_neBot' ⟨0, htpos⟩ le_rfl
    apply (isClosed_feedbackRegularityRegion eta).mem_of_tendsto
      (safeFeedbackPostResidualPath_tendsto_pre
        (n := n) hlam0 hlamHalf hB x0 p0 sample t)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsExit : (s : WithTop ℝ≥0) <
        safeFeedbackRegularityExitTime hlam0 hlamHalf eta B x0 p0 sample :=
      (WithTop.coe_lt_coe.mpr hs).trans ht
    have hnot := CountingProcess.not_mem_of_lt_hittingAfter_zero
      (u := safeFeedbackPostResidualPath
        (n := n) hlam0 hlamHalf B x0 p0)
      (s := feedbackRegularityBadSet eta) hsExit
    simpa only [feedbackRegularityBadSet, Set.mem_compl_iff, not_not] using hnot

private theorem safeSourcePreStabilizedResidualDensityAt_eq_unclipped
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B x0 p0 : ℝ} (hB : 0 < B) (t : ℝ≥0) (sample : FiniteSample n)
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    safeSourcePreStabilizedResidualDensityAt
        hlam0 hlamHalf B x0 p0 t sample =
      safeSourceUnclippedResidualDensityAt
        hlam0 hlamHalf x0 p0 t sample := by
  have hge := sourceUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
  have hhalf : B / 2 ≤ safeSourceUnclippedRemainingMassAt
      hlam0 hlamHalf x0 p0 t sample := by
    change B / 2 ≤ sourceUnclippedRemainingMass n
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
      (elapsedFeedbackCoordinate x0 t)
    nlinarith [hge, hB]
  simp only [safeSourcePreStabilizedResidualDensityAt,
    safeSourceStabilizedRemainingMassAt, max_eq_right hhalf,
    safeSourceUnclippedResidualDensityAt]

private theorem safeTargetPreStabilizedResidualDensityAt_eq_unclipped
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B x0 p0 : ℝ} (hB : 0 < B) (t : ℝ≥0) (sample : FiniteSample n)
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    safeTargetPreStabilizedResidualDensityAt
        hlam0 hlamHalf B x0 p0 t sample =
      safeTargetUnclippedResidualDensityAt
        hlam0 hlamHalf x0 p0 t sample := by
  have hge := targetUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
  have hhalf : B / 2 ≤ safeTargetUnclippedRemainingMassAt
      hlam0 hlamHalf x0 p0 t sample := by
    change B / 2 ≤ targetUnclippedRemainingMass n
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
      (elapsedFeedbackCoordinate x0 t)
    nlinarith [hge, hB]
  simp only [safeTargetPreStabilizedResidualDensityAt,
    safeTargetStabilizedRemainingMassAt, max_eq_right hhalf,
    safeTargetUnclippedResidualDensityAt]

/-- Strict survival of both exits gives the genuine pre-jump regularity hypothesis. -/
theorem crossingRegularity_of_lt_safeFeedbackRegularityExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {eta B x0 p0 : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (t : ℝ≥0)
    (sample : FiniteSample n)
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample))
    (hregExit : (t : WithTop ℝ≥0) <
      safeFeedbackRegularityExitTime hlam0 hlamHalf eta B x0 p0 sample) :
    CrossingRegularity lam eta
      (safeSourceUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 t sample)
      (safeTargetUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 t sample) := by
  have hreg := feedbackRegularityRegion_of_lt_safeFeedbackRegularityExitTime
    (n := n) hlam0 hlamHalf hB eta x0 p0 t sample hregExit
  change 1 - eta ≤
      safeSourcePreStabilizedResidualDensityAt
        hlam0 hlamHalf B x0 p0 t sample ∧
    safeSourcePreStabilizedResidualDensityAt
        hlam0 hlamHalf B x0 p0 t sample ≤ 1 + eta ∧
    1 - eta ≤ safeTargetPreStabilizedResidualDensityAt
        hlam0 hlamHalf B x0 p0 t sample ∧
    safeTargetPreStabilizedResidualDensityAt
        hlam0 hlamHalf B x0 p0 t sample ≤ 1 + eta at hreg
  rw [safeSourcePreStabilizedResidualDensityAt_eq_unclipped
      hlam0 hlamHalf hB t sample hbulk,
    safeTargetPreStabilizedResidualDensityAt_eq_unclipped
      hlam0 hlamHalf hB t sample hbulk] at hreg
  exact ⟨heta0, hetaSmall, hreg.1, hreg.2.1, hreg.2.2.1, hreg.2.2.2⟩

end FiniteSample

end OTSelector
