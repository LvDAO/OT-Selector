import OTSelector.Feedback.FeedbackBulkMask
import OTSelector.Probability.CountingProcess.ContinuousOpenHitting

/-!
# The first feedback bulk exit

The actual feedback intensities use a pointwise bulk mask, which may become one again after a path
has left and later re-entered the strip.  This file defines the first exit from the closed bulk
region and proves the stopping and predictable-through-stop facts needed to localize A1 before
that re-entry can occur.
-/

open MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

open FiniteSample

variable {n : ℕ}

/-- The open complement of the closed feedback bulk region. -/
def feedbackBulkBadSet (n : ℕ) (B : ℝ) : Set (ℝ × ℝ) :=
  {z | ¬feedbackBulkRegion n B z.1 z.2}

theorem isOpen_feedbackBulkBadSet (n : ℕ) (B : ℝ) :
    IsOpen (feedbackBulkBadSet n B) := by
  have hleft : IsClosed {z : ℝ × ℝ | B ≤ z.1} :=
    isClosed_le continuous_const continuous_fst
  have hright : IsClosed {z : ℝ × ℝ | z.1 ≤ (n : ℝ) - B} :=
    isClosed_le continuous_fst continuous_const
  have hp : IsClosed {z : ℝ × ℝ | |z.2| ≤ B / 8} :=
    isClosed_le (continuous_abs.comp continuous_snd) continuous_const
  have hclosed : IsClosed {z : ℝ × ℝ | feedbackBulkRegion n B z.1 z.2} := by
    have heq : {z : ℝ × ℝ | feedbackBulkRegion n B z.1 z.2} =
        {z : ℝ × ℝ | B ≤ z.1} ∩
          ({z : ℝ × ℝ | z.1 ≤ (n : ℝ) - B} ∩
            {z : ℝ × ℝ | |z.2| ≤ B / 8}) := by
      ext z
      simp [feedbackBulkRegion]
    rw [heq]
    exact hleft.inter (hright.inter hp)
  rw [feedbackBulkBadSet]
  exact isOpen_compl_iff.mpr hclosed

/-- The deterministic spatial coordinate and safe graph height as one continuous state path. -/
noncomputable def safeFeedbackBulkPath
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ × ℝ :=
  (elapsedFeedbackCoordinate x0 t,
    safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)

theorem safeFeedbackBulkPath_adapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    Adapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackBulkPath (n := n) hlam0 hlamHalf x0 p0) := by
  intro t
  exact measurable_const.prodMk
    (measurable_safeFeedbackHeightAtElapsed_usual
      (n := n) hlam0 hlamHalf x0 p0 t)

theorem safeFeedbackBulkPath_continuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) :
    Continuous (fun t : ℝ≥0 ↦
      safeFeedbackBulkPath hlam0 hlamHalf x0 p0 t sample) := by
  exact (continuous_const.add continuous_subtype_val).prodMk
    (safeFeedbackHeightAtElapsed_continuous hlam0 hlamHalf x0 p0 sample)

/-- First elapsed time at which the safe feedback path enters the open bad region. -/
noncomputable def safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) : FiniteSample n → WithTop ℝ≥0 :=
  MeasureTheory.hittingAfter
    (safeFeedbackBulkPath (n := n) hlam0 hlamHalf x0 p0)
    (feedbackBulkBadSet n B) 0

theorem safeFeedbackBulkExitTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackBulkExitTime (n := n) hlam0 hlamHalf B x0 p0) := by
  have : Filtration.IsRightContinuous
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) :=
    usualRevealedFiltration_isRightContinuous
      (n := n) hlam0 hlamHalf x0 p0
  simpa only [safeFeedbackBulkExitTime] using
    CountingProcess.MeasureTheory.Adapted.isStoppingTime_hittingAfter_zero_isOpen
      (safeFeedbackBulkPath_adapted (n := n) hlam0 hlamHalf x0 p0)
      (fun sample ↦ safeFeedbackBulkPath_continuous
        (n := n) hlam0 hlamHalf x0 p0 sample)
      (isOpen_feedbackBulkBadSet n B)

/-- The right-closed indicator through the first bulk exit. -/
noncomputable def safeFeedbackBulkThroughExitMask
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) : ℝ≥0 → FiniteSample n → ℝ :=
  CountingProcess.throughStopMask
    (safeFeedbackBulkExitTime (n := n) hlam0 hlamHalf B x0 p0)

theorem safeFeedbackBulkThroughExitMask_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackBulkThroughExitMask (n := n) hlam0 hlamHalf B x0 p0) := by
  simpa only [safeFeedbackBulkThroughExitMask, safeFeedbackBulkExitTime] using
    CountingProcess.throughStopMask_hittingAfter_zero_predictable
      (safeFeedbackBulkPath_adapted (n := n) hlam0 hlamHalf x0 p0)
      (fun sample ↦ safeFeedbackBulkPath_continuous
        (n := n) hlam0 hlamHalf x0 p0 sample)
      (isOpen_feedbackBulkBadSet n B)

theorem safeFeedbackBulkThroughExitMask_boundedSimplePredictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    CountingProcess.IsBoundedSimplePredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackBulkThroughExitMask (n := n) hlam0 hlamHalf B x0 p0) := by
  simpa only [safeFeedbackBulkThroughExitMask, safeFeedbackBulkExitTime] using
    CountingProcess.throughStopMask_hittingAfter_zero_boundedSimplePredictable
      (safeFeedbackBulkPath_adapted (n := n) hlam0 hlamHalf x0 p0)
      (fun sample ↦ safeFeedbackBulkPath_continuous
        (n := n) hlam0 hlamHalf x0 p0 sample)
      (isOpen_feedbackBulkBadSet n B)

/-- Strict survival before the first exit keeps the actual graph point in the closed bulk. -/
theorem feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) := by
  have hnot := CountingProcess.not_mem_of_lt_hittingAfter_zero
    (u := safeFeedbackBulkPath (n := n) hlam0 hlamHalf x0 p0)
    (s := feedbackBulkBadSet n B) ht
  simpa only [safeFeedbackBulkPath, feedbackBulkBadSet, Set.mem_ofPred_eq, not_not] using hnot

end OTSelector
