import OTSelector.Feedback.FeedbackRegularityStopping

/-!
# The combined A1 stopping coordinate

The A1 coordinate is the minimum of the bulk exit, the residual-regularity exit, and a
deterministic horizon.  Its mask is written as the product of the three right-closed masks; a
pointwise theorem identifies that product with the through-stop mask of the minimum.
-/

open MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-- The A1 stopping coordinate: bulk exit, regularity exit, or deterministic horizon. -/
noncomputable def safeFeedbackA1StopTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) : FiniteSample n → WithTop ℝ≥0 :=
  fun sample ↦ min
    (safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample)
    (min (safeFeedbackRegularityExitTime
      hlam0 hlamHalf eta B x0 p0 sample) (T : WithTop ℝ≥0))

theorem safeFeedbackA1StopTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta x0 p0 : ℝ) (T : ℝ≥0) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackA1StopTime
        (n := n) hlam0 hlamHalf eta B x0 p0 T) := by
  exact (safeFeedbackBulkExitTime_isStoppingTime
    (n := n) hlam0 hlamHalf B x0 p0).min
      ((safeFeedbackRegularityExitTime_isStoppingTime
        (n := n) hlam0 hlamHalf hB eta x0 p0).min_const T)

/-- Product form of the right-closed A1 localization mask. -/
noncomputable def safeFeedbackA1ThroughStopMask
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) : ℝ≥0 → FiniteSample n → ℝ :=
  fun t sample ↦
    safeFeedbackBulkThroughExitMask hlam0 hlamHalf B x0 p0 t sample *
      (safeFeedbackRegularityThroughExitMask
        hlam0 hlamHalf eta B x0 p0 t sample *
        CountingProcess.throughStopMask
          (fun _ : FiniteSample n ↦ (T : WithTop ℝ≥0)) t sample)

theorem safeFeedbackA1ThroughStopMask_eq_product
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T t : ℝ≥0) (sample : FiniteSample n) :
    safeFeedbackA1ThroughStopMask
        hlam0 hlamHalf eta B x0 p0 T t sample =
      safeFeedbackBulkThroughExitMask hlam0 hlamHalf B x0 p0 t sample *
        (safeFeedbackRegularityThroughExitMask
          hlam0 hlamHalf eta B x0 p0 t sample *
          CountingProcess.throughStopMask
            (fun _ : FiniteSample n ↦ (T : WithTop ℝ≥0)) t sample) :=
  rfl

private theorem throughStopMask_min_min_eq_product
    {a b c q : WithTop ℝ≥0} :
    (if q ≤ min a (min b c) then (1 : ℝ) else 0) =
      (if q ≤ a then 1 else 0) *
        ((if q ≤ b then 1 else 0) * (if q ≤ c then 1 else 0)) := by
  simp only [le_min_iff]
  split_ifs <;> simp_all

/-- The product mask is exactly the through-stop mask of the combined coordinate. -/
theorem safeFeedbackA1ThroughStopMask_eq_throughStopMask
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T t : ℝ≥0) (sample : FiniteSample n) :
    safeFeedbackA1ThroughStopMask
        hlam0 hlamHalf eta B x0 p0 T t sample =
      CountingProcess.throughStopMask
        (safeFeedbackA1StopTime
          (n := n) hlam0 hlamHalf eta B x0 p0 T) t sample := by
  simp only [safeFeedbackA1ThroughStopMask, safeFeedbackBulkThroughExitMask,
    safeFeedbackRegularityThroughExitMask, CountingProcess.throughStopMask,
    safeFeedbackA1StopTime]
  exact (throughStopMask_min_min_eq_product
    (a := safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample)
    (b := safeFeedbackRegularityExitTime
      hlam0 hlamHalf eta B x0 p0 sample)
    (c := (T : WithTop ℝ≥0)) (q := (t : WithTop ℝ≥0))).symm

theorem safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta x0 p0 : ℝ) (T : ℝ≥0) :
    CountingProcess.IsBoundedSimplePredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackA1ThroughStopMask
        (n := n) hlam0 hlamHalf eta B x0 p0 T) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hbulk := safeFeedbackBulkThroughExitMask_boundedSimplePredictable
    (n := n) hlam0 hlamHalf B x0 p0
  have hreg := safeFeedbackRegularityThroughExitMask_boundedSimplePredictable
    (n := n) hlam0 hlamHalf hB eta x0 p0
  have hT : CountingProcess.IsBoundedSimplePredictable ℱ
      (CountingProcess.throughStopMask
        (fun _ : FiniteSample n ↦ (T : WithTop ℝ≥0))) :=
    CountingProcess.throughStopMask_boundedSimplePredictable
      (isStoppingTime_const ℱ T) Set.finite_range_const
  exact hbulk.mul_process (hreg.mul_process hT)

theorem safeFeedbackA1ThroughStopMask_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (eta x0 p0 : ℝ) (T : ℝ≥0) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (safeFeedbackA1ThroughStopMask
        (n := n) hlam0 hlamHalf eta B x0 p0 T) :=
  (safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0 hlamHalf hB eta x0 p0 T).1

/-! ## Strict-survival projections -/

theorem lt_safeFeedbackBulkExitTime_of_lt_A1Stop
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample) :
    (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample :=
  ht.trans_le (min_le_left _ _)

theorem lt_safeFeedbackRegularityExitTime_of_lt_A1Stop
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample) :
    (t : WithTop ℝ≥0) <
      safeFeedbackRegularityExitTime hlam0 hlamHalf eta B x0 p0 sample :=
  ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))

theorem lt_horizon_of_lt_safeFeedbackA1Stop
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample) :
    t < T := by
  apply WithTop.coe_lt_coe.mp
  exact ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))

end FiniteSample

end OTSelector
