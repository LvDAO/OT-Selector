import OTSelector.Feedback.FeedbackA1Stopping
import OTSelector.Feedback.FeedbackRegularitySurvival
import OTSelector.Feedback.NoTieNull

/-!
# Finite-sample survival of the combined A1 stop

The actual A1 good event is the intersection of the measurable no-feedback-tie event and the
measurable rank-array VC event.  The tie event is null under the canonical finite-sample law, so
the complement of the A1 event has exactly the same probability as the complement of the VC
event.  On this event, the regularity-survival comparison removes the regularity coordinate from
the combined A1 stopping time.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace OTSelector

open FiniteSample

/-! ## The actual A1 good event -/

/-- The actual finite-sample event used by A1 survival: no feedback ties and uniform VC
regularity of both rank arrays. -/
noncomputable def feedbackA1GoodEvent
    (n : ℕ) (lam x0 p0 : ℝ) : Set (FiniteSample n) :=
  {sample | sample.NoFeedbackTies lam x0 p0} ∩ feedbackVCRegularityGoodEvent n

theorem measurableSet_feedbackA1GoodEvent
    (n : ℕ) (lam x0 p0 : ℝ) :
    MeasurableSet (feedbackA1GoodEvent n lam x0 p0) :=
  (FiniteSample.measurableSet_noFeedbackTies lam x0 p0).inter
    (measurableSet_feedbackVCRegularityGoodEvent n)

theorem feedbackA1GoodEvent.noFeedbackTies
    {n : ℕ} {lam x0 p0 : ℝ} {sample : FiniteSample n}
    (hgood : sample ∈ feedbackA1GoodEvent n lam x0 p0) :
    sample.NoFeedbackTies lam x0 p0 :=
  hgood.1

theorem feedbackA1GoodEvent.vcRegularity
    {n : ℕ} {lam x0 p0 : ℝ} {sample : FiniteSample n}
    (hgood : sample ∈ feedbackA1GoodEvent n lam x0 p0) :
    sample ∈ feedbackVCRegularityGoodEvent n :=
  hgood.2

/-! ## Removal of the regularity coordinate -/

/-- On the actual A1 good event and under the two explicit numerical side conditions, the
regularity exit cannot reduce the combined A1 stopping time. -/
theorem safeFeedbackA1StopTime_eq_min_bulkExit_horizon_of_good
    {n : ℕ} (hn : 4 ≤ n) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {eta B : ℝ} (heta : 0 ≤ eta) (hB : 0 < B)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample ∈ feedbackA1GoodEvent n lam x0 p0)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤
      eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤
      eta * (13 * B / 16)) :
    safeFeedbackA1StopTime
        hlam0 hlamHalf eta B x0 p0 T sample =
      min (safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample)
        (T : WithTop ℝ≥0) := by
  have hreg := min_bulkExit_horizon_le_regularityExitTime_of_feedback_good
    hn hlam0 hlamHalf heta hB x0 p0 T sample
      (feedbackA1GoodEvent.noFeedbackTies hgood)
      (feedbackA1GoodEvent.vcRegularity hgood) hsqrt hlinear
  rw [safeFeedbackA1StopTime]
  apply le_antisymm
  · exact le_min (min_le_left _ _)
      ((min_le_right _ _).trans (min_le_right _ _))
  · exact le_min (min_le_left _ _) (le_min hreg (min_le_right _ _))

/-! ## Probability of the actual A1 event -/

/-- The no-tie factor removes only a null set, so the A1 bad-event probability equals the
two-rank-array VC bad-event probability exactly. -/
theorem feedbackA1GoodEvent_compl_measure_eq
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        (feedbackA1GoodEvent n lam x0 p0)ᶜ =
      (finiteSampleLaw n : Measure (FiniteSample n))
        (feedbackVCRegularityGoodEvent n)ᶜ := by
  let noTie : Set (FiniteSample n) :=
    {sample | sample.NoFeedbackTies lam x0 p0}
  let vcGood : Set (FiniteSample n) := feedbackVCRegularityGoodEvent n
  have htie : (finiteSampleLaw n : Measure (FiniteSample n)) noTieᶜ = 0 := by
    change (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | ¬sample.NoFeedbackTies lam x0 p0} = 0
    exact FiniteSample.measure_feedbackTieEvent_eq_zero hlam0 hlamHalf
  have hcompl : (feedbackA1GoodEvent n lam x0 p0)ᶜ = noTieᶜ ∪ vcGoodᶜ := by
    ext sample
    change (¬(sample.NoFeedbackTies lam x0 p0 ∧
      sample ∈ feedbackVCRegularityGoodEvent n)) ↔
        ¬sample.NoFeedbackTies lam x0 p0 ∨
          sample ∉ feedbackVCRegularityGoodEvent n
    tauto
  apply le_antisymm
  · rw [hcompl]
    calc
      (finiteSampleLaw n : Measure (FiniteSample n)) (noTieᶜ ∪ vcGoodᶜ) ≤
          (finiteSampleLaw n : Measure (FiniteSample n)) noTieᶜ +
            (finiteSampleLaw n : Measure (FiniteSample n)) vcGoodᶜ :=
        measure_union_le _ _
      _ = (finiteSampleLaw n : Measure (FiniteSample n)) vcGoodᶜ := by
        rw [htie, zero_add]
  · apply measure_mono
    intro sample hsample
    rw [hcompl]
    exact Or.inr hsample

/-- The complement of the actual A1 good event has the same explicit polynomial upper bound as
the two-array VC event. -/
theorem feedbackA1GoodEvent_compl_le
    (n : ℕ) (hn : 4 ≤ n) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        (feedbackA1GoodEvent n lam x0 p0)ᶜ ≤
      2 * RelativeVC.regularityPolynomialBadBound n := by
  rw [feedbackA1GoodEvent_compl_measure_eq hlam0 hlamHalf x0 p0]
  exact feedbackVCRegularityGoodEvent_compl_le n hn

/-- Under the actual finite-sample law, the probability of either a feedback tie or a rank-array
VC failure tends to zero. -/
theorem tendsto_feedbackA1GoodEvent_bad_probability
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) :
    Filter.Tendsto
      (fun n ↦ (finiteSampleLaw n : Measure (FiniteSample n))
        (feedbackA1GoodEvent n lam x0 p0)ᶜ)
      Filter.atTop (nhds 0) := by
  convert tendsto_feedbackVCRegularity_bad_probability using 1
  funext n
  exact feedbackA1GoodEvent_compl_measure_eq
    (n := n) hlam0 hlamHalf x0 p0

/-! ## An exact eventual wrapper for varying numerical parameters -/

/-- If the two numerical survival inequalities and the sign conditions hold eventually for
varying `eta n` and `B n`, then eventually the A1 stop equals the bulk/horizon minimum throughout
the actual A1 good event.  The assumptions are precisely the pointwise hypotheses of the survival
theorem, with no additional asymptotic interface. -/
theorem eventually_safeFeedbackA1StopTime_eq_min_bulkExit_horizon_on_good
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℕ → ℝ) (x0 p0 : ℝ) (T : ℕ → ℝ≥0)
    (heta : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ eta n)
    (hB : ∀ᶠ n : ℕ in Filter.atTop, 0 < B n)
    (hsqrt : ∀ᶠ n : ℕ in Filter.atTop,
      4 * (33280 : ℝ) ^ 2 * Real.log n ≤
        eta n ^ 2 * (13 * B n / 16))
    (hlinear : ∀ᶠ n : ℕ in Filter.atTop,
      2 * (33280 : ℝ) * Real.log n ≤
        eta n * (13 * B n / 16)) :
    ∀ᶠ n in Filter.atTop, ∀ sample : FiniteSample n,
      sample ∈ feedbackA1GoodEvent n lam x0 p0 →
        safeFeedbackA1StopTime
            hlam0 hlamHalf (eta n) (B n) x0 p0 (T n) sample =
          min (safeFeedbackBulkExitTime
            hlam0 hlamHalf (B n) x0 p0 sample)
            (T n : WithTop ℝ≥0) := by
  filter_upwards [Filter.eventually_ge_atTop 4, heta, hB, hsqrt, hlinear]
    with n hn hetaN hBN hsqrtN hlinearN
  intro sample hgood
  exact safeFeedbackA1StopTime_eq_min_bulkExit_horizon_of_good
    hn hlam0 hlamHalf hetaN hBN x0 p0 (T n) sample hgood hsqrtN hlinearN

end OTSelector
