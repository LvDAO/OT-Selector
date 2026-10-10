import OTSelector.Feedback.FeedbackBulkMask
import OTSelector.Feedback.StateMeasurable

/-!
# Joint measurability and bulk bounds for fixed-state feedback rates

The affine source and target rates associated with a `FeedbackStepState` are jointly measurable
in the state and observation coordinate.  On the geometric bulk region they are nonnegative and
bounded by `feedbackBulkRateCap`.  No separate history-validity premise is needed: the seen sets
are finsets of `Fin n`, so their cardinalities are at most `n` for every state.
-/

open MeasureTheory Set
open scoped Classical

namespace OTSelector

variable {n : ℕ}

/-- The fixed-state source rate is jointly measurable in the state and observation coordinate. -/
theorem measurable_sourceUnclippedStateRateAt_joint (lam : ℝ) :
    Measurable fun pair : FeedbackStepState n × ℝ ↦
      FeedbackStepState.sourceUnclippedStateRateAt lam pair.1 pair.2 := by
  have hcardNat : Measurable fun pair : FeedbackStepState n × ℝ ↦
      pair.1.seenSource.card :=
    FiniteSample.measurable_finset_card.comp
      (FeedbackStepState.measurable_seenSource.comp measurable_fst)
  have hcard : Measurable fun pair : FeedbackStepState n × ℝ ↦
      (pair.1.seenSource.card : ℝ) :=
    (continuous_of_discreteTopology (f := fun k : ℕ ↦ (k : ℝ))).measurable.comp hcardNat
  have hx : Measurable fun pair : FeedbackStepState n × ℝ ↦ pair.1.x :=
    FeedbackStepState.measurable_x.comp measurable_fst
  have hp : Measurable fun pair : FeedbackStepState n × ℝ ↦ pair.1.p :=
    FeedbackStepState.measurable_p.comp measurable_fst
  have hslope : Measurable fun pair : FeedbackStepState n × ℝ ↦ pair.1.slope lam :=
    (FeedbackStepState.measurable_slope lam).comp measurable_fst
  have hcurve : Measurable fun pair : FeedbackStepState n × ℝ ↦
      segmentCurve pair.1.x pair.1.p (pair.1.slope lam) pair.2 := by
    simp only [segmentCurve]
    exact hp.add (hslope.mul (measurable_snd.sub hx))
  have hnum : Measurable fun pair : FeedbackStepState n × ℝ ↦
      (n : ℝ) - (pair.1.seenSource.card : ℝ) :=
    measurable_const.sub hcard
  have hden : Measurable fun pair : FeedbackStepState n × ℝ ↦
      sourceUnclippedRemainingMass n
        (segmentCurve pair.1.x pair.1.p (pair.1.slope lam) pair.2) pair.2 := by
    simp only [sourceUnclippedRemainingMass]
    exact (measurable_const.sub measurable_snd).add (hcurve.div measurable_const)
  have hfactor : Measurable fun pair : FeedbackStepState n × ℝ ↦
      1 - pair.1.slope lam / 2 :=
    measurable_const.sub (hslope.div measurable_const)
  change Measurable fun pair : FeedbackStepState n × ℝ ↦
    ((n : ℝ) - (pair.1.seenSource.card : ℝ)) /
        sourceUnclippedRemainingMass n
          (segmentCurve pair.1.x pair.1.p (pair.1.slope lam) pair.2) pair.2 *
      (1 - pair.1.slope lam / 2)
  convert (hnum.div hden).mul hfactor using 1
  funext pair
  rfl

/-- The fixed-state target rate is jointly measurable in the state and observation coordinate. -/
theorem measurable_targetUnclippedStateRateAt_joint (lam : ℝ) :
    Measurable fun pair : FeedbackStepState n × ℝ ↦
      FeedbackStepState.targetUnclippedStateRateAt lam pair.1 pair.2 := by
  have hcardNat : Measurable fun pair : FeedbackStepState n × ℝ ↦
      pair.1.seenTarget.card :=
    FiniteSample.measurable_finset_card.comp
      (FeedbackStepState.measurable_seenTarget.comp measurable_fst)
  have hcard : Measurable fun pair : FeedbackStepState n × ℝ ↦
      (pair.1.seenTarget.card : ℝ) :=
    (continuous_of_discreteTopology (f := fun k : ℕ ↦ (k : ℝ))).measurable.comp hcardNat
  have hx : Measurable fun pair : FeedbackStepState n × ℝ ↦ pair.1.x :=
    FeedbackStepState.measurable_x.comp measurable_fst
  have hp : Measurable fun pair : FeedbackStepState n × ℝ ↦ pair.1.p :=
    FeedbackStepState.measurable_p.comp measurable_fst
  have hslope : Measurable fun pair : FeedbackStepState n × ℝ ↦ pair.1.slope lam :=
    (FeedbackStepState.measurable_slope lam).comp measurable_fst
  have hcurve : Measurable fun pair : FeedbackStepState n × ℝ ↦
      segmentCurve pair.1.x pair.1.p (pair.1.slope lam) pair.2 := by
    simp only [segmentCurve]
    exact hp.add (hslope.mul (measurable_snd.sub hx))
  have hnum : Measurable fun pair : FeedbackStepState n × ℝ ↦
      (n : ℝ) - (pair.1.seenTarget.card : ℝ) :=
    measurable_const.sub hcard
  have hden : Measurable fun pair : FeedbackStepState n × ℝ ↦
      targetUnclippedRemainingMass n
        (segmentCurve pair.1.x pair.1.p (pair.1.slope lam) pair.2) pair.2 := by
    simp only [targetUnclippedRemainingMass]
    exact (measurable_const.sub measurable_snd).sub
      ((measurable_const.mul hcurve).div measurable_const)
  have hfactor : Measurable fun pair : FeedbackStepState n × ℝ ↦
      1 + 3 * pair.1.slope lam / 2 :=
    measurable_const.add ((measurable_const.mul hslope).div measurable_const)
  change Measurable fun pair : FeedbackStepState n × ℝ ↦
    ((n : ℝ) - (pair.1.seenTarget.card : ℝ)) /
        targetUnclippedRemainingMass n
          (segmentCurve pair.1.x pair.1.p (pair.1.slope lam) pair.2) pair.2 *
      (1 + 3 * pair.1.slope lam / 2)
  convert (hnum.div hden).mul hfactor using 1
  funext pair
  rfl

private theorem rate_le_four_mul_div
    {B N a d q : ℝ} (hB : 0 < B) (hd : 0 < d)
    (hdhalf : B / 2 ≤ d) (hN : 0 ≤ N) (haN : a ≤ N)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2) :
    a / d * q ≤ 4 * N / B := by
  have hhalf : 0 < B / 2 := by positivity
  have hinv : 1 / d ≤ 1 / (B / 2) :=
    one_div_le_one_div_of_le hhalf hdhalf
  have hratio : a / d ≤ N / (B / 2) := by
    calc
      a / d = a * (1 / d) := by ring
      _ ≤ N * (1 / d) := mul_le_mul_of_nonneg_right haN (by positivity)
      _ ≤ N * (1 / (B / 2)) := mul_le_mul_of_nonneg_left hinv hN
      _ = N / (B / 2) := by ring
  calc
    a / d * q ≤ (N / (B / 2)) * q := mul_le_mul_of_nonneg_right hratio hq0
    _ ≤ (N / (B / 2)) * 2 :=
      mul_le_mul_of_nonneg_left hq2 (div_nonneg hN hhalf.le)
    _ = 4 * N / B := by
      field_simp [ne_of_gt hB]
      ring

/-- On the bulk region, the arbitrary-state source rate lies between zero and the deterministic
bulk cap. -/
theorem sourceUnclippedStateRateAt_mem_Icc_of_bulk
    (state : FeedbackStepState n) {lam B x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hB : 0 < B)
    (hbulk : feedbackBulkRegion n B x
      (segmentCurve state.x state.p (state.slope lam) x)) :
    FeedbackStepState.sourceUnclippedStateRateAt lam state x ∈
      Icc 0 (feedbackBulkRateCap n B) := by
  have hden_ge := sourceUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
  have hden : 0 < sourceUnclippedRemainingMass n
      (segmentCurve state.x state.p (state.slope lam) x) x := by
    nlinarith [hden_ge]
  have hden_half : B / 2 ≤ sourceUnclippedRemainingMass n
      (segmentCurve state.x state.p (state.slope lam) x) x := by
    nlinarith [hden_ge]
  have hcard_le : state.seenSource.card ≤ n := by
    simpa using state.seenSource.card_le_univ
  have hcard_le_real : (state.seenSource.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcard_le
  have hnum0 : 0 ≤ (n : ℝ) - (state.seenSource.card : ℝ) :=
    sub_nonneg.mpr hcard_le_real
  have hnumN : (n : ℝ) - (state.seenSource.card : ℝ) ≤ (n : ℝ) := by
    exact sub_le_self _ (by positivity)
  have hslope : |state.slope lam| ≤ lam := by
    simpa only [FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0)
  have hslope_bounds := abs_le.mp hslope
  have hfactor0 : 0 ≤ 1 - state.slope lam / 2 := by
    nlinarith [hslope_bounds.2]
  have hfactor2 : 1 - state.slope lam / 2 ≤ 2 := by
    nlinarith [hslope_bounds.1, hlamHalf]
  rw [Set.mem_Icc]
  constructor
  · simp only [FeedbackStepState.sourceUnclippedStateRateAt]
    exact mul_nonneg (div_nonneg hnum0 hden.le) hfactor0
  · rw [feedbackBulkRateCap_eq_div hB]
    simp only [FeedbackStepState.sourceUnclippedStateRateAt]
    exact rate_le_four_mul_div hB hden hden_half (by positivity)
      hnumN hfactor0 hfactor2

/-- On the bulk region, the arbitrary-state target rate lies between zero and the deterministic
bulk cap. -/
theorem targetUnclippedStateRateAt_mem_Icc_of_bulk
    (state : FeedbackStepState n) {lam B x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hB : 0 < B)
    (hbulk : feedbackBulkRegion n B x
      (segmentCurve state.x state.p (state.slope lam) x)) :
    FeedbackStepState.targetUnclippedStateRateAt lam state x ∈
      Icc 0 (feedbackBulkRateCap n B) := by
  have hden_ge := targetUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
  have hden : 0 < targetUnclippedRemainingMass n
      (segmentCurve state.x state.p (state.slope lam) x) x := by
    nlinarith [hden_ge]
  have hden_half : B / 2 ≤ targetUnclippedRemainingMass n
      (segmentCurve state.x state.p (state.slope lam) x) x := by
    nlinarith [hden_ge]
  have hcard_le : state.seenTarget.card ≤ n := by
    simpa using state.seenTarget.card_le_univ
  have hcard_le_real : (state.seenTarget.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcard_le
  have hnum0 : 0 ≤ (n : ℝ) - (state.seenTarget.card : ℝ) :=
    sub_nonneg.mpr hcard_le_real
  have hnumN : (n : ℝ) - (state.seenTarget.card : ℝ) ≤ (n : ℝ) := by
    exact sub_le_self _ (by positivity)
  have hslope : |state.slope lam| ≤ lam := by
    simpa only [FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0)
  have hslope_bounds := abs_le.mp hslope
  have hfactor0 : 0 ≤ 1 + 3 * state.slope lam / 2 := by
    nlinarith [hslope_bounds.1, hlamHalf]
  have hfactor2 : 1 + 3 * state.slope lam / 2 ≤ 2 := by
    nlinarith [hslope_bounds.2, hlamHalf]
  rw [Set.mem_Icc]
  constructor
  · simp only [FeedbackStepState.targetUnclippedStateRateAt]
    exact mul_nonneg (div_nonneg hnum0 hden.le) hfactor0
  · rw [feedbackBulkRateCap_eq_div hB]
    simp only [FeedbackStepState.targetUnclippedStateRateAt]
    exact rate_le_four_mul_div hB hden hden_half (by positivity)
      hnumN hfactor0 hfactor2

end OTSelector
