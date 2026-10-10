import OTSelector.Feedback.FiniteHistoryHazardGeometry

/-!
# Slabs of a fixed affine feedback section

This file isolates the deterministic geometry needed before the probabilistic intensity layer.
For `0 ≤ lam < 1/2`, the strict remaining region at a later coordinate is contained in the
strict remaining region at an earlier coordinate.  Its set difference is therefore the genuine
`(s,t]` slab, and the existing rank-strip area identity computes its one-point mass.

Nothing here identifies this fixed-section slab with an adaptive compensator.  In particular,
the conditional statement below, when used, is only the elementary conditional probability for
one point under a fixed measurable region.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## Positivity of the marked factors -/

private theorem sourceMarkedFactor_feedbackSlope_pos
    {lam q u : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hq : |q| ≤ lam) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < sourceMarkedFactor q u := by
  have hq_le : q ≤ lam := (le_abs_self q).trans hq
  have hu_comp0 : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hu_comp1 : 1 - u ≤ 1 := by linarith
  have hprod : q * (1 - u) ≤ lam * (1 - u) :=
    mul_le_mul_of_nonneg_right hq_le hu_comp0
  have hprod' : lam * (1 - u) ≤ lam := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu_comp1 hlam0
  dsimp [sourceMarkedFactor]
  nlinarith

private theorem targetMarkedFactor_feedbackSlope_pos
    {lam q v : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hq : |q| ≤ lam) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < targetMarkedFactor q v := by
  have hq_ge : -lam ≤ q := neg_le_of_abs_le hq
  have hvsum0 : 0 ≤ 1 + v := by linarith
  have hvsum2 : 1 + v ≤ 2 := by linarith
  have hprod : (-lam) * (1 + v) ≤ q * (1 + v) :=
    mul_le_mul_of_nonneg_right hq_ge hvsum0
  have hprod' : (-lam) * (1 + v) ≥ -2 * lam := by
    have hbound : lam * (1 + v) ≤ lam * 2 :=
      mul_le_mul_of_nonneg_left hvsum2 hlam0
    nlinarith
  dsimp [targetMarkedFactor]
  nlinarith

/-! ## Nested strict remaining regions -/

theorem sourceRawRemainingSetAt_subset
    (state : FeedbackStepState n) (lam s t : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t) :
    sourceRawRemainingSetAt n lam state t ⊆ sourceRawRemainingSetAt n lam state s := by
  intro z hzt
  have hq : |state.slope lam| ≤ lam :=
    abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0
  have hz0 : 0 ≤ (z.2 : ℝ) := z.2.property.1
  have hz1 : (z.2 : ℝ) ≤ 1 := z.2.property.2
  have hfactor : 0 < sourceMarkedFactor (state.slope lam) (z.2 : ℝ) :=
    sourceMarkedFactor_feedbackSlope_pos hlam0 hlamHalf hq hz0 hz1
  have hboundary := sourceBoundary_segment_sub state.x state.p (state.slope lam)
    s t (z.2 : ℝ)
  have hinc : 0 ≤ (t - s) * sourceMarkedFactor (state.slope lam) (z.2 : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hst) hfactor.le
  change t < (n : ℝ) * (z.1 : ℝ) +
      segmentCurve state.x state.p (state.slope lam) t * (1 - (z.2 : ℝ)) at hzt
  change s < (n : ℝ) * (z.1 : ℝ) +
      segmentCurve state.x state.p (state.slope lam) s * (1 - (z.2 : ℝ))
  have hboundary' :
      (t - segmentCurve state.x state.p (state.slope lam) t * (1 - (z.2 : ℝ))) -
          (s - segmentCurve state.x state.p (state.slope lam) s * (1 - (z.2 : ℝ))) =
        (t - s) * sourceMarkedFactor (state.slope lam) (z.2 : ℝ) := by
    simpa [sourceBoundary] using hboundary
  nlinarith

theorem targetRawRemainingSetAt_subset
    (state : FeedbackStepState n) (lam s t : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t) :
    targetRawRemainingSetAt n lam state t ⊆ targetRawRemainingSetAt n lam state s := by
  intro z hzt
  have hq : |state.slope lam| ≤ lam :=
    abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0
  have hz0 : 0 ≤ (z.2 : ℝ) := z.2.property.1
  have hz1 : (z.2 : ℝ) ≤ 1 := z.2.property.2
  have hfactor : 0 < targetMarkedFactor (state.slope lam) (z.2 : ℝ) :=
    targetMarkedFactor_feedbackSlope_pos hlam0 hlamHalf hq hz0 hz1
  have hboundary := targetBoundary_segment_sub state.x state.p (state.slope lam)
    s t (z.2 : ℝ)
  have hinc : 0 ≤ (t - s) * targetMarkedFactor (state.slope lam) (z.2 : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hst) hfactor.le
  change t < (n : ℝ) * (z.1 : ℝ) -
      segmentCurve state.x state.p (state.slope lam) t * (1 + (z.2 : ℝ)) at hzt
  change s < (n : ℝ) * (z.1 : ℝ) -
      segmentCurve state.x state.p (state.slope lam) s * (1 + (z.2 : ℝ))
  have hboundary' :
      (t + segmentCurve state.x state.p (state.slope lam) t * (1 + (z.2 : ℝ))) -
          (s + segmentCurve state.x state.p (state.slope lam) s * (1 + (z.2 : ℝ))) =
        (t - s) * targetMarkedFactor (state.slope lam) (z.2 : ℝ) := by
    simpa [targetBoundary] using hboundary
  nlinarith

/-! ## Exact one-point slab masses -/

theorem unitSquareUniform_sourceRawRemainingSetAt_sdiff_real
    (state : FeedbackStepState n) (lam s t : ℝ) (hn : 0 < n) (hst : s ≤ t)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u) ∧
      (∀ u : UnitMark,
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n)) :
    (unitSquareUniform : Measure MarkedHeight).real
        (sourceRawRemainingSetAt n lam state s \
          sourceRawRemainingSetAt n lam state t) =
      (t - s) * (1 - state.slope lam / 2) / n := by
  have hsub := sourceRawRemainingSetAt_subset state lam s t
    hlam0 hlamHalf hst
  rw [measureReal_sdiff hsub
    (isOpen_sourceRawRemainingSetAt lam state t).measurableSet]
  exact unitSquareUniform_sourceRawRemainingSetAt_mass_sub state lam s t hn hst hbulk

theorem unitSquareUniform_targetRawRemainingSetAt_sdiff_real
    (state : FeedbackStepState n) (lam s t : ℝ) (hn : 0 < n) (hst : s ≤ t)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v) ∧
      (∀ v : UnitMark,
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)) :
    (unitSquareUniform : Measure MarkedHeight).real
        (targetRawRemainingSetAt n lam state s \
          targetRawRemainingSetAt n lam state t) =
      (t - s) * (1 + 3 * state.slope lam / 2) / n := by
  have hsub := targetRawRemainingSetAt_subset state lam s t
    hlam0 hlamHalf hst
  rw [measureReal_sdiff hsub
    (isOpen_targetRawRemainingSetAt lam state t).measurableSet]
  exact unitSquareUniform_targetRawRemainingSetAt_mass_sub state lam s t hn hst hbulk

/-! ## Optional elementary conditional probability -/

theorem unitSquareUniform_sourceRawRemainingSetAt_cond_sdiff_real
    (state : FeedbackStepState n) (lam s t : ℝ) (hn : 0 < n) (hst : s ≤ t)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u) ∧
      (∀ u : UnitMark,
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n))
    (hRs : 0 < (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSetAt n lam state s)) :
    ((unitSquareUniform : Measure MarkedHeight)[
      sourceRawRemainingSetAt n lam state s \
        sourceRawRemainingSetAt n lam state t |
      sourceRawRemainingSetAt n lam state s]).toReal =
      ((t - s) * (1 - state.slope lam / 2) / n) /
        (unitSquareUniform : Measure MarkedHeight).real
          (sourceRawRemainingSetAt n lam state s) := by
  let μ : Measure MarkedHeight := unitSquareUniform
  let Rs := sourceRawRemainingSetAt n lam state s
  let Rt := sourceRawRemainingSetAt n lam state t
  have hRs_meas : MeasurableSet Rs := by
    exact (isOpen_sourceRawRemainingSetAt lam state s).measurableSet
  have hcond := ProbabilityTheory.cond_apply hRs_meas μ (Rs \ Rt)
  have hinter : Rs ∩ (Rs \ Rt) = Rs \ Rt := by
    exact inter_eq_right.mpr sdiff_subset
  rw [hcond, hinter]
  change ENNReal.toReal ((μ Rs)⁻¹ * μ (Rs \ Rt)) = _
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hRs_real : 0 < ENNReal.toReal (μ Rs) := by
    simpa [Measure.real, μ, Rs] using hRs
  have hdiff_real := unitSquareUniform_sourceRawRemainingSetAt_sdiff_real
    state lam s t hn hst hlam0 hlamHalf hbulk
  have hdiff_cast : ENNReal.toReal (μ (Rs \ Rt)) =
      (t - s) * (1 - state.slope lam / 2) / n := by
    simpa [μ, Rs, Rt, Measure.real] using hdiff_real
  rw [hdiff_cast]
  have hden : ENNReal.toReal (μ Rs) ≠ 0 := ne_of_gt hRs_real
  simp only [Measure.real, μ, Rs, div_eq_mul_inv]
  field_simp [hden]

theorem unitSquareUniform_targetRawRemainingSetAt_cond_sdiff_real
    (state : FeedbackStepState n) (lam s t : ℝ) (hn : 0 < n) (hst : s ≤ t)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v) ∧
      (∀ v : UnitMark,
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n))
    (hRs : 0 < (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSetAt n lam state s)) :
    ((unitSquareUniform : Measure MarkedHeight)[
      targetRawRemainingSetAt n lam state s \
        targetRawRemainingSetAt n lam state t |
      targetRawRemainingSetAt n lam state s]).toReal =
      ((t - s) * (1 + 3 * state.slope lam / 2) / n) /
        (unitSquareUniform : Measure MarkedHeight).real
          (targetRawRemainingSetAt n lam state s) := by
  let μ : Measure MarkedHeight := unitSquareUniform
  let Rs := targetRawRemainingSetAt n lam state s
  let Rt := targetRawRemainingSetAt n lam state t
  have hRs_meas : MeasurableSet Rs := by
    exact (isOpen_targetRawRemainingSetAt lam state s).measurableSet
  have hcond := ProbabilityTheory.cond_apply hRs_meas μ (Rs \ Rt)
  have hinter : Rs ∩ (Rs \ Rt) = Rs \ Rt := by
    exact inter_eq_right.mpr sdiff_subset
  rw [hcond, hinter]
  change ENNReal.toReal ((μ Rs)⁻¹ * μ (Rs \ Rt)) = _
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hRs_real : 0 < ENNReal.toReal (μ Rs) := by
    simpa [Measure.real, μ, Rs] using hRs
  have hdiff_real := unitSquareUniform_targetRawRemainingSetAt_sdiff_real
    state lam s t hn hst hlam0 hlamHalf hbulk
  have hdiff_cast : ENNReal.toReal (μ (Rs \ Rt)) =
      (t - s) * (1 + 3 * state.slope lam / 2) / n := by
    simpa [μ, Rs, Rt, Measure.real] using hdiff_real
  rw [hdiff_cast]
  have hden : ENNReal.toReal (μ Rs) ≠ 0 := ne_of_gt hRs_real
  simp only [Measure.real, μ, Rs, div_eq_mul_inv]
  field_simp [hden]

end OTSelector
