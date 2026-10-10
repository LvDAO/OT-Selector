import OTSelector.Feedback.FeedbackA2HorizonRange

/-!
# I4 for the actual stopped feedback graph

The A1 stop occurs no later than the shear exit. Continuity therefore bounds the whole
stopped, constantly extended graph by `B / 8`. For a square-root buffer its normalized
uniform envelope vanishes. This uses the actual stop on every no-tie sample and needs
no survival event or assumed envelope estimate.
-/

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace OTSelector.FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-- The stopped graph stays within the shear boundary, including the stopping point. -/
theorem abs_stoppedContinuationFeedbackGraph_curve_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta : ℝ) {B : ℝ} (hB : 0 < B) (T : ℝ≥0)
    (hNoTie : sample.NoFeedbackTies lam B 0) (x : ℝ) :
    |(sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve x| ≤ B / 8 := by
  apply sample.abs_horizonFeedbackGraph_curve_le_of_horizon_le_bulkExit
    hlam0 hlamHalf hB hNoTie
  rw [sample.coe_safeFeedbackA1StopElapsed]
  exact min_le_left _ _

/-- Deterministic normalized envelope bound for the actual stopped graph. -/
theorem normalizedStoppedContinuationFeedbackCurve_supAbs_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (eta : ℝ) {B : ℝ} (hB : 0 < B) (T : ℝ≥0)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    graphSupAbs (sample.normalizedStoppedContinuationFeedbackCurve
      hlam0 hlamHalf eta B T) ≤ (B / 8) / (n : ℝ) := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨z, rfl⟩
  unfold normalizedStoppedContinuationFeedbackCurve normalizedCurveOfGraph
    normalizedGraph rescaleGraph
  dsimp only
  rw [abs_div, abs_of_pos (show 0 < (n : ℝ) by exact_mod_cast hn)]
  exact div_le_div_of_nonneg_right
    (sample.abs_stoppedContinuationFeedbackGraph_curve_le
      hlam0 hlamHalf eta hB T hNoTie _) (Nat.cast_nonneg n)

/-- I4 in the varying-sample-space formulation. For fixed positive buffer amplitude,
every fixed normalized envelope threshold eventually has probability zero. -/
theorem eventually_normalizedStoppedContinuationFeedbackCurve_supAbs_tail_eq_zero
    {lam amplitude : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hAmplitude : 0 < amplitude) (eta : ℕ → ℝ) (T : ℕ → ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (finiteSampleLaw n : Measure (FiniteSample n)).real {sample |
        ε ≤ graphSupAbs (sample.normalizedStoppedContinuationFeedbackCurve
          hlam0 hlamHalf (eta n) (amplitude * Real.sqrt n) (T n))} = 0 := by
  have hSqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hSqrt.eventually (eventually_gt_atTop (amplitude / (8 * ε))),
    eventually_gt_atTop (0 : ℕ)] with n hScale hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hSqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hB : 0 < amplitude * Real.sqrt (n : ℝ) := mul_pos hAmplitude hSqrtPos
  have hSmall : (amplitude * Real.sqrt (n : ℝ) / 8) / (n : ℝ) < ε := by
    have hA : amplitude < Real.sqrt (n : ℝ) * (8 * ε) :=
      (div_lt_iff₀ (by positivity : 0 < 8 * ε)).mp hScale
    have hMul := mul_lt_mul_of_pos_right hA hSqrtPos
    have hSquare := Real.mul_self_sqrt hnR.le
    apply (div_lt_iff₀ hnR).2
    nlinarith
  apply (measureReal_eq_zero_iff).mpr
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [finiteSampleLaw_noFeedbackTies_ae
    (n := n) (x0 := amplitude * Real.sqrt n) (p0 := 0) hlam0 hlamHalf]
    with sample hNoTie
  exact not_le.mpr ((sample.normalizedStoppedContinuationFeedbackCurve_supAbs_le
    hlam0 hlamHalf hn (eta n) hB (T n) hNoTie).trans_lt hSmall)

end OTSelector.FiniteSample
