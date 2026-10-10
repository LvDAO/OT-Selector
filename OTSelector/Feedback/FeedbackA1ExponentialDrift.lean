import OTSelector.Feedback.FeedbackA1StoppedDrift

/-!
# Exponential drift for the actual A1 feedback current

This file transfers the scalar exponential Lyapunov estimate to the clipped finite-sample
generator and then instantiates it along the actual bulk-thinned counting processes before the
combined A1 stopping coordinate.
-/

open scoped NNReal

namespace OTSelector

/-- The fixed small exponential parameter used in the A1 endpoint estimate. -/
noncomputable def feedbackA1ExponentialTheta (lam : ℝ) : ℝ :=
  lam / 12

/-- The decay coefficient in the A1 exponential Lyapunov drift. -/
noncomputable def feedbackA1ExponentialDecay (lam : ℝ) : ℝ :=
  lam / 2 * (Real.exp (feedbackA1ExponentialTheta lam) - 1)

/-- The additive coefficient in the A1 exponential Lyapunov drift. -/
noncomputable def feedbackA1ExponentialForcing (lam : ℝ) : ℝ :=
  (6 + lam / 2) * (Real.exp (feedbackA1ExponentialTheta lam) - 1)

theorem feedbackA1ExponentialTheta_pos {lam : ℝ} (hlam0 : 0 < lam) :
    0 < feedbackA1ExponentialTheta lam := by
  unfold feedbackA1ExponentialTheta
  positivity

theorem feedbackA1ExponentialTheta_le_one {lam : ℝ} (hlam : lam < 1 / 8) :
    feedbackA1ExponentialTheta lam ≤ 1 := by
  unfold feedbackA1ExponentialTheta
  linarith

theorem feedbackA1ExponentialDecay_pos {lam : ℝ} (hlam0 : 0 < lam) :
    0 < feedbackA1ExponentialDecay lam := by
  exact exponential_decay_coefficient_pos hlam0 (feedbackA1ExponentialTheta_pos hlam0)

theorem feedbackA1ExponentialForcing_nonneg {lam : ℝ} (hlam0 : 0 < lam) :
    0 ≤ feedbackA1ExponentialForcing lam := by
  unfold feedbackA1ExponentialForcing
  exact mul_nonneg (by linarith)
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (feedbackA1ExponentialTheta_pos hlam0).le))

theorem feedbackA1ExponentialForcing_div_decay {lam : ℝ} (hlam0 : 0 < lam) :
    feedbackA1ExponentialForcing lam / feedbackA1ExponentialDecay lam = 1 + 12 / lam := by
  unfold feedbackA1ExponentialForcing feedbackA1ExponentialDecay
  have hexp : Real.exp (feedbackA1ExponentialTheta lam) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (feedbackA1ExponentialTheta_pos hlam0)))
  field_simp [hexp, ne_of_gt hlam0]
  ring

/-- On the regularity event, the strict-interior clipped feedback rate has exponential inward
drift with the fixed parameter `lam / 12`. -/
theorem feedback_clipped_rate_exponential_le
    {lam eta rMinus rPlus : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus)
    (R : ℕ) (k : ℤ) (hlo : -(R : ℤ) < k) (hhi : k < (R : ℤ)) :
    clippedGeneratorRate R (exponentialLyapunov (feedbackA1ExponentialTheta lam))
        (sourceTotalRate rMinus (feedbackSlope lam (k : ℝ)))
        (targetTotalRate rPlus (feedbackSlope lam (k : ℝ))) k ≤
      -feedbackA1ExponentialDecay lam *
          exponentialLyapunov (feedbackA1ExponentialTheta lam) k +
        feedbackA1ExponentialForcing lam := by
  let b : ℤ → ℝ := fun j ↦ sourceTotalRate rMinus (feedbackSlope lam (j : ℝ))
  let d : ℤ → ℝ := fun j ↦ targetTotalRate rPlus (feedbackSlope lam (j : ℝ))
  have hb : ∀ j, 0 ≤ b j ∧ b j ≤ 3 := by
    intro j
    exact sourceTotalRate_bounds (k := (j : ℝ)) hlam0 hlam hreg
  have hd : ∀ j, 0 ≤ d j ∧ d j ≤ 3 := by
    intro j
    exact targetTotalRate_bounds (k := (j : ℝ)) hlam0 hlam hreg
  have hinward : ∀ j, j ≠ 0 →
      if 0 < j then b j - d j ≤ -lam else lam ≤ b j - d j := by
    intro j hj
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
    have h := feedback_rate_inward_drift hlam0 hlam hreg hjR
    by_cases hjpos : 0 < j
    · have hjposR : (0 : ℝ) < j := by exact_mod_cast hjpos
      simpa [b, d, hjpos, hjposR] using h
    · have hjposR : ¬(0 : ℝ) < j := by exact_mod_cast hjpos
      simpa [b, d, hjpos, hjposR] using h
  rw [clippedGeneratorRate_eq_integerBirthDeathGenerator R
    (exponentialLyapunov (feedbackA1ExponentialTheta lam)) b d k hlo hhi]
  have hsmall : 4 * (3 : ℝ) * feedbackA1ExponentialTheta lam ≤ lam := by
    unfold feedbackA1ExponentialTheta
    ring_nf
    exact le_rfl
  have h := exponential_generator_drift_of_small_theta b d (C := 3) (c := lam)
      (theta := feedbackA1ExponentialTheta lam) (by norm_num) hlam0
      (feedbackA1ExponentialTheta_pos hlam0) (feedbackA1ExponentialTheta_le_one hlam)
      hsmall hb hd hinward k
  norm_num [b, d, feedbackA1ExponentialDecay, feedbackA1ExponentialForcing] at h ⊢
  exact h

namespace FiniteSample

variable {n : ℕ}

/-- Before the combined A1 stop, the actual bulk generator satisfies the fixed exponential drift
bound with no abstract drift input remaining. -/
theorem safeFeedbackBulk_clippedGeneratorRate_exponential_le_of_lt_A1Stop
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T t : ℝ≥0)
    (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T sample) :
    clippedGeneratorRate (feedbackA1CurrentCutoff n)
        (exponentialLyapunov (feedbackA1ExponentialTheta lam))
        (safeSourceBulkRate hlam0.le (by linarith) B x0 p0 t sample)
        (safeTargetBulkRate hlam0.le (by linarith) B x0 p0 t sample)
        (CountingProcess.leftCurrentOfCounts
          (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0.le (by linarith) B x0 p0)
          (safeTargetBulkCount hlam0.le (by linarith) B x0 p0) t sample) ≤
      -feedbackA1ExponentialDecay lam *
          exponentialLyapunov (feedbackA1ExponentialTheta lam)
            (CountingProcess.leftCurrentOfCounts
              (safeK0 lam x0 p0)
              (safeSourceBulkCount hlam0.le (by linarith) B x0 p0)
              (safeTargetBulkCount hlam0.le (by linarith) B x0 p0) t sample) +
        feedbackA1ExponentialForcing lam := by
  have hlamHalf : lam < 1 / 2 := by linarith
  let k : ℤ := CountingProcess.leftCurrentOfCounts
    (safeK0 lam x0 p0)
    (safeSourceBulkCount hlam0.le hlamHalf B x0 p0)
    (safeTargetBulkCount hlam0.le hlamHalf B x0 p0) t sample
  have hbulkExit := lt_safeFeedbackBulkExitTime_of_lt_A1Stop
    (n := n) hlam0.le hlamHalf eta B x0 p0 T t sample ht
  have hreg := crossingRegularity_of_lt_safeFeedbackA1Stop
    (n := n) hlam0.le hlamHalf hB heta0 hetaSmall T t sample ht
  have hinterior := leftCurrentOfSafeBulkCounts_strictInterior
    (n := n) hlam0.le hlamHalf B x0 p0 t sample
  rw [safeSourceBulkRate_eq_feedbackSourceIntensity_of_lt_exit
      (n := n) hlam0.le hlamHalf hB t sample hbulkExit,
    safeTargetBulkRate_eq_feedbackTargetIntensity_of_lt_exit
      (n := n) hlam0.le hlamHalf hB t sample hbulkExit]
  simp only [feedbackSourceIntensity, feedbackTargetIntensity]
  exact feedback_clipped_rate_exponential_le hlam0 hlam hreg
    (feedbackA1CurrentCutoff n) k hinterior.1 hinterior.2

end FiniteSample

end OTSelector
