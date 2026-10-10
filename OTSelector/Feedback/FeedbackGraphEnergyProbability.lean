import OTSelector.Feedback.FeedbackGraphEnergyAssembly
import OTSelector.Feedback.FeedbackA2Asymptotic

/-!
# Linear expectation and probability bounds for the actual graph energy

The first-stage majorant is the sum of the stopped left prefix, initial suffix,
and bulk energies. Its expectation is linear in the sample size at the actual
square-root buffer. No energy bound is introduced as an assumption.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace OTSelector.FiniteSample

open CountingProcess

variable {n : ℕ}

/-- An explicit coefficient for the actual first-stage energy expectation. -/
noncomputable def feedbackPreRightEnergyLinearConstant (lam amplitude : ℝ) : ℝ :=
  8 * (1 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2 +
    2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2) * (1 + amplitude ^ 2) +
  2 * ((2 + 5 * amplitude) / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2 +
    4 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2) +
  feedbackBulkEnergyLinearConstant lam amplitude

theorem feedbackPreRightEnergy_integrable_and_integral_le_linear
    {lam eta amplitude : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hamp : 0 < amplitude) {B : ℝ≥0}
    (hB : (B : ℝ) = amplitude * Real.sqrt n) (hBquarter : 4 * (B : ℝ) ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (T : ℝ≥0) (hT : (T : ℝ) ≤ n) :
    Integrable (feedbackPreRightEnergy (n := n) hlam0.le (by linarith) eta B T)
      (finiteSampleLaw n) ∧
    (∫ sample : FiniteSample n,
      feedbackPreRightEnergy hlam0.le (by linarith) eta B T sample ∂(finiteSampleLaw n)) ≤
      feedbackPreRightEnergyLinearConstant lam amplitude * n := by
  have hBpos : 0 < B := by
    change 0 < (B : ℝ)
    rw [hB]
    exact mul_pos hamp (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hBn : (B : ℝ) ≤ n := by nlinarith [B.2]
  have he := feedbackPreRightEnergy_integrable_and_integral_le
    hlam0 hlam hn hBpos hBquarter heta0 hetaSmall T
  refine ⟨he.1, he.2.trans ?_⟩
  have hBsq : (B : ℝ) ^ 2 = amplitude ^ 2 * n := by
    rw [hB, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hBsqrt : (B : ℝ) * Real.sqrt B ≤ amplitude * (n : ℝ) := by
    calc
      (B : ℝ) * Real.sqrt B ≤ (B : ℝ) * Real.sqrt n :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBn) B.2
      _ = amplitude * (n : ℝ) := by
        rw [hB, mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have hleft : (B : ℝ) + (B : ℝ) ^ 2 ≤ (1 + amplitude ^ 2) * n := by
    rw [hBsq]
    nlinarith
  have hi : 2 * (B : ℝ) + 5 * (B : ℝ) * Real.sqrt B ≤ (2 + 5 * amplitude) * n := by
    nlinarith
  have ht : (6 + 81 / lam) * (T : ℝ) ≤ (6 + 81 / lam) * n :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have hl := mul_le_mul_of_nonneg_left hleft
    (show 0 ≤ 8 * (1 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2 +
      2 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2) by positivity)
  have hi' := div_le_div_of_nonneg_right hi
    (sq_nonneg (lowerOccupationCountRate ((1 : ℝ) / 2)))
  have hb := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (add_le_add hi ht) (show 0 ≤ 2 * lam by positivity))
    (show 0 ≤ 6 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2 by positivity)
  unfold feedbackPreRightEnergyLinearConstant feedbackBulkEnergyLinearConstant
  simp only [div_eq_mul_inv] at hl hi' hb ⊢
  nlinarith only [hl, hi', hb]

/-- Markov's bound for the actual first-stage energy under the true finite-sample law. -/
theorem measureReal_feedbackPreRightEnergy_tail_le
    {lam eta amplitude K : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hamp : 0 < amplitude) {B : ℝ≥0}
    (hB : (B : ℝ) = amplitude * Real.sqrt n) (hBquarter : 4 * (B : ℝ) ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (T : ℝ≥0) (hT : (T : ℝ) ≤ n) (hK : 0 < K) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {sample | K * n ≤ feedbackPreRightEnergy hlam0.le (by linarith) eta B T sample} ≤
      feedbackPreRightEnergyLinearConstant lam amplitude / K := by
  have he := feedbackPreRightEnergy_integrable_and_integral_le_linear
    hlam0 hlam hn hamp hB hBquarter heta0 hetaSmall T hT
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (Filter.Eventually.of_forall fun sample ↦
      feedbackPreRightEnergy_nonneg sample hlam0.le (by linarith) eta B T) he.1 (K * n)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ hK).mpr
  nlinarith [he.2]

/-- The square-root buffer eventually satisfies the left-prefix quarter-range condition. -/
theorem eventually_feedback_buffer_quarter (amplitude : ℝ) :
    ∀ᶠ n : ℕ in atTop, 4 * (amplitude * Real.sqrt n) ≤ (n : ℝ) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually (eventually_ge_atTop (4 * amplitude))] with n hn
  have hm := mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg (n : ℝ))
  rw [Real.mul_self_sqrt (Nat.cast_nonneg n)] at hm
  nlinarith only [hm]

/-- Explicit coefficient after the two actual random-energy bounds and interval/current
controls are imposed. The remaining boundary errors cost only another constant times `n`. -/
noncomputable def feedbackGraphEnergyLinearConstant
    (amplitude Kpre Kright L a W : ℝ) : ℝ :=
  Kpre + 2 * L * W ^ 2 +
    amplitude ^ 2 * (64 * Kright + 4 * (512 + (10 * L + 8 * a + 9) ^ 2))

theorem stoppedGraphComparisonEnergy_le_linear_of_actual_controls
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (eta : ℝ) (B T : ℝ≥0)
    {amplitude Kpre Kright L a W error : ℝ}
    (hB : (B : ℝ) = amplitude * Real.sqrt n) (hB1 : 1 ≤ (B : ℝ))
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hW : 0 ≤ W)
    (herr0 : 0 ≤ error) (herr : error ≤ Real.sqrt B)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hleftGeneric : sample ∈ leftHeightGenericEvent n)
    (hleft : leftRateExitTime n B sample = (B : WithTop ℝ≥0))
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0))
    (hgeometry : (B : ℝ) + T ≤
      (n : ℝ) - (8 * (L * Real.sqrt B) + 1) - 8 * (a * Real.sqrt B + error))
    (hdensity : sample.GraphIntervalLowerDensity
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
      ((B : ℝ) + T) ((n : ℝ) - (8 * (L * Real.sqrt B) + 1)) (1 / 8) error)
    (hsource : sample.graphCrossingRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) ≤
      sample.graphSourceBackwardWindowCount
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) W)
    (htarget : sample.graphCrossingRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) ≤
      sample.graphTargetBackwardWindowCount
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) W)
    (hcurrentR : |sample.graphRankCurrent
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T)| ≤ L)
    (hcurrentH : |sample.graphRankCurrent
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
      ((n : ℝ) - (8 * (L * Real.sqrt B) + 1))| ≤ a * Real.sqrt B)
    (hq : |actualRightTailFrozenHeight hlam0 hlamHalf B 0 T sample| ≤ L * Real.sqrt B)
    (hcount : (sample.graphTerminalRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ((B : ℝ) + T) : ℝ) ≤ 4 * B)
    (hpre : feedbackPreRightEnergy hlam0 hlamHalf eta B T sample ≤ Kpre * n)
    (hright : rightBoundaryFrozenEnergy lam ((B : ℝ) + T) ((n : ℝ) + 2 * B)
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T) sample ≤ Kright * (B : ℝ) ^ 2) :
    sample.graphComparisonEnergy
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) ≤
      feedbackGraphEnergyLinearConstant amplitude Kpre Kright L a W * n := by
  have hsqrt1 : 1 ≤ Real.sqrt (B : ℝ) := by
    simpa using Real.sqrt_le_sqrt hB1
  have hsqrt0 := Real.sqrt_nonneg (B : ℝ)
  have hV : 0 ≤ 8 * (a * Real.sqrt B + error) := by positivity
  have hRH : (B : ℝ) + T ≤ (n : ℝ) - (8 * (L * Real.sqrt B) + 1) := by
    linarith
  have hall := sample.stoppedGraphComparisonEnergy_le_actual_energies
    hlam0 hlamHalf hn eta B T hNoTie hleftGeneric hleft hstop hRH
    (show (n : ℝ) - (8 * (L * Real.sqrt B) + 1) ≤ n by
      linarith [mul_nonneg hL hsqrt0])
    (by norm_num : (0 : ℝ) < 1 / 8) herr0 hW hV hgeometry hdensity hsource htarget hcurrentR
    (show |sample.graphRankCurrent
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
        ((n : ℝ) - (8 * (L * Real.sqrt B) + 1))| ≤
        (1 / 8) * (8 * (a * Real.sqrt B + error)) - error by linarith)
    hq hcount
  have herrsq : error ^ 2 ≤ (B : ℝ) := by
    have hp := pow_le_pow_left₀ herr0 herr 2
    simpa only [Real.sq_sqrt (show 0 ≤ (B : ℝ) from B.2)] using hp
  have hwidth0 : 0 ≤ (n : ℝ) + 2 * (L * Real.sqrt B) -
      ((n : ℝ) - (8 * (L * Real.sqrt B) + 1)) + 8 * (a * Real.sqrt B + error) := by
    nlinarith [mul_nonneg hL hsqrt0, mul_nonneg ha hsqrt0]
  have hwidth : (n : ℝ) + 2 * (L * Real.sqrt B) -
      ((n : ℝ) - (8 * (L * Real.sqrt B) + 1)) + 8 * (a * Real.sqrt B + error) ≤
      (10 * L + 8 * a + 9) * Real.sqrt B := by nlinarith
  have hwidthsq := pow_le_pow_left₀ hwidth0 hwidth 2
  simp only [mul_pow, Real.sq_sqrt (show 0 ≤ (B : ℝ) from B.2)] at hwidthsq
  have hterminal := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left herrsq (show (0 : ℝ) ≤ 512 by norm_num))
      hwidthsq) (show 0 ≤ 4 * (B : ℝ) by positivity)
  have hcross : 2 * L * W ^ 2 ≤ 2 * L * W ^ 2 * (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa using mul_le_mul_of_nonneg_left hn1 (show 0 ≤ 2 * L * W ^ 2 by positivity)
  have hBsq : (B : ℝ) ^ 2 = amplitude ^ 2 * n := by
    rw [hB, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  norm_num at hall
  calc
    _ ≤ Kpre * n + 2 * L * W ^ 2 * n + 64 * Kright * (B : ℝ) ^ 2 +
        4 * (512 + (10 * L + 8 * a + 9) ^ 2) * (B : ℝ) ^ 2 := by
      nlinarith only [hall, hpre, hright, hterminal, hcross]
    _ = _ := by
      rw [hBsq]
      unfold feedbackGraphEnergyLinearConstant
      ring

end OTSelector.FiniteSample
