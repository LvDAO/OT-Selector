import OTSelector.Feedback.FeedbackI3BacklogSum
import OTSelector.Feedback.FeedbackA1Excursion
import OTSelector.Feedback.FeedbackA2Asymptotic
import OTSelector.Feedback.FeedbackStoppedGraphEnergyBridge

/-!
# Explicit energy of the actual interior bulk gaps

The actual initial-current cubic moment closes the expectation bound for the two interior
same-rank gap families.  For a buffer `B = amplitude * sqrt n` and a horizon at most `n`, the
bound is linear in `n`, with an explicit coefficient independent of `n`.

These gaps belong to the raw full-recursion graph and are stopped by A1.  On measurable survival
sets, the same bound transfers to the bulk energy of the stopped-continuation graph.  Boundary
and terminal edges remain separate geometric steps.
-/

open Filter MeasureTheory Set
open scoped BigOperators NNReal

namespace OTSelector.FiniteSample

open CountingProcess

variable {n : ℕ}

/-- The actual source and target interior same-rank gaps, summed in square. -/
noncomputable def feedbackBulkInteriorEnergy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) : FiniteSample n → ℝ :=
  fun sample ↦
    (∑ r : Fin n,
      sourceInteriorStoppedFullRankGap hlam0 hlamHalf eta B B 0 T r sample ^ 2) +
    ∑ r : Fin n,
      targetInteriorStoppedFullRankGap hlam0 hlamHalf eta B B 0 T r sample ^ 2

/-- The actual bulk gap energy has an explicit expectation bound, with the initial cubic
moment and both counting-process intensities discharged under the finite-sample law. -/
theorem feedbackBulkInteriorEnergy_integrable_and_integral_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (hBn : B ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) :
    Integrable (feedbackBulkInteriorEnergy (n := n) hlam0.le (by linarith) eta B T)
        (finiteSampleLaw n) ∧
      (∫ sample : FiniteSample n,
        feedbackBulkInteriorEnergy (n := n) hlam0.le (by linarith) eta B T sample
        ∂(finiteSampleLaw n)) ≤
      (6 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2) *
          ((2 * B + 5 * B * Real.sqrt B + (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) +
        4 * (n : ℝ) / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  have henergy := source_targetInteriorStoppedFullRankGap_sq_sum_integrable_and_integral_le
    (n := n) hlam0 hlam hn hB heta0 hetaSmall T
  refine ⟨henergy.1, henergy.2.trans ?_⟩
  have hinitial := integral_safeFeedback_initial_clippedObservable_le
    (n := n) hlam0.le (by linarith) hn hB.le hBn
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact div_le_div_of_nonneg_right (add_le_add_left hinitial _) (by positivity)

/-- Coefficient in the linear expectation bound for buffer `amplitude * sqrt n`. -/
noncomputable def feedbackBulkEnergyLinearConstant (lam amplitude : ℝ) : ℝ :=
  (6 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2) *
      ((8 + 5 * amplitude + 81 / lam) / (2 * lam)) +
    4 / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2

/-- At a square-root buffer and a horizon at most `n`, the actual bulk gap-energy expectation
is bounded by an explicit constant times `n`. -/
theorem feedbackBulkInteriorEnergy_integrable_and_integral_le_linear
    {lam eta amplitude : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hamp : 0 < amplitude)
    (hBn : amplitude * Real.sqrt n ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (T : ℝ≥0) (hT : (T : ℝ) ≤ n) :
    Integrable
        (feedbackBulkInteriorEnergy (n := n) hlam0.le (by linarith) eta
          (amplitude * Real.sqrt n) T) (finiteSampleLaw n) ∧
      (∫ sample : FiniteSample n,
        feedbackBulkInteriorEnergy (n := n) hlam0.le (by linarith) eta
          (amplitude * Real.sqrt n) T sample ∂(finiteSampleLaw n)) ≤
        feedbackBulkEnergyLinearConstant lam amplitude * n := by
  let B := amplitude * Real.sqrt n
  have hB : 0 < B := mul_pos hamp (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have henergy := feedbackBulkInteriorEnergy_integrable_and_integral_le
    hlam0 hlam hn hB hBn heta0 hetaSmall T
  refine ⟨henergy.1, henergy.2.trans ?_⟩
  have hBsqrt : B * Real.sqrt B ≤ amplitude * (n : ℝ) := by
    calc
      B * Real.sqrt B ≤ B * Real.sqrt n :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBn) hB.le
      _ = amplitude * (n : ℝ) := by
        dsimp [B]
        rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have hinitial : 2 * B + 5 * B * Real.sqrt B ≤ (2 + 5 * amplitude) * n := by
    nlinarith
  have htime : (6 + 81 / lam) * (T : ℝ) ≤ (6 + 81 / lam) * n :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  calc
    (6 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2) *
          ((2 * B + 5 * B * Real.sqrt B + (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) +
        4 * (n : ℝ) / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 ≤
        (6 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2) *
          (((2 + 5 * amplitude) * n + (6 + 81 / lam) * n) / (2 * lam)) +
        4 * (n : ℝ) / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (add_le_add hinitial htime) (by positivity)
    _ = feedbackBulkEnergyLinearConstant lam amplitude * n := by
      unfold feedbackBulkEnergyLinearConstant
      ring

/-- Every eventually bounded horizon gives an eventual `O(n)` expectation bound at the
square-root buffer.  The buffer geometry is supplied by the existing A2 asymptotic theorem. -/
theorem eventually_feedbackBulkInteriorEnergy_integrable_and_integral_le_linear
    {lam eta amplitude : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hamp : 0 < amplitude) (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (T : ℕ → ℝ≥0) (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ n) :
    ∀ᶠ n : ℕ in atTop,
      Integrable
          (feedbackBulkInteriorEnergy (n := n) hlam0.le (by linarith) eta
            (amplitude * Real.sqrt n) (T n)) (finiteSampleLaw n) ∧
        (∫ sample : FiniteSample n,
          feedbackBulkInteriorEnergy (n := n) hlam0.le (by linarith) eta
            (amplitude * Real.sqrt n) (T n) sample ∂(finiteSampleLaw n)) ≤
          feedbackBulkEnergyLinearConstant lam amplitude * n := by
  filter_upwards [eventually_feedbackA2Asymptotic_horizon_geometry hamp, hT]
    with n hn hnT
  apply feedbackBulkInteriorEnergy_integrable_and_integral_le_linear
    hlam0 hlam (by omega) hamp _ heta0 hetaSmall (T n) hnT
  simpa only [feedbackA2AsymptoticBuffer_eq] using hn.2.2.1

/-- If the actual A1 stop reaches the horizon on a sample without ties, the raw bulk energy
is exactly the bulk-retained energy of the actual stopped-continuation graph. -/
theorem feedbackBulkInteriorEnergy_eq_stoppedGraphBulk_of_survival
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) :
    feedbackBulkInteriorEnergy hlam0 hlamHalf eta B T sample =
      sample.graphBulkRetainedRankEnergy
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T)
        B (B + (T : ℝ)) := by
  rw [sample.stoppedContinuationFeedbackGraph_eq_horizon hlam0 hlamHalf eta B T hstop]
  exact sample.rawStoppedRankGapEnergy_eq_horizonBulkRetainedRankEnergy
    hlam0 hlamHalf eta B T hNoTie hstop

/-- On any measurable set of tie-free samples whose actual A1 stop reaches `T`, the stopped
graph's bulk-retained energy is integrable and inherits the explicit actual bulk bound. -/
theorem stoppedGraphBulk_indicator_integrable_and_integral_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (hBn : B ≤ n)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    (S : Set (FiniteSample n)) (hS : MeasurableSet S)
    (hSurvival : ∀ sample ∈ S, sample.NoFeedbackTies lam B 0 ∧
      safeFeedbackA1StopTime hlam0.le (by linarith) eta B B 0 T sample =
        (T : WithTop ℝ≥0)) :
    Integrable (S.indicator fun sample ↦
      sample.graphBulkRetainedRankEnergy
        (sample.stoppedContinuationFeedbackGraph hlam0.le (by linarith) eta B T)
        B (B + (T : ℝ))) (finiteSampleLaw n) ∧
      (∫ sample : FiniteSample n, S.indicator (fun sample' ↦
        sample'.graphBulkRetainedRankEnergy
          (sample'.stoppedContinuationFeedbackGraph hlam0.le (by linarith) eta B T)
          B (B + (T : ℝ))) sample ∂(finiteSampleLaw n)) ≤
        (6 / lowerOccupationCountRate ((1 : ℝ) / 2) ^ 2) *
          ((2 * B + 5 * B * Real.sqrt B + (6 + 81 / lam) * (T : ℝ)) / (2 * lam)) +
        4 * (n : ℝ) / lowerOccupationDecayRate ((1 : ℝ) / 2) ^ 2 := by
  let X := feedbackBulkInteriorEnergy (n := n) hlam0.le (by linarith) eta B T
  have heq : (S.indicator fun sample ↦
      sample.graphBulkRetainedRankEnergy
        (sample.stoppedContinuationFeedbackGraph hlam0.le (by linarith) eta B T)
        B (B + (T : ℝ))) = S.indicator X := by
    funext sample
    by_cases hs : sample ∈ S
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      exact (feedbackBulkInteriorEnergy_eq_stoppedGraphBulk_of_survival
        hlam0.le (by linarith) eta B T sample (hSurvival sample hs).1
        (hSurvival sample hs).2).symm
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
  have hraw := feedbackBulkInteriorEnergy_integrable_and_integral_le
    hlam0 hlam hn hB hBn heta0 hetaSmall T
  rw [heq]
  refine ⟨hraw.1.indicator hS, le_trans ?_ hraw.2⟩
  apply integral_mono (hraw.1.indicator hS) hraw.1
  intro sample
  by_cases hs : sample ∈ S
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs]
    dsimp only [X, feedbackBulkInteriorEnergy]
    positivity

end OTSelector.FiniteSample
