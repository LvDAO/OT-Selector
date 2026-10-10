import OTSelector.Feedback.FeedbackA1Stopping

/-!
# Pointwise A1 drift before the combined stop

The finite feedback current is uniformly inside the deterministic cutoff `2 * n + 1`.
Strict survival of the A1 coordinate supplies both bulk membership and predictable residual
regularity.  The actual bulk rates can therefore be rewritten as the feedback intensities and
inserted into the existing cubic generator inequality.
-/

open MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace CountingProcess

private theorem countBefore_le_at
    {Ω : Type*} [MeasurableSpace Ω] {N : ℝ≥0 → Ω → ℕ}
    {t : ℝ≥0} {ω : Ω} (hmono : Monotone fun s ↦ N s ω) :
    countBefore N t ω ≤ N t ω := by
  by_contra hle
  have hsucc : N t ω + 1 ≤ countBefore N t ω :=
    Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hle)
  rw [countBefore_succ_le_iff hmono] at hsucc
  rcases hsucc with ⟨s, hst, hs⟩
  exact (Nat.not_lt_of_ge (hmono hst.le)) hs

end CountingProcess

namespace FiniteSample

variable {n : ℕ}

/-- A deterministic cutoff strictly outside every possible finite feedback current. -/
def feedbackA1CurrentCutoff (n : ℕ) : ℕ :=
  2 * n + 1

private theorem safeK0_mem_Icc
    (lam x0 p0 : ℝ) (sample : FiniteSample n) :
    -(n : ℤ) ≤ safeK0 lam x0 p0 sample ∧
      safeK0 lam x0 p0 sample ≤ (n : ℤ) := by
  classical
  have hsource : (sample.initialSeenSource x0 p0).card ≤ n := by
    simpa using Finset.card_le_card
      (Finset.subset_univ (sample.initialSeenSource x0 p0))
  have htarget : (sample.initialSeenTarget x0 p0).card ≤ n := by
    simpa using Finset.card_le_card
      (Finset.subset_univ (sample.initialSeenTarget x0 p0))
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · simp only [safeK0, hgood, ite_true, initialFeedbackCurrent]
    constructor <;> omega
  · simp [safeK0, hgood]

private theorem safeSourceBulkCount_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    safeSourceBulkCount hlam0 hlamHalf B x0 p0 t sample ≤ n := by
  simpa only [safeSourceBulkCount] using
    CountingProcess.finiteEventCountThinned_le
      (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample

private theorem safeTargetBulkCount_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    safeTargetBulkCount hlam0 hlamHalf B x0 p0 t sample ≤ n := by
  simpa only [safeTargetBulkCount] using
    CountingProcess.finiteEventCountThinned_le
      (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample

/-- The left current of the bulk counts lies strictly inside `[-(2n+1),2n+1]`. -/
theorem leftCurrentOfSafeBulkCounts_strictInterior
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    -(feedbackA1CurrentCutoff n : ℤ) <
        CountingProcess.leftCurrentOfCounts
          (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
          (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample ∧
      CountingProcess.leftCurrentOfCounts
          (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
          (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample <
        (feedbackA1CurrentCutoff n : ℤ) := by
  have hsourceMono := (safeSourceBulkCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf B x0 p0).monotone sample
  have htargetMono := (safeTargetBulkCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf B x0 p0).monotone sample
  have hsourceBefore : CountingProcess.countBefore
      (safeSourceBulkCount hlam0 hlamHalf B x0 p0) t sample ≤ n :=
    (CountingProcess.countBefore_le_at hsourceMono).trans
      (safeSourceBulkCount_le hlam0 hlamHalf B x0 p0 t sample)
  have htargetBefore : CountingProcess.countBefore
      (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample ≤ n :=
    (CountingProcess.countBefore_le_at htargetMono).trans
      (safeTargetBulkCount_le hlam0 hlamHalf B x0 p0 t sample)
  have hK0 := safeK0_mem_Icc (n := n) lam x0 p0 sample
  simp only [CountingProcess.leftCurrentOfCounts, feedbackA1CurrentCutoff]
  constructor <;> omega

/-- Strict A1 survival supplies regularity for the actual predictable residual densities. -/
theorem crossingRegularity_of_lt_safeFeedbackA1Stop
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {eta B x0 p0 : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T t : ℝ≥0)
    (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T sample) :
    CrossingRegularity lam eta
      (safeSourceUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 t sample)
      (safeTargetUnclippedResidualDensityAt hlam0 hlamHalf x0 p0 t sample) := by
  have hbulkExit := lt_safeFeedbackBulkExitTime_of_lt_A1Stop
    (n := n) hlam0 hlamHalf eta B x0 p0 T t sample ht
  have hregExit := lt_safeFeedbackRegularityExitTime_of_lt_A1Stop
    (n := n) hlam0 hlamHalf eta B x0 p0 T t sample ht
  exact crossingRegularity_of_lt_safeFeedbackRegularityExitTime
    (n := n) hlam0 hlamHalf hB heta0 hetaSmall t sample
      (feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime
        (n := n) hlam0 hlamHalf B x0 p0 t sample hbulkExit)
      hregExit

/-- Before the A1 stop, the actual bulk generator has the cubic inward-drift bound. -/
theorem safeFeedbackBulk_clippedGeneratorRate_cubic_le_of_lt_A1Stop
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T t : ℝ≥0)
    (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T sample) :
    clippedGeneratorRate (feedbackA1CurrentCutoff n) cubicLyapunov
        (safeSourceBulkRate hlam0.le (by linarith) B x0 p0 t sample)
        (safeTargetBulkRate hlam0.le (by linarith) B x0 p0 t sample)
        (CountingProcess.leftCurrentOfCounts
          (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0.le (by linarith) B x0 p0)
          (safeTargetBulkCount hlam0.le (by linarith) B x0 p0) t sample) ≤
      -(2 * lam) *
          (CountingProcess.leftCurrentOfCounts
            (safeK0 lam x0 p0)
            (safeSourceBulkCount hlam0.le (by linarith) B x0 p0)
            (safeTargetBulkCount hlam0.le (by linarith) B x0 p0)
            t sample : ℝ) ^ 2 +
        (6 + 81 / lam) := by
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
  exact feedback_clipped_rate_cubic_le hlam0 hlam hreg
    (feedbackA1CurrentCutoff n) k hinterior.1 hinterior.2

end FiniteSample

end OTSelector
