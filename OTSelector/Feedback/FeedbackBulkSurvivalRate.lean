import OTSelector.Feedback.FeedbackOccupation
import OTSelector.Feedback.FiniteEventBulkSurvival

/-!
# Feedback rates before the first bulk exit

This file identifies the actual bounded bulk rates with the unclipped feedback rates on the
strict survival interval.  The proof is pathwise: finite-event counts keep the remaining-label
numerators in `[0,n]`, while bulk geometry keeps both affine remaining masses away from zero.

The final statements rewrite the rates using the left current of the bulk-thinned counts.  They
are the rate-side input for the stopped marked-Dynkin argument; no stopped-intensity interface is
introduced.
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
  have hsucc : N t ω + 1 ≤ countBefore N t ω := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hle)
  rw [countBefore_succ_le_iff hmono] at hsucc
  rcases hsucc with ⟨s, hst, hs⟩
  exact (Nat.not_lt_of_ge (hmono hst.le)) hs

end CountingProcess

namespace FiniteSample

variable {n : ℕ}

/-! ## Pathwise remaining-count bounds -/

private theorem sourceCount_le_initialRemaining
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample.NoFeedbackTies lam x0 p0) :
    safeSourceCount hlam0 hlamHalf x0 p0 t sample ≤
      n - (sample.initialSeenSource x0 p0).card := by
  rw [safeSourceCount_eq_card_diff]
  simp only [hgood, ↓reduceIte]
  have hsubset :
      (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
          sample.initialSeenSource x0 p0 ⊆
        Finset.univ \ sample.initialSeenSource x0 p0 := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
  have hcard := Finset.card_le_card hsubset
  calc
    _ ≤ (Finset.univ \ sample.initialSeenSource x0 p0).card := hcard
    _ = n - (sample.initialSeenSource x0 p0).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp

private theorem targetCount_le_initialRemaining
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample.NoFeedbackTies lam x0 p0) :
    safeTargetCount hlam0 hlamHalf x0 p0 t sample ≤
      n - (sample.initialSeenTarget x0 p0).card := by
  rw [safeTargetCount_eq_card_diff]
  simp only [hgood, ↓reduceIte]
  have hsubset :
      (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
          sample.initialSeenTarget x0 p0 ⊆
        Finset.univ \ sample.initialSeenTarget x0 p0 := by
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, (Finset.mem_sdiff.mp hj).2⟩
  have hcard := Finset.card_le_card hsubset
  calc
    _ ≤ (Finset.univ \ sample.initialSeenTarget x0 p0).card := hcard
    _ = n - (sample.initialSeenTarget x0 p0).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp

/-- The predictable source remainder always lies in the deterministic interval `[0,n]`. -/
theorem safeSourceRemainingBefore_mem_Icc
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    safeSourceRemainingBefore hlam0 hlamHalf x0 p0 t sample ∈
      Set.Icc (0 : ℝ) (n : ℝ) := by
  classical
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · have hmono := (safeSourceCount_isSimpleCountingProcess
      (n := n) hlam0 hlamHalf x0 p0).monotone sample
    have hbefore : CountingProcess.countBefore
        (safeSourceCount hlam0 hlamHalf x0 p0) t sample ≤
        safeSourceCount hlam0 hlamHalf x0 p0 t sample :=
      CountingProcess.countBefore_le_at hmono
    have hcount := sourceCount_le_initialRemaining
      (n := n) hlam0 hlamHalf x0 p0 t sample hgood
    have hinitCard : (sample.initialSeenSource x0 p0).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (sample.initialSeenSource x0 p0))
    have hcountReal :
        (CountingProcess.countBefore (safeSourceCount hlam0 hlamHalf x0 p0) t sample : ℝ) ≤
          (n : ℝ) - ((sample.initialSeenSource x0 p0).card : ℝ) := by
      calc
        _ ≤ ((n - (sample.initialSeenSource x0 p0).card : ℕ) : ℝ) := by
          exact_mod_cast hbefore.trans hcount
        _ = (n : ℝ) - ((sample.initialSeenSource x0 p0).card : ℝ) := by
          rw [Nat.cast_sub hinitCard]
    have hcard0 : (0 : ℝ) ≤ (sample.initialSeenSource x0 p0).card := by positivity
    simp only [safeSourceRemainingBefore, safeInitialSourceRemainingReal, hgood,
      ↓reduceIte, initialSourceRemainingReal, Set.mem_Icc]
    constructor <;> linarith
  · have hmono := (safeSourceCount_isSimpleCountingProcess
      (n := n) hlam0 hlamHalf x0 p0).monotone sample
    have hcount0 : safeSourceCount hlam0 hlamHalf x0 p0 t sample = 0 := by
      simp [safeSourceCount_eq_card_diff, hgood]
    have hbefore0 : CountingProcess.countBefore
        (safeSourceCount hlam0 hlamHalf x0 p0) t sample = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hcount0] using
        (CountingProcess.countBefore_le_at (t := t) hmono)
    simp [safeSourceRemainingBefore, safeInitialSourceRemainingReal, hgood, hbefore0]

/-- The predictable target remainder always lies in the deterministic interval `[0,n]`. -/
theorem safeTargetRemainingBefore_mem_Icc
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    safeTargetRemainingBefore hlam0 hlamHalf x0 p0 t sample ∈
      Set.Icc (0 : ℝ) (n : ℝ) := by
  classical
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · have hmono := (safeTargetCount_isSimpleCountingProcess
      (n := n) hlam0 hlamHalf x0 p0).monotone sample
    have hbefore : CountingProcess.countBefore
        (safeTargetCount hlam0 hlamHalf x0 p0) t sample ≤
        safeTargetCount hlam0 hlamHalf x0 p0 t sample :=
      CountingProcess.countBefore_le_at hmono
    have hcount := targetCount_le_initialRemaining
      (n := n) hlam0 hlamHalf x0 p0 t sample hgood
    have hinitCard : (sample.initialSeenTarget x0 p0).card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ (sample.initialSeenTarget x0 p0))
    have hcountReal :
        (CountingProcess.countBefore (safeTargetCount hlam0 hlamHalf x0 p0) t sample : ℝ) ≤
          (n : ℝ) - ((sample.initialSeenTarget x0 p0).card : ℝ) := by
      calc
        _ ≤ ((n - (sample.initialSeenTarget x0 p0).card : ℕ) : ℝ) := by
          exact_mod_cast hbefore.trans hcount
        _ = (n : ℝ) - ((sample.initialSeenTarget x0 p0).card : ℝ) := by
          rw [Nat.cast_sub hinitCard]
    have hcard0 : (0 : ℝ) ≤ (sample.initialSeenTarget x0 p0).card := by positivity
    simp only [safeTargetRemainingBefore, safeInitialTargetRemainingReal, hgood,
      ↓reduceIte, initialTargetRemainingReal, Set.mem_Icc]
    constructor <;> linarith
  · have hmono := (safeTargetCount_isSimpleCountingProcess
      (n := n) hlam0 hlamHalf x0 p0).monotone sample
    have hcount0 : safeTargetCount hlam0 hlamHalf x0 p0 t sample = 0 := by
      simp [safeTargetCount_eq_card_diff, hgood]
    have hbefore0 : CountingProcess.countBefore
        (safeTargetCount hlam0 hlamHalf x0 p0) t sample = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [hcount0] using
        (CountingProcess.countBefore_le_at (t := t) hmono)
    simp [safeTargetRemainingBefore, safeInitialTargetRemainingReal, hgood, hbefore0]

/-! ## Inactive clipping on the actual bulk path -/

private theorem scaledRate_le_four_n_div_B
    {B N a d q : ℝ} (hB : 0 < B) (hd : 0 < d)
    (hdhalf : B / 2 ≤ d) (hN : 0 ≤ N) (_ha0 : 0 ≤ a) (haN : a ≤ N)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2) :
    a / d * q ≤ 4 * N / B := by
  have hhalf : 0 < B / 2 := by positivity
  have hinv : 1 / d ≤ 1 / (B / 2) := one_div_le_one_div_of_le hhalf hdhalf
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

/-- Inside the actual bulk region, the source cap and mask do not change the algebraic rate. -/
theorem safeSourceBulkRate_eq_safeSourceUnclippedRateAt_of_feedbackBulkRegion
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B x0 p0 : ℝ} (hB : 0 < B) (t : ℝ≥0) (sample : FiniteSample n)
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample =
      safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
  have hdenGe := sourceUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
  have hden : 0 < safeSourceUnclippedRemainingMassAt
      hlam0 hlamHalf x0 p0 t sample := by
    change 0 < sourceUnclippedRemainingMass n
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
      (elapsedFeedbackCoordinate x0 t)
    nlinarith [hdenGe, hB]
  have hnum := safeSourceRemainingBefore_mem_Icc
    (n := n) hlam0 hlamHalf x0 p0 t sample
  have hslope := abs_feedbackSlope_le
    (lam := lam) (k := (safePreCurrentAt hlam0 hlamHalf x0 p0 t sample : ℝ)) hlam0
  have hfac0 : 0 ≤ 1 - safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample / 2 := by
    simp only [safePreFeedbackSlope]
    nlinarith [abs_le.mp hslope]
  have hfac2 : 1 - safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample / 2 ≤ 2 := by
    simp only [safePreFeedbackSlope]
    nlinarith [abs_le.mp hslope]
  have hunclip0 : 0 ≤ safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
    simp only [safeSourceUnclippedRateAt, sourceTotalRate,
      safeSourceUnclippedResidualDensityAt]
    exact mul_nonneg (div_nonneg hnum.1 hden.le) hfac0
  have hunclipCap : safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample ≤
      feedbackBulkRateCap n B := by
    rw [feedbackBulkRateCap_eq_div hB]
    simp only [safeSourceUnclippedRateAt, sourceTotalRate,
      safeSourceUnclippedResidualDensityAt]
    have hdenHalf : B / 2 ≤ safeSourceUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 t sample := by
      change B / 2 ≤ sourceUnclippedRemainingMass n
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t)
      nlinarith [hdenGe, hB]
    exact scaledRate_le_four_n_div_B hB hden hdenHalf
      (Nat.cast_nonneg n) hnum.1 hnum.2 hfac0 hfac2
  have hclip := clipToStrip_eq_of_mem hunclip0 hunclipCap
  simp [safeSourceBulkRate, safeFeedbackBulkMask, hbulk, hclip]

/-- Inside the actual bulk region, the target cap and mask do not change the algebraic rate. -/
theorem safeTargetBulkRate_eq_safeTargetUnclippedRateAt_of_feedbackBulkRegion
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B x0 p0 : ℝ} (hB : 0 < B) (t : ℝ≥0) (sample : FiniteSample n)
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample =
      safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
  have hdenGe := targetUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
  have hden : 0 < safeTargetUnclippedRemainingMassAt
      hlam0 hlamHalf x0 p0 t sample := by
    change 0 < targetUnclippedRemainingMass n
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
      (elapsedFeedbackCoordinate x0 t)
    nlinarith [hdenGe, hB]
  have hnum := safeTargetRemainingBefore_mem_Icc
    (n := n) hlam0 hlamHalf x0 p0 t sample
  have hslope := abs_feedbackSlope_le
    (lam := lam) (k := (safePreCurrentAt hlam0 hlamHalf x0 p0 t sample : ℝ)) hlam0
  have hfac0 : 0 ≤ 1 + 3 * safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample / 2 := by
    simp only [safePreFeedbackSlope]
    nlinarith [abs_le.mp hslope, hlamHalf]
  have hfac2 : 1 + 3 * safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample / 2 ≤ 2 := by
    simp only [safePreFeedbackSlope]
    nlinarith [abs_le.mp hslope, hlamHalf]
  have hunclip0 : 0 ≤ safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
    simp only [safeTargetUnclippedRateAt, targetTotalRate,
      safeTargetUnclippedResidualDensityAt]
    exact mul_nonneg (div_nonneg hnum.1 hden.le) hfac0
  have hunclipCap : safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample ≤
      feedbackBulkRateCap n B := by
    rw [feedbackBulkRateCap_eq_div hB]
    simp only [safeTargetUnclippedRateAt, targetTotalRate,
      safeTargetUnclippedResidualDensityAt]
    have hdenHalf : B / 2 ≤ safeTargetUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 t sample := by
      change B / 2 ≤ targetUnclippedRemainingMass n
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t)
      nlinarith [hdenGe, hB]
    exact scaledRate_le_four_n_div_B hB hden hdenHalf
      (Nat.cast_nonneg n) hnum.1 hnum.2 hfac0 hfac2
  have hclip := clipToStrip_eq_of_mem hunclip0 hunclipCap
  simp [safeTargetBulkRate, safeFeedbackBulkMask, hbulk, hclip]

/-! ## Strict survival and left-current intensity formulas -/

theorem safeSourceBulkRate_eq_safeSourceUnclippedRateAt_of_lt_exit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B x0 p0 : ℝ} (hB : 0 < B) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample =
      safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
  exact safeSourceBulkRate_eq_safeSourceUnclippedRateAt_of_feedbackBulkRegion
    hlam0 hlamHalf hB t sample
      (feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime
        (n := n) hlam0 hlamHalf B x0 p0 t sample ht)

theorem safeTargetBulkRate_eq_safeTargetUnclippedRateAt_of_lt_exit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B x0 p0 : ℝ} (hB : 0 < B) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample =
      safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
  exact safeTargetBulkRate_eq_safeTargetUnclippedRateAt_of_feedbackBulkRegion
    hlam0 hlamHalf hB t sample
      (feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime
        (n := n) hlam0 hlamHalf B x0 p0 t sample ht)

/-- Before the first bulk exit, the source rate is evaluated at the bulk-count left current. -/
theorem safeSourceBulkRate_eq_feedbackSourceIntensity_of_lt_exit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B x0 p0 : ℝ} (hB : 0 < B) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample =
      feedbackSourceIntensity lam
        (safeSourceUnclippedResidualDensityAt hlam0 hlamHalf x0 p0)
        (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample := by
  rw [safeSourceBulkRate_eq_safeSourceUnclippedRateAt_of_lt_exit
    (n := n) hlam0 hlamHalf hB t sample ht]
  simp only [safeSourceUnclippedRateAt, safePreFeedbackSlope, feedbackSourceIntensity]
  rw [leftCurrentOfSafeBulkCounts_eq_safePreCurrentAt_of_lt_safeFeedbackBulkExitTime
    (n := n) hlam0 hlamHalf B x0 p0 t sample ht]

/-- Before the first bulk exit, the target rate is evaluated at the bulk-count left current. -/
theorem safeTargetBulkRate_eq_feedbackTargetIntensity_of_lt_exit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B x0 p0 : ℝ} (hB : 0 < B) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample =
      feedbackTargetIntensity lam
        (safeTargetUnclippedResidualDensityAt hlam0 hlamHalf x0 p0)
        (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample := by
  rw [safeTargetBulkRate_eq_safeTargetUnclippedRateAt_of_lt_exit
    (n := n) hlam0 hlamHalf hB t sample ht]
  simp only [safeTargetUnclippedRateAt, safePreFeedbackSlope, feedbackTargetIntensity]
  rw [leftCurrentOfSafeBulkCounts_eq_safePreCurrentAt_of_lt_safeFeedbackBulkExitTime
    (n := n) hlam0 hlamHalf B x0 p0 t sample ht]

end FiniteSample

end OTSelector
