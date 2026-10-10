import OTSelector.Feedback.FeedbackA2Asymptotic

/-!
# A vanishing tolerance for actual feedback regularity

For the physical buffer `B = amplitude * sqrt n`, the logarithmic ratio
`q = log n / (13 B / 16)` tends to zero. The explicit tolerance
`2 * 33280 * (sqrt q + q)` satisfies both finite-sample VC inequalities and eventually fits
the feedback drift condition for every fixed positive parameter.
-/

open Filter
open scoped Topology

namespace OTSelector

/-- Logarithmic regularity error relative to the actual bulk denominator floor. -/
noncomputable def feedbackVanishingRegularityRatio (amplitude : ℝ) (n : ℕ) : ℝ :=
  Real.log n / (13 * feedbackA2AsymptoticBuffer amplitude n / 16)

/-- Explicit regularity tolerance on the square-root buffer scale. -/
noncomputable def feedbackVanishingRegularityEta (amplitude : ℝ) (n : ℕ) : ℝ :=
  2 * 33280 * (Real.sqrt (feedbackVanishingRegularityRatio amplitude n) +
    feedbackVanishingRegularityRatio amplitude n)

theorem feedbackVanishingRegularityRatio_nonneg {amplitude : ℝ} (hamp : 0 ≤ amplitude)
    (n : ℕ) : 0 ≤ feedbackVanishingRegularityRatio amplitude n := by
  unfold feedbackVanishingRegularityRatio
  rw [feedbackA2AsymptoticBuffer_eq]
  exact div_nonneg (Real.log_natCast_nonneg n) (by positivity)

theorem feedbackVanishingRegularityEta_nonneg {amplitude : ℝ} (hamp : 0 ≤ amplitude)
    (n : ℕ) : 0 ≤ feedbackVanishingRegularityEta amplitude n := by
  unfold feedbackVanishingRegularityEta
  have hq := feedbackVanishingRegularityRatio_nonneg hamp n
  positivity

/-- The needed logarithmic ratio limit is the standard `log = o(sqrt)` specialization. -/
theorem tendsto_feedbackVanishingRegularityRatio (amplitude : ℝ) :
    Tendsto (feedbackVanishingRegularityRatio amplitude) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
    have h := ((isLittleO_log_rpow_atTop (r := (1 / (2 : ℝ))) (by norm_num)).comp_tendsto
      tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
    simpa only [← Real.sqrt_eq_rpow, Function.comp_def] using h
  have h := hlog.div_const (13 * amplitude / 16)
  simp only [zero_div] at h
  convert h using 1
  ext n
  unfold feedbackVanishingRegularityRatio
  rw [feedbackA2AsymptoticBuffer_eq, div_div]
  congr 1
  ring

theorem tendsto_feedbackVanishingRegularityEta (amplitude : ℝ) :
    Tendsto (feedbackVanishingRegularityEta amplitude) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ ↦ 2 * (33280 : ℝ) *
    (Real.sqrt (feedbackVanishingRegularityRatio amplitude n) +
      feedbackVanishingRegularityRatio amplitude n)) atTop (𝓝 0)
  have hq := tendsto_feedbackVanishingRegularityRatio amplitude
  have h := ((Real.continuous_sqrt.tendsto 0).comp hq).add hq
  simpa only [Real.sqrt_zero, zero_add, mul_zero, feedbackVanishingRegularityEta,
    Function.comp_def] using
    h.const_mul (2 * (33280 : ℝ))

/-- The explicit tolerance satisfies both denominator-sensitive VC inequalities in every
positive row; asymptotics are needed only for making this tolerance small. -/
theorem feedbackVanishingRegularity_inequalities {amplitude : ℝ} (hamp : 0 < amplitude)
    {n : ℕ} (hn : 0 < n) :
    4 * (33280 : ℝ) ^ 2 * Real.log n ≤
        feedbackVanishingRegularityEta amplitude n ^ 2 *
          (13 * feedbackA2AsymptoticBuffer amplitude n / 16) ∧
      2 * (33280 : ℝ) * Real.log n ≤
        feedbackVanishingRegularityEta amplitude n *
          (13 * feedbackA2AsymptoticBuffer amplitude n / 16) := by
  let d := 13 * feedbackA2AsymptoticBuffer amplitude n / 16
  let q := feedbackVanishingRegularityRatio amplitude n
  let eta := feedbackVanishingRegularityEta amplitude n
  have hd : 0 < d := by
    dsimp [d]
    rw [feedbackA2AsymptoticBuffer_eq]
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
    positivity
  have hq : 0 ≤ q := feedbackVanishingRegularityRatio_nonneg hamp.le n
  have heta : 0 ≤ eta := feedbackVanishingRegularityEta_nonneg hamp.le n
  have hqd : q * d = Real.log n := div_mul_cancel₀ _ hd.ne'
  have hs : 2 * (33280 : ℝ) * Real.sqrt q ≤ eta := by
    dsimp [eta, feedbackVanishingRegularityEta, q]
    nlinarith [feedbackVanishingRegularityRatio_nonneg hamp.le n]
  have hl : 2 * (33280 : ℝ) * q ≤ eta := by
    dsimp [eta, feedbackVanishingRegularityEta, q]
    nlinarith [Real.sqrt_nonneg (feedbackVanishingRegularityRatio amplitude n)]
  have hsquare : 4 * (33280 : ℝ) ^ 2 * q ≤ eta ^ 2 := by
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  constructor
  · change 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * d
    calc
      _ = (4 * (33280 : ℝ) ^ 2 * q) * d := by rw [← hqd]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsquare hd.le
  · change 2 * (33280 : ℝ) * Real.log n ≤ eta * d
    calc
      _ = (2 * (33280 : ℝ) * q) * d := by rw [← hqd]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hl hd.le

/-- All numerical inputs for actual bulk regularity and drift hold eventually with a single
explicit tolerance that tends to zero. -/
theorem eventually_feedbackVanishingRegularity_parameters {lam amplitude : ℝ}
    (hlam0 : 0 < lam) (hamp : 0 < amplitude) :
    ∀ᶠ n : ℕ in atTop,
      4 ≤ n ∧ 0 < feedbackA2AsymptoticBuffer amplitude n ∧
      0 ≤ feedbackVanishingRegularityEta amplitude n ∧
      feedbackVanishingRegularityEta amplitude n * (2 + lam) ≤ lam ∧
      4 * (33280 : ℝ) ^ 2 * Real.log n ≤
        feedbackVanishingRegularityEta amplitude n ^ 2 *
          (13 * feedbackA2AsymptoticBuffer amplitude n / 16) ∧
      2 * (33280 : ℝ) * Real.log n ≤
        feedbackVanishingRegularityEta amplitude n *
          (13 * feedbackA2AsymptoticBuffer amplitude n / 16) := by
  have hsmall : ∀ᶠ n : ℕ in atTop,
      feedbackVanishingRegularityEta amplitude n * (2 + lam) < lam :=
    ((tendsto_feedbackVanishingRegularityEta amplitude).mul_const (2 + lam)).eventually
      (gt_mem_nhds (by simpa using hlam0))
  filter_upwards [eventually_ge_atTop 4, hsmall] with n hn hs
  have hn0 : 0 < n := by omega
  refine ⟨hn, ?_, feedbackVanishingRegularityEta_nonneg hamp.le n, hs.le,
    feedbackVanishingRegularity_inequalities hamp hn0⟩
  rw [feedbackA2AsymptoticBuffer_eq]
  exact mul_pos hamp (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn0))

end OTSelector
