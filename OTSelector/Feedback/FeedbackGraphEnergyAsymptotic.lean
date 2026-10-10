import OTSelector.Feedback.FeedbackGraphEnergyProbability

/-! # Numerical geometry of the interval-count energy estimate -/

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace OTSelector.FiniteSample

/-- The inward rounding of the interval grid costs `2c = 1/4`. -/
noncomputable def feedbackRightDensityError (n : ℕ) : ℝ := 60 * Real.log n + 1 / 4

theorem eventually_feedbackRightDensityError_le_sqrt_buffer
    {amplitude : ℝ} (hamp : 0 < amplitude) :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ feedbackRightDensityError n ∧
      feedbackRightDensityError n ≤ Real.sqrt (amplitude * Real.sqrt n) := by
  have hsa : 0 < Real.sqrt amplitude := Real.sqrt_pos.mpr hamp
  have hLittle : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / (4 : ℝ))) :=
    (isLittleO_log_rpow_atTop (r := (1 / (4 : ℝ))) (by norm_num)).comp_tendsto
      tendsto_natCast_atTop_atTop
  have hbuffer : Tendsto (fun n : ℕ ↦ amplitude * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hamp
  filter_upwards [hLittle.bound (show 0 < Real.sqrt amplitude / 120 by positivity),
    hbuffer.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1] with n hlog hB hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at hlog
  have hroot : Real.sqrt (amplitude * Real.sqrt n) =
      Real.sqrt amplitude * (n : ℝ) ^ (1 / (4 : ℝ)) := by
    rw [Real.sqrt_mul hamp.le]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hroot1 : 1 ≤ Real.sqrt (amplitude * Real.sqrt n) := by
    simpa using Real.sqrt_le_sqrt hB
  constructor
  · unfold feedbackRightDensityError
    positivity
  · unfold feedbackRightDensityError
    nlinarith

/-- The terminal density window fits inside the square-root buffer for any fixed current
and height constants. This discharges the geometry in the actual linear energy estimate. -/
theorem eventually_feedbackRight_energy_geometry
    {amplitude L a : ℝ} (hamp : 0 < amplitude) (hL : 0 ≤ L) (ha : 0 ≤ a) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ amplitude * Real.sqrt n ∧
      L * Real.sqrt (amplitude * Real.sqrt n) ≤ (amplitude * Real.sqrt n) / 8 ∧
      8 * (L * Real.sqrt (amplitude * Real.sqrt n)) + 1 +
        8 * (a * Real.sqrt (amplitude * Real.sqrt n) + feedbackRightDensityError n) ≤
        amplitude * Real.sqrt n := by
  have hbuffer : Tendsto (fun n : ℕ ↦ amplitude * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hamp
  have hroot := Real.tendsto_sqrt_atTop.comp hbuffer
  filter_upwards [hbuffer.eventually (eventually_ge_atTop 1),
    hroot.eventually (eventually_ge_atTop (8 * L + 8 * a + 10)),
    eventually_feedbackRightDensityError_le_sqrt_buffer hamp] with n hB hr he
  have hB0 : 0 ≤ amplitude * Real.sqrt (n : ℝ) := by positivity
  have hs := Real.sq_sqrt hB0
  have hs0 := Real.sqrt_nonneg (amplitude * Real.sqrt (n : ℝ))
  dsimp only [Function.comp_apply] at hr
  have hm := mul_le_mul_of_nonneg_right hr hs0
  refine ⟨hB, ?_, ?_⟩
  · nlinarith [mul_nonneg ha hs0]
  · nlinarith

/-- The actual A2 horizon eventually contains every fixed physical window. -/
theorem eventually_feedback_horizon_gt {amplitude : ℝ} (hamp : 0 < amplitude) (W : ℝ) :
    ∀ᶠ n : ℕ in atTop, W < (feedbackA2AsymptoticHorizon amplitude n : ℝ) := by
  filter_upwards [eventually_feedbackA2Asymptotic_horizon_geometry hamp,
    eventually_feedback_buffer_quarter amplitude,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop (2 * W))]
    with n hg hquarter hn
  rw [← feedbackA2AsymptoticBuffer_eq] at hquarter
  linarith [hg.2.2.2.1]

/-- The remaining left-stop and interval-grid probability losses vanish with the row size. -/
theorem tendsto_feedback_energy_remainder {amplitude : ℝ} (hamp : 0 < amplitude) :
    Tendsto (fun n : ℕ ↦ 4 * Real.exp (-(amplitude * Real.sqrt n) / 8) +
      16 / (n : ℝ) ^ 3) atTop (𝓝 0) := by
  have hbuffer : Tendsto (fun n : ℕ ↦ amplitude * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hamp
  have he : Tendsto (fun n : ℕ ↦ -(amplitude * Real.sqrt n) / 8) atTop atBot := by
    simpa only [neg_div, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using
      hbuffer.const_mul_atTop_of_neg (show -(8 : ℝ)⁻¹ < 0 by norm_num)
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hdiv : Tendsto (fun n : ℕ ↦ 16 / (n : ℝ) ^ 3) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := (16 : ℝ))).mul (tendsto_inv_atTop_zero.comp hpow)
  have hexp : Tendsto (fun n : ℕ ↦ 4 * Real.exp (-(amplitude * Real.sqrt n) / 8))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (tendsto_const_nhds (x := (4 : ℝ))).mul (Real.tendsto_exp_atBot.comp he)
  simpa only [zero_add] using hexp.add hdiv

/-- A single fixed bulk window can make the crossing-prefix failure arbitrarily small and
simultaneously dominate any prescribed boundary current. -/
theorem exists_bulk_window_small_failure (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ≥0, 0 < r ∧
      L ≤ CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2) * r ∧
      2 * Real.exp (-CountingProcess.lowerOccupationDecayRate ((1 : ℝ) / 2) * (r : ℝ)) < ε := by
  have hc := (CountingProcess.lowerOccupation_rates_pos (by norm_num : (0 : ℝ) < 1 / 2)).1
  have hd := (CountingProcess.lowerOccupation_rates_pos (by norm_num : (0 : ℝ) < 1 / 2)).2
  have hlin : Tendsto (fun r : ℝ ↦ CountingProcess.lowerOccupationCountRate ((1 : ℝ) / 2) * r)
      atTop atTop := tendsto_id.const_mul_atTop hc
  have hexp : Tendsto (fun r : ℝ ↦ 2 * Real.exp
      (-CountingProcess.lowerOccupationDecayRate ((1 : ℝ) / 2) * r)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hd)))
  obtain ⟨r, hr0, hrL, hrε⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((hlin.eventually (eventually_ge_atTop L)).and
      (hexp.eventually (eventually_lt_nhds hε)))).exists
  exact ⟨⟨r, hr0.le⟩, hr0, hrL, hrε⟩

end OTSelector.FiniteSample
