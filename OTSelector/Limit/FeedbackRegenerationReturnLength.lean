import OTSelector.Limit.FeedbackRegenerationReturnCount
import OTSelector.Limit.FeedbackRegenerationNonexplosion

/-!
# Continuous length of the actual feedback excursion

The total return duration includes the initial zero hold. The nonzero excursion length excludes
that first hold. Both observables use the least positive zero index on the actual joint trajectory.
Positive exponential moments of deterministic clocks, combined with the proved return-count tail,
control the continuous excursion length without assuming stopping-time independence.
-/

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal BigOperators

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

private theorem lintegral_waitLaplace_of_rate_add_pos {r theta : ℝ} (hr : 0 < r)
    (hr' : 0 < r + theta) :
    ∫⁻ t, waitLaplace theta t ∂expMeasure r = ENNReal.ofReal (r / (r + theta)) := by
  have hpdf (t : ℝ) : exponentialPDF r t * waitLaplace theta t =
      ENNReal.ofReal (r / (r + theta)) * exponentialPDF (r + theta) t := by
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht, exponentialPDF_of_nonneg ht, waitLaplace,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        r * Real.exp (-(r * t)) * Real.exp (-(theta * t)) =
            r * Real.exp (-((r + theta) * t)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ = r / (r + theta) * ((r + theta) * Real.exp (-((r + theta) * t))) := by
          field_simp
    · simp [exponentialPDF_of_neg (lt_of_not_ge ht)]
  change ∫⁻ t, waitLaplace theta t ∂volume.withDensity (exponentialPDF r) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (by unfold exponentialPDF; fun_prop)
      (measurable_waitLaplace theta)]
  simp only [Pi.mul_apply, hpdf]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one hr', mul_one]

/-- The actual waiting law has a uniformly bounded positive exponential moment at one half. -/
theorem feedbackHoldingJumpKernel_exp_half_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∫⁻ z, waitLaplace (-(1 / 2)) z.1 ∂feedbackHoldingJumpKernel lam k ≤ 2 := by
  have hq := (totalJumpRate_bounds hlam₀ k).1
  rw [← lintegral_map (measurable_waitLaplace _) measurable_fst,
    feedbackHoldingJumpKernel_map_wait hlam₀ hlam,
    lintegral_waitLaplace_of_rate_add_pos (totalJumpRate_pos hlam₀ hlam k) (by linarith)]
  rw [← ENNReal.ofReal_ofNat]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (by linarith)).mpr
  linarith

private theorem waitLaplace_add' (theta s t : ℝ) :
    waitLaplace theta (s + t) = waitLaplace theta s * waitLaplace theta t := by
  unfold waitLaplace
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- One positive exponential-moment step, using the actual conditional transition law. -/
theorem feedbackJumpTime_exp_half_succ_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    ∫⁻ w, waitLaplace (-(1 / 2)) (feedbackJumpTime (n + 1) w)
      ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k ≤
      2 * ∫⁻ w, waitLaplace (-(1 / 2)) (feedbackJumpTime n w)
        ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam k
  let f : ((i : Finset.Iic n) → ℝ × ℤ) × (ℝ × ℤ) → ℝ≥0∞ :=
    fun p ↦ waitLaplace (-(1 / 2)) (feedbackHistoryTime n p.1) * waitLaplace (-(1 / 2)) p.2.1
  have hf : Measurable f := by dsimp [f]; fun_prop
  change ∫⁻ w, waitLaplace (-(1 / 2)) (feedbackJumpTime (n + 1) w) ∂μ ≤ _
  calc
    _ = ∫⁻ p, f p ∂μ.map (fun w ↦ (frestrictLe n w, w (n + 1))) := by
      rw [lintegral_map hf (by fun_prop)]
      apply lintegral_congr
      intro w
      simp [f, feedbackJumpTime_succ, waitLaplace_add']
    _ = ∫⁻ x, waitLaplace (-(1 / 2)) (feedbackHistoryTime n x) *
        (∫⁻ z, waitLaplace (-(1 / 2)) z.1 ∂condDistrib
          (fun w : ℕ → ℝ × ℤ ↦ w (n + 1)) (frestrictLe n) μ x)
        ∂μ.map (frestrictLe n) := by
      rw [← compProd_map_condDistrib (μ := μ) (X := frestrictLe n)
        (Y := fun w : ℕ → ℝ × ℤ ↦ w (n + 1))
        (measurable_pi_apply (n + 1)).aemeasurable, Measure.lintegral_compProd hf]
      apply lintegral_congr
      intro x
      change (∫⁻ z : ℝ × ℤ, waitLaplace (-(1 / 2)) (feedbackHistoryTime n x) *
        waitLaplace (-(1 / 2)) z.1 ∂_) = _
      exact lintegral_const_mul _ (by fun_prop)
    _ ≤ ∫⁻ x, waitLaplace (-(1 / 2)) (feedbackHistoryTime n x) * 2
        ∂μ.map (frestrictLe n) := by
      apply lintegral_mono_ae
      filter_upwards [feedbackHoldingJumpTrajectory_condDistrib hlam₀ hlam k n] with x hx
      apply mul_le_mul_right
      rw [hx]
      exact feedbackHoldingJumpKernel_exp_half_le hlam₀ hlam _
    _ = _ := by
      rw [lintegral_mul_const _ (by fun_prop), lintegral_map (by fun_prop) (by fun_prop)]
      simp only [feedbackHistoryTime_restrict, mul_comm]
      rfl

/-- Positive exponential moments of n actual waiting times grow by at most a factor two per step. -/
theorem feedbackJumpTime_exp_half_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) :
    ∫⁻ w, waitLaplace (-(1 / 2)) (feedbackJumpTime n w)
      ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k ≤ 2 ^ n := by
  induction n with
  | zero => simp [waitLaplace]
  | succ n ih =>
      exact (feedbackJumpTime_exp_half_succ_le hlam₀ hlam k n).trans
        ((mul_le_mul_right ih _).trans_eq (pow_succ' _ _).symm)

/-- Upper tail for the actual clock, requiring no independence of the successive waits. -/
theorem feedbackJumpTime_upperTail {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) (n : ℕ) (T : ℝ) :
    feedbackHoldingJumpTrajectory lam hlam₀ hlam k {w | T ≤ feedbackJumpTime n w} ≤
      ENNReal.ofReal (Real.exp (-(T / 2))) * 2 ^ n := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam k
  have hm : Measurable (fun w ↦ waitLaplace (-(1 / 2)) (feedbackJumpTime n w)) := by fun_prop
  have he : waitLaplace (-(1 / 2)) T ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have he' : waitLaplace (-(1 / 2)) T ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    _ ≤ μ {w | waitLaplace (-(1 / 2)) T ≤
        waitLaplace (-(1 / 2)) (feedbackJumpTime n w)} := by
      apply measure_mono
      intro w hw
      change T ≤ feedbackJumpTime n w at hw
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ (∫⁻ w, waitLaplace (-(1 / 2)) (feedbackJumpTime n w) ∂μ) /
        waitLaplace (-(1 / 2)) T := meas_ge_le_lintegral_div hm.aemeasurable he he'
    _ ≤ 2 ^ n / waitLaplace (-(1 / 2)) T := by
      apply ENNReal.div_le_div_right
      exact feedbackJumpTime_exp_half_le hlam₀ hlam k n
    _ = _ := by
      rw [ENNReal.div_eq_inv_mul, waitLaplace,
        ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
      congr 3
      ring

/-- Every actual positive-index wait is strictly positive almost surely. -/
theorem feedbackHoldingJumpTrajectory_waits_positive {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∀ᵐ w ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam k,
      ∀ n : ℕ, 0 < (w (n + 1)).1 := by
  apply ae_all_iff.mpr
  intro n
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam k
  have hprod : ∀ᵐ p ∂μ.map (frestrictLe n) ⊗ₘ condDistrib
      (fun w : ℕ → ℝ × ℤ ↦ w (n + 1)) (frestrictLe n) μ, 0 < p.2.1 := by
    apply Measure.ae_compProd_of_ae_ae (by measurability)
    filter_upwards [feedbackHoldingJumpTrajectory_condDistrib hlam₀ hlam k n] with x hx
    rw [hx]
    change ∀ᵐ z ∂feedbackHoldingJumpKernel lam (x ⟨n, by simp⟩).2, 0 < z.1
    let := feedbackHoldingJumpKernel_isMarkov hlam₀ hlam
    apply (mem_ae_iff_prob_eq_one (by measurability)).mpr
    rw [show {z : ℝ × ℤ | 0 < z.1} = Set.Ioi 0 ×ˢ Set.univ by ext z; simp]
    exact feedbackHoldingJumpKernel_positive_wait hlam₀ hlam (x ⟨n, by simp⟩).2
  rw [compProd_map_condDistrib (μ := μ) (X := frestrictLe n)
    (Y := fun w : ℕ → ℝ × ℤ ↦ w (n + 1))
    (measurable_pi_apply (n + 1)).aemeasurable] at hprod
  have hm : Measurable (fun w : ℕ → ℝ × ℤ ↦ (frestrictLe n w, w (n + 1))) := by fun_prop
  exact ae_of_ae_map (μ := μ) (p := fun p : ((i : Finset.Iic n) → ℝ × ℤ) × (ℝ × ℤ) ↦
    0 < p.2.1) hm.aemeasurable hprod

/-- Length of the stopped nonzero excursion; the initial zero hold (coordinate one) is excluded. -/
noncomputable def feedbackExcursionLength (w : ℕ → ℝ × ℤ) : ℝ≥0∞ :=
  ∑' n : ℕ, {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)}.indicator
    (fun w ↦ ENNReal.ofReal (w (n + 2)).1) w

/-- Total positive-return duration, including the initial zero hold. -/
noncomputable def feedbackReturnLength (w : ℕ → ℝ × ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (w 1).1 + feedbackExcursionLength w

@[fun_prop]
theorem measurable_feedbackExcursionLength : Measurable feedbackExcursionLength := by
  unfold feedbackExcursionLength
  exact Measurable.tsum fun n ↦
    (show Measurable (fun w : ℕ → ℝ × ℤ ↦ ENNReal.ofReal (w (n + 2)).1) from by
      fun_prop).indicator
    ((measurableSet_feedbackAvoidsZero n).preimage measurable_feedbackPostInitialCurrent)

@[fun_prop]
theorem measurable_feedbackReturnLength : Measurable feedbackReturnLength := by
  unfold feedbackReturnLength
  fun_prop

theorem feedbackExcursionLength_le_returnLength (w : ℕ → ℝ × ℤ) :
    feedbackExcursionLength w ≤ feedbackReturnLength w := le_add_self

private theorem feedbackAvoidsZero_mono {m n : ℕ} (hmn : m ≤ n) (w : ℕ → ℤ)
    (h : feedbackAvoidsZero n w) : feedbackAvoidsZero m w :=
  fun i hi ↦ h i (Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hi).trans hmn))

/-- The accumulated positive waits agree with the physical clock on nonnegative-wait paths. -/
theorem feedbackJumpTime_ofReal_eq_sum (w : ℕ → ℝ × ℤ)
    (hw : ∀ i, 0 ≤ (w (i + 1)).1) (n : ℕ) :
    ENNReal.ofReal (feedbackJumpTime n w) = ∑ i ∈ Finset.range n, ENNReal.ofReal (w (i + 1)).1 := by
  have hn (n : ℕ) : 0 ≤ feedbackJumpTime n w := by
    induction n with
    | zero => simp
    | succ n ih => rw [feedbackJumpTime_succ]; exact add_nonneg ih (hw n)
  induction n with
  | zero => simp
  | succ n ih =>
      rw [feedbackJumpTime_succ, ENNReal.ofReal_add (hn n) (hw n), ih, Finset.sum_range_succ]

/-- Once return has occurred by index n+1, its stopped duration is bounded by that finite clock. -/
theorem feedbackReturnLength_le_clock_of_not_avoids (w : ℕ → ℝ × ℤ)
    (hw : ∀ i, 0 ≤ (w (i + 1)).1) (n : ℕ)
    (h : ¬ feedbackAvoidsZero n (feedbackPostInitialCurrent w)) :
    feedbackReturnLength w ≤ ENNReal.ofReal (feedbackJumpTime (n + 1) w) := by
  unfold feedbackReturnLength feedbackExcursionLength
  rw [tsum_eq_sum (s := Finset.range n) (fun j hj ↦ by
    have hjn : n ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)
    exact Set.indicator_of_notMem (fun hh ↦ h (feedbackAvoidsZero_mono hjn _ hh)) _)]
  rw [feedbackJumpTime_ofReal_eq_sum w hw, Finset.sum_range_succ']
  conv_rhs => rw [add_comm]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro j hj
  by_cases hjz : feedbackAvoidsZero j (feedbackPostInitialCurrent w) <;>
    simp [Set.indicator, hjz, Nat.add_assoc]

/-- On a returning path, the stopped duration is the literal physical time of its first return. -/
theorem feedbackReturnLength_eq_first_clock (w : ℕ → ℝ × ℤ)
    (hw : ∀ i, 0 ≤ (w (i + 1)).1) (h : ∃ n, feedbackPostInitialCurrent w n = 0) :
    feedbackReturnLength w = ENNReal.ofReal (feedbackJumpTime (Nat.find h + 1) w) := by
  unfold feedbackReturnLength feedbackExcursionLength
  have heq (n : ℕ) :
      {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)}.indicator
        (fun w ↦ ENNReal.ofReal (w (n + 2)).1) w =
          if n < Nat.find h then ENNReal.ofReal (w (n + 2)).1 else 0 := by
    simp [Set.indicator, feedbackAvoidsZero_iff_lt_firstZero _ h]
  simp_rw [heq]
  rw [tsum_eq_sum (s := Finset.range (Nat.find h)) (fun n hn ↦ by
    simp only [Finset.mem_range, not_lt] at hn
    exact ite_eq_right (Nat.not_lt.mpr hn)),
    feedbackJumpTime_ofReal_eq_sum w hw, Finset.sum_range_succ']
  conv_rhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact ite_eq_left (Finset.mem_range.mp hn)

/-- Split the return-duration tail into a return-count tail and a deterministic-clock tail. -/
theorem feedbackReturnLength_tail_split {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) (T : ℝ) :
    feedbackHoldingJumpTrajectory lam hlam₀ hlam 0 {w | ENNReal.ofReal T < feedbackReturnLength w} ≤
      ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n +
        ENNReal.ofReal (Real.exp (-(T / 2))) * 2 ^ (n + 1) := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam 0
  calc
    _ ≤ μ ({w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)} ∪
        {w | T ≤ feedbackJumpTime (n + 1) w}) := by
      apply measure_mono_ae
      filter_upwards [feedbackHoldingJumpTrajectory_waits_positive hlam₀ hlam 0] with w hw
      intro h
      by_cases hz : feedbackAvoidsZero n (feedbackPostInitialCurrent w)
      · exact Or.inl hz
      · right
        by_contra ht
        exact not_lt_of_ge ((feedbackReturnLength_le_clock_of_not_avoids w
          (fun i ↦ (hw i).le) n hz).trans
            (ENNReal.ofReal_le_ofReal (le_of_not_ge ht))) h
    _ ≤ μ {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)} +
        μ {w | T ≤ feedbackJumpTime (n + 1) w} := measure_union_le _ _
    _ ≤ _ := add_le_add (feedbackHoldingJumpTrajectory_positive_return_tail hlam₀ hlam n)
      (feedbackJumpTime_upperTail hlam₀ hlam 0 (n + 1) T)

/-- Clock-tail ratio on the grid of physical times `4n`. -/
noncomputable def feedbackClockTailRatio : ℝ≥0∞ := ENNReal.ofReal (2 * Real.exp (-2))

theorem feedbackClockTailRatio_lt_one : feedbackClockTailRatio < 1 := by
  rw [feedbackClockTailRatio, ENNReal.ofReal_lt_one, Real.exp_neg]
  have he : 2 < Real.exp 2 := lt_of_lt_of_le (by norm_num) (Real.add_one_le_exp 2)
  rw [← div_eq_mul_inv, div_lt_one (Real.exp_pos 2)]
  exact he

/-- A geometric tail for the actual total return duration on a fixed linear time grid. -/
theorem feedbackReturnLength_tail {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    feedbackHoldingJumpTrajectory lam hlam₀ hlam 0
      {w | ENNReal.ofReal (4 * (n + 1 : ℕ)) < feedbackReturnLength w} ≤
      ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n +
        feedbackClockTailRatio ^ (n + 1) := by
  apply (feedbackReturnLength_tail_split hlam₀ hlam n (4 * (n + 1 : ℕ))).trans_eq
  congr 1
  rw [feedbackClockTailRatio, ENNReal.ofReal_mul (by norm_num), mul_pow]
  have he : -(4 * ((n + 1 : ℕ) : ℝ) / 2) = (n + 1 : ℕ) * (-2 : ℝ) := by ring
  rw [he, Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos _).le]
  norm_num [mul_comm]

/-- The actual nonzero excursion inherits the same geometric physical-length tail. -/
theorem feedbackExcursionLength_tail {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    feedbackHoldingJumpTrajectory lam hlam₀ hlam 0
      {w | ENNReal.ofReal (4 * (n + 1 : ℕ)) < feedbackExcursionLength w} ≤
      ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n +
        feedbackClockTailRatio ^ (n + 1) :=
  (measure_mono (fun w hw ↦ hw.trans_le (feedbackExcursionLength_le_returnLength w))).trans
    (feedbackReturnLength_tail hlam₀ hlam n)

/-- The actual stopped total return duration is finite almost surely. -/
theorem feedbackReturnLength_finite {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam 0, feedbackReturnLength w < ∞ := by
  filter_upwards [feedbackHoldingJumpTrajectory_returns_zero hlam₀ hlam,
    feedbackHoldingJumpTrajectory_waits_positive hlam₀ hlam 0] with w hz hw
  have h : ∃ n, feedbackPostInitialCurrent w n = 0 := by
    obtain ⟨n, hn, hz⟩ := hz
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact ⟨j, hz⟩
  rw [feedbackReturnLength_eq_first_clock w (fun i ↦ (hw i).le) h]
  exact ENNReal.ofReal_lt_top

private theorem grid_polynomial_geometric_summable {r : ℝ} (hr₀ : 0 < r)
    (hr₁ : r < 1) (p : ℕ) :
    (∑' n : ℕ, ENNReal.ofReal (4 * ((n + 2 : ℕ) : ℝ)) ^ p * ENNReal.ofReal r ^ n) < ∞ := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr₀]
  have hs : Summable (fun n : ℕ ↦ (n : ℝ) ^ p * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one p hr
  have hshift := (((summable_nat_add_iff 2).mpr hs).div_const (r ^ 2)).mul_left (4 ^ p)
  have hs' : Summable (fun n : ℕ ↦ (4 * ((n + 2 : ℕ) : ℝ)) ^ p * r ^ n) := by
    apply hshift.congr
    intro n
    rw [pow_add, mul_pow]
    field_simp
  have heq (n : ℕ) :
      ENNReal.ofReal ((4 * ((n + 2 : ℕ) : ℝ)) ^ p * r ^ n) =
        ENNReal.ofReal (4 * ((n + 2 : ℕ) : ℝ)) ^ p * ENNReal.ofReal r ^ n := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_pow hr₀.le]
  simpa only [heq] using hs'.tsum_ofReal_lt_top

private theorem returnLength_weighted_tail_summable {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (p : ℕ) :
    (∑' n : ℕ, ENNReal.ofReal (4 * ((n + 2 : ℕ) : ℝ)) ^ p *
      (ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n +
        feedbackClockTailRatio ^ (n + 1))) < ∞ := by
  have heq (n : ℕ) : ENNReal.ofReal (4 * ((n + 2 : ℕ) : ℝ)) ^ p *
      (ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n +
        feedbackClockTailRatio ^ (n + 1)) =
      ENNReal.ofReal (1 + lam) * (ENNReal.ofReal (4 * ((n + 2 : ℕ) : ℝ)) ^ p *
        ENNReal.ofReal (feedbackExcursionRatio lam) ^ n) +
      feedbackClockTailRatio * (ENNReal.ofReal (4 * ((n + 2 : ℕ) : ℝ)) ^ p *
        feedbackClockTailRatio ^ n) := by rw [pow_succ']; ring
  simp_rw [heq]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (grid_polynomial_geometric_summable (feedbackExcursionRatio_pos hlam₀ hlam)
        (feedbackExcursionRatio_lt_one hlam₀) p)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (grid_polynomial_geometric_summable (by positivity : 0 < 2 * Real.exp (-2))
        (ENNReal.ofReal_lt_one.mp feedbackClockTailRatio_lt_one) p)

/-- Every integer moment of the actual total return duration is finite. -/
theorem feedbackReturnLength_moments {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (p : ℕ) :
    (∫⁻ w, feedbackReturnLength w ^ p
      ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam 0) < ∞ := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam 0
  let F : ℕ → (ℕ → ℝ × ℤ) → ℝ≥0∞ := fun n ↦
    {w | ENNReal.ofReal (4 * ((n + 1 : ℕ) : ℝ)) < feedbackReturnLength w}.indicator
      (fun _ ↦ ENNReal.ofReal (4 * ((n + 2 : ℕ) : ℝ)) ^ p)
  have hm (n : ℕ) : MeasurableSet
      {w | ENNReal.ofReal (4 * ((n + 1 : ℕ) : ℝ)) < feedbackReturnLength w} := by measurability
  have hF (n : ℕ) : Measurable (F n) := measurable_const.indicator (hm n)
  have hbound : ∀ᵐ w ∂μ, feedbackReturnLength w ^ p ≤ 4 ^ p + ∑' n : ℕ, F n w := by
    filter_upwards [feedbackReturnLength_finite hlam₀ hlam] with w hw
    have hex : ∃ n : ℕ, feedbackReturnLength w ≤ ENNReal.ofReal (4 * ((n + 1 : ℕ) : ℝ)) := by
      obtain ⟨n, hn⟩ := exists_nat_gt (feedbackReturnLength w).toReal
      refine ⟨n, (ENNReal.le_ofReal_iff_toReal_le hw.ne (by positivity)).mpr ?_⟩
      push_cast
      linarith
    have hle := ENNReal.pow_le_pow_left (n := p) (Nat.find_spec hex)
    cases hi : Nat.find hex with
    | zero =>
        simp only [hi, zero_add, Nat.cast_one, mul_one, ENNReal.ofReal_ofNat] at hle
        exact hle.trans le_self_add
    | succ j =>
        have hj : ENNReal.ofReal (4 * ((j + 1 : ℕ) : ℝ)) < feedbackReturnLength w :=
          lt_of_not_ge (Nat.find_min hex (by rw [hi]; omega))
        calc
          _ ≤ ENNReal.ofReal (4 * ((j + 2 : ℕ) : ℝ)) ^ p := by simpa only [hi] using hle
          _ = F j w := by
            dsimp [F]
            rw [Set.indicator_of_mem (show w ∈
              {w | ENNReal.ofReal (4 * ((j + 1 : ℕ) : ℝ)) < feedbackReturnLength w} from hj)]
          _ ≤ ∑' n : ℕ, F n w := ENNReal.le_tsum j
          _ ≤ _ := le_add_self
  apply lt_of_le_of_lt (lintegral_mono_ae hbound)
  rw [lintegral_add_left measurable_const, lintegral_tsum (fun n ↦ (hF n).aemeasurable)]
  simp only [lintegral_const, measure_univ, mul_one]
  apply lt_of_le_of_lt (add_le_add_right (ENNReal.tsum_le_tsum (fun n ↦ ?_)) (4 ^ p))
    (ENNReal.add_lt_top.mpr ⟨ENNReal.pow_lt_top (by norm_num),
      returnLength_weighted_tail_summable hlam₀ hlam p⟩)
  change (∫⁻ w, F n w ∂μ) ≤ _
  rw [show F n = {w | ENNReal.ofReal (4 * ((n + 1 : ℕ) : ℝ)) < feedbackReturnLength w}.indicator
      (fun _ ↦ ENNReal.ofReal (4 * ((n + 2 : ℕ) : ℝ)) ^ p) from rfl,
    lintegral_indicator (hm n), lintegral_const, Measure.restrict_apply_univ]
  exact mul_le_mul_right (feedbackReturnLength_tail hlam₀ hlam n) _

/-- The nonzero excursion (excluding the initial zero hold) has every integer length moment. -/
theorem feedbackExcursionLength_moments {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (p : ℕ) :
    (∫⁻ w, feedbackExcursionLength w ^ p
      ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam 0) < ∞ :=
  lt_of_le_of_lt (lintegral_mono (fun w ↦
    ENNReal.pow_le_pow_left (feedbackExcursionLength_le_returnLength w)))
    (feedbackReturnLength_moments hlam₀ hlam p)

end OTSelector.Limit
