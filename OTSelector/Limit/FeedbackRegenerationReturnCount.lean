import OTSelector.Limit.FeedbackRegenerationReturnPhysical
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Jump-count moments for the actual feedback excursion

The first positive return count equals one plus the number of prefixes of positive jump indices
that have avoided zero. This explicit observable is measurable and may be infinite on arbitrary
paths. Its finite moments below are consequences of the proved actual trajectory tail.
-/

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ENNReal BigOperators

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- The first positive return count, represented by its prefix-survival indicators. -/
noncomputable def feedbackReturnJumpCount (w : ℕ → ℝ × ℤ) : ℝ≥0∞ :=
  1 + ∑' n : ℕ, {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)}.indicator
    (fun _ ↦ (1 : ℝ≥0∞)) w

@[fun_prop]
theorem measurable_feedbackReturnJumpCount : Measurable feedbackReturnJumpCount := by
  unfold feedbackReturnJumpCount
  have ht : Measurable (fun w ↦ ∑' n : ℕ,
      {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) w) :=
    Measurable.tsum fun n ↦ measurable_const.indicator
      ((measurableSet_feedbackAvoidsZero n).preimage measurable_feedbackPostInitialCurrent)
  exact measurable_const.add ht

/-- The prefix event has its literal meaning before the least zero index. -/
theorem feedbackAvoidsZero_iff_lt_firstZero (w : ℕ → ℤ) (h : ∃ n, w n = 0) (n : ℕ) :
    feedbackAvoidsZero n w ↔ n < Nat.find h := by
  constructor
  · intro hn
    by_contra hlt
    exact hn (Nat.find h) (Finset.mem_Iic.mpr (Nat.le_of_not_gt hlt)) (Nat.find_spec h)
  · intro hn i hi
    exact Nat.find_min h ((Finset.mem_Iic.mp hi).trans_lt hn)

/-- On every path which returns, the indicator count is exactly its first positive zero index. -/
theorem feedbackReturnJumpCount_eq_first (w : ℕ → ℝ × ℤ)
    (h : ∃ n, feedbackPostInitialCurrent w n = 0) :
    feedbackReturnJumpCount w = (Nat.find h + 1 : ℕ) := by
  unfold feedbackReturnJumpCount
  have heq (n : ℕ) :
      {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) w = if n < Nat.find h then 1 else 0 := by
    simp [Set.indicator, feedbackAvoidsZero_iff_lt_firstZero _ h]
  simp_rw [heq]
  rw [tsum_eq_sum (s := Finset.range (Nat.find h)) (fun n hn ↦ by
    simp only [Finset.mem_range, not_lt] at hn
    exact ite_eq_right (Nat.not_lt.mpr hn))]
  have hs : (∑ n ∈ Finset.range (Nat.find h),
      if n < Nat.find h then (1 : ℝ≥0∞) else 0) = Nat.find h := by
    calc
      _ = ∑ _n ∈ Finset.range (Nat.find h), (1 : ℝ≥0∞) :=
        Finset.sum_congr rfl (fun n hn ↦ ite_eq_left (Finset.mem_range.mp hn))
      _ = _ := by simp
  rw [hs]
  simp only [Nat.cast_add, Nat.cast_one, add_comm]

/-- Explicit first-moment bound for the actual excursion jump count. -/
theorem feedbackReturnJumpCount_integral_le {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∫⁻ w, feedbackReturnJumpCount w ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam 0 ≤
      1 + ENNReal.ofReal (1 + lam) * (1 - ENNReal.ofReal (feedbackExcursionRatio lam))⁻¹ := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam 0
  have hm (n : ℕ) : MeasurableSet {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)} :=
    (measurableSet_feedbackAvoidsZero n).preimage measurable_feedbackPostInitialCurrent
  change ∫⁻ w, (1 + ∑' n : ℕ, {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)}.indicator
    (fun _ ↦ (1 : ℝ≥0∞)) w) ∂μ ≤ _
  rw [lintegral_add_left measurable_const,
    lintegral_tsum (fun n ↦ (measurable_const.indicator (hm n)).aemeasurable)]
  simp only [lintegral_const, measure_univ, mul_one]
  apply add_le_add_right
  calc
    _ = ∑' n : ℕ, μ {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)} := by
      congr 1
      funext n
      rw [lintegral_indicator (hm n)]
      simp
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (1 + lam) *
        ENNReal.ofReal (feedbackExcursionRatio lam) ^ n :=
      ENNReal.tsum_le_tsum (fun n ↦ feedbackHoldingJumpTrajectory_positive_return_tail hlam₀ hlam n)
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

private theorem excursion_polynomial_geometric_summable {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (p : ℕ) :
    (∑' n : ℕ, ((n + 2 : ℕ) : ℝ≥0∞) ^ p *
      ENNReal.ofReal (feedbackExcursionRatio lam) ^ n) < ∞ := by
  let r := feedbackExcursionRatio lam
  have hr₀ : 0 < r := feedbackExcursionRatio_pos hlam₀ hlam
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr₀]
    exact feedbackExcursionRatio_lt_one hlam₀
  have hs : Summable (fun n : ℕ ↦ (n : ℝ) ^ p * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one p hr
  have hshift := ((summable_nat_add_iff 2).mpr hs).div_const (r ^ 2)
  have hs' : Summable (fun n : ℕ ↦ ((n + 2 : ℕ) : ℝ) ^ p * r ^ n) := by
    apply hshift.congr
    intro n
    rw [pow_add]
    field_simp
  have heq (n : ℕ) :
      ENNReal.ofReal (((n + 2 : ℕ) : ℝ) ^ p * r ^ n) =
        ((n + 2 : ℕ) : ℝ≥0∞) ^ p * ENNReal.ofReal r ^ n := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_pow hr₀.le]
    simp only [ENNReal.ofReal_natCast]
  simpa only [heq] using hs'.tsum_ofReal_lt_top

/-- Every nonnegative integer moment of the actual first positive return jump count is finite. -/
theorem feedbackReturnJumpCount_moments {lam : ℝ} (hlam₀ : 0 < lam)
    (hlam : lam < 1 / 2) (p : ℕ) :
    (∫⁻ w, feedbackReturnJumpCount w ^ p
      ∂feedbackHoldingJumpTrajectory lam hlam₀ hlam 0) < ∞ := by
  let μ := feedbackHoldingJumpTrajectory lam hlam₀ hlam 0
  let F : ℕ → (ℕ → ℝ × ℤ) → ℝ≥0∞ := fun n ↦
    {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)}.indicator
      (fun _ ↦ ((n + 2 : ℕ) : ℝ≥0∞) ^ p)
  have hm (n : ℕ) : MeasurableSet {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)} :=
    (measurableSet_feedbackAvoidsZero n).preimage measurable_feedbackPostInitialCurrent
  have hF (n : ℕ) : Measurable (F n) := measurable_const.indicator (hm n)
  have hbound : ∀ᵐ w ∂μ, feedbackReturnJumpCount w ^ p ≤ 1 + ∑' n : ℕ, F n w := by
    filter_upwards [feedbackHoldingJumpTrajectory_returns_zero hlam₀ hlam] with w hw
    have hex : ∃ n, feedbackPostInitialCurrent w n = 0 := by
      obtain ⟨n, hn, hz⟩ := hw
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      exact ⟨j, hz⟩
    rw [feedbackReturnJumpCount_eq_first w hex]
    cases hi : Nat.find hex with
    | zero => simp only [zero_add, Nat.cast_one, one_pow]; exact le_self_add
    | succ j =>
        have hj : feedbackAvoidsZero j (feedbackPostInitialCurrent w) :=
          (feedbackAvoidsZero_iff_lt_firstZero _ hex j).mpr (by rw [hi]; omega)
        calc
          _ = F j w := by
            dsimp [F]
            rw [Set.indicator_of_mem (show
              w ∈ {w | feedbackAvoidsZero j (feedbackPostInitialCurrent w)} from hj)]
          _ ≤ ∑' n : ℕ, F n w := ENNReal.le_tsum j
          _ ≤ _ := le_add_self
  have hseries : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ≥0∞) ^ p *
      (ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n)) < ∞ := by
    have heq : (∑' n : ℕ, ((n + 2 : ℕ) : ℝ≥0∞) ^ p *
        (ENNReal.ofReal (1 + lam) * ENNReal.ofReal (feedbackExcursionRatio lam) ^ n)) =
        ENNReal.ofReal (1 + lam) * ∑' n : ℕ, ((n + 2 : ℕ) : ℝ≥0∞) ^ p *
          ENNReal.ofReal (feedbackExcursionRatio lam) ^ n := by
      rw [← ENNReal.tsum_mul_left]
      congr 1
      funext n
      ac_rfl
    rw [heq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (excursion_polynomial_geometric_summable hlam₀ hlam p)
  apply lt_of_le_of_lt (lintegral_mono_ae hbound)
  rw [lintegral_add_left measurable_const, lintegral_tsum (fun n ↦ (hF n).aemeasurable)]
  simp only [lintegral_const, measure_univ, mul_one]
  apply lt_of_le_of_lt (add_le_add_right (ENNReal.tsum_le_tsum (fun n ↦ ?_)) 1)
    (ENNReal.add_lt_top.mpr ⟨by simp, hseries⟩)
  change (∫⁻ w, F n w ∂μ) ≤ _
  rw [show F n = {w | feedbackAvoidsZero n (feedbackPostInitialCurrent w)}.indicator
      (fun _ ↦ ((n + 2 : ℕ) : ℝ≥0∞) ^ p) from rfl,
    lintegral_indicator (hm n), lintegral_const, Measure.restrict_apply_univ]
  exact mul_le_mul_right (feedbackHoldingJumpTrajectory_positive_return_tail hlam₀ hlam n) _

end OTSelector.Limit
