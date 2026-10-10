import OTSelector.Feedback.FeedbackLeftCountingIntensity

/-!
# Survival of the actual left rate stop

The existing terminal count event controls the post-jump rates, including their jump values.
Consequently its probability bound applies to the actual capped rate exit time used by the
left-prefix energy theorem.  Genericity costs no probability under the original iid sample law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace OTSelector.FiniteSample

variable {n : ℕ}

/-- The actual post-jump rate path remains in its admissible region on the terminal count event. -/
theorem leftPostRatePath_mem_region_of_count_good (hn : 0 < n) {B t : ℝ≥0}
    (htB : t ≤ B) (hBquarter : 4 * (B : ℝ) ≤ n) {sample : FiniteSample n}
    (hgeneric : sample ∈ leftHeightGenericEvent n)
    (hgood : sample ∈ leftRateCountGoodEvent n B) :
    leftPostRatePath n B t sample ∈ leftRateRegion := by
  have hBn : (B : ℝ) ≤ n := by nlinarith [B.2]
  have htBreal : (t : ℝ) ≤ B := htB
  change leftColorPostRate n B 0 t sample ∈ Icc ((1 : ℝ) / 2) 2 ∧
    leftColorPostRate n B 1 t sample ∈ Icc ((1 : ℝ) / 2) 2
  constructor
  · rw [leftColorPostRate, ite_eq_left hgeneric,
      show leftColorCount n B 0 = leftSourceCountingProcess n B from rfl,
      leftSourceCountingProcess_eq_leftSourceCountAt_of_good hn htB hBn hgeneric,
      leftRateDenominator_eq_sub_of_le htB]
    apply leftRate_mem_Icc_of_count_le hn t.2 htBreal hBquarter (by positivity)
    have hmono := leftSourceCountAt_rank_le_terminal hn t.2 htBreal hBn sample
    exact (Nat.cast_le.mpr hmono).trans hgood.1
  · rw [leftColorPostRate, ite_eq_left hgeneric,
      show leftColorCount n B 1 = leftTargetCountingProcess n B from rfl,
      leftTargetCountingProcess_eq_leftTargetCountAt_of_good hn htB hBn hgeneric,
      leftRateDenominator_eq_sub_of_le htB]
    apply leftRate_mem_Icc_of_count_le hn t.2 htBreal hBquarter (by positivity)
    have hmono := leftTargetCountAt_rank_le_terminal hn t.2 htBreal hBn sample
    exact (Nat.cast_le.mpr hmono).trans hgood.2

/-- A generic sample on the terminal count event reaches the prescribed left endpoint before
the rate stop. This discharges the survival input of the left-prefix graph bridge. -/
theorem leftRateExitTime_eq_boundary_of_count_good (hn : 0 < n) {B : ℝ≥0}
    (hBquarter : 4 * (B : ℝ) ≤ n) {sample : FiniteSample n}
    (hgeneric : sample ∈ leftHeightGenericEvent n)
    (hgood : sample ∈ leftRateCountGoodEvent n B) :
    leftRateExitTime n B sample = (B : WithTop ℝ≥0) := by
  unfold leftRateExitTime
  apply min_eq_right
  simp only [hittingAfter]
  split_ifs with h
  · apply WithTop.coe_le_coe.mpr
    apply le_csInf h
    intro t ht
    by_contra hBt
    have hregion := leftPostRatePath_mem_region_of_count_good hn
      (le_of_not_ge hBt) hBquarter hgeneric hgood
    exact ht.2 hregion
  · exact le_top

/-- The true left rate-exit failure inherits the existing exponential count tail. -/
theorem measure_leftRateExitTime_ne_boundary_le (hn : 0 < n) {B : ℝ≥0}
    (hB : 0 < B) (hBquarter : 4 * (B : ℝ) ≤ n) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | leftRateExitTime n B sample ≠ (B : WithTop ℝ≥0)} ≤
      2 * ENNReal.ofReal (2 * Real.exp (-(B : ℝ) / 8)) := by
  have hBn : (B : ℝ) ≤ n := by nlinarith [B.2]
  apply (measure_mono_ae ?_).trans
    (measure_leftRateCountGoodEvent_compl_le_exp hn (show 0 < (B : ℝ) from hB) hBn)
  filter_upwards [ae_mem_leftHeightGenericEvent n] with sample hgeneric
  intro hfail hgood
  exact hfail (leftRateExitTime_eq_boundary_of_count_good hn hBquarter hgeneric hgood)

/-- Real-valued probability bound for the actual left-stop failure. -/
theorem measureReal_leftRateExitTime_ne_boundary_le (hn : 0 < n) {B : ℝ≥0}
    (hB : 0 < B) (hBquarter : 4 * (B : ℝ) ≤ n) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {sample | leftRateExitTime n B sample ≠ (B : WithTop ℝ≥0)} ≤
      4 * Real.exp (-(B : ℝ) / 8) := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    (measure_leftRateExitTime_ne_boundary_le hn hB hBquarter)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by positivity)] at h
  change (finiteSampleLaw n : Measure (FiniteSample n)).real
    {sample | leftRateExitTime n B sample ≠ (B : WithTop ℝ≥0)} ≤ _ at h
  linarith

end OTSelector.FiniteSample
