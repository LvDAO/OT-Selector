import OTSelector.Feedback.FeedbackRightIntervalCounts
import OTSelector.Probability.FiniteIntervalCountsProduct

/-!
# Two-color interval counts on the complete frozen product law

The probability bound retains the entire heterogeneous unseen product.  Each color is an iid
subfamily with its actual boundary-conditioned marginal; a union bound handles the two colors.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace OTSelector.RightTail

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit two-color integer-grid failure envelope. -/
noncomputable def intervalGridFailureBound (N : ℕ) (r : ℝ) : ℝ :=
  4 * (N + 1 : ℝ) ^ 2 * Real.exp (-r / 12)

theorem intervalGridFailureBound_nonneg (N : ℕ) (r : ℝ) :
    0 ≤ intervalGridFailureBound N r := by unfold intervalGridFailureBound; positivity

/-- Both colors have uniform grid lower counts under the actual heterogeneous product law. -/
theorem fixedLaw_twoColorGrid_failure_le
    {n N : ℕ} (hn : 0 < n) (J : Finset ι) {q xR hi c r : ℝ}
    (hR : (xR, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (hstrip : ∀ u ∈ Icc xR hi, (u, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (hsource : 2 * c * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n q xR)) ≤ J.card)
    (htarget : 2 * c * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSet n q xR)) ≤ Jᶜ.card) (hr : 0 < r) :
    Measure.pi (fixedLaw n q xR J)
      {sample | ¬(FiniteIntervalCounts.groupGridGood N J (sourcePhase n q) xR hi c r sample ∧
        FiniteIntervalCounts.groupGridGood N Jᶜ (targetPhase n q) xR hi c r sample)} ≤
      ENNReal.ofReal (intervalGridFailureBound N r) := by
  let P := fixedLaw n q xR J
  have : ∀ i, IsProbabilityMeasure (P i) := fixedLaw_isProbabilityMeasure hn J hR
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hareas := remainingAreas_pos_of_unclippedRegion hR
  have hsourceSection := FiniteSample.sourceBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have htargetSection := FiniteSample.targetBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have hsourceMass : 0 < (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n q xR) := by
    rw [unitSquareUniform_sourceRawRemainingSet hn
      (fun u ↦ (hsourceSection u).1.le) (fun u ↦ (hsourceSection u).2.le)]
    exact div_pos hareas.1 hnreal
  have htargetMass : 0 < (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSet n q xR) := by
    rw [unitSquareUniform_targetRawRemainingSet hn
      (fun u ↦ (htargetSection u).1.le) (fun u ↦ (htargetSection u).2.le)]
    exact div_pos hareas.2 hnreal
  let QS := (unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]
  let QT := (unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]
  have : IsProbabilityMeasure QS :=
    cond_isProbabilityMeasure ((measureReal_ne_zero_iff).mp hsourceMass.ne')
  have : IsProbabilityMeasure QT :=
    cond_isProbabilityMeasure ((measureReal_ne_zero_iff).mp htargetMass.ne')
  have hs : Measure.pi P
      {sample | ¬FiniteIntervalCounts.groupGridGood N J (sourcePhase n q) xR hi c r sample} ≤
      ((N + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp (-r / 12)) := by
    apply FiniteIntervalCounts.measure_not_groupGridGood_pi_le P QS J
      (fun i hi ↦ by simp [P, fixedLaw, hi, QS]) N
      (by unfold sourcePhase; fun_prop) xR hi c hr
    intro a b hRa hab hbh
    rw [sourceLaw_Ioo hn hRa hab (hstrip _ ⟨hRa, hab.trans hbh⟩)
      (hstrip _ ⟨hRa.trans hab, hbh⟩)]
    have hd := (le_div_iff₀ (mul_pos hnreal hsourceMass)).mpr hsource
    have h := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hab)
    calc
      _ ≤ _ := h
      _ = _ := by ring
  have ht : Measure.pi P
      {sample | ¬FiniteIntervalCounts.groupGridGood N Jᶜ (targetPhase n q) xR hi c r sample} ≤
      ((N + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp (-r / 12)) := by
    apply FiniteIntervalCounts.measure_not_groupGridGood_pi_le P QT Jᶜ
      (fun i hi ↦ by simp [P, fixedLaw, Finset.mem_compl.mp hi, QT]) N
      (by unfold targetPhase; fun_prop) xR hi c hr
    intro a b hRa hab hbh
    rw [targetLaw_Ioo hn hRa hab (hstrip _ ⟨hRa, hab.trans hbh⟩)
      (hstrip _ ⟨hRa.trans hab, hbh⟩)]
    have hd := (le_div_iff₀ (mul_pos hnreal htargetMass)).mpr htarget
    have h := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hab)
    calc
      _ ≤ _ := h
      _ = _ := by ring
  have hset : {sample | ¬(FiniteIntervalCounts.groupGridGood N J (sourcePhase n q) xR hi c r sample ∧
      FiniteIntervalCounts.groupGridGood N Jᶜ (targetPhase n q) xR hi c r sample)} =
      {sample | ¬FiniteIntervalCounts.groupGridGood N J (sourcePhase n q) xR hi c r sample} ∪
        {sample | ¬FiniteIntervalCounts.groupGridGood N Jᶜ (targetPhase n q) xR hi c r sample} := by
    ext sample
    simp only [mem_ofPred_eq, mem_union]
    tauto
  rw [hset]
  refine (measure_union_le _ _).trans ((add_le_add hs ht).trans ?_)
  have heq : ENNReal.ofReal (intervalGridFailureBound N r) =
      2 * (((N + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp (-r / 12))) := by
    have heqreal : intervalGridFailureBound N r =
        2 * (((N + 1 : ℕ) : ℝ) ^ 2 * (2 * Real.exp (-r / 12))) := by
      unfold intervalGridFailureBound
      push_cast
      ring
    rw [heqreal, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (by positivity)]
    norm_num [ENNReal.ofReal_add]
  rw [heq]
  exact le_of_eq (by ring)

/-- A logarithmic grid error gives a polynomially vanishing failure envelope. -/
theorem intervalGridFailureBound_log_le {n : ℕ} (hn : 1 ≤ n) :
    intervalGridFailureBound n (60 * Real.log n) ≤ 16 / (n : ℝ) ^ 3 := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : Real.exp (-(60 * Real.log (n : ℝ)) / 12) = 1 / (n : ℝ) ^ 5 := by
    rw [show -(60 * Real.log (n : ℝ)) / 12 = (5 : ℕ) * (-Real.log (n : ℝ)) by
      norm_num; ring, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hnreal]
    simp [one_div, inv_pow]
  rw [intervalGridFailureBound, hexp]
  have hsquare : ((n : ℝ) + 1) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
  calc
    4 * ((n : ℝ) + 1) ^ 2 * (1 / (n : ℝ) ^ 5) ≤
        4 * (4 * (n : ℝ) ^ 2) * (1 / (n : ℝ) ^ 5) := by
      gcongr
    _ = _ := by field_simp; ring

end OTSelector.RightTail
