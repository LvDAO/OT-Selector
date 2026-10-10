import OTSelector.Feedback.CrossingRates

/-!
# Deterministic bounds for the feedback crossing rates

The residual-density window makes both marked crossing rates uniformly bounded.  This
file contains only the scalar algebra used by the later generator estimates.
-/

namespace OTSelector

/-- The feedback slope is bounded by the magnitude of the feedback parameter. -/
theorem abs_feedbackSlope_le {lam k : ℝ} (hlam : 0 ≤ lam) :
    |feedbackSlope lam k| ≤ lam := by
  by_cases hkpos : 0 < k
  · simp [feedbackSlope, hkpos, abs_of_nonneg hlam]
  · by_cases hkneg : k < 0
    · have hnot : ¬0 < k := not_lt.mpr (le_of_lt hkneg)
      simp [feedbackSlope, hnot, hkneg, abs_of_nonneg hlam]
    · have hkzero : k = 0 := by
        linarith [le_of_not_gt hkpos, le_of_not_gt hkneg]
      subst k
      simpa [feedbackSlope] using hlam

private theorem crossing_eta_le_one_sixteenth
    {lam eta rMinus rPlus : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) :
    eta ≤ 1 / 16 := by
  have htwo : 2 * eta ≤ eta * (2 + lam) := by
    have h := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ 2 + lam by linarith)
      hreg.eta_nonneg
    nlinarith
  nlinarith [hreg.eta_small]

private theorem source_rate_nonneg
    {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) :
    0 ≤ sourceTotalRate rMinus (feedbackSlope lam k) := by
  have heta : eta ≤ 1 / 16 := crossing_eta_le_one_sixteenth hlam0 hlam hreg
  have hw := abs_feedbackSlope_le (k := k) hlam0.le
  have hw_bounds : -lam ≤ feedbackSlope lam k ∧ feedbackSlope lam k ≤ lam :=
    (abs_le.mp hw)
  have hr : 0 ≤ rMinus := by nlinarith [hreg.source_lower]
  have hf : 0 ≤ 1 - feedbackSlope lam k / 2 := by
    nlinarith [hw_bounds.2]
  exact mul_nonneg hr hf

private theorem target_rate_nonneg
    {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) :
    0 ≤ targetTotalRate rPlus (feedbackSlope lam k) := by
  have heta : eta ≤ 1 / 16 := crossing_eta_le_one_sixteenth hlam0 hlam hreg
  have hw := abs_feedbackSlope_le (k := k) hlam0.le
  have hw_bounds : -lam ≤ feedbackSlope lam k ∧ feedbackSlope lam k ≤ lam :=
    (abs_le.mp hw)
  have hr : 0 ≤ rPlus := by nlinarith [hreg.target_lower]
  have hf : 0 ≤ 1 + 3 * feedbackSlope lam k / 2 := by
    nlinarith [hw_bounds.1]
  exact mul_nonneg hr hf

/-- The source crossing rate is nonnegative and bounded by the universal constant `3`. -/
theorem sourceTotalRate_bounds
    {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) :
    0 ≤ sourceTotalRate rMinus (feedbackSlope lam k) ∧
      sourceTotalRate rMinus (feedbackSlope lam k) ≤ 3 := by
  have heta : eta ≤ 1 / 16 := crossing_eta_le_one_sixteenth hlam0 hlam hreg
  have hw := abs_feedbackSlope_le (k := k) hlam0.le
  have hw_bounds : -lam ≤ feedbackSlope lam k ∧ feedbackSlope lam k ≤ lam :=
    (abs_le.mp hw)
  have hr : 0 ≤ rMinus := by nlinarith [hreg.source_lower]
  have hru : 1 + eta ≤ (17 : ℝ) / 16 := by nlinarith [heta]
  have hf : 0 ≤ 1 - feedbackSlope lam k / 2 := by
    nlinarith [hw_bounds.2]
  have hfu : 1 - feedbackSlope lam k / 2 ≤ (17 : ℝ) / 16 := by
    nlinarith [hw_bounds.1, hlam]
  have hstep₁ := mul_le_mul_of_nonneg_right hreg.source_upper hf
  have hstep₂ :
      (1 + eta) * (1 - feedbackSlope lam k / 2) ≤
        (1 + eta) * ((17 : ℝ) / 16) :=
    mul_le_mul_of_nonneg_left hfu (by linarith [hreg.eta_nonneg])
  have hstep₃ := mul_le_mul_of_nonneg_right hru (by norm_num : (0 : ℝ) ≤ 17 / 16)
  constructor
  · exact source_rate_nonneg hlam0 hlam hreg
  · simp only [sourceTotalRate] at hstep₁ ⊢
    calc
      rMinus * (1 - feedbackSlope lam k / 2) ≤
          (1 + eta) * (1 - feedbackSlope lam k / 2) := hstep₁
      _ ≤ (1 + eta) * ((17 : ℝ) / 16) := hstep₂
      _ ≤ ((17 : ℝ) / 16) * ((17 : ℝ) / 16) := hstep₃
      _ ≤ 3 := by norm_num

/-- The target crossing rate is nonnegative and bounded by the universal constant `3`. -/
theorem targetTotalRate_bounds
    {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) :
    0 ≤ targetTotalRate rPlus (feedbackSlope lam k) ∧
      targetTotalRate rPlus (feedbackSlope lam k) ≤ 3 := by
  have heta : eta ≤ 1 / 16 := crossing_eta_le_one_sixteenth hlam0 hlam hreg
  have hw := abs_feedbackSlope_le (k := k) hlam0.le
  have hw_bounds : -lam ≤ feedbackSlope lam k ∧ feedbackSlope lam k ≤ lam :=
    (abs_le.mp hw)
  have hr : 0 ≤ rPlus := by nlinarith [hreg.target_lower]
  have hru : 1 + eta ≤ (17 : ℝ) / 16 := by nlinarith [heta]
  have hf : 0 ≤ 1 + 3 * feedbackSlope lam k / 2 := by
    nlinarith [hw_bounds.1]
  have hfu : 1 + 3 * feedbackSlope lam k / 2 ≤ (19 : ℝ) / 16 := by
    nlinarith [hw_bounds.2, hlam]
  have hstep₁ := mul_le_mul_of_nonneg_right hreg.target_upper hf
  have hstep₂ :
      (1 + eta) * (1 + 3 * feedbackSlope lam k / 2) ≤
        (1 + eta) * ((19 : ℝ) / 16) :=
    mul_le_mul_of_nonneg_left hfu (by linarith [hreg.eta_nonneg])
  have hstep₃ := mul_le_mul_of_nonneg_right hru (by norm_num : (0 : ℝ) ≤ 19 / 16)
  constructor
  · exact target_rate_nonneg hlam0 hlam hreg
  · simp only [targetTotalRate] at hstep₁ ⊢
    calc
      rPlus * (1 + 3 * feedbackSlope lam k / 2) ≤
          (1 + eta) * (1 + 3 * feedbackSlope lam k / 2) := hstep₁
      _ ≤ (1 + eta) * ((19 : ℝ) / 16) := hstep₂
      _ ≤ ((17 : ℝ) / 16) * ((19 : ℝ) / 16) := hstep₃
      _ ≤ 3 := by norm_num

/-- The scalar rate difference has the local inward drift with constant `c = lam`. -/
theorem feedback_rate_inward_drift
    {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) (hk : k ≠ 0) :
    (if 0 < k then
        sourceTotalRate rMinus (feedbackSlope lam k) -
          targetTotalRate rPlus (feedbackSlope lam k) ≤ -lam
      else
        lam ≤ sourceTotalRate rMinus (feedbackSlope lam k) -
          targetTotalRate rPlus (feedbackSlope lam k)) := by
  exact A1_inward_drift hlam0 hlam hreg hk

end OTSelector
