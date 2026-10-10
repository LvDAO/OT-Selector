import OTSelector.Feedback.Graph

/-!
# Adaptive crossing-rate algebra

This is the exact finite-dimensional algebra behind (1.13)--(1.20).  Empirical-process estimates
are responsible only for proving that the residual densities stay in the displayed regularity
window.
-/

namespace OTSelector

/-- Feedback slope `λ sign(k)`, with the paper's convention `sign(0)=0`. -/
noncomputable def feedbackSlope (lam k : ℝ) : ℝ :=
  if 0 < k then lam else if k < 0 then -lam else 0

def sourceMarkedFactor (w u : ℝ) : ℝ :=
  1 - w * (1 - u)

def targetMarkedFactor (w v : ℝ) : ℝ :=
  1 + w * (1 + v)

/-- Total source rate obtained by averaging its affine mark density on `[0,1]`. -/
noncomputable def sourceTotalRate (residualDensity w : ℝ) : ℝ :=
  residualDensity * (1 - w / 2)

/-- Total target rate obtained by averaging its affine mark density on `[0,1]`. -/
noncomputable def targetTotalRate (residualDensity w : ℝ) : ℝ :=
  residualDensity * (1 + 3 * w / 2)

theorem sourceMarkedFactor_uniform_average (w : ℝ) :
    sourceMarkedFactor w (1 / 2) = 1 - w / 2 := by
  simp [sourceMarkedFactor]
  ring

theorem targetMarkedFactor_uniform_average (w : ℝ) :
    targetMarkedFactor w (1 / 2) = 1 + 3 * w / 2 := by
  simp [targetMarkedFactor]
  ring

/-- Residual-density regularity needed for the A1 drift calculation. -/
structure CrossingRegularity (lam eta rMinus rPlus : ℝ) : Prop where
  eta_nonneg : 0 ≤ eta
  eta_small : eta * (2 + lam) ≤ lam
  source_lower : 1 - eta ≤ rMinus
  source_upper : rMinus ≤ 1 + eta
  target_lower : 1 - eta ≤ rPlus
  target_upper : rPlus ≤ 1 + eta

/-- Positive current gives a uniformly negative rate drift. -/
theorem A1_drift_positive {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) (hk : 0 < k) :
    sourceTotalRate rMinus (feedbackSlope lam k) -
      targetTotalRate rPlus (feedbackSlope lam k) ≤ -lam := by
  have hw : feedbackSlope lam k = lam := by simp [feedbackSlope, hk]
  have hsourceFactor : 0 ≤ 1 - lam / 2 := by linarith
  have htargetFactor : 0 ≤ 1 + 3 * lam / 2 := by linarith
  have hs := mul_le_mul_of_nonneg_right hreg.source_upper hsourceFactor
  have ht := mul_le_mul_of_nonneg_right hreg.target_lower htargetFactor
  rw [hw]
  simp only [sourceTotalRate, targetTotalRate]
  nlinarith [hreg.eta_small]

/-- Negative current gives a uniformly positive rate drift. -/
theorem A1_drift_negative {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) (hk : k < 0) :
    lam ≤ sourceTotalRate rMinus (feedbackSlope lam k) -
      targetTotalRate rPlus (feedbackSlope lam k) := by
  have hw : feedbackSlope lam k = -lam := by simp [feedbackSlope, hk, not_lt.mpr (le_of_lt hk)]
  have hsourceFactor : 0 ≤ 1 + lam / 2 := by linarith
  have htargetFactor : 0 ≤ 1 - 3 * lam / 2 := by linarith
  have hs := mul_le_mul_of_nonneg_right hreg.source_lower hsourceFactor
  have ht := mul_le_mul_of_nonneg_right hreg.target_upper htargetFactor
  have heta : eta * (2 - lam) ≤ lam := by nlinarith [hreg.eta_small]
  rw [hw]
  simp only [sourceTotalRate, targetTotalRate]
  nlinarith

/-- Combined A1 inward-drift statement away from zero. -/
theorem A1_inward_drift {lam eta rMinus rPlus k : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus) (hk : k ≠ 0) :
    (if 0 < k then
        sourceTotalRate rMinus (feedbackSlope lam k) -
          targetTotalRate rPlus (feedbackSlope lam k) ≤ -lam
      else
        lam ≤ sourceTotalRate rMinus (feedbackSlope lam k) -
          targetTotalRate rPlus (feedbackSlope lam k)) := by
  split_ifs with hpos
  · exact A1_drift_positive hlam0 hlam hreg hpos
  · exact A1_drift_negative hlam0 hlam hreg (lt_of_le_of_ne (le_of_not_gt hpos) hk)

end OTSelector
