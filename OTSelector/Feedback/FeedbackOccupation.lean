import OTSelector.Feedback.MarkedOccupation
import OTSelector.Feedback.RateBounds

/-!
# Cubic occupation for the feedback rates

This file specializes the genuine two-colour Dynkin estimate to the source and target rates from
the feedback construction.  It does not construct those intensities: the final missing I1 step is
to prove that the finite crossing paths have exactly these predictable intensities.
-/

open Set
open scoped NNReal MeasureTheory

namespace OTSelector

/-- Source jump rate evaluated at the left current. -/
noncomputable def feedbackSourceIntensity {Ω : Type*}
    (lam : ℝ) (rMinus : ℝ≥0 → Ω → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => sourceTotalRate (rMinus s ω)
    (feedbackSlope lam
      (CountingProcess.leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ))

/-- Target jump rate evaluated at the left current. -/
noncomputable def feedbackTargetIntensity {Ω : Type*}
    (lam : ℝ) (rPlus : ℝ≥0 → Ω → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => targetTotalRate (rPlus s ω)
    (feedbackSlope lam
      (CountingProcess.leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ))

/-- On the regularity event, the strict-interior clipped feedback rate has cubic inward drift. -/
theorem feedback_clipped_rate_cubic_le
    {lam eta rMinus rPlus : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hreg : CrossingRegularity lam eta rMinus rPlus)
    (R : ℕ) (k : ℤ) (hlo : -(R : ℤ) < k) (hhi : k < (R : ℤ)) :
    clippedGeneratorRate R cubicLyapunov
        (sourceTotalRate rMinus (feedbackSlope lam (k : ℝ)))
        (targetTotalRate rPlus (feedbackSlope lam (k : ℝ))) k ≤
      -(2 * lam) * (k : ℝ) ^ 2 + (6 + 81 / lam) := by
  have hb := sourceTotalRate_bounds (k := (k : ℝ)) hlam0 hlam hreg
  have hd := targetTotalRate_bounds (k := (k : ℝ)) hlam0 hlam hreg
  have h := clippedGeneratorRate_cubicLyapunov_le_local R _ _
    (C := 3) (c := lam) (by norm_num) hlam0 hb.1 hb.2 hd.1 hd.2 k
      (fun hk => by
        have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
        by_cases hkpos : 0 < k
        · have hkposR : (0 : ℝ) < k := by exact_mod_cast hkpos
          simpa [hkpos, hkposR] using
            feedback_rate_inward_drift hlam0 hlam hreg hkR
        · have hkposR : ¬(0 : ℝ) < k := by exact_mod_cast hkpos
          simpa [hkpos, hkposR] using
            feedback_rate_inward_drift hlam0 hlam hreg hkR)
        hlo hhi
  norm_num at h ⊢
  exact h

namespace CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A1's deterministic-time cubic occupation estimate once the actual feedback intensities and
the pointwise regularity window have been proved. -/
theorem feedback_cubic_clipped_occupation_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {rMinus rPlus : ℝ≥0 → Ω → ℝ}
    {lam eta : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus
      (feedbackSourceIntensity lam rMinus K0 Nplus Nminus))
    (hΛminus : HasPredictableIntensity μ ℱ Nminus
      (feedbackTargetIntensity lam rPlus K0 Nplus Nminus))
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω => (K0 ω : ℝ)))
    (hAplus : ∀ t, Integrable (fun ω => integratedIntensity
      (feedbackSourceIntensity lam rMinus K0 Nplus Nminus)
        (fun _ _ => (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable (fun ω => integratedIntensity
      (feedbackTargetIntensity lam rPlus K0 Nplus Nminus)
        (fun _ _ => (1 : ℝ)) t ω) μ)
    (t : ℝ≥0)
    (hObs0 : Integrable
      (clippedObservable R cubicLyapunov K0 Nplus Nminus 0) μ)
    (hOccupation : Integrable
      (clippedQuadraticOccupation K0 Nplus Nminus t) μ)
    (hplusTime : ∀ ω, IntegrableOn
      (fun s => clippedUpwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) *
          feedbackSourceIntensity lam rMinus K0 Nplus Nminus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hminusTime : ∀ ω, IntegrableOn
      (fun s => clippedDownwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) *
          feedbackTargetIntensity lam rPlus K0 Nplus Nminus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hOccupationTime : ∀ ω, IntegrableOn
      (fun s => (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hRegular : ∀ ω s, s ∈ Ioc (0 : ℝ≥0) t →
      CrossingRegularity lam eta (rMinus s ω) (rPlus s ω))
    (hInterior : ∀ ω s, s ∈ Ioc (0 : ℝ≥0) t →
      -(R : ℤ) < leftCurrentOfCounts K0 Nplus Nminus s ω ∧
        leftCurrentOfCounts K0 Nplus Nminus s ω < (R : ℤ)) :
    ∫ ω, clippedQuadraticOccupation K0 Nplus Nminus t ω ∂μ ≤
      ((∫ ω, clippedObservable R cubicLyapunov K0 Nplus Nminus 0 ω ∂μ) +
        (6 + 81 / lam) * (t : ℝ)) / (2 * lam) := by
  have h := cubic_clipped_occupation_bound_of_rate_drift
    (C := 3) hplus hminus hNo hΛplus hΛminus hK0 hAplus hAminus
      hlam0 t hObs0 hOccupation hplusTime hminusTime hOccupationTime (by
        intro ω s hs
        have hdrift := feedback_clipped_rate_cubic_le hlam0 hlam
          (hRegular ω s hs) R (leftCurrentOfCounts K0 Nplus Nminus s ω)
            (hInterior ω s hs).1 (hInterior ω s hs).2
        simp only [feedbackSourceIntensity, feedbackTargetIntensity]
        norm_num at hdrift ⊢
        exact hdrift)
  norm_num at h ⊢
  exact h

end CountingProcess

end OTSelector
