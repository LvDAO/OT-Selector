import OTSelector.Feedback.LyapunovCutoff
import OTSelector.Probability.CountingProcess.MarkedChainRule

/-!
# Pathwise chain rule for a clipped two-colour current

This file only composes the deterministic clipping algebra with the pathwise chain rule for two
simple counting processes.  The no-simultaneous-jumps and simple-process hypotheses remain explicit;
no martingale or predictability conclusion is asserted here.
-/

open scoped BigOperators NNReal

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The clipped observable obtained by evaluating `f` at the clipped counting current. -/
noncomputable def clippedObservable (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => f (integerClip R (currentOfCounts K0 Nplus Nminus t ω))

@[simp]
theorem clippedObservable_zero
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (R : ℕ) (f : ℤ → ℝ) (ω : Ω) :
    clippedObservable R f K0 Nplus Nminus 0 ω = f (integerClip R (K0 ω)) := by
  simp [clippedObservable, currentOfCounts_zero hplus hminus]

/-! ## Exact pathwise clipped chain rule -/

/-- Exact pathwise chain rule for the clipped two-colour current. -/
theorem clippedObservable_chain_rule
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    {T : ℝ≥0} (hNo : NoSimultaneousJumpsOn Nplus Nminus T)
    (R : ℕ) (f : ℤ → ℝ) (ω : Ω) :
    clippedObservable R f K0 Nplus Nminus T ω -
        clippedObservable R f K0 Nplus Nminus 0 ω =
      countingIntegral Nplus
          (fun s ω' => clippedUpwardIncrement R f
            (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω +
        countingIntegral Nminus
          (fun s ω' => clippedDownwardIncrement R f
            (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω := by
  simpa [clippedObservable, clippedUpwardIncrement, clippedDownwardIncrement,
    currentOfCounts_zero hplus hminus] using
    (currentOfCounts_chain_rule hplus hminus hNo
      (fun k : ℤ => f (integerClip R k)) ω)

/-! ## Algebraic subtraction of the two compensators -/

/-- The clipped observable increment minus its two integrated intensities is the sum of the
corresponding compensated counting integrals. -/
theorem clippedObservable_sub_integratedIntensities_eq_compensated_sum
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    {T : ℝ≥0} (hNo : NoSimultaneousJumpsOn Nplus Nminus T)
    (R : ℕ) (f : ℤ → ℝ)
    (Λplus Λminus : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    clippedObservable R f K0 Nplus Nminus T ω -
        clippedObservable R f K0 Nplus Nminus 0 ω -
        (integratedIntensity Λplus
            (fun s ω' => clippedUpwardIncrement R f
              (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω +
          integratedIntensity Λminus
            (fun s ω' => clippedDownwardIncrement R f
              (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω) =
      compensatedIntegral Nplus Λplus
          (fun s ω' => clippedUpwardIncrement R f
            (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω +
        compensatedIntegral Nminus Λminus
          (fun s ω' => clippedDownwardIncrement R f
            (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω := by
  rw [clippedObservable_chain_rule hplus hminus hNo R f ω]
  simp only [compensatedIntegral]
  ring

end OTSelector.CountingProcess
