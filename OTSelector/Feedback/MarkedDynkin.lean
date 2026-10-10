import OTSelector.Feedback.ClippedChainRule
import OTSelector.Feedback.MarkedPredictable
import OTSelector.Probability.CountingProcess.BoundedGridStopping

/-!
# Stopped Dynkin formula for a two-colour counting current

The observable is clipped in the integer state variable.  Its two one-step increments are then
bounded predictable transforms, so the two compensator martingales can be added.  The pathwise
chain rule identifies their sum with the Dynkin residual; finite-grid optional sampling supplies
the stopped formula.

This file does not construct the feedback crossing intensities.  It proves the process theorem
once those two genuine intensities and the predictable-transform hypotheses are available.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The compensated Dynkin residual of the clipped current observable. -/
noncomputable def clippedDynkinProcess
    (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω =>
    clippedObservable R f K0 Nplus Nminus t ω -
      clippedObservable R f K0 Nplus Nminus 0 ω -
      (integratedIntensity Λplus
          (fun s ω' => clippedUpwardIncrement R f
            (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω +
        integratedIntensity Λminus
          (fun s ω' => clippedDownwardIncrement R f
            (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω)

omit [MeasurableSpace Ω] in
@[simp]
theorem clippedDynkinProcess_zero
    (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus 0 ω = 0 := by
  simp [clippedDynkinProcess, integratedIntensity]

/-- The clipped Dynkin residual is pathwise the sum of the two compensated counting integrals. -/
theorem clippedDynkinProcess_eq_compensated_sum
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (R : ℕ) (f : ℤ → ℝ) (Λplus Λminus : ℝ≥0 → Ω → ℝ) :
    clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus =
      fun t ω =>
        compensatedIntegral Nplus Λplus
            (fun s ω' => clippedUpwardIncrement R f
              (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω +
          compensatedIntegral Nminus Λminus
            (fun s ω' => clippedDownwardIncrement R f
              (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω := by
  funext t ω
  exact clippedObservable_sub_integratedIntensities_eq_compensated_sum
    hplus hminus (hNo t) R f Λplus Λminus ω

/-- The clipped Dynkin residual is a true martingale for two genuine predictable intensities. -/
theorem clippedDynkinProcess_martingale
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (R : ℕ) (f : ℤ → ℝ)
    (hHplus : IsBoundedPredictable ℱ
      (fun s ω => clippedUpwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω)))
    (hHminus : IsBoundedPredictable ℱ
      (fun s ω => clippedDownwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω)))
    (hAplus : ∀ t, Integrable
      (fun ω => integratedIntensity Λplus (fun _ _ => (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω => integratedIntensity Λminus (fun _ _ => (1 : ℝ)) t ω) μ) :
    Martingale (clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus) ℱ μ := by
  rw [clippedDynkinProcess_eq_compensated_sum hplus hminus hNo R f Λplus Λminus]
  change Martingale
    (compensatedIntegral Nplus Λplus
        (fun s ω => clippedUpwardIncrement R f
          (leftCurrentOfCounts K0 Nplus Nminus s ω)) +
      compensatedIntegral Nminus Λminus
        (fun s ω => clippedDownwardIncrement R f
          (leftCurrentOfCounts K0 Nplus Nminus s ω))) ℱ μ
  exact (hΛplus.martingale_of_boundedPredictable hHplus hAplus).add
    (hΛminus.martingale_of_boundedPredictable hHminus hAminus)

/-- The clipped Dynkin residual is a true martingale when the initial current is measurable at
time zero; the bounded-predictable increment hypotheses are derived from that measurability. -/
theorem clippedDynkinProcess_martingale_of_initial_measurable
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω => (K0 ω : ℝ)))
    (R : ℕ) (f : ℤ → ℝ)
    (hAplus : ∀ t, Integrable
      (fun ω => integratedIntensity Λplus (fun _ _ => (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω => integratedIntensity Λminus (fun _ _ => (1 : ℝ)) t ω) μ) :
    Martingale (clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus) ℱ μ := by
  exact clippedDynkinProcess_martingale hplus hminus hNo hΛplus hΛminus R f
    (clippedUpwardIncrement_boundedPredictable hplus hminus hK0 R f)
    (clippedDownwardIncrement_boundedPredictable hplus hminus hK0 R f)
    hAplus hAminus

/-- Deterministic-time conditional Dynkin identity for the clipped residual martingale. -/
theorem clippedDynkinProcess_condExp_ae_eq
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (R : ℕ) (f : ℤ → ℝ)
    (hHplus : IsBoundedPredictable ℱ
      (fun s ω => clippedUpwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω)))
    (hHminus : IsBoundedPredictable ℱ
      (fun s ω => clippedDownwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω)))
    (hAplus : ∀ t, Integrable
      (fun ω => integratedIntensity Λplus (fun _ _ => (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω => integratedIntensity Λminus (fun _ _ => (1 : ℝ)) t ω) μ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    μ[clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus t | ℱ s] =ᵐ[μ]
      clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus s := by
  exact (clippedDynkinProcess_martingale hplus hminus hNo hΛplus hΛminus R f
    hHplus hHminus hAplus hAminus).condExp_ae_eq hst

/-- Deterministic-time conditional Dynkin identity when the initial current is measurable at time
zero; the bounded-predictable increment hypotheses are derived internally. -/
theorem clippedDynkinProcess_condExp_ae_eq_of_initial_measurable
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω => (K0 ω : ℝ)))
    (R : ℕ) (f : ℤ → ℝ)
    (hAplus : ∀ t, Integrable
      (fun ω => integratedIntensity Λplus (fun _ _ => (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω => integratedIntensity Λminus (fun _ _ => (1 : ℝ)) t ω) μ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    μ[clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus t | ℱ s] =ᵐ[μ]
      clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus s := by
  exact clippedDynkinProcess_condExp_ae_eq hplus hminus hNo hΛplus hΛminus R f
    (clippedUpwardIncrement_boundedPredictable hplus hminus hK0 R f)
    (clippedDownwardIncrement_boundedPredictable hplus hminus hK0 R f)
    hAplus hAminus hst

/-- Finite-grid optional sampling for the genuine clipped Dynkin martingale. -/
theorem clippedDynkinProcess_optionalSampling_finiteRange
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (R : ℕ) (f : ℤ → ℝ)
    (hHplus : IsBoundedPredictable ℱ
      (fun s ω => clippedUpwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω)))
    (hHminus : IsBoundedPredictable ℱ
      (fun s ω => clippedDownwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω)))
    (hAplus : ∀ t, Integrable
      (fun ω => integratedIntensity Λplus (fun _ _ => (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω => integratedIntensity Λminus (fun _ _ => (1 : ℝ)) t ω) μ)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    stoppedValue (clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus) σ =ᵐ[μ]
      μ[stoppedValue (clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus) τ |
        hσ.measurableSpace] :=
  (clippedDynkinProcess_martingale hplus hminus hNo hΛplus hΛminus R f
    hHplus hHminus hAplus hAminus)
    |>.stoppedValue_ae_eq_condExp_of_le_of_countable_range
      hτ hσ hστ hτ_le hτ_range.countable hσ_range.countable

/-- Finite-range optional sampling for the clipped Dynkin residual when the initial current is
measurable at time zero; the bounded-predictable increment hypotheses are derived internally. -/
theorem clippedDynkinProcess_optionalSampling_finiteRange_of_initial_measurable
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω => (K0 ω : ℝ)))
    (R : ℕ) (f : ℤ → ℝ)
    (hAplus : ∀ t, Integrable
      (fun ω => integratedIntensity Λplus (fun _ _ => (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω => integratedIntensity Λminus (fun _ _ => (1 : ℝ)) t ω) μ)
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hστ : σ ≤ τ) {T : ℝ≥0} (hτ_le : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    stoppedValue (clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus) σ =ᵐ[μ]
      μ[stoppedValue (clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus) τ |
        hσ.measurableSpace] := by
  exact clippedDynkinProcess_optionalSampling_finiteRange hplus hminus hNo hΛplus hΛminus R f
    (clippedUpwardIncrement_boundedPredictable hplus hminus hK0 R f)
    (clippedDownwardIncrement_boundedPredictable hplus hminus hK0 R f)
    hAplus hAminus hσ hτ hστ hτ_le hσ_range hτ_range

end OTSelector.CountingProcess
