import OTSelector.Feedback.ClippedGenerator
import OTSelector.Feedback.MarkedGenerator

/-!
# Cubic occupation from the marked generator

This module identifies the sum of the two counting compensators with the time integral of the
clipped birth--death generator.  It then integrates a pointwise generator drift estimate.  The
probabilistic Dynkin step is already supplied by `MarkedGenerator.lean`; the only later input is
the actual feedback rate inequality.
-/

open Set
open scoped NNReal MeasureTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Time integral of the squared left current. -/
noncomputable def clippedQuadraticOccupation
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Ioc (0 : ℝ≥0) t,
    (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 ∂timeMeasure

omit [MeasurableSpace Ω] in
/-- The two marked compensators combine into the time integral of the clipped generator rate. -/
theorem clippedGeneratorCompensator_eq_integral_rate
    (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω)
    (hplusInt : IntegrableOn
      (fun s => clippedUpwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λplus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hminusInt : IntegrableOn
      (fun s => clippedDownwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λminus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure) :
    clippedGeneratorCompensator R f K0 Nplus Nminus Λplus Λminus t ω =
      ∫ s in Ioc (0 : ℝ≥0) t,
        clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
          (leftCurrentOfCounts K0 Nplus Nminus s ω) ∂timeMeasure := by
  rw [clippedGeneratorCompensator, integratedIntensity, integratedIntensity,
    ← integral_add hplusInt hminusInt]
  congr 1
  funext s
  simp only [clippedGeneratorRate]
  ring

omit [MeasurableSpace Ω] in
/-- A pointwise clipped-generator drift integrates to a pathwise compensator bound. -/
theorem clippedGeneratorCompensator_le_of_rate_drift
    (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ)
    {C c : ℝ} (t : ℝ≥0) (ω : Ω)
    (hplusInt : IntegrableOn
      (fun s => clippedUpwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λplus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hminusInt : IntegrableOn
      (fun s => clippedDownwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λminus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hOccupationInt : IntegrableOn
      (fun s => (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hDrift : ∀ s ∈ Ioc (0 : ℝ≥0) t,
      clippedGeneratorRate R cubicLyapunov (Λplus s ω) (Λminus s ω)
          (leftCurrentOfCounts K0 Nplus Nminus s ω) ≤
        -(2 * c) * (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 +
          (2 * C + 9 * C ^ 2 / c)) :
    clippedGeneratorCompensator R cubicLyapunov K0 Nplus Nminus
        Λplus Λminus t ω ≤
      -(2 * c) * clippedQuadraticOccupation K0 Nplus Nminus t ω +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
  let q : ℝ≥0 → ℝ := fun s =>
    (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2
  let rate : ℝ≥0 → ℝ := fun s =>
    clippedGeneratorRate R cubicLyapunov (Λplus s ω) (Λminus s ω)
      (leftCurrentOfCounts K0 Nplus Nminus s ω)
  let β : ℝ := 2 * C + 9 * C ^ 2 / c
  have hrateInt : IntegrableOn rate (Ioc (0 : ℝ≥0) t) timeMeasure := by
    have hfun : rate =
        (fun s => clippedUpwardIncrement R cubicLyapunov
            (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λplus s ω) +
          (fun s => clippedDownwardIncrement R cubicLyapunov
            (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λminus s ω) := by
      funext s
      simp [rate, clippedGeneratorRate, mul_comm]
    rw [hfun]
    exact hplusInt.add hminusInt
  have hdomInt : IntegrableOn (fun s => -(2 * c) * q s + β)
      (Ioc (0 : ℝ≥0) t) timeMeasure := by
    exact (hOccupationInt.const_mul _).add
      (integrableOn_const (timeMeasure_Ioc_lt_top 0 t).ne)
  have hmono :
      (∫ s in Ioc (0 : ℝ≥0) t, rate s ∂timeMeasure) ≤
        ∫ s in Ioc (0 : ℝ≥0) t, (-(2 * c) * q s + β) ∂timeMeasure := by
    apply integral_mono_ae hrateInt hdomInt
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hDrift s hs
  have hcomp := clippedGeneratorCompensator_eq_integral_rate R cubicLyapunov K0
    Nplus Nminus Λplus Λminus t ω hplusInt hminusInt
  have hconst :
      (∫ _s in Ioc (0 : ℝ≥0) t, β ∂timeMeasure) = β * (t : ℝ) := by
    rw [integral_timeMeasure_eq_intervalIntegral (fun _ : ℝ≥0 => β) 0 t (by simp)]
    simp [mul_comm]
  rw [← hcomp] at hmono
  change clippedGeneratorCompensator R cubicLyapunov K0 Nplus Nminus
      Λplus Λminus t ω ≤ _
  calc
    clippedGeneratorCompensator R cubicLyapunov K0 Nplus Nminus
        Λplus Λminus t ω
        ≤ ∫ s in Ioc (0 : ℝ≥0) t, (-(2 * c) * q s + β) ∂timeMeasure := hmono
    _ = -(2 * c) * (∫ s in Ioc (0 : ℝ≥0) t, q s ∂timeMeasure) + β * (t : ℝ) := by
      rw [integral_add (hOccupationInt.const_mul _)
        (integrableOn_const (timeMeasure_Ioc_lt_top 0 t).ne), integral_const_mul, hconst]
    _ = -(2 * c) * clippedQuadraticOccupation K0 Nplus Nminus t ω +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
      rfl

/-- End-to-end deterministic-time cubic occupation estimate from two genuine intensities and the
pointwise clipped-rate drift. -/
theorem cubic_clipped_occupation_bound_of_rate_drift
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω => (K0 ω : ℝ)))
    (hAplus : ∀ t, Integrable
      (fun ω => integratedIntensity Λplus (fun _ _ => (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω => integratedIntensity Λminus (fun _ _ => (1 : ℝ)) t ω) μ)
    {C c : ℝ} (hc : 0 < c) (t : ℝ≥0)
    (hObs0 : Integrable
      (clippedObservable R cubicLyapunov K0 Nplus Nminus 0) μ)
    (hOccupation : Integrable
      (clippedQuadraticOccupation K0 Nplus Nminus t) μ)
    (hplusTime : ∀ ω, IntegrableOn
      (fun s => clippedUpwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λplus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hminusTime : ∀ ω, IntegrableOn
      (fun s => clippedDownwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λminus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hOccupationTime : ∀ ω, IntegrableOn
      (fun s => (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hDrift : ∀ ω s, s ∈ Ioc (0 : ℝ≥0) t →
      clippedGeneratorRate R cubicLyapunov (Λplus s ω) (Λminus s ω)
          (leftCurrentOfCounts K0 Nplus Nminus s ω) ≤
        -(2 * c) * (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 +
          (2 * C + 9 * C ^ 2 / c)) :
    ∫ ω, clippedQuadraticOccupation K0 Nplus Nminus t ω ∂μ ≤
      ((∫ ω, clippedObservable R cubicLyapunov K0 Nplus Nminus 0 ω ∂μ) +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) / (2 * c) := by
  apply cubic_clipped_occupation_bound_of_compensator_drift hplus hminus hNo
    hΛplus hΛminus hK0 hAplus hAminus hc
    (clippedQuadraticOccupation K0 Nplus Nminus t) hOccupation t hObs0
  intro ω
  exact clippedGeneratorCompensator_le_of_rate_drift R K0 Nplus Nminus
    Λplus Λminus t ω (hplusTime ω) (hminusTime ω) (hOccupationTime ω)
      (hDrift ω)

end OTSelector.CountingProcess
