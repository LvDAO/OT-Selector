import OTSelector.Feedback.MarkedOccupation
import OTSelector.Feedback.MarkedStoppedDynkin

/-!
# Cubic occupation through a predictable stopping mask

The masked compensator is the integral of the clipped generator multiplied by `1_{s ≤ τ}`.
A drift estimate strictly before `τ` suffices: the only additional point retained by the mask is
`s = τ`, and every singleton has zero `timeMeasure` measure.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The project time measure has no atoms. -/
private theorem timeMeasure_singleton_zero (a : ℝ≥0) :
    timeMeasure ({a} : Set ℝ≥0) = 0 := by
  rw [timeMeasure, Measure.map_apply measurable_real_toNNReal
    (measurableSet_singleton a)]
  rw [Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton a))]
  have hpre : Real.toNNReal ⁻¹' ({a} : Set ℝ≥0) ∩ Ici (0 : ℝ) =
      ({(a : ℝ)} : Set ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ici]
    constructor
    · rintro ⟨hxa, hx0⟩
      have hxcoe : Real.toNNReal x = Real.toNNReal (a : ℝ) := by
        simpa using hxa
      exact Real.toNNReal_eq_toNNReal_iff hx0 a.2 |>.mp hxcoe
    · intro hxa
      subst x
      exact ⟨Real.toNNReal_coe, a.2⟩
  rw [hpre, Real.volume_singleton]

omit [MeasurableSpace Ω] in
private theorem ae_coe_ne_stopping_coordinate
    (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) (ω : Ω) :
    ∀ᵐ (s : ℝ≥0) ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) T)),
      (s : WithTop ℝ≥0) ≠ τ ω := by
  cases hτ : τ ω with
  | top =>
      filter_upwards with s
      exact WithTop.coe_ne_top
  | coe a =>
      have hne : ∀ᵐ (s : ℝ≥0) ∂timeMeasure, s ≠ a := by
        apply MeasureTheory.ae_iff.mpr
        simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
          timeMeasure_singleton_zero a
      filter_upwards [ae_restrict_of_ae hne] with s hs
      simpa only [hτ, ne_eq, WithTop.coe_eq_coe] using hs

/-- Time integral of the squared left current through the right-closed stop coordinate. -/
noncomputable def throughStopClippedQuadraticOccupation
    (τ : Ω → WithTop ℝ≥0) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Ioc (0 : ℝ≥0) t,
    throughStopMask τ s ω *
      (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 ∂timeMeasure

omit [MeasurableSpace Ω] in
/-- The two masked marked compensators combine into the masked clipped-generator rate. -/
theorem throughStopClippedGeneratorCompensator_eq_integral_rate
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω)
    (hplusInt : IntegrableOn
      (fun s ↦ throughStopMask τ s ω * clippedUpwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λplus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hminusInt : IntegrableOn
      (fun s ↦ throughStopMask τ s ω * clippedDownwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λminus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure) :
    throughStopClippedGeneratorCompensator τ R f K0 Nplus Nminus
        Λplus Λminus t ω =
      ∫ s in Ioc (0 : ℝ≥0) t,
        throughStopMask τ s ω *
          clippedGeneratorRate R f (Λplus s ω) (Λminus s ω)
            (leftCurrentOfCounts K0 Nplus Nminus s ω) ∂timeMeasure := by
  rw [throughStopClippedGeneratorCompensator, integratedIntensity, integratedIntensity,
    ← integral_add hplusInt hminusInt]
  congr 1
  funext s
  simp only [clippedGeneratorRate]
  ring

omit [MeasurableSpace Ω] in
/-- A time-a.e. drift estimate strictly before `τ` integrates to a pathwise masked compensator
bound.  The endpoint `s = τ` is removed by atomlessness of `timeMeasure`. -/
theorem throughStopClippedGeneratorCompensator_le_of_rate_drift_ae
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (t : ℝ≥0) (ω : Ω)
    (hplusInt : IntegrableOn
      (fun s ↦ throughStopMask τ s ω * clippedUpwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λplus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hminusInt : IntegrableOn
      (fun s ↦ throughStopMask τ s ω * clippedDownwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λminus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hOccupationInt : IntegrableOn
      (fun s ↦ throughStopMask τ s ω *
        (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hDrift : ∀ᵐ (s : ℝ≥0) ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) t)),
      (s : WithTop ℝ≥0) < τ ω →
        clippedGeneratorRate R cubicLyapunov (Λplus s ω) (Λminus s ω)
            (leftCurrentOfCounts K0 Nplus Nminus s ω) ≤
          -(2 * c) * (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 +
            (2 * C + 9 * C ^ 2 / c)) :
    throughStopClippedGeneratorCompensator τ R cubicLyapunov K0 Nplus Nminus
        Λplus Λminus t ω ≤
      -(2 * c) * throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t ω +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
  let M : ℝ≥0 → ℝ := fun s ↦ throughStopMask τ s ω
  let q : ℝ≥0 → ℝ := fun s ↦
    (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2
  let rate : ℝ≥0 → ℝ := fun s ↦
    clippedGeneratorRate R cubicLyapunov (Λplus s ω) (Λminus s ω)
      (leftCurrentOfCounts K0 Nplus Nminus s ω)
  let β : ℝ := 2 * C + 9 * C ^ 2 / c
  have hβ : 0 ≤ β := by
    dsimp [β]
    positivity
  have hrateInt : IntegrableOn (fun s ↦ M s * rate s)
      (Ioc (0 : ℝ≥0) t) timeMeasure := by
    have hfun : (fun s ↦ M s * rate s) =
        (fun s ↦ throughStopMask τ s ω * clippedUpwardIncrement R cubicLyapunov
            (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λplus s ω) +
          (fun s ↦ throughStopMask τ s ω * clippedDownwardIncrement R cubicLyapunov
            (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λminus s ω) := by
      funext s
      simp only [M, rate, clippedGeneratorRate, Pi.add_apply]
      ring
    rw [hfun]
    exact hplusInt.add hminusInt
  have hdomInt : IntegrableOn (fun s ↦ -(2 * c) * (M s * q s) + β)
      (Ioc (0 : ℝ≥0) t) timeMeasure :=
    (hOccupationInt.const_mul _).add
      (integrableOn_const (timeMeasure_Ioc_lt_top 0 t).ne)
  have hendpoint := ae_coe_ne_stopping_coordinate τ t ω
  have hpoint : ∀ᵐ (s : ℝ≥0) ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) t)),
      M s * rate s ≤ -(2 * c) * (M s * q s) + β := by
    filter_upwards [hDrift, hendpoint] with s hsdrift hsne
    by_cases hsle : (s : WithTop ℝ≥0) ≤ τ ω
    · have hslt : (s : WithTop ℝ≥0) < τ ω := lt_of_le_of_ne hsle hsne
      have hdrift := hsdrift hslt
      simpa only [M, q, rate, throughStopMask, ite_eq_left hsle, one_mul] using hdrift
    · simp only [M, throughStopMask, ite_eq_right hsle, zero_mul]
      simpa using hβ
  have hmono :
      (∫ s in Ioc (0 : ℝ≥0) t, M s * rate s ∂timeMeasure) ≤
        ∫ s in Ioc (0 : ℝ≥0) t,
          (-(2 * c) * (M s * q s) + β) ∂timeMeasure :=
    integral_mono_ae hrateInt hdomInt hpoint
  have hcomp := throughStopClippedGeneratorCompensator_eq_integral_rate
    τ R cubicLyapunov K0 Nplus Nminus Λplus Λminus t ω hplusInt hminusInt
  have hconst :
      (∫ _s in Ioc (0 : ℝ≥0) t, β ∂timeMeasure) = β * (t : ℝ) := by
    rw [integral_timeMeasure_eq_intervalIntegral (fun _ : ℝ≥0 ↦ β) 0 t (by simp)]
    simp [mul_comm]
  rw [← hcomp] at hmono
  change throughStopClippedGeneratorCompensator τ R cubicLyapunov K0 Nplus Nminus
      Λplus Λminus t ω ≤ _
  calc
    throughStopClippedGeneratorCompensator τ R cubicLyapunov K0 Nplus Nminus
        Λplus Λminus t ω
        ≤ ∫ s in Ioc (0 : ℝ≥0) t,
            (-(2 * c) * (M s * q s) + β) ∂timeMeasure := hmono
    _ = -(2 * c) * (∫ s in Ioc (0 : ℝ≥0) t, M s * q s ∂timeMeasure) +
          β * (t : ℝ) := by
      rw [integral_add (hOccupationInt.const_mul _)
        (integrableOn_const (timeMeasure_Ioc_lt_top 0 t).ne), integral_const_mul, hconst]
    _ = -(2 * c) * throughStopClippedQuadraticOccupation
          τ K0 Nplus Nminus t ω + (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
      rfl

omit [MeasurableSpace Ω] in
/-- Pointwise strict-pre-exit drift is a convenient corollary of the a.e. pathwise theorem. -/
theorem throughStopClippedGeneratorCompensator_le_of_rate_drift
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (t : ℝ≥0) (ω : Ω)
    (hplusInt : IntegrableOn
      (fun s ↦ throughStopMask τ s ω * clippedUpwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λplus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hminusInt : IntegrableOn
      (fun s ↦ throughStopMask τ s ω * clippedDownwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λminus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hOccupationInt : IntegrableOn
      (fun s ↦ throughStopMask τ s ω *
        (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hDrift : ∀ (s : ℝ≥0), (s : WithTop ℝ≥0) < τ ω →
      clippedGeneratorRate R cubicLyapunov (Λplus s ω) (Λminus s ω)
          (leftCurrentOfCounts K0 Nplus Nminus s ω) ≤
        -(2 * c) * (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 +
          (2 * C + 9 * C ^ 2 / c)) :
    throughStopClippedGeneratorCompensator τ R cubicLyapunov K0 Nplus Nminus
        Λplus Λminus t ω ≤
      -(2 * c) * throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t ω +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
  apply throughStopClippedGeneratorCompensator_le_of_rate_drift_ae
    τ R K0 Nplus Nminus Λplus Λminus hC hc t ω
    hplusInt hminusInt hOccupationInt
  filter_upwards with s
  exact hDrift s

/-- End-to-end cubic occupation estimate through an arbitrary predictable right-closed stopping
mask.  The drift input is only sample-a.e. and, for each such sample, time-a.e. strictly before
the stopping coordinate. -/
theorem cubic_clipped_throughStop_occupation_bound_of_rate_drift_ae
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    (hAplus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λplus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λminus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (t : ℝ≥0)
    (hObs0 : Integrable
      (clippedObservable R cubicLyapunov K0 Nplus Nminus 0) μ)
    (hOccupation : Integrable
      (throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t) μ)
    (hOccupationTime : ∀ ω, IntegrableOn
      (fun s ↦ throughStopMask τ s ω *
        (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hDrift : ∀ᵐ ω ∂μ, ∀ᵐ (s : ℝ≥0)
      ∂(timeMeasure.restrict (Ioc (0 : ℝ≥0) t)),
        (s : WithTop ℝ≥0) < τ ω →
          clippedGeneratorRate R cubicLyapunov (Λplus s ω) (Λminus s ω)
              (leftCurrentOfCounts K0 Nplus Nminus s ω) ≤
            -(2 * c) * (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 +
              (2 * C + 9 * C ^ 2 / c)) :
    ∫ ω, throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t ω ∂μ ≤
      ((∫ ω, clippedObservable R cubicLyapunov K0 Nplus Nminus 0 ω ∂μ) +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) / (2 * c) := by
  let Hplus : ℝ≥0 → Ω → ℝ := fun s ω ↦ clippedUpwardIncrement R cubicLyapunov
    (leftCurrentOfCounts K0 Nplus Nminus s ω)
  let Hminus : ℝ≥0 → Ω → ℝ := fun s ω ↦ clippedDownwardIncrement R cubicLyapunov
    (leftCurrentOfCounts K0 Nplus Nminus s ω)
  have hHplus : IsBoundedPredictable ℱ Hplus := by
    simpa only [Hplus] using
      clippedUpwardIncrement_boundedPredictable hplus hminus hK0 R cubicLyapunov
  have hHminus : IsBoundedPredictable ℱ Hminus := by
    simpa only [Hminus] using
      clippedDownwardIncrement_boundedPredictable hplus hminus hK0 R cubicLyapunov
  have hMHplus : IsBoundedPredictable ℱ
      (fun s ω ↦ throughStopMask τ s ω * Hplus s ω) :=
    hMask.isBoundedPredictable.mul_process hHplus
  have hMHminus : IsBoundedPredictable ℱ
      (fun s ω ↦ throughStopMask τ s ω * Hminus s ω) :=
    hMask.isBoundedPredictable.mul_process hHminus
  have hplusTime : ∀ ω, IntegrableOn
      (fun s ↦ throughStopMask τ s ω * clippedUpwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λplus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure := by
    intro ω
    simpa only [Hplus] using hMHplus.integrableOn_mul_intensity hΛplus t ω
  have hminusTime : ∀ ω, IntegrableOn
      (fun s ↦ throughStopMask τ s ω * clippedDownwardIncrement R cubicLyapunov
        (leftCurrentOfCounts K0 Nplus Nminus s ω) * Λminus s ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure := by
    intro ω
    simpa only [Hminus] using hMHminus.integrableOn_mul_intensity hΛminus t ω
  have hCompInt : Integrable
      (throughStopClippedGeneratorCompensator τ R cubicLyapunov K0 Nplus Nminus
        Λplus Λminus t) μ := by
    apply throughStopClippedGeneratorCompensator_integrable hΛplus hΛminus
      (by simpa only [Hplus] using hMHplus)
      (by simpa only [Hminus] using hMHminus) hAplus hAminus
  have hM := throughStopClippedDynkinProcess_martingale hplus hminus hNo
    hΛplus hΛminus hK0 hMask R cubicLyapunov hAplus hAminus
  have hObsT := stoppedClippedObservable_integrable_of_martingale hM t hObs0 hCompInt
  have hDynkin := integral_stoppedClippedObservable_eq_add_throughStopCompensator
    hM t hObsT hObs0 hCompInt
  have hCompBound : ∀ᵐ ω ∂μ,
      throughStopClippedGeneratorCompensator τ R cubicLyapunov K0 Nplus Nminus
          Λplus Λminus t ω ≤
        -(2 * c) * throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t ω +
          (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
    filter_upwards [hDrift] with ω hω
    exact throughStopClippedGeneratorCompensator_le_of_rate_drift_ae
      τ R K0 Nplus Nminus Λplus Λminus hC hc t ω
        (hplusTime ω) (hminusTime ω) (hOccupationTime ω) hω
  have hrightInt : Integrable
      (fun ω ↦ -(2 * c) * throughStopClippedQuadraticOccupation
          τ K0 Nplus Nminus t ω +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) μ :=
    (hOccupation.const_mul _).add (integrable_const _)
  have hcompIntegral :
      (∫ ω, throughStopClippedGeneratorCompensator τ R cubicLyapunov K0
          Nplus Nminus Λplus Λminus t ω ∂μ) ≤
        ∫ ω, (-(2 * c) * throughStopClippedQuadraticOccupation
          τ K0 Nplus Nminus t ω +
            (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) ∂μ :=
    integral_mono_ae hCompInt hrightInt hCompBound
  have hrightEq :
      (∫ ω, (-(2 * c) * throughStopClippedQuadraticOccupation
          τ K0 Nplus Nminus t ω +
            (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) ∂μ) =
        -(2 * c) *
            (∫ ω, throughStopClippedQuadraticOccupation
              τ K0 Nplus Nminus t ω ∂μ) +
          (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
    rw [integral_add (hOccupation.const_mul _) (integrable_const _), integral_const_mul,
      integral_const]
    simp [smul_eq_mul]
  rw [hrightEq] at hcompIntegral
  have hterminal :
      0 ≤ ∫ ω, MeasureTheory.stoppedProcess
        (clippedObservable R cubicLyapunov K0 Nplus Nminus) τ t ω ∂μ := by
    exact integral_nonneg fun ω ↦ by
      simp only [MeasureTheory.stoppedProcess, clippedObservable, cubicLyapunov]
      positivity
  have hcore :
      (2 * c) *
          (∫ ω, throughStopClippedQuadraticOccupation
            τ K0 Nplus Nminus t ω ∂μ) ≤
        (∫ ω, clippedObservable R cubicLyapunov K0 Nplus Nminus 0 ω ∂μ) +
          (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
    nlinarith [hterminal, hDynkin, hcompIntegral]
  apply (le_div_iff₀ (by positivity : 0 < 2 * c)).2
  simpa [mul_comm] using hcore

/-- Pointwise-in-sample, pointwise-in-time drift specialization of the a.e. theorem. -/
theorem cubic_clipped_throughStop_occupation_bound_of_rate_drift
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    (hAplus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λplus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λminus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (t : ℝ≥0)
    (hObs0 : Integrable
      (clippedObservable R cubicLyapunov K0 Nplus Nminus 0) μ)
    (hOccupation : Integrable
      (throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t) μ)
    (hOccupationTime : ∀ ω, IntegrableOn
      (fun s ↦ throughStopMask τ s ω *
        (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hDrift : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < τ ω →
      clippedGeneratorRate R cubicLyapunov (Λplus s ω) (Λminus s ω)
          (leftCurrentOfCounts K0 Nplus Nminus s ω) ≤
        -(2 * c) * (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 +
          (2 * C + 9 * C ^ 2 / c)) :
    ∫ ω, throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t ω ∂μ ≤
      ((∫ ω, clippedObservable R cubicLyapunov K0 Nplus Nminus 0 ω ∂μ) +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) / (2 * c) := by
  apply cubic_clipped_throughStop_occupation_bound_of_rate_drift_ae
    hplus hminus hNo hΛplus hΛminus hK0 hMask hAplus hAminus hC hc t
      hObs0 hOccupation hOccupationTime
  filter_upwards with ω
  filter_upwards with s
  exact hDrift ω s

end OTSelector.CountingProcess
