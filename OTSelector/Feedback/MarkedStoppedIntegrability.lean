import OTSelector.Feedback.MarkedStoppedOccupation

/-!
# Integrability of finite stopped-current occupations

The stopped Dynkin estimate is stated for a general counting current, so it keeps the
integrability of the quadratic occupation explicit.  Finite feedback paths have a deterministic
current bound.  This file converts that bound, together with predictability, into the required
sample measurability and integrability without adding a probabilistic hypothesis.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A predictable stopped quadratic occupation is strongly measurable in the sample variable. -/
theorem throughStopClippedQuadraticOccupation_stronglyMeasurable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    (t : ℝ≥0) :
    StronglyMeasurable
      (throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t) := by
  let q : ℝ≥0 → Ω → ℝ := fun s ω ↦
    throughStopMask τ s ω * (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2
  have hleft : IsStronglyPredictable ℱ
      (fun s ω ↦ (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ)) :=
    leftCurrentOfCounts_cast_predictable hplus hminus hK0
  have hqPred : IsStronglyPredictable ℱ q := by
    exact hMask.1.mul (hleft.pow 2)
  have hq : StronglyMeasurable (Function.uncurry q) :=
    hqPred.mono (predictable_le_ambient ℱ)
  let g : ℝ≥0 × Ω → ℝ :=
    (Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω)).indicator (Function.uncurry q)
  have hg : StronglyMeasurable g := by
    exact hq.indicator (measurableSet_Ioc.prod MeasurableSet.univ)
  let htimeSFinite : SFinite timeMeasure := by
    unfold timeMeasure
    infer_instance
  have hint : StronglyMeasurable (fun ω ↦ ∫ s, g (s, ω) ∂timeMeasure) := by
    exact @StronglyMeasurable.integral_prod_left'
      ℝ≥0 Ω ℝ (inferInstance : MeasurableSpace ℝ≥0)
      (inferInstance : MeasurableSpace Ω) timeMeasure _ _ htimeSFinite g hg
  have heq : (fun ω ↦ ∫ s, g (s, ω) ∂timeMeasure) =
      throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t := by
    funext ω
    rw [throughStopClippedQuadraticOccupation,
      ← integral_indicator measurableSet_Ioc]
    congr 1
    funext s
    simp only [g, q, Set.indicator, mem_prod, mem_Ioc, mem_univ, and_true,
      Function.uncurry_apply_pair]
  rw [← heq]
  exact hint

omit [MeasurableSpace Ω] in
/-- A deterministic bound on the left current gives the corresponding pathwise bound on the
stopped quadratic occupation. -/
theorem norm_throughStopClippedQuadraticOccupation_le
    (τ : Ω → WithTop ℝ≥0) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hCurrent : ∀ s ω,
      |(leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ)| ≤ K)
    (t : ℝ≥0) (ω : Ω) :
    ‖throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t ω‖ ≤
      K ^ 2 * (t : ℝ) := by
  let q : ℝ≥0 → ℝ := fun s ↦
    throughStopMask τ s ω * (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2
  have hqBound : ∀ s, ‖q s‖ ≤ K ^ 2 := by
    intro s
    have hfactor := mul_nonneg
      (sub_nonneg.mpr (hCurrent s ω))
      (add_nonneg hK (abs_nonneg (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ)))
    have hsquare :
        (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 ≤ K ^ 2 := by
      nlinarith [sq_abs (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ)]
    by_cases hs : (s : WithTop ℝ≥0) ≤ τ ω
    · simp only [q, throughStopMask, ite_eq_left hs, one_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact hsquare
    · simp only [q, throughStopMask, ite_eq_right hs, zero_mul, norm_zero]
      exact sq_nonneg K
  have hconst : IntegrableOn (fun _ : ℝ≥0 ↦ K ^ 2)
      (Ioc (0 : ℝ≥0) t) timeMeasure :=
    integrableOn_const (timeMeasure_Ioc_lt_top 0 t).ne
  calc
    ‖throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t ω‖
        ≤ ∫ _s in Ioc (0 : ℝ≥0) t, K ^ 2 ∂timeMeasure := by
          apply norm_integral_le_of_norm_le hconst
          exact ae_of_all _ hqBound
    _ = K ^ 2 * (t : ℝ) := by
      rw [integral_timeMeasure_eq_intervalIntegral (fun _ : ℝ≥0 ↦ K ^ 2) 0 t (by simp)]
      simp [mul_comm]

/-- The stopped quadratic integrand is pathwise integrable on every bounded horizon when the
left current has a deterministic bound. -/
theorem throughStopClippedQuadraticOccupation_integrableOn_of_current_bound
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    {K : ℝ} (hK : 0 ≤ K)
    (hCurrent : ∀ s ω,
      |(leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ)| ≤ K)
    (t : ℝ≥0) (ω : Ω) :
    IntegrableOn
      (fun s ↦ throughStopMask τ s ω *
        (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2)
      (Ioc (0 : ℝ≥0) t) timeMeasure := by
  let q : ℝ≥0 → Ω → ℝ := fun s ω' ↦
    throughStopMask τ s ω' *
      (leftCurrentOfCounts K0 Nplus Nminus s ω' : ℝ) ^ 2
  have hleft : IsStronglyPredictable ℱ
      (fun s ω' ↦ (leftCurrentOfCounts K0 Nplus Nminus s ω' : ℝ)) :=
    leftCurrentOfCounts_cast_predictable hplus hminus hK0
  have hqPred : IsStronglyPredictable ℱ q := by
    exact hMask.1.mul (hleft.pow 2)
  have hqAmbient : StronglyMeasurable (Function.uncurry q) :=
    hqPred.mono (predictable_le_ambient ℱ)
  have hqSection : StronglyMeasurable (fun s ↦ q s ω) := by
    exact hqAmbient.comp_measurable (measurable_id.prodMk measurable_const)
  apply Measure.integrableOn_of_bounded (timeMeasure_Ioc_lt_top 0 t).ne
    hqSection.aestronglyMeasurable (M := K ^ 2)
  apply ae_of_all
  intro s
  have hfactor := mul_nonneg
    (sub_nonneg.mpr (hCurrent s ω))
    (add_nonneg hK (abs_nonneg (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ)))
  have hsquare :
      (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 ≤ K ^ 2 := by
    nlinarith [sq_abs (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ)]
  by_cases hs : (s : WithTop ℝ≥0) ≤ τ ω
  · simp only [q, throughStopMask, ite_eq_left hs, one_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hsquare
  · simp only [q, throughStopMask, ite_eq_right hs, zero_mul, norm_zero]
    exact sq_nonneg K

/-- The localized cubic initial observable is automatically integrable on a finite measure.
Clipping, rather than a separate moment assumption on `K0`, supplies the deterministic bound. -/
theorem clippedObservable_cubic_zero_integrable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (R : ℕ) :
    Integrable (clippedObservable R cubicLyapunov K0 Nplus Nminus 0) μ := by
  have hK : StronglyMeasurable (fun ω ↦ (K0 ω : ℝ)) :=
    hK0.mono (ℱ.le 0)
  have hgInt : Measurable
      (fun k : ℤ ↦ cubicLyapunov (integerClip R k)) :=
    measurable_of_countable _
  have hg : Measurable
      (fun x : ℝ ↦ cubicLyapunov (integerClip R (Int.floor x))) :=
    hgInt.comp Int.measurable_floor
  have hObs : StronglyMeasurable
      (clippedObservable R cubicLyapunov K0 Nplus Nminus 0) := by
    have hcomp := (hg.comp hK.measurable).stronglyMeasurable
    convert hcomp using 1
    funext ω
    rw [clippedObservable_zero hplus hminus]
    simp
  refine Integrable.of_bound hObs.aestronglyMeasurable ((R : ℝ) ^ 3) ?_
  filter_upwards with ω
  rw [clippedObservable_zero hplus hminus, Real.norm_eq_abs]
  have hstate := integerClip_mem_cutoffStates R (K0 ω)
  rw [cutoffStates, Finset.mem_Icc] at hstate
  have hkabs : |(integerClip R (K0 ω) : ℝ)| ≤ (R : ℝ) := by
    rw [abs_le]
    constructor
    · exact_mod_cast hstate.1
    · exact_mod_cast hstate.2
  have hcube : cubicLyapunov (integerClip R (K0 ω)) ≤ (R : ℝ) ^ 3 := by
    dsimp [cubicLyapunov]
    exact pow_le_pow_left₀ (abs_nonneg _) hkabs 3
  rw [abs_of_nonneg]
  · exact hcube
  · dsimp [cubicLyapunov]
    positivity

/-- On a finite sample law, predictability and a uniform current bound automatically close the
sample-integrability side condition of the stopped occupation theorem. -/
theorem throughStopClippedQuadraticOccupation_integrable_of_current_bound
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    {K : ℝ} (hK : 0 ≤ K)
    (hCurrent : ∀ s ω,
      |(leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ)| ≤ K)
    (t : ℝ≥0) :
    Integrable (throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t) μ := by
  refine Integrable.of_bound
    (throughStopClippedQuadraticOccupation_stronglyMeasurable
      hplus hminus hK0 hMask t).aestronglyMeasurable
    (K ^ 2 * (t : ℝ)) ?_
  filter_upwards with ω
  exact norm_throughStopClippedQuadraticOccupation_le
    τ K0 Nplus Nminus hK hCurrent t ω

/-- End-to-end stopped cubic occupation bound for a uniformly bounded counting current.  All
occupation and localized-initial-observable integrability assumptions are discharged internally. -/
theorem cubic_clipped_throughStop_occupation_bound_of_rate_drift_of_current_bound
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
    {K : ℝ} (hK : 0 ≤ K)
    (hCurrent : ∀ s ω,
      |(leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ)| ≤ K)
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (t : ℝ≥0)
    (hDrift : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < τ ω →
      clippedGeneratorRate R cubicLyapunov (Λplus s ω) (Λminus s ω)
          (leftCurrentOfCounts K0 Nplus Nminus s ω) ≤
        -(2 * c) * (leftCurrentOfCounts K0 Nplus Nminus s ω : ℝ) ^ 2 +
          (2 * C + 9 * C ^ 2 / c)) :
    ∫ ω, throughStopClippedQuadraticOccupation τ K0 Nplus Nminus t ω ∂μ ≤
      ((∫ ω, clippedObservable R cubicLyapunov K0 Nplus Nminus 0 ω ∂μ) +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) / (2 * c) := by
  apply cubic_clipped_throughStop_occupation_bound_of_rate_drift
    hplus hminus hNo hΛplus hΛminus hK0 hMask hAplus hAminus hC hc t
  · exact clippedObservable_cubic_zero_integrable hplus hminus hK0 R
  · exact throughStopClippedQuadraticOccupation_integrable_of_current_bound
      hplus hminus hK0 hMask hK hCurrent t
  · exact fun ω ↦
      throughStopClippedQuadraticOccupation_integrableOn_of_current_bound
        hplus hminus hK0 hMask hK hCurrent t ω
  · exact hDrift

end OTSelector.CountingProcess
