import OTSelector.Feedback.MarkedGenerator
import OTSelector.Probability.CountingProcess.OccupationBound
import OTSelector.Probability.CountingProcess.StoppingMasks

/-!
# Marked Dynkin formula through a predictable stopping mask

The right-closed mask `1_{s ≤ τ}` retains a jump occurring at the exit time.  Multiplying the
two clipped jump increments by this mask therefore gives exactly the clipped observable stopped
at `τ`, while keeping the original counting processes and their genuine intensities unchanged.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Bounded-predictable multiplication -/

/-- Every bounded simple predictable process is bounded predictable. -/
theorem IsBoundedSimplePredictable.isBoundedPredictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsBoundedSimplePredictable ℱ H) :
    IsBoundedPredictable ℱ H := by
  obtain ⟨hpred, _, C, hC, hbound⟩ := hH
  exact ⟨hpred, C, hC, hbound⟩

/-- Bounded predictable processes are closed under pointwise multiplication. -/
theorem IsBoundedPredictable.mul_process
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {F G : ℝ≥0 → Ω → ℝ}
    (hF : IsBoundedPredictable ℱ F) (hG : IsBoundedPredictable ℱ G) :
    IsBoundedPredictable ℱ (fun t ω ↦ F t ω * G t ω) := by
  obtain ⟨hFpred, C, hC, hFbound⟩ := hF
  obtain ⟨hGpred, D, hD, hGbound⟩ := hG
  refine ⟨hFpred.mul hGpred, C * D, mul_nonneg hC hD, ?_⟩
  intro t ω
  rw [abs_mul]
  exact mul_le_mul (hFbound t ω) (hGbound t ω) (abs_nonneg _) hC

/-- Multiplying a bounded predictable transform by a genuine intensity is pathwise integrable
on every bounded time interval. -/
theorem IsBoundedPredictable.integrableOn_mul_intensity
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    (hH : IsBoundedPredictable ℱ H)
    (hΛ : HasPredictableIntensity μ ℱ N Λ) (t : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun s ↦ H s ω * Λ s ω) (Ioc (0 : ℝ≥0) t) timeMeasure := by
  obtain ⟨hHpred, C, hC, hHbound⟩ := hH
  let ν : Measure ℝ≥0 := timeMeasure.restrict (Ioc (0 : ℝ≥0) t)
  have hprodPred : StronglyMeasurable[ℱ.predictable]
      (Function.uncurry (fun s ω' ↦ H s ω' * Λ s ω')) := by
    change StronglyMeasurable[ℱ.predictable]
      (Function.uncurry H * Function.uncurry Λ)
    exact hHpred.mul hΛ.predictable
  have hprodAmbient : StronglyMeasurable[Prod.instMeasurableSpace]
      (Function.uncurry (fun s ω' ↦ H s ω' * Λ s ω')) :=
    hprodPred.mono (predictable_le_ambient ℱ)
  have hsection : StronglyMeasurable (fun s ↦ H s ω * Λ s ω) := by
    exact hprodAmbient.comp_measurable (measurable_id.prodMk measurable_const)
  have hdom : Integrable (fun s ↦ C * Λ s ω) ν := by
    dsimp [ν]
    exact (hΛ.integrableOn t ω).const_mul C
  apply Integrable.mono' hdom hsection.aestronglyMeasurable
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΛ.nonneg s ω)]
  exact mul_le_mul_of_nonneg_right (hHbound s ω) (hΛ.nonneg s ω)

/-! ## Pathwise stopping of counting integrals -/

omit [MeasurableSpace Ω] in
/-- The finite horizon cut by `τ`, expressed as an ordinary nonnegative real time. -/
private noncomputable def cutTime (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (T : WithTop ℝ≥0) (τ ω)).untopA

omit [MeasurableSpace Ω] in
private theorem coe_cutTime (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    (cutTime T τ ω : WithTop ℝ≥0) = min (T : WithTop ℝ≥0) (τ ω) := by
  unfold cutTime
  have hne : min (T : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top T)).ne
  rw [WithTop.untopA_eq_untop hne]
  exact WithTop.coe_untop _ hne

omit [MeasurableSpace Ω] in
/-- Masking a counting integral by `1_{s ≤ τ}` is exactly deterministic evaluation at the
pathwise cut time `T ∧ τ`. -/
theorem countingIntegral_mul_throughStopMask
    {N : ℝ≥0 → Ω → ℕ}
    (hmono : ∀ ω, Monotone fun t ↦ N t ω)
    (hrc : ∀ ω t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    countingIntegral N (fun s ω' ↦ throughStopMask τ s ω' * H s ω') T ω =
      countingIntegral N H (cutTime T τ ω) ω := by
  classical
  let u := cutTime T τ ω
  have huT : u ≤ T := by
    apply WithTop.coe_le_coe.mp
    rw [show (u : WithTop ℝ≥0) = min (T : WithTop ℝ≥0) (τ ω) by
      exact coe_cutTime T τ ω]
    exact min_le_left _ _
  have hNuT : N u ω ≤ N T ω := hmono ω huT
  have hfilter :
      (Finset.range (N T ω)).filter
          (fun k ↦ (jumpTime N k ω : WithTop ℝ≥0) ≤ τ ω) =
        Finset.range (N u ω) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hkT, hkτ⟩
      have hjT : jumpTime N k ω ≤ T := jumpTime_le_of_lt hkT
      have hju : jumpTime N k ω ≤ u := by
        apply WithTop.coe_le_coe.mp
        rw [show (u : WithTop ℝ≥0) = min (T : WithTop ℝ≥0) (τ ω) by
          exact coe_cutTime T τ ω]
        exact le_min (WithTop.coe_le_coe.mpr hjT) hkτ
      exact lt_of_jumpTime_le (hmono ω) (hrc ω) ⟨T, hkT⟩ hju
    · intro hku
      have hkT : k < N T ω := lt_of_lt_of_le hku hNuT
      have hju : jumpTime N k ω ≤ u := jumpTime_le_of_lt hku
      refine ⟨hkT, ?_⟩
      have hjmin : (jumpTime N k ω : WithTop ℝ≥0) ≤
          min (T : WithTop ℝ≥0) (τ ω) := by
        rw [← coe_cutTime T τ ω]
        exact WithTop.coe_le_coe.mpr hju
      exact hjmin.trans (min_le_right _ _)
  unfold countingIntegral
  simp only [throughStopMask]
  rw [← hfilter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hstop : (jumpTime N k ω : WithTop ℝ≥0) ≤ τ ω
  · simp only [hstop, ite_true, one_mul]
  · simp only [hstop, ite_false, zero_mul]

omit [MeasurableSpace Ω] in
/-- Functional form of the preceding pathwise identity. -/
theorem countingIntegral_mul_throughStopMask_eq_stoppedProcess
    {N : ℝ≥0 → Ω → ℕ}
    (hmono : ∀ ω, Monotone fun t ↦ N t ω)
    (hrc : ∀ ω t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t)
    (τ : Ω → WithTop ℝ≥0) (H : ℝ≥0 → Ω → ℝ) :
    (fun T ω ↦ countingIntegral N
      (fun s ω' ↦ throughStopMask τ s ω' * H s ω') T ω) =
      MeasureTheory.stoppedProcess (countingIntegral N H) τ := by
  funext T ω
  rw [countingIntegral_mul_throughStopMask hmono hrc]
  rfl

/-! ## The masked clipped Dynkin martingale -/

/-- Sum of the two clipped compensators through the right-closed stopping mask. -/
noncomputable def throughStopClippedGeneratorCompensator
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  integratedIntensity Λplus
      (fun s ω' ↦ throughStopMask τ s ω' * clippedUpwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω +
    integratedIntensity Λminus
      (fun s ω' ↦ throughStopMask τ s ω' * clippedDownwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω

/-- The stopped clipped observable minus its masked generator compensator. -/
noncomputable def throughStopClippedDynkinProcess
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω ↦
    MeasureTheory.stoppedProcess (clippedObservable R f K0 Nplus Nminus) τ t ω -
      clippedObservable R f K0 Nplus Nminus 0 ω -
        throughStopClippedGeneratorCompensator τ R f K0 Nplus Nminus
          Λplus Λminus t ω

omit [MeasurableSpace Ω] in
@[simp]
theorem throughStopClippedDynkinProcess_zero
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    throughStopClippedDynkinProcess τ R f K0 Nplus Nminus Λplus Λminus 0 ω = 0 := by
  simp [throughStopClippedDynkinProcess, throughStopClippedGeneratorCompensator,
    MeasureTheory.stoppedProcess, integratedIntensity]

/-- The masked Dynkin residual is pathwise the sum of the two masked compensated integrals. -/
theorem throughStopClippedDynkinProcess_eq_compensated_sum
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (τ : Ω → WithTop ℝ≥0) (R : ℕ) (f : ℤ → ℝ) (Λplus Λminus : ℝ≥0 → Ω → ℝ) :
    throughStopClippedDynkinProcess τ R f K0 Nplus Nminus Λplus Λminus =
      fun t ω ↦
        compensatedIntegral Nplus Λplus
            (fun s ω' ↦ throughStopMask τ s ω' * clippedUpwardIncrement R f
              (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω +
          compensatedIntegral Nminus Λminus
            (fun s ω' ↦ throughStopMask τ s ω' * clippedDownwardIncrement R f
              (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω := by
  funext t ω
  let u := cutTime t τ ω
  have hchain := clippedObservable_chain_rule (K0 := K0)
    hplus hminus (hNo u) R f ω
  have hplusStop := countingIntegral_mul_throughStopMask
    (fun ω' ↦ hplus.monotone ω') (fun ω' s ↦ hplus.rightContinuous ω' s)
    τ (fun s ω' ↦ clippedUpwardIncrement R f
      (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω
  have hminusStop := countingIntegral_mul_throughStopMask
    (fun ω' ↦ hminus.monotone ω') (fun ω' s ↦ hminus.rightContinuous ω' s)
    τ (fun s ω' ↦ clippedDownwardIncrement R f
      (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω
  rw [throughStopClippedDynkinProcess, throughStopClippedGeneratorCompensator]
  change clippedObservable R f K0 Nplus Nminus u ω -
      clippedObservable R f K0 Nplus Nminus 0 ω - _ = _
  rw [hchain, ← hplusStop, ← hminusStop]
  simp only [compensatedIntegral]
  ring

/-- The masked clipped Dynkin residual is a true martingale. -/
theorem throughStopClippedDynkinProcess_martingale
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    {Λplus Λminus : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    (hNo : ∀ T, NoSimultaneousJumpsOn Nplus Nminus T)
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hK0 : StronglyMeasurable[ℱ 0] (fun ω ↦ (K0 ω : ℝ)))
    (hMask : IsBoundedSimplePredictable ℱ (throughStopMask τ))
    (R : ℕ) (f : ℤ → ℝ)
    (hAplus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λplus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λminus (fun _ _ ↦ (1 : ℝ)) t ω) μ) :
    Martingale (throughStopClippedDynkinProcess τ R f K0 Nplus Nminus Λplus Λminus) ℱ μ := by
  let Hplus : ℝ≥0 → Ω → ℝ := fun s ω ↦ clippedUpwardIncrement R f
    (leftCurrentOfCounts K0 Nplus Nminus s ω)
  let Hminus : ℝ≥0 → Ω → ℝ := fun s ω ↦ clippedDownwardIncrement R f
    (leftCurrentOfCounts K0 Nplus Nminus s ω)
  have hHplus : IsBoundedPredictable ℱ Hplus := by
    simpa only [Hplus] using
      clippedUpwardIncrement_boundedPredictable hplus hminus hK0 R f
  have hHminus : IsBoundedPredictable ℱ Hminus := by
    simpa only [Hminus] using
      clippedDownwardIncrement_boundedPredictable hplus hminus hK0 R f
  have hMHplus : IsBoundedPredictable ℱ
      (fun s ω ↦ throughStopMask τ s ω * Hplus s ω) :=
    hMask.isBoundedPredictable.mul_process hHplus
  have hMHminus : IsBoundedPredictable ℱ
      (fun s ω ↦ throughStopMask τ s ω * Hminus s ω) :=
    hMask.isBoundedPredictable.mul_process hHminus
  rw [throughStopClippedDynkinProcess_eq_compensated_sum hplus hminus hNo
    τ R f Λplus Λminus]
  change Martingale
    (compensatedIntegral Nplus Λplus
        (fun s ω ↦ throughStopMask τ s ω * Hplus s ω) +
      compensatedIntegral Nminus Λminus
        (fun s ω ↦ throughStopMask τ s ω * Hminus s ω)) ℱ μ
  exact (hΛplus.martingale_of_boundedPredictable hMHplus hAplus).add
    (hΛminus.martingale_of_boundedPredictable hMHminus hAminus)

/-- The masked generator compensator is integrable under the ordinary total-intensity moment
hypotheses. -/
theorem throughStopClippedGeneratorCompensator_integrable
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {R : ℕ} {f : ℤ → ℝ} {K0 : Ω → ℤ}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0}
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
    (hHplus : IsBoundedPredictable ℱ
      (fun s ω ↦ throughStopMask τ s ω * clippedUpwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω)))
    (hHminus : IsBoundedPredictable ℱ
      (fun s ω ↦ throughStopMask τ s ω * clippedDownwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω)))
    (hAplus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λplus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (hAminus : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λminus (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (t : ℝ≥0) :
    Integrable (throughStopClippedGeneratorCompensator τ R f K0 Nplus Nminus
      Λplus Λminus t) μ := by
  exact (integratedIntensity_integrable_of_boundedPredictable
    hΛplus hHplus hAplus t).add
      (integratedIntensity_integrable_of_boundedPredictable hΛminus hHminus hAminus t)

/-- A genuine through-stop clipped Dynkin martingale has zero expectation at deterministic
times. -/
theorem integral_throughStopClippedDynkinProcess_eq_zero
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {f : ℤ → ℝ} {K0 : Ω → ℤ}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0}
    (hM : Martingale
      (throughStopClippedDynkinProcess τ R f K0 Nplus Nminus Λplus Λminus) ℱ μ)
    (t : ℝ≥0) :
    ∫ ω, throughStopClippedDynkinProcess
      τ R f K0 Nplus Nminus Λplus Λminus t ω ∂μ = 0 := by
  have hEq := hM.setIntegral_eq (i := 0) (j := t) bot_le
    (s := Set.univ) MeasurableSet.univ
  simpa only [Measure.restrict_univ, throughStopClippedDynkinProcess_zero, integral_zero]
    using hEq.symm

/-- The stopped clipped observable is integrable once its initial value and masked compensator
are integrable. -/
theorem stoppedClippedObservable_integrable_of_martingale
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {f : ℤ → ℝ} {K0 : Ω → ℤ}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0}
    (hM : Martingale
      (throughStopClippedDynkinProcess τ R f K0 Nplus Nminus Λplus Λminus) ℱ μ)
    (t : ℝ≥0)
    (hObs0 : Integrable (clippedObservable R f K0 Nplus Nminus 0) μ)
    (hComp : Integrable
      (throughStopClippedGeneratorCompensator τ R f K0 Nplus Nminus
        Λplus Λminus t) μ) :
    Integrable
      (MeasureTheory.stoppedProcess (clippedObservable R f K0 Nplus Nminus) τ t) μ := by
  have heq :
      MeasureTheory.stoppedProcess (clippedObservable R f K0 Nplus Nminus) τ t =
        fun ω ↦ throughStopClippedDynkinProcess
            τ R f K0 Nplus Nminus Λplus Λminus t ω +
          clippedObservable R f K0 Nplus Nminus 0 ω +
            throughStopClippedGeneratorCompensator τ R f K0 Nplus Nminus
              Λplus Λminus t ω := by
    funext ω
    simp only [throughStopClippedDynkinProcess]
    ring
  rw [heq]
  exact ((hM.integrable t).add hObs0).add hComp

/-- Deterministic-time expectation Dynkin identity for the stopped clipped observable. -/
theorem integral_stoppedClippedObservable_eq_add_throughStopCompensator
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {f : ℤ → ℝ} {K0 : Ω → ℤ}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0}
    (hM : Martingale
      (throughStopClippedDynkinProcess τ R f K0 Nplus Nminus Λplus Λminus) ℱ μ)
    (t : ℝ≥0)
    (hObsT : Integrable
      (MeasureTheory.stoppedProcess (clippedObservable R f K0 Nplus Nminus) τ t) μ)
    (hObs0 : Integrable (clippedObservable R f K0 Nplus Nminus 0) μ)
    (hComp : Integrable
      (throughStopClippedGeneratorCompensator τ R f K0 Nplus Nminus
        Λplus Λminus t) μ) :
    ∫ ω, MeasureTheory.stoppedProcess
        (clippedObservable R f K0 Nplus Nminus) τ t ω ∂μ =
      (∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) +
        ∫ ω, throughStopClippedGeneratorCompensator
          τ R f K0 Nplus Nminus Λplus Λminus t ω ∂μ := by
  have hzero := integral_throughStopClippedDynkinProcess_eq_zero hM t
  change (∫ ω,
      (MeasureTheory.stoppedProcess (clippedObservable R f K0 Nplus Nminus) τ t ω -
        clippedObservable R f K0 Nplus Nminus 0 ω) -
          throughStopClippedGeneratorCompensator τ R f K0 Nplus Nminus
            Λplus Λminus t ω ∂μ) = 0 at hzero
  have hsplit :
      (∫ ω,
          (MeasureTheory.stoppedProcess (clippedObservable R f K0 Nplus Nminus) τ t ω -
            clippedObservable R f K0 Nplus Nminus 0 ω) -
              throughStopClippedGeneratorCompensator τ R f K0 Nplus Nminus
                Λplus Λminus t ω ∂μ) =
        (∫ ω, MeasureTheory.stoppedProcess
          (clippedObservable R f K0 Nplus Nminus) τ t ω ∂μ) -
          (∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) -
            ∫ ω, throughStopClippedGeneratorCompensator
              τ R f K0 Nplus Nminus Λplus Λminus t ω ∂μ := by
    calc
      _ = (∫ ω, MeasureTheory.stoppedProcess
            (clippedObservable R f K0 Nplus Nminus) τ t ω -
              clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) -
            ∫ ω, throughStopClippedGeneratorCompensator
              τ R f K0 Nplus Nminus Λplus Λminus t ω ∂μ :=
          integral_sub (hObsT.sub hObs0) hComp
      _ = _ := by rw [integral_sub hObsT hObs0]
  rw [hsplit] at hzero
  linarith

end OTSelector.CountingProcess
