import OTSelector.Feedback.MarkedDynkin

/-!
# Expectation identities from the genuine marked Dynkin martingale

This module extracts the integrated Dynkin identity from `clippedDynkinProcess_martingale`.
Unlike the earlier probability-facing algebra, the identity below is not supplied as a hypothesis:
it follows from the actual two-colour compensated martingale.  Integrability of the three terms is
kept explicit only where the integral must be split algebraically.
-/

open Set
open scoped NNReal MeasureTheory ProbabilityTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Sum of the two predictable compensators in the clipped current chain rule. -/
noncomputable def clippedGeneratorCompensator
    (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  integratedIntensity Λplus
      (fun s ω' => clippedUpwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω +
    integratedIntensity Λminus
      (fun s ω' => clippedDownwardIncrement R f
        (leftCurrentOfCounts K0 Nplus Nminus s ω')) t ω

omit [MeasurableSpace Ω] in
theorem clippedDynkinProcess_eq_observable_sub_compensator
    (R : ℕ) (f : ℤ → ℝ) (K0 : Ω → ℤ)
    (Nplus Nminus : ℝ≥0 → Ω → ℕ) (Λplus Λminus : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus t ω =
      clippedObservable R f K0 Nplus Nminus t ω -
        clippedObservable R f K0 Nplus Nminus 0 ω -
          clippedGeneratorCompensator R f K0 Nplus Nminus Λplus Λminus t ω := by
  rfl

/-- A genuine clipped Dynkin martingale has zero expectation at every deterministic time. -/
theorem integral_clippedDynkinProcess_eq_zero
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {f : ℤ → ℝ} {K0 : Ω → ℤ}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hM : Martingale
      (clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus) ℱ μ)
    (t : ℝ≥0) :
    ∫ ω, clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus t ω ∂μ = 0 := by
  have hEq := hM.setIntegral_eq (i := 0) (j := t) bot_le
    (s := Set.univ) MeasurableSet.univ
  simpa only [Measure.restrict_univ, clippedDynkinProcess_zero, integral_zero] using hEq.symm

/-- The deterministic-time expectation form of the clipped Dynkin identity. -/
theorem integral_clippedObservable_eq_add_generatorCompensator
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {f : ℤ → ℝ} {K0 : Ω → ℤ}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hM : Martingale
      (clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus) ℱ μ)
    (t : ℝ≥0)
    (hObsT : Integrable (clippedObservable R f K0 Nplus Nminus t) μ)
    (hObs0 : Integrable (clippedObservable R f K0 Nplus Nminus 0) μ)
    (hComp : Integrable
      (clippedGeneratorCompensator R f K0 Nplus Nminus Λplus Λminus t) μ) :
    ∫ ω, clippedObservable R f K0 Nplus Nminus t ω ∂μ =
      ∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ +
        ∫ ω, clippedGeneratorCompensator
          R f K0 Nplus Nminus Λplus Λminus t ω ∂μ := by
  have hzero := integral_clippedDynkinProcess_eq_zero hM t
  rw [show clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus t =
      fun ω => clippedObservable R f K0 Nplus Nminus t ω -
        clippedObservable R f K0 Nplus Nminus 0 ω -
          clippedGeneratorCompensator R f K0 Nplus Nminus Λplus Λminus t ω by
      funext ω
      rfl] at hzero
  change (∫ ω, (clippedObservable R f K0 Nplus Nminus t ω -
      clippedObservable R f K0 Nplus Nminus 0 ω) -
        clippedGeneratorCompensator R f K0 Nplus Nminus Λplus Λminus t ω ∂μ) = 0 at hzero
  have hsplit :
      (∫ ω, (clippedObservable R f K0 Nplus Nminus t ω -
          clippedObservable R f K0 Nplus Nminus 0 ω) -
            clippedGeneratorCompensator R f K0 Nplus Nminus Λplus Λminus t ω ∂μ) =
        (∫ ω, clippedObservable R f K0 Nplus Nminus t ω ∂μ) -
          (∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) -
            ∫ ω, clippedGeneratorCompensator
              R f K0 Nplus Nminus Λplus Λminus t ω ∂μ := by
    calc
      _ = (∫ ω, clippedObservable R f K0 Nplus Nminus t ω -
            clippedObservable R f K0 Nplus Nminus 0 ω ∂μ) -
            ∫ ω, clippedGeneratorCompensator
              R f K0 Nplus Nminus Λplus Λminus t ω ∂μ :=
          integral_sub (hObsT.sub hObs0) hComp
      _ = _ := by rw [integral_sub hObsT hObs0]
  rw [hsplit] at hzero
  linarith

/-- The two compensator terms are integrable under the same hypotheses used by the bounded
predictable martingale closure. -/
theorem clippedGeneratorCompensator_integrable
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {R : ℕ} {f : ℤ → ℝ} {K0 : Ω → ℤ}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hΛplus : HasPredictableIntensity μ ℱ Nplus Λplus)
    (hΛminus : HasPredictableIntensity μ ℱ Nminus Λminus)
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
    (t : ℝ≥0) :
    Integrable
      (clippedGeneratorCompensator R f K0 Nplus Nminus Λplus Λminus t) μ := by
  exact (integratedIntensity_integrable_of_boundedPredictable
    hΛplus hHplus hAplus t).add
      (integratedIntensity_integrable_of_boundedPredictable
        hΛminus hHminus hAminus t)

/-- The observable at time `t` is integrable once its initial value is integrable: the Dynkin
residual and both compensators already are integrable. -/
theorem clippedObservable_integrable_of_martingale
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {f : ℤ → ℝ} {K0 : Ω → ℤ}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {Λplus Λminus : ℝ≥0 → Ω → ℝ}
    (hM : Martingale
      (clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus) ℱ μ)
    (t : ℝ≥0)
    (hObs0 : Integrable (clippedObservable R f K0 Nplus Nminus 0) μ)
    (hComp : Integrable
      (clippedGeneratorCompensator R f K0 Nplus Nminus Λplus Λminus t) μ) :
    Integrable (clippedObservable R f K0 Nplus Nminus t) μ := by
  have heq : clippedObservable R f K0 Nplus Nminus t = fun ω =>
      clippedDynkinProcess R f K0 Nplus Nminus Λplus Λminus t ω +
        clippedObservable R f K0 Nplus Nminus 0 ω +
          clippedGeneratorCompensator R f K0 Nplus Nminus Λplus Λminus t ω := by
    funext ω
    rw [clippedDynkinProcess_eq_observable_sub_compensator]
    ring
  rw [heq]
  exact ((hM.integrable t).add hObs0).add hComp

/-- A genuine pair of predictable intensities supplies the expectation Dynkin identity directly;
no external Dynkin equality remains among the hypotheses. -/
theorem integral_clippedObservable_eq_add_generatorCompensator_of_initial_measurable
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {R : ℕ} {f : ℤ → ℝ} {K0 : Ω → ℤ}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {Λplus Λminus : ℝ≥0 → Ω → ℝ}
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
    (hObs0 : Integrable (clippedObservable R f K0 Nplus Nminus 0) μ)
    (t : ℝ≥0) :
    ∫ ω, clippedObservable R f K0 Nplus Nminus t ω ∂μ =
      ∫ ω, clippedObservable R f K0 Nplus Nminus 0 ω ∂μ +
        ∫ ω, clippedGeneratorCompensator
          R f K0 Nplus Nminus Λplus Λminus t ω ∂μ := by
  let Hplus : ℝ≥0 → Ω → ℝ := fun s ω => clippedUpwardIncrement R f
    (leftCurrentOfCounts K0 Nplus Nminus s ω)
  let Hminus : ℝ≥0 → Ω → ℝ := fun s ω => clippedDownwardIncrement R f
    (leftCurrentOfCounts K0 Nplus Nminus s ω)
  have hHplus : IsBoundedPredictable ℱ Hplus := by
    simpa only [Hplus] using
      clippedUpwardIncrement_boundedPredictable hplus hminus hK0 R f
  have hHminus : IsBoundedPredictable ℱ Hminus := by
    simpa only [Hminus] using
      clippedDownwardIncrement_boundedPredictable hplus hminus hK0 R f
  have hM := clippedDynkinProcess_martingale hplus hminus hNo hΛplus hΛminus R f
    hHplus hHminus hAplus hAminus
  have hComp := clippedGeneratorCompensator_integrable hΛplus hΛminus
    hHplus hHminus hAplus hAminus t
  have hObsT := clippedObservable_integrable_of_martingale hM t hObs0 hComp
  exact integral_clippedObservable_eq_add_generatorCompensator
    hM t hObsT hObs0 hComp

/-- Cubic occupation estimate obtained from the genuine two-colour Dynkin martingale and a
pointwise compensator drift bound.  The remaining drift hypothesis is deterministic: later
feedback code supplies it by integrating the clipped generator inequality before the stopping
coordinate. -/
theorem cubic_clipped_occupation_bound_of_compensator_drift
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
    {C c : ℝ} (hc : 0 < c)
    (Q : Ω → ℝ) (hQint : Integrable Q μ) (t : ℝ≥0)
    (hObs0 : Integrable
      (clippedObservable R cubicLyapunov K0 Nplus Nminus 0) μ)
    (hCompBound : ∀ ω,
      clippedGeneratorCompensator R cubicLyapunov K0 Nplus Nminus
          Λplus Λminus t ω ≤
        -(2 * c) * Q ω + (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) :
    ∫ ω, Q ω ∂μ ≤
      ((∫ ω, clippedObservable R cubicLyapunov K0 Nplus Nminus 0 ω ∂μ) +
        (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) / (2 * c) := by
  let Hplus : ℝ≥0 → Ω → ℝ := fun s ω => clippedUpwardIncrement R cubicLyapunov
    (leftCurrentOfCounts K0 Nplus Nminus s ω)
  let Hminus : ℝ≥0 → Ω → ℝ := fun s ω => clippedDownwardIncrement R cubicLyapunov
    (leftCurrentOfCounts K0 Nplus Nminus s ω)
  have hHplus : IsBoundedPredictable ℱ Hplus := by
    simpa only [Hplus] using
      clippedUpwardIncrement_boundedPredictable hplus hminus hK0 R cubicLyapunov
  have hHminus : IsBoundedPredictable ℱ Hminus := by
    simpa only [Hminus] using
      clippedDownwardIncrement_boundedPredictable hplus hminus hK0 R cubicLyapunov
  have hCompInt := clippedGeneratorCompensator_integrable hΛplus hΛminus
    hHplus hHminus hAplus hAminus t
  have hM := clippedDynkinProcess_martingale hplus hminus hNo hΛplus hΛminus
    R cubicLyapunov hHplus hHminus hAplus hAminus
  have hObsT := clippedObservable_integrable_of_martingale hM t hObs0 hCompInt
  have hDynkin := integral_clippedObservable_eq_add_generatorCompensator
    hM t hObsT hObs0 hCompInt
  have hrightInt : Integrable
      (fun ω => -(2 * c) * Q ω + (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) μ :=
    (hQint.const_mul _).add (integrable_const _)
  have hcompIntegral :
      (∫ ω, clippedGeneratorCompensator R cubicLyapunov K0 Nplus Nminus
          Λplus Λminus t ω ∂μ) ≤
        ∫ ω, (-(2 * c) * Q ω +
          (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) ∂μ :=
    integral_mono_ae hCompInt hrightInt (ae_of_all _ hCompBound)
  have hrightEq :
      (∫ ω, (-(2 * c) * Q ω +
          (2 * C + 9 * C ^ 2 / c) * (t : ℝ)) ∂μ) =
        -(2 * c) * (∫ ω, Q ω ∂μ) +
          (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
    rw [integral_add (hQint.const_mul _) (integrable_const _), integral_const_mul,
      integral_const]
    simp [smul_eq_mul]
  rw [hrightEq] at hcompIntegral
  have hterminal :
      0 ≤ ∫ ω, clippedObservable R cubicLyapunov K0 Nplus Nminus t ω ∂μ := by
    exact integral_nonneg fun ω => by
      simp only [clippedObservable, cubicLyapunov]
      positivity
  have hcore :
      (2 * c) * (∫ ω, Q ω ∂μ) ≤
        (∫ ω, clippedObservable R cubicLyapunov K0 Nplus Nminus 0 ω ∂μ) +
          (2 * C + 9 * C ^ 2 / c) * (t : ℝ) := by
    nlinarith [hterminal, hDynkin, hcompIntegral]
  apply (le_div_iff₀ (by positivity : 0 < 2 * c)).2
  simpa [mul_comm] using hcore

end OTSelector.CountingProcess
