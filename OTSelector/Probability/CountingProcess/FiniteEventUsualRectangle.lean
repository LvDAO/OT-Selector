import OTSelector.Probability.CountingProcess.FiniteEventThinning
import OTSelector.Probability.CountingProcess.FiniteEventIntensitySideConditions
import OTSelector.Probability.CountingProcess.UsualRectangleLift
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Raw-to-usual rectangle identities for finite-event counts

This module supplies the analytic side conditions needed to apply
`setIntegral_eq_of_usualAugmentation_of_rightL1` to a finite-event count minus an accumulated
bounded rate.  Event times are stopping times for the usual augmentation, while the input
count-increment identity is required only on the raw filtration.

The proof uses finite-cardinality bounds, pathwise right-continuity of the count, continuity of
the accumulated rate, and dominated convergence under a finite base measure.  No martingale or
intensity assertion is assumed.
-/

open Filter Set
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Fixed-time side conditions -/

/-- A finite count of stopping times is strongly adapted.  No positivity or no-tie assumption is
needed for this fixed-time measurability statement. -/
theorem finiteEventCountTop_stronglyAdapted
    {m : ℕ} (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop ℝ≥0)
    (hξ : ∀ i, IsStoppingTime F (ξ i)) :
    StronglyAdapted F (fun t ω ↦ (finiteEventCountTop ξ t ω : ℝ)) := by
  classical
  intro t
  let f : Fin m → Ω → ℝ := fun i ω ↦
    if ξ i ω ≤ (t : WithTop ℝ≥0) then 1 else 0
  have hsum : StronglyMeasurable[F t] (∑ i : Fin m, f i) := by
    apply Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin m)) (f := f)
    intro i hi
    have hmeas : Measurable[F t] (fun ω ↦ f i ω) := by
      simp only [f]
      exact Measurable.ite ((hξ i).measurableSet_le t)
        measurable_const measurable_const
    exact hmeas.stronglyMeasurable
  convert hsum using 1
  funext ω
  simpa [f] using (finiteEventCountTop_cast_eq_sum (R := ℝ) ξ t ω)

/-- Under a finite base measure, every fixed-time finite-event count is integrable. -/
theorem finiteEventCountTop_integrable
    {m : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop ℝ≥0)
    (hξ : ∀ i, IsStoppingTime F (ξ i)) :
    ∀ t, Integrable (fun ω ↦ (finiteEventCountTop ξ t ω : ℝ)) μ := by
  have hAdapted := finiteEventCountTop_stronglyAdapted F ξ hξ
  intro t
  have hmeas : AEStronglyMeasurable
      (fun ω ↦ (finiteEventCountTop ξ t ω : ℝ)) μ :=
    ((hAdapted t).mono (F.le t)).measurable.aestronglyMeasurable
  refine Integrable.of_bound hmeas (m : ℝ) ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast finiteEventCountTop_le ξ t ω

omit [MeasurableSpace Ω] in
/-- Additivity of the accumulated unit rate on `(s,t]`, stated using only pathwise local
integrability. -/
theorem setIntegral_Ioc_eq_integratedIntensity_one_sub
    {Λ : ℝ≥0 → Ω → ℝ} {ω : Ω} {s t : ℝ≥0} (hst : s ≤ t)
    (hΛint : IntegrableOn (fun u ↦ Λ u ω) (Ioc (0 : ℝ≥0) t) timeMeasure) :
    (∫ u in Ioc s t, Λ u ω ∂timeMeasure) =
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω -
        integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω := by
  have h0s : Ioc (0 : ℝ≥0) s ⊆ Ioc (0 : ℝ≥0) t := by
    intro u hu
    exact ⟨hu.1, hu.2.trans hst⟩
  have hst' : Ioc s t ⊆ Ioc (0 : ℝ≥0) t := by
    intro u hu
    exact ⟨lt_of_le_of_lt bot_le hu.1, hu.2⟩
  have hInt0s := hΛint.mono_set h0s
  have hIntst := hΛint.mono_set hst'
  have hadd :
      (∫ u in Ioc (0 : ℝ≥0) t, Λ u ω ∂timeMeasure) =
        (∫ u in Ioc (0 : ℝ≥0) s, Λ u ω ∂timeMeasure) +
          ∫ u in Ioc s t, Λ u ω ∂timeMeasure := by
    rw [← Ioc_union_Ioc_eq_Ioc (show (0 : ℝ≥0) ≤ s from bot_le) hst]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      hInt0s hIntst
  simp only [integratedIntensity, one_mul]
  linarith

omit [MeasurableSpace Ω] in
/-- A nonnegative pathwise locally integrable rate bounded by `C` has accumulated unit rate in
`[0, C t]`. -/
theorem integratedIntensity_one_nonneg_le_of_bounded
    {Λ : ℝ≥0 → Ω → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (hΛnonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛupper : ∀ u ω, Λ u ω ≤ C)
    (hΛint : ∀ t ω,
      IntegrableOn (fun u ↦ Λ u ω) (Ioc (0 : ℝ≥0) t) timeMeasure)
    (t : ℝ≥0) (ω : Ω) :
    0 ≤ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω ∧
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω ≤ C * (t : ℝ) := by
  have hnonneg : 0 ≤ ∫ u in Ioc (0 : ℝ≥0) t, Λ u ω ∂timeMeasure :=
    setIntegral_nonneg measurableSet_Ioc (fun u _ ↦ hΛnonneg u ω)
  have hmono : (∫ u in Ioc (0 : ℝ≥0) t, Λ u ω ∂timeMeasure) ≤
      ∫ u in Ioc (0 : ℝ≥0) t, (fun _ ↦ C) u ∂timeMeasure := by
    refine setIntegral_mono_on (hΛint t ω) ?_ measurableSet_Ioc ?_
    · exact integrableOn_const (C := C) (timeMeasure_Ioc_lt_top 0 t).ne
    · intro u hu
      exact hΛupper u ω
  have hconst : (∫ u in Ioc (0 : ℝ≥0) t, (fun _ ↦ C) u ∂timeMeasure) =
      C * (t : ℝ) := by
    rw [integral_timeMeasure_eq_intervalIntegral (fun _ ↦ C) 0 t (by simp)]
    rw [intervalIntegral.integral_const]
    simp
    ring
  simpa [integratedIntensity] using ⟨hnonneg, hmono.trans_eq hconst⟩

/-- Predictability and a deterministic pathwise rate bound give fixed-time integrability of the
accumulated unit rate under a finite base measure. -/
theorem integratedIntensity_one_integrable_of_bounded_local
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    {Λ : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hΛpred : IsStronglyPredictable F Λ) (hC : 0 ≤ C)
    (hΛnonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛupper : ∀ u ω, Λ u ω ≤ C)
    (hΛint : ∀ t ω,
      IntegrableOn (fun u ↦ Λ u ω) (Ioc (0 : ℝ≥0) t) timeMeasure) :
    ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ := by
  have hPathOne : ∀ t ω, IntegrableOn (fun u ↦ (1 : ℝ) * Λ u ω)
      (Ioc (0 : ℝ≥0) t) timeMeasure := by
    intro t ω
    simpa only [one_mul] using hΛint t ω
  have hAdapted : StronglyAdapted F
      (fun t ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) :=
    finiteEvent_integratedIntensity_stronglyAdapted F hΛpred
      (boundedSimplePredictable_one F) hPathOne
  intro t
  have hmeas : AEStronglyMeasurable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ :=
    ((hAdapted t).mono (F.le t)).measurable.aestronglyMeasurable
  refine Integrable.of_bound hmeas (C * (t : ℝ)) ?_
  filter_upwards [] with ω
  have hbound := integratedIntensity_one_nonneg_le_of_bounded
    hC hΛnonneg hΛupper hΛint t ω
  rw [Real.norm_eq_abs, abs_of_nonneg hbound.1]
  exact hbound.2

/-! ## The right-L1 bridge -/

private theorem integral_centered_eq_iff_increment_eq
    {ν : Measure Ω} {Nt Ns At As R : Ω → ℝ}
    (hNt : Integrable Nt ν) (hNs : Integrable Ns ν)
    (hAt : Integrable At ν) (hAs : Integrable As ν)
    (hR : ∀ ω, R ω = At ω - As ω) :
    (∫ ω, Nt ω - At ω ∂ν) = (∫ ω, Ns ω - As ω ∂ν) ↔
      (∫ ω, Nt ω - Ns ω ∂ν) = ∫ ω, R ω ∂ν := by
  have hCenteredT : (∫ ω, Nt ω - At ω ∂ν) = (∫ ω, Nt ω ∂ν) - ∫ ω, At ω ∂ν :=
    integral_sub' hNt hAt
  have hCenteredS : (∫ ω, Ns ω - As ω ∂ν) = (∫ ω, Ns ω ∂ν) - ∫ ω, As ω ∂ν :=
    integral_sub' hNs hAs
  have hCountInc : (∫ ω, Nt ω - Ns ω ∂ν) = (∫ ω, Nt ω ∂ν) - ∫ ω, Ns ω ∂ν :=
    integral_sub' hNt hNs
  have hRate : (∫ ω, R ω ∂ν) = ∫ ω, At ω - As ω ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall hR)
  have hAccumInc : (∫ ω, At ω - As ω ∂ν) = (∫ ω, At ω ∂ν) - ∫ ω, As ω ∂ν :=
    integral_sub' hAt hAs
  rw [hCenteredT, hCenteredS, hCountInc, hRate, hAccumInc]
  constructor <;> intro h <;> linarith

private theorem finiteEvent_centered_rightL1
    {m : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Fin m → Ω → WithTop ℝ≥0) (Λ : ℝ≥0 → Ω → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hΛnonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛupper : ∀ u ω, Λ u ω ≤ C)
    (hΛint : ∀ t ω,
      IntegrableOn (fun u ↦ Λ u ω) (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hMIntegrable : ∀ t, Integrable
      (fun ω ↦ (finiteEventCountTop ξ t ω : ℝ) -
        integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ)
    (s : ℝ≥0) {r : ℕ → ℝ≥0} (hr : Tendsto r atTop (𝓝 s))
    (hrRight : ∀ᶠ n in atTop, s < r n) :
    Tendsto (fun n ↦ ∫⁻ ω,
      ‖((finiteEventCountTop ξ (r n) ω : ℝ) -
          integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) (r n) ω) -
        ((finiteEventCountTop ξ s ω : ℝ) -
          integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω)‖ₑ ∂μ)
      atTop (𝓝 0) := by
  let M : ℝ≥0 → Ω → ℝ := fun t ω ↦
    (finiteEventCountTop ξ t ω : ℝ) -
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω
  let K : ℝ := 2 * ((m : ℝ) + C * ((s : ℝ) + 1))
  have hMInt : ∀ t, Integrable (M t) μ := by
    intro t
    simpa only [M] using hMIntegrable t
  have hrWithin : Tendsto r atTop (𝓝[Ici s] s) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hr, hrRight.mono fun n hn ↦ hn.le⟩
  have hPointwise : ∀ ω, Tendsto (fun n ↦ M (r n) ω) atTop (𝓝 (M s ω)) := by
    intro ω
    have hN : Tendsto (fun n ↦ (finiteEventCountTop ξ (r n) ω : ℝ)) atTop
        (𝓝 (finiteEventCountTop ξ s ω : ℝ)) :=
      (finiteEventCountTop_rightContinuous ξ ω s).tendsto.comp hrWithin
    have hA : Tendsto
        (fun n ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) (r n) ω) atTop
        (𝓝 (integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω)) :=
      ((A_continuous (fun t ↦ hΛint t ω)).tendsto s).comp hr
    simpa only [M] using hN.sub hA
  have hslt : s < s + 1 := lt_add_of_pos_right s zero_lt_one
  have hrUpper : ∀ᶠ n in atTop, r n < s + 1 :=
    hr.eventually (Iio_mem_nhds hslt)
  have hFMeas : ∀ᶠ n in atTop,
      AEMeasurable (fun ω ↦ ‖M (r n) ω - M s ω‖ₑ) μ :=
    Filter.Eventually.of_forall fun n ↦
      ((hMInt (r n)).sub (hMInt s)).aestronglyMeasurable.enorm
  have hBound : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
      ‖M (r n) ω - M s ω‖ₑ ≤ ENNReal.ofReal K := by
    filter_upwards [hrUpper] with n hn
    exact Filter.Eventually.of_forall fun ω ↦ by
      have hrReal : (r n : ℝ) ≤ (s : ℝ) + 1 := by
        exact_mod_cast hn.le
      have hsReal : (s : ℝ) ≤ (s : ℝ) + 1 := by linarith
      have hNr : ‖(finiteEventCountTop ξ (r n) ω : ℝ)‖ ≤ (m : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast finiteEventCountTop_le ξ (r n) ω
      have hNs : ‖(finiteEventCountTop ξ s ω : ℝ)‖ ≤ (m : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast finiteEventCountTop_le ξ s ω
      have hAr0 := integratedIntensity_one_nonneg_le_of_bounded
        hC hΛnonneg hΛupper hΛint (r n) ω
      have hAs0 := integratedIntensity_one_nonneg_le_of_bounded
        hC hΛnonneg hΛupper hΛint s ω
      have hAr :
          ‖integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) (r n) ω‖ ≤
            C * ((s : ℝ) + 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hAr0.1]
        exact hAr0.2.trans (mul_le_mul_of_nonneg_left hrReal hC)
      have hAs : ‖integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω‖ ≤
          C * ((s : ℝ) + 1) := by
        rw [Real.norm_eq_abs, abs_of_nonneg hAs0.1]
        exact hAs0.2.trans (mul_le_mul_of_nonneg_left hsReal hC)
      have hMr : ‖M (r n) ω‖ ≤ (m : ℝ) + C * ((s : ℝ) + 1) := by
        exact (norm_sub_le _ _).trans (add_le_add hNr hAr)
      have hMs : ‖M s ω‖ ≤ (m : ℝ) + C * ((s : ℝ) + 1) := by
        exact (norm_sub_le _ _).trans (add_le_add hNs hAs)
      have hnorm : ‖M (r n) ω - M s ω‖ ≤ K := by
        calc
          ‖M (r n) ω - M s ω‖ ≤ ‖M (r n) ω‖ + ‖M s ω‖ := norm_sub_le _ _
          _ ≤ ((m : ℝ) + C * ((s : ℝ) + 1)) +
              ((m : ℝ) + C * ((s : ℝ) + 1)) := add_le_add hMr hMs
          _ = K := by simp only [K]; ring
      simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm
  have hFinite : (∫⁻ _ : Ω, ENNReal.ofReal K ∂μ) ≠ ∞ :=
    (lintegral_const_lt_top (μ := μ) ENNReal.ofReal_ne_top).ne
  have hLimit : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ ‖M (r n) ω - M s ω‖ₑ) atTop (𝓝 0) := by
    filter_upwards [] with ω
    have hconst : Tendsto (fun _ : ℕ ↦ M s ω) atTop (nhds (M s ω)) :=
      tendsto_const_nhds
    have hzero : Tendsto (fun n ↦ M (r n) ω - M s ω) atTop (𝓝 0) := by
      simpa using (hPointwise ω).sub hconst
    simpa only [Function.comp_def, enorm_zero] using
      (continuous_enorm.tendsto (0 : ℝ)).comp hzero
  have hDCT := tendsto_lintegral_filter_of_dominated_convergence'
    (μ := μ) (l := atTop)
    (F := fun n ω ↦ ‖M (r n) ω - M s ω‖ₑ)
    (f := fun _ ↦ (0 : ℝ≥0∞))
    (fun _ ↦ ENNReal.ofReal K) hFMeas hBound hFinite hLimit
  simpa only [M, lintegral_zero] using hDCT

/-! ## Raw-to-usual extension -/

/-- Extend a raw finite-event count-increment identity to the usual augmentation.

The event family may already be a predictably thinned family.  It is only required to consist of
stopping times for the usual augmentation.  The rate assumptions are predictability,
nonnegativity, a deterministic bound, and finite-horizon pathwise integrability. -/
theorem finiteEventCountTop_increment_setIntegral_eq_of_usualAugmentation
    {m : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F₀ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop ℝ≥0)
    (hξ : ∀ i, IsStoppingTime (usualAugmentation F₀ μ) (ξ i))
    (Λ : ℝ≥0 → Ω → ℝ)
    (hΛpred : IsStronglyPredictable (usualAugmentation F₀ μ) Λ)
    {C : ℝ} (hC : 0 ≤ C)
    (hΛnonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛupper : ∀ u ω, Λ u ω ≤ C)
    (hΛint : ∀ t ω,
      IntegrableOn (fun u ↦ Λ u ω) (Ioc (0 : ℝ≥0) t) timeMeasure)
    (hRaw : ∀ {s t : ℝ≥0}, s ≤ t → ∀ B : Set Ω, MeasurableSet[F₀ s] B →
      (∫ ω in B,
        ((finiteEventCountTop ξ t ω : ℝ) - finiteEventCountTop ξ s ω) ∂μ) =
        ∫ ω in B, ∫ u in Ioc s t, Λ u ω ∂timeMeasure ∂μ) :
    ∀ {s t : ℝ≥0}, s ≤ t → ∀ B : Set Ω,
      MeasurableSet[usualAugmentation F₀ μ s] B →
        (∫ ω in B,
          ((finiteEventCountTop ξ t ω : ℝ) - finiteEventCountTop ξ s ω) ∂μ) =
          ∫ ω in B, ∫ u in Ioc s t, Λ u ω ∂timeMeasure ∂μ := by
  have hNIntegrable := finiteEventCountTop_integrable μ (usualAugmentation F₀ μ) ξ hξ
  have hAIntegrable := integratedIntensity_one_integrable_of_bounded_local
    μ (usualAugmentation F₀ μ) hΛpred hC hΛnonneg hΛupper hΛint
  have hMIntegrable : ∀ t, Integrable
      (fun ω ↦ (finiteEventCountTop ξ t ω : ℝ) -
        integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ := by
    intro t
    exact (hNIntegrable t).sub (hAIntegrable t)
  have hRawCentered : ∀ {s t : ℝ≥0}, s ≤ t → ∀ B : Set Ω,
      MeasurableSet[F₀ s] B →
        (∫ ω in B, (finiteEventCountTop ξ t ω : ℝ) -
          integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω ∂μ) =
        ∫ ω in B, (finiteEventCountTop ξ s ω : ℝ) -
          integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω ∂μ := by
    intro s t hst B hB
    apply (integral_centered_eq_iff_increment_eq
      ((hNIntegrable t).mono_measure Measure.restrict_le_self)
      ((hNIntegrable s).mono_measure Measure.restrict_le_self)
      ((hAIntegrable t).mono_measure Measure.restrict_le_self)
      ((hAIntegrable s).mono_measure Measure.restrict_le_self)
      (fun ω ↦ setIntegral_Ioc_eq_integratedIntensity_one_sub hst (hΛint t ω))).2
    exact hRaw hst B hB
  have hRightL1 : ∀ s : ℝ≥0, ∀ {r : ℕ → ℝ≥0},
      Tendsto r atTop (𝓝 s) →
      (∀ᶠ n in atTop, s < r n) →
      Tendsto (fun n ↦ ∫⁻ ω,
        ‖((finiteEventCountTop ξ (r n) ω : ℝ) -
            integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) (r n) ω) -
          ((finiteEventCountTop ξ s ω : ℝ) -
            integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) s ω)‖ₑ ∂μ)
        atTop (𝓝 0) := by
    intro s r hr hrRight
    exact finiteEvent_centered_rightL1 μ ξ Λ hC hΛnonneg hΛupper hΛint
      hMIntegrable s hr hrRight
  intro s t hst B hB
  have hCentered := setIntegral_eq_of_usualAugmentation_of_rightL1 F₀
    (fun u ω ↦ (finiteEventCountTop ξ u ω : ℝ) -
      integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) u ω)
    hMIntegrable hRawCentered hRightL1 hst hB
  apply (integral_centered_eq_iff_increment_eq
    ((hNIntegrable t).mono_measure Measure.restrict_le_self)
    ((hNIntegrable s).mono_measure Measure.restrict_le_self)
    ((hAIntegrable t).mono_measure Measure.restrict_le_self)
    ((hAIntegrable s).mono_measure Measure.restrict_le_self)
    (fun ω ↦ setIntegral_Ioc_eq_integratedIntensity_one_sub hst (hΛint t ω))).1
  exact hCentered

end OTSelector.CountingProcess
