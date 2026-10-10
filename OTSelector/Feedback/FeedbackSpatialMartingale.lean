import OTSelector.Feedback.FeedbackA1Occupation
import OTSelector.Feedback.FeedbackA1EndpointBridge
import OTSelector.Probability.SpatialMartingaleAverage
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Spatial martingale residuals of the actual finite feedback process

The martingale below is instantiated from the proved finite-event intensities and the actual A1
stopping mask. Spatially separated residual windows are orthogonal by conditional expectation.
-/

open MeasureTheory Set Filter
open scoped NNReal ProbabilityTheory
set_option maxHeartbeats 800000

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- The actual finite bulk Dynkin residual, stopped at the combined A1 localization. -/
noncomputable def safeFeedbackSpatialDynkin
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ) :
    ℝ≥0 → FiniteSample n → ℝ :=
  throughStopClippedDynkinProcess
    (safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T) R f
    (safeK0 lam x0 p0)
    (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
    (safeTargetBulkCount hlam0 hlamHalf B x0 p0)
    (safeSourceBulkRate hlam0 hlamHalf B x0 p0)
    (safeTargetBulkRate hlam0 hlamHalf B x0 p0)

/-- This is the genuine finite-sample martingale; no intensity or Dynkin premise is required. -/
theorem safeFeedbackSpatialDynkin_martingale
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (eta x0 p0 : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ) :
    Martingale (safeFeedbackSpatialDynkin (n := n) hlam0 hlamHalf eta B x0 p0 T R f)
      (usualRevealedFiltration hlam0 hlamHalf x0 p0) (finiteSampleLaw n) := by
  have hp := safeSourceBulkCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf B x0 p0
  have hm := safeTargetBulkCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf B x0 p0
  have hIp := safeSourceBulkCount_hasPredictableIntensity
    (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hIm := safeTargetBulkCount_hasPredictableIntensity
    (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hMask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0 hlamHalf hB eta x0 p0 T
  have hEq : safeFeedbackA1ThroughStopMask (n := n) hlam0 hlamHalf eta B x0 p0 T =
      throughStopMask (safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T) := by
    funext u sample
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask
      hlam0 hlamHalf eta B x0 p0 T u sample
  rw [hEq] at hMask
  exact throughStopClippedDynkinProcess_martingale hp hm
    (safeBulkCounts_noSimultaneousJumpsOn hlam0 hlamHalf B x0 p0)
    hIp hIm (safeK0_stronglyMeasurable_usual_zero hlam0 hlamHalf x0 p0) hMask R f
    (fun t ↦ integratedIntensity_one_integrable_of_bounded
      (feedbackBulkRateCap_nonneg n B)
      (safeSourceBulkRate_le_cap hlam0 hlamHalf B x0 p0) hp hIp t)
    (fun t ↦ integratedIntensity_one_integrable_of_bounded
      (feedbackBulkRateCap_nonneg n B)
      (safeTargetBulkRate_le_cap hlam0 hlamHalf B x0 p0) hm hIm t)

end OTSelector.FiniteSample

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An integrable past-tested martingale increment has mean zero. -/
theorem integral_past_mul_martingale_increment_eq_zero
    {μ : Measure Ω} {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ F] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ℝ≥0} (hst : s ≤ t) {H : Ω → ℝ}
    (hH : StronglyMeasurable[F s] H)
    (hInt : Integrable (fun ω ↦ H ω * (M t ω - M s ω)) μ) :
    (∫ ω, H ω * (M t ω - M s ω) ∂μ) = 0 := by
  have hd : Integrable (fun ω ↦ M t ω - M s ω) μ :=
    (hM.integrable t).sub (hM.integrable s)
  have hzero : μ[(fun ω ↦ M t ω - M s ω) | F s] =ᵐ[μ] 0 := by
    filter_upwards [condExp_sub (hM.integrable t) (hM.integrable s) (F s),
      hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)] with ω hsub ht hs
    simp only [Pi.sub_apply, Pi.zero_apply] at *
    change μ[M t - M s | F s] ω = 0
    rw [hsub, ht, hs, sub_self]
  have hpull := condExp_mul_of_stronglyMeasurable_left hH hInt hd
  calc
    _ = ∫ ω, μ[(fun ω ↦ H ω * (M t ω - M s ω)) | F s] ω ∂μ :=
      (integral_condExp (F.le s)).symm
    _ = 0 := by
      calc
        _ = ∫ _ω : Ω, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hpull, hzero] with ω hp hz
          change μ[H * (fun ω ↦ M t ω - M s ω) | F s] ω = 0
          simpa only [Pi.mul_apply, Pi.zero_apply, hz, mul_zero] using hp
        _ = 0 := by simp

/-- A bounded test of the past multiplied by the next martingale increment. -/
noncomputable def pastWindowResidual (M G : ℝ≥0 → Ω → ℝ) (t x : ℝ≥0) (ω : Ω) : ℝ :=
  G x ω * (M (x + t) ω - M x ω)

/-- Nonoverlapping windows of bounded past-tested martingale increments are orthogonal. -/
theorem integral_pastWindowResidual_mul_eq_zero_of_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ F]
    {M G : ℝ≥0 → Ω → ℝ} (hM : Martingale M F μ) (hG : StronglyAdapted F G)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hGb : ∀ x ω, ‖G x ω‖ ≤ A) (t : ℝ≥0)
    (hMb : ∀ x ω, ‖M (x + t) ω - M x ω‖ ≤ D)
    {x y : ℝ≥0} (hxy : x + t ≤ y) :
    (∫ ω, pastWindowResidual M G t x ω * pastWindowResidual M G t y ω ∂μ) = 0 := by
  have hx : x ≤ y := (le_add_of_nonneg_right (by positivity : (0 : ℝ≥0) ≤ t)).trans hxy
  let H : Ω → ℝ := fun ω ↦ pastWindowResidual M G t x ω * G y ω
  have hH : StronglyMeasurable[F y] H :=
    ((hG x).mono (F.mono hx) |>.mul
      ((hM.stronglyMeasurable (x + t)).mono (F.mono hxy) |>.sub
        ((hM.stronglyMeasurable x).mono (F.mono hx)))).mul (hG y)
  have hbound (ω : Ω) : ‖H ω * (M (y + t) ω - M y ω)‖ ≤ (A * D) ^ 2 := by
    dsimp only [H, pastWindowResidual]
    simp only [norm_mul]
    calc
      _ ≤ (A * D) * A * D := by gcongr; exacts [hGb x ω, hMb x ω, hGb y ω, hMb y ω]
      _ = _ := by ring
  have hInt : Integrable (fun ω ↦ H ω * (M (y + t) ω - M y ω)) μ :=
    Integrable.of_bound
      ((hH.mono (F.le y)).mul
        ((hM.stronglyMeasurable (y + t)).mono (F.le _) |>.sub
          ((hM.stronglyMeasurable y).mono (F.le _)))).aestronglyMeasurable
      ((A * D) ^ 2) (Eventually.of_forall hbound)
  have hz := integral_past_mul_martingale_increment_eq_zero hM
    (show y ≤ y + t from le_add_of_nonneg_right (by positivity)) hH hInt
  simpa only [H, pastWindowResidual, mul_assoc] using hz

end OTSelector.Probability

namespace OTSelector.CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Parameter-dependent compensators are jointly measurable in horizon and sample. -/
theorem measurable_uncurry_integratedIntensity {Λ H : ℝ≥0 → Ω → ℝ}
    (hΛ : Measurable (Function.uncurry Λ)) (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (integratedIntensity Λ H)) := by
  let : SFinite timeMeasure := by unfold timeMeasure; infer_instance
  have hg : Measurable (fun p : (ℝ≥0 × Ω) × ℝ≥0 ↦
      if 0 < p.2 ∧ p.2 ≤ p.1.1 then H p.2 p.1.2 * Λ p.2 p.1.2 else 0) := by
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.fst))
    · exact (hH.comp (measurable_snd.prodMk measurable_fst.snd)).mul
        (hΛ.comp (measurable_snd.prodMk measurable_fst.snd))
    · exact measurable_const
  have hi := (hg.stronglyMeasurable.integral_prod_right' (ν := timeMeasure)).measurable
  convert hi using 1
  funext p
  change integratedIntensity Λ H p.1 p.2 = _
  rw [integratedIntensity, ← integral_indicator measurableSet_Ioc]
  simp only [Set.indicator, mem_Ioc]

/-- Joint measurability of a finite event count follows directly from the event times. -/
theorem measurable_uncurry_finiteEventCountTop {m : ℕ}
    (ξ : Fin m → Ω → WithTop ℝ≥0) (hξ : ∀ i, Measurable (ξ i)) :
    Measurable (Function.uncurry (finiteEventCountTop ξ)) := by
  classical
  change Measurable (fun p : ℝ≥0 × Ω ↦ finiteEventCountTop ξ p.1 p.2)
  simp_rw [finiteEventCountTop_eq_sum]
  exact Finset.measurable_sum _ (fun i _ ↦ Measurable.ite
    (measurableSet_le ((hξ i).comp measurable_snd) measurable_fst.withTop_coe)
    measurable_const measurable_const)

end OTSelector.CountingProcess

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- The actual stopped finite Dynkin process is jointly measurable. -/
theorem measurable_uncurry_safeFeedbackSpatialDynkin
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (eta x0 p0 : ℝ) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ) :
    Measurable (Function.uncurry
      (safeFeedbackSpatialDynkin (n := n) hlam0 hlamHalf eta B x0 p0 T R f)) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  let τ := safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B x0 p0 T
  have hτ : Measurable τ :=
    (safeFeedbackA1StopTime_isStoppingTime hlam0 hlamHalf hB eta x0 p0 T).measurable.mono
      (safeFeedbackA1StopTime_isStoppingTime hlam0 hlamHalf hB eta x0 p0 T).measurableSpace_le le_rfl
  have hp := safeSourceBulkCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf B x0 p0
  have hm := safeTargetBulkCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf B x0 p0
  have hK := safeK0_stronglyMeasurable_usual_zero (n := n) hlam0 hlamHalf x0 p0
  have hKint : Measurable (safeK0 (n := n) lam x0 p0) := by
    simpa only [Int.floor_intCast] using ((hK.mono (F.le 0)).measurable.floor)
  have hNp : Measurable (Function.uncurry (safeSourceBulkCount
      (n := n) hlam0 hlamHalf B x0 p0)) := by
    exact measurable_uncurry_finiteEventCountTop _ (fun i ↦
      (safeSourceBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0 i).measurable.mono
        (safeSourceBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0 i).measurableSpace_le le_rfl)
  have hNm : Measurable (Function.uncurry (safeTargetBulkCount
      (n := n) hlam0 hlamHalf B x0 p0)) := by
    exact measurable_uncurry_finiteEventCountTop _ (fun i ↦
      (safeTargetBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0 i).measurable.mono
        (safeTargetBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0 i).measurableSpace_le le_rfl)
  have hObs : Measurable (Function.uncurry (clippedObservable R f
      (safeK0 (n := n) lam x0 p0) (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
      (safeTargetBulkCount hlam0 hlamHalf B x0 p0))) := by
    exact (measurable_of_countable (fun k : ℤ ↦ f (integerClip R k))).comp
      (((hKint.comp measurable_snd).add ((measurable_of_countable (fun k : ℕ ↦ (k : ℤ))).comp hNp)).sub ((measurable_of_countable (fun k : ℕ ↦ (k : ℤ))).comp hNm))
  have hcut : Measurable (fun p : ℝ≥0 × FiniteSample n ↦
      (min (p.1 : WithTop ℝ≥0) (τ p.2)).untopA) :=
    (measurable_fst.withTop_coe.min (hτ.comp measurable_snd)).untopA
  have hStopObs := hObs.comp (hcut.prodMk measurable_snd)
  have harg0 : Measurable (fun p : ℝ≥0 × FiniteSample n ↦ ((0 : ℝ≥0), p.2)) :=
    measurable_const.prodMk measurable_snd
  have hObs0 := hObs.comp harg0
  have hMask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0 hlamHalf hB eta x0 p0 T
  have hMaskEq : safeFeedbackA1ThroughStopMask (n := n) hlam0 hlamHalf eta B x0 p0 T =
      throughStopMask τ := by
    funext s ω
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0 hlamHalf eta B x0 p0 T s ω
  rw [hMaskEq] at hMask
  have hMp := (hMask.1.mul (clippedUpwardIncrement_boundedPredictable hp hm hK R f).1).mono
    (predictable_le_ambient F)
  have hMm := (hMask.1.mul (clippedDownwardIncrement_boundedPredictable hp hm hK R f).1).mono
    (predictable_le_ambient F)
  have hIp := safeSourceBulkCount_hasPredictableIntensity
    (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hIm := safeTargetBulkCount_hasPredictableIntensity
    (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hHp : Measurable (Function.uncurry (fun s ω ↦ throughStopMask τ s ω *
      clippedUpwardIncrement R f (leftCurrentOfCounts (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) s ω))) := hMp.measurable
  have hHm : Measurable (Function.uncurry (fun s ω ↦ throughStopMask τ s ω *
      clippedDownwardIncrement R f (leftCurrentOfCounts (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) s ω))) := hMm.measurable
  have hAp := measurable_uncurry_integratedIntensity
    (hIp.predictable.mono (predictable_le_ambient F)).measurable hHp
  have hAm := measurable_uncurry_integratedIntensity
    (hIm.predictable.mono (predictable_le_ambient F)).measurable hHm
  exact (hStopObs.sub hObs0).sub (hAp.add hAm)

end OTSelector.FiniteSample

namespace OTSelector.CountingProcess

private theorem timeMeasure_singleton_zero_spatial (a : ℝ≥0) :
    timeMeasure ({a} : Set ℝ≥0) = 0 := by
  rw [timeMeasure, Measure.map_apply measurable_real_toNNReal (measurableSet_singleton a)]
  rw [Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton a))]
  have hpre : Real.toNNReal ⁻¹' ({a} : Set ℝ≥0) ∩ Ici (0 : ℝ) = {(a : ℝ)} := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ici]
    constructor
    · rintro ⟨hx, hx0⟩
      have h := congrArg NNReal.toReal hx
      simpa only [Real.coe_toNNReal x hx0] using h
    · rintro rfl
      exact ⟨Real.toNNReal_coe, a.2⟩
  rw [hpre, Real.volume_singleton]

/-- The right-closed stopping mask has the strict-survival rate bound at almost every time. -/
theorem throughStopMask_rate_bound_ae {τ : WithTop ℝ≥0} {Λ : ℝ≥0 → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hΛ : ∀ s, 0 ≤ Λ s)
    (hb : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) < τ → Λ s ≤ C) :
    ∀ᵐ s : ℝ≥0 ∂timeMeasure, ‖(if (s : WithTop ℝ≥0) ≤ τ then 1 else (0 : ℝ)) * Λ s‖ ≤ C := by
  have hn : ∀ᵐ s ∂timeMeasure, s ≠ τ.untopA :=
    (measure_eq_zero_iff_ae_notMem.mp (timeMeasure_singleton_zero_spatial τ.untopA))
  filter_upwards [hn] with s hs
  by_cases hle : (s : WithTop ℝ≥0) ≤ τ
  · have hlt : (s : WithTop ℝ≥0) < τ := lt_of_le_of_ne hle (by
      intro heq
      apply hs
      have := congrArg WithTop.untopA heq
      simpa only [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] using this)
    simpa only [ite_eq_left hle, one_mul, Real.norm_eq_abs, abs_of_nonneg (hΛ s)] using hb s hlt
  · simp only [ite_eq_right hle, zero_mul, norm_zero]
    exact hC

/-- A uniformly bounded measurable time integrand has uniformly bounded local integral increments. -/
theorem norm_setIntegral_zero_sub_le {g : ℝ≥0 → ℝ} (hg : Measurable g) {C : ℝ}
    (_hC : 0 ≤ C) (hb : ∀ᵐ s ∂timeMeasure, ‖g s‖ ≤ C)
    {u v : ℝ≥0} (huv : u ≤ v) :
    ‖(∫ s in Ioc 0 v, g s ∂timeMeasure) - (∫ s in Ioc 0 u, g s ∂timeMeasure)‖ ≤
      C * ((v : ℝ) - u) := by
  have hi : IntegrableOn g (Ioc 0 v) timeMeasure :=
    (integrableOn_const (C := C) (timeMeasure_Ioc_lt_top 0 v).ne).mono'
      hg.aestronglyMeasurable (ae_restrict_of_ae hb)
  have heq := setIntegral_Ioc_eq_integratedIntensity_one_sub
    (Ω := Unit) (Λ := fun s _ ↦ g s) (ω := ()) huv hi
  simp only [integratedIntensity, one_mul] at heq
  rw [← heq]
  have hnorm := norm_setIntegral_le_of_norm_le_const_ae (timeMeasure_Ioc_lt_top u v)
    (ae_restrict_of_ae hb)
  have hmass : timeMeasure.real (Ioc u v) = (v : ℝ) - u := by
    have hm := congrArg (fun m : Measure ℝ ↦ m.real univ) (map_coe_timeMeasure_restrict u v)
    simpa only [measureReal_def, Measure.map_apply NNReal.continuous_coe.measurable
      MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
      Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (show (u : ℝ) ≤ v from huv))] using hm
  simpa only [hmass] using hnorm

end OTSelector.CountingProcess

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- Actual A1 localization gives uniform upper bounds for both physical finite rates. -/
theorem safeFeedbackSpatial_rates_le_of_lt_stop
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T s : ℝ≥0) (ω : FiniteSample n)
    (hs : (s : WithTop ℝ≥0) < safeFeedbackA1StopTime
      hlam0.le (by linarith) eta B x0 p0 T ω) :
    safeSourceBulkRate hlam0.le (by linarith) B x0 p0 s ω ≤ 3 ∧
      safeTargetBulkRate hlam0.le (by linarith) B x0 p0 s ω ≤ 3 := by
  have hlamHalf : lam < 1 / 2 := by linarith
  have hbulk := lt_safeFeedbackBulkExitTime_of_lt_A1Stop
    hlam0.le hlamHalf eta B x0 p0 T s ω hs
  have hreg := crossingRegularity_of_lt_safeFeedbackA1Stop
    hlam0.le hlamHalf hB heta hetaSmall T s ω hs
  rw [safeSourceBulkRate_eq_feedbackSourceIntensity_of_lt_exit
      hlam0.le hlamHalf hB s ω hbulk,
    safeTargetBulkRate_eq_feedbackTargetIntensity_of_lt_exit
      hlam0.le hlamHalf hB s ω hbulk]
  exact ⟨(sourceTotalRate_bounds hlam0 hlam hreg).2,
    (targetTotalRate_bounds hlam0 hlam hreg).2⟩

end OTSelector.FiniteSample

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- Actual stopped Dynkin increments have a uniform bound independent of the finite sample size. -/
theorem norm_safeFeedbackSpatialDynkin_sub_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hf : ∀ k, ‖f k‖ ≤ Cf)
    {u v : ℝ≥0} (huv : u ≤ v) (ω : FiniteSample n) :
    ‖safeFeedbackSpatialDynkin hlam0.le (by linarith) eta B x0 p0 T R f v ω -
      safeFeedbackSpatialDynkin hlam0.le (by linarith) eta B x0 p0 T R f u ω‖ ≤
      2 * Cf + 12 * Cf * ((v : ℝ) - u) := by
  have hlamHalf : lam < 1 / 2 := by linarith
  let F := usualRevealedFiltration (n := n) hlam0.le hlamHalf x0 p0
  let τ := safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B x0 p0 T
  let Np := safeSourceBulkCount (n := n) hlam0.le hlamHalf B x0 p0
  let Nm := safeTargetBulkCount (n := n) hlam0.le hlamHalf B x0 p0
  let Lp := safeSourceBulkRate (n := n) hlam0.le hlamHalf B x0 p0
  let Lm := safeTargetBulkRate (n := n) hlam0.le hlamHalf B x0 p0
  let k := leftCurrentOfCounts (safeK0 lam x0 p0) Np Nm
  let gp : ℝ≥0 → ℝ := fun s ↦ throughStopMask τ s ω * clippedUpwardIncrement R f (k s ω) * Lp s ω
  let gm : ℝ≥0 → ℝ := fun s ↦ throughStopMask τ s ω * clippedDownwardIncrement R f (k s ω) * Lm s ω
  have hp := safeSourceBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0
  have hm := safeTargetBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0
  have hK := safeK0_stronglyMeasurable_usual_zero (n := n) hlam0.le hlamHalf x0 p0
  have hIp := safeSourceBulkCount_hasPredictableIntensity
    (n := n) (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB
  have hIm := safeTargetBulkCount_hasPredictableIntensity
    (n := n) (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB
  have hMask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have hMaskEq : safeFeedbackA1ThroughStopMask (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      throughStopMask τ := by
    funext s ω
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0.le hlamHalf eta B x0 p0 T s ω
  rw [hMaskEq] at hMask
  have harg : Measurable (fun s : ℝ≥0 ↦ (s, ω)) := measurable_id.prodMk measurable_const
  have hmp : Measurable gp := by
    have hj := ((hMask.1.mul (clippedUpwardIncrement_boundedPredictable hp hm hK R f).1).mul
      hIp.predictable).mono (predictable_le_ambient F)
    have hc := hj.measurable.comp harg
    exact hc
  have hmm : Measurable gm := by
    have hj := ((hMask.1.mul (clippedDownwardIncrement_boundedPredictable hp hm hK R f).1).mul
      hIm.predictable).mono (predictable_le_ambient F)
    have hc := hj.measurable.comp harg
    exact hc
  have hUp (s : ℝ≥0) : ‖clippedUpwardIncrement R f (k s ω)‖ ≤ 2 * Cf := by
    change ‖f (integerClip R (k s ω + 1)) - f (integerClip R (k s ω))‖ ≤ _
    calc
      _ ≤ Cf + Cf := (norm_sub_le _ _).trans (add_le_add (hf _) (hf _))
      _ = _ := by ring
  have hDown (s : ℝ≥0) : ‖clippedDownwardIncrement R f (k s ω)‖ ≤ 2 * Cf := by
    change ‖f (integerClip R (k s ω - 1)) - f (integerClip R (k s ω))‖ ≤ _
    calc
      _ ≤ Cf + Cf := (norm_sub_le _ _).trans (add_le_add (hf _) (hf _))
      _ = _ := by ring
  have hpb := throughStopMask_rate_bound_ae (τ := τ ω) (C := 3) (by norm_num)
    (fun s ↦ hIp.nonneg s ω) (fun s hs ↦
      (safeFeedbackSpatial_rates_le_of_lt_stop hlam0 hlam hB heta hetaSmall T s ω hs).1)
  have hmb := throughStopMask_rate_bound_ae (τ := τ ω) (C := 3) (by norm_num)
    (fun s ↦ hIm.nonneg s ω) (fun s hs ↦
      (safeFeedbackSpatial_rates_le_of_lt_stop hlam0 hlam hB heta hetaSmall T s ω hs).2)
  have hgp : ∀ᵐ s ∂timeMeasure, ‖gp s‖ ≤ 6 * Cf := by
    filter_upwards [hpb] with s hs
    have heq : gp s = clippedUpwardIncrement R f (k s ω) * (throughStopMask τ s ω * Lp s ω) := by
      dsimp [gp]; ring
    rw [heq, norm_mul]
    exact (mul_le_mul (hUp s) hs (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hgm : ∀ᵐ s ∂timeMeasure, ‖gm s‖ ≤ 6 * Cf := by
    filter_upwards [hmb] with s hs
    have heq : gm s = clippedDownwardIncrement R f (k s ω) * (throughStopMask τ s ω * Lm s ω) := by
      dsimp [gm]; ring
    rw [heq, norm_mul]
    exact (mul_le_mul (hDown s) hs (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hap := norm_setIntegral_zero_sub_le hmp (by positivity : 0 ≤ 6 * Cf) hgp huv
  have ham := norm_setIntegral_zero_sub_le hmm (by positivity : 0 ≤ 6 * Cf) hgm huv
  let O := stoppedProcess (clippedObservable R f (safeK0 lam x0 p0) Np Nm) τ
  have hO (s : ℝ≥0) : ‖O s ω‖ ≤ Cf := hf _
  have heq : safeFeedbackSpatialDynkin hlam0.le hlamHalf eta B x0 p0 T R f v ω -
      safeFeedbackSpatialDynkin hlam0.le hlamHalf eta B x0 p0 T R f u ω =
      (O v ω - O u ω) -
      (((∫ s in Ioc 0 v, gp s ∂timeMeasure) - (∫ s in Ioc 0 u, gp s ∂timeMeasure)) +
        ((∫ s in Ioc 0 v, gm s ∂timeMeasure) - (∫ s in Ioc 0 u, gm s ∂timeMeasure))) := by
    dsimp [safeFeedbackSpatialDynkin, throughStopClippedDynkinProcess,
      throughStopClippedGeneratorCompensator, integratedIntensity, gp, gm, O, k, τ, Np, Nm, Lp, Lm]
    ring
  rw [heq]
  calc
    _ ≤ (‖O v ω‖ + ‖O u ω‖) +
        (‖(∫ s in Ioc 0 v, gp s ∂timeMeasure) - (∫ s in Ioc 0 u, gp s ∂timeMeasure)‖ +
          ‖(∫ s in Ioc 0 v, gm s ∂timeMeasure) - (∫ s in Ioc 0 u, gm s ∂timeMeasure)‖) :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_add_le _ _))
    _ ≤ _ := by linarith [hO v, hO u]

end OTSelector.FiniteSample

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Extend a local future residual by zero to negative spatial roots. -/
noncomputable def spatialWindowResidual (M G : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (x : ℝ) (ω : Ω) : ℝ :=
  if 0 ≤ x then pastWindowResidual M G t x.toNNReal ω else 0

/-- Spatial averaging of actual past-tested martingale increments, with all separated-window
orthogonality proved from the martingale property. -/
theorem integral_sq_average_spatialWindowResidual_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ F]
    {M G : ℝ≥0 → Ω → ℝ} (hM : Martingale M F μ)
    (hMm : Measurable (Function.uncurry M)) (hG : StronglyAdapted F G)
    (hGm : Measurable (Function.uncurry G))
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hGb : ∀ x ω, ‖G x ω‖ ≤ A) (t : ℝ≥0)
    (hMb : ∀ x ω, ‖M (x + t) ω - M x ω‖ ≤ D)
    {a b : ℝ} (hab : a < b) :
    (∫ ω, ((b - a)⁻¹ * ∫ x in Ioc a b, spatialWindowResidual M G t x ω) ^ 2 ∂μ) ≤
      2 * (t : ℝ) * (A * D) ^ 2 / (b - a) := by
  have harg : Measurable (fun p : ℝ × Ω ↦ (p.1.toNNReal, p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  have hargt : Measurable (fun p : ℝ × Ω ↦ (p.1.toNNReal + t, p.2)) :=
    ((measurable_real_toNNReal.comp measurable_fst).add_const t).prodMk measurable_snd
  have hX : Measurable (Function.uncurry (spatialWindowResidual M G t)) := by
    exact Measurable.ite (measurableSet_le measurable_const measurable_fst)
      ((hGm.comp harg).mul ((hMm.comp hargt).sub (hMm.comp harg))) measurable_const
  have hb (x : ℝ) (ω : Ω) : ‖spatialWindowResidual M G t x ω‖ ≤ A * D := by
    unfold spatialWindowResidual
    split_ifs with hx
    · rw [pastWindowResidual, norm_mul]
      exact mul_le_mul (hGb _ _) (hMb _ _) (norm_nonneg _) hA
    · simpa only [norm_zero] using mul_nonneg hA hD
  have hs (x y : ℝ) (hsep : (t : ℝ) ≤ |x - y|) :
      (∫ ω, spatialWindowResidual M G t x ω * spatialWindowResidual M G t y ω ∂μ) = 0 := by
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · simp only [spatialWindowResidual, ite_eq_left hx, ite_eq_left hy]
        rcases le_total x y with hxy | hyx
        · have horder : x.toNNReal + t ≤ y.toNNReal := by
            change (x.toNNReal : ℝ) + (t : ℝ) ≤ (y.toNNReal : ℝ)
            rw [Real.coe_toNNReal x hx, Real.coe_toNNReal y hy]
            rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hsep
            linarith
          exact integral_pastWindowResidual_mul_eq_zero_of_le hM hG hA hD hGb t hMb horder
        · have horder : y.toNNReal + t ≤ x.toNNReal := by
            change (y.toNNReal : ℝ) + (t : ℝ) ≤ (x.toNNReal : ℝ)
            rw [Real.coe_toNNReal x hx, Real.coe_toNNReal y hy]
            rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hsep
            linarith
          simpa only [mul_comm] using
            integral_pastWindowResidual_mul_eq_zero_of_le hM hG hA hD hGb t hMb horder
      · simp [spatialWindowResidual, hy]
    · simp [spatialWindowResidual, hx]
  exact integral_sq_spatialAverage_le μ hX (mul_nonneg hA hD) t.2 hab hb hs

end OTSelector.Probability

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- The original finite-sample law satisfies the uniform inverse-window residual bound. All
martingale, intensity, time-measurability, and separated-window identities are discharged. -/
theorem safeFeedbackSpatialDynkin_average_sq_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0) (R : ℕ) (f : ℤ → ℝ)
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hf : ∀ k, ‖f k‖ ≤ Cf)
    (G : ℝ≥0 → FiniteSample n → ℝ)
    (hG : StronglyAdapted (usualRevealedFiltration hlam0.le (by linarith) x0 p0) G)
    (hGm : Measurable (Function.uncurry G))
    {CG : ℝ} (hCG : 0 ≤ CG) (hGb : ∀ x ω, ‖G x ω‖ ≤ CG)
    (t : ℝ≥0) {a b : ℝ} (hab : a < b) :
    (∫ ω, ((b - a)⁻¹ * ∫ x in Ioc a b,
      Probability.spatialWindowResidual
        (safeFeedbackSpatialDynkin hlam0.le (by linarith) eta B x0 p0 T R f) G t x ω) ^ 2
          ∂(finiteSampleLaw n)) ≤
      2 * (t : ℝ) * (CG * (2 * Cf + 12 * Cf * t)) ^ 2 / (b - a) := by
  apply Probability.integral_sq_average_spatialWindowResidual_le
    (safeFeedbackSpatialDynkin_martingale hlam0.le (by linarith) hn hB eta x0 p0 T R f)
    (measurable_uncurry_safeFeedbackSpatialDynkin hlam0.le (by linarith) hn hB eta x0 p0 T R f)
    hG hGm hCG (by positivity) hGb t ?_ hab
  intro x ω
  have h := norm_safeFeedbackSpatialDynkin_sub_le (x0 := x0) (p0 := p0) hlam0 hlam hn hB heta hetaSmall T R f hCf hf
    (u := x) (v := x + t) (le_add_of_nonneg_right (by positivity)) ω
  simpa only [NNReal.coe_add, add_sub_cancel_left] using h

end OTSelector.FiniteSample

namespace OTSelector.FiniteSample

variable {lam eta : ℝ}

/-- For any growing root windows, the original finite stopped residual tends to zero in mean
square. The bound is uniform over sample sizes, localization horizons, and clipping radii. -/
theorem tendsto_safeFeedbackSpatialDynkin_average_sq_zero
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam)
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j)
    (B x0 p0 : ℕ → ℝ) (hB : ∀ j, 0 < B j) (T : ℕ → ℝ≥0) (R : ℕ → ℕ)
    (f : ℤ → ℝ) {Cf : ℝ} (hCf : 0 ≤ Cf) (hf : ∀ k, ‖f k‖ ≤ Cf)
    (G : ∀ j, ℝ≥0 → FiniteSample (N j) → ℝ)
    (hG : ∀ j, StronglyAdapted
      (usualRevealedFiltration hlam0.le (by linarith) (x0 j) (p0 j)) (G j))
    (hGm : ∀ j, Measurable (Function.uncurry (G j)))
    {CG : ℝ} (hCG : 0 ≤ CG) (hGb : ∀ j x ω, ‖G j x ω‖ ≤ CG)
    (t : ℝ≥0) (a b : ℕ → ℝ) (hab : ∀ j, a j < b j)
    (hwidth : Tendsto (fun j ↦ b j - a j) atTop atTop) :
    Tendsto (fun j ↦ ∫ ω, ((b j - a j)⁻¹ * ∫ x in Ioc (a j) (b j),
      Probability.spatialWindowResidual
        (safeFeedbackSpatialDynkin hlam0.le (by linarith) eta (B j) (x0 j) (p0 j)
          (T j) (R j) f) (G j) t x ω) ^ 2 ∂(finiteSampleLaw (N j))) atTop (nhds 0) := by
  apply squeeze_zero
    (fun j ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    (fun j ↦ safeFeedbackSpatialDynkin_average_sq_le
      hlam0 hlam (hN j) (hB j) heta hetaSmall (T j) (R j) f hCf hf
      (G j) (hG j) (hGm j) hCG (hGb j) t (hab j))
  exact hwidth.const_div_atTop _

end OTSelector.FiniteSample

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- At the actual finite cutoff, the observable and both jump increments are completely
unclipped. Thus the spatial estimate concerns the original finite counting current. -/
theorem safeFeedbackSpatialDynkin_eq_unclipped
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B x0 p0 : ℝ) (T : ℝ≥0) (f : ℤ → ℝ) (t : ℝ≥0) (ω : FiniteSample n) :
    let τ := safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B x0 p0 T
    let K := currentOfCounts (safeK0 lam x0 p0)
      (safeSourceBulkCount hlam0 hlamHalf B x0 p0) (safeTargetBulkCount hlam0 hlamHalf B x0 p0)
    let Km := leftCurrentOfCounts (safeK0 lam x0 p0)
      (safeSourceBulkCount hlam0 hlamHalf B x0 p0) (safeTargetBulkCount hlam0 hlamHalf B x0 p0)
    safeFeedbackSpatialDynkin hlam0 hlamHalf eta B x0 p0 T (feedbackA1CurrentCutoff n) f t ω =
      stoppedProcess (fun s ω ↦ f (K s ω)) τ t ω - f (K 0 ω) -
        (integratedIntensity (safeSourceBulkRate hlam0 hlamHalf B x0 p0)
          (fun s ω ↦ throughStopMask τ s ω * (f (Km s ω + 1) - f (Km s ω))) t ω +
        integratedIntensity (safeTargetBulkRate hlam0 hlamHalf B x0 p0)
          (fun s ω ↦ throughStopMask τ s ω * (f (Km s ω - 1) - f (Km s ω))) t ω) := by
  dsimp only
  have hobs : clippedObservable (feedbackA1CurrentCutoff n) f (safeK0 lam x0 p0)
      (safeSourceBulkCount (n := n) hlam0 hlamHalf B x0 p0)
      (safeTargetBulkCount hlam0 hlamHalf B x0 p0) =
      fun s ω ↦ f (currentOfCounts (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0) (safeTargetBulkCount hlam0 hlamHalf B x0 p0) s ω) := by
    funext s ω
    have hi := currentOfSafeBulkCounts_strictInterior_post hlam0 hlamHalf B x0 p0 s ω
    exact congrArg f (integerClip_eq_self_of_strictInterior _ hi.1 hi.2)
  have hup (s : ℝ≥0) (ω : FiniteSample n) :
      clippedUpwardIncrement (feedbackA1CurrentCutoff n) f
        (leftCurrentOfCounts (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0) (safeTargetBulkCount hlam0 hlamHalf B x0 p0) s ω) =
      f (leftCurrentOfCounts (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0) (safeTargetBulkCount hlam0 hlamHalf B x0 p0) s ω + 1) -
        f (leftCurrentOfCounts (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0) (safeTargetBulkCount hlam0 hlamHalf B x0 p0) s ω) := by
    have hi := leftCurrentOfSafeBulkCounts_strictInterior hlam0 hlamHalf B x0 p0 s ω
    rw [clippedUpwardIncrement, integerClip_succ_eq_self_of_strictInterior _ hi.1 hi.2,
      integerClip_eq_self_of_strictInterior _ hi.1 hi.2]
  have hdown (s : ℝ≥0) (ω : FiniteSample n) :
      clippedDownwardIncrement (feedbackA1CurrentCutoff n) f
        (leftCurrentOfCounts (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0) (safeTargetBulkCount hlam0 hlamHalf B x0 p0) s ω) =
      f (leftCurrentOfCounts (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0) (safeTargetBulkCount hlam0 hlamHalf B x0 p0) s ω - 1) -
        f (leftCurrentOfCounts (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0) (safeTargetBulkCount hlam0 hlamHalf B x0 p0) s ω) := by
    have hi := leftCurrentOfSafeBulkCounts_strictInterior hlam0 hlamHalf B x0 p0 s ω
    rw [clippedDownwardIncrement, integerClip_pred_eq_self_of_strictInterior _ hi.1 hi.2,
      integerClip_eq_self_of_strictInterior _ hi.1 hi.2]
  simp only [safeFeedbackSpatialDynkin, throughStopClippedDynkinProcess,
    throughStopClippedGeneratorCompensator, hobs, hup, hdown]

end OTSelector.FiniteSample
