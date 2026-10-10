import OTSelector.Feedback.FeedbackMarkedSceneReadout
import OTSelector.Feedback.FeedbackVanishingRegularity
import OTSelector.Feedback.FeedbackGraphPrimitive
import OTSelector.Probability.CountingProcess.ShiftedTimeMeasure

/-! # The actual environment drift is the vanishing-error limit of the finite marked drift -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal Topology
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector

namespace Limit

/-- A bounded mark test has a uniformly bounded ideal feedback rate. -/
theorem norm_feedbackEnvironmentMarkRate_le_two_mul
    {lam C : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1/2)
    (b : Bool) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (_hC : 0 ≤ C)
    (hbound : ∀u, ‖ψ u‖ ≤ C) (k : ℤ) :
    ‖feedbackEnvironmentMarkRate lam b ψ k‖ ≤ 2*C := by
  have hq : |lam * currentSign k| ≤ lam := by
    rw [← feedbackSlope_intCast]
    exact abs_feedbackSlope_le hlam0
  have hs := norm_sourceFeedbackMarkMean_le hlam0 hlam hq ψ hψ hbound
  have ht := norm_targetFeedbackMarkMean_le hlam0 hlam hq ψ hψ hbound
  have hq' := abs_le.mp hq
  cases b
  · change ‖deathRate lam k * targetFeedbackMarkMean (lam*currentSign k) ψ‖ ≤ _
    rw [norm_mul]
    have hb : ‖deathRate lam k‖ ≤ 2 := by
      rw [Real.norm_eq_abs, abs_le]
      unfold deathRate
      constructor <;> nlinarith
    exact mul_le_mul hb ht (norm_nonneg _) (by norm_num)
  · change ‖birthRate lam k * sourceFeedbackMarkMean (lam*currentSign k) ψ‖ ≤ _
    rw [norm_mul]
    have hb : ‖birthRate lam k‖ ≤ 2 := by
      rw [Real.norm_eq_abs, abs_le]
      unfold birthRate
      constructor <;> nlinarith
    exact mul_le_mul hb hs (norm_nonneg _) (by norm_num)

end Limit
namespace FiniteSample
open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- On the original VC event, an auxiliary shrinking tolerance controls the real predictable
residual densities; the original stopping tolerance is kept unchanged. -/
theorem crossingRegularity_of_vc_survival_with_tolerance
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (hn : 4 ≤ n)
    {eta eps B : ℝ} (heps : 0 ≤ eps) (hepsSmall : eps*(2+lam) ≤ lam) (hB : 0 < B)
    (T u : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample ∈ feedbackA1GoodEvent n lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hu : u < T)
    (hsqrt : 4*(33280:ℝ)^2*Real.log n ≤ eps^2*(13*B/16))
    (hlinear : 2*(33280:ℝ)*Real.log n ≤ eps*(13*B/16)) :
    CrossingRegularity lam eps
      (safeSourceUnclippedResidualDensityAt hlam0 hlamHalf B 0 u sample)
      (safeTargetUnclippedResidualDensityAt hlam0 hlamHalf B 0 u sample) := by
  have hbulk : (u : WithTop ℝ≥0) < safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
    apply (WithTop.coe_lt_coe.mpr hu).trans_le
    rw [← hstop]
    exact min_le_left _ _
  have hreg := min_bulkExit_horizon_le_regularityExitTime_of_feedback_good hn hlam0 hlamHalf
    heps hB B 0 T sample hgood.1 hgood.2 hsqrt hlinear
  apply crossingRegularity_of_lt_safeFeedbackRegularityExitTime hlam0 hlamHalf hB heps hepsSmall
    u sample (feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 u sample hbulk)
  exact (lt_min hbulk (WithTop.coe_lt_coe.mpr hu)).trans_le hreg

/-- The actual finite marked drift, with the original physical rate and predictable mark mean. -/
noncomputable def safeBulkMarkedDrift
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (B x0 p0 : ℝ)
    (b : Bool) (ψ : UnitMark → ℝ) (u : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  if b then safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample *
      sourceFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ
  else safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample *
      targetFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ

/-- Actual VC regularity controls the marked drift error by the shrinking tolerance. -/
theorem norm_safeBulkMarkedDrift_sub_environmentMarkRate_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (hn : 4 ≤ n)
    {eta eps B C : ℝ} (heps : 0 ≤ eps) (hepsSmall : eps*(2+lam) ≤ lam) (hB : 0 < B)
    (T u : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample ∈ feedbackA1GoodEvent n lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hu : u < T)
    (hsqrt : 4*(33280:ℝ)^2*Real.log n ≤ eps^2*(13*B/16))
    (hlinear : 2*(33280:ℝ)*Real.log n ≤ eps*(13*B/16))
    (b : Bool) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hC : 0 ≤ C) (hbound : ∀v, ‖ψ v‖ ≤ C) :
    ‖safeBulkMarkedDrift hlam0 hlamHalf B B 0 b ψ u sample -
      Limit.feedbackEnvironmentMarkRate lam b ψ (safePreCurrentAt hlam0 hlamHalf B 0 u sample)‖ ≤
        2*C*eps := by
  have hreg := crossingRegularity_of_vc_survival_with_tolerance hlam0 hlamHalf hn heps hepsSmall
    hB T u sample hgood hstop hu hsqrt hlinear
  have hexit : (u : WithTop ℝ≥0) < safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
    apply (WithTop.coe_lt_coe.mpr hu).trans_le
    rw [← hstop]
    exact min_le_left _ _
  have hrate := Limit.norm_feedbackEnvironmentMarkRate_le_two_mul hlam0 hlamHalf b ψ hψ hC hbound
    (safePreCurrentAt hlam0 hlamHalf B 0 u sample)
  have heq : safePreFeedbackSlope hlam0 hlamHalf B 0 u sample =
      lam * Limit.currentSign (safePreCurrentAt hlam0 hlamHalf B 0 u sample) :=
    feedbackSlope_intCast _ _
  cases b
  · have hr : ‖safeTargetUnclippedResidualDensityAt hlam0 hlamHalf B 0 u sample - 1‖ ≤ eps := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hreg.target_lower], by linarith [hreg.target_upper]⟩
    have hd : safeBulkMarkedDrift hlam0 hlamHalf B B 0 false ψ u sample -
        Limit.feedbackEnvironmentMarkRate lam false ψ (safePreCurrentAt hlam0 hlamHalf B 0 u sample) =
      (safeTargetUnclippedResidualDensityAt hlam0 hlamHalf B 0 u sample - 1) *
        Limit.feedbackEnvironmentMarkRate lam false ψ (safePreCurrentAt hlam0 hlamHalf B 0 u sample) := by
      simp only [safeBulkMarkedDrift, Bool.false_eq_true, ite_false, Limit.feedbackEnvironmentMarkRate]
      rw [safeTargetBulkRate_eq_safeTargetUnclippedRateAt_of_lt_exit hlam0 hlamHalf hB u sample hexit]
      simp only [safeTargetUnclippedRateAt, targetTotalRate, heq, Limit.deathRate]
      ring
    rw [hd, norm_mul]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul hr hrate (norm_nonneg _) heps
  · have hr : ‖safeSourceUnclippedResidualDensityAt hlam0 hlamHalf B 0 u sample - 1‖ ≤ eps := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hreg.source_lower], by linarith [hreg.source_upper]⟩
    have hd : safeBulkMarkedDrift hlam0 hlamHalf B B 0 true ψ u sample -
        Limit.feedbackEnvironmentMarkRate lam true ψ (safePreCurrentAt hlam0 hlamHalf B 0 u sample) =
      (safeSourceUnclippedResidualDensityAt hlam0 hlamHalf B 0 u sample - 1) *
        Limit.feedbackEnvironmentMarkRate lam true ψ (safePreCurrentAt hlam0 hlamHalf B 0 u sample) := by
      simp only [safeBulkMarkedDrift, ite_true, Limit.feedbackEnvironmentMarkRate]
      rw [safeSourceBulkRate_eq_safeSourceUnclippedRateAt_of_lt_exit hlam0 hlamHalf hB u sample hexit]
      simp only [safeSourceUnclippedRateAt, sourceTotalRate, heq, Limit.birthRate]
      ring
    rw [hd, norm_mul]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul hr hrate (norm_nonneg _) heps

/-- Unified colour readout of the actual stopped geometric-mark martingales. -/
noncomputable def safeColorSpatialMarkedCompensator
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    (b : Bool) (ψ : UnitMark → ℝ) : ℝ≥0 → FiniteSample n → ℝ :=
  if b then safeSourceSpatialMarkedCompensator hlam0 hlamHalf eta B B 0 T ψ
  else safeTargetSpatialMarkedCompensator hlam0 hlamHalf eta B B 0 T ψ

private theorem safeBulkMarkedDrift_integrableOn
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (hn : 0 < n)
    {B C : ℝ} (hB : 0 < B) (b : Bool) (ψ : UnitMark → ℝ) (hψ : Continuous ψ)
    (hC : 0 ≤ C) (hbound : ∀ v, ‖ψ v‖ ≤ C) (v : ℝ≥0) (sample : FiniteSample n) :
    IntegrableOn (fun u ↦ safeBulkMarkedDrift hlam0 hlamHalf B B 0 b ψ u sample)
      (Ioc 0 v) timeMeasure := by
  cases b
  · have hi := safeTargetBulkCount_hasPredictableIntensity (n := n) (x0 := B) (p0 := 0)
      hlam0 hlamHalf hn hB
    have hm := targetFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
      (n := n) hlam0 hlamHalf B 0 ψ hψ hC hbound
    simpa only [safeBulkMarkedDrift, Bool.false_eq_true, ite_false, mul_comm] using
      hm.isBoundedPredictable.integrableOn_mul_intensity hi v sample
  · have hi := safeSourceBulkCount_hasPredictableIntensity (n := n) (x0 := B) (p0 := 0)
      hlam0 hlamHalf hn hB
    have hm := sourceFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
      (n := n) hlam0 hlamHalf B 0 ψ hψ hC hbound
    simpa only [safeBulkMarkedDrift, ite_true, mul_comm] using
      hm.isBoundedPredictable.integrableOn_mul_intensity hi v sample

private theorem environmentMarkRate_pre_integrableOn
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (B : ℝ)
    (b : Bool) (ψ : UnitMark → ℝ) (v : ℝ≥0) (sample : FiniteSample n) :
    IntegrableOn (fun u ↦ Limit.feedbackEnvironmentMarkRate lam b ψ
      (safePreCurrentAt hlam0 hlamHalf B 0 u sample)) (Ioc 0 v) timeMeasure := by
  have hm := (measurable_of_countable (Limit.feedbackEnvironmentMarkRate lam b ψ)).comp
    (sample.measurable_safeCurrentAt_time hlam0 hlamHalf B 0)
  have hi : IntegrableOn (fun u ↦ Limit.feedbackEnvironmentMarkRate lam b ψ
      (safeCurrentAt hlam0 hlamHalf B 0 u sample)) (Ioc 0 v) timeMeasure :=
    (integrableOn_const (C := Limit.feedbackEnvironmentMarkRateBound lam b ψ)
      (timeMeasure_Ioc_lt_top 0 v).ne).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ Limit.norm_feedbackEnvironmentMarkRate_le lam b ψ _)
  apply hi.congr
  filter_upwards [ae_restrict_of_ae (safePreCurrentAt_ae_eq_safeCurrentAt hlam0 hlamHalf B 0 sample)]
    with u hu
  exact congrArg _ hu.symm

/-- The original environment drift is the integral of the actual predictable current; the
pre/post distinction disappears only after removing the finitely many event times. -/
theorem integral_environmentMarkRate_pre_eq_stoppedScene
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T s t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (ht : s+t ≤ T) (b : Bool) (ψ : UnitMark → ℝ) :
    (∫ u in Ioc s (s+t), Limit.feedbackEnvironmentMarkRate lam b ψ
      (safePreCurrentAt hlam0 hlamHalf B 0 u sample) ∂timeMeasure) =
      ∫ x in 0..(t:ℝ), Limit.feedbackEnvironmentMarkRate lam b ψ
        (Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment
          (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+(s:ℝ)))) x) := by
  let e := Matching.feedbackSceneEnvironment
    (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+(s:ℝ)))
  let g := fun x ↦ Limit.feedbackEnvironmentMarkRate lam b ψ (Limit.feedbackEnvironmentCurrent e x)
  calc
    _ = ∫ u in Ioc s (s+t), g (-(s:ℝ)+(u:ℝ)) ∂timeMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (safePreCurrentAt_ae_eq_safeCurrentAt hlam0 hlamHalf B 0 sample)] with u hu hp
      rw [hp]
      dsimp [g, e]
      rw [feedbackEnvironmentCurrent_stoppedScene_eq_safeCurrentAt hlam0 hlamHalf eta B T u
        sample hNoTie hstop (hu.2.trans ht) (B+(s:ℝ)) (-(s:ℝ)+(u:ℝ)) (by ring)]
    _ = _ := by
      rw [integral_shifted_timeMeasure_eq_intervalIntegral g (-(s:ℝ)) s (s+t)
        (le_add_of_nonneg_right t.2)]
      simp only [NNReal.coe_add, neg_add_cancel, neg_add_cancel_left]
      rfl

private theorem marked_timeMeasure_real_Ioc_add (s t : ℝ≥0) :
    timeMeasure.real (Ioc s (s+t)) = (t:ℝ) := by
  have h := integral_timeMeasure_eq_intervalIntegral (fun _ ↦ (1:ℝ)) s (s+t)
    (le_add_of_nonneg_right t.2)
  simpa only [integral_const, smul_eq_mul, mul_one, intervalIntegral.integral_const, measureReal_def, Measure.restrict_apply_univ,
    NNReal.coe_add, add_sub_cancel_left] using h

/-- The true environment compensator differs from the stopped finite marked martingale by an
explicit vanishing regularity error, on the original sample's survival and VC event. -/
theorem norm_environmentMarkedCompensator_stoppedScene_sub_martingale_increment_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (hn : 4 ≤ n)
    {eta eps B C : ℝ} (heps : 0 ≤ eps) (hepsSmall : eps*(2+lam) ≤ lam) (hB : 0 < B)
    (T s t : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample ∈ feedbackA1GoodEvent n lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (ht : s+t < T)
    (hsqrt : 4*(33280:ℝ)^2*Real.log n ≤ eps^2*(13*B/16))
    (hlinear : 2*(33280:ℝ)*Real.log n ≤ eps*(13*B/16))
    (b : Bool) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hC : 0 ≤ C) (hbound : ∀v, ‖ψ v‖ ≤ C) :
    ‖Limit.feedbackEnvironmentMarkedCompensator lam b ψ t (Matching.feedbackSceneEnvironment
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+(s:ℝ)))) -
      (safeColorSpatialMarkedCompensator hlam0 hlamHalf eta B T b ψ (s+t) sample -
        safeColorSpatialMarkedCompensator hlam0 hlamHalf eta B T b ψ s sample)‖ ≤
      2*C*eps*(t:ℝ) := by
  have hst : s ≤ s+t := le_add_of_nonneg_right t.2
  have hn0 : 0 < n := by omega
  have hfin := safeBulkMarkedDrift_integrableOn hlam0 hlamHalf hn0 hB b ψ hψ hC hbound (s+t) sample
  have hideal := environmentMarkRate_pre_integrableOn hlam0 hlamHalf B b ψ (s+t) sample
  have hsub : Ioc s (s+t) ⊆ Ioc (0:ℝ≥0) (s+t) :=
    fun _ hu ↦ ⟨lt_of_le_of_lt (zero_le : (0:ℝ≥0) ≤ s) hu.1, hu.2⟩
  have hnorm : ‖∫ u in Ioc s (s+t), safeBulkMarkedDrift hlam0 hlamHalf B B 0 b ψ u sample -
      Limit.feedbackEnvironmentMarkRate lam b ψ (safePreCurrentAt hlam0 hlamHalf B 0 u sample)
        ∂timeMeasure‖ ≤ 2*C*eps*(t:ℝ) := by
    have h := norm_setIntegral_le_of_norm_le_const (timeMeasure_Ioc_lt_top s (s+t))
      (fun u hu ↦ norm_safeBulkMarkedDrift_sub_environmentMarkRate_le hlam0 hlamHalf hn
        heps hepsSmall hB T u sample hgood hstop (hu.2.trans_lt ht) hsqrt hlinear b ψ hψ hC hbound)
    simpa only [marked_timeMeasure_real_Ioc_add] using h
  have hid := integral_environmentMarkRate_pre_eq_stoppedScene hlam0 hlamHalf eta B T s t
    sample hgood.1 hstop ht.le b ψ
  rw [integral_sub (hfin.mono_set hsub) (hideal.mono_set hsub), hid] at hnorm
  have heq := setIntegral_Ioc_eq_integratedIntensity_one_sub (Ω := Unit)
    (Λ := fun u _ ↦ safeBulkMarkedDrift hlam0 hlamHalf B B 0 b ψ u sample) (ω := ()) hst hfin
  simp only [integratedIntensity, one_mul] at heq
  rw [heq] at hnorm
  have hle (u : ℝ≥0) (hu : u ≤ s+t) : (u : WithTop ℝ≥0) ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample := by
    rw [hstop]
    exact WithTop.coe_le_coe.mpr (hu.trans ht.le)
  cases b
  · rw [Limit.feedbackEnvironmentMarkedCompensator,
      firstEventTestCount_target_stoppedScene_eq_markSum_increment hlam0 hlamHalf eta B T s t sample hgood.1 hstop ht ψ]
    simp only [safeColorSpatialMarkedCompensator, Bool.false_eq_true, ite_false,
      safeTargetSpatialMarkedCompensator]
    rw [stoppedProcess_eq_of_le (hle _ le_rfl), stoppedProcess_eq_of_le (hle _ hst)]
    simp only [safeTargetBulkMarkedCompensator, integratedIntensity]
    simp only [safeBulkMarkedDrift, Bool.false_eq_true, ite_false, mul_comm] at hnorm
    convert hnorm using 1 <;> first | (solve | ring) | (congr 1; simp_rw [mul_comm]; ring)
  · rw [Limit.feedbackEnvironmentMarkedCompensator,
      firstEventTestCount_source_stoppedScene_eq_markSum_increment hlam0 hlamHalf eta B T s t sample hgood.1 hstop ht ψ]
    simp only [safeColorSpatialMarkedCompensator, ite_true, safeSourceSpatialMarkedCompensator]
    rw [stoppedProcess_eq_of_le (hle _ le_rfl), stoppedProcess_eq_of_le (hle _ hst)]
    simp only [safeSourceBulkMarkedCompensator, integratedIntensity]
    simp only [safeBulkMarkedDrift, ite_true, mul_comm] at hnorm
    convert hnorm using 1 <;> first | (solve | ring) | (congr 1; simp_rw [mul_comm]; ring)

/-- On actual survival, the graph in the rooted environment is exactly the integral of
its own current feedback velocity. This identity has no regularity-error term. -/
theorem feedbackEnvironmentGraph_stoppedScene_eq_integral_current
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T s t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hst : s+t ≤ T) :
    (Matching.feedbackSceneEnvironment
      (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+(s:ℝ)))).path.graphHeight t =
      ∫u in (0:ℝ)..(t:ℝ), lam * Limit.currentSign
        (Limit.feedbackEnvironmentCurrent (Matching.feedbackSceneEnvironment
          (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+(s:ℝ)))) u) := by
  have hst' : (s:ℝ)+(t:ℝ) ≤ (T:ℝ) := by exact_mod_cast hst
  have hp := sample.stoppedContinuationFeedbackGraph_curve_sub_eq_integral_safeCurrentAt
    hlam0 hlamHalf eta B T hstop hNoTie s.2
    (le_add_of_nonneg_right t.2) hst'
  have hshift := intervalIntegral.integral_comp_add_right
    (fun u : ℝ ↦ lam * Limit.currentSign (safeCurrentAt hlam0 hlamHalf B 0 u.toNNReal sample))
    (s:ℝ) (a := 0) (b := (t:ℝ))
  change (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve
      ((t:ℝ)+(B+(s:ℝ))) -
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve (B+(s:ℝ)) = _
  rw [show (t:ℝ)+(B+(s:ℝ)) = B+((s:ℝ)+(t:ℝ)) by ring]
  refine hp.trans ?_
  erw [show (s:ℝ)+(t:ℝ) = (t:ℝ)+(s:ℝ) by ring]
  erw [show (∫u in (s:ℝ)..((t:ℝ)+(s:ℝ)), lam * Limit.currentSign
      (safeCurrentAt hlam0 hlamHalf B 0 u.toNNReal sample)) =
      ∫u in (0:ℝ)..(t:ℝ), lam * Limit.currentSign
        (safeCurrentAt hlam0 hlamHalf B 0 (u+(s:ℝ)).toNNReal sample) by
    simpa only [zero_add] using hshift.symm]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc (0:ℝ) (t:ℝ) := by
    change u ∈ uIcc (0:ℝ) (t:ℝ) at hu
    exact (uIcc_of_le t.2) ▸ hu
  have hus : 0 ≤ u+(s:ℝ) := add_nonneg hu'.1 s.2
  have he := feedbackEnvironmentCurrent_stoppedScene_eq_safeCurrentAt hlam0 hlamHalf eta B T
    (u+(s:ℝ)).toNNReal sample hNoTie hstop
    (by apply NNReal.coe_le_coe.mp; rw [Real.coe_toNNReal _ hus]; linarith [hu'.2])
    (B+(s:ℝ)) u (by rw [Real.coe_toNNReal _ hus]; ring)
  exact congrArg (fun k ↦ lam * Limit.currentSign k) he.symm

end FiniteSample
end OTSelector
