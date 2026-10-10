import OTSelector.Feedback.FeedbackMarkedSpatialMartingale
import OTSelector.Feedback.FeedbackSpatialMartingale
import OTSelector.Limit.FeedbackMartingaleProblemStoppedProcess

/-!
# Regularity and A1 stopping of the actual geometric-mark martingales
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical NNReal Topology
set_option maxHeartbeats 800000

namespace OTSelector.CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

private theorem measurable_section_of_predictable
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable F H) (ω : Ω) : Measurable (fun u ↦ H u ω) :=
  (hH.mono (predictable_le_ambient F)).measurable.comp
    (measurable_id.prodMk measurable_const)

theorem measurable_uncurry_finiteEventWeightedSum
    (ξ : Fin m → Ω → WithTop ℝ≥0) (w : Fin m → Ω → ℝ)
    (hξ : ∀ i, Measurable (ξ i)) (hw : ∀ i, Measurable (w i)) :
    Measurable (Function.uncurry (finiteEventWeightedSum ξ w)) := by
  classical
  unfold finiteEventWeightedSum Function.uncurry
  exact Finset.measurable_sum _ (fun i _ ↦ Measurable.ite
    (measurableSet_le ((hξ i).comp measurable_snd) measurable_fst.withTop_coe)
    ((hw i).comp measurable_snd) measurable_const)

omit [MeasurableSpace Ω] in
/-- Bounded marks are controlled by the actual number of events in the window. -/
theorem norm_finiteEventWeightedSum_sub_le
    (ξ : Fin m → Ω → WithTop ℝ≥0) (w : Fin m → Ω → ℝ)
    {C : ℝ} (_hC : 0 ≤ C) (hw : ∀ i ω, ‖w i ω‖ ≤ C)
    {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    ‖finiteEventWeightedSum ξ w t ω - finiteEventWeightedSum ξ w s ω‖ ≤
      C * ((finiteEventCountTop ξ t ω : ℝ) - finiteEventCountTop ξ s ω) := by
  have hc (u : ℝ≥0) : finiteEventWeightedSum ξ (fun _ _ ↦ (1 : ℝ)) u ω =
      (finiteEventCountTop ξ u ω : ℝ) := by
    exact (finiteEventCountTop_cast_eq_sum ξ u ω).symm
  have he := finiteEventWeightedSum_sub ξ (fun _ _ ↦ (1 : ℝ)) hst ω
  rw [hc, hc] at he
  rw [finiteEventWeightedSum_sub ξ w hst ω, he, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · simpa using hw i ω
  · simp

omit [MeasurableSpace Ω] in
/-- Stopping an ordinary compensator is exactly multiplication by the right-closed stop mask. -/
theorem integratedIntensity_mul_throughStopMask_eq_stoppedProcess
    (Λ H : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) :
    (fun t ω ↦ integratedIntensity Λ (fun u ω ↦ throughStopMask τ u ω * H u ω) t ω) =
      stoppedProcess (integratedIntensity Λ H) τ := by
  classical
  funext t ω
  rw [Limit.stoppedProcess_eq_cappedStoppingValue]
  let S : Set ℝ≥0 := {u | (u : WithTop ℝ≥0) ≤ τ ω}
  have hS : MeasurableSet S := measurableSet_le measurable_id.withTop_coe measurable_const
  change (∫ u in Ioc 0 t, (throughStopMask τ u ω * H u ω) * Λ u ω ∂timeMeasure) =
    ∫ u in Ioc 0 (cappedStoppingValue t τ ω), H u ω * Λ u ω ∂timeMeasure
  have hf : (fun u ↦ (throughStopMask τ u ω * H u ω) * Λ u ω) =
      S.indicator (fun u ↦ H u ω * Λ u ω) := by
    funext u
    simp only [throughStopMask, Set.indicator, S, mem_ofPred_eq]
    split_ifs <;> simp
  rw [hf, integral_indicator hS, Measure.restrict_restrict hS]
  have hset : S ∩ Ioc 0 t = Ioc 0 (cappedStoppingValue t τ ω) := by
    ext u
    simp only [mem_inter_iff, mem_Ioc, S, mem_ofPred_eq]
    have hu : u ≤ cappedStoppingValue t τ ω ↔
        (u : WithTop ℝ≥0) ≤ τ ω ∧ u ≤ t := by
      rw [← WithTop.coe_le_coe, coe_cappedStoppingValue, le_min_iff, WithTop.coe_le_coe]
    rw [hu]
    tauto
  rw [hset]

end OTSelector.CountingProcess

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

theorem measurable_uncurry_safeSourceBulkMarkedCompensator
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Measurable (Function.uncurry
      (safeSourceBulkMarkedCompensator (n := n) hlam0 hlamHalf B x0 p0 ψ)) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hmark : Measurable (Function.uncurry
      (safeSourceBulkMarkSum (n := n) hlam0 hlamHalf B x0 p0 ψ)) :=
    measurable_uncurry_finiteEventWeightedSum _ _ (fun i ↦
      (safeSourceBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0 i).measurable.mono
        (safeSourceBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0 i).measurableSpace_le le_rfl)
      (fun i ↦ hψ.measurable.comp (measurable_sourceMark i))
  have hI := safeSourceBulkCount_hasPredictableIntensity
    (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hmean := sourceFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
    (n := n) hlam0 hlamHalf x0 p0 ψ hψ hC hbound
  exact hmark.sub (measurable_uncurry_integratedIntensity
    (hI.predictable.mono (predictable_le_ambient F)).measurable
    (hmean.1.mono (predictable_le_ambient F)).measurable)

theorem safeSourceBulkMarkedCompensator_rightContinuous
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) (sample : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ safeSourceBulkMarkedCompensator
      hlam0 hlamHalf B x0 p0 ψ s sample) (Ici t) t := by
  have hI := safeSourceBulkCount_hasPredictableIntensity
    (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hmean := sourceFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
    (n := n) hlam0 hlamHalf x0 p0 ψ hψ hC hbound
  have hc := A_continuous (Ω := Unit)
    (Λ := fun u _ ↦ sourceFeedbackMarkMean
      (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ *
        safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample) (ω := ())
    (fun u ↦ hmean.isBoundedPredictable.integrableOn_mul_intensity hI u sample)
  simp only [integratedIntensity, one_mul] at hc
  exact (safeSourceBulkMarkSum_rightContinuous hlam0 hlamHalf B x0 p0 ψ sample t).sub
    hc.continuousAt.continuousWithinAt

theorem norm_safeSourceBulkMarkedCompensator_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) (t : ℝ≥0) (sample : FiniteSample n) :
    ‖safeSourceBulkMarkedCompensator hlam0 hlamHalf B x0 p0 ψ t sample‖ ≤
      (n : ℝ) * C + C * feedbackBulkRateCap n B * t := by
  have hI := safeSourceBulkCount_hasPredictableIntensity
    (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hmean (u : ℝ≥0) (ω : FiniteSample n) :
      |sourceFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u ω) ψ| ≤ C :=
    norm_sourceFeedbackMarkMean_le hlam0 hlamHalf (abs_feedbackSlope_le hlam0) ψ hψ hbound
  have hA := abs_integratedIntensity_le_of_bound hI C hC hmean t sample
  have hcap := (integratedIntensity_one_nonneg_le_of_bounded
    (feedbackBulkRateCap_nonneg n B) hI.nonneg
    (safeSourceBulkRate_le_cap hlam0 hlamHalf B x0 p0) hI.integrableOn t sample).2
  unfold safeSourceBulkMarkedCompensator
  calc
    _ ≤ ‖safeSourceBulkMarkSum hlam0 hlamHalf B x0 p0 ψ t sample‖ +
        ‖integratedIntensity (safeSourceBulkRate hlam0 hlamHalf B x0 p0)
          (fun u ω ↦ sourceFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u ω) ψ)
          t sample‖ := norm_sub_le _ _
    _ ≤ (n : ℝ) * C + C * (feedbackBulkRateCap n B * t) :=
      add_le_add (norm_safeSourceBulkMarkSum_le hlam0 hlamHalf B x0 p0 ψ hC hbound t sample)
        (hA.trans (mul_le_mul_of_nonneg_left hcap hC))
    _ = _ := by ring

theorem measurable_uncurry_safeTargetBulkMarkedCompensator
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Measurable (Function.uncurry
      (safeTargetBulkMarkedCompensator (n := n) hlam0 hlamHalf B x0 p0 ψ)) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hmark : Measurable (Function.uncurry
      (safeTargetBulkMarkSum (n := n) hlam0 hlamHalf B x0 p0 ψ)) :=
    measurable_uncurry_finiteEventWeightedSum _ _ (fun i ↦
      (safeTargetBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0 i).measurable.mono
        (safeTargetBulkEventTime_isStoppingTime hlam0 hlamHalf B x0 p0 i).measurableSpace_le le_rfl)
      (fun i ↦ hψ.measurable.comp (measurable_targetMark i))
  have hI := safeTargetBulkCount_hasPredictableIntensity
    (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hmean := targetFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
    (n := n) hlam0 hlamHalf x0 p0 ψ hψ hC hbound
  exact hmark.sub (measurable_uncurry_integratedIntensity
    (hI.predictable.mono (predictable_le_ambient F)).measurable
    (hmean.1.mono (predictable_le_ambient F)).measurable)

theorem safeTargetBulkMarkedCompensator_rightContinuous
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) (sample : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ safeTargetBulkMarkedCompensator
      hlam0 hlamHalf B x0 p0 ψ s sample) (Ici t) t := by
  have hI := safeTargetBulkCount_hasPredictableIntensity
    (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hmean := targetFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
    (n := n) hlam0 hlamHalf x0 p0 ψ hψ hC hbound
  have hc := A_continuous (Ω := Unit)
    (Λ := fun u _ ↦ targetFeedbackMarkMean
      (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u sample) ψ *
        safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample) (ω := ())
    (fun u ↦ hmean.isBoundedPredictable.integrableOn_mul_intensity hI u sample)
  simp only [integratedIntensity, one_mul] at hc
  exact (safeTargetBulkMarkSum_rightContinuous hlam0 hlamHalf B x0 p0 ψ sample t).sub
    hc.continuousAt.continuousWithinAt

theorem norm_safeTargetBulkMarkedCompensator_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) (t : ℝ≥0) (sample : FiniteSample n) :
    ‖safeTargetBulkMarkedCompensator hlam0 hlamHalf B x0 p0 ψ t sample‖ ≤
      (n : ℝ) * C + C * feedbackBulkRateCap n B * t := by
  have hI := safeTargetBulkCount_hasPredictableIntensity
    (x0 := x0) (p0 := p0) hlam0 hlamHalf hn hB
  have hmean (u : ℝ≥0) (ω : FiniteSample n) :
      |targetFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u ω) ψ| ≤ C :=
    norm_targetFeedbackMarkMean_le hlam0 hlamHalf (abs_feedbackSlope_le hlam0) ψ hψ hbound
  have hA := abs_integratedIntensity_le_of_bound hI C hC hmean t sample
  have hcap := (integratedIntensity_one_nonneg_le_of_bounded
    (feedbackBulkRateCap_nonneg n B) hI.nonneg
    (safeTargetBulkRate_le_cap hlam0 hlamHalf B x0 p0) hI.integrableOn t sample).2
  unfold safeTargetBulkMarkedCompensator
  calc
    _ ≤ ‖safeTargetBulkMarkSum hlam0 hlamHalf B x0 p0 ψ t sample‖ +
        ‖integratedIntensity (safeTargetBulkRate hlam0 hlamHalf B x0 p0)
          (fun u ω ↦ targetFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 u ω) ψ)
          t sample‖ := norm_sub_le _ _
    _ ≤ (n : ℝ) * C + C * (feedbackBulkRateCap n B * t) :=
      add_le_add (norm_safeTargetBulkMarkSum_le hlam0 hlamHalf B x0 p0 ψ hC hbound t sample)
        (hA.trans (mul_le_mul_of_nonneg_left hcap hC))
    _ = _ := by ring


/-- The actual geometric-mark residual through the genuine A1 localization time. -/
noncomputable def safeSourceSpatialMarkedCompensator
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (eta B x0 p0 : ℝ)
    (T : ℝ≥0) (ψ : UnitMark → ℝ) : ℝ≥0 → FiniteSample n → ℝ :=
  stoppedProcess (safeSourceBulkMarkedCompensator hlam0 hlamHalf B x0 p0 ψ)
    (safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T)

theorem safeSourceSpatialMarkedCompensator_martingale
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (eta x0 p0 : ℝ) (T : ℝ≥0) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Martingale (safeSourceSpatialMarkedCompensator hlam0 hlamHalf eta B x0 p0 T ψ)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) (finiteSampleLaw n) := by
  apply Limit.martingale_stoppedProcess_of_rightContinuous_bounded
    (safeSourceBulkMarkedCompensator_martingale hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound)
    (safeFeedbackA1StopTime_isStoppingTime hlam0 hlamHalf hB eta x0 p0 T)
    (safeSourceBulkMarkedCompensator_rightContinuous hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound)
  intro S
  refine ⟨(n : ℝ) * C + C * feedbackBulkRateCap n B * S, ?_⟩
  intro ω s hs
  exact (norm_safeSourceBulkMarkedCompensator_le hlam0 hlamHalf hn hB x0 p0 ψ hψ
    hC hbound s ω).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (show (s : ℝ) ≤ S from hs)
        (mul_nonneg hC (feedbackBulkRateCap_nonneg n B))))

theorem measurable_uncurry_safeSourceSpatialMarkedCompensator
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (eta x0 p0 : ℝ) (T : ℝ≥0) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Measurable (Function.uncurry
      (safeSourceSpatialMarkedCompensator (n := n) hlam0 hlamHalf eta B x0 p0 T ψ)) := by
  have hτ := safeFeedbackA1StopTime_isStoppingTime (n := n)
    hlam0 hlamHalf hB eta x0 p0 T
  have hmτ : Measurable (safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B x0 p0 T) :=
    hτ.measurable.mono hτ.measurableSpace_le le_rfl
  exact (measurable_uncurry_safeSourceBulkMarkedCompensator
    hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound).comp
      (((measurable_fst.withTop_coe.min (hmτ.comp measurable_snd)).untopA).prodMk measurable_snd)

/-- The actual geometric-mark residual through the genuine A1 localization time. -/
noncomputable def safeTargetSpatialMarkedCompensator
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (eta B x0 p0 : ℝ)
    (T : ℝ≥0) (ψ : UnitMark → ℝ) : ℝ≥0 → FiniteSample n → ℝ :=
  stoppedProcess (safeTargetBulkMarkedCompensator hlam0 hlamHalf B x0 p0 ψ)
    (safeFeedbackA1StopTime hlam0 hlamHalf eta B x0 p0 T)

theorem safeTargetSpatialMarkedCompensator_martingale
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (eta x0 p0 : ℝ) (T : ℝ≥0) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Martingale (safeTargetSpatialMarkedCompensator hlam0 hlamHalf eta B x0 p0 T ψ)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0) (finiteSampleLaw n) := by
  apply Limit.martingale_stoppedProcess_of_rightContinuous_bounded
    (safeTargetBulkMarkedCompensator_martingale hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound)
    (safeFeedbackA1StopTime_isStoppingTime hlam0 hlamHalf hB eta x0 p0 T)
    (safeTargetBulkMarkedCompensator_rightContinuous hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound)
  intro S
  refine ⟨(n : ℝ) * C + C * feedbackBulkRateCap n B * S, ?_⟩
  intro ω s hs
  exact (norm_safeTargetBulkMarkedCompensator_le hlam0 hlamHalf hn hB x0 p0 ψ hψ
    hC hbound s ω).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (show (s : ℝ) ≤ S from hs)
        (mul_nonneg hC (feedbackBulkRateCap_nonneg n B))))

theorem measurable_uncurry_safeTargetSpatialMarkedCompensator
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (eta x0 p0 : ℝ) (T : ℝ≥0) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Measurable (Function.uncurry
      (safeTargetSpatialMarkedCompensator (n := n) hlam0 hlamHalf eta B x0 p0 T ψ)) := by
  have hτ := safeFeedbackA1StopTime_isStoppingTime (n := n)
    hlam0 hlamHalf hB eta x0 p0 T
  have hmτ : Measurable (safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B x0 p0 T) :=
    hτ.measurable.mono hτ.measurableSpace_le le_rfl
  exact (measurable_uncurry_safeTargetBulkMarkedCompensator
    hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound).comp
      (((measurable_fst.withTop_coe.min (hmτ.comp measurable_snd)).untopA).prodMk measurable_snd)


/-- Each stopped marked residual increment is bounded by its actual count increment plus the
uniformly bounded compensator on that window. -/
theorem norm_safeSourceSpatialMarkedCompensator_sub_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) {s t : ℝ≥0} (hst : s ≤ t)
    (ω : FiniteSample n) :
    ‖safeSourceSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ t ω -
      safeSourceSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ s ω‖ ≤
      C * (stoppedProcess (fun u ω ↦
        (safeSourceBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
          (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
        stoppedProcess (fun u ω ↦
        (safeSourceBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
          (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω) +
        3 * C * ((t : ℝ) - s) := by
  have hlamHalf : lam < 1 / 2 := by linarith
  let τ := safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B x0 p0 T
  let Λ := safeSourceBulkRate (n := n) hlam0.le hlamHalf B x0 p0
  let H : ℝ≥0 → FiniteSample n → ℝ := fun u ω ↦
    sourceFeedbackMarkMean (safePreFeedbackSlope hlam0.le hlamHalf x0 p0 u ω) ψ
  let g : ℝ≥0 → ℝ := fun u ↦ throughStopMask τ u ω * H u ω * Λ u ω
  have hI := safeSourceBulkCount_hasPredictableIntensity
    (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB
  have hmean := sourceFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf x0 p0 ψ hψ hC hbound
  have hmask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have hmEq : safeFeedbackA1ThroughStopMask (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      throughStopMask τ := by
    funext u ω
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0.le hlamHalf eta B x0 p0 T u ω
  rw [hmEq] at hmask
  have hpred : IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0.le hlamHalf x0 p0)
      (fun u ω ↦ throughStopMask τ u ω * H u ω * Λ u ω) :=
    (hmask.1.mul hmean.1).mul hI.predictable
  have hgm : Measurable g := by
    exact measurable_section_of_predictable hpred ω
  have hgb : ∀ᵐ u ∂timeMeasure, ‖g u‖ ≤ 3 * C := by
    filter_upwards [throughStopMask_rate_bound_ae (τ := τ ω) (C := 3) (by norm_num)
      (fun u ↦ hI.nonneg u ω) (fun u hu ↦
        (safeFeedbackSpatial_rates_le_of_lt_stop hlam0 hlam hB heta hetaSmall T u ω hu).1)]
      with u hu
    have hm : ‖H u ω‖ ≤ C := norm_sourceFeedbackMarkMean_le hlam0.le hlamHalf
      (abs_feedbackSlope_le hlam0.le) ψ hψ hbound
    have heq : g u = H u ω * (throughStopMask τ u ω * Λ u ω) := by dsimp [g]; ring
    rw [heq, norm_mul]
    exact (mul_le_mul hm hu (norm_nonneg _) hC).trans_eq (by ring)
  have hAb := norm_setIntegral_zero_sub_le hgm (mul_nonneg (by norm_num) hC) hgb hst
  have hcuts : cappedStoppingValue s τ ω ≤ cappedStoppingValue t τ ω := by
    apply WithTop.coe_le_coe.mp
    rw [coe_cappedStoppingValue, coe_cappedStoppingValue]
    exact min_le_min_left _ (WithTop.coe_le_coe.mpr hst)
  have hNb := norm_finiteEventWeightedSum_sub_le (Ω := FiniteSample n) (m := n)
    (fun i ↦ safeSourceBulkEventTime hlam0.le hlamHalf B x0 p0 i)
    (fun i ω ↦ ψ (ω.sourceMark i)) hC (fun i ω ↦ hbound _) hcuts ω
  have heq (u : ℝ≥0) : safeSourceSpatialMarkedCompensator
      hlam0.le hlamHalf eta B x0 p0 T ψ u ω =
        safeSourceBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue u τ ω) ω -
          ∫ v in Ioc 0 u, g v ∂timeMeasure := by
    change stoppedProcess (safeSourceBulkMarkedCompensator hlam0.le hlamHalf B x0 p0 ψ) τ u ω = _
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
    change safeSourceBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue u τ ω) ω -
      integratedIntensity Λ H (cappedStoppingValue u τ ω) ω =
        safeSourceBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue u τ ω) ω -
          ∫ v in Ioc 0 u, g v ∂timeMeasure
    congr 1
    have hh := congrFun (congrFun
      (integratedIntensity_mul_throughStopMask_eq_stoppedProcess Λ H τ) u) ω
    rw [Limit.stoppedProcess_eq_cappedStoppingValue] at hh
    exact hh.symm
  rw [heq, heq]
  have halg (a b c d : ℝ) : (a-b)-(c-d) = (a-c)-(b-d) := by ring
  rw [halg]
  apply (norm_sub_le _ _).trans
  have hfinal := add_le_add hNb hAb
  change ‖safeSourceBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue t τ ω) ω -
    safeSourceBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue s τ ω) ω‖ +
      ‖(∫ v in Ioc 0 t, g v ∂timeMeasure) - (∫ v in Ioc 0 s, g v ∂timeMeasure)‖ ≤ _ at hfinal
  rw [Limit.stoppedProcess_eq_cappedStoppingValue]
  exact hfinal

/-- Each stopped marked residual increment is bounded by its actual count increment plus the
uniformly bounded compensator on that window. -/
theorem norm_safeTargetSpatialMarkedCompensator_sub_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) {s t : ℝ≥0} (hst : s ≤ t)
    (ω : FiniteSample n) :
    ‖safeTargetSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ t ω -
      safeTargetSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ s ω‖ ≤
      C * (stoppedProcess (fun u ω ↦
        (safeTargetBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
          (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) t ω -
        stoppedProcess (fun u ω ↦
        (safeTargetBulkCount hlam0.le (by linarith) B x0 p0 u ω : ℝ))
          (safeFeedbackA1StopTime hlam0.le (by linarith) eta B x0 p0 T) s ω) +
        3 * C * ((t : ℝ) - s) := by
  have hlamHalf : lam < 1 / 2 := by linarith
  let τ := safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B x0 p0 T
  let Λ := safeTargetBulkRate (n := n) hlam0.le hlamHalf B x0 p0
  let H : ℝ≥0 → FiniteSample n → ℝ := fun u ω ↦
    targetFeedbackMarkMean (safePreFeedbackSlope hlam0.le hlamHalf x0 p0 u ω) ψ
  let g : ℝ≥0 → ℝ := fun u ↦ throughStopMask τ u ω * H u ω * Λ u ω
  have hI := safeTargetBulkCount_hasPredictableIntensity
    (x0 := x0) (p0 := p0) hlam0.le hlamHalf hn hB
  have hmean := targetFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf x0 p0 ψ hψ hC hbound
  have hmask := safeFeedbackA1ThroughStopMask_boundedSimplePredictable
    (n := n) hlam0.le hlamHalf hB eta x0 p0 T
  have hmEq : safeFeedbackA1ThroughStopMask (n := n) hlam0.le hlamHalf eta B x0 p0 T =
      throughStopMask τ := by
    funext u ω
    exact safeFeedbackA1ThroughStopMask_eq_throughStopMask hlam0.le hlamHalf eta B x0 p0 T u ω
  rw [hmEq] at hmask
  have hpred : IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0.le hlamHalf x0 p0)
      (fun u ω ↦ throughStopMask τ u ω * H u ω * Λ u ω) :=
    (hmask.1.mul hmean.1).mul hI.predictable
  have hgm : Measurable g := by
    exact measurable_section_of_predictable hpred ω
  have hgb : ∀ᵐ u ∂timeMeasure, ‖g u‖ ≤ 3 * C := by
    filter_upwards [throughStopMask_rate_bound_ae (τ := τ ω) (C := 3) (by norm_num)
      (fun u ↦ hI.nonneg u ω) (fun u hu ↦
        (safeFeedbackSpatial_rates_le_of_lt_stop hlam0 hlam hB heta hetaSmall T u ω hu).2)]
      with u hu
    have hm : ‖H u ω‖ ≤ C := norm_targetFeedbackMarkMean_le hlam0.le hlamHalf
      (abs_feedbackSlope_le hlam0.le) ψ hψ hbound
    have heq : g u = H u ω * (throughStopMask τ u ω * Λ u ω) := by dsimp [g]; ring
    rw [heq, norm_mul]
    exact (mul_le_mul hm hu (norm_nonneg _) hC).trans_eq (by ring)
  have hAb := norm_setIntegral_zero_sub_le hgm (mul_nonneg (by norm_num) hC) hgb hst
  have hcuts : cappedStoppingValue s τ ω ≤ cappedStoppingValue t τ ω := by
    apply WithTop.coe_le_coe.mp
    rw [coe_cappedStoppingValue, coe_cappedStoppingValue]
    exact min_le_min_left _ (WithTop.coe_le_coe.mpr hst)
  have hNb := norm_finiteEventWeightedSum_sub_le (Ω := FiniteSample n) (m := n)
    (fun i ↦ safeTargetBulkEventTime hlam0.le hlamHalf B x0 p0 i)
    (fun i ω ↦ ψ (ω.targetMark i)) hC (fun i ω ↦ hbound _) hcuts ω
  have heq (u : ℝ≥0) : safeTargetSpatialMarkedCompensator
      hlam0.le hlamHalf eta B x0 p0 T ψ u ω =
        safeTargetBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue u τ ω) ω -
          ∫ v in Ioc 0 u, g v ∂timeMeasure := by
    change stoppedProcess (safeTargetBulkMarkedCompensator hlam0.le hlamHalf B x0 p0 ψ) τ u ω = _
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
    change safeTargetBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue u τ ω) ω -
      integratedIntensity Λ H (cappedStoppingValue u τ ω) ω =
        safeTargetBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue u τ ω) ω -
          ∫ v in Ioc 0 u, g v ∂timeMeasure
    congr 1
    have hh := congrFun (congrFun
      (integratedIntensity_mul_throughStopMask_eq_stoppedProcess Λ H τ) u) ω
    rw [Limit.stoppedProcess_eq_cappedStoppingValue] at hh
    exact hh.symm
  rw [heq, heq]
  have halg (a b c d : ℝ) : (a-b)-(c-d) = (a-c)-(b-d) := by ring
  rw [halg]
  apply (norm_sub_le _ _).trans
  have hfinal := add_le_add hNb hAb
  change ‖safeTargetBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue t τ ω) ω -
    safeTargetBulkMarkSum hlam0.le hlamHalf B x0 p0 ψ (cappedStoppingValue s τ ω) ω‖ +
      ‖(∫ v in Ioc 0 t, g v ∂timeMeasure) - (∫ v in Ioc 0 s, g v ∂timeMeasure)‖ ≤ _ at hfinal
  rw [Limit.stoppedProcess_eq_cappedStoppingValue]
  exact hfinal


/-- A finite deterministic envelope for the genuine A1-stopped geometric-mark residual. -/
theorem norm_safeSourceSpatialMarkedCompensator_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (eta x0 p0 : ℝ) (T : ℝ≥0) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) (t : ℝ≥0) (ω : FiniteSample n) :
    ‖safeSourceSpatialMarkedCompensator hlam0 hlamHalf eta B x0 p0 T ψ t ω‖ ≤
      (n : ℝ) * C + C * feedbackBulkRateCap n B * T := by
  let τ := safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B x0 p0 T
  have ht : cappedStoppingValue t τ ω ≤ T := by
    apply WithTop.coe_le_coe.mp
    rw [coe_cappedStoppingValue]
    exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  change ‖stoppedProcess (safeSourceBulkMarkedCompensator hlam0 hlamHalf B x0 p0 ψ) τ t ω‖ ≤ _
  rw [Limit.stoppedProcess_eq_cappedStoppingValue]
  exact (norm_safeSourceBulkMarkedCompensator_le hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound
    _ ω).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (show (_ : ℝ) ≤ T from ht)
      (mul_nonneg hC (feedbackBulkRateCap_nonneg n B))))

/-- A finite deterministic envelope for the genuine A1-stopped geometric-mark residual. -/
theorem norm_safeTargetSpatialMarkedCompensator_le
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {B : ℝ} (hn : 0 < n) (hB : 0 < B)
    (eta x0 p0 : ℝ) (T : ℝ≥0) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) (t : ℝ≥0) (ω : FiniteSample n) :
    ‖safeTargetSpatialMarkedCompensator hlam0 hlamHalf eta B x0 p0 T ψ t ω‖ ≤
      (n : ℝ) * C + C * feedbackBulkRateCap n B * T := by
  let τ := safeFeedbackA1StopTime (n := n) hlam0 hlamHalf eta B x0 p0 T
  have ht : cappedStoppingValue t τ ω ≤ T := by
    apply WithTop.coe_le_coe.mp
    rw [coe_cappedStoppingValue]
    exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  change ‖stoppedProcess (safeTargetBulkMarkedCompensator hlam0 hlamHalf B x0 p0 ψ) τ t ω‖ ≤ _
  rw [Limit.stoppedProcess_eq_cappedStoppingValue]
  exact (norm_safeTargetBulkMarkedCompensator_le hlam0 hlamHalf hn hB x0 p0 ψ hψ hC hbound
    _ ω).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (show (_ : ℝ) ≤ T from ht)
      (mul_nonneg hC (feedbackBulkRateCap_nonneg n B))))

end OTSelector.FiniteSample
