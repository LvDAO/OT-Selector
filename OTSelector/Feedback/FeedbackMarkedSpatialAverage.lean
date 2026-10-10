import OTSelector.Feedback.FeedbackMarkedStoppedMartingale
import OTSelector.Feedback.FeedbackCountWindowMoment

/-!
# Uniform spatial residual closure for the actual geometric marks

The original finite marks have genuine stopped compensated martingales. Their local count
second moments give a uniform residual bound, and separated spatial windows are orthogonal.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical NNReal Topology
set_option maxHeartbeats 800000

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem integral_sq_le_of_count_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ] {M X : Ω → ℝ}
    (hM : Integrable (fun ω ↦ M ω ^ 2) μ) (hX : Integrable (fun ω ↦ X ω ^ 2) μ)
    {C D V : ℝ} (hb : ∀ ω, ‖M ω‖ ≤ C * X ω + D)
    (hEX : (∫ ω, X ω^2 ∂μ) ≤ V) :
    (∫ ω, M ω^2 ∂μ) ≤ 2*C^2*V + 2*D^2 := by
  have hpoint (ω : Ω) : M ω^2 ≤ 2*C^2*(X ω)^2 + 2*D^2 := by
    have hh := hb ω
    rw [Real.norm_eq_abs] at hh
    have hs : |M ω|^2 ≤ (C * X ω + D)^2 := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).2 hh
    rw [sq_abs] at hs
    nlinarith [sq_nonneg (C * X ω - D)]
  calc
    _ ≤ ∫ ω, 2*C^2*(X ω)^2 + 2*D^2 ∂μ :=
      integral_mono hM ((hX.const_mul _).add (integrable_const _)) hpoint
    _ = 2*C^2*(∫ ω, X ω^2 ∂μ) + 2*D^2 := by
      rw [integral_add (hX.const_mul _) (integrable_const _), integral_const_mul]; simp
    _ ≤ _ := by gcongr

end OTSelector.Probability

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- Uniform local second moment for the actual stopped source geometric-mark residual. -/
theorem integral_sq_safeSourceSpatialMarkedCompensator_increment_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω : FiniteSample n,
      (safeSourceSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ t ω -
       safeSourceSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ s ω)^2
        ∂(finiteSampleLaw n)) ≤ C^2 * (6 * ((t : ℝ) - s) + 54 * ((t : ℝ) - s)^2) := by
  have hlamHalf : lam < 1 / 2 := by linarith
  let F := usualRevealedFiltration (n := n) hlam0.le hlamHalf x0 p0
  let τ := safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B x0 p0 T
  let M := safeSourceSpatialMarkedCompensator (n := n) hlam0.le hlamHalf eta B x0 p0 T ψ
  let Q := stoppedProcess (fun u ω ↦
    (safeSourceBulkCount (n := n) hlam0.le hlamHalf B x0 p0 u ω : ℝ)) τ
  have hMm := safeSourceSpatialMarkedCompensator_martingale
    hlam0.le hlamHalf hn hB eta x0 p0 T ψ hψ hC hbound
  have hMb (u : ℝ≥0) (ω : FiniteSample n) : ‖M u ω‖ ≤
      (n : ℝ)*C + C*feedbackBulkRateCap n B*T :=
    norm_safeSourceSpatialMarkedCompensator_le hlam0.le hlamHalf hn hB eta x0 p0 T ψ hψ hC hbound u ω
  have hQm : StronglyAdapted F Q := by
    change StronglyAdapted F (stoppedProcess _ τ)
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
    have hN := safeSourceBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0
    exact Limit.stronglyAdapted_cappedStoppingValue_of_rightContinuous hN.stronglyAdapted
      (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta x0 p0 T) hN.rightContinuous
  have hQb (u : ℝ≥0) (ω : FiniteSample n) : ‖Q u ω‖ ≤ (n : ℝ) := by
    change ‖(safeSourceBulkCount hlam0.le hlamHalf B x0 p0 _ ω : ℝ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast finiteEventCountTop_le
      (fun i ↦ safeSourceBulkEventTime hlam0.le hlamHalf B x0 p0 i) _ ω
  have hiM : Integrable (fun ω ↦ (M t ω - M s ω)^2) (finiteSampleLaw n) := by
    apply Integrable.of_bound
      ((((hMm.stronglyMeasurable t).mono (F.le t)).sub
        ((hMm.stronglyMeasurable s).mono (F.le s))).pow 2).aestronglyMeasurable
      ((2*((n:ℝ)*C+C*feedbackBulkRateCap n B*T))^2)
    filter_upwards with ω
    simp only [Pi.pow_apply, Pi.sub_apply, norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hMb t ω, hMb s ω])
  have hiQ : Integrable (fun ω ↦ (Q t ω - Q s ω)^2) (finiteSampleLaw n) := by
    apply Integrable.of_bound
      ((((hQm t).mono (F.le t)).sub ((hQm s).mono (F.le s))).pow 2).aestronglyMeasurable
      ((2*(n:ℝ))^2)
    filter_upwards with ω
    simp only [Pi.pow_apply, Pi.sub_apply, norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hQb t ω, hQb s ω])
  have hh := Probability.integral_sq_le_of_count_bound hiM hiQ
    (fun ω ↦ norm_safeSourceSpatialMarkedCompensator_sub_le hlam0 hlam hn hB heta hetaSmall
      T ψ hψ hC hbound hst ω)
    (integral_sq_safeSourceA1Count_increment_le hlam0 hlam hn hB heta hetaSmall T hst)
  convert hh using 1; ring

/-- Uniform local second moment for the actual stopped target geometric-mark residual. -/
theorem integral_sq_safeTargetSpatialMarkedCompensator_increment_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω : FiniteSample n,
      (safeTargetSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ t ω -
       safeTargetSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ s ω)^2
        ∂(finiteSampleLaw n)) ≤ C^2 * (6 * ((t : ℝ) - s) + 54 * ((t : ℝ) - s)^2) := by
  have hlamHalf : lam < 1 / 2 := by linarith
  let F := usualRevealedFiltration (n := n) hlam0.le hlamHalf x0 p0
  let τ := safeFeedbackA1StopTime (n := n) hlam0.le hlamHalf eta B x0 p0 T
  let M := safeTargetSpatialMarkedCompensator (n := n) hlam0.le hlamHalf eta B x0 p0 T ψ
  let Q := stoppedProcess (fun u ω ↦
    (safeTargetBulkCount (n := n) hlam0.le hlamHalf B x0 p0 u ω : ℝ)) τ
  have hMm := safeTargetSpatialMarkedCompensator_martingale
    hlam0.le hlamHalf hn hB eta x0 p0 T ψ hψ hC hbound
  have hMb (u : ℝ≥0) (ω : FiniteSample n) : ‖M u ω‖ ≤
      (n : ℝ)*C + C*feedbackBulkRateCap n B*T :=
    norm_safeTargetSpatialMarkedCompensator_le hlam0.le hlamHalf hn hB eta x0 p0 T ψ hψ hC hbound u ω
  have hQm : StronglyAdapted F Q := by
    change StronglyAdapted F (stoppedProcess _ τ)
    rw [Limit.stoppedProcess_eq_cappedStoppingValue]
    have hN := safeTargetBulkCount_isSimpleCountingProcess (n := n) hlam0.le hlamHalf B x0 p0
    exact Limit.stronglyAdapted_cappedStoppingValue_of_rightContinuous hN.stronglyAdapted
      (safeFeedbackA1StopTime_isStoppingTime hlam0.le hlamHalf hB eta x0 p0 T) hN.rightContinuous
  have hQb (u : ℝ≥0) (ω : FiniteSample n) : ‖Q u ω‖ ≤ (n : ℝ) := by
    change ‖(safeTargetBulkCount hlam0.le hlamHalf B x0 p0 _ ω : ℝ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast finiteEventCountTop_le
      (fun i ↦ safeTargetBulkEventTime hlam0.le hlamHalf B x0 p0 i) _ ω
  have hiM : Integrable (fun ω ↦ (M t ω - M s ω)^2) (finiteSampleLaw n) := by
    apply Integrable.of_bound
      ((((hMm.stronglyMeasurable t).mono (F.le t)).sub
        ((hMm.stronglyMeasurable s).mono (F.le s))).pow 2).aestronglyMeasurable
      ((2*((n:ℝ)*C+C*feedbackBulkRateCap n B*T))^2)
    filter_upwards with ω
    simp only [Pi.pow_apply, Pi.sub_apply, norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hMb t ω, hMb s ω])
  have hiQ : Integrable (fun ω ↦ (Q t ω - Q s ω)^2) (finiteSampleLaw n) := by
    apply Integrable.of_bound
      ((((hQm t).mono (F.le t)).sub ((hQm s).mono (F.le s))).pow 2).aestronglyMeasurable
      ((2*(n:ℝ))^2)
    filter_upwards with ω
    simp only [Pi.pow_apply, Pi.sub_apply, norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [hQb t ω, hQb s ω])
  have hh := Probability.integral_sq_le_of_count_bound hiM hiQ
    (fun ω ↦ norm_safeTargetSpatialMarkedCompensator_sub_le hlam0 hlam hn hB heta hetaSmall
      T ψ hψ hC hbound hst ω)
    (integral_sq_safeTargetA1Count_increment_le hlam0 hlam hn hB heta hetaSmall T hst)
  convert hh using 1; ring

end OTSelector.FiniteSample

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Uniform increment second moments, together with the genuine martingale equations, give
spatial residual closure. A finite process envelope is used only for integrability. -/
theorem integral_sq_average_spatialWindowResidual_le_of_increment_moment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {M G : ℝ≥0 → Ω → ℝ} (hM : Martingale M F μ)
    (hMm : Measurable (Function.uncurry M)) (hG : StronglyAdapted F G)
    (hGm : Measurable (Function.uncurry G))
    {A B V : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hGb : ∀ x ω, ‖G x ω‖ ≤ A) (hMb : ∀ x ω, ‖M x ω‖ ≤ B) (t : ℝ≥0)
    (hmean : ∀ x, (∫ ω, (M (x+t) ω - M x ω)^2 ∂μ) ≤ V)
    {a b : ℝ} (hab : a < b) :
    (∫ ω, ((b-a)⁻¹ * ∫ x in Ioc a b, spatialWindowResidual M G t x ω)^2 ∂μ) ≤
      2 * (t : ℝ) * (A^2 * V) / (b-a) := by
  have harg : Measurable (fun p : ℝ × Ω ↦ (p.1.toNNReal, p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  have hargt : Measurable (fun p : ℝ × Ω ↦ (p.1.toNNReal+t, p.2)) :=
    ((measurable_real_toNNReal.comp measurable_fst).add_const t).prodMk measurable_snd
  have hX : Measurable (Function.uncurry (spatialWindowResidual M G t)) :=
    Measurable.ite (measurableSet_le measurable_const measurable_fst)
      ((hGm.comp harg).mul ((hMm.comp hargt).sub (hMm.comp harg))) measurable_const
  have hinc (x : ℝ≥0) (ω : Ω) : ‖M (x+t) ω - M x ω‖ ≤ 2*B :=
    (norm_sub_le _ _).trans (by linarith [hMb (x+t) ω, hMb x ω])
  have hb (x : ℝ) (ω : Ω) : ‖spatialWindowResidual M G t x ω‖ ≤ A*(2*B) := by
    unfold spatialWindowResidual
    split_ifs
    · rw [pastWindowResidual, norm_mul]
      exact mul_le_mul (hGb _ _) (hinc _ _) (norm_nonneg _) hA
    · simpa only [norm_zero] using mul_nonneg hA (mul_nonneg (by norm_num) hB)
  apply integral_sq_spatialAverage_le_of_memLp μ hX (C := A^2*V) (t := (t : ℝ))
    (a := a) (b := b) (mul_nonneg (sq_nonneg A) hV) t.2 hab
  · intro x
    exact MemLp.of_bound (hX.comp measurable_prodMk_left).aestronglyMeasurable _
      (Eventually.of_forall (hb x))
  · intro x
    by_cases hx : 0 ≤ x
    · have hi : Integrable (fun ω ↦ (M (x.toNNReal+t) ω - M x.toNNReal ω)^2) μ := by
        apply Integrable.of_bound
          (((hMm.comp measurable_prodMk_left).sub
            (hMm.comp measurable_prodMk_left)).pow_const 2).aestronglyMeasurable ((2*B)^2)
        filter_upwards with ω
        simp only [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hinc _ ω) 2
      have hiX : Integrable (fun ω ↦ spatialWindowResidual M G t x ω ^ 2) μ := by
        apply Integrable.of_bound ((hX.comp measurable_prodMk_left).pow_const 2).aestronglyMeasurable
          ((A*(2*B))^2)
        filter_upwards with ω
        simp only [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb x ω) 2
      calc
        _ ≤ ∫ ω, A^2*(M (x.toNNReal+t) ω - M x.toNNReal ω)^2 ∂μ := by
          apply integral_mono hiX (hi.const_mul _)
          intro ω
          simp only [spatialWindowResidual, ite_eq_left hx, pastWindowResidual, mul_pow]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          have hh : |G x.toNNReal ω| ≤ A := hGb _ _
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA).2 hh
        _ = A^2 * ∫ ω, (M (x.toNNReal+t) ω - M x.toNNReal ω)^2 ∂μ := integral_const_mul _ _
        _ ≤ A^2*V := mul_le_mul_of_nonneg_left (hmean _) (sq_nonneg A)
    · simp only [spatialWindowResidual, ite_eq_right hx, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
      exact mul_nonneg (sq_nonneg A) hV
  · intro x y hsep
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · simp only [spatialWindowResidual, ite_eq_left hx, ite_eq_left hy]
        rcases le_total x y with hxy | hyx
        · have horder : x.toNNReal+t ≤ y.toNNReal := by
            change (x.toNNReal : ℝ)+(t : ℝ) ≤ (y.toNNReal : ℝ)
            rw [Real.coe_toNNReal x hx, Real.coe_toNNReal y hy]
            rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hsep
            have ht : (t : ℝ) ≤ y-x := by simpa only [neg_sub] using hsep
            simpa only [add_comm] using (le_sub_iff_add_le.mp ht)
          exact integral_pastWindowResidual_mul_eq_zero_of_le hM hG hA
            (mul_nonneg (by norm_num) hB) hGb t hinc horder
        · have horder : y.toNNReal+t ≤ x.toNNReal := by
            change (y.toNNReal : ℝ)+(t : ℝ) ≤ (x.toNNReal : ℝ)
            rw [Real.coe_toNNReal x hx, Real.coe_toNNReal y hy]
            rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hsep
            simpa only [add_comm] using (le_sub_iff_add_le.mp hsep)
          simpa only [mul_comm] using integral_pastWindowResidual_mul_eq_zero_of_le hM hG hA
            (mul_nonneg (by norm_num) hB) hGb t hinc horder
      · simp [spatialWindowResidual, hy]
    · simp [spatialWindowResidual, hx]

end OTSelector.Probability

namespace OTSelector.FiniteSample

variable {n : ℕ} {lam eta : ℝ}

/-- The true finite marked residual has an inverse-root-window mean-square bound. -/
theorem safeSourceSpatialMarkedCompensator_average_sq_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C)
    (G : ℝ≥0 → FiniteSample n → ℝ)
    (hG : StronglyAdapted (usualRevealedFiltration hlam0.le (by linarith) x0 p0) G)
    (hGm : Measurable (Function.uncurry G)) {A : ℝ} (hA : 0 ≤ A)
    (hGb : ∀ x ω, ‖G x ω‖ ≤ A) (t : ℝ≥0) {a b : ℝ} (hab : a < b) :
    (∫ ω, ((b-a)⁻¹ * ∫ x in Ioc a b, Probability.spatialWindowResidual
      (safeSourceSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ) G t x ω)^2
        ∂(finiteSampleLaw n)) ≤
      2 * (t : ℝ) * (A^2 * (C^2 * (6*(t : ℝ)+54*(t : ℝ)^2))) / (b-a) := by
  apply Probability.integral_sq_average_spatialWindowResidual_le_of_increment_moment
    (safeSourceSpatialMarkedCompensator_martingale hlam0.le (by linarith) hn hB eta x0 p0 T ψ hψ hC hbound)
    (measurable_uncurry_safeSourceSpatialMarkedCompensator hlam0.le (by linarith) hn hB eta x0 p0 T ψ hψ hC hbound)
    hG hGm hA
    (show 0 ≤ (n:ℝ)*C+C*feedbackBulkRateCap n B*T from
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
        (mul_nonneg (mul_nonneg hC (feedbackBulkRateCap_nonneg n B)) T.2))
    (by positivity) hGb
    (norm_safeSourceSpatialMarkedCompensator_le hlam0.le (by linarith) hn hB eta x0 p0 T ψ hψ hC hbound)
    t ?_ hab
  intro x
  have hh := integral_sq_safeSourceSpatialMarkedCompensator_increment_le
    (x0 := x0) (p0 := p0) hlam0 hlam hn hB heta hetaSmall T ψ hψ hC hbound
    (s := x) (t := x+t) (le_add_of_nonneg_right (by positivity))
  simpa only [NNReal.coe_add, add_sub_cancel_left] using hh

/-- The true finite marked residual has an inverse-root-window mean-square bound. -/
theorem safeTargetSpatialMarkedCompensator_average_sq_le
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {B x0 p0 : ℝ} (hn : 0 < n) (hB : 0 < B) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T : ℝ≥0)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C)
    (G : ℝ≥0 → FiniteSample n → ℝ)
    (hG : StronglyAdapted (usualRevealedFiltration hlam0.le (by linarith) x0 p0) G)
    (hGm : Measurable (Function.uncurry G)) {A : ℝ} (hA : 0 ≤ A)
    (hGb : ∀ x ω, ‖G x ω‖ ≤ A) (t : ℝ≥0) {a b : ℝ} (hab : a < b) :
    (∫ ω, ((b-a)⁻¹ * ∫ x in Ioc a b, Probability.spatialWindowResidual
      (safeTargetSpatialMarkedCompensator hlam0.le (by linarith) eta B x0 p0 T ψ) G t x ω)^2
        ∂(finiteSampleLaw n)) ≤
      2 * (t : ℝ) * (A^2 * (C^2 * (6*(t : ℝ)+54*(t : ℝ)^2))) / (b-a) := by
  apply Probability.integral_sq_average_spatialWindowResidual_le_of_increment_moment
    (safeTargetSpatialMarkedCompensator_martingale hlam0.le (by linarith) hn hB eta x0 p0 T ψ hψ hC hbound)
    (measurable_uncurry_safeTargetSpatialMarkedCompensator hlam0.le (by linarith) hn hB eta x0 p0 T ψ hψ hC hbound)
    hG hGm hA
    (show 0 ≤ (n:ℝ)*C+C*feedbackBulkRateCap n B*T from
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
        (mul_nonneg (mul_nonneg hC (feedbackBulkRateCap_nonneg n B)) T.2))
    (by positivity) hGb
    (norm_safeTargetSpatialMarkedCompensator_le hlam0.le (by linarith) hn hB eta x0 p0 T ψ hψ hC hbound)
    t ?_ hab
  intro x
  have hh := integral_sq_safeTargetSpatialMarkedCompensator_increment_le
    (x0 := x0) (p0 := p0) hlam0 hlam hn hB heta hetaSmall T ψ hψ hC hbound
    (s := x) (t := x+t) (le_add_of_nonneg_right (by positivity))
  simpa only [NNReal.coe_add, add_sub_cancel_left] using hh


/-- Growing root windows make the actual marked residual vanish in mean square, uniformly in
sample size and in the A1 localization horizon. -/
theorem tendsto_safeSourceSpatialMarkedCompensator_average_sq_zero
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam)
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j)
    (B x0 p0 : ℕ → ℝ) (hB : ∀ j, 0 < B j) (T : ℕ → ℝ≥0)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C)
    (G : ∀ j, ℝ≥0 → FiniteSample (N j) → ℝ)
    (hG : ∀ j, StronglyAdapted
      (usualRevealedFiltration hlam0.le (by linarith) (x0 j) (p0 j)) (G j))
    (hGm : ∀ j, Measurable (Function.uncurry (G j)))
    {A : ℝ} (hA : 0 ≤ A) (hGb : ∀ j x ω, ‖G j x ω‖ ≤ A)
    (t : ℝ≥0) (a b : ℕ → ℝ) (hab : ∀ j, a j < b j)
    (hwidth : Tendsto (fun j ↦ b j - a j) atTop atTop) :
    Tendsto (fun j ↦ ∫ ω, ((b j-a j)⁻¹ * ∫ x in Ioc (a j) (b j),
      Probability.spatialWindowResidual
        (safeSourceSpatialMarkedCompensator hlam0.le (by linarith) eta
          (B j) (x0 j) (p0 j) (T j) ψ) (G j) t x ω)^2 ∂(finiteSampleLaw (N j)))
        atTop (nhds 0) := by
  apply squeeze_zero
    (fun j ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    (fun j ↦ safeSourceSpatialMarkedCompensator_average_sq_le
      hlam0 hlam (hN j) (hB j) heta hetaSmall (T j) ψ hψ hC hbound
      (G j) (hG j) (hGm j) hA (hGb j) t (hab j))
  exact hwidth.const_div_atTop _

/-- Growing root windows make the actual marked residual vanish in mean square, uniformly in
sample size and in the A1 localization horizon. -/
theorem tendsto_safeTargetSpatialMarkedCompensator_average_sq_zero
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (heta : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam)
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j)
    (B x0 p0 : ℕ → ℝ) (hB : ∀ j, 0 < B j) (T : ℕ → ℝ≥0)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C)
    (G : ∀ j, ℝ≥0 → FiniteSample (N j) → ℝ)
    (hG : ∀ j, StronglyAdapted
      (usualRevealedFiltration hlam0.le (by linarith) (x0 j) (p0 j)) (G j))
    (hGm : ∀ j, Measurable (Function.uncurry (G j)))
    {A : ℝ} (hA : 0 ≤ A) (hGb : ∀ j x ω, ‖G j x ω‖ ≤ A)
    (t : ℝ≥0) (a b : ℕ → ℝ) (hab : ∀ j, a j < b j)
    (hwidth : Tendsto (fun j ↦ b j - a j) atTop atTop) :
    Tendsto (fun j ↦ ∫ ω, ((b j-a j)⁻¹ * ∫ x in Ioc (a j) (b j),
      Probability.spatialWindowResidual
        (safeTargetSpatialMarkedCompensator hlam0.le (by linarith) eta
          (B j) (x0 j) (p0 j) (T j) ψ) (G j) t x ω)^2 ∂(finiteSampleLaw (N j)))
        atTop (nhds 0) := by
  apply squeeze_zero
    (fun j ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    (fun j ↦ safeTargetSpatialMarkedCompensator_average_sq_le
      hlam0 hlam (hN j) (hB j) heta hetaSmall (T j) ψ hψ hC hbound
      (G j) (hG j) (hGm j) hA (hGb j) t (hab j))
  exact hwidth.const_div_atTop _

end OTSelector.FiniteSample
