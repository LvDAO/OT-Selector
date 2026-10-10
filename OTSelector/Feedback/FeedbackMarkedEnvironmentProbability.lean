import OTSelector.Feedback.FeedbackMarkedEnvironmentAverage

/-! # Restricted convergence in probability of the actual finite ENV residual -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal Topology
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.Probability
variable {Ω : Type*} [MeasurableSpace Ω]

private theorem integrable_sq_spatialWindowAverage
    {μ : Measure Ω} [IsProbabilityMeasure μ] {M G : ℝ≥0 → Ω → ℝ}
    (hM : Measurable (Function.uncurry M)) (hG : Measurable (Function.uncurry G))
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hGb : ∀u ω, ‖G u ω‖ ≤ A) (hMb : ∀u ω, ‖M u ω‖ ≤ D)
    (t : ℝ≥0) (a d : ℝ) :
    Integrable (fun ω ↦ ((d-a)⁻¹*∫x in Ioc a d, spatialWindowResidual M G t x ω)^2) μ := by
  have harg : Measurable (fun p : ℝ×Ω ↦ (p.1.toNNReal,p.2)) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  have hargt : Measurable (fun p : ℝ×Ω ↦ (p.1.toNNReal+t,p.2)) :=
    ((measurable_real_toNNReal.comp measurable_fst).add_const t).prodMk measurable_snd
  have hX : Measurable (Function.uncurry (spatialWindowResidual M G t)) :=
    Measurable.ite (measurableSet_le measurable_const measurable_fst)
      ((hG.comp harg).mul ((hM.comp hargt).sub (hM.comp harg))) measurable_const
  have hb (x : ℝ) (ω : Ω) : ‖spatialWindowResidual M G t x ω‖ ≤ A*(2*D) := by
    unfold spatialWindowResidual pastWindowResidual
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (hGb _ _) ((norm_sub_le _ _).trans (by linarith [hMb (x.toNNReal+t) ω, hMb x.toNNReal ω]))
        (norm_nonneg _) hA
    · simpa only [norm_zero] using mul_nonneg hA (mul_nonneg (by norm_num) hD)
  have havg : Measurable (fun ω ↦ (d-a)⁻¹*∫x in Ioc a d, spatialWindowResidual M G t x ω) :=
    measurable_const.mul (hX.stronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc a d))).measurable
  let K := |(d-a)⁻¹| * (A*(2*D)*volume.real (Ioc a d))
  have hbavg (ω : Ω) : ‖(d-a)⁻¹*∫x in Ioc a d, spatialWindowResidual M G t x ω‖ ≤ K := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top (fun x _ ↦ hb x ω))
      (abs_nonneg _)
  apply Integrable.of_bound (havg.pow_const 2).aestronglyMeasurable (K^2)
  filter_upwards with ω
  simp only [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbavg ω) 2

end OTSelector.Probability

namespace OTSelector.FiniteSample
open CountingProcess
variable {n : ℕ} {lam eta : ℝ}

private theorem finiteMarkedSpatialAverage_sq_integrable
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) {B C A : ℝ} (hn : 0 < n) (hB : 0 < B)
    (T : ℝ≥0) (b : Bool) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hC : 0 ≤ C)
    (hbound : ∀u, ‖ψ u‖ ≤ C) (G : ℝ≥0 → FiniteSample n → ℝ)
    (hGm : Measurable (Function.uncurry G)) (hA : 0 ≤ A) (hGb : ∀u ω, ‖G u ω‖ ≤ A)
    (t : ℝ≥0) (a d : ℝ) :
    Integrable (fun ω ↦ finiteMarkedSpatialAverage hlam0 hlamHalf eta B T b ψ G t a d ω ^2)
      (finiteSampleLaw n) := by
  have hD : 0 ≤ (n:ℝ)*C+C*feedbackBulkRateCap n B*T := by
    have hcap := feedbackBulkRateCap_nonneg n B
    positivity
  cases b
  · exact Probability.integrable_sq_spatialWindowAverage
      (measurable_uncurry_safeTargetSpatialMarkedCompensator hlam0 hlamHalf hn hB eta B 0 T ψ hψ hC hbound)
      hGm hA hD hGb (norm_safeTargetSpatialMarkedCompensator_le hlam0 hlamHalf hn hB eta B 0 T ψ hψ hC hbound) t a d
  · exact Probability.integrable_sq_spatialWindowAverage
      (measurable_uncurry_safeSourceSpatialMarkedCompensator hlam0 hlamHalf hn hB eta B 0 T ψ hψ hC hbound)
      hGm hA hD hGb (norm_safeSourceSpatialMarkedCompensator_le hlam0 hlamHalf hn hB eta B 0 T ψ hψ hC hbound) t a d

/-- The colour-unified actual finite average inherits the proved uniform second moment. -/
theorem integral_sq_finiteMarkedSpatialAverage_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8) {B C A : ℝ} (hn : 0 < n) (hB : 0 < B)
    (heta : 0 ≤ eta) (hetaSmall : eta*(2+lam) ≤ lam) (T : ℝ≥0)
    (b : Bool) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hC : 0 ≤ C) (hbound : ∀u, ‖ψ u‖ ≤ C)
    (G : ℝ≥0 → FiniteSample n → ℝ)
    (hG : StronglyAdapted (usualRevealedFiltration hlam0.le (by linarith) B 0) G)
    (hGm : Measurable (Function.uncurry G)) (hA : 0 ≤ A) (hGb : ∀u ω, ‖G u ω‖ ≤ A)
    (t : ℝ≥0) {a d : ℝ} (had : a < d) :
    (∫ω, finiteMarkedSpatialAverage hlam0.le (by linarith) eta B T b ψ G t a d ω ^2 ∂finiteSampleLaw n) ≤
      2*(t:ℝ)*(A^2*(C^2*(6*(t:ℝ)+54*(t:ℝ)^2)))/(d-a) := by
  cases b
  · exact safeTargetSpatialMarkedCompensator_average_sq_le hlam0 hlam hn hB heta hetaSmall T ψ hψ hC hbound G hG hGm hA hGb t had
  · exact safeSourceSpatialMarkedCompensator_average_sq_le hlam0 hlam hn hB heta hetaSmall T ψ hψ hC hbound G hG hGm hA hGb t had

/-- A residual failure is counted only among the original VC-good samples surviving to the
horizon. This is the event needed by finite-sample selection. -/
def environmentMarkedResidualBadEvent
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    (b : Bool) (ψ : UnitMark → ℝ) (G : ℝ≥0 → FiniteSample n → ℝ)
    (t : ℝ≥0) (a d δ : ℝ) : Set (FiniteSample n) :=
  {sample | sample ∈ feedbackA1GoodEvent n lam B 0 ∧
    safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0) ∧
    δ ≤ ‖environmentMarkedSpatialAverage hlam0 hlamHalf eta B T b ψ G t a d sample‖}

/-- A true finite-sample probability bound for the original ENV residual, obtained from the
proved martingale moment and the actual VC drift error. -/
theorem measureReal_environmentMarkedResidualBadEvent_le
    (hlam0 : 0 < lam) (hlam : lam < 1/8) (hn : 4 ≤ n)
    {eta eps B C A δ : ℝ} (heta : 0 ≤ eta) (hetaSmall : eta*(2+lam) ≤ lam)
    (heps : 0 ≤ eps) (hepsSmall : eps*(2+lam) ≤ lam) (hB : 0 < B) (hδ : 0 < δ)
    (T t : ℝ≥0) {a d : ℝ} (ha : 0 ≤ a) (had : a < d) (hd : d+(t:ℝ) < T)
    (hsqrt : 4*(33280:ℝ)^2*Real.log n ≤ eps^2*(13*B/16))
    (hlinear : 2*(33280:ℝ)*Real.log n ≤ eps*(13*B/16))
    (b : Bool) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hC : 0 ≤ C) (hbound : ∀v, ‖ψ v‖ ≤ C)
    (G : ℝ≥0 → FiniteSample n → ℝ)
    (hG : StronglyAdapted (usualRevealedFiltration hlam0.le (by linarith) B 0) G)
    (hGm : Measurable (Function.uncurry G)) (hA : 0 ≤ A) (hGb : ∀u ω, ‖G u ω‖ ≤ A)
    (herr : 2*A*C*eps*(t:ℝ) ≤ δ/2) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      (environmentMarkedResidualBadEvent hlam0.le (by linarith) eta B T b ψ G t a d δ) ≤
        (2*(t:ℝ)*(A^2*(C^2*(6*(t:ℝ)+54*(t:ℝ)^2)))/(d-a)) / (δ/2)^2 := by
  let F := finiteMarkedSpatialAverage hlam0.le (by linarith) eta B T b ψ G t a d
  have hi := finiteMarkedSpatialAverage_sq_integrable (n := n) (eta := eta) hlam0.le (by linarith) (by omega : 0<n) hB
    T b ψ hψ hC hbound G hGm hA hGb t a d
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (f := fun ω ↦ F ω^2) (ae_of_all _ fun _ ↦ sq_nonneg _) hi ((δ/2)^2)
  have hE := integral_sq_finiteMarkedSpatialAverage_le hlam0 hlam (by omega : 0<n) hB heta hetaSmall
    T b ψ hψ hC hbound G hG hGm hA hGb t had
  have hsub : environmentMarkedResidualBadEvent hlam0.le (by linarith) eta B T b ψ G t a d δ ⊆
      {ω | (δ/2)^2 ≤ F ω^2} := by
    intro ω hω
    have he := norm_environmentMarkedSpatialAverage_sub_finite_le hlam0.le (by linarith) hn heps hepsSmall
      hB T t ω hω.1 hω.2.1 ha had hd hsqrt hlinear b ψ hψ hC hbound G hGm hA hGb
    have hnorm := norm_sub_le
      (environmentMarkedSpatialAverage hlam0.le (by linarith) eta B T b ψ G t a d ω - F ω) (-F ω)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hnorm
    have hlow : δ/2 ≤ ‖F ω‖ := by linarith [hω.2.2]
    have hs := (sq_le_sq₀ (by linarith : 0≤δ/2) (norm_nonneg (F ω))).2 hlow
    simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, sq_abs] using hs
  apply (measureReal_mono (μ := (finiteSampleLaw n : Measure (FiniteSample n))) hsub).trans
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0<δ/2))).mpr
  calc
    _ = (δ/2)^2 * (finiteSampleLaw n : Measure (FiniteSample n)).real {ω | (δ/2)^2 ≤ F ω^2} := by ring
    _ ≤ ∫ω, F ω^2 ∂finiteSampleLaw n := hm
    _ ≤ _ := hE

/-- The original ENV residual vanishes in probability inside the actual good survival event.
The regularity tolerance is an explicit shrinking VC scale, not the fixed localization eta. -/
theorem tendsto_measureReal_environmentMarkedResidualBadEvent_zero
    (hlam0 : 0 < lam) (hlam : lam < 1/8) (heta : 0 ≤ eta) (hetaSmall : eta*(2+lam) ≤ lam)
    {amplitude C A δ : ℝ} (hamp : 0 < amplitude) (hδ : 0 < δ)
    (T : ℕ → ℝ≥0) (t : ℝ≥0) (a d : ℕ → ℝ)
    (hwindow : ∀ᶠ n in atTop, 0 ≤ a n ∧ a n < d n ∧ d n+(t:ℝ) < T n)
    (hwidth : Tendsto (fun n ↦ d n-a n) atTop atTop)
    (b : Bool) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hC : 0 ≤ C) (hbound : ∀v, ‖ψ v‖ ≤ C)
    (G : ∀n, ℝ≥0 → FiniteSample n → ℝ)
    (hG : ∀n, StronglyAdapted (usualRevealedFiltration hlam0.le (by linarith)
      (feedbackA2AsymptoticBuffer amplitude n) 0) (G n))
    (hGm : ∀n, Measurable (Function.uncurry (G n))) (hA : 0 ≤ A) (hGb : ∀n u ω, ‖G n u ω‖ ≤ A) :
    Tendsto (fun n ↦ (finiteSampleLaw n : Measure (FiniteSample n)).real
      (environmentMarkedResidualBadEvent hlam0.le (by linarith) eta
        (feedbackA2AsymptoticBuffer amplitude n) (T n) b ψ (G n) t (a n) (d n) δ)) atTop (nhds 0) := by
  have heps := tendsto_feedbackVanishingRegularityEta amplitude
  have herr : ∀ᶠ n in atTop, 2*A*C*feedbackVanishingRegularityEta amplitude n*(t:ℝ) ≤ δ/2 := by
    have hlim : Tendsto (fun n ↦ 2*A*C*feedbackVanishingRegularityEta amplitude n*(t:ℝ)) atTop (nhds 0) := by
      simpa using (heps.const_mul (2*A*C)).mul_const (t:ℝ)
    exact (tendsto_order.mp hlim).2 (δ/2) (by linarith) |>.mono fun _ h ↦ h.le
  apply squeeze_zero'
    (Eventually.of_forall fun _ ↦ measureReal_nonneg)
    (show ∀ᶠ n in atTop, _ ≤
      (2*(t:ℝ)*(A^2*(C^2*(6*(t:ℝ)+54*(t:ℝ)^2)))/(d n-a n))/(δ/2)^2 from ?_)
  · simpa using (hwidth.const_div_atTop (2*(t:ℝ)*(A^2*(C^2*(6*(t:ℝ)+54*(t:ℝ)^2))))).div_const ((δ/2)^2)
  · filter_upwards [eventually_feedbackVanishingRegularity_parameters hlam0 hamp, hwindow, herr]
      with n hp hw he
    exact measureReal_environmentMarkedResidualBadEvent_le hlam0 hlam hp.1 heta hetaSmall
      hp.2.2.1 hp.2.2.2.1 hp.2.1 hδ (T n) t hw.1 hw.2.1 hw.2.2 hp.2.2.2.2.1 hp.2.2.2.2.2
      b ψ hψ hC hbound (G n) (hG n) (hGm n) hA (hGb n) he

end OTSelector.FiniteSample
