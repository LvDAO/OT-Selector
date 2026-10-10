import OTSelector.PointProcess.MatchingSceneCutVacancy
import OTSelector.PointProcess.MatchingSceneMartingaleObservable
import OTSelector.Feedback.FeedbackMarkedEnvironmentResidual

/-!
# The actual feedback graph equation in weak limits

Every surviving finite feedback graph satisfies the oriented integral equation on a bulk
window, including negative displacements from its spatial root. The residual is measurable
and continuous at scenes with a vacant root. Actual finite root laws give it the constant law
at zero; almost-everywhere continuous mapping transports that law to a tight weak limit.
This argument uses no annealed energy expectation and no pathwise coupling of the scenes.
-/

open MeasureTheory ProbabilityTheory Set Filter Function Topology
open scoped Classical ENNReal NNReal

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} {lam : ℝ}

/-- The actual finite primitive identity also holds with reversed integration endpoints. -/
theorem stoppedGraph_curve_sub_eq_integral_safeCurrentAt_oriented
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    (sample : FiniteSample n) (hgood : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve (B+t) -
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve (B+s) =
    ∫ v in s..t, lam * Limit.currentSign (safeCurrentAt hlam0 hlamHalf B 0 v.toNNReal sample) := by
  rcases le_total s t with hst | hts
  · exact sample.stoppedContinuationFeedbackGraph_curve_sub_eq_integral_safeCurrentAt
      hlam0 hlamHalf eta B T hstop hgood hs hst htT
  · rw [intervalIntegral.integral_symm]
    rw [← sample.stoppedContinuationFeedbackGraph_curve_sub_eq_integral_safeCurrentAt
      hlam0 hlamHalf eta B T hstop hgood ht hts hsT]
    ring

/-- At any spatial root with both endpoints in the surviving bulk, the actual stopped graph
satisfies its own current equation for an arbitrary real displacement. -/
theorem stoppedRootedScene_graph_eq_integral_currentAt
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    (sample : FiniteSample n) (hgood : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (z q : ℝ) (hleft : B ≤ z + min 0 q) (hright : z + max 0 q ≤ B + (T : ℝ)) :
    (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T z).path.graphHeight q =
      ∫ v in (0:ℝ)..q, lam * Limit.currentSign
        ((sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T z).currentAt v) := by
  have hs : 0 ≤ z-B := by linarith [min_le_left (0:ℝ) q]
  have ht : 0 ≤ (z-B)+q := by linarith [min_le_right (0:ℝ) q]
  have hsT : z-B ≤ T := by linarith [le_max_left (0:ℝ) q]
  have htT : (z-B)+q ≤ T := by linarith [le_max_right (0:ℝ) q]
  have hp := stoppedGraph_curve_sub_eq_integral_safeCurrentAt_oriented
    hlam0 hlamHalf eta B T sample hgood hstop hs ht hsT htT
  change (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve (q+z) -
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve z = _
  have hshift := intervalIntegral.integral_comp_add_right
    (fun v : ℝ ↦ lam * Limit.currentSign (safeCurrentAt hlam0 hlamHalf B 0 v.toNNReal sample))
    (z-B) (a := 0) (b := q)
  have hid : (∫ v in z-B..((z-B)+q), lam * Limit.currentSign
      (safeCurrentAt hlam0 hlamHalf B 0 v.toNNReal sample)) =
      ∫ v in (0:ℝ)..q, lam * Limit.currentSign
        (safeCurrentAt hlam0 hlamHalf B 0 (v+(z-B)).toNNReal sample) := by
    simpa only [zero_add, add_comm q (z-B)] using hshift.symm
  have hp' : (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve (q+z) -
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve z =
      ∫ v in (0:ℝ)..q, lam * Limit.currentSign
        (safeCurrentAt hlam0 hlamHalf B 0 (v+(z-B)).toNNReal sample) := by
    have h₁ : B + ((z-B)+q) = q+z := by ring
    have h₂ : B + (z-B) = z := by ring
    simpa only [h₁, h₂] using hp.trans hid
  refine hp'.trans (intervalIntegral.integral_congr ?_)
  intro v hv
  change v ∈ Icc (min 0 q) (max 0 q) at hv
  have hv0 : 0 ≤ v+(z-B) := by linarith [hv.1]
  have hvT : v+(z-B) ≤ T := by linarith [hv.2]
  have he := feedbackEnvironmentCurrent_stoppedScene_eq_safeCurrentAt hlam0 hlamHalf eta B T
    (v+(z-B)).toNNReal sample hgood hstop
    (by apply NNReal.coe_le_coe.mp; simpa only [Real.coe_toNNReal _ hv0] using hvT)
    z v (by rw [Real.coe_toNNReal _ hv0]; ring)
  exact congrArg (fun k ↦ lam * Limit.currentSign k) he.symm

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene

/-- The actual graph-minus-current primitive residual at a fixed spatial displacement. -/
noncomputable def graphCurrentResidual (lam q : ℝ) (scene : MatchingScene) : ℝ :=
  scene.path.graphHeight q - ∫ v in (0:ℝ)..q, lam * Limit.currentSign (scene.currentAt v)

/-- This real residual is an observable of the existing scene carrier. -/
theorem measurable_graphCurrentResidual (lam q : ℝ) : Measurable (graphCurrentResidual lam q) := by
  have hg : Continuous (fun scene : MatchingScene ↦ scene.path.graphHeight q) :=
    continuous_eval.comp (continuous_graphHeight.prodMk continuous_const)
  have hm : Measurable (fun p : MatchingScene × ℝ ↦ lam * Limit.currentSign (p.1.currentAt p.2)) :=
    measurable_const.mul ((measurable_of_countable (fun k : ℤ ↦ Limit.currentSign k)).comp
      (Limit.measurable_feedbackEnvironmentCurrent.comp
        (measurable_snd.prodMk (Matching.measurable_feedbackSceneEnvironment.comp measurable_fst))))
  have hi : Measurable (fun scene : MatchingScene ↦
      ∫ v in (0:ℝ)..q, lam * Limit.currentSign (scene.currentAt v)) :=
    ((hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 q))).sub
      (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc q 0)))).measurable
  exact hg.measurable.sub hi

/-- Only root vacancy is needed for continuity; jumps inside the integration interval may move. -/
theorem continuousAt_graphCurrentResidual (lam q : ℝ) {scene : MatchingScene}
    (h0 : scene.VacantCut 0) : ContinuousAt (graphCurrentResidual lam q) scene := by
  have hbound (k : ℤ) : ‖lam * Limit.currentSign k‖ ≤ ‖lam‖ := by
    cases k with
    | ofNat k => cases k <;> simp [Limit.currentSign]
    | negSucc k => simp [Limit.currentSign]
  exact (continuous_eval.comp (continuous_graphHeight.prodMk continuous_const)).continuousAt.sub
    (continuousAt_integral_currentAt h0 (fun k ↦ lam * Limit.currentSign k) hbound 0 q)

/-- Zero residual laws pass to a weak limit by actual almost-everywhere continuous mapping.
The statement concerns laws, without selecting convergent sample paths. -/
private theorem ae_graphCurrentResidual_eq_zero_of_tendsto
    (lam q : ℝ) {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun k ↦ (μ k : Measure MatchingScene)))
    (hroot : ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.VacantCut 0)
    (hzero : ∀ᶠ k in atTop, ∀ᵐ scene ∂(μ k : Measure MatchingScene),
      graphCurrentResidual lam q scene = 0) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), graphCurrentResidual lam q scene = 0 := by
  let δ : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, Measure.dirac.isProbabilityMeasure⟩
  have hm := measurable_graphCurrentResidual lam q
  have hmap := tendsto_map_of_ae_continuousAt μ hlim htight hm
    (hroot.mono fun scene hs ↦ continuousAt_graphCurrentResidual lam q hs)
  have hevent : ∀ᶠ k in atTop, (μ k).map hm.aemeasurable = δ := by
    filter_upwards [hzero] with k hk
    apply Subtype.ext
    change (μ k : Measure MatchingScene).map (graphCurrentResidual lam q) = Measure.dirac 0
    rw [Measure.map_congr hk, Measure.map_const, measure_univ, one_smul]
  have hδ : Tendsto (fun k ↦ (μ k).map hm.aemeasurable) atTop (𝓝 δ) :=
    tendsto_const_nhds.congr' (hevent.mono fun k hk ↦ hk.symm)
  have heq := congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hmap hδ)
  change (ν : Measure MatchingScene).map (graphCurrentResidual lam q) = Measure.dirac 0 at heq
  have hz : ∀ᵐ x ∂(ν : Measure MatchingScene).map (graphCurrentResidual lam q), x = (0:ℝ) := by
    rw [heq]
    simp
  exact (ae_map_iff hm.aemeasurable (measurableSet_singleton (0:ℝ))).mp hz

/-- A fixed real graph equation holds almost surely in any tight weak limit of the original
surviving stopped optimizer scenes. Vacancy is derived from actual finite root counts. -/
theorem ae_graph_eq_integral_currentAt_of_stoppedRootLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (sample : ∀ k, FiniteSample (N k)) (eta B : ℕ → ℝ) (T : ℕ → ℝ≥0)
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) = (sample k).rootedMatchingSceneLaw
      ((sample k).stoppedContinuationFeedbackGraph hlam0 hlamHalf (eta k) (B k) (T k))
      (sample k).euclideanOptimizer (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun k ↦ (μ k : Measure MatchingScene))) {ρ : ℝ}
    (hcount : ∀ᶠ k in atTop, (N k : ℝ) ≤ ρ*(b k-a k))
    (hgood : ∀ᶠ k in atTop, (sample k).NoFeedbackTies lam (B k) 0 ∧
      FiniteSample.safeFeedbackA1StopTime hlam0 hlamHalf (eta k) (B k) (B k) 0 (T k) (sample k) =
        (T k : WithTop ℝ≥0)) (q : ℝ)
    (hfit : ∀ᶠ k in atTop, B k ≤ a k + min 0 q ∧ b k + max 0 q ≤ B k + (T k : ℝ)) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), scene.path.graphHeight q =
      ∫ v in (0:ℝ)..q, lam * Limit.currentSign (scene.currentAt v) := by
  have hroot := ae_vacantCut_of_rootedMatchingSceneLaw_tendsto sample
    (fun k ↦ (sample k).stoppedContinuationFeedbackGraph hlam0 hlamHalf (eta k) (B k) (T k))
    (fun k ↦ (sample k).euclideanOptimizer) a b hab hlaw hlim hcount 0
  have hz : ∀ᶠ k in atTop, ∀ᵐ scene ∂(μ k : Measure MatchingScene),
      graphCurrentResidual lam q scene = 0 := by
    filter_upwards [hgood, hfit] with k hk hfitk
    rw [hlaw k, FiniteSample.rootedMatchingSceneLaw]
    apply (ae_map_iff ((sample k).measurable_rootedMatchingScene _ _).aemeasurable
      ((measurable_graphCurrentResidual lam q) (measurableSet_singleton (0:ℝ)))).mpr
    change ∀ᵐ z ∂(volume (Ioc (a k) (b k)))⁻¹ • volume.restrict (Ioc (a k) (b k)),
      graphCurrentResidual lam q ((sample k).stoppedRootedEuclideanScene
        hlam0 hlamHalf (eta k) (B k) (T k) z) = 0
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    apply sub_eq_zero.mpr
    exact FiniteSample.stoppedRootedScene_graph_eq_integral_currentAt
      hlam0 hlamHalf (eta k) (B k) (T k) (sample k) hk.1 hk.2 z q
      (by linarith [hz.1]) (by linarith [hz.2])
  exact (ae_graphCurrentResidual_eq_zero_of_tendsto lam q hlim htight hroot hz).mono
    fun scene hs ↦ sub_eq_zero.mp hs

/-- The actual limiting graph equation holds on one full-measure event at every rational cut.
All hypotheses refer to the original finite samples and their actual spatial root laws. -/
theorem ae_forall_rat_graph_eq_integral_currentAt_of_stoppedRootLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (sample : ∀ k, FiniteSample (N k)) (eta B : ℕ → ℝ) (T : ℕ → ℝ≥0)
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) = (sample k).rootedMatchingSceneLaw
      ((sample k).stoppedContinuationFeedbackGraph hlam0 hlamHalf (eta k) (B k) (T k))
      (sample k).euclideanOptimizer (a k) (b k))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun k ↦ (μ k : Measure MatchingScene))) {ρ : ℝ}
    (hcount : ∀ᶠ k in atTop, (N k : ℝ) ≤ ρ*(b k-a k))
    (hgood : ∀ᶠ k in atTop, (sample k).NoFeedbackTies lam (B k) 0 ∧
      FiniteSample.safeFeedbackA1StopTime hlam0 hlamHalf (eta k) (B k) (B k) 0 (T k) (sample k) =
        (T k : WithTop ℝ≥0))
    (hfit : ∀ q : ℚ, ∀ᶠ k in atTop,
      B k ≤ a k + min 0 (q:ℝ) ∧ b k + max 0 (q:ℝ) ≤ B k + (T k : ℝ)) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), ∀ q : ℚ, scene.path.graphHeight q =
      ∫ v in (0:ℝ)..(q:ℝ), lam * Limit.currentSign (scene.currentAt v) := by
  apply ae_all_iff.mpr
  intro q
  exact ae_graph_eq_integral_currentAt_of_stoppedRootLaw_tendsto hlam0 hlamHalf
    sample eta B T a b hab hlaw hlim htight hcount hgood q (hfit q)

end OTSelector.PointProcess.MatchingScene
