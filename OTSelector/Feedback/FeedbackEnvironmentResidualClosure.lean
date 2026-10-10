import OTSelector.Feedback.FeedbackEnvironmentResidualSelection
import OTSelector.Feedback.FeedbackEnvironmentCountableMarks
import OTSelector.Feedback.FeedbackEnvironmentResidualTime

/-! # The actual countable residuals determine all original past-cylinder identities

Uniformly bounded compact-open approximation extends the outer functions. Common compact
supports extend the past point tests on every locally finite configuration. The actual count
first moments then extend marks and observation times by dominated convergence.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal CompactlySupported BoundedContinuousFunction
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.MatchingScene

private theorem integral_countablePastResidual_eq_zero
    (μ : Measure MatchingScene) [IsFiniteMeasure μ]
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1/2)
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ)) μ)
    (hzero : ∀i : ActualEnvironmentResidualIndex,
      (∫scene, countableEnvironmentResidual lam i scene ∂μ) = 0)
    {ns nt : ℕ} (fs : Fin ns → ℕ × ℕ) (ft : Fin nt → ℕ × ℕ)
    (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ) (b : Bool) (pi : ℕ × ℕ) (d a : ℕ) :
    (∫scene, pastMarkedResidual lam (fun j ↦ countablePastTest (fs j))
      (fun j ↦ countablePastTest (ft j)) H b (countableEnvironmentMarkTest pi)
      ((a:ℝ≥0)/(d+1:ℕ)) scene ∂μ) = 0 := by
  let Y (scene : MatchingScene) : EnvironmentPastCoordinates ns nt :=
    (fun j ↦ LocalConfiguration.testIntegral scene.source (countablePastTest (fs j)),
     fun j ↦ LocalConfiguration.testIntegral scene.target (countablePastTest (ft j)),
     (scene.path.rootCurrent:ℝ))
  have hY : Measurable Y :=
    (measurable_pi_lambda _ fun j ↦ (LocalConfiguration.measurable_testIntegral _).comp
      measurable_source).prodMk
    ((measurable_pi_lambda _ fun j ↦ (LocalConfiguration.measurable_testIntegral _).comp
      measurable_target).prodMk
      ((measurable_of_countable (fun z : ℤ ↦ (z:ℝ))).comp continuous_rootCurrent.measurable))
  have hR := Limit.integrable_feedbackEnvironmentMarkedCompensator_of_count μ hlam0 hlam
    Matching.feedbackSceneEnvironment Matching.measurable_feedbackSceneEnvironment
    b ((a:ℝ≥0)/(d+1:ℕ)) (hcount b _) (countableEnvironmentMarkTest pi)
  have hh := Probability.integral_mul_bcf_eq_zero_of_countable_tests μ hY hR
    (fun hi ↦ by
      simpa only [countableEnvironmentResidual,pastMarkedResidual,environmentPastCylinder,Y,Matching.feedbackSceneEnvironment,mul_comm]
        using hzero (⟨⟨ns,nt,fs,ft,hi,pi,b⟩,d,a⟩)) H
  simpa only [pastMarkedResidual,environmentPastCylinder,Y,Matching.feedbackSceneEnvironment,mul_comm] using hh

private theorem integral_pastResidual_countableMark_eq_zero
    (μ : Measure MatchingScene) [IsFiniteMeasure μ]
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1/2)
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ)) μ)
    (hzero : ∀i : ActualEnvironmentResidualIndex,
      (∫scene, countableEnvironmentResidual lam i scene ∂μ) = 0)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (hfs : ∀i p, 0 ≤ p.1 → fs i p = 0) (hft : ∀i p, 0 ≤ p.1 → ft i p = 0)
    (b : Bool) (pi : ℕ × ℕ) (d a : ℕ) :
    (∫scene, pastMarkedResidual lam fs ft H b (countableEnvironmentMarkTest pi)
      ((a:ℝ≥0)/(d+1:ℕ)) scene ∂μ) = 0 := by
  have hs (j : Fin ns) := exists_countablePastTest_tendsto (fs j)
    (fun x v hx ↦ hfs j (x,v) hx)
  have ht (j : Fin nt) := exists_countablePastTest_tendsto (ft j)
    (fun x v hx ↦ hft j (x,v) hx)
  choose ms hms us hus using hs
  choose mt hmt ut hut using ht
  let Fs (k : ℕ) (j : Fin ns) := countablePastTest (ms j,us j k)
  let Ft (k : ℕ) (j : Fin nt) := countablePastTest (mt j,ut j k)
  let t : ℝ≥0 := (a:ℝ≥0)/(d+1:ℕ)
  let ψ := countableEnvironmentMarkTest pi
  let R (scene : MatchingScene) := Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
    (Matching.feedbackSceneEnvironment scene)
  have hR : Integrable R μ := Limit.integrable_feedbackEnvironmentMarkedCompensator_of_count
    μ hlam0 hlam Matching.feedbackSceneEnvironment Matching.measurable_feedbackSceneEnvironment
    b t (hcount b t) ψ
  have hident (k : ℕ) : (∫scene, pastMarkedResidual lam (Fs k) (Ft k) H b ψ t scene ∂μ) = 0 :=
    integral_countablePastResidual_eq_zero μ hlam0 hlam hcount hzero
      (fun j ↦ (ms j,us j k)) (fun j ↦ (mt j,ut j k)) H b pi d a
  have hconv := tendsto_integral_of_dominated_convergence
    (f := fun scene ↦ pastMarkedResidual lam fs ft H b ψ t scene)
    (fun scene ↦ ‖H‖*‖R scene‖)
    (fun k ↦ (measurable_pastMarkedResidual lam (Fs k) (Ft k) H b ψ t).aestronglyMeasurable)
    (hR.norm.const_mul ‖H‖)
    (fun k ↦ Eventually.of_forall fun scene ↦ by
      rw [pastMarkedResidual,norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_environmentPastCylinder_le (Fs k) (Ft k) H (Matching.feedbackSceneEnvironment scene))
        (norm_nonneg _))
    (Eventually.of_forall fun scene ↦ by
      have hsc := tendsto_pi_nhds.mpr fun j ↦ tendsto_testIntegral_of_common_support
        scene.source (hms j) (fun k ↦ support_countablePastTest_subset (ms j,us j k)) (hus j)
      have htc := tendsto_pi_nhds.mpr fun j ↦ tendsto_testIntegral_of_common_support
        scene.target (hmt j) (fun k ↦ support_countablePastTest_subset (mt j,ut j k)) (hut j)
      exact (H.continuous.tendsto _ |>.comp
        (hsc.prodMk_nhds (htc.prodMk_nhds
          (tendsto_const_nhds (x := (scene.path.rootCurrent:ℝ)))))).mul tendsto_const_nhds)
  exact tendsto_nhds_unique hconv (by
    simpa only [hident] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0)))

/-- The selected countable actual observables imply every original compact-past, bounded
continuous marked residual identity. Genuine local count integrability supplies all domination. -/
theorem pastCylinderResidualIdentities_of_countableResiduals
    (μ : Measure MatchingScene) [IsFiniteMeasure μ]
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1/2)
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ)) μ)
    (hzero : ∀i : ActualEnvironmentResidualIndex,
      (∫scene, countableEnvironmentResidual lam i scene ∂μ) = 0) :
    PastCylinderResidualIdentities μ lam := by
  apply pastCylinderResidualIdentities_of_nonneg_rational μ lam hcount
  intro ns nt fs ft H hfs hft b ψ d a
  have hh := Limit.integral_markedIncrement_eq_zero_of_countable_marks μ hlam0 hlam
    Matching.feedbackSceneEnvironment Matching.measurable_feedbackSceneEnvironment
    b 0 ((a:ℝ≥0)/(d+1:ℕ)) (hcount b 0) (hcount b _)
    ((measurable_environmentPastCylinder fs ft H).comp Matching.measurable_feedbackSceneEnvironment)
    (norm_nonneg H) (fun scene ↦ norm_environmentPastCylinder_le fs ft H _)
    (fun pi ↦ by
      simpa only [Limit.feedbackEnvironmentMarkedCompensator_zero,sub_zero,pastMarkedResidual,Function.comp_apply] using
        integral_pastResidual_countableMark_eq_zero μ hlam0.le hlam hcount hzero
          fs ft H hfs hft b pi d a) ψ
  simpa only [Limit.feedbackEnvironmentMarkedCompensator_zero,sub_zero,pastMarkedResidual,Function.comp_apply] using hh

end OTSelector.PointProcess.MatchingScene
