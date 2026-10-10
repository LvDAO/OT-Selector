import OTSelector.PointProcess.PastWindowTestApproximation
import OTSelector.PointProcess.MatchingSceneMartingaleClosure
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentRestartReadout

/-!
# From compact past tests to the actual marked-count history

Compact point tests approximate negative hard windows at vacant cuts. Bounded outer cylinders
allow dominated convergence using only the integrability of the future compensator. Actual
reroot stationarity then moves these identities to every observation time. In particular, no
adaptedness of a stopped finite scene is asserted or needed in this limit-law step.
-/

open MeasureTheory ProbabilityTheory Set Filter Function Topology
open scoped Classical NNReal CompactlySupported BoundedContinuousFunction
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess.MatchingScene

/-- Residual identities tested by the original finite continuous environment-past cylinders. -/
def PastCylinderResidualIdentities (μ : Measure MatchingScene) (lam : ℝ) : Prop :=
  ∀ (ns nt : ℕ) (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ),
    (∀ i p, 0 ≤ p.1 → fs i p = 0) → (∀ i p, 0 ≤ p.1 → ft i p = 0) →
    ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0),
      (∫ scene, pastMarkedResidual lam fs ft H b ψ t scene ∂μ) = 0

private noncomputable def hardPastCylinder {ns nt : ℕ}
    (as bs : Fin ns → ℝ) (ats bt : Fin nt → ℝ)
    (ψs : Fin ns → UnitMark →ᵇ ℝ) (ψt : Fin nt → UnitMark →ᵇ ℝ)
    (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ) (scene : MatchingScene) : ℝ :=
  H (fun i ↦ ∫ p in LocalConfiguration.spatialIoc (as i) (bs i), ψs i p.2
        ∂LocalConfiguration.countingMeasure scene.source,
    fun i ↦ ∫ p in LocalConfiguration.spatialIoc (ats i) (bt i), ψt i p.2
        ∂LocalConfiguration.countingMeasure scene.target,
    (scene.path.rootCurrent : ℝ))

/-- Passing the original past-cylinder identities to finitely many actual negative windows. -/
private theorem integral_hardPastCylinder_mul_compensator_eq_zero
    (μ : Measure MatchingScene) (lam : ℝ)
    (hCc : PastCylinderResidualIdentities μ lam)
    (hcuts : ∀ x : ℝ, ∀ᵐ scene ∂μ, scene.VacantCut x)
    {ns nt : ℕ} (as bs : Fin ns → ℝ) (ats bt : Fin nt → ℝ)
    (ψs : Fin ns → UnitMark →ᵇ ℝ) (ψt : Fin nt → UnitMark →ᵇ ℝ)
    (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (hbs : ∀ i, bs i ≤ 0) (hbt : ∀ i, bt i ≤ 0)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0)
    (hM : Integrable (fun scene ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene)) μ) :
    (∫ scene, hardPastCylinder as bs ats bt ψs ψt H scene *
      Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
        (Matching.feedbackSceneEnvironment scene) ∂μ) = 0 := by
  let fs (n : ℕ) (i : Fin ns) := pastWindowTest (as i) (bs i) (ψs i) n
  let ft (n : ℕ) (i : Fin nt) := pastWindowTest (ats i) (bt i) (ψt i) n
  have hzero (n : ℕ) : (∫ scene, pastMarkedResidual lam (fs n) (ft n) H b ψ t scene ∂μ) = 0 :=
    hCc ns nt (fs n) (ft n) H
      (fun i p hp ↦ pastWindowTest_eq_zero_of_nonneg (hbs i) _ _ p hp)
      (fun i p hp ↦ pastWindowTest_eq_zero_of_nonneg (hbt i) _ _ p hp) b ψ t
  have hlim := tendsto_integral_of_dominated_convergence
    (f := fun scene ↦ hardPastCylinder as bs ats bt ψs ψt H scene *
      Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
        (Matching.feedbackSceneEnvironment scene))
    (fun scene ↦ ‖H‖ * ‖Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene)‖)
    (fun n ↦ (measurable_pastMarkedResidual lam (fs n) (ft n) H b ψ t).aestronglyMeasurable)
    (hM.norm.const_mul ‖H‖) ?_ ?_
  · have heq : (fun n ↦ ∫ scene, pastMarkedResidual lam (fs n) (ft n) H b ψ t scene ∂μ) =
        fun _ : ℕ ↦ (0 : ℝ) := funext hzero
    rw [heq] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  · intro n
    exact Eventually.of_forall fun scene ↦ by
      rw [pastMarkedResidual, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_environmentPastCylinder_le _ _ _ _)
        (norm_nonneg _)
  · have hsource : ∀ᵐ scene ∂μ, ∀ i : Fin ns, scene.VacantCut (bs i) :=
      (ae_all_iff).mpr fun i ↦ hcuts (bs i)
    have htarget : ∀ᵐ scene ∂μ, ∀ i : Fin nt, scene.VacantCut (bt i) :=
      (ae_all_iff).mpr fun i ↦ hcuts (bt i)
    filter_upwards [hsource, htarget] with scene hs ht
    have hsc := tendsto_pi_nhds.mpr fun i ↦
      tendsto_testIntegral_pastWindowTest scene.source (as i) (bs i) (ψs i) (hs i).1
    have htc := tendsto_pi_nhds.mpr fun i ↦
      tendsto_testIntegral_pastWindowTest scene.target (ats i) (bt i) (ψt i) (ht i).2
    exact (H.continuous.tendsto _ |>.comp
      (hsc.prodMk_nhds (htc.prodMk_nhds
        (tendsto_const_nhds (x := (scene.path.rootCurrent : ℝ)))))).mul tendsto_const_nhds

private def historyWindowRight (s : ℝ≥0) : PastCountIndex → ℝ
  | .inl _ => 0
  | .inr q => q.1 - s

private noncomputable def historyWindowMark (b : Bool) : PastCountIndex → UnitMark →ᵇ ℝ
  | .inl _ => BoundedContinuousFunction.const UnitMark 1
  | .inr q => if q.2.1 = b then q.2.2 else 0

private theorem historyWindowRight_nonpos (s : ℝ≥0) (i : PastCountAt s) :
    historyWindowRight s i.1 ≤ 0 := by
  rcases i with ⟨i, hi⟩
  cases i with
  | inl u => exact le_refl _
  | inr q => exact sub_nonpos.mpr (show (q.1 : ℝ) ≤ s from hi)

private noncomputable def historyReconstruction (s : ℝ≥0) (J : Finset (PastCountAt s)) :
    C(EnvironmentPastCoordinates (Fintype.card J) (Fintype.card J), J → ℝ) where
  toFun x j := match j.1.1 with
    | .inl _ => x.2.2 - x.1 (Fintype.equivFin J j) + x.2.1 (Fintype.equivFin J j)
    | .inr _ => x.1 (Fintype.equivFin J j) + x.2.1 (Fintype.equivFin J j)
  continuous_toFun := by
    apply continuous_pi
    intro j
    cases j.1.1 with
    | inl u =>
      change Continuous (fun x : EnvironmentPastCoordinates (Fintype.card J) (Fintype.card J) ↦
        x.2.2 - x.1 (Fintype.equivFin J j) + x.2.1 (Fintype.equivFin J j))
      fun_prop
    | inr q =>
      change Continuous (fun x : EnvironmentPastCoordinates (Fintype.card J) (Fintype.card J) ↦
        x.1 (Fintype.equivFin J j) + x.2.1 (Fintype.equivFin J j))
      fun_prop

private theorem rootCurrent_reroot_neg (s : ℝ≥0) (scene : MatchingScene) :
    ((reroot (-(s : ℝ)) scene).path.rootCurrent : ℝ) =
      (scene.path.rootCurrent : ℝ) -
        (∫ _p in LocalConfiguration.spatialIoc (-(s : ℝ)) 0, (1 : ℝ)
          ∂LocalConfiguration.countingMeasure scene.source) +
        (∫ _p in LocalConfiguration.spatialIoc (-(s : ℝ)) 0, (1 : ℝ)
          ∂LocalConfiguration.countingMeasure scene.target) := by
  have hs : LocalConfiguration.spatialCount scene.source 0 (-(s : ℝ)) = 0 :=
    LocalConfiguration.spatialCount_eq_zero_of_le scene.source (neg_nonpos.mpr s.2)
  have ht : LocalConfiguration.spatialCount scene.target 0 (-(s : ℝ)) = 0 :=
    LocalConfiguration.spatialCount_eq_zero_of_le scene.target (neg_nonpos.mpr s.2)
  have hK : (reroot (-(s : ℝ)) scene).path.rootCurrent = scene.path.rootCurrent -
      LocalConfiguration.spatialCount scene.source (-(s : ℝ)) 0 +
      LocalConfiguration.spatialCount scene.target (-(s : ℝ)) 0 := by
    change scene.path.rootCurrent +
      (LocalConfiguration.spatialCount scene.source 0 (-(s : ℝ)) -
       LocalConfiguration.spatialCount scene.source (-(s : ℝ)) 0 -
       (LocalConfiguration.spatialCount scene.target 0 (-(s : ℝ)) -
        LocalConfiguration.spatialCount scene.target (-(s : ℝ)) 0)) = _
    omega
  have hKr := congrArg (fun z : ℤ ↦ (z : ℝ)) hK
  simp only [Int.cast_add, Int.cast_sub, LocalConfiguration.spatialCount_cast] at hKr
  simpa only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply_univ] using hKr

private theorem hardPastCylinder_history (s : ℝ≥0) (J : Finset (PastCountAt s))
    (F : (J → ℝ) →ᵇ ℝ) (scene : MatchingScene) :
    hardPastCylinder
      (fun _ ↦ -(s : ℝ))
      (fun i ↦ historyWindowRight s ((Fintype.equivFin J).symm i).1.1)
      (fun _ ↦ -(s : ℝ))
      (fun i ↦ historyWindowRight s ((Fintype.equivFin J).symm i).1.1)
      (fun i ↦ historyWindowMark true ((Fintype.equivFin J).symm i).1.1)
      (fun i ↦ historyWindowMark false ((Fintype.equivFin J).symm i).1.1)
      (F.compContinuous (historyReconstruction s J)) scene =
      F (J.restrict (pastCountHistory s (reroot (-(s : ℝ)) scene))) := by
  apply congrArg F
  funext j
  simp only [historyReconstruction, ContinuousMap.coe_mk, Equiv.symm_apply_apply,
    Finset.restrict, pastCountHistory]
  rcases hi : j.1.1 with u | ⟨u, b, ψ⟩
  · simpa only [hi, historyWindowRight, historyWindowMark,
      BoundedContinuousFunction.const_apply, pastCountObservable] using
      (rootCurrent_reroot_neg s scene).symm
  · change _ = LocalConfiguration.firstEventTestCount
      (Limit.feedbackEnvironmentTwoColor (FeedbackEnvironment.reroot (-(s : ℝ))
        (Matching.feedbackSceneEnvironment scene))) b ψ u
    rw [Limit.firstEventTestCount_feedbackEnvironment_reroot]
    cases b <;> simp [historyWindowRight, historyWindowMark,
      Limit.feedbackEnvironmentTwoColor, Matching.feedbackSceneEnvironment, sub_eq_add_neg]

/-- All finite hard-count histories have the original residual identity at every time.
Stationarity is used only for deterministic reroots; no random-time substitution occurs. -/
theorem cylinder_residuals_of_pastCylinderResidualIdentities
    (μ : Measure MatchingScene) [IsFiniteMeasure μ] (lam : ℝ)
    (hstationary : ∀ a : ℝ, MeasurePreserving (reroot a) μ μ)
    (hcuts : ∀ x : ℝ, ∀ᵐ scene ∂μ, scene.VacantCut x)
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ)) μ)
    (hCc : PastCylinderResidualIdentities μ lam)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (s t : ℝ≥0) (hst : s ≤ t)
    (J : Finset (PastCountAt s)) (F : (J → ℝ) →ᵇ ℝ) :
    (∫ scene, (Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene) -
      Limit.feedbackEnvironmentMarkedCompensator lam b ψ s
      (Matching.feedbackSceneEnvironment scene)) *
        F (J.restrict (pastCountHistory s scene)) ∂μ) = 0 := by
  have hz := integral_hardPastCylinder_mul_compensator_eq_zero μ lam hCc hcuts
    (fun _ : Fin (Fintype.card J) ↦ -(s : ℝ))
    (fun i ↦ historyWindowRight s ((Fintype.equivFin J).symm i).1.1)
    (fun _ : Fin (Fintype.card J) ↦ -(s : ℝ))
    (fun i ↦ historyWindowRight s ((Fintype.equivFin J).symm i).1.1)
    (fun i ↦ historyWindowMark true ((Fintype.equivFin J).symm i).1.1)
    (fun i ↦ historyWindowMark false ((Fintype.equivFin J).symm i).1.1)
    (F.compContinuous (historyReconstruction s J))
    (fun i ↦ historyWindowRight_nonpos s ((Fintype.equivFin J).symm i).1)
    (fun i ↦ historyWindowRight_nonpos s ((Fintype.equivFin J).symm i).1)
    b ψ (t - s) (integrable_markedCompensator μ hcount lam b ψ (t - s))
  simp_rw [hardPastCylinder_history] at hz
  rw [← (hstationary (-(s : ℝ))).integral_comp
    (rerootMeasurableEquiv (-(s : ℝ))).measurableEmbedding]
  convert hz using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun scene ↦ by
    have he := Limit.feedbackEnvironmentMarkedCompensator_add lam b ψ
      (Matching.feedbackSceneEnvironment (reroot (-(s : ℝ)) scene)) s (t - s)
    rw [add_tsub_cancel_of_le hst] at he
    have hre : FeedbackEnvironment.reroot (s : ℝ)
        (Matching.feedbackSceneEnvironment (reroot (-(s : ℝ)) scene)) =
        Matching.feedbackSceneEnvironment scene := by
      change Matching.feedbackSceneEnvironment (reroot (s : ℝ) (reroot (-(s : ℝ)) scene)) = _
      rw [reroot_add, neg_add_cancel, reroot_zero]
    rw [hre] at he
    dsimp only
    rw [he, mul_comm]

/-- The actual marked compensator martingale follows from compact past-cylinder identities. -/
theorem markedCompensator_martingale_of_pastCylinderResidualIdentities
    (μ : Measure MatchingScene) [IsFiniteMeasure μ] (lam : ℝ)
    (hstationary : ∀ a : ℝ, MeasurePreserving (reroot a) μ μ)
    (hcuts : ∀ x : ℝ, ∀ᵐ scene ∂μ, scene.VacantCut x)
    (hcount : ∀ (b : Bool) (t : ℝ≥0), Integrable (fun scene ↦
      (LocalConfiguration.spatialCount
        (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ)) μ)
    (hCc : PastCylinderResidualIdentities μ lam) (b : Bool) (ψ : UnitMark →ᵇ ℝ) :
    Martingale (fun t scene ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene)) markedCountFiltration μ :=
  markedCompensator_martingale_of_cylinder_residuals μ hcount lam
    (cylinder_residuals_of_pastCylinderResidualIdentities μ lam hstationary hcuts hcount hCc) b ψ

end OTSelector.PointProcess.MatchingScene
