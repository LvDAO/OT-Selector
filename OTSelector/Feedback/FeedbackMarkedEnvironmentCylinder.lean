import OTSelector.Feedback.FeedbackMarkedEnvironmentProbability
import OTSelector.Feedback.FeedbackEnvironmentPast

/-! # Actual scene past-cylinder marked residuals vanish on good surviving samples -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal Topology CompactlySupported BoundedContinuousFunction
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

namespace OTSelector.FiniteSample
open PointProcess CountingProcess
variable {n : ℕ} {lam eta : ℝ}

/-- A spatial martingale test written entirely in the original finite rooted environments.
The past test uses their two-color configurations and root current; the future residual uses
their actual marked counts and ideal feedback drift. -/
noncomputable def environmentPastMarkedSpatialResidual
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) (a d : ℝ) (sample : FiniteSample n) : ℝ :=
  (d-a)⁻¹ * ∫x in Ioc a d,
    environmentPastCylinder fs ft H (Matching.feedbackSceneEnvironment
      (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+x))) *
    Limit.feedbackEnvironmentMarkedCompensator lam b ψ t (Matching.feedbackSceneEnvironment
      (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+x)))

/-- The globally adapted finite test equals the actual scene test throughout a surviving
root window. The equivalence only uses information from the environment past. -/
theorem environmentPastMarkedSpatialResidual_eq_adapted
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (hs : ∀i x v, 0 ≤ x → fs i (x,v) = 0)
    (ht : ∀j x v, 0 ≤ x → ft j (x,v) = 0)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) {a d : ℝ} (ha : 0 ≤ a) (hd : d ≤ T)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0)) :
    environmentPastMarkedSpatialResidual hlam0 hlamHalf eta B T fs ft H b ψ t a d sample =
      environmentMarkedSpatialAverage hlam0 hlamHalf eta B T b ψ
        (safeEnvironmentPastCylinder hlam0 hlamHalf B fs ft H) t a d sample := by
  unfold environmentPastMarkedSpatialResidual environmentMarkedSpatialAverage
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hx0 : 0 ≤ x := ha.trans hx.1.le
  have hu : x.toNNReal ≤ T := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hx0]
    exact hx.2.trans hd
  have he := safeEnvironmentPastCylinder_eq_stopped hlam0 hlamHalf eta B T x.toNNReal sample
    hNoTie hstop hu fs ft H hs ht
  rw [Real.coe_toNNReal _ hx0] at he
  exact congrArg (fun v ↦ v * Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
    (Matching.feedbackSceneEnvironment
      (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B+x)))) he.symm

/-- The actual scene residual failure, restricted to the original VC-good survival event. -/
def environmentPastMarkedResidualBadEvent
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) (a d δ : ℝ) : Set (FiniteSample n) :=
  {sample | sample ∈ feedbackA1GoodEvent n lam B 0 ∧
    safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0) ∧
    δ ≤ ‖environmentPastMarkedSpatialResidual hlam0 hlamHalf eta B T fs ft H b ψ t a d sample‖}

theorem environmentPastMarkedResidualBadEvent_eq_adapted
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2) (eta B : ℝ) (T : ℝ≥0)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (hs : ∀i x v, 0 ≤ x → fs i (x,v) = 0)
    (ht : ∀j x v, 0 ≤ x → ft j (x,v) = 0)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) {a d : ℝ} (ha : 0 ≤ a) (hd : d ≤ T) (δ : ℝ) :
    environmentPastMarkedResidualBadEvent (n := n) hlam0 hlamHalf eta B T fs ft H b ψ t a d δ =
      environmentMarkedResidualBadEvent hlam0 hlamHalf eta B T b ψ
        (safeEnvironmentPastCylinder hlam0 hlamHalf B fs ft H) t a d δ := by
  ext sample
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  constructor <;> rintro ⟨hg, hstop, herr⟩
  · exact ⟨hg, hstop, by
      rwa [environmentPastMarkedSpatialResidual_eq_adapted hlam0 hlamHalf eta B T fs ft H
        hs ht b ψ t ha hd sample hg.1 hstop] at herr⟩
  · exact ⟨hg, hstop, by
      rwa [environmentPastMarkedSpatialResidual_eq_adapted hlam0 hlamHalf eta B T fs ft H
        hs ht b ψ t ha hd sample hg.1 hstop]⟩

/-- Every genuine bounded continuous past-cylinder marked test vanishes in probability on
the original good surviving samples. The filtration, measurability, mark law, and drift
approximation are all instantiated by the actual finite model. -/
theorem tendsto_measureReal_environmentPastMarkedResidualBadEvent_zero
    (hlam0 : 0 < lam) (hlam : lam < 1/8) (heta : 0 ≤ eta) (hetaSmall : eta*(2+lam) ≤ lam)
    {amplitude δ : ℝ} (hamp : 0 < amplitude) (hδ : 0 < δ)
    (T : ℕ → ℝ≥0) (t : ℝ≥0) (a d : ℕ → ℝ)
    (hwindow : ∀ᶠ n in atTop, 0 ≤ a n ∧ a n < d n ∧ d n+(t:ℝ) < T n)
    (hwidth : Tendsto (fun n ↦ d n-a n) atTop atTop)
    {ns nt : ℕ} (fs : Fin ns → C_c(MatchingPoint, ℝ))
    (ft : Fin nt → C_c(MatchingPoint, ℝ)) (H : EnvironmentPastCoordinates ns nt →ᵇ ℝ)
    (hs : ∀i x v, 0 ≤ x → fs i (x,v) = 0)
    (ht : ∀j x v, 0 ≤ x → ft j (x,v) = 0)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) :
    Tendsto (fun n ↦ (finiteSampleLaw n : Measure (FiniteSample n)).real
      (environmentPastMarkedResidualBadEvent hlam0.le (by linarith) eta
        (feedbackA2AsymptoticBuffer amplitude n) (T n) fs ft H b ψ t (a n) (d n) δ))
      atTop (nhds 0) := by
  have hbase := tendsto_measureReal_environmentMarkedResidualBadEvent_zero
    hlam0 hlam heta hetaSmall hamp hδ T t a d hwindow hwidth b ψ ψ.continuous
    (norm_nonneg ψ) (fun v ↦ ψ.norm_coe_le_norm v)
    (fun n ↦ safeEnvironmentPastCylinder hlam0.le (by linarith)
      (feedbackA2AsymptoticBuffer amplitude n) fs ft H)
    (fun n ↦ safeEnvironmentPastCylinder_stronglyAdapted hlam0.le (by linarith)
      (feedbackA2AsymptoticBuffer amplitude n) fs ft H
      (fun i v ↦ hs i 0 v le_rfl) (fun j v ↦ ht j 0 v le_rfl))
    (fun n ↦ measurable_safeEnvironmentPastCylinder hlam0.le (by linarith)
      (feedbackA2AsymptoticBuffer amplitude n) fs ft H)
    (norm_nonneg H) (fun n u ω ↦ norm_safeEnvironmentPastCylinder_le hlam0.le (by linarith)
      (feedbackA2AsymptoticBuffer amplitude n) fs ft H u ω)
  apply hbase.congr'
  filter_upwards [hwindow] with n hn
  rw [environmentPastMarkedResidualBadEvent_eq_adapted hlam0.le (by linarith) eta
    (feedbackA2AsymptoticBuffer amplitude n) (T n) fs ft H hs ht b ψ t hn.1
    (by linarith [hn.2.2, t.2]) δ]

end OTSelector.FiniteSample
