import OTSelector.Feedback.FeedbackEnvironmentPastPoints

/-!
# Actual environment past cylinders in the revealed filtration

The canonical cylinder uses finitely many two-color compact point tests supported in the
negative half line and the current at the root. The actual finite process uses the raw
exploration, and is globally adapted and jointly measurable. On survival through the horizon
it is exactly the cylinder of the stopped rooted environment used in the marked spatial
averages. No matching edge is observed.

This is the finite-model adaptation bridge. It does not assert a monotone-class theorem or
identification of an entire past sigma algebra; those use the natural marked-count filtration
in the martingale-problem closure.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped Classical BigOperators NNReal CompactlySupported BoundedContinuousFunction

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector
namespace PointProcess

/-- Finite coordinates of an environment past cylinder: source tests, target tests, and current. -/
abbrev EnvironmentPastCoordinates (s t : ℕ) := (Fin s → ℝ) × (Fin t → ℝ) × ℝ

/-- A bounded continuous cylinder of the actual environment, without any edge information. -/
noncomputable def environmentPastCylinder {s t : ℕ}
    (fs : Fin s → C_c(MatchingPoint, ℝ)) (ft : Fin t → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates s t →ᵇ ℝ) (e : FeedbackEnvironment) : ℝ :=
  H (fun i ↦ LocalConfiguration.testIntegral e.source (fs i),
    fun j ↦ LocalConfiguration.testIntegral e.target (ft j), (e.path.rootCurrent : ℝ))

/-- Canonical cylinders are measurable in the existing actual environment carrier. -/
theorem measurable_environmentPastCylinder {s t : ℕ}
    (fs : Fin s → C_c(MatchingPoint, ℝ)) (ft : Fin t → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates s t →ᵇ ℝ) :
    Measurable (environmentPastCylinder fs ft H) := by
  exact H.continuous.measurable.comp
    ((measurable_pi_lambda _ fun i ↦ (LocalConfiguration.measurable_testIntegral (fs i)).comp
      FeedbackEnvironment.measurable_source).prodMk
      ((measurable_pi_lambda _ fun j ↦ (LocalConfiguration.measurable_testIntegral (ft j)).comp
        FeedbackEnvironment.measurable_target).prodMk
        ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
          FeedbackEnvironment.measurable_rootCurrent)))

theorem norm_environmentPastCylinder_le {s t : ℕ}
    (fs : Fin s → C_c(MatchingPoint, ℝ)) (ft : Fin t → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates s t →ᵇ ℝ) (e : FeedbackEnvironment) :
    ‖environmentPastCylinder fs ft H e‖ ≤ ‖H‖ := H.norm_coe_le_norm _

end PointProcess

namespace FiniteSample

open PointProcess CountingProcess
variable {n : ℕ} {lam : ℝ}

/-- The safe actual current is jointly measurable, including at its jump times. -/
theorem measurable_safeCurrentAt_real_uncurry (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) : Measurable (fun p : ℝ≥0 × FiniteSample n ↦
      (safeCurrentAt hlam0 hlamHalf B 0 p.1 p.2 : ℝ)) := by
  have hK : Measurable (fun sample : FiniteSample n ↦ (safeK0 lam B 0 sample : ℝ)) :=
    ((safeK0_stronglyMeasurable_usual_zero hlam0 hlamHalf B 0).mono
      ((usualRevealedFiltration (n := n) hlam0 hlamHalf B 0).le 0)).measurable
  have hsource : Measurable (fun p : ℝ≥0 × FiniteSample n ↦
      (safeSourceCount hlam0 hlamHalf B 0 p.1 p.2 : ℝ)) := by
    simp only [safeSourceCount, finiteEventCountTop_cast_eq_sum]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite (measurableSet_le
      ((sourceEventTime_isStoppingTime (n := n) hlam0 hlamHalf B 0 i).measurable'.comp measurable_snd)
      (Measurable.withTop_coe measurable_fst)) measurable_const measurable_const
  have htarget : Measurable (fun p : ℝ≥0 × FiniteSample n ↦
      (safeTargetCount hlam0 hlamHalf B 0 p.1 p.2 : ℝ)) := by
    simp only [safeTargetCount, finiteEventCountTop_cast_eq_sum]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite (measurableSet_le
      ((targetEventTime_isStoppingTime (n := n) hlam0 hlamHalf B 0 i).measurable'.comp measurable_snd)
      (Measurable.withTop_coe measurable_fst)) measurable_const measurable_const
  convert ((hK.comp measurable_snd).add hsource).sub htarget using 1
  ext p
  simp only [safeCurrentAt_eq_K0_add_counts, Int.cast_sub, Int.cast_add, Int.cast_natCast,
    Pi.sub_apply, Pi.add_apply, Function.comp_apply]

/-- Globally adapted finite-model version of an actual environment cylinder. -/
noncomputable def safeEnvironmentPastCylinder (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) {s t : ℕ}
    (fs : Fin s → C_c(MatchingPoint, ℝ)) (ft : Fin t → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates s t →ᵇ ℝ) (u : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  H (fun i ↦ safeSourcePastTest hlam0 hlamHalf B (fs i) u sample,
    fun j ↦ safeTargetPastTest hlam0 hlamHalf B (ft j) u sample,
      (safeCurrentAt hlam0 hlamHalf B 0 u sample : ℝ))

/-- Negative-support point cylinders satisfy the actual filtration hypothesis of the marked
spatial average theorem at every observation time. -/
theorem safeEnvironmentPastCylinder_stronglyAdapted (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) {s t : ℕ}
    (fs : Fin s → C_c(MatchingPoint, ℝ)) (ft : Fin t → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates s t →ᵇ ℝ)
    (hs : ∀ i v, fs i (0,v) = 0) (ht : ∀ j v, ft j (0,v) = 0) :
    StronglyAdapted (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (safeEnvironmentPastCylinder hlam0 hlamHalf B fs ft H) := by
  intro u
  let : MeasurableSpace (FiniteSample n) := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 u
  have hsource : Measurable[usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 u]
      (fun sample i ↦ safeSourcePastTest hlam0 hlamHalf B (fs i) u sample) := by
    exact measurable_pi_iff.mpr fun i ↦ (safeSourcePastTest_stronglyAdapted hlam0 hlamHalf B
      (fs i) (fs i).continuous.measurable (hs i) u).measurable
  have htarget : Measurable[usualRevealedFiltration (n := n) hlam0 hlamHalf B 0 u]
      (fun sample j ↦ safeTargetPastTest hlam0 hlamHalf B (ft j) u sample) := by
    exact measurable_pi_iff.mpr fun j ↦ (safeTargetPastTest_stronglyAdapted hlam0 hlamHalf B
      (ft j) (ft j).continuous.measurable (ht j) u).measurable
  exact (H.continuous.measurable.comp (hsource.prodMk (htarget.prodMk
    (rightBoundaryCurrent_stronglyMeasurable hlam0 hlamHalf B 0 u).measurable))).stronglyMeasurable

/-- The same process is jointly measurable, as required for the spatial-average integral. -/
theorem measurable_safeEnvironmentPastCylinder (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) {s t : ℕ}
    (fs : Fin s → C_c(MatchingPoint, ℝ)) (ft : Fin t → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates s t →ᵇ ℝ) :
    Measurable (Function.uncurry (safeEnvironmentPastCylinder (n := n) hlam0 hlamHalf B fs ft H)) := by
  exact H.continuous.measurable.comp
    ((measurable_pi_lambda _ fun i ↦ measurable_safeSourcePastTest hlam0 hlamHalf B
      (fs i) (fs i).continuous.measurable).prodMk
      ((measurable_pi_lambda _ fun j ↦ measurable_safeTargetPastTest hlam0 hlamHalf B
        (ft j) (ft j).continuous.measurable).prodMk
        (measurable_safeCurrentAt_real_uncurry hlam0 hlamHalf B)))

/-- Uniformity comes from the outer test, independently of sample size and elapsed time. -/
theorem norm_safeEnvironmentPastCylinder_le (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (B : ℝ) {s t : ℕ}
    (fs : Fin s → C_c(MatchingPoint, ℝ)) (ft : Fin t → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates s t →ᵇ ℝ) (u : ℝ≥0) (sample : FiniteSample n) :
    ‖safeEnvironmentPastCylinder hlam0 hlamHalf B fs ft H u sample‖ ≤ ‖H‖ := H.norm_coe_le_norm _

/-- At every surviving bulk cut the adapted cylinder is exactly the canonical cylinder of the
actual stopped environment used in `environmentMarkedSpatialAverage`. -/
theorem safeEnvironmentPastCylinder_eq_stopped (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1/2)
    (eta B : ℝ) (T u : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample = (T : WithTop ℝ≥0))
    (hu : u ≤ T) {s t : ℕ}
    (fs : Fin s → C_c(MatchingPoint, ℝ)) (ft : Fin t → C_c(MatchingPoint, ℝ))
    (H : EnvironmentPastCoordinates s t →ᵇ ℝ)
    (hs : ∀ i x v, 0 ≤ x → fs i (x,v) = 0)
    (ht : ∀ j x v, 0 ≤ x → ft j (x,v) = 0) :
    safeEnvironmentPastCylinder hlam0 hlamHalf B fs ft H u sample =
      environmentPastCylinder fs ft H (Matching.feedbackSceneEnvironment
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B + (u : ℝ)))) := by
  have hsource : (fun i ↦ safeSourcePastTest hlam0 hlamHalf B (fs i) u sample) =
      (fun i ↦ LocalConfiguration.testIntegral (Matching.feedbackSceneEnvironment
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B + (u : ℝ)))).source (fs i)) := by
    funext i
    exact safeSourcePastTest_eq_stopped_environment_test hlam0 hlamHalf eta B T u sample
      hgood hstop hu (fs i) (hs i)
  have htarget : (fun j ↦ safeTargetPastTest hlam0 hlamHalf B (ft j) u sample) =
      (fun j ↦ LocalConfiguration.testIntegral (Matching.feedbackSceneEnvironment
        (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (B + (u : ℝ)))).target (ft j)) := by
    funext j
    exact safeTargetPastTest_eq_stopped_environment_test hlam0 hlamHalf eta B T u sample
      hgood hstop hu (ft j) (ht j)
  have hcurrent := feedbackEnvironmentCurrent_stoppedScene_eq_safeCurrentAt hlam0 hlamHalf
    eta B T u sample hgood hstop hu (B + (u : ℝ)) 0 (by ring)
  simp only [Limit.feedbackEnvironmentCurrent, FeedbackEnvironment.currentIncrement,
    LocalConfiguration.orientedCount_self, sub_self, add_zero] at hcurrent
  simp only [safeEnvironmentPastCylinder, environmentPastCylinder, hsource, htarget, hcurrent]

end FiniteSample
end OTSelector
