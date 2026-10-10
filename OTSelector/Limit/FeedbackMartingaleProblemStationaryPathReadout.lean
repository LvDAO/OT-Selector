import OTSelector.Limit.FeedbackStationaryFutureEnvironment

/-!
# Physical readouts of the invariant-initial marked trajectory

The current in coordinate zero is the actual initial-current label: each deterministic-current
trajectory starts at its proved virtual coordinate. Reading both positive point measures from
the invariant-initial path therefore gives the same joint law as the stationary environment.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 200000

namespace OTSelector.Limit

open PointProcess

/-- The coordinate-zero current and the complete path retain the original invariant-current
mixture. The current identification uses the proved virtual initial coordinate of each path law. -/
theorem feedbackStationaryMarkedTrajectory_map_current_future {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    (feedbackStationaryMarkedTrajectory lam hlam0 hlam).map
      (fun w ↦ ((w 0).2.2, w)) =
        invariantCurrentMeasure lam ⊗ₘ feedbackCurrentTrajectoryKernel lam hlam0 hlam := by
  have : IsProbabilityMeasure (invariantCurrentMeasure lam) :=
    ⟨invariantCurrentMeasure_apply_univ hlam0 hlam⟩
  have hzero : Measurable (fun p : ℤ × FeedbackCellPath ↦ (p.2 0).2.2) :=
    ((measurable_pi_apply 0).comp measurable_snd).snd.snd
  have hsupp : ∀ᵐ p ∂(invariantCurrentMeasure lam ⊗ₘ
      feedbackCurrentTrajectoryKernel lam hlam0 hlam), (p.2 0).2.2 = p.1 := by
    apply Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hzero measurable_fst)
    apply Eventually.of_forall
    intro k
    filter_upwards [feedbackMarkedTrajectory_initial hlam0 hlam k] with w hw
    rw [hw]
    rfl
  have hsnd : (invariantCurrentMeasure lam ⊗ₘ
      feedbackCurrentTrajectoryKernel lam hlam0 hlam).map Prod.snd =
        feedbackStationaryMarkedTrajectory lam hlam0 hlam := by
    change (invariantCurrentMeasure lam ⊗ₘ
      feedbackCurrentTrajectoryKernel lam hlam0 hlam).snd = _
    rw [Measure.snd_compProd, feedbackCurrentTrajectoryKernel_comp_invariant hlam0 hlam]
  have hObs : Measurable (fun w : FeedbackCellPath ↦ ((w 0).2.2, w)) :=
    (measurable_pi_apply 0).snd.snd.prodMk measurable_id
  rw [← hsnd, Measure.map_map hObs measurable_snd]
  calc
    _ = (invariantCurrentMeasure lam ⊗ₘ
        feedbackCurrentTrajectoryKernel lam hlam0 hlam).map id := by
      apply Measure.map_congr
      filter_upwards [hsupp] with p hp
      exact Prod.ext hp rfl
    _ = _ := Measure.map_id

/-- Reading the initial current and both physical forward point measures from the stationary
marked trajectory gives the actual feedback point-process kernel. -/
theorem feedbackStationaryMarkedTrajectory_map_current_positivePoints {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    (feedbackStationaryMarkedTrajectory lam hlam0 hlam).map
      (fun w ↦ ((w 0).2.2, feedbackFuturePointMeasures w)) =
        invariantCurrentMeasure lam ⊗ₘ feedbackFuturePointKernel lam hlam0 hlam := by
  have hObs : Measurable (fun w : FeedbackCellPath ↦ ((w 0).2.2, w)) :=
    (measurable_pi_apply 0).snd.snd.prodMk measurable_id
  have h := congrArg (fun μ : Measure (ℤ × FeedbackCellPath) ↦
      μ.map (Prod.map id feedbackFuturePointMeasures))
    (feedbackStationaryMarkedTrajectory_map_current_future hlam0 hlam)
  rw [Measure.map_map (measurable_id.prodMap measurable_feedbackFuturePointMeasures) hObs,
    ← Measure.compProd_map measurable_feedbackFuturePointMeasures] at h
  exact h

/-- The physical current/positive-configuration readout of the invariant-initial path is the
same joint distribution as the actual stationary feedback environment. -/
theorem feedbackStationaryMarkedTrajectory_map_current_positivePoints_eq_environment {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    (feedbackStationaryMarkedTrajectory lam hlam0 hlam).map
      (fun w ↦ ((w 0).2.2, feedbackFuturePointMeasures w)) =
    (feedbackStationaryEnvironmentLaw lam hlam0 hlam).map
      (fun e ↦ (e.path.rootCurrent, feedbackPositiveEnvironmentPoints e)) := by
  rw [feedbackStationaryMarkedTrajectory_map_current_positivePoints hlam0 hlam,
    feedbackStationaryEnvironmentLaw_map_current_positivePoints hlam0 hlam]

end OTSelector.Limit
