import OTSelector.Limit.FeedbackStationaryFuture

/-!
# Finite-history transitions of the actual stationary future

The forward path read from the actual cell roof is the Ionescu--Tulcea process with invariant
initial current. Consequently every finite revealed history has the original marked holding
kernel as its next-step conditional distribution.
-/

open MeasureTheory ProbabilityTheory Set Filter Preorder
open scoped ENNReal

namespace OTSelector.Limit

/-- The actual marked feedback process with invariant initial current and virtual initial mark. -/
noncomputable def feedbackStationaryMarkedTrajectory (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Measure FeedbackCellPath := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  exact Kernel.trajMeasure (X := fun _ ↦ FeedbackMarkedStep)
    ((invariantCurrentMeasure lam).map feedbackMarkedVirtual) (feedbackMarkedHistoryKernel lam)

instance feedbackStationaryMarkedTrajectory_isProbability (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : IsProbabilityMeasure
      (feedbackStationaryMarkedTrajectory lam hlam0 hlam) := by
  have : IsProbabilityMeasure (invariantCurrentMeasure lam) :=
    ⟨invariantCurrentMeasure_apply_univ hlam0 hlam⟩
  have : IsProbabilityMeasure ((invariantCurrentMeasure lam).map feedbackMarkedVirtual) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  unfold feedbackStationaryMarkedTrajectory
  infer_instance

/-- Mixing the actual deterministic-current processes gives the invariant-initial process. -/
theorem feedbackCurrentTrajectoryKernel_comp_invariant {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    feedbackCurrentTrajectoryKernel lam hlam0 hlam ∘ₘ invariantCurrentMeasure lam =
      feedbackStationaryMarkedTrajectory lam hlam0 hlam := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  unfold feedbackStationaryMarkedTrajectory Kernel.trajMeasure
  ext s hs
  rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
    Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hs) (MeasurableEquiv.measurable _)]
  change (∫⁻ k, (feedbackCurrentTrajectoryKernel lam hlam0 hlam k) s
      ∂invariantCurrentMeasure lam) =
    ∫⁻ a : FeedbackMarkedStep, (Kernel.traj (X := fun _ ↦ FeedbackMarkedStep)
      (feedbackMarkedHistoryKernel lam) 0 (fun _ ↦ a)) s
      ∂(invariantCurrentMeasure lam).map feedbackMarkedVirtual
  have hm : Measurable (fun a : FeedbackMarkedStep ↦
      (Kernel.traj (X := fun _ ↦ FeedbackMarkedStep) (feedbackMarkedHistoryKernel lam) 0
        (fun _ ↦ a)) s) :=
    (Kernel.measurable_coe _ hs).comp (measurable_pi_lambda _ fun _ ↦ measurable_id)
  rw [lintegral_map hm (measurable_of_countable feedbackMarkedVirtual)]
  apply lintegral_congr
  intro k
  exact congrArg (fun μ : Measure FeedbackCellPath ↦ μ s)
    (feedbackMarkedTrajectory_eq_traj lam hlam0 hlam k)

/-- The complete future of the actual roof has the invariant-initial feedback process law. -/
theorem feedbackReturnRoofLaw_map_future {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (PointProcess.feedbackReturnRoofLaw lam hlam0 hlam).map feedbackRoofFuture =
      feedbackStationaryMarkedTrajectory lam hlam0 hlam := by
  have h := congrArg Measure.snd
    (feedbackReturnRoofLaw_map_current_future hlam0 hlam)
  rw [Measure.snd_map_prodMk measurable_feedbackRoofFutureCurrent,
    Measure.snd_compProd, feedbackCurrentTrajectoryKernel_comp_invariant hlam0 hlam] at h
  exact h

/-- Every finite marked history of the invariant-initial process has the actual next-step kernel. -/
theorem feedbackStationaryMarkedTrajectory_condDistrib {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    condDistrib (fun w : FeedbackCellPath ↦ w (n + 1)) (frestrictLe n)
      (feedbackStationaryMarkedTrajectory lam hlam0 hlam) =ᵐ[
        (feedbackStationaryMarkedTrajectory lam hlam0 hlam).map (frestrictLe n)]
          feedbackMarkedHistoryKernel lam n := by
  have : IsProbabilityMeasure (invariantCurrentMeasure lam) :=
    ⟨invariantCurrentMeasure_apply_univ hlam0 hlam⟩
  have : IsProbabilityMeasure ((invariantCurrentMeasure lam).map feedbackMarkedVirtual) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  exact Kernel.condDistrib_trajMeasure (X := fun _ ↦ FeedbackMarkedStep)

/-- On the original occupation probability space, the next wait, mark and current conditional
on every finite future history have the actual feedback holding kernel. -/
theorem feedbackRoofFuture_history_condDistrib {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (n : ℕ) :
    condDistrib (fun p ↦ feedbackRoofFuture p (n + 1))
      (fun p ↦ frestrictLe n (feedbackRoofFuture p))
      (PointProcess.feedbackReturnRoofLaw lam hlam0 hlam) =ᵐ[
        (PointProcess.feedbackReturnRoofLaw lam hlam0 hlam).map
          (fun p ↦ frestrictLe n (feedbackRoofFuture p))]
            feedbackMarkedHistoryKernel lam n := by
  have h := condDistrib_map (X := frestrictLe n)
    (Y := fun w : FeedbackCellPath ↦ w (n + 1))
    (ν := PointProcess.feedbackReturnRoofLaw lam hlam0 hlam)
    (measurable_frestrictLe n).aemeasurable (measurable_pi_apply _).aemeasurable
    measurable_feedbackRoofFuture.aemeasurable
  simp only [feedbackReturnRoofLaw_map_future hlam0 hlam] at h
  have hk := feedbackStationaryMarkedTrajectory_condDistrib hlam0 hlam n
  have he : (feedbackStationaryMarkedTrajectory lam hlam0 hlam).map (frestrictLe n) =
      (PointProcess.feedbackReturnRoofLaw lam hlam0 hlam).map
        (frestrictLe n ∘ feedbackRoofFuture) := by
    rw [← feedbackReturnRoofLaw_map_future hlam0 hlam,
      Measure.map_map (measurable_frestrictLe n) measurable_feedbackRoofFuture]
  rw [he] at hk
  exact h.symm.trans hk

/-- At a stationary observation point the next actual waiting time, mark and new current have
the exponential holding/marked-jump product kernel, conditional on the environment current. -/
theorem feedbackRoofFuture_firstStep_condDistrib {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    condDistrib (fun p ↦ feedbackRoofFuture p 1) (feedbackRoofEnvironmentCurrent lam)
      (PointProcess.feedbackReturnRoofLaw lam hlam0 hlam) =ᵐ[invariantCurrentMeasure lam]
        feedbackMarkedHoldingKernel lam := by
  have h := condDistrib_comp (mβ := inferInstance) (feedbackRoofEnvironmentCurrent lam)
    (μ := PointProcess.feedbackReturnRoofLaw lam hlam0 hlam)
    measurable_feedbackRoofFuture.aemeasurable (measurable_pi_apply 1)
  rw [feedbackReturnRoofLaw_map_environmentCurrent hlam0 hlam] at h
  filter_upwards [h, feedbackRoofFuture_condDistrib hlam0 hlam] with k hk hfull
  calc
    _ = ((condDistrib feedbackRoofFuture (feedbackRoofEnvironmentCurrent lam)
      (PointProcess.feedbackReturnRoofLaw lam hlam0 hlam)).map (fun w ↦ w 1)) k := hk
    _ = (feedbackMarkedTrajectory lam hlam0 hlam k).map (fun w ↦ w 1) := by
      rw [Kernel.map_apply _ (measurable_pi_apply 1), hfull]
      rfl
    _ = feedbackMarkedHoldingKernel lam k := feedbackMarkedTrajectory_map_one hlam0 hlam k

end OTSelector.Limit
