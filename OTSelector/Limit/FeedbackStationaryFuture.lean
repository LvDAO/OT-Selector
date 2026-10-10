import OTSelector.Limit.FeedbackStationaryFutureOccupation
import OTSelector.Limit.FeedbackStationaryFutureRoof
import OTSelector.Limit.FeedbackStationaryFutureGeometry

/-!
# The complete marked future of the actual stationary feedback construction

The actual normalized cell roof carries a complete forward marked trajectory. Conditional on
its current at the observation point, this future has the original feedback trajectory law.
Its initial current distribution is the proved invariant law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace OTSelector.Limit

open PointProcess

attribute [local instance] Classical.propDecidable

/-- The actual forward path at the observation point of the iid cell suspension. -/
noncomputable def feedbackRoofFuture (p : FeedbackCellSequence × ℝ) : FeedbackCellPath :=
  feedbackCellFuture (feedbackConcatPositiveCellPaths p.1) p.2

@[fun_prop]
theorem measurable_feedbackRoofFuture : Measurable feedbackRoofFuture :=
  measurable_feedbackCellFuture.comp
    (f := fun p : FeedbackCellSequence × ℝ ↦ (feedbackConcatPositiveCellPaths p.1, p.2))
    (measurable_feedbackConcatPositiveCellPaths.prodMap measurable_id)

/-- The current read from the same physical cell roof as the complete future. -/
noncomputable def feedbackRoofFutureCurrent (p : FeedbackCellSequence × ℝ) : ℤ :=
  feedbackCellCurrent (feedbackConcatPositiveCellPaths p.1) p.2

@[fun_prop]
theorem measurable_feedbackRoofFutureCurrent : Measurable feedbackRoofFutureCurrent :=
  measurable_feedbackCellCurrent.comp
    (f := fun p : FeedbackCellSequence × ℝ ↦ (feedbackConcatPositiveCellPaths p.1, p.2))
    (measurable_feedbackConcatPositiveCellPaths.prodMap measurable_id)

/-- The genuine full feedback trajectory kernel indexed by its starting current. -/
noncomputable def feedbackCurrentTrajectoryKernel (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Kernel ℤ FeedbackCellPath where
  toFun k := feedbackMarkedTrajectory lam hlam0 hlam k
  measurable' := measurable_of_countable _

instance feedbackCurrentTrajectoryKernel_isMarkov (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : IsMarkovKernel (feedbackCurrentTrajectoryKernel lam hlam0 hlam) :=
  ⟨fun k ↦ feedbackMarkedTrajectory_isProbability hlam0 hlam k⟩

/-- The actual cell roof, on each current atom, carries the complete trajectory from that current. -/
theorem lintegral_feedbackRoofFuture_current {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) {f : FeedbackCellPath → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, if feedbackRoofFutureCurrent p = k then f (feedbackRoofFuture p) else 0
      ∂feedbackReturnRoofLaw lam hlam0 hlam) =
      ENNReal.ofReal (invariantMass lam k) *
        ∫⁻ w, f w ∂feedbackMarkedTrajectory lam hlam0 hlam k := by
  have hF : Measurable (fun p : FeedbackCellPath × ℝ ↦
      if feedbackCellCurrent p.1 p.2 = k then f (feedbackCellFuture p.1 p.2) else 0) :=
    (hf.comp measurable_feedbackCellFuture).ite
      (measurableSet_eq_fun measurable_feedbackCellCurrent measurable_const) measurable_const
  unfold feedbackRoofFutureCurrent feedbackRoofFuture
  rw [lintegral_feedbackReturnRoofLaw_concatPositive lam hlam0 hlam hF]
  exact lintegral_feedbackCellFuture_state_normalized hlam0 hlam k hf

/-- All joint nonnegative observations of the real current and the complete forward path have
the invariant-current mixture of actual trajectory expectations. -/
theorem lintegral_feedbackRoofFuture_joint {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {F : ℤ × FeedbackCellPath → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F (feedbackRoofFutureCurrent p, feedbackRoofFuture p)
      ∂feedbackReturnRoofLaw lam hlam0 hlam) =
      ∑' k : ℤ, ENNReal.ofReal (invariantMass lam k) *
        ∫⁻ w, F (k, w) ∂feedbackMarkedTrajectory lam hlam0 hlam k := by
  have hsplit (p : FeedbackCellSequence × ℝ) :
      F (feedbackRoofFutureCurrent p, feedbackRoofFuture p) =
        ∑' k : ℤ, if feedbackRoofFutureCurrent p = k then F (k, feedbackRoofFuture p) else 0 := by
    rw [tsum_eq_single (feedbackRoofFutureCurrent p)]
    · simp
    · intro k hk
      simp [Ne.symm hk]
  simp_rw [hsplit]
  have hterm (k : ℤ) : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      if feedbackRoofFutureCurrent p = k then F (k, feedbackRoofFuture p) else 0) :=
    (((hF.comp measurable_prodMk_left).comp measurable_feedbackRoofFuture).ite
      (measurableSet_eq_fun measurable_feedbackRoofFutureCurrent measurable_const)
      measurable_const)
  rw [lintegral_tsum (fun k ↦ (hterm k).aemeasurable)]
  apply tsum_congr
  intro k
  exact lintegral_feedbackRoofFuture_current hlam0 hlam k
    (hF.comp measurable_prodMk_left)

/-- The joint current/future law of the actual stationary roof is the actual invariant measure
composed with the original complete marked trajectory kernel. -/
theorem feedbackReturnRoofLaw_map_current_future {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackReturnRoofLaw lam hlam0 hlam).map
      (fun p ↦ (feedbackRoofFutureCurrent p, feedbackRoofFuture p)) =
      invariantCurrentMeasure lam ⊗ₘ feedbackCurrentTrajectoryKernel lam hlam0 hlam := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_feedbackRoofFutureCurrent.prodMk measurable_feedbackRoofFuture),
    lintegral_feedbackRoofFuture_joint hlam0 hlam hF, Measure.lintegral_compProd hF,
    lintegral_countable']
  apply tsum_congr
  intro k
  rw [invariantCurrentMeasure, withDensity_apply _ (measurableSet_singleton k), lintegral_singleton]
  simp only [Measure.count_singleton, mul_one]
  exact mul_comm _ _

/-- The actual environment's root current on the return-roof probability space. -/
noncomputable def feedbackRoofEnvironmentCurrent (lam : ℝ)
    (p : FeedbackCellSequence × ℝ) : ℤ :=
  (feedbackReturnEnvironmentObservation lam p).2.path.rootCurrent

@[fun_prop]
theorem measurable_feedbackRoofEnvironmentCurrent (lam : ℝ) :
    Measurable (feedbackRoofEnvironmentCurrent lam) :=
  FeedbackEnvironment.measurable_rootCurrent.comp
    (f := fun p : FeedbackCellSequence × ℝ ↦ (feedbackReturnEnvironmentObservation lam p).2)
    (measurable_feedbackReturnEnvironmentObservation lam).snd

/-- The current used by the forward path agrees with the actual environment observable. -/
theorem feedbackRoofEnvironmentCurrent_eq_futureCurrent {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : feedbackRoofEnvironmentCurrent lam =ᵐ[
      feedbackReturnRoofLaw lam hlam0 hlam] feedbackRoofFutureCurrent :=
  feedbackReturnRoofLaw_rootCurrent_eq_concatPositive lam hlam0 hlam

/-- Joint identification with the actual observable environment current, rather than an
auxiliary state label supplied to the trajectory construction. -/
theorem feedbackReturnRoofLaw_map_environmentCurrent_future {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackReturnRoofLaw lam hlam0 hlam).map
      (fun p ↦ (feedbackRoofEnvironmentCurrent lam p, feedbackRoofFuture p)) =
      invariantCurrentMeasure lam ⊗ₘ feedbackCurrentTrajectoryKernel lam hlam0 hlam := by
  rw [← feedbackReturnRoofLaw_map_current_future hlam0 hlam]
  apply Measure.map_congr
  filter_upwards [feedbackRoofEnvironmentCurrent_eq_futureCurrent hlam0 hlam] with p hp
  rw [hp]

/-- The same roof has the proved invariant law for the actual root-current observable. -/
theorem feedbackReturnRoofLaw_map_environmentCurrent {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackReturnRoofLaw lam hlam0 hlam).map (feedbackRoofEnvironmentCurrent lam) =
      invariantCurrentMeasure lam := by
  have h := congrArg Measure.fst
    (feedbackReturnRoofLaw_map_environmentCurrent_future hlam0 hlam)
  rw [Measure.fst_map_prodMk measurable_feedbackRoofFuture, Measure.fst_compProd] at h
  exact h

/-- Under the actual stationary occupation construction, conditional on its true environment
root current, the complete future has the original marked feedback trajectory law. -/
theorem feedbackRoofFuture_condDistrib {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    condDistrib feedbackRoofFuture (feedbackRoofEnvironmentCurrent lam)
      (feedbackReturnRoofLaw lam hlam0 hlam) =ᵐ[invariantCurrentMeasure lam]
        feedbackCurrentTrajectoryKernel lam hlam0 hlam := by
  rw [← feedbackReturnRoofLaw_map_environmentCurrent hlam0 hlam]
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (measurable_feedbackRoofEnvironmentCurrent lam) measurable_feedbackRoofFuture
  rw [feedbackReturnRoofLaw_map_environmentCurrent hlam0 hlam]
  exact feedbackReturnRoofLaw_map_environmentCurrent_future hlam0 hlam

end OTSelector.Limit
