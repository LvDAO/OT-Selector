import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentTrajectory
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentObservedHistory
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentPoints
import OTSelector.Limit.FeedbackMartingaleProblemStationaryPathReadout

/-!
# Uniqueness of the actual future under the marked spatial martingale problem

The revealed initial current and continuous marked counts suffice: the finite marked histories
are recovered measurably from those observations. Optional sampling then identifies every
actual holding/mark transition and hence the complete chronological path. Local finiteness
identifies that path's atom measures with the original positive point configurations.
-/

open MeasureTheory ProbabilityTheory Set Filter Preorder
open scoped NNReal ENNReal BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit

open PointProcess

section OriginalMartingaleProblem

variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
  (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
  (hroot : Measurable[ℱ 0] (fun ω ↦ (e ω).path.rootCurrent))
  (htest : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0),
    Measurable[ℱ t] (fun ω ↦ LocalConfiguration.firstEventTestCount
      (feedbackEnvironmentTwoColor (e ω)) b ψ t))
  (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
  (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
    Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)

include he hlam0 hlam hroot htest hsimple hM in
/-- Every actual finite event index is attained under the original marked martingale problem. -/
theorem feedbackEnvironment_eventTimes_finite_of_marked_martingale :
    ∀ n, ∀ᵐ ω ∂μ, feedbackEnvironmentEventTime (e ω) n ≠ ∞ := by
  apply (feedbackEnvironment_futurePath_joint_steps μ ℱ e he hlam0 hlam
    (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest) hsimple hM ?_).1
  intro n _
  exact ⟨_, feedbackEnvironmentFuturePrefix_measurable_version e ℱ hroot htest μ n hsimple⟩

include he hlam0 hlam hroot htest hsimple hM in
/-- The full chronological path law is determined by the initial current and the original
two-color marked compensator martingales. All stopped-history and jump-kernel premises have
been proved from actual revealed counts. -/
theorem feedbackEnvironment_futurePath_law_of_marked_martingale :
    μ.map (fun ω ↦ feedbackEnvironmentFuturePath (e ω)) =
      @Kernel.trajMeasure (fun _ ↦ FeedbackMarkedStep) (fun _ ↦ inferInstance)
        ((μ.map (fun ω ↦ (e ω).path.rootCurrent)).map feedbackMarkedVirtual)
        (feedbackMarkedHistoryKernel lam) (feedbackMarkedHistoryKernel_isMarkov hlam0 hlam) := by
  apply feedbackEnvironment_futurePath_law μ ℱ e he hlam0 hlam
    (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest) hsimple hM
  intro n _
  exact ⟨_, feedbackEnvironmentFuturePrefix_measurable_version e ℱ hroot htest μ n hsimple⟩

include he hlam0 hlam hroot htest hsimple hM in
/-- With invariant initial current, the actual chronological future has the same complete path
law as the independently constructed stationary feedback process. -/
theorem feedbackEnvironment_futurePath_law_of_invariant_current
    (hinit : μ.map (fun ω ↦ (e ω).path.rootCurrent) = invariantCurrentMeasure lam) :
    μ.map (fun ω ↦ feedbackEnvironmentFuturePath (e ω)) =
      feedbackStationaryMarkedTrajectory lam hlam0 hlam := by
  rw [feedbackEnvironment_futurePath_law_of_marked_martingale μ ℱ e he hlam0 hlam
    hroot htest hsimple hM, hinit]
  rfl

include he hlam0 hlam hroot htest hsimple hM in
/-- The physical positive counting measures agree almost surely with the atoms of the uniquely
identified chronological path. Escape from bounded windows follows from actual local counts. -/
theorem ae_feedbackPositiveEnvironmentPoints_eq_futurePath :
    (fun ω ↦ feedbackPositiveEnvironmentPoints (e ω)) =ᵐ[μ]
      (fun ω ↦ feedbackFuturePointMeasures (feedbackEnvironmentFuturePath (e ω))) := by
  have hall := feedbackEnvironment_eventTimes_finite_of_marked_martingale
    μ ℱ e he hlam0 hlam hroot htest hsimple hM
  filter_upwards [hsimple, ae_all_iff.mpr hall] with ω hs hf
  exact feedbackPositiveEnvironmentPoints_eq_futurePath (e ω) hs hf
    (tendsto_feedbackEnvironmentEventTime_toReal_atTop (e ω) hs hf)

include he hlam0 hlam hroot htest hsimple hM in
/-- With invariant initial current, the joint law of the actual root current and both entire
positive configurations is the stationary feedback kernel. This is a physical environment
readout, not an auxiliary trajectory label. -/
theorem feedbackEnvironment_current_positivePoints_law
    (hinit : μ.map (fun ω ↦ (e ω).path.rootCurrent) = invariantCurrentMeasure lam) :
    μ.map (fun ω ↦ ((e ω).path.rootCurrent, feedbackPositiveEnvironmentPoints (e ω))) =
      invariantCurrentMeasure lam ⊗ₘ feedbackFuturePointKernel lam hlam0 hlam := by
  have hW : Measurable (fun ω ↦ feedbackEnvironmentFuturePath (e ω)) :=
    measurable_feedbackEnvironmentFuturePath.comp he
  have hObs : Measurable (fun w : FeedbackCellPath ↦
      ((w 0).2.2, feedbackFuturePointMeasures w)) :=
    (measurable_pi_apply 0).snd.snd.prodMk measurable_feedbackFuturePointMeasures
  calc
    _ = μ.map (fun ω ↦ ((feedbackEnvironmentFuturePath (e ω) 0).2.2,
        feedbackFuturePointMeasures (feedbackEnvironmentFuturePath (e ω)))) := by
      apply Measure.map_congr
      filter_upwards [ae_feedbackPositiveEnvironmentPoints_eq_futurePath μ ℱ e he
        hlam0 hlam hroot htest hsimple hM] with ω hω
      exact Prod.ext rfl hω
    _ = (μ.map (fun ω ↦ feedbackEnvironmentFuturePath (e ω))).map
        (fun w ↦ ((w 0).2.2, feedbackFuturePointMeasures w)) :=
      (Measure.map_map hObs hW).symm
    _ = _ := by
      rw [feedbackEnvironment_futurePath_law_of_invariant_current μ ℱ e he hlam0 hlam
        hroot htest hsimple hM hinit,
        feedbackStationaryMarkedTrajectory_map_current_positivePoints hlam0 hlam]

include he hlam0 hlam hroot htest hsimple hM in
/-- The original martingale problem identifies the complete positive physical readout with
that of the constructed stationary environment. -/
theorem feedbackEnvironment_current_positivePoints_law_eq_stationary
    (hinit : μ.map (fun ω ↦ (e ω).path.rootCurrent) = invariantCurrentMeasure lam) :
    μ.map (fun ω ↦ ((e ω).path.rootCurrent, feedbackPositiveEnvironmentPoints (e ω))) =
      (feedbackStationaryEnvironmentLaw lam hlam0 hlam).map
        (fun e ↦ (e.path.rootCurrent, feedbackPositiveEnvironmentPoints e)) := by
  rw [feedbackEnvironment_current_positivePoints_law μ ℱ e he hlam0 hlam
    hroot htest hsimple hM hinit,
    feedbackStationaryEnvironmentLaw_map_current_positivePoints hlam0 hlam]

end OriginalMartingaleProblem
end OTSelector.Limit
