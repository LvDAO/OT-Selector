import OTSelector.Limit.FeedbackMartingaleProblemCurrentStationarity
import OTSelector.Limit.FeedbackMartingaleProblemCurrentMass
import OTSelector.Limit.FeedbackMartingaleProblemTwoSidedPoints

/-!
# Stationary identification of the actual current and both full point configurations

The marked martingale problem and actual real reroot stationarity determine the invariant
current marginal. They consequently identify the entire two-sided marked point law with
the independently constructed stationary feedback environment. The graph coordinate is
left for the separate feedback integral identity.
-/

open MeasureTheory ProbabilityTheory Set Filter
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
  (hstationary : ∀ a : ℝ, (μ.map e).map (FeedbackEnvironment.reroot a) = μ.map e)

include he hlam0 hlam hroot htest hsimple hM hstationary in
/-- The original marked martingale problem plus physical stationarity determines the root
current distribution. No invariant-marginal assumption is used. -/
theorem feedbackEnvironment_current_law_of_stationary_marked_martingale :
    μ.map (fun ω ↦ (e ω).path.rootCurrent) = invariantCurrentMeasure lam := by
  let ρ := μ.map (fun ω ↦ (e ω).path.rootCurrent)
  have hρ : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map
    (FeedbackEnvironment.measurable_rootCurrent.comp he).aemeasurable
  exact eq_invariantCurrentMeasure_of_integral_generator_zero hlam0 hlam ρ
    (integral_feedbackCurrentIndicatorGenerator_eq_zero μ ℱ e he hlam0 hlam
      hroot htest hsimple hM hstationary)

include he hlam0 hlam hroot htest hsimple hM hstationary in
/-- The complete two-sided physical point data, jointly with the current, have the actual
stationary feedback law. The separate real-reroot stationarity premise is visible here. -/
theorem feedbackEnvironment_twoSidedPoints_law_of_stationary_marked_martingale :
    μ.map (fun ω ↦ feedbackTwoSidedPointData (e ω)) =
      (feedbackStationaryEnvironmentLaw lam hlam0 hlam).map feedbackTwoSidedPointData := by
  have hinit := feedbackEnvironment_current_law_of_stationary_marked_martingale
    μ ℱ e he hlam0 hlam hroot htest hsimple hM hstationary
  have hpositive := feedbackEnvironment_current_positivePoints_law_eq_stationary
    μ ℱ e he hlam0 hlam hroot htest hsimple hM hinit
  have hm : Measurable (fun e : FeedbackEnvironment ↦
      (e.path.rootCurrent, feedbackPositiveEnvironmentPoints e)) :=
    FeedbackEnvironment.measurable_rootCurrent.prodMk measurable_feedbackPositiveEnvironmentPoints
  have hh := map_feedbackTwoSidedPointData_eq_of_stationary_positive
    (μ.map e) (feedbackStationaryEnvironmentLaw lam hlam0 hlam) hstationary
    (fun a ↦ (measurePreserving_feedbackStationaryEnvironmentLaw hlam0 hlam a).map_eq) (by
      rwa [Measure.map_map hm he])
  rwa [Measure.map_map measurable_feedbackTwoSidedPointData he] at hh

end OriginalMartingaleProblem
end OTSelector.Limit
