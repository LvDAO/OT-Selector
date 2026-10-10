import OTSelector.Limit.FeedbackMartingaleProblemStationaryPoints
import OTSelector.Limit.FeedbackMartingaleProblemGraph

/-!
# Uniqueness of the full stationary feedback environment

The original marked-count martingale problem determines the current marginal and both complete
point configurations. The actual feedback graph integral then determines the remaining graph
coordinate. The reference law is the independently constructed stationary occupation law.
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
/-- The original marked MP, real reroot stationarity and the feedback graph equation identify
the entire bare environment law. The graph equation only needs to hold at rational cuts. -/
theorem feedbackEnvironment_law_of_stationary_marked_martingale_rational
    (hgraph : ∀ᵐ ω ∂μ, ∀ q : ℚ, (e ω).path.graphHeight (q : ℝ) =
      ∫ s in 0..(q : ℝ), lam * currentSign (feedbackEnvironmentCurrent (e ω) s)) :
    μ.map e = feedbackStationaryEnvironmentLaw lam hlam0 hlam := by
  apply eq_of_feedbackTwoSidedPointData_law_of_rational_integral lam
    (μ.map e) (feedbackStationaryEnvironmentLaw lam hlam0 hlam)
  · have hmeas : MeasurableSet {v : FeedbackEnvironment | ∀ q : ℚ,
        v.path.graphHeight (q : ℝ) = ∫ s in 0..(q : ℝ),
          lam * currentSign (feedbackEnvironmentCurrent v s)} := by
      simp only [ofPred_forall]
      apply MeasurableSet.iInter
      intro q
      exact measurableSet_eq_fun
        ((GraphHeight.continuous_apply (q : ℝ)).measurable.comp FeedbackEnvironment.measurable_graphHeight)
        (measurable_feedbackEnvironmentIntegral lam (q : ℝ))
    exact (ae_map_iff he.aemeasurable hmeas).mpr hgraph
  · filter_upwards [ae_feedbackStationaryEnvironment_integral hlam0 hlam] with v hv q
    exact hv q
  · rw [Measure.map_map measurable_feedbackTwoSidedPointData he]
    exact feedbackEnvironment_twoSidedPoints_law_of_stationary_marked_martingale
      μ ℱ e he hlam0 hlam hroot htest hsimple hM hstationary

include he hlam0 hlam hroot htest hsimple hM hstationary in
/-- Full-cut version of stationary feedback-environment uniqueness. -/
theorem feedbackEnvironment_law_of_stationary_marked_martingale
    (hgraph : ∀ᵐ ω ∂μ, ∀ t : ℝ, (e ω).path.graphHeight t =
      ∫ s in 0..t, lam * currentSign (feedbackEnvironmentCurrent (e ω) s)) :
    μ.map e = feedbackStationaryEnvironmentLaw lam hlam0 hlam :=
  feedbackEnvironment_law_of_stationary_marked_martingale_rational μ ℱ e he hlam0 hlam
    hroot htest hsimple hM hstationary (hgraph.mono fun _ h q ↦ h q)

end OriginalMartingaleProblem
end OTSelector.Limit
