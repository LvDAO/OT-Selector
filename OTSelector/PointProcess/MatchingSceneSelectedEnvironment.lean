import OTSelector.PointProcess.MatchingSceneGoodSubsequence
import OTSelector.PointProcess.MatchingSceneResidualLimit
import OTSelector.PointProcess.MatchingSceneMartingaleClosure
import OTSelector.PointProcess.MatchingScenePastCountApproximation
import OTSelector.Feedback.FeedbackEnvironmentResidualClosure
import OTSelector.Limit.FeedbackMartingaleProblemStationaryEnvironment

/-!
# Identifying the environment of an actual selected weak subsequence

All tightness, vacancy, stationarity, simplicity and graph-equation inputs come from the actual
selected optimizer scenes. Their retained count budgets give integrable local counts in the
limit. Residual identities then yield the true marked martingale problem and identify the
whole environment with the independently constructed stationary feedback law.
-/

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Classical BigOperators ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported

set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096

namespace OTSelector.FeedbackGoodSceneSubsequence

open FiniteSample PointProcess PointProcess.MatchingScene

variable {lam amplitude globalQ endpointQ C δ u v : ℝ}
    {hlam0 : 0 < lam} {hlam : lam < 1 / 8} {huv : u < v}
    {bad : ∀ n, Set (FiniteSample (n + 1))}
    {residual : ∀ _m n : ℕ, FiniteSample (n + 1) → ℝ}
    (data : FeedbackGoodSceneSubsequence hlam0 hlam amplitude globalQ endpointQ C δ u v huv bad residual)

/-- Retained genuine count-square budgets imply integrability of every marked compensator
under the actual selected weak limit, before any martingale or environment identification. -/
theorem integrable_compensator (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0) :
    Integrable (fun scene ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
      (Matching.feedbackSceneEnvironment scene)) (data.limit : Measure MatchingScene) := by
  obtain ⟨R, htR⟩ := exists_nat_ge (t : ℝ)
  obtain ⟨K, _, hbound⟩ := data.count_bound R
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  let μ (k : ℕ) := feedbackSelectionSceneLaw hlam0.le (hlam.trans (by norm_num))
    amplitude u v huv (data.sample (k + N))
  have hlim : Tendsto μ atTop (𝓝 data.limit) :=
    data.law_tendsto.comp (tendsto_add_atTop_nat N)
  have htight : IsTightMeasureSet (range fun k ↦ (μ k : Measure MatchingScene)) :=
    data.tight.subset (by rintro _ ⟨k, rfl⟩; exact mem_range.mpr ⟨k + N, rfl⟩)
  have hc (k : ℕ) : (∫⁻ scene, closedAggregateMass (R : ℝ) scene ^ 2
      ∂(μ k : Measure MatchingScene)) ≤ ENNReal.ofReal K := by
    exact hN (k + N) (Nat.le_add_left N k)
  let fs : Fin 0 → C_c(MatchingPoint, ℝ) := Fin.elim0
  let H : EnvironmentPastCoordinates 0 0 →ᵇ ℝ := BoundedContinuousFunction.const _ 1
  have hi := (integrable_pastMarkedResidual_limit_of_closed_count_sq_bound μ hlim htight
    hlam0.le (hlam.trans (by norm_num)) fs fs H b ψ t htR
    ((data.vacantCut 0).and (data.vacantCut t)) ENNReal.ofReal_ne_top hc).2
  have he : pastMarkedResidual lam fs fs H b ψ t =
      (fun scene ↦ Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
        (Matching.feedbackSceneEnvironment scene)) := by
    funext scene
    simp [pastMarkedResidual, environmentPastCylinder, H]
  rw [he] at hi
  exact hi

/-- The local-count `L¹` input to the natural-filtration closure is proved from the selected
count budgets, not assumed as a property of the limiting phase. -/
theorem integrable_colorCount (b : Bool) (t : ℝ≥0) :
    Integrable (fun scene ↦ (LocalConfiguration.spatialCount
      (Limit.feedbackEnvironmentTwoColor (Matching.feedbackSceneEnvironment scene) b) 0 t : ℝ))
      (data.limit : Measure MatchingScene) := by
  have hi := data.integrable_compensator b (BoundedContinuousFunction.const UnitMark 1) t
  have hd := Limit.integrable_integral_feedbackEnvironmentMarkRate_current
    (data.limit : Measure MatchingScene) Matching.feedbackSceneEnvironment
    Matching.measurable_feedbackSceneEnvironment lam b (fun _ ↦ 1) t
  apply (hi.add hd).congr
  exact Eventually.of_forall fun scene ↦ by
    simp [Limit.feedbackEnvironmentMarkedCompensator,
      LocalConfiguration.firstEventTestCount_one]

/-- Finite observed-count cylinder identities identify the entire actual selected environment.
The natural marked martingale problem is constructed internally from those identities. -/
theorem environmentLaw_eq_of_count_cylinders
    (hamp : 0 < amplitude) (hglobalQ : 0 < globalQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude) (hu : 0 < u) (hv : v < 1)
    (hres : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (s t : ℝ≥0), s ≤ t →
      ∀ (J : Finset (PastCountAt s)) (F : (J → ℝ) →ᵇ ℝ),
        (∫ scene, (Limit.feedbackEnvironmentMarkedCompensator lam b ψ t
          (Matching.feedbackSceneEnvironment scene) -
          Limit.feedbackEnvironmentMarkedCompensator lam b ψ s
          (Matching.feedbackSceneEnvironment scene)) *
            F (J.restrict (pastCountHistory s scene)) ∂(data.limit : Measure MatchingScene)) = 0) :
    (data.limit : Measure MatchingScene).map Matching.feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num)) := by
  apply Limit.feedbackEnvironment_law_of_stationary_marked_martingale_rational
    (data.limit : Measure MatchingScene) markedCountFiltration Matching.feedbackSceneEnvironment
    Matching.measurable_feedbackSceneEnvironment hlam0 (hlam.trans (by norm_num))
    (rootCurrent_markedCountFiltration 0) markedCount_adapted data.environment_timeSimple
    (markedCompensator_martingale_of_cylinder_residuals
      (data.limit : Measure MatchingScene) data.integrable_colorCount lam hres)
  · intro a
    have he : Measurable (FeedbackEnvironment.reroot a) :=
      FeedbackEnvironment.measurable_uncurry_reroot.comp
        (f := fun e : FeedbackEnvironment ↦ (a, e))
        (measurable_const.prodMk measurable_id)
    rw [Measure.map_map he Matching.measurable_feedbackSceneEnvironment]
    change (data.limit : Measure MatchingScene).map
      (Matching.feedbackSceneEnvironment ∘ MatchingScene.reroot a) = _
    rw [← Measure.map_map Matching.measurable_feedbackSceneEnvironment
      (data.stationary a).measurable, (data.stationary a).map_eq]
  · exact data.graphODE hamp hglobalQ hcoefficient hu hv

/-- Original compactly supported environment-past residual identities identify the selected
limit. Local-count integrability, natural-filtration martingales, stationarity, simplicity and
the rational graph equation are all derived inside this theorem. -/
theorem environmentLaw_eq_of_past_cylinders
    (hamp : 0 < amplitude) (hglobalQ : 0 < globalQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude) (hu : 0 < u) (hv : v < 1)
    (hCc : PastCylinderResidualIdentities (data.limit : Measure MatchingScene) lam) :
    (data.limit : Measure MatchingScene).map Matching.feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num)) :=
  data.environmentLaw_eq_of_count_cylinders hamp hglobalQ hcoefficient hu hv
    (cylinder_residuals_of_pastCylinderResidualIdentities (data.limit : Measure MatchingScene)
      lam data.stationary data.vacantCut data.integrable_colorCount hCc)

/-- The actual countable residual family retained by good-sample selection identifies the
entire limiting environment. This final interface assumes neither a martingale problem nor
an environment law, and has no residual identity hypothesis. -/
theorem environmentLaw_eq
    (selected : FeedbackGoodSceneSubsequence hlam0 hlam amplitude globalQ endpointQ C δ u v huv bad
      (feedbackCountableSpatialResidual hlam0.le (hlam.trans (by norm_num)) amplitude u v))
    (hamp : 0 < amplitude) (hglobalQ : 0 < globalQ)
    (hcoefficient : 8 * (globalQ + 33) < amplitude) (hu : 0 < u) (hv : v < 1) :
    (selected.limit : Measure MatchingScene).map Matching.feedbackSceneEnvironment =
      Limit.feedbackStationaryEnvironmentLaw lam hlam0 (hlam.trans (by norm_num)) :=
  selected.environmentLaw_eq_of_past_cylinders hamp hglobalQ hcoefficient hu hv
    (pastCylinderResidualIdentities_of_countableResiduals (selected.limit : Measure MatchingScene)
      hlam0 (hlam.trans (by norm_num)) selected.integrable_colorCount selected.countableResidual_zero)

end OTSelector.FeedbackGoodSceneSubsequence
