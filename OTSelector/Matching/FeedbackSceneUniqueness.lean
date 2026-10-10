import OTSelector.Matching.FeedbackSceneInvariantConditioning
import OTSelector.Matching.DisagreementJoining

/-!
# Uniqueness of the actual stationary feedback matching law

The two scene laws are joined over their common actual feedback environment. Geometric
agreement at a common empty cut, invariant conditioning, and the actual conditional window
bounds imply equality almost surely in that joining. Thus the original laws coincide and their
conditional scene laws are the same Dirac mass over almost every environment.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

local instance : Nonempty MatchingScene := ⟨⟨0, 0, 0, ⟨0, 0⟩⟩⟩

/-- Stationary locally minimizing candidate scene laws over the actual feedback environment are
unique. Their conditional matching given that environment is almost surely deterministic. -/
theorem feedbackSceneLaws_unique {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hlam8 : lam < 1 / 8)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPenv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQenv : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hPstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P)
    (hQstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) Q Q)
    (hcandidate : ∀ k : Fin 2, ∀ᵐ scene ∂(![P, Q] k),
      FeedbackSceneEnergyCandidate lam scene)
    (hroot : ∀ k : Fin 2,
      (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂(![P, Q] k)) < ∞) :
    P = Q ∧ ∀ᵐ e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam,
      ∃ scene, (feedbackSceneEnvironmentLaw P).condKernel e = Measure.dirac scene ∧
        (feedbackSceneEnvironmentLaw Q).condKernel e = Measure.dirac scene := by
  obtain ⟨regularity⟩ := exists_feedbackConditionalRegularityParameters hlam0 hlam
  let J := feedbackSceneRoofJoining lam hlam0 hlam P Q
  have hscene (k : Fin 2) : J.map (fun q ↦ feedbackSceneRoofScene q k) = ![P, Q] k := by
    fin_cases k
    · exact feedbackSceneRoofJoining_scene_left lam hlam0 hlam P Q hPenv
    · exact feedbackSceneRoofJoining_scene_right lam hlam0 hlam P Q hPenv hQenv
  have henv : ∀ᵐ q ∂J, ∀ k : Fin 2,
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1 := by
    filter_upwards [feedbackSceneRoofJoining_ae_environment lam hlam0 hlam P Q hPenv hQenv]
      with q hq k
    fin_cases k
    · exact hq.1
    · exact hq.2
  have hcand (k : Fin 2) : ∀ᵐ scene ∂J.map (fun q ↦ feedbackSceneRoofScene q k),
      FeedbackSceneEnergyCandidate lam scene := by
    rw [hscene]
    exact hcandidate k
  have hm : Measurable (fun scene : MatchingScene ↦ MatchingScene.crossingEnergyMoment scene 0) :=
    measurable_feedbackSceneCrossingMoment.comp
      (f := fun scene : MatchingScene ↦ (scene, (0 : ℝ))) (measurable_id.prodMk measurable_const)
  have hmoment (k : Fin 2) :
      (∫⁻ q, MatchingScene.crossingEnergyMoment (feedbackSceneRoofScene q k) 0 ∂J) < ∞ := by
    rw [← lintegral_map hm (measurable_feedbackSceneRoofScene k), hscene]
    exact hroot k
  have hedges := ae_feedbackSceneEdges_eq_of_commonEmptyCut hlam8 regularity J
    (feedbackSceneRoofJoining_roof lam hlam0 hlam P Q) henv
    (fun t ↦ measurePreserving_feedbackSceneRoofFlow hlam0 hlam P Q hPenv hQenv t
      (hPstat t) (hQstat t)) hcand hmoment
    (ae_feedbackSceneRoofJoining_commonEmptyCut_implies_edges_eq hlam0 hlam hlam8 P Q
      hPenv hQenv hPstat hQstat hcandidate)
  exact feedbackSceneLaws_eq_and_condKernel_dirac_of_ae_edges_eq hlam0 hlam P Q hPenv hQenv hedges

/-- A single admissible actual stationary scene law has no remaining conditional matching
randomness after its complete feedback environment has been specified. -/
theorem feedbackSceneLaw_condKernel_dirac {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (hlam8 : lam < 1 / 8)
    (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (henv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P)
    (hcandidate : ∀ᵐ scene ∂P, FeedbackSceneEnergyCandidate lam scene)
    (hroot : (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂P) < ∞) :
    ∀ᵐ e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam,
      ∃ scene, (feedbackSceneEnvironmentLaw P).condKernel e = Measure.dirac scene := by
  have hcand (k : Fin 2) : ∀ᵐ scene ∂(![P, P] k), FeedbackSceneEnergyCandidate lam scene := by
    fin_cases k <;> exact hcandidate
  have hm (k : Fin 2) :
      (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂(![P, P] k)) < ∞ := by
    fin_cases k <;> exact hroot
  filter_upwards [(feedbackSceneLaws_unique hlam0 hlam hlam8 P P henv henv hstat hstat hcand hm).2]
    with e he
  obtain ⟨scene, hs, _⟩ := he
  exact ⟨scene, hs⟩

end OTSelector.Matching
