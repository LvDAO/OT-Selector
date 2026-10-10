import OTSelector.Matching.FeedbackSceneJoining
import OTSelector.Limit.FeedbackRoofFlow
import OTSelector.Probability.IndependentJoiningStationarity
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Spatial stationarity of the actual roof/scene joining

The concrete roof translation and actual scene rerooting preserve the same relative joining.
This follows from the proved roof flow and disintegration uniqueness for invariant joint laws.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

local instance : Nonempty MatchingScene := ⟨⟨0, 0, 0, ⟨0, 0⟩⟩⟩

local instance : MeasurableVAdd₂ ℝ FeedbackEnvironment where
  measurable_vadd := FeedbackEnvironment.measurable_uncurry_reroot

/-- The environment translation used by the actual relative joining. -/
noncomputable def feedbackEnvironmentRerootEquiv (t : ℝ) :
    FeedbackEnvironment ≃ᵐ FeedbackEnvironment := MeasurableEquiv.vadd t

/-- Forgetting edges commutes with the actual spatial rerooting. -/
theorem feedbackSceneEnvironment_reroot (t : ℝ) (scene : MatchingScene) :
    feedbackSceneEnvironment (MatchingScene.reroot t scene) =
      FeedbackEnvironment.reroot t (feedbackSceneEnvironment scene) := rfl

/-- A stationary scene retains stationarity when recorded with its environment. -/
theorem feedbackSceneEnvironmentLaw_map_reroot (P : Measure MatchingScene) (t : ℝ)
    (hP : MeasurePreserving (MatchingScene.reroot t) P P) :
    (feedbackSceneEnvironmentLaw P).map
      (Prod.map (FeedbackEnvironment.reroot t) (MatchingScene.reroot t)) =
        feedbackSceneEnvironmentLaw P := by
  have hg : Measurable (fun s : MatchingScene ↦ (feedbackSceneEnvironment s, s)) :=
    measurable_feedbackSceneEnvironment.prodMk measurable_id
  rw [feedbackSceneEnvironmentLaw, Measure.map_map
    ((show Measurable (FeedbackEnvironment.reroot t) from
      measurable_const_vadd t).prodMap hP.measurable) hg]
  change P.map ((fun s ↦ (feedbackSceneEnvironment s, s)) ∘ MatchingScene.reroot t) = _
  rw [← Measure.map_map hg hP.measurable, hP.map_eq]

/-- The actual roof/environment graph law is invariant under the concrete joint translation. -/
theorem feedbackRoofEnvironmentLaw_map_flow {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (t : ℝ) :
    (feedbackRoofEnvironmentLaw lam hlam0 hlam).map
      (Prod.map (FeedbackEnvironment.reroot t) (feedbackRoofFlow t)) =
        feedbackRoofEnvironmentLaw lam hlam0 hlam := by
  let R := feedbackStationaryRoofLaw lam hlam0 hlam
  have hf := measurePreserving_feedbackRoofFlow hlam0 hlam t
  have hg : Measurable (fun p ↦ (feedbackRoofEnvironment lam p, p)) :=
    (measurable_feedbackRoofEnvironment lam).prodMk measurable_id
  rw [feedbackRoofEnvironmentLaw,
    Measure.map_map ((show Measurable (FeedbackEnvironment.reroot t) from
      measurable_const_vadd t).prodMap hf.measurable) hg]
  calc
    _ = R.map ((fun p ↦ (feedbackRoofEnvironment lam p, p)) ∘ feedbackRoofFlow t) := by
      apply Measure.map_congr
      filter_upwards [feedbackRoofFlow_environment_ae hlam0 hlam] with p hp
      exact Prod.ext (hp t).symm rfl
    _ = _ := by rw [← Measure.map_map hg hf.measurable, hf.map_eq]

/-- The actual pair joining is invariant under simultaneous rerooting of both scenes. -/
theorem feedbackScenePairLaw_map_reroot (P Q : Measure MatchingScene)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (henv : P.map feedbackSceneEnvironment = Q.map feedbackSceneEnvironment) (t : ℝ)
    (hP : MeasurePreserving (MatchingScene.reroot t) P P)
    (hQ : MeasurePreserving (MatchingScene.reroot t) Q Q) :
    (feedbackScenePairLaw P Q).map (Prod.map (FeedbackEnvironment.reroot t)
      (Prod.map (MatchingScene.reroot t) (MatchingScene.reroot t))) = feedbackScenePairLaw P Q :=
  relativeIndependentJoining_map_eq_of_map_prod_eq (feedbackSceneEnvironmentLaw P)
    (feedbackSceneEnvironmentLaw Q) (by simpa using henv)
    (feedbackEnvironmentRerootEquiv t) hP.measurable hQ.measurable
    (feedbackSceneEnvironmentLaw_map_reroot P t hP)
    (feedbackSceneEnvironmentLaw_map_reroot Q t hQ)

/-- Translate the actual environment, its attached roof, and the two sampled scenes together. -/
noncomputable def feedbackSceneRoofFlow (t : ℝ) : FeedbackSceneRoofPoint → FeedbackSceneRoofPoint :=
  Prod.map (FeedbackEnvironment.reroot t)
    (Prod.map (feedbackRoofFlow t) (Prod.map (MatchingScene.reroot t) (MatchingScene.reroot t)))

@[fun_prop]
theorem measurable_feedbackSceneRoofFlow (t : ℝ) : Measurable (feedbackSceneRoofFlow t) :=
  (feedbackEnvironmentRerootEquiv t).measurable.prodMap
    ((measurable_feedbackRoofFlow.comp (measurable_const.prodMk measurable_id)).prodMap
      ((MatchingScene.rerootMeasurableEquiv t).measurable.prodMap
        (MatchingScene.rerootMeasurableEquiv t).measurable))

/-- The genuine attached-roof joining is stationary whenever its two original scenes are. -/
theorem measurePreserving_feedbackSceneRoofFlow {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (P Q : Measure MatchingScene)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPenv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQenv : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (t : ℝ) (hP : MeasurePreserving (MatchingScene.reroot t) P P)
    (hQ : MeasurePreserving (MatchingScene.reroot t) Q Q) :
    MeasurePreserving (feedbackSceneRoofFlow t) (feedbackSceneRoofJoining lam hlam0 hlam P Q)
      (feedbackSceneRoofJoining lam hlam0 hlam P Q) := by
  let : Nonempty (FeedbackCellSequence × ℝ) :=
    nonempty_of_isProbabilityMeasure (feedbackStationaryRoofLaw lam hlam0 hlam)
  refine ⟨measurable_feedbackSceneRoofFlow t, ?_⟩
  apply relativeIndependentJoining_map_eq_of_map_prod_eq
    (feedbackRoofEnvironmentLaw lam hlam0 hlam) (feedbackScenePairLaw P Q)
    (by simpa using hPenv.symm) (feedbackEnvironmentRerootEquiv t)
    (measurePreserving_feedbackRoofFlow hlam0 hlam t).measurable
    (hP.measurable.prodMap hQ.measurable)
    (feedbackRoofEnvironmentLaw_map_flow hlam0 hlam t)
  exact feedbackScenePairLaw_map_reroot P Q (hPenv.trans hQenv.symm) t hP hQ

end OTSelector.Matching
