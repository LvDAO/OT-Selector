import OTSelector.Matching.FeedbackSceneMatching
import OTSelector.Probability.IndependentJoining

/-!
# Attaching the actual stationary roof to scene laws

The roof is adjoined by relative independent joining over the shared feedback environment.
Both scene laws retain their original marginals, while the roof marginal is exactly the actual
stationary occupation law. No pre-existing regenerative coordinates on a scene are assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

local instance : Nonempty MatchingScene := ⟨⟨0, 0, 0, ⟨0, 0⟩⟩⟩

/-- Forgetting the actual matching edges keeps exactly the feedback environment. -/
def feedbackSceneEnvironment (scene : MatchingScene) : FeedbackEnvironment :=
  ⟨scene.source, scene.target, scene.path⟩

@[fun_prop]
theorem measurable_feedbackSceneEnvironment : Measurable feedbackSceneEnvironment :=
  FeedbackEnvironment.measurable_mk MatchingScene.measurable_source MatchingScene.measurable_target
    (FeedbackPath.continuous_graphHeight.measurable.comp MatchingScene.measurable_path)
    (FeedbackPath.continuous_rootCurrent.measurable.comp MatchingScene.measurable_path)

/-- The actual scene law recorded together with its own environment. -/
noncomputable def feedbackSceneEnvironmentLaw (P : Measure MatchingScene) :
    Measure (FeedbackEnvironment × MatchingScene) :=
  P.map (fun scene ↦ (feedbackSceneEnvironment scene, scene))

instance (P : Measure MatchingScene) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (feedbackSceneEnvironmentLaw P) :=
  Measure.isProbabilityMeasure_map (measurable_feedbackSceneEnvironment.prodMk measurable_id).aemeasurable

/-- The actual stationary roof recorded together with its observed environment. -/
noncomputable def feedbackRoofEnvironmentLaw (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    Measure (FeedbackEnvironment × (FeedbackCellSequence × ℝ)) :=
  (feedbackStationaryRoofLaw lam hlam0 hlam).map
    (fun p ↦ (feedbackRoofEnvironment lam p, p))

instance (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    IsProbabilityMeasure (feedbackRoofEnvironmentLaw lam hlam0 hlam) :=
  Measure.isProbabilityMeasure_map ((measurable_feedbackRoofEnvironment lam).prodMk measurable_id).aemeasurable

/-- Two scene laws are joined over their actual common environment. -/
noncomputable def feedbackScenePairLaw (P Q : Measure MatchingScene)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    Measure (FeedbackEnvironment × (MatchingScene × MatchingScene)) :=
  relativeIndependentJoining (feedbackSceneEnvironmentLaw P) (feedbackSceneEnvironmentLaw Q)

instance (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (feedbackScenePairLaw P Q) := by unfold feedbackScenePairLaw; infer_instance

/-- The complete joining retains the true roof and both original scene marginals. -/
noncomputable def feedbackSceneRoofJoining (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    Measure (FeedbackEnvironment × ((FeedbackCellSequence × ℝ) × (MatchingScene × MatchingScene))) := by
  let : Nonempty (FeedbackCellSequence × ℝ) :=
    nonempty_of_isProbabilityMeasure (feedbackStationaryRoofLaw lam hlam0 hlam)
  exact relativeIndependentJoining (feedbackRoofEnvironmentLaw lam hlam0 hlam) (feedbackScenePairLaw P Q)

instance (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (feedbackSceneRoofJoining lam hlam0 hlam P Q) := by
  unfold feedbackSceneRoofJoining
  infer_instance

@[simp]
theorem feedbackSceneEnvironmentLaw_fst (P : Measure MatchingScene) :
    (feedbackSceneEnvironmentLaw P).fst = P.map feedbackSceneEnvironment := by
  have hm : Measurable (fun scene : MatchingScene ↦ (feedbackSceneEnvironment scene, scene)) := by fun_prop
  rw [Measure.fst, feedbackSceneEnvironmentLaw, Measure.map_map measurable_fst hm]
  rfl

@[simp]
theorem feedbackSceneEnvironmentLaw_snd (P : Measure MatchingScene) :
    (feedbackSceneEnvironmentLaw P).snd = P := by
  have hm : Measurable (fun scene : MatchingScene ↦ (feedbackSceneEnvironment scene, scene)) := by fun_prop
  rw [Measure.snd, feedbackSceneEnvironmentLaw, Measure.map_map measurable_snd hm]
  exact Measure.map_id

@[simp]
theorem feedbackRoofEnvironmentLaw_fst (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    (feedbackRoofEnvironmentLaw lam hlam0 hlam).fst =
      feedbackStationaryEnvironmentLaw lam hlam0 hlam := by
  have hm : Measurable (fun p ↦ (feedbackRoofEnvironment lam p, p)) := by
    exact (measurable_feedbackRoofEnvironment lam).prodMk measurable_id
  rw [Measure.fst, feedbackRoofEnvironmentLaw, Measure.map_map measurable_fst hm]
  exact feedbackStationaryRoofLaw_environment_map lam hlam0 hlam

@[simp]
theorem feedbackRoofEnvironmentLaw_snd (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    (feedbackRoofEnvironmentLaw lam hlam0 hlam).snd = feedbackStationaryRoofLaw lam hlam0 hlam := by
  have hm : Measurable (fun p ↦ (feedbackRoofEnvironment lam p, p)) := by
    exact (measurable_feedbackRoofEnvironment lam).prodMk measurable_id
  rw [Measure.snd, feedbackRoofEnvironmentLaw, Measure.map_map measurable_snd hm]
  exact Measure.map_id

/-- The first scene pair marginal of the concrete relative joining. -/
theorem feedbackScenePairLaw_left (P Q : Measure MatchingScene)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (feedbackScenePairLaw P Q).map (fun q ↦ (q.1, q.2.1)) = feedbackSceneEnvironmentLaw P :=
  relativeIndependentJoining_map_left _ _

/-- The second scene pair marginal uses exactly equality of the actual environment laws. -/
theorem feedbackScenePairLaw_right (P Q : Measure MatchingScene)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (henv : P.map feedbackSceneEnvironment = Q.map feedbackSceneEnvironment) :
    (feedbackScenePairLaw P Q).map (fun q ↦ (q.1, q.2.2)) = feedbackSceneEnvironmentLaw Q :=
  relativeIndependentJoining_map_right _ _ (by simpa using henv)

@[simp]
theorem feedbackScenePairLaw_fst (P Q : Measure MatchingScene)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (feedbackScenePairLaw P Q).fst = P.map feedbackSceneEnvironment := by
  have he := congrArg Measure.fst (feedbackScenePairLaw_left P Q)
  simp only [Measure.fst] at he
  rw [Measure.map_map measurable_fst (measurable_fst.prodMk measurable_snd.fst)] at he
  exact he.trans (feedbackSceneEnvironmentLaw_fst P)

/-- The roof/environment marginal of the complete joining is the original actual graph law. -/
theorem feedbackSceneRoofJoining_left (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (feedbackSceneRoofJoining lam hlam0 hlam P Q).map (fun q ↦ (q.1, q.2.1)) =
      feedbackRoofEnvironmentLaw lam hlam0 hlam := by
  let : Nonempty (FeedbackCellSequence × ℝ) :=
    nonempty_of_isProbabilityMeasure (feedbackStationaryRoofLaw lam hlam0 hlam)
  exact relativeIndependentJoining_map_left (feedbackRoofEnvironmentLaw lam hlam0 hlam)
    (feedbackScenePairLaw P Q)

/-- Attaching roof coordinates does not change the joined scene pair law. -/
theorem feedbackSceneRoofJoining_right (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam) :
    (feedbackSceneRoofJoining lam hlam0 hlam P Q).map (fun q ↦ (q.1, q.2.2)) =
      feedbackScenePairLaw P Q := by
  let : Nonempty (FeedbackCellSequence × ℝ) :=
    nonempty_of_isProbabilityMeasure (feedbackStationaryRoofLaw lam hlam0 hlam)
  exact relativeIndependentJoining_map_right (feedbackRoofEnvironmentLaw lam hlam0 hlam)
    (feedbackScenePairLaw P Q) (by simpa using hP.symm)

/-- The lifted roof is exactly the actual stationary occupation law. -/
theorem feedbackSceneRoofJoining_roof (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    (feedbackSceneRoofJoining lam hlam0 hlam P Q).map (fun q ↦ q.2.1) =
      feedbackStationaryRoofLaw lam hlam0 hlam := by
  rw [← feedbackRoofEnvironmentLaw_snd lam hlam0 hlam, Measure.snd,
    ← feedbackSceneRoofJoining_left lam hlam0 hlam P Q,
    Measure.map_map measurable_snd (measurable_fst.prodMk measurable_snd.fst)]
  rfl

/-- The first scene keeps its exact original marginal. -/
theorem feedbackSceneRoofJoining_scene_left (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam) :
    (feedbackSceneRoofJoining lam hlam0 hlam P Q).map (fun q ↦ q.2.2.1) = P := by
  have he := congrArg (fun m : Measure (FeedbackEnvironment × (MatchingScene × MatchingScene)) ↦
    m.map (fun q ↦ q.2.1)) (feedbackSceneRoofJoining_right lam hlam0 hlam P Q hP)
  rw [Measure.map_map measurable_snd.fst (measurable_fst.prodMk measurable_snd.snd)] at he
  have hm := congrArg Measure.snd (feedbackScenePairLaw_left P Q)
  simp only [Measure.snd] at hm
  rw [Measure.map_map measurable_snd (measurable_fst.prodMk measurable_snd.fst)] at hm
  exact he.trans (hm.trans (feedbackSceneEnvironmentLaw_snd P))

/-- The second scene also keeps its original marginal when the two environment laws agree. -/
theorem feedbackSceneRoofJoining_scene_right (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQ : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam) :
    (feedbackSceneRoofJoining lam hlam0 hlam P Q).map (fun q ↦ q.2.2.2) = Q := by
  have he := congrArg (fun m : Measure (FeedbackEnvironment × (MatchingScene × MatchingScene)) ↦
    m.map (fun q ↦ q.2.2)) (feedbackSceneRoofJoining_right lam hlam0 hlam P Q hP)
  rw [Measure.map_map measurable_snd.snd (measurable_fst.prodMk measurable_snd.snd)] at he
  have hm := congrArg Measure.snd (feedbackScenePairLaw_right P Q (hP.trans hQ.symm))
  simp only [Measure.snd] at hm
  rw [Measure.map_map measurable_snd (measurable_fst.prodMk measurable_snd.snd)] at hm
  exact he.trans (hm.trans (feedbackSceneEnvironmentLaw_snd Q))

/-- Recording a scene with its own environment is supported on that actual graph. -/
theorem feedbackSceneEnvironmentLaw_ae (P : Measure MatchingScene) :
    ∀ᵐ q ∂feedbackSceneEnvironmentLaw P, q.1 = feedbackSceneEnvironment q.2 := by
  unfold feedbackSceneEnvironmentLaw
  apply (ae_map_iff (measurable_feedbackSceneEnvironment.prodMk measurable_id).aemeasurable
    (measurableSet_eq_fun measurable_fst
      (measurable_feedbackSceneEnvironment.comp measurable_snd))).mpr
  exact ae_of_all _ fun _ ↦ rfl

/-- The actual roof/environment graph is also an almost-sure identity. -/
theorem feedbackRoofEnvironmentLaw_ae (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    ∀ᵐ q ∂feedbackRoofEnvironmentLaw lam hlam0 hlam, q.1 = feedbackRoofEnvironment lam q.2 := by
  unfold feedbackRoofEnvironmentLaw
  apply (ae_map_iff ((measurable_feedbackRoofEnvironment lam).prodMk measurable_id).aemeasurable
    (measurableSet_eq_fun measurable_fst
      ((measurable_feedbackRoofEnvironment lam).comp measurable_snd))).mpr
  exact ae_of_all _ fun _ ↦ rfl

/-- Both scenes in the relative joining share the same actual environment. -/
theorem feedbackScenePairLaw_ae_environment (P Q : Measure MatchingScene)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (henv : P.map feedbackSceneEnvironment = Q.map feedbackSceneEnvironment) :
    ∀ᵐ q ∂feedbackScenePairLaw P Q,
      q.1 = feedbackSceneEnvironment q.2.1 ∧ q.1 = feedbackSceneEnvironment q.2.2 := by
  have hl := feedbackSceneEnvironmentLaw_ae P
  have hr := feedbackSceneEnvironmentLaw_ae Q
  rw [← feedbackScenePairLaw_left P Q] at hl
  rw [← feedbackScenePairLaw_right P Q henv] at hr
  exact (ae_of_ae_map (measurable_fst.prodMk measurable_snd.fst).aemeasurable hl).and
    (ae_of_ae_map (measurable_fst.prodMk measurable_snd.snd).aemeasurable hr)

/-- The attached roof really reconstructs each sampled scene's complete environment. -/
theorem feedbackSceneRoofJoining_ae_environment (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQ : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam) :
    ∀ᵐ q ∂feedbackSceneRoofJoining lam hlam0 hlam P Q,
      feedbackSceneEnvironment q.2.2.1 = feedbackRoofEnvironment lam q.2.1 ∧
      feedbackSceneEnvironment q.2.2.2 = feedbackRoofEnvironment lam q.2.1 := by
  have hl := feedbackRoofEnvironmentLaw_ae lam hlam0 hlam
  have hr := feedbackScenePairLaw_ae_environment P Q (hP.trans hQ.symm)
  rw [← feedbackSceneRoofJoining_left lam hlam0 hlam P Q] at hl
  rw [← feedbackSceneRoofJoining_right lam hlam0 hlam P Q hP] at hr
  filter_upwards [ae_of_ae_map (measurable_fst.prodMk measurable_snd.fst).aemeasurable hl,
    ae_of_ae_map (measurable_fst.prodMk measurable_snd.snd).aemeasurable hr] with q hroof hscene
  exact ⟨hscene.1.symm.trans hroof, hscene.2.symm.trans hroof⟩

/-- Carrier of the actual two-scene/roof joining. -/
abbrev FeedbackSceneRoofPoint :=
  FeedbackEnvironment × ((FeedbackCellSequence × ℝ) × (MatchingScene × MatchingScene))

/-- Select one of the two genuine scene coordinates. -/
def feedbackSceneRoofScene (q : FeedbackSceneRoofPoint) (k : Fin 2) : MatchingScene :=
  ![q.2.2.1, q.2.2.2] k

@[fun_prop]
theorem measurable_feedbackSceneRoofScene (k : Fin 2) : Measurable (fun q ↦ feedbackSceneRoofScene q k) := by
  fin_cases k
  · exact measurable_snd.snd.fst
  · exact measurable_snd.snd.snd

/-- A measurable full-measure support carries genuine perfect assignments for both scenes.
The measurable core is obtained from mathlib; no Borel claim about perfectness is needed here. -/
theorem exists_feedbackSceneRoofJoining_support (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQ : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfectP : ∀ᵐ scene ∂P, scene.IsSimplePerfectMatching)
    (hperfectQ : ∀ᵐ scene ∂Q, scene.IsSimplePerfectMatching) :
    ∃ S : Set FeedbackSceneRoofPoint, MeasurableSet S ∧
      (∀ᵐ q ∂feedbackSceneRoofJoining lam hlam0 hlam P Q, q ∈ S) ∧
      ∀ q ∈ S, ∀ k : Fin 2,
        (feedbackSceneRoofScene q k).IsSimplePerfectMatching ∧
        feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1 := by
  let J := feedbackSceneRoofJoining lam hlam0 hlam P Q
  let good : Set FeedbackSceneRoofPoint := {q | ∀ k : Fin 2,
    (feedbackSceneRoofScene q k).IsSimplePerfectMatching ∧
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1}
  have hgood : ∀ᵐ q ∂J, q ∈ good := by
    have hleft := hperfectP
    have hright := hperfectQ
    rw [← feedbackSceneRoofJoining_scene_left lam hlam0 hlam P Q hP] at hleft
    rw [← feedbackSceneRoofJoining_scene_right lam hlam0 hlam P Q hP hQ] at hright
    filter_upwards [feedbackSceneRoofJoining_ae_environment lam hlam0 hlam P Q hP hQ,
      ae_of_ae_map measurable_snd.snd.fst.aemeasurable hleft,
      ae_of_ae_map measurable_snd.snd.snd.aemeasurable hright] with q he hp hq
    intro k
    fin_cases k
    · exact ⟨hp, he.1⟩
    · exact ⟨hq, he.2⟩
  have heq : (univ : Set FeedbackSceneRoofPoint) =ᵐ[J] good := by
    filter_upwards [hgood] with q hq
    exact propext ⟨fun _ ↦ hq, fun _ ↦ mem_univ q⟩
  have hnull : NullMeasurableSet (univ : Set FeedbackSceneRoofPoint) J :=
    MeasurableSet.nullMeasurableSet (μ := J)
      (MeasurableSet.univ : MeasurableSet (univ : Set FeedbackSceneRoofPoint))
  obtain ⟨S, hSgood, hS, hSeq⟩ := (hnull.congr heq).exists_measurable_subset_ae_eq
  refine ⟨S, hS, ?_, fun q hq ↦ hSgood hq⟩
  filter_upwards [hgood, hSeq] with q hq he
  exact he.mpr hq

/-- Restricting to any such full-measure measurable support preserves the entire actual law. -/
theorem feedbackSceneRoofJoining_support_map (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {S : Set FeedbackSceneRoofPoint} (hS : MeasurableSet S)
    (hfull : ∀ᵐ q ∂feedbackSceneRoofJoining lam hlam0 hlam P Q, q ∈ S) :
    ((feedbackSceneRoofJoining lam hlam0 hlam P Q).comap (Subtype.val : S → _)).map Subtype.val =
      feedbackSceneRoofJoining lam hlam0 hlam P Q := by
  rw [map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hfull]

end OTSelector.Matching
