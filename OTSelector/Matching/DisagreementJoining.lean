import OTSelector.Matching.DisagreementFeedbackProbability
import OTSelector.Matching.FeedbackSceneJoiningSupport
import OTSelector.Matching.DisagreementSceneGeometry
import OTSelector.Matching.FeedbackNoFiniteTiesBorel

/-!
# One-sided orbit exclusion on the actual stationary joining

This instantiates the measurable-label mass transport on the measurable full-measure
support of the actual two-scene/roof law. Its shift and source intensity come from the
proved roof flow and the actual stationary feedback environment.
-/

open Function Set MeasureTheory
open scoped Classical ENNReal

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

/-- The geometric full-measure support produced by the actual relative joining. -/
def FeedbackSceneSupportGood (lam : ℝ) (S : Set FeedbackSceneRoofPoint) : Prop :=
  ∀ q ∈ S, ∀ k : Fin 2,
    (feedbackSceneRoofScene q k).IsSimplePerfectMatching ∧
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1

/-- The genuine disagreement permutation on the actual joining support. -/
noncomputable def feedbackSceneSupportRawPartner {lam : ℝ} {S : Set FeedbackSceneRoofPoint}
    (hgood : FeedbackSceneSupportGood lam S) (q : S) : Equiv.Perm (ℤ × ℕ) :=
  feedbackSceneRawPartner q.val.2.1 q.val.2.2.1 q.val.2.2.2
    (hgood q q.property 0).1 (hgood q q.property 1).1
    (congrArg FeedbackEnvironment.source (hgood q q.property 0).2)
    (congrArg FeedbackEnvironment.target (hgood q q.property 0).2)
    (congrArg FeedbackEnvironment.source (hgood q q.property 1).2)
    (congrArg FeedbackEnvironment.target (hgood q q.property 1).2)

/-- The actual stationary joining has no one-sided infinite disagreement orbit.
All intensity, coordinate covariance, and permutation measurability inputs are proved above. -/
theorem ae_feedbackSceneRoofJoiningSupport_no_oneSidedOrbit
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPenv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQenv : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hPstat : ∀ a, MeasurePreserving (MatchingScene.reroot a) P P)
    (hQstat : ∀ a, MeasurePreserving (MatchingScene.reroot a) Q Q)
    {S : Set FeedbackSceneRoofPoint} (hS : MeasurableSet S)
    (hfull : ∀ᵐ q ∂feedbackSceneRoofJoining lam hlam0 hlam P Q, q ∈ S)
    (hgood : FeedbackSceneSupportGood lam S) :
    ∀ᵐ q ∂(feedbackSceneRoofJoining lam hlam0 hlam P Q).comap (Subtype.val : S → _), ∀ i,
      ¬ LowerAnchoredOrbit (feedbackSceneSupportRawPartner hgood q)
        (fun j ↦ (feedbackRootedEventPoint q.val.2.1 j).1) i ∧
      ¬ LowerAnchoredOrbit (feedbackSceneSupportRawPartner hgood q)
        (fun j ↦ -(feedbackRootedEventPoint q.val.2.1 j).1) i := by
  let J := feedbackSceneRoofJoining lam hlam0 hlam P Q
  let μ := J.comap (Subtype.val : S → FeedbackSceneRoofPoint)
  let p (q : S) := q.val.2.1
  let scene₁ (q : S) := q.val.2.2.1
  let scene₂ (q : S) := q.val.2.2.2
  have hp : Measurable p := measurable_subtype_coe.snd.fst
  have h₁ : Measurable scene₁ := measurable_subtype_coe.snd.snd.fst
  have h₂ : Measurable scene₂ := measurable_subtype_coe.snd.snd.snd
  have hval : μ.map Subtype.val = J :=
    feedbackSceneRoofJoining_support_map lam hlam0 hlam P Q hS hfull
  have hroof : μ.map p = feedbackStationaryRoofLaw lam hlam0 hlam := by
    calc
      _ = (μ.map Subtype.val).map (fun q : FeedbackSceneRoofPoint ↦ q.2.1) :=
        (Measure.map_map measurable_snd.fst measurable_subtype_coe).symm
      _ = _ := by rw [hval]; exact feedbackSceneRoofJoining_roof lam hlam0 hlam P Q
  have hJshift (a : ℝ) : MeasurePreserving (feedbackSceneRoofFlow a) J J :=
    measurePreserving_feedbackSceneRoofFlow hlam0 hlam P Q hPenv hQenv a (hPstat a) (hQstat a)
  let shift := fun a ↦ feedbackSceneSupportFlow S (-a)
  have hshift (a : ℝ) : MeasurePreserving (shift a) μ μ :=
    measurePreserving_feedbackSceneSupportFlow hS J hfull (-a) (hJshift (-a))
  have hflow (a : ℝ) : ∀ᵐ q ∂μ,
      p (shift a q) = feedbackRoofFlow (-a) (p q) ∧
      scene₁ (shift a q) = (scene₁ q).reroot (-a) ∧
      scene₂ (shift a q) = (scene₂ q).reroot (-a) := by
    filter_upwards [feedbackSceneSupportFlow_ae hS J hfull (-a) (hJshift (-a))] with q hq
    exact ⟨congrArg (fun z : FeedbackSceneRoofPoint ↦ z.2.1) hq,
      congrArg (fun z : FeedbackSceneRoofPoint ↦ z.2.2.1) hq,
      congrArg (fun z : FeedbackSceneRoofPoint ↦ z.2.2.2) hq⟩
  exact ae_feedbackSceneRawPartner_no_oneSidedOrbit p scene₁ scene₂
    (fun q ↦ (hgood q q.property 0).1) (fun q ↦ (hgood q q.property 1).1)
    (fun q ↦ congrArg FeedbackEnvironment.source (hgood q q.property 0).2)
    (fun q ↦ congrArg FeedbackEnvironment.target (hgood q q.property 0).2)
    (fun q ↦ congrArg FeedbackEnvironment.source (hgood q q.property 1).2)
    (fun q ↦ congrArg FeedbackEnvironment.target (hgood q q.property 1).2)
    hp h₁ h₂ hlam0 hlam μ hroof shift hshift hflow

/-- For each fixed spatial cut, the actual stationary joining almost surely has the
property that a common empty cut forces equality of the complete edge configurations. -/
theorem ae_feedbackSceneRoofJoining_commonEmptyCut_implies_edges_eq
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (hlam8 : lam < 1 / 8)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPenv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQenv : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hPstat : ∀ a, MeasurePreserving (MatchingScene.reroot a) P P)
    (hQstat : ∀ a, MeasurePreserving (MatchingScene.reroot a) Q Q)
    (hcandidate : ∀ k : Fin 2, ∀ᵐ scene ∂(![P, Q] k), FeedbackSceneEnergyCandidate lam scene) :
    ∀ x, ∀ᵐ q ∂feedbackSceneRoofJoining lam hlam0 hlam P Q,
      feedbackSceneCommonEmptyCut q x → q.2.2.1.edges = q.2.2.2.edges := by
  intro x
  have hperfectP : ∀ᵐ scene ∂P, scene.IsSimplePerfectMatching :=
    (hcandidate 0).mono fun _ h ↦ h.perfect
  have hperfectQ : ∀ᵐ scene ∂Q, scene.IsSimplePerfectMatching :=
    (hcandidate 1).mono fun _ h ↦ h.perfect
  obtain ⟨S, hS, hfull, hgood⟩ := exists_feedbackSceneRoofJoining_support
    lam hlam0 hlam P Q hPenv hQenv hperfectP hperfectQ
  let J := feedbackSceneRoofJoining lam hlam0 hlam P Q
  let μ := J.comap (Subtype.val : S → FeedbackSceneRoofPoint)
  have hval : μ.map Subtype.val = J :=
    feedbackSceneRoofJoining_support_map lam hlam0 hlam P Q hS hfull
  have hroof : μ.map (fun q : S ↦ q.val.2.1) = feedbackStationaryRoofLaw lam hlam0 hlam := by
    calc
      _ = (μ.map Subtype.val).map (fun q : FeedbackSceneRoofPoint ↦ q.2.1) :=
        (Measure.map_map measurable_snd.fst measurable_subtype_coe).symm
      _ = _ := by rw [hval]; exact feedbackSceneRoofJoining_roof lam hlam0 hlam P Q
  have henv : μ.map (fun q : S ↦ feedbackRoofEnvironment lam q.val.2.1) =
      feedbackStationaryEnvironmentLaw lam hlam0 hlam := by
    rw [← feedbackStationaryRoofLaw_environment_map lam hlam0 hlam, ← hroof,
      Measure.map_map (measurable_feedbackRoofEnvironment lam) measurable_subtype_coe.snd.fst]
    rfl
  have hmEnv : Measurable (fun q : S ↦ feedbackRoofEnvironment lam q.val.2.1) :=
    (measurable_feedbackRoofEnvironment lam).comp measurable_subtype_coe.snd.fst
  have htie := feedbackStationaryEnvironmentLaw_no_finite_ties hlam0 hlam8
  have hnon := ae_feedbackStationary_zero_count_at hlam0 hlam x
  rw [← henv] at htie hnon
  have hc (k : Fin 2) : ∀ᵐ q ∂μ, FeedbackSceneEnergyCandidate lam (feedbackSceneRoofScene q.val k) := by
    have hm : μ.map (fun q : S ↦ feedbackSceneRoofScene q.val k) = ![P, Q] k := by
      calc
        _ = (μ.map Subtype.val).map (fun q ↦ feedbackSceneRoofScene q k) :=
          (Measure.map_map (measurable_feedbackSceneRoofScene k) measurable_subtype_coe).symm
        _ = _ := by
          rw [hval]
          fin_cases k
          · exact feedbackSceneRoofJoining_scene_left lam hlam0 hlam P Q hPenv
          · exact feedbackSceneRoofJoining_scene_right lam hlam0 hlam P Q hPenv hQenv
    have hh := hcandidate k
    rw [← hm] at hh
    exact ae_of_ae_map ((measurable_feedbackSceneRoofScene k).comp measurable_subtype_coe).aemeasurable hh
  have hanchor := ae_feedbackSceneRoofJoiningSupport_no_oneSidedOrbit
    hlam0 hlam P Q hPenv hQenv hPstat hQstat hS hfull hgood
  change ∀ᵐ q ∂J, _
  rw [← hval]
  apply (MeasurableEmbedding.subtype_coe hS).ae_map_iff.mpr
  filter_upwards [hanchor, ae_of_ae_map hmEnv.aemeasurable htie,
    ae_of_ae_map hmEnv.aemeasurable hnon, ae_all_iff.mpr hc] with q ha ht hn hcq
  exact fun hcut ↦ feedbackScene_edges_eq_of_commonEmptyCut q.val
    (hgood q q.property) hcq ht ha x hn hcut

end OTSelector.Matching
