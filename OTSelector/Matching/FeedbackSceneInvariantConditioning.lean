import OTSelector.Matching.FeedbackSceneEnergyMoment
import OTSelector.Matching.FeedbackSceneJoiningFlow
import OTSelector.Probability.ErgodicConditioning

/-!
# Invariant conditioning closes actual matching uniqueness

Conditioning the actual joint law on its invariant disagreement event preserves the true roof
marginal, because the iid renewal roof is ergodic for the entire real flow. The original joint
correlations are retained. Finite root moments survive conditioning, so the common-cut theorem
applies again inside disagreement and contradicts the geometric agreement at a common cut.
-/

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

local instance : Nonempty MatchingScene := ⟨⟨0, 0, 0, ⟨0, 0⟩⟩⟩

/-- The actual iid suspension is ergodic for all spatial translations jointly. -/
theorem feedbackRoofFlow_aeconst {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    {S : Set (FeedbackCellSequence × ℝ)} (hS : MeasurableSet S)
    (hinv : ∀ t : ℝ, feedbackRoofFlow t ⁻¹' S =ᵐ[feedbackStationaryRoofLaw lam hlam0 hlam] S) :
    EventuallyConst S (ae (feedbackStationaryRoofLaw lam hlam0 hlam)) := by
  rw [← feedbackRoofFlow_stationaryLaw_eq hlam0 hlam] at hinv ⊢
  exact aeconst_set_renewalStationaryLaw (feedbackCellBase lam hlam0 hlam)
    (measurable_feedbackCellLength.comp (measurable_pi_apply 0))
    (integrable_feedbackCellBase_length hlam0 hlam 0)
    ((feedbackCellBase_lengths_positive hlam0 hlam).mono fun _ hw ↦ hw 0)
    (IIDShift.ergodic_shift_one (feedbackMarkedTrajectory lam hlam0 hlam 0))
    measurable_feedbackRoofFlow (measurable_id.prodMk measurable_const)
    feedbackRoofFlow_add
    ((feedbackCellBase_roots_good hlam0 hlam).mono fun _ hw ↦
      (feedbackRoofFlow_cellLength hw).symm) hS hinv

/-- Invariant conditioning preserves the actual roof marginal of the original joint law. -/
theorem map_cond_feedbackSceneRoof_invariant {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (J : Measure FeedbackSceneRoofPoint) [IsProbabilityMeasure J]
    (hroof : J.map (fun q ↦ q.2.1) = feedbackStationaryRoofLaw lam hlam0 hlam)
    (hstationary : ∀ t, MeasurePreserving (feedbackSceneRoofFlow t) J J)
    {B : Set FeedbackSceneRoofPoint} (hB : MeasurableSet B)
    (hBinv : ∀ t, feedbackSceneRoofFlow t ⁻¹' B =ᵐ[J] B) (hpos : J B ≠ 0) :
    (ProbabilityTheory.cond J B).map (fun q ↦ q.2.1) =
      feedbackStationaryRoofLaw lam hlam0 hlam := by
  let : VAdd ℝ (FeedbackCellSequence × ℝ) := ⟨feedbackRoofFlow⟩
  let : MeasurableConstVAdd ℝ (FeedbackCellSequence × ℝ) := ⟨fun t ↦
    measurable_feedbackRoofFlow.comp (f := fun p : FeedbackCellSequence × ℝ ↦ (t, p))
      (measurable_const.prodMk measurable_id)⟩
  let : VAdd ℝ FeedbackSceneRoofPoint := ⟨feedbackSceneRoofFlow⟩
  let : MeasurableConstVAdd ℝ FeedbackSceneRoofPoint := ⟨measurable_feedbackSceneRoofFlow⟩
  let : VAddInvariantMeasure ℝ (FeedbackCellSequence × ℝ)
      (feedbackStationaryRoofLaw lam hlam0 hlam) := ⟨fun t S hS ↦
    (measurePreserving_feedbackRoofFlow hlam0 hlam t).measure_preimage hS.nullMeasurableSet⟩
  let : ErgodicVAdd ℝ (FeedbackCellSequence × ℝ)
      (feedbackStationaryRoofLaw lam hlam0 hlam) := ⟨fun hS hI ↦
    feedbackRoofFlow_aeconst hlam0 hlam hS hI⟩
  exact Probability.map_cond_invariant_event
    (show MeasurePreserving (fun q : FeedbackSceneRoofPoint ↦ q.2.1) J
      (feedbackStationaryRoofLaw lam hlam0 hlam) from ⟨measurable_snd.fst, hroof⟩)
    hstationary (fun _ _ ↦ rfl) hB hBinv hpos

/-- The actual two scenes differ as edge configurations. -/
def feedbackSceneDifference : Set FeedbackSceneRoofPoint :=
  {q | q.2.2.1.edges ≠ q.2.2.2.edges}

theorem measurableSet_feedbackSceneDifference : MeasurableSet feedbackSceneDifference :=
  (measurableSet_eq_fun (MatchingScene.measurable_edges.comp measurable_snd.snd.fst)
    (MatchingScene.measurable_edges.comp measurable_snd.snd.snd)).compl

/-- Spatial translation preserves exact disagreement of the actual edge configurations. -/
theorem feedbackSceneDifference_invariant (t : ℝ) :
    feedbackSceneRoofFlow t ⁻¹' feedbackSceneDifference = feedbackSceneDifference := by
  have hi : Injective (LocalConfiguration.mapHomeomorph
      (base := (matchingPointBase, matchingPointBase)) (MatchingScene.edgeReroot t)) := by
    intro a b hab
    have h := congrArg (LocalConfiguration.mapHomeomorph (MatchingScene.edgeReroot t).symm) hab
    simpa only [LocalConfiguration.mapHomeomorph_trans, Homeomorph.self_trans_symm,
      LocalConfiguration.mapHomeomorph_refl] using h
  ext q
  exact not_congr hi.eq_iff

/-- A stationary actual joint law admits the common-cut argument without any independence
requirement on its two scene coordinates. Only finite actual root moments are needed. -/
theorem exists_feedbackSceneJoint_commonEmptyCut_of_finite_rootMoment
    {lam : ℝ} {hlam0 : 0 < lam} {hlam : lam < 1 / 2} (hlam8 : lam < 1 / 8)
    (regularity : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (J : Measure FeedbackSceneRoofPoint) [IsProbabilityMeasure J]
    (hroof : J.map (fun q ↦ q.2.1) = feedbackStationaryRoofLaw lam hlam0 hlam)
    (henv : ∀ᵐ q ∂J, ∀ k : Fin 2,
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1)
    (hstationary : ∀ t, MeasurePreserving (feedbackSceneRoofFlow t) J J)
    (hcandidate : ∀ k : Fin 2, ∀ᵐ scene ∂J.map (fun q ↦ feedbackSceneRoofScene q k),
      FeedbackSceneEnergyCandidate lam scene)
    (hroot : ∀ k : Fin 2, (∫⁻ q, MatchingScene.crossingEnergyMoment (feedbackSceneRoofScene q k) 0 ∂J) < ∞) :
    ∃ h > 0, 0 < (ProbabilityTheory.cond J {q | q.2.1 ∈ feedbackRoofHoldBand lam h}).real
      {q | feedbackSceneCommonEmptyCut q (h / 2)} := by
  let P := J.map (fun q ↦ feedbackSceneRoofScene q 0)
  let Q := J.map (fun q ↦ feedbackSceneRoofScene q 1)
  let : IsProbabilityMeasure P :=
    Measure.isProbabilityMeasure_map (measurable_feedbackSceneRoofScene 0).aemeasurable
  let : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map (measurable_feedbackSceneRoofScene 1).aemeasurable
  have hscene (k : Fin 2) : J.map (fun q ↦ feedbackSceneRoofScene q k) = ![P, Q] k := by
    fin_cases k <;> rfl
  have hcand (k : Fin 2) : ∀ᵐ scene ∂(![P, Q] k), FeedbackSceneEnergyCandidate lam scene := by
    rw [← hscene k]
    exact hcandidate k
  have hstationaryScene (k : Fin 2) (t : ℝ) :
      MeasurePreserving (MatchingScene.reroot t) (![P, Q] k) (![P, Q] k) := by
    rw [← hscene k]
    apply ((measurable_feedbackSceneRoofScene k).measurePreserving J).of_semiconj (hstationary t)
    · intro q
      fin_cases k <;> rfl
    · exact (MatchingScene.rerootMeasurableEquiv t).measurable
  let C (k : Fin 2) :=
    (∫⁻ q, MatchingScene.crossingEnergyMoment (feedbackSceneRoofScene q k) 0 ∂J).toReal
  have hm : Measurable (fun scene : MatchingScene ↦ MatchingScene.crossingEnergyMoment scene 0) :=
    measurable_feedbackSceneCrossingMoment.comp
      (f := fun scene : MatchingScene ↦ (scene, (0 : ℝ))) (measurable_id.prodMk measurable_const)
  have hb (k : Fin 2) :
      (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂(![P, Q] k)) ≤ ENNReal.ofReal (C k) := by
    rw [← hscene k, lintegral_map hm (measurable_feedbackSceneRoofScene k)]
    dsimp only [C]
    rw [ENNReal.ofReal_toReal (hroot k).ne]
  have hmoment (k : Fin 2) (h R : ℝ) (hR : 0 < R) :
      Integrable (fun scene ↦ feedbackSceneWindowEnergy scene h R) (![P, Q] k) ∧
        (∫ scene, feedbackSceneWindowEnergy scene h R ∂(![P, Q] k)) ≤ C k * R := by
    let : IsProbabilityMeasure (![P, Q] k) := by
      fin_cases k
      · exact (inferInstance : IsProbabilityMeasure P)
      · exact (inferInstance : IsProbabilityMeasure Q)
    exact feedbackSceneWindowEnergy_moment_le (![P, Q] k) (hstationaryScene k)
      ((hcand k).mono fun _ hc ↦ ⟨hc.perfect, hc.finite_crossings⟩)
      ENNReal.toReal_nonneg (hb k) h R hR.le
  exact exists_feedbackSceneJoint_commonEmptyCut hlam8 regularity P Q J hroof hscene henv
    hcand C (fun k h R hR ↦ (hmoment k h R hR).1) (fun k h R hR ↦ (hmoment k h R hR).2)

/-- A positive invariant restriction remains stationary under each concrete spatial translation. -/
theorem measurePreserving_cond_feedbackSceneRoofFlow
    (J : Measure FeedbackSceneRoofPoint) [IsProbabilityMeasure J]
    (hstationary : ∀ t, MeasurePreserving (feedbackSceneRoofFlow t) J J)
    {B : Set FeedbackSceneRoofPoint} (hB : MeasurableSet B)
    (hBinv : ∀ t, feedbackSceneRoofFlow t ⁻¹' B =ᵐ[J] B) (t : ℝ) :
    MeasurePreserving (feedbackSceneRoofFlow t) (ProbabilityTheory.cond J B)
      (ProbabilityTheory.cond J B) := by
  have hr := (hstationary t).restrict_preimage hB
  rw [Measure.restrict_congr_set (hBinv t)] at hr
  exact hr.smul_measure _

/-- Finite nonnegative actual moments remain finite after conditioning on a positive event. -/
theorem feedbackScene_rootMoment_cond_lt_top
    (J : Measure FeedbackSceneRoofPoint) [IsProbabilityMeasure J]
    {B : Set FeedbackSceneRoofPoint} (hpos : J B ≠ 0) (k : Fin 2)
    (hroot : (∫⁻ q, MatchingScene.crossingEnergyMoment (feedbackSceneRoofScene q k) 0 ∂J) < ∞) :
    (∫⁻ q, MatchingScene.crossingEnergyMoment (feedbackSceneRoofScene q k) 0
      ∂ProbabilityTheory.cond J B) < ∞ := by
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hpos))
    ((setLIntegral_le_lintegral B _).trans_lt hroot)

/-- Conditioning on disagreement upgrades geometric agreement at a common empty cut to almost
sure equality. The true joint law is conditioned directly throughout the proof. -/
theorem ae_feedbackSceneEdges_eq_of_commonEmptyCut
    {lam : ℝ} {hlam0 : 0 < lam} {hlam : lam < 1 / 2} (hlam8 : lam < 1 / 8)
    (regularity : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (J : Measure FeedbackSceneRoofPoint) [IsProbabilityMeasure J]
    (hroof : J.map (fun q ↦ q.2.1) = feedbackStationaryRoofLaw lam hlam0 hlam)
    (henv : ∀ᵐ q ∂J, ∀ k : Fin 2,
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1)
    (hstationary : ∀ t, MeasurePreserving (feedbackSceneRoofFlow t) J J)
    (hcandidate : ∀ k : Fin 2, ∀ᵐ scene ∂J.map (fun q ↦ feedbackSceneRoofScene q k),
      FeedbackSceneEnergyCandidate lam scene)
    (hroot : ∀ k : Fin 2, (∫⁻ q, MatchingScene.crossingEnergyMoment (feedbackSceneRoofScene q k) 0 ∂J) < ∞)
    (hcut : ∀ x : ℝ, ∀ᵐ q ∂J,
      feedbackSceneCommonEmptyCut q x → q.2.2.1.edges = q.2.2.2.edges) :
    ∀ᵐ q ∂J, q.2.2.1.edges = q.2.2.2.edges := by
  by_contra hnot
  have hpos : J feedbackSceneDifference ≠ 0 := by
    simpa only [ae_iff, feedbackSceneDifference] using hnot
  let ν := ProbabilityTheory.cond J feedbackSceneDifference
  let : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure hpos
  have hνroof := map_cond_feedbackSceneRoof_invariant hlam0 hlam J hroof hstationary
    measurableSet_feedbackSceneDifference (fun t ↦ ae_of_all _ fun _ ↦
      congrArg (fun S ↦ _ ∈ S) (feedbackSceneDifference_invariant t)) hpos
  have hνstationary : ∀ t, MeasurePreserving (feedbackSceneRoofFlow t) ν ν :=
    measurePreserving_cond_feedbackSceneRoofFlow J hstationary measurableSet_feedbackSceneDifference
      (fun t ↦ ae_of_all _ fun q ↦ congrArg (fun S ↦ q ∈ S) (feedbackSceneDifference_invariant t))
  have hcand (k : Fin 2) : ∀ᵐ scene ∂ν.map (fun q ↦ feedbackSceneRoofScene q k),
      FeedbackSceneEnergyCandidate lam scene :=
    (ProbabilityTheory.cond_absolutelyContinuous.map (measurable_feedbackSceneRoofScene k)).ae_le
      (hcandidate k)
  have hνenv : ∀ᵐ q ∂ν, ∀ k : Fin 2,
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1 :=
    ProbabilityTheory.cond_absolutelyContinuous.ae_le henv
  obtain ⟨h, hh, hcutpos⟩ := exists_feedbackSceneJoint_commonEmptyCut_of_finite_rootMoment
    hlam8 regularity ν hνroof hνenv hνstationary hcand
    (fun k ↦ feedbackScene_rootMoment_cond_lt_top J hpos k (hroot k))
  let ξ := ProbabilityTheory.cond ν {q | q.2.1 ∈ feedbackRoofHoldBand lam h}
  have hmem : ∀ᵐ q ∂ν, q ∈ feedbackSceneDifference := by
    apply Measure.ae_smul_measure
    exact ae_restrict_mem measurableSet_feedbackSceneDifference
  have hfalse : ∀ᵐ q ∂ξ, ¬feedbackSceneCommonEmptyCut q (h / 2) := by
    have hm : ∀ᵐ q ∂ξ, q ∈ feedbackSceneDifference :=
      ProbabilityTheory.cond_absolutelyContinuous.ae_le hmem
    have hc : ∀ᵐ q ∂ξ,
        feedbackSceneCommonEmptyCut q (h / 2) → q.2.2.1.edges = q.2.2.2.edges :=
      ProbabilityTheory.cond_absolutelyContinuous.ae_le
        (ProbabilityTheory.cond_absolutelyContinuous.ae_le (hcut (h / 2)))
    filter_upwards [hm, hc] with q hm hc
    exact fun hq ↦ hm (hc hq)
  have hz : ξ {q | feedbackSceneCommonEmptyCut q (h / 2)} = 0 := by
    simpa only [ae_iff, not_not] using hfalse
  change 0 < ξ.real {q | feedbackSceneCommonEmptyCut q (h / 2)} at hcutpos
  rw [Measure.real, hz, ENNReal.toReal_zero] at hcutpos
  exact (lt_irrefl (0 : ℝ)) hcutpos

/-- On the actual common-environment support, equality of edge codes is equality of scenes. -/
theorem ae_feedbackSceneRoofJoining_scenes_eq_of_edges_eq
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQ : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hedges : ∀ᵐ q ∂feedbackSceneRoofJoining lam hlam0 hlam P Q,
      q.2.2.1.edges = q.2.2.2.edges) :
    ∀ᵐ q ∂feedbackSceneRoofJoining lam hlam0 hlam P Q, q.2.2.1 = q.2.2.2 := by
  filter_upwards [hedges,
    feedbackSceneRoofJoining_ae_environment lam hlam0 hlam P Q hP hQ] with q he henv
  have h := henv.1.trans henv.2.symm
  exact MatchingScene.ext (congrArg FeedbackEnvironment.source h)
    (congrArg FeedbackEnvironment.target h) he (congrArg FeedbackEnvironment.path h)

/-- Actual joining agreement gives equality of the original scene laws and a common Dirac
conditional scene law over almost every actual stationary environment. -/
theorem feedbackSceneLaws_eq_and_condKernel_dirac_of_ae_edges_eq
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQ : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hedges : ∀ᵐ q ∂feedbackSceneRoofJoining lam hlam0 hlam P Q,
      q.2.2.1.edges = q.2.2.2.edges) :
    P = Q ∧ ∀ᵐ e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam,
      ∃ scene, (feedbackSceneEnvironmentLaw P).condKernel e = Measure.dirac scene ∧
        (feedbackSceneEnvironmentLaw Q).condKernel e = Measure.dirac scene := by
  have hscenes := ae_feedbackSceneRoofJoining_scenes_eq_of_edges_eq hlam0 hlam P Q hP hQ hedges
  have hpair : ∀ᵐ q ∂feedbackScenePairLaw P Q, q.2.1 = q.2.2 := by
    rw [← feedbackSceneRoofJoining_right lam hlam0 hlam P Q hP]
    exact (ae_map_iff (measurable_fst.prodMk measurable_snd.snd).aemeasurable
      (measurableSet_eq_fun measurable_snd.fst measurable_snd.snd)).mpr hscenes
  have heq := eq_of_relativeIndependentJoining_ae_eq (feedbackSceneEnvironmentLaw P)
    (feedbackSceneEnvironmentLaw Q) (by simpa using hP.trans hQ.symm) hpair
  refine ⟨?_, ?_⟩
  · simpa only [feedbackSceneEnvironmentLaw_snd] using congrArg Measure.snd heq
  · have hd := ae_condKernel_common_dirac_of_relativeIndependentJoining_ae_eq
      (feedbackSceneEnvironmentLaw P) (feedbackSceneEnvironmentLaw Q) hpair
    simpa only [feedbackSceneEnvironmentLaw_fst, hP] using hd

end OTSelector.Matching
