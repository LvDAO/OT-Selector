import OTSelector.Matching.FeedbackSceneJoining

/-!
# The common empty cut under the actual scene joining

The original scene laws supply local minimality, their recovered current, and their linear
energy means. Relative joining attaches the genuine stationary roof. Passing to a measurable
full-measure support permits the actual atom assignments to be pulled back to retained labels;
the proved conditional bootstrap then gives a common empty cut in the original joined law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

/-- The geometric properties inherited by a candidate matching scene. -/
structure FeedbackSceneEnergyCandidate (lam : ℝ) (scene : MatchingScene) : Prop where
  perfect : scene.IsSimplePerfectMatching
  finite_crossings : ∀ x, {i : MatchingScene.SourceAtom scene |
    Crosses x i.val.1 (MatchingScene.atomAssignment perfect i).val.1}.Finite
  current_eq : ∀ x, (MatchingScene.spatialMatching perfect).current x = scene.currentAt x
  locally_minimizing : (MatchingScene.spatialMatching perfect).IsLocallyMinimizing
    (fun i j ↦ markedQuadraticCost scene.path.graphHeight i.val j.val)

/-- The two actual scenes have no edge crossing the indicated rooted cut. -/
def feedbackSceneCommonEmptyCut (q : FeedbackSceneRoofPoint) (x : ℝ) : Prop :=
  ∀ k : Fin 2, ∀ hp : (feedbackSceneRoofScene q k).IsSimplePerfectMatching,
    ∀ i : MatchingScene.SourceAtom (feedbackSceneRoofScene q k),
      ¬Crosses x i.val.1 (MatchingScene.atomAssignment hp i).val.1

/-- Pulling scene assignments back to labels preserves the assertion of a common empty cut. -/
theorem feedbackSceneCommonEmptyCut_of_labels {lam : ℝ} (q : FeedbackSceneRoofPoint)
    (hgood : ∀ k : Fin 2, (feedbackSceneRoofScene q k).IsSimplePerfectMatching ∧
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1)
    (h : ℝ)
    (hcut : ∀ k : Fin 2, ∀ i : FeedbackEventLabel q.2.1.1 1,
      ¬Crosses (q.2.1.2 + h / 2) (feedbackCellEventPoint q.2.1.1 i).1
        (feedbackCellEventPoint q.2.1.1
          (feedbackSceneAssignment q.2.1 (feedbackSceneRoofScene q k) (hgood k).1
            (congrArg FeedbackEnvironment.source (hgood k).2)
            (congrArg FeedbackEnvironment.target (hgood k).2) i)).1) :
    feedbackSceneCommonEmptyCut q (h / 2) := by
  intro k hp i hi
  let scene := feedbackSceneRoofScene q k
  have hs := congrArg FeedbackEnvironment.source (hgood k).2
  have ht := congrArg FeedbackEnvironment.target (hgood k).2
  obtain ⟨j, rfl⟩ := (feedbackSceneSourceEquiv q.2.1 scene hs).surjective i
  have hsource := feedbackSceneSourceEquiv_coordinate q.2.1 scene hs j
  have htarget := feedbackSceneAssignment_coordinate q.2.1 scene hp hs ht j
  apply hcut k j
  change Crosses (h / 2) (feedbackSceneSourceEquiv q.2.1 scene hs j).val.1
    (MatchingScene.atomAssignment hp (feedbackSceneSourceEquiv q.2.1 scene hs j)).val.1 at hi
  rw [hsource, htarget] at hi
  rcases hi with hi | hi
  · exact Or.inl ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · exact Or.inr ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-- Any actual joint law with the true roof marginal has a positive conditional common empty
cut. No conditional independence of the scenes is required. -/
theorem exists_feedbackSceneJoint_commonEmptyCut
    {lam : ℝ} {hlam0 : 0 < lam} {hlam : lam < 1 / 2} (hlam8 : lam < 1 / 8)
    (regularity : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (J : Measure FeedbackSceneRoofPoint) [IsProbabilityMeasure J]
    (hJroof : J.map (fun q ↦ q.2.1) = feedbackStationaryRoofLaw lam hlam0 hlam)
    (hJscene : ∀ k : Fin 2, J.map (fun q ↦ feedbackSceneRoofScene q k) = ![P, Q] k)
    (henv : ∀ᵐ q ∂J, ∀ k : Fin 2,
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1)
    (hcandidate : ∀ k : Fin 2, ∀ᵐ scene ∂(![P, Q] k),
      FeedbackSceneEnergyCandidate lam scene)
    (Cenergy : Fin 2 → ℝ)
    (henergyInt : ∀ k h R, 0 < R →
      Integrable (fun scene ↦ feedbackSceneWindowEnergy scene h R) (![P, Q] k))
    (hmean : ∀ k h R, 0 < R →
      (∫ scene, feedbackSceneWindowEnergy scene h R ∂(![P, Q] k)) ≤ Cenergy k * R) :
    ∃ h > 0, 0 < (ProbabilityTheory.cond J
      {q | q.2.1 ∈ feedbackRoofHoldBand lam h}).real
      {q | feedbackSceneCommonEmptyCut q (h / 2)} := by
  let good : Set FeedbackSceneRoofPoint := {q | ∀ k : Fin 2,
    (feedbackSceneRoofScene q k).IsSimplePerfectMatching ∧
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1}
  have hgoodJ : ∀ᵐ q ∂J, q ∈ good := by
    have hc : ∀ᵐ q ∂J, ∀ k : Fin 2,
        FeedbackSceneEnergyCandidate lam (feedbackSceneRoofScene q k) := by
      rw [ae_all_iff]
      intro k
      have hk := hcandidate k
      rw [← hJscene k] at hk
      exact ae_of_ae_map (measurable_feedbackSceneRoofScene k).aemeasurable hk
    filter_upwards [hc, henv] with q hc he
    exact fun k ↦ ⟨(hc k).perfect, he k⟩
  have heq : (univ : Set FeedbackSceneRoofPoint) =ᵐ[J] good := by
    filter_upwards [hgoodJ] with q hq
    exact propext ⟨fun _ ↦ hq, fun _ ↦ mem_univ q⟩
  obtain ⟨S, hSgood, hS, hSeq⟩ :=
    ((MeasurableSet.univ.nullMeasurableSet (μ := J)).congr heq).exists_measurable_subset_ae_eq
  have hfull : ∀ᵐ q ∂J, q ∈ S := by
    filter_upwards [hgoodJ, hSeq] with q hq he
    exact he.mpr hq
  have hgood := fun q hq ↦ hSgood (a := q) hq
  let μ := J.comap (Subtype.val : S → FeedbackSceneRoofPoint)
  have hval : μ.map Subtype.val = J := by
    rw [map_comap_subtype_coe hS, Measure.restrict_eq_self_of_ae_mem hfull]
  let : IsProbabilityMeasure (μ.map Subtype.val) := hval ▸ inferInstance
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_of_map Subtype.val
  let p (q : S) := q.val.2.1
  let scene (k : Fin 2) (q : S) := feedbackSceneRoofScene q.val k
  have hp : Measurable p := measurable_subtype_coe.snd.fst
  have hscene (k : Fin 2) : Measurable (scene k) :=
    (measurable_feedbackSceneRoofScene k).comp measurable_subtype_coe
  have hroof : μ.map p = feedbackStationaryRoofLaw lam hlam0 hlam := by
    calc
      _ = (μ.map Subtype.val).map (fun q : FeedbackSceneRoofPoint ↦ q.2.1) :=
        (Measure.map_map measurable_snd.fst measurable_subtype_coe).symm
      _ = _ := by rw [hval]; exact hJroof
  have hsceneMap (k : Fin 2) : μ.map (scene k) = ![P, Q] k := by
    calc
      _ = (μ.map Subtype.val).map (fun q ↦ feedbackSceneRoofScene q k) :=
        (Measure.map_map (measurable_feedbackSceneRoofScene k) measurable_subtype_coe).symm
      _ = _ := by rw [hval]; exact hJscene k
  let assignment (k : Fin 2) (q : S) := feedbackSceneAssignment (p q) (scene k q)
    (hgood q q.property k).1 (congrArg FeedbackEnvironment.source (hgood q q.property k).2)
      (congrArg FeedbackEnvironment.target (hgood q q.property k).2)
  have hcurrent : ∀ᵐ q ∂μ, ∀ x,
      FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam (p q).1).currentIncrement
        (feedbackConcatenatedEnvironment lam (p q).1).path x =
          feedbackConcatenatedCurrent (p q).1 x := by
    have hw : ∀ᵐ p ∂feedbackStationaryRoofLaw lam hlam0 hlam, ∀ x,
        FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam p.1).currentIncrement
          (feedbackConcatenatedEnvironment lam p.1).path x = feedbackConcatenatedCurrent p.1 x := by
      apply Measure.ae_smul_measure
      apply ae_restrict_of_ae
      exact Measure.quasiMeasurePreserving_fst.ae
        (ae_currentAt_feedbackConcatenatedEnvironment hlam0 hlam)
    rw [← hroof] at hw
    exact ae_of_ae_map hp.aemeasurable hw
  have hadmissible (k : Fin 2) : ∀ᵐ q ∂μ,
      FeedbackMatchingAdmissible (p q) (assignment k q) lam := by
    have hc := hcandidate k
    rw [← hsceneMap k] at hc
    filter_upwards [ae_of_ae_map (hscene k).aemeasurable hc, hcurrent] with q hc hw
    exact feedbackSceneAssignment_admissible (p q) (scene k q) (hgood q q.property k).1
      (hgood q q.property k).2 hc.finite_crossings hc.current_eq hc.locally_minimizing hw
  have henergy (k : Fin 2) (h R : ℝ) :
      (fun q ↦ feedbackWindowEnergy (p q) (assignment k q) h R) =
        (fun q ↦ feedbackSceneWindowEnergy (scene k q) h R) := by
    funext q
    rw [feedbackSceneWindowEnergy_of_perfect _ (hgood q q.property k).1]
    exact feedbackSceneAssignment_windowEnergy (p q) (scene k q) _ _ _ h R
  have hInt (k : Fin 2) (h R : ℝ) (hR : 0 < R) :
      Integrable (fun q ↦ feedbackWindowEnergy (p q) (assignment k q) h R) μ := by
    rw [henergy]
    have hi := henergyInt k h R hR
    rw [← hsceneMap k] at hi
    exact hi.comp_measurable (hscene k)
  have hMean (k : Fin 2) (h R : ℝ) (hR : 0 < R) :
      (∫ q, feedbackWindowEnergy (p q) (assignment k q) h R ∂μ) ≤ Cenergy k * R := by
    rw [henergy]
    have hi := henergyInt k h R hR
    rw [← hsceneMap k] at hi
    rw [← integral_map (hscene k).aemeasurable hi.aestronglyMeasurable, hsceneMap]
    exact hmean k h R hR
  obtain ⟨h, hh, hpos⟩ := exists_feedbackConditional_commonEmptyCut hlam8 regularity
    μ hp hroof assignment hadmissible Cenergy hInt hMean
  refine ⟨h, hh, ?_⟩
  let A : Set FeedbackSceneRoofPoint := {q | q.2.1 ∈ feedbackRoofHoldBand lam h}
  have hA : MeasurableSet A := (measurableSet_feedbackRoofHoldBand lam h).preimage measurable_snd.fst
  let ν := ProbabilityTheory.cond μ (Subtype.val ⁻¹' A)
  let N := ProbabilityTheory.cond J A
  have hmass : μ (Subtype.val ⁻¹' A) = J A := by
    rw [← Measure.map_apply measurable_subtype_coe hA, hval]
  have hνmap : ν.map Subtype.val = N := by
    change (ProbabilityTheory.cond μ (Subtype.val ⁻¹' A)).map Subtype.val = ProbabilityTheory.cond J A
    rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul,
      ← Measure.restrict_map measurable_subtype_coe hA, hval, hmass]
  have hApos : J A ≠ 0 := by
    change J ((fun q ↦ q.2.1) ⁻¹' feedbackRoofHoldBand lam h) ≠ 0
    rw [← Measure.map_apply measurable_snd.fst (measurableSet_feedbackRoofHoldBand lam h), hJroof]
    exact (feedbackStationaryRoofLaw_band_pos lam hlam0 hlam h hh.le).ne'
  let : IsProbabilityMeasure N := ProbabilityTheory.cond_isProbabilityMeasure hApos
  have hle : ν {q | ∀ k : Fin 2, ∀ i : FeedbackEventLabel (p q).1 1,
      ¬Crosses ((p q).2 + h / 2) (feedbackCellEventPoint (p q).1 i).1
        (feedbackCellEventPoint (p q).1 (assignment k q i)).1} ≤
      N {q | feedbackSceneCommonEmptyCut q (h / 2)} := by
    have hs : {q : S | ∀ k : Fin 2, ∀ i : FeedbackEventLabel (p q).1 1,
        ¬Crosses ((p q).2 + h / 2) (feedbackCellEventPoint (p q).1 i).1
          (feedbackCellEventPoint (p q).1 (assignment k q i)).1} ⊆
        Subtype.val ⁻¹' {q | feedbackSceneCommonEmptyCut q (h / 2)} :=
      fun q hq ↦ feedbackSceneCommonEmptyCut_of_labels q.val (hgood q q.property) h hq
    apply le_trans (measure_mono hs)
    exact (Measure.le_map_apply measurable_subtype_coe.aemeasurable _).trans_eq
      (congrArg (fun m ↦ m {q | feedbackSceneCommonEmptyCut q (h / 2)}) hνmap)
  exact hpos.trans_le (ENNReal.toReal_mono (measure_ne_top N _) hle)

/-- The actual joined law assigns positive conditional probability to a common empty cut.
Only the original, unconditional scene energy means enter the argument. -/
theorem exists_feedbackSceneRoofJoining_commonEmptyCut
    {lam : ℝ} {hlam0 : 0 < lam} {hlam : lam < 1 / 2} (hlam8 : lam < 1 / 8)
    (regularity : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQ : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hcandidate : ∀ k : Fin 2, ∀ᵐ scene ∂(![P, Q] k),
      FeedbackSceneEnergyCandidate lam scene)
    (Cenergy : Fin 2 → ℝ)
    (henergyInt : ∀ k h R, 0 < R →
      Integrable (fun scene ↦ feedbackSceneWindowEnergy scene h R) (![P, Q] k))
    (hmean : ∀ k h R, 0 < R →
      (∫ scene, feedbackSceneWindowEnergy scene h R ∂(![P, Q] k)) ≤ Cenergy k * R) :
    ∃ h > 0, 0 < (ProbabilityTheory.cond (feedbackSceneRoofJoining lam hlam0 hlam P Q)
      {q | q.2.1 ∈ feedbackRoofHoldBand lam h}).real
      {q | feedbackSceneCommonEmptyCut q (h / 2)} := by
  apply exists_feedbackSceneJoint_commonEmptyCut hlam8 regularity P Q
    (feedbackSceneRoofJoining lam hlam0 hlam P Q)
    (feedbackSceneRoofJoining_roof lam hlam0 hlam P Q) _ _ hcandidate Cenergy henergyInt hmean
  · intro k
    fin_cases k
    · exact feedbackSceneRoofJoining_scene_left lam hlam0 hlam P Q hP
    · exact feedbackSceneRoofJoining_scene_right lam hlam0 hlam P Q hP hQ
  · filter_upwards [feedbackSceneRoofJoining_ae_environment lam hlam0 hlam P Q hP hQ] with q hq k
    fin_cases k
    · exact hq.1
    · exact hq.2

end OTSelector.Matching
