import OTSelector.Matching.FeedbackSceneUniqueness
import OTSelector.PointProcess.MassTransport
import OTSelector.Limit.FeedbackMarkIntensity

/-!
# The actual source Palm coupling of feedback marks

The projective law counts the marks of each genuine matching edge whose source lies in the
spatial unit window. Its source marginal follows from the actual source intensity. Stationary
mass transport moves the target-mark observation to a target window, proving the other uniform
marginal. Scene-law uniqueness then gives uniqueness of this same Palm coupling.
-/

open MeasureTheory ProbabilityTheory Set Function Filter
open scoped ENNReal Classical BigOperators

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

/-- Mean counting measure of the actual marked matching edges, with their original multiplicities. -/
noncomputable def feedbackSceneEdgeIntensity (P : Measure MatchingScene) :
    Measure (MatchingPoint × MatchingPoint) :=
  P.bind (fun scene ↦ LocalConfiguration.countingMeasure scene.edges)

/-- Actual mark-pair Palm measure, observed by the source coordinate in `(0,1]`. -/
noncomputable def feedbackProjectiveLaw (P : Measure MatchingScene) : Measure (UnitMark × UnitMark) :=
  ((feedbackSceneEdgeIntensity P).restrict {e | e.1.1 ∈ Ioc (0 : ℝ) 1}).map
    (fun e ↦ (e.1.2, e.2.2))

private theorem measurable_edgeCounting :
    Measurable (fun scene : MatchingScene ↦ LocalConfiguration.countingMeasure scene.edges) :=
  LocalConfiguration.measurable_countingMeasure.comp MatchingScene.measurable_edges

/-- Strict physical clocks make every actual concatenated marked configuration simple. -/
theorem feedbackConcatenatedPoints_multiplicity_le_one (w : FeedbackCellSequence)
    (direction : ℤ) (p : MatchingPoint) :
    LocalConfiguration.multiplicity (feedbackConcatenatedPoints direction w) p ≤ 1 := by
  have hb : LocalConfiguration.countingMeasure (feedbackConcatenatedPoints direction w) {p} ≤ 1 := by
    by_cases hz : LocalConfiguration.countingMeasure (feedbackConcatenatedPoints direction w) {p} = 0
    · simp [hz]
    obtain ⟨i, hi, hip⟩ := (feedbackConcatenatedPoints_atom_iff w direction p).mp hz
    rw [countingMeasure_feedbackConcatenatedPoints, Measure.sum_apply _ (measurableSet_singleton p),
      tsum_eq_single i]
    · simp [hi, hip]
    · intro j hji
      by_cases hj : feedbackCellEventActive w direction j
      · have hne : feedbackCellEventPoint w j ≠ p := by
          intro hjp
          apply hji
          exact feedbackCellEventPoint_fst_injective hj.1 hj.2.1 hi.2.1
            (congrArg Prod.fst (hjp.trans hip.symm))
        simp [hj, hne]
      · simp [hj]
  rw [LocalConfiguration.countingMeasure_singleton] at hb
  exact_mod_cast hb

theorem feedbackRerootedPoints_multiplicity_le_one (w : FeedbackCellSequence)
    (u : ℝ) (direction : ℤ) (p : MatchingPoint) :
    LocalConfiguration.multiplicity
      (LocalConfiguration.reroot u (feedbackConcatenatedPoints direction w)) p ≤ 1 := by
  have hb := feedbackConcatenatedPoints_multiplicity_le_one w direction
    ((Configuration.pointTranslation (-u)).symm p)
  have he : LocalConfiguration.multiplicity
      (LocalConfiguration.reroot u (feedbackConcatenatedPoints direction w)) p =
      LocalConfiguration.multiplicity (feedbackConcatenatedPoints direction w)
        ((Configuration.pointTranslation (-u)).symm p) := by
    apply Nat.cast_injective (R := ℝ≥0∞)
    rw [← LocalConfiguration.countingMeasure_singleton,
      ← LocalConfiguration.countingMeasure_singleton, LocalConfiguration.countingMeasure_reroot,
      Measure.map_apply (Configuration.pointTranslation (-u)).measurable (measurableSet_singleton p)]
    congr 1
    ext x
    simp only [mem_preimage, mem_singleton_iff]
    exact (Configuration.pointTranslation (-u)).toEquiv.eq_symm_apply.symm
  rw [he]
  exact hb

private theorem countingMeasure_edges_map_fst {scene : MatchingScene}
    (hp : scene.IsSimplePerfectMatching)
    (hs : ∀ x, LocalConfiguration.multiplicity scene.source x ≤ 1) :
    (LocalConfiguration.countingMeasure scene.edges).map Prod.fst =
      LocalConfiguration.countingMeasure scene.source := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_fst, MatchingScene.lintegral_edges_eq_tsum_source hp,
    LocalConfiguration.lintegral_eq_tsum_atoms]
  apply tsum_congr
  intro x
  have hx : LocalConfiguration.multiplicity scene.source x.val = 1 :=
    Nat.le_antisymm (hs _) (Nat.one_le_iff_ne_zero.mpr x.property)
  simp only [hx, Nat.cast_one, mul_one]

private theorem countingMeasure_edges_map_snd {scene : MatchingScene}
    (hp : scene.IsSimplePerfectMatching)
    (ht : ∀ x, LocalConfiguration.multiplicity scene.target x ≤ 1) :
    (LocalConfiguration.countingMeasure scene.edges).map Prod.snd =
      LocalConfiguration.countingMeasure scene.target := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_snd, MatchingScene.lintegral_edges_eq_tsum_source hp,
    LocalConfiguration.lintegral_eq_tsum_atoms, ← (MatchingScene.atomAssignment hp).tsum_eq]
  apply tsum_congr
  intro x
  have hx : LocalConfiguration.multiplicity scene.target (MatchingScene.atomAssignment hp x).val = 1 :=
    Nat.le_antisymm (ht _) (Nat.one_le_iff_ne_zero.mpr (MatchingScene.atomAssignment hp x).property)
  simp only [hx, Nat.cast_one, mul_one]

private theorem edgeIntensity_projection_of_joining
    (P : Measure MatchingScene) (J : Measure FeedbackSceneRoofPoint)
    (hscene : J.map (fun q ↦ q.2.2.1) = P)
    (π : MatchingPoint × MatchingPoint → MatchingPoint) (hπ : Measurable π)
    (E : MatchingScene → LocalConfiguration matchingPointBase) (hE : Measurable E)
    (hp : ∀ᵐ q ∂J, (LocalConfiguration.countingMeasure q.2.2.1.edges).map π =
      LocalConfiguration.countingMeasure (E q.2.2.1)) :
    (feedbackSceneEdgeIntensity P).map π = P.bind (fun scene ↦ LocalConfiguration.countingMeasure (E scene)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hN : Measurable (fun scene ↦ LocalConfiguration.countingMeasure (E scene)) :=
    LocalConfiguration.measurable_countingMeasure.comp hE
  have hfe : Measurable (fun scene : MatchingScene ↦
      ∫⁻ e, f (π e) ∂LocalConfiguration.countingMeasure scene.edges) :=
    (Measure.measurable_lintegral (hf.comp hπ)).comp measurable_edgeCounting
  have hfN : Measurable (fun scene : MatchingScene ↦
      ∫⁻ x, f x ∂LocalConfiguration.countingMeasure (E scene)) :=
    (Measure.measurable_lintegral hf).comp hN
  rw [lintegral_map hf hπ, feedbackSceneEdgeIntensity,
    Measure.lintegral_bind (f := fun e ↦ f (π e)) measurable_edgeCounting.aemeasurable (hf.comp hπ).aemeasurable,
    Measure.lintegral_bind hN.aemeasurable hf.aemeasurable, ← hscene,
    lintegral_map hfe measurable_snd.snd.fst, lintegral_map hfN measurable_snd.snd.fst]
  apply lintegral_congr_ae
  filter_upwards [hp] with q hq
  rw [← lintegral_map hf hπ, hq]

private theorem endpointIntensity_eq_of_environment {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (P : Measure MatchingScene)
    (henv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (E : FeedbackEnvironment → LocalConfiguration matchingPointBase) (hE : Measurable E) :
    P.bind (fun scene ↦ LocalConfiguration.countingMeasure (E (feedbackSceneEnvironment scene))) =
      (feedbackStationaryEnvironmentLaw lam hlam0 hlam).bind (fun e ↦ LocalConfiguration.countingMeasure (E e)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hN : Measurable (fun e ↦ LocalConfiguration.countingMeasure (E e)) :=
    LocalConfiguration.measurable_countingMeasure.comp hE
  have hNS : Measurable (fun scene ↦ LocalConfiguration.countingMeasure
      (E (feedbackSceneEnvironment scene))) := hN.comp measurable_feedbackSceneEnvironment
  have hfN : Measurable (fun e : FeedbackEnvironment ↦
      ∫⁻ x, f x ∂LocalConfiguration.countingMeasure (E e)) :=
    (Measure.measurable_lintegral hf).comp hN
  rw [Measure.lintegral_bind hNS.aemeasurable hf.aemeasurable,
    Measure.lintegral_bind hN.aemeasurable hf.aemeasurable, ← henv,
    lintegral_map hfN measurable_feedbackSceneEnvironment]

/-- The full mean edge measure has the actual uniform marked intensity at both endpoints. -/
theorem feedbackSceneEdgeIntensity_marginals {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (henv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂P, scene.IsSimplePerfectMatching) :
    (feedbackSceneEdgeIntensity P).map Prod.fst = (volume : Measure ℝ).prod (volume : Measure UnitMark) ∧
    (feedbackSceneEdgeIntensity P).map Prod.snd = (volume : Measure ℝ).prod (volume : Measure UnitMark) := by
  let J := feedbackSceneRoofJoining lam hlam0 hlam P P
  have hscene : J.map (fun q ↦ q.2.2.1) = P :=
    feedbackSceneRoofJoining_scene_left lam hlam0 hlam P P henv
  have hp : ∀ᵐ q ∂J, q.2.2.1.IsSimplePerfectMatching := by
    rw [← hscene] at hperfect
    exact ae_of_ae_map measurable_snd.snd.fst.aemeasurable hperfect
  have he := feedbackSceneRoofJoining_ae_environment lam hlam0 hlam P P henv henv
  constructor
  · have hproj : ∀ᵐ q ∂J, (LocalConfiguration.countingMeasure q.2.2.1.edges).map Prod.fst =
        LocalConfiguration.countingMeasure q.2.2.1.source := by
      filter_upwards [hp, he] with q hp he
      apply countingMeasure_edges_map_fst hp
      intro x
      have hs : q.2.2.1.source = (feedbackRoofEnvironment lam q.2.1).source :=
        congrArg FeedbackEnvironment.source he.1
      rw [hs]
      exact feedbackRerootedPoints_multiplicity_le_one q.2.1.1 q.2.1.2 1 x
    rw [edgeIntensity_projection_of_joining P J hscene Prod.fst measurable_fst
      MatchingScene.source MatchingScene.measurable_source hproj]
    exact (endpointIntensity_eq_of_environment hlam0 hlam P henv FeedbackEnvironment.source
      FeedbackEnvironment.measurable_source).trans (feedbackStationary_source_intensity hlam0 hlam)
  · have hproj : ∀ᵐ q ∂J, (LocalConfiguration.countingMeasure q.2.2.1.edges).map Prod.snd =
        LocalConfiguration.countingMeasure q.2.2.1.target := by
      filter_upwards [hp, he] with q hp he
      apply countingMeasure_edges_map_snd hp
      intro x
      have ht : q.2.2.1.target = (feedbackRoofEnvironment lam q.2.1).target :=
        congrArg FeedbackEnvironment.target he.1
      rw [ht]
      exact feedbackRerootedPoints_multiplicity_le_one q.2.1.1 q.2.1.2 (-1) x
    rw [edgeIntensity_projection_of_joining P J hscene Prod.snd measurable_snd
      MatchingScene.target MatchingScene.measurable_target hproj]
    exact (endpointIntensity_eq_of_environment hlam0 hlam P henv FeedbackEnvironment.target
      FeedbackEnvironment.measurable_target).trans (feedbackStationary_target_intensity hlam0 hlam)

/-- Stationarity of the scene law transports the actual mean edge measure diagonally. -/
theorem measurePreserving_feedbackSceneEdgeIntensity (P : Measure MatchingScene)
    (hstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P) (t : ℝ) :
    MeasurePreserving (MatchingScene.edgeReroot t) (feedbackSceneEdgeIntensity P)
      (feedbackSceneEdgeIntensity P) := by
  apply measurePreserving_bind_of_covariant P _ measurable_edgeCounting (hstat t)
    (MatchingScene.edgeReroot t).measurable
  exact ae_of_all _ fun scene ↦ LocalConfiguration.countingMeasure_mapHomeomorph _ scene.edges

/-- The source mark marginal of the actual unit-source Palm measure is uniform. -/
theorem feedbackProjectiveLaw_source {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (henv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂P, scene.IsSimplePerfectMatching) :
    (feedbackProjectiveLaw P).map Prod.fst = (volume : Measure UnitMark) := by
  have hs := (feedbackSceneEdgeIntensity_marginals hlam0 hlam P henv hperfect).1
  ext B hB
  rw [feedbackProjectiveLaw, Measure.map_map measurable_fst (measurable_fst.snd.prodMk measurable_snd.snd)]
  simp only [Function.comp_def]
  rw [Measure.map_apply measurable_fst.snd hB, Measure.restrict_apply (measurable_fst.snd hB)]
  have hset : (fun e : MatchingPoint × MatchingPoint ↦ e.1.2) ⁻¹' B ∩
      {e | e.1.1 ∈ Ioc (0 : ℝ) 1} = Prod.fst ⁻¹' (Ioc (0 : ℝ) 1 ×ˢ B) := by
    ext e
    exact and_comm
  rw [hset, ← Measure.map_apply measurable_fst (measurableSet_Ioc.prod hB), hs, Measure.prod_prod]
  simp

/-- Target marks retain their true uniform intensity after moving the observation window from
source to target by stationary mass transport. -/
theorem feedbackProjectiveLaw_target {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (henv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂P, scene.IsSimplePerfectMatching)
    (hstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P) :
    (feedbackProjectiveLaw P).map Prod.snd = (volume : Measure UnitMark) := by
  obtain ⟨hsource, htarget⟩ := feedbackSceneEdgeIntensity_marginals hlam0 hlam P henv hperfect
  ext B hB
  let E := feedbackSceneEdgeIntensity P
  let MB : Set (MatchingPoint × MatchingPoint) := {e | e.2.2 ∈ B}
  have hMB : MeasurableSet MB := measurable_snd.snd hB
  let pos : MatchingPoint × MatchingPoint → ℝ × ℝ := fun e ↦ (e.1.1, e.2.1)
  have hpos : Measurable pos := measurable_fst.fst.prodMk measurable_snd.fst
  let T := (E.restrict MB).map pos
  have hout : T (Ioc (0 : ℝ) 1 ×ˢ univ) =
      E {e | e.1.1 ∈ Ioc (0 : ℝ) 1 ∧ e.2.2 ∈ B} := by
    rw [Measure.map_apply hpos (measurableSet_Ioc.prod MeasurableSet.univ),
      Measure.restrict_apply (hpos (measurableSet_Ioc.prod MeasurableSet.univ))]
    congr 1
    ext e
    simp only [pos, MB, mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true, mem_ofPred_eq]
  have hin : T (univ ×ˢ Ioc (0 : ℝ) 1) = (volume : Measure UnitMark) B := by
    rw [Measure.map_apply hpos (MeasurableSet.univ.prod measurableSet_Ioc),
      Measure.restrict_apply (hpos (MeasurableSet.univ.prod measurableSet_Ioc))]
    have heq : pos ⁻¹' (univ ×ˢ Ioc (0 : ℝ) 1) ∩ MB =
        Prod.snd ⁻¹' (Ioc (0 : ℝ) 1 ×ˢ B) := by
      ext e
      simp only [pos, MB, mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_ofPred_eq]
    rw [heq, ← Measure.map_apply measurable_snd (measurableSet_Ioc.prod hB),
      htarget, Measure.prod_prod]
    simp
  have hfinite : T (Ioc (0 : ℝ) 1 ×ˢ univ) < ∞ := by
    rw [hout]
    apply lt_of_le_of_lt (measure_mono (show
      {e : MatchingPoint × MatchingPoint | e.1.1 ∈ Ioc (0 : ℝ) 1 ∧ e.2.2 ∈ B} ⊆
      Prod.fst ⁻¹' (Ioc (0 : ℝ) 1 ×ˢ univ) from fun _ he ↦ ⟨he.1, mem_univ _⟩))
    rw [← Measure.map_apply measurable_fst (measurableSet_Ioc.prod MeasurableSet.univ),
      hsource, Measure.prod_prod]
    simp
  have hT (a : ℝ) : MeasurePreserving (fun z : ℝ × ℝ ↦ (a + z.1, a + z.2)) T T := by
    have hr : MeasurePreserving (MatchingScene.edgeReroot (-a)) (E.restrict MB) (E.restrict MB) :=
      (measurePreserving_feedbackSceneEdgeIntensity P hstat (-a)).restrict_preimage hMB
    apply (hpos.measurePreserving (E.restrict MB)).of_semiconj hr
    · intro e
      ext <;> simp [pos, MatchingScene.edgeReroot_apply, add_comm]
    · exact (measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd)
  have hm := stationary_mass_transport T hT hfinite
  rw [feedbackProjectiveLaw, Measure.map_map measurable_snd (measurable_fst.snd.prodMk measurable_snd.snd)]
  simp only [Function.comp_def]
  rw [Measure.map_apply measurable_snd.snd hB, Measure.restrict_apply (measurable_snd.snd hB)]
  have heq : (fun e : MatchingPoint × MatchingPoint ↦ e.2.2) ⁻¹' B ∩
      {e | e.1.1 ∈ Ioc (0 : ℝ) 1} = {e | e.1.1 ∈ Ioc (0 : ℝ) 1 ∧ e.2.2 ∈ B} := by
    ext e
    exact and_comm
  rw [heq, ← hout, ← hm, hin]

/-- The actual source Palm mark-pair measure is normalized, without an extra renormalization. -/
theorem feedbackProjectiveLaw_isProbability {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (henv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hperfect : ∀ᵐ scene ∂P, scene.IsSimplePerfectMatching) :
    IsProbabilityMeasure (feedbackProjectiveLaw P) := by
  constructor
  have h := congrArg (fun μ : Measure UnitMark ↦ μ univ)
    (feedbackProjectiveLaw_source hlam0 hlam P henv hperfect)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, measure_univ] using h

/-- Uniqueness of admissible actual stationary scenes determines the same projective Palm
coupling, with no change to its unit-source observation rule. -/
theorem feedbackProjectiveLaws_unique {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hlam8 : lam < 1 / 8)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPenv : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQenv : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hPstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) P P)
    (hQstat : ∀ t : ℝ, MeasurePreserving (MatchingScene.reroot t) Q Q)
    (hcandidate : ∀ k : Fin 2, ∀ᵐ scene ∂(![P, Q] k), FeedbackSceneEnergyCandidate lam scene)
    (hroot : ∀ k : Fin 2,
      (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂(![P, Q] k)) < ∞) :
    feedbackProjectiveLaw P = feedbackProjectiveLaw Q :=
  congrArg feedbackProjectiveLaw
    (feedbackSceneLaws_unique hlam0 hlam hlam8 P Q hPenv hQenv hPstat hQstat hcandidate hroot).1

end OTSelector.Matching
