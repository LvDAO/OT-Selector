import OTSelector.Matching.FeedbackSceneJoiningEnergy
import OTSelector.PointProcess.MatchingSceneTransportCrossingEnergy

/-!
# From the stationary root crossing moment to window energy

The observable is defined on every scene by its actual edge counting measure. Its measurability
and translation covariance are unconditional. On perfect scenes with finite crossings it agrees
with the spatial matching energy. Fubini and stationarity transport a root moment to every window.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

/-- The nonnegative contribution of an actual edge to crossing energy at a cut. -/
noncomputable def feedbackSceneEdgeEnergy (x : ℝ) (e : MatchingPoint × MatchingPoint) : ℝ :=
  |(crossingSign e.1.1 e.2.1 x : ℝ)| * (1 + |e.2.1 - e.1.1|)

@[fun_prop]
theorem measurable_feedbackSceneEdgeEnergy :
    Measurable (fun p : ℝ × (MatchingPoint × MatchingPoint) ↦
      feedbackSceneEdgeEnergy p.1 p.2) := by
  have hs : Measurable (fun p : ℝ × (MatchingPoint × MatchingPoint) ↦
      if p.2.1.1 ≤ p.1 then (1 : ℤ) else 0) :=
    measurable_const.ite (measurableSet_le measurable_snd.fst.fst measurable_fst) measurable_const
  have ht : Measurable (fun p : ℝ × (MatchingPoint × MatchingPoint) ↦
      if p.2.2.1 ≤ p.1 then (1 : ℤ) else 0) :=
    measurable_const.ite (measurableSet_le measurable_snd.snd.fst measurable_fst) measurable_const
  have hc : Measurable (fun z : ℤ ↦ (z : ℝ)) := measurable_of_countable _
  exact ((hc.comp (hs.sub ht)).abs).mul
    (measurable_const.add (measurable_snd.snd.fst.sub measurable_snd.fst.fst).abs)

/-- A total measurable crossing energy read directly from the scene's edge configuration. -/
noncomputable def feedbackSceneCrossingEnergy (scene : MatchingScene) (x : ℝ) : ℝ :=
  (MatchingScene.crossingEnergyMoment scene x).toReal

@[fun_prop]
theorem measurable_feedbackSceneCrossingMoment :
    Measurable (fun p : MatchingScene × ℝ ↦ MatchingScene.crossingEnergyMoment p.1 p.2) := by
  let K : Kernel (MatchingScene × ℝ) (MatchingPoint × MatchingPoint) :=
    LocalConfiguration.countingKernel.comap (fun p ↦ p.1.edges)
      (MatchingScene.measurable_edges.comp measurable_fst)
  have hf : Measurable (fun q : (MatchingScene × ℝ) × (MatchingPoint × MatchingPoint) ↦
      ENNReal.ofReal (feedbackSceneEdgeEnergy q.1.2 q.2)) :=
    (measurable_feedbackSceneEdgeEnergy.comp (measurable_fst.snd.prodMk measurable_snd)).ennreal_ofReal
  exact hf.lintegral_kernel_prod_right' (κ := K)

@[fun_prop]
theorem measurable_feedbackSceneCrossingEnergy :
    Measurable (fun p : MatchingScene × ℝ ↦ feedbackSceneCrossingEnergy p.1 p.2) :=
  measurable_feedbackSceneCrossingMoment.ennreal_toReal

/-- Crossing energy is nonnegative even on scenes outside the eventual perfect support. -/
theorem feedbackSceneCrossingEnergy_nonneg (scene : MatchingScene) (x : ℝ) :
    0 ≤ feedbackSceneCrossingEnergy scene x := ENNReal.toReal_nonneg

/-- Actual edge energy translates with the cut. -/
theorem feedbackSceneEdgeEnergy_reroot (a x : ℝ) (e : MatchingPoint × MatchingPoint) :
    feedbackSceneEdgeEnergy x (MatchingScene.edgeReroot a e) =
      feedbackSceneEdgeEnergy (x + a) e := by
  unfold feedbackSceneEdgeEnergy crossingSign
  simp only [MatchingScene.edgeReroot_apply, sub_le_iff_le_add]
  rw [show e.2.1 - a - (e.1.1 - a) = e.2.1 - e.1.1 by ring]

/-- Actual counting energy is covariant under scene rerooting. -/
theorem feedbackSceneCrossingEnergy_reroot (a : ℝ) (scene : MatchingScene) (x : ℝ) :
    feedbackSceneCrossingEnergy (MatchingScene.reroot a scene) x =
      feedbackSceneCrossingEnergy scene (x + a) := by
  unfold feedbackSceneCrossingEnergy MatchingScene.crossingEnergyMoment
  change (∫⁻ e, ENNReal.ofReal (feedbackSceneEdgeEnergy x e)
    ∂LocalConfiguration.countingMeasure
      (LocalConfiguration.mapHomeomorph (MatchingScene.edgeReroot a) scene.edges)).toReal = _
  have hf : Measurable (fun e ↦ ENNReal.ofReal (feedbackSceneEdgeEnergy x e)) :=
    (measurable_feedbackSceneEdgeEnergy.comp
      (f := fun e : MatchingPoint × MatchingPoint ↦ (x, e))
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [LocalConfiguration.countingMeasure_mapHomeomorph,
    lintegral_map hf (MatchingScene.edgeReroot a).measurable]
  simp only [feedbackSceneEdgeEnergy_reroot]
  rfl

/-- Finite actual crossings make the measurable counting observable the original matching sum. -/
theorem feedbackSceneCrossingEnergy_eq {scene : MatchingScene}
    (hp : scene.IsSimplePerfectMatching)
    (hfinite : ∀ x, {i : MatchingScene.SourceAtom scene |
      Crosses x i.val.1 (MatchingScene.atomAssignment hp i).val.1}.Finite) (x : ℝ) :
    feedbackSceneCrossingEnergy scene x = (MatchingScene.spatialMatching hp).crossingEnergy x := by
  let M := MatchingScene.spatialMatching hp
  have hloc : M.LocallyFinite :=
    ⟨MatchingScene.finite_sourceAtoms_window scene, MatchingScene.finite_targetAtoms_window scene⟩
  have hrows := M.finite_edgesMeeting hloc (x - 1) (x + 1)
    (hfinite (x - 1)) (hfinite (x + 1))
  have hsupport : (support (fun i : MatchingScene.SourceAtom scene ↦
      crossingSign i.val.1 (MatchingScene.atomAssignment hp i).val.1 x)).Finite := by
    apply hrows.subset
    intro i hi
    by_contra hn
    have hz : crossingSign i.val.1 (MatchingScene.atomAssignment hp i).val.1 x = 0 := by
      by_cases hs : i.val.1 ≤ x <;>
        by_cases ht : (MatchingScene.atomAssignment hp i).val.1 ≤ x
      · simp [crossingSign, hs, ht]
      · exact False.elim (hn ⟨Or.inl (by change i.val.1 < x + 1; linarith),
          Or.inr (by change x - 1 < (MatchingScene.atomAssignment hp i).val.1; linarith)⟩)
      · exact False.elim (hn ⟨Or.inr (by change (MatchingScene.atomAssignment hp i).val.1 < x + 1; linarith),
          Or.inl (by change x - 1 < i.val.1; linarith)⟩)
      · simp [crossingSign, hs, ht]
    exact hi hz
  rw [feedbackSceneCrossingEnergy, MatchingScene.crossingEnergyMoment_eq_spatialMatching hp x hsupport,
    ENNReal.toReal_ofReal ((MatchingScene.spatialMatching hp).crossingEnergy_nonneg x)]

/-- Stationarity turns an integrable root energy into the same finite moment at every cut. -/
theorem feedbackSceneCrossingEnergy_cut_moment (P : Measure MatchingScene)
    (hstationary : ∀ x, MeasurePreserving (MatchingScene.reroot x) P P)
    (hroot : Integrable (fun scene ↦ feedbackSceneCrossingEnergy scene 0) P) (x : ℝ) :
    Integrable (fun scene ↦ feedbackSceneCrossingEnergy scene x) P ∧
      (∫ scene, feedbackSceneCrossingEnergy scene x ∂P) =
        ∫ scene, feedbackSceneCrossingEnergy scene 0 ∂P := by
  have he : (fun scene ↦ feedbackSceneCrossingEnergy scene x) =
      (fun scene ↦ feedbackSceneCrossingEnergy (MatchingScene.reroot x scene) 0) := by
    funext scene
    rw [feedbackSceneCrossingEnergy_reroot, zero_add]
  rw [he]
  refine ⟨(hstationary x).integrable_comp_of_integrable hroot, ?_⟩
  exact (hstationary x).integral_comp (MatchingScene.rerootMeasurableEquiv x).measurableEmbedding
    (fun scene ↦ feedbackSceneCrossingEnergy scene 0)

/-- Every rooted window has an integrable energy and mean equal to its length times the root mean. -/
theorem feedbackSceneWindowEnergy_moment (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (hstationary : ∀ x, MeasurePreserving (MatchingScene.reroot x) P P)
    (hgood : ∀ᵐ scene ∂P, ∃ hp : scene.IsSimplePerfectMatching,
      ∀ x, {i : MatchingScene.SourceAtom scene |
        Crosses x i.val.1 (MatchingScene.atomAssignment hp i).val.1}.Finite)
    (hroot : Integrable (fun scene ↦ feedbackSceneCrossingEnergy scene 0) P)
    (h L : ℝ) (hL : 0 ≤ L) :
    Integrable (fun scene ↦ feedbackSceneWindowEnergy scene h L) P ∧
      (∫ scene, feedbackSceneWindowEnergy scene h L ∂P) =
        L * ∫ scene, feedbackSceneCrossingEnergy scene 0 ∂P := by
  let I := Icc (h / 2 - L / 2) (h / 2 + L / 2)
  let V : Measure ℝ := volume.restrict I
  let F (q : ℝ × MatchingScene) := feedbackSceneCrossingEnergy q.2 q.1
  have hF : Measurable F := measurable_feedbackSceneCrossingEnergy.comp
    (f := fun q : ℝ × MatchingScene ↦ (q.2, q.1)) measurable_swap
  let : IsFiniteMeasure V := ⟨by simp [V, I]⟩
  have hcuts := feedbackSceneCrossingEnergy_cut_moment P hstationary hroot
  have hFnorm : (fun x ↦ ∫ scene, ‖F (x, scene)‖ ∂P) =
      (fun _ ↦ ∫ scene, feedbackSceneCrossingEnergy scene 0 ∂P) := by
    funext x
    simp only [F, Real.norm_eq_abs, abs_of_nonneg (feedbackSceneCrossingEnergy_nonneg _ _)]
    exact (hcuts x).2
  have hFI : Integrable F (V.prod P) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ fun x ↦ (hcuts x).1, ?_⟩
    rw [hFnorm]
    exact integrable_const _
  have heq : (fun scene ↦ feedbackSceneWindowEnergy scene h L) =ᵐ[P]
      (fun scene ↦ ∫ x, F (x, scene) ∂V) := by
    filter_upwards [hgood] with scene ⟨hp, hf⟩
    rw [feedbackSceneWindowEnergy_of_perfect _ hp]
    exact integral_congr_ae (ae_of_all _ fun x ↦ (feedbackSceneCrossingEnergy_eq hp hf x).symm)
  refine ⟨hFI.integral_prod_right.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, ← integral_integral_swap hFI]
  simp_rw [show ∀ x scene, F (x, scene) = feedbackSceneCrossingEnergy scene x from fun _ _ ↦ rfl,
    fun x ↦ (hcuts x).2]
  rw [integral_const]
  have hvol : V.real univ = L := by
    simp only [V, Measure.real, Measure.restrict_apply_univ, I, Real.volume_Icc]
    rw [show h / 2 + L / 2 - (h / 2 - L / 2) = L by ring, ENNReal.toReal_ofReal hL]
  rw [hvol, smul_eq_mul]

/-- The proved actual root counting-moment bound supplies the unconditional linear window mean. -/
theorem feedbackSceneWindowEnergy_moment_le (P : Measure MatchingScene) [IsProbabilityMeasure P]
    (hstationary : ∀ x, MeasurePreserving (MatchingScene.reroot x) P P)
    (hgood : ∀ᵐ scene ∂P, ∃ hp : scene.IsSimplePerfectMatching,
      ∀ x, {i : MatchingScene.SourceAtom scene |
        Crosses x i.val.1 (MatchingScene.atomAssignment hp i).val.1}.Finite)
    {C : ℝ} (hC : 0 ≤ C)
    (hroot : (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂P) ≤ ENNReal.ofReal C)
    (h L : ℝ) (hL : 0 ≤ L) :
    Integrable (fun scene ↦ feedbackSceneWindowEnergy scene h L) P ∧
      (∫ scene, feedbackSceneWindowEnergy scene h L ∂P) ≤ C * L := by
  have hm : Measurable (fun scene ↦ MatchingScene.crossingEnergyMoment scene 0) :=
    measurable_feedbackSceneCrossingMoment.comp
      (f := fun scene : MatchingScene ↦ (scene, (0 : ℝ)))
      (measurable_id.prodMk measurable_const)
  have hfin := hroot.trans_lt ENNReal.ofReal_lt_top
  have hi : Integrable (fun scene ↦ feedbackSceneCrossingEnergy scene 0) P :=
    integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin.ne
  have hb : (∫ scene, feedbackSceneCrossingEnergy scene 0 ∂P) ≤ C := by
    change (∫ scene, (MatchingScene.crossingEnergyMoment scene 0).toReal ∂P) ≤ C
    rw [integral_toReal hm.aemeasurable (ae_lt_top hm hfin.ne)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hroot).trans_eq (ENNReal.toReal_ofReal hC)
  obtain ⟨hI, hmean⟩ := feedbackSceneWindowEnergy_moment P hstationary hgood hi h L hL
  exact ⟨hI, hmean.trans_le ((mul_le_mul_of_nonneg_left hb hL).trans_eq (mul_comm L C))⟩

/-- The actual root moment, stationary scene law, and geometric candidate properties imply a
positive common empty cut under the actual roof joining. The entire conditional energy bootstrap
and its window-moment inputs have been discharged by the preceding results. -/
theorem exists_feedbackSceneRoofJoining_commonEmptyCut_of_rootMoment
    {lam : ℝ} {hlam0 : 0 < lam} {hlam : lam < 1 / 2} (hlam8 : lam < 1 / 8)
    (regularity : FeedbackConditionalRegularityParameters lam hlam0 hlam)
    (P Q : Measure MatchingScene) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hQ : Q.map feedbackSceneEnvironment = feedbackStationaryEnvironmentLaw lam hlam0 hlam)
    (hcandidate : ∀ k : Fin 2, ∀ᵐ scene ∂(![P, Q] k), FeedbackSceneEnergyCandidate lam scene)
    (hstationary : ∀ k : Fin 2, ∀ x,
      MeasurePreserving (MatchingScene.reroot x) (![P, Q] k) (![P, Q] k))
    (C : Fin 2 → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hroot : ∀ k, (∫⁻ scene, MatchingScene.crossingEnergyMoment scene 0 ∂(![P, Q] k)) ≤
      ENNReal.ofReal (C k)) :
    ∃ h > 0, 0 < (ProbabilityTheory.cond (feedbackSceneRoofJoining lam hlam0 hlam P Q)
      {q | q.2.1 ∈ feedbackRoofHoldBand lam h}).real
      {q | feedbackSceneCommonEmptyCut q (h / 2)} := by
  have hmoment (k : Fin 2) (h R : ℝ) (hR : 0 < R) :
      Integrable (fun scene ↦ feedbackSceneWindowEnergy scene h R) (![P, Q] k) ∧
        (∫ scene, feedbackSceneWindowEnergy scene h R ∂(![P, Q] k)) ≤ C k * R := by
    let : IsProbabilityMeasure (![P, Q] k) := by
      fin_cases k
      · exact (inferInstance : IsProbabilityMeasure P)
      · exact (inferInstance : IsProbabilityMeasure Q)
    exact feedbackSceneWindowEnergy_moment_le (![P, Q] k) (hstationary k)
      ((hcandidate k).mono fun _ hc ↦ ⟨hc.perfect, hc.finite_crossings⟩)
      (hC k) (hroot k) h R hR.le
  exact exists_feedbackSceneRoofJoining_commonEmptyCut hlam8 regularity P Q hP hQ
    hcandidate C (fun k h R hR ↦ (hmoment k h R hR).1)
      (fun k h R hR ↦ (hmoment k h R hR).2)

end OTSelector.Matching
