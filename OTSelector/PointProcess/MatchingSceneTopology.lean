import OTSelector.PointProcess.FiniteMatchingSceneMeasurable
import OTSelector.PointProcess.LocalConfigurationCompactness
import OTSelector.PointProcess.LocalConfigurationBorel

/-!
# Product vague topology for actual matching scenes

Source, target, and edge configurations carry their proved vague topologies.  The path carries
compact-open graph-height convergence and discrete root current.  This topology has exactly the
previously constructed scene sigma algebra; no Polish-space assumption is imposed on it.
-/

open MeasureTheory Set Function Filter Topology
open scoped Classical NNReal
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance : TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase
noncomputable local instance : TopologicalSpace
    (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueTopology (matchingPointBase, matchingPointBase)

local instance : BorelSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueBorelSpace
local instance : BorelSpace (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueBorelSpace
local instance : T2Space (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueT2Space
local instance : T2Space (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueT2Space

/-- Three genuine vague configuration coordinates and the existing path topology. -/
noncomputable instance instTopologicalSpace : TopologicalSpace MatchingScene :=
  TopologicalSpace.induced equivCoordinates inferInstance

/-- Coordinate assembly is a homeomorphism for the actual product topology. -/
noncomputable def coordinatesHomeomorph : MatchingScene ≃ₜ Coordinates where
  toEquiv := equivCoordinates
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    simpa using (continuous_id : Continuous (id : Coordinates → Coordinates))

section LabeledBorel

local instance {X : Type*} [MetricSpace X] (base : X) (n : ℕ) :
    TopologicalSpace (FinitePointCloud (LocalConfiguration.Shell base n)) :=
  FinitePointCloud.cloudTopology _
local instance {X : Type*} [MetricSpace X] [SecondCountableTopology X] (base : X) (n : ℕ) :
    SecondCountableTopology (FinitePointCloud (LocalConfiguration.Shell base n)) :=
  FinitePointCloud.cloudSecondCountableTopology
local instance {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (base : X) (n : ℕ) :
    BorelSpace (FinitePointCloud (LocalConfiguration.Shell base n)) :=
  FinitePointCloud.cloudBorelSpace

private abbrev LabeledCoordinates := LocalConfiguration.LabeledShellClouds matchingPointBase ×
  LocalConfiguration.LabeledShellClouds matchingPointBase ×
  LocalConfiguration.LabeledShellClouds (matchingPointBase, matchingPointBase) × FeedbackPath

private def forgetCoordinates (p : LabeledCoordinates) : Coordinates :=
  (LocalConfiguration.forgetLabels p.1, LocalConfiguration.forgetLabels p.2.1,
    LocalConfiguration.forgetLabels p.2.2.1, p.2.2.2)

private noncomputable def chooseCoordinates (p : Coordinates) : LabeledCoordinates :=
  (LocalConfiguration.chooseLabels p.1, LocalConfiguration.chooseLabels p.2.1,
    LocalConfiguration.chooseLabels p.2.2.1, p.2.2.2)

private theorem continuous_forgetCoordinates : Continuous forgetCoordinates :=
  (LocalConfiguration.continuous_forgetLabels.comp continuous_fst).prodMk <|
    (LocalConfiguration.continuous_forgetLabels.comp (continuous_fst.comp continuous_snd)).prodMk <|
      (LocalConfiguration.continuous_forgetLabels.comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
          (continuous_snd.comp (continuous_snd.comp continuous_snd))

private theorem measurable_chooseCoordinates : Measurable chooseCoordinates :=
  (LocalConfiguration.measurable_chooseLabels.comp measurable_fst).prodMk <|
    (LocalConfiguration.measurable_chooseLabels.comp (measurable_fst.comp measurable_snd)).prodMk <|
      (LocalConfiguration.measurable_chooseLabels.comp
        (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd))

/-- Finite products retain Borel compatibility through the continuous labeled-cloud presentation;
this does not assume that the full configuration topology is second countable. -/
private theorem coordinatesBorelSpace : BorelSpace Coordinates := by
  constructor
  apply le_antisymm
  · have h : @Measurable Coordinates Coordinates (borel Coordinates) inferInstance id := by
      let : MeasurableSpace Coordinates := borel Coordinates
      let : BorelSpace Coordinates := ⟨rfl⟩
      exact continuous_fst.measurable.prodMk <|
        (continuous_fst.comp continuous_snd).measurable.prodMk <|
          (continuous_fst.comp (continuous_snd.comp continuous_snd)).measurable.prodMk
            (continuous_snd.comp (continuous_snd.comp continuous_snd)).measurable
    exact h
  · have hforget : @Measurable LabeledCoordinates Coordinates inferInstance
        (borel Coordinates) forgetCoordinates := by
      let : MeasurableSpace Coordinates := borel Coordinates
      let : BorelSpace Coordinates := ⟨rfl⟩
      exact continuous_forgetCoordinates.measurable
    have h := hforget.comp measurable_chooseCoordinates
    have hid : forgetCoordinates ∘ chooseCoordinates = id := by
      funext p
      simp [forgetCoordinates, chooseCoordinates]
    rw [hid] at h
    exact h

end LabeledBorel

private instance : BorelSpace Coordinates := coordinatesBorelSpace

/-- The physical product topology has exactly the already established scene Borel structure. -/
instance instBorelSpace : BorelSpace MatchingScene := by
  constructor
  change MeasurableSpace.comap equivCoordinates inferInstance =
    @borel MatchingScene (TopologicalSpace.induced equivCoordinates inferInstance)
  rw [borel_comap, ← BorelSpace.measurable_eq]

instance instT2Space : T2Space MatchingScene :=
  coordinatesHomeomorph.isEmbedding.t2Space

@[fun_prop]
theorem continuous_source : Continuous (source : MatchingScene → _) :=
  continuous_fst.comp coordinatesHomeomorph.continuous

@[fun_prop]
theorem continuous_target : Continuous (target : MatchingScene → _) :=
  (continuous_fst.comp continuous_snd).comp coordinatesHomeomorph.continuous

@[fun_prop]
theorem continuous_edges : Continuous (edges : MatchingScene → _) :=
  (continuous_fst.comp (continuous_snd.comp continuous_snd)).comp coordinatesHomeomorph.continuous

@[fun_prop]
theorem continuous_path : Continuous (path : MatchingScene → _) :=
  (continuous_snd.comp (continuous_snd.comp continuous_snd)).comp coordinatesHomeomorph.continuous

@[fun_prop]
theorem continuous_graphHeight : Continuous (fun scene : MatchingScene ↦ scene.path.graphHeight) :=
  FeedbackPath.continuous_graphHeight.comp continuous_path

@[fun_prop]
theorem continuous_rootCurrent : Continuous (fun scene : MatchingScene ↦ scene.path.rootCurrent) :=
  FeedbackPath.continuous_rootCurrent.comp continuous_path

/-- Moving endpoint evaluations converge under the actual scene topology. -/
theorem tendsto_graphHeight_apply {ι : Type*} {l : Filter ι}
    {scene : ι → MatchingScene} {limit : MatchingScene} {x : ι → ℝ} {y : ℝ}
    (hscene : Tendsto scene l (𝓝 limit)) (hx : Tendsto x l (𝓝 y)) :
    Tendsto (fun i ↦ (scene i).path.graphHeight (x i)) l (𝓝 (limit.path.graphHeight y)) :=
  (continuous_eval.tendsto (limit.path.graphHeight, y)).comp
    ((continuous_graphHeight.tendsto limit).comp hscene |>.prodMk_nhds hx)

/-- Compact containment can be assembled coordinate by coordinate without a stronger topology. -/
theorem isCompact_coordinates_preimage
    {Ks Kt : Set (LocalConfiguration matchingPointBase)}
    {Ke : Set (LocalConfiguration (matchingPointBase, matchingPointBase))}
    {Kp : Set FeedbackPath}
    (hs : IsCompact Ks) (ht : IsCompact Kt) (he : IsCompact Ke) (hp : IsCompact Kp) :
    IsCompact {scene : MatchingScene | scene.source ∈ Ks ∧ scene.target ∈ Kt ∧
      scene.edges ∈ Ke ∧ scene.path ∈ Kp} := by
  exact coordinatesHomeomorph.isCompact_preimage.mpr (hs.prod (ht.prod (he.prod hp)))

/-- Shell count bounds, a graph Lipschitz bound, and a bounded root current give an actual compact
set of matching scenes.  The shell condition is only used for containment, not as a topology. -/
theorem exists_isCompact_superset_of_bounds (Ns Nt Ne : ℕ → ℕ) (L : ℝ≥0) (J : ℕ) :
    ∃ K : Set MatchingScene, IsCompact K ∧
      {scene : MatchingScene | (∀ k, (scene.source k).card ≤ Ns k) ∧
        (∀ k, (scene.target k).card ≤ Nt k) ∧ (∀ k, (scene.edges k).card ≤ Ne k) ∧
        LipschitzWith L scene.path.graphHeight ∧ |scene.path.rootCurrent| ≤ J} ⊆ K := by
  obtain ⟨Ks, hs, hKs⟩ := LocalConfiguration.exists_isCompact_superset_shellCard_le
    (base := matchingPointBase) Ns
  obtain ⟨Kt, ht, hKt⟩ := LocalConfiguration.exists_isCompact_superset_shellCard_le
    (base := matchingPointBase) Nt
  obtain ⟨Ke, he, hKe⟩ := LocalConfiguration.exists_isCompact_superset_shellCard_le
    (base := (matchingPointBase, matchingPointBase)) Ne
  let Kp : Set FeedbackPath := FeedbackPath.coordinates ⁻¹'
    (GraphHeight.lipschitzSet L ×ˢ Icc (-(J : ℤ)) J)
  have hp : IsCompact Kp :=
    FeedbackPath.isClosedEmbedding_coordinates.isCompact_preimage
      ((GraphHeight.isCompact_lipschitzSet L).prod (Set.finite_Icc _ _).isCompact)
  refine ⟨{scene | scene.source ∈ Ks ∧ scene.target ∈ Kt ∧ scene.edges ∈ Ke ∧ scene.path ∈ Kp},
    isCompact_coordinates_preimage hs ht he hp, ?_⟩
  intro scene hscene
  exact ⟨hKs hscene.1, hKt hscene.2.1, hKe hscene.2.2.1,
    hscene.2.2.2.1, abs_le.mp hscene.2.2.2.2⟩

end OTSelector.PointProcess.MatchingScene
