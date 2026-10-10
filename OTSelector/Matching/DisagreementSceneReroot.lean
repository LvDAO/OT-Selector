import OTSelector.PointProcess.MatchingScenePerfect
import OTSelector.Matching.DisagreementMassTransport

/-!
# Actual scene partners under rerooting

Translation acts on source atoms, target atoms, and actual edge atoms. The unique
partner read from a simple perfect matching therefore commutes with this action.
Jointly measurable singleton counts supply the edge-relation interface for fixed
raw event labels.
-/

open Function Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess

namespace LocalConfiguration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [StandardBorelSpace X] {base : X}

/-- Singleton counts remain measurable when both the configuration and tested point move. -/
theorem measurable_countingMeasure_singleton :
    Measurable (fun z : LocalConfiguration base × X ↦ countingMeasure z.1 {z.2}) := by
  let K : Kernel (LocalConfiguration base × X) X := countingKernel.comap Prod.fst measurable_fst
  have hEq : MeasurableSet {z : (LocalConfiguration base × X) × X | z.2 = z.1.2} :=
    measurableSet_eq_fun measurable_snd (measurable_snd.comp measurable_fst)
  have hone : Measurable (fun _ : (LocalConfiguration base × X) × X ↦ (1 : ℝ≥0∞)) := measurable_const
  have hmeas := (hone.indicator hEq).lintegral_kernel_prod_right' (κ := K)
  convert hmeas using 1
  funext z
  change countingMeasure z.1 {z.2} =
    ∫⁻ y, {w : (LocalConfiguration base × X) × X | w.2 = w.1.2}.indicator
      (fun _ ↦ (1 : ℝ≥0∞)) (z, y) ∂countingMeasure z.1
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  change countingMeasure z.1 {z.2} = ∫⁻ y, ({z.2} : Set X).indicator 1 y ∂countingMeasure z.1
  exact (lintegral_indicator_one (measurableSet_singleton _)).symm

/-- Actual atom membership is jointly measurable, with multiplicities retained. -/
theorem measurableSet_atom :
    MeasurableSet {z : LocalConfiguration base × X | multiplicity z.1 z.2 ≠ 0} := by
  have h := (measurable_countingMeasure_singleton (base := base)) (measurableSet_singleton 0).compl
  convert h using 1
  ext z
  simp

end LocalConfiguration

namespace MatchingScene

@[simp]
theorem source_multiplicity_reroot (scene : MatchingScene) (a : ℝ) (x : MatchingPoint) :
    LocalConfiguration.multiplicity (scene.reroot a).source (x.1 - a, x.2) =
      LocalConfiguration.multiplicity scene.source x := by
  simp only [reroot, LocalConfiguration.reroot, LocalConfiguration.multiplicity_translate,
    sub_neg_eq_add, sub_add_cancel, Prod.eta]

@[simp]
theorem target_multiplicity_reroot (scene : MatchingScene) (a : ℝ) (x : MatchingPoint) :
    LocalConfiguration.multiplicity (scene.reroot a).target (x.1 - a, x.2) =
      LocalConfiguration.multiplicity scene.target x := by
  simp only [reroot, LocalConfiguration.reroot, LocalConfiguration.multiplicity_translate,
    sub_neg_eq_add, sub_add_cancel, Prod.eta]

@[simp]
theorem edge_multiplicity_reroot (scene : MatchingScene) (a : ℝ) (x y : MatchingPoint) :
    LocalConfiguration.multiplicity (scene.reroot a).edges ((x.1 - a, x.2), (y.1 - a, y.2)) =
      LocalConfiguration.multiplicity scene.edges (x, y) := by
  change LocalConfiguration.multiplicity
    (LocalConfiguration.mapHomeomorph (edgeReroot a) scene.edges) (edgeReroot a (x, y)) = _
  rw [LocalConfiguration.multiplicity_mapHomeomorph, Homeomorph.symm_apply_apply]

/-- The geometric perfect matching property is preserved by the actual scene action. -/
theorem IsSimplePerfectMatching.reroot {scene : MatchingScene}
    (h : IsSimplePerfectMatching scene) (a : ℝ) : IsSimplePerfectMatching (scene.reroot a) := by
  have hs (x : MatchingPoint) : LocalConfiguration.multiplicity (scene.reroot a).source x =
      LocalConfiguration.multiplicity scene.source (x.1 + a, x.2) := by
    simp only [MatchingScene.reroot, LocalConfiguration.reroot,
      LocalConfiguration.multiplicity_translate, sub_neg_eq_add]
  have ht (x : MatchingPoint) : LocalConfiguration.multiplicity (scene.reroot a).target x =
      LocalConfiguration.multiplicity scene.target (x.1 + a, x.2) := by
    simp only [MatchingScene.reroot, LocalConfiguration.reroot,
      LocalConfiguration.multiplicity_translate, sub_neg_eq_add]
  have he (e : MatchingPoint × MatchingPoint) :
      LocalConfiguration.multiplicity (scene.reroot a).edges e =
        LocalConfiguration.multiplicity scene.edges ((e.1.1 + a, e.1.2), (e.2.1 + a, e.2.2)) := by
    simpa using edge_multiplicity_reroot scene a (e.1.1 + a, e.1.2) (e.2.1 + a, e.2.2)
  refine {
    simple_edges := ?_
    endpoints := ?_
    source_injective := ?_
    target_injective := ?_
    source_exists := ?_
    target_exists := ?_ }
  · intro e
    rw [he]
    exact h.simple_edges _
  · intro e hedge
    rw [he] at hedge
    simpa only [hs, ht] using h.endpoints _ hedge
  · intro x hx y hy hxy
    change LocalConfiguration.multiplicity (scene.reroot a).edges x ≠ 0 at hx
    change LocalConfiguration.multiplicity (scene.reroot a).edges y ≠ 0 at hy
    rw [he] at hx hy
    have hh := h.source_injective hx hy
      (congrArg (fun v : MatchingPoint ↦ (v.1 + a, v.2)) hxy)
    have hh' := congrArg (edgeReroot a) hh
    simpa using hh'
  · intro x hx y hy hxy
    change LocalConfiguration.multiplicity (scene.reroot a).edges x ≠ 0 at hx
    change LocalConfiguration.multiplicity (scene.reroot a).edges y ≠ 0 at hy
    rw [he] at hx hy
    have hh := h.target_injective hx hy
      (congrArg (fun v : MatchingPoint ↦ (v.1 + a, v.2)) hxy)
    have hh' := congrArg (edgeReroot a) hh
    simpa using hh'
  · intro x hx
    rw [hs] at hx
    obtain ⟨y, hy⟩ := h.source_exists _ hx
    refine ⟨(y.1 - a, y.2), ?_⟩
    rw [he]
    simpa using hy
  · intro y hy
    rw [ht] at hy
    obtain ⟨x, hx⟩ := h.target_exists _ hy
    refine ⟨(x.1 - a, x.2), ?_⟩
    rw [he]
    simpa using hx

/-- The full actual source-atom relabelling induced by moving the observation origin. -/
noncomputable def sourceAtomRerootEquiv (scene : MatchingScene) (a : ℝ) :
    SourceAtom scene ≃ SourceAtom (scene.reroot a) where
  toFun x := ⟨(x.val.1 - a, x.val.2), by simpa using x.property⟩
  invFun x := ⟨(x.val.1 + a, x.val.2), by
    have h := x.property
    rw [← source_multiplicity_reroot scene a (x.val.1 + a, x.val.2)]
    simpa using h⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

/-- The corresponding relabelling of actual target atoms. -/
noncomputable def targetAtomRerootEquiv (scene : MatchingScene) (a : ℝ) :
    TargetAtom scene ≃ TargetAtom (scene.reroot a) where
  toFun x := ⟨(x.val.1 - a, x.val.2), by simpa using x.property⟩
  invFun x := ⟨(x.val.1 + a, x.val.2), by
    have h := x.property
    rw [← target_multiplicity_reroot scene a (x.val.1 + a, x.val.2)]
    simpa using h⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp

/-- Edge membership characterizes the partner selected by actual perfect matching geometry. -/
theorem atomAssignment_eq_iff_edge {scene : MatchingScene} (h : IsSimplePerfectMatching scene)
    (x : SourceAtom scene) (y : TargetAtom scene) :
    atomAssignment h x = y ↔ LocalConfiguration.multiplicity scene.edges (x.val, y.val) ≠ 0 := by
  constructor
  · intro heq
    rw [← heq]
    exact atomAssignment_edge h x
  · intro hedge
    apply Subtype.ext
    exact congrArg Prod.snd (h.source_injective (atomAssignment_edge h x) hedge rfl)

/-- Rerooting conjugates the actual partner bijection whenever both scenes are perfect.
No assumption about covariance of the chosen partner is used. -/
theorem atomAssignment_reroot {scene : MatchingScene} (h : IsSimplePerfectMatching scene)
    (a : ℝ) (ha : IsSimplePerfectMatching (scene.reroot a)) (x : SourceAtom scene) :
    atomAssignment ha (sourceAtomRerootEquiv scene a x) =
      targetAtomRerootEquiv scene a (atomAssignment h x) := by
  apply (atomAssignment_eq_iff_edge ha _ _).mpr
  change LocalConfiguration.multiplicity (scene.reroot a).edges
    ((x.val.1 - a, x.val.2), ((atomAssignment h x).val.1 - a, (atomAssignment h x).val.2)) ≠ 0
  rw [edge_multiplicity_reroot]
  exact atomAssignment_edge h x

/-- The actual edge relation is Borel jointly in the whole scene and both marked endpoints. -/
theorem measurableSet_edgeAtom :
    MeasurableSet {z : MatchingScene × (MatchingPoint × MatchingPoint) |
      LocalConfiguration.multiplicity z.1.edges z.2 ≠ 0} := by
  exact LocalConfiguration.measurableSet_atom.preimage
    ((measurable_edges.comp measurable_fst).prodMk measurable_snd)

/-- Testing a measurable raw source-target label pair against the scene edges is measurable. -/
theorem measurableSet_edgeAtom_param {Ω : Type*} [MeasurableSpace Ω]
    {scene : Ω → MatchingScene} {x y : Ω → MatchingPoint}
    (hscene : Measurable scene) (hx : Measurable x) (hy : Measurable y) :
    MeasurableSet {ω | LocalConfiguration.multiplicity (scene ω).edges (x ω, y ω) ≠ 0} :=
  measurableSet_edgeAtom.preimage (hscene.prodMk (hx.prodMk hy))

end MatchingScene

end OTSelector.PointProcess
