import OTSelector.PointProcess.FiniteMatchingSceneMeasurable
import OTSelector.PointProcess.LocalConfigurationTranslation
import OTSelector.PointProcess.CountingKernel
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Actual rerooting of matching scenes

Both endpoints of every edge are shifted horizontally.  The integer current is updated using
actual signed point counts between the old and new roots, with multiplicities retained.
-/

open MeasureTheory ProbabilityTheory Set Function Topology
open scoped BigOperators Classical ENNReal NNReal CompactlySupported
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.PointProcess.LocalConfiguration

section Homeomorph

variable {X : Type*} [MetricSpace X] [ProperSpace X] {base : X}

/-- Transport a configuration by a point homeomorphism, retaining every multiplicity. -/
noncomputable def mapHomeomorph (e : X ≃ₜ X) (config : LocalConfiguration base) :
    LocalConfiguration base :=
  ofLocallyFinsupp {
    toFun x := multiplicity config (e.symm x)
    supportWithinDomain' := subset_univ _
    supportLocallyFiniteWithinDomain' x _ := by
      obtain ⟨s, hs, hfin⟩ := locallyFiniteSupport_multiplicity config (e.symm x)
      refine ⟨e '' s, ?_, ?_⟩
      · simpa using e.isOpenMap.image_mem_nhds hs
      · refine (hfin.image e).subset ?_
        rintro y ⟨⟨z, hz, rfl⟩, hy⟩
        exact ⟨z, ⟨hz, by simpa [Function.mem_support] using hy⟩, rfl⟩ }

@[simp]
theorem multiplicity_mapHomeomorph (e : X ≃ₜ X) (config : LocalConfiguration base) (x : X) :
    multiplicity (mapHomeomorph e config) x = multiplicity config (e.symm x) :=
  multiplicity_ofLocallyFinsupp _ x

@[simp]
theorem mapHomeomorph_refl (config : LocalConfiguration base) :
    mapHomeomorph (Homeomorph.refl X) config = config := by
  apply toLocallyFinsupp_injective
  ext x
  simp

theorem mapHomeomorph_trans (e f : X ≃ₜ X) (config : LocalConfiguration base) :
    mapHomeomorph f (mapHomeomorph e config) = mapHomeomorph (e.trans f) config := by
  apply toLocallyFinsupp_injective
  ext x
  simp

/-- Test integrals pull back along the actual point transport. -/
theorem testIntegral_mapHomeomorph (e : X ≃ₜ X) (config : LocalConfiguration base)
    (f : C_c(X, ℝ)) :
    testIntegral (mapHomeomorph e config) f = testIntegral config (f.comp e.toCocompactMap) := by
  unfold testIntegral
  symm
  apply finsum_eq_of_bijective e e.bijective
  intro x
  simp [testSummand]

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- Point transport pushes forward the actual multiplicity counting measure. -/
theorem countingMeasure_mapHomeomorph (e : X ≃ₜ X) (config : LocalConfiguration base) :
    countingMeasure (mapHomeomorph e config) = (countingMeasure config).map e := by
  let := Measure.Regular.map (μ := countingMeasure config) e
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_countingMeasure, testIntegral_mapHomeomorph, ← integral_countingMeasure]
  exact (integral_map_of_stronglyMeasurable (f := fun x ↦ f x)
    e.measurable f.continuous.stronglyMeasurable).symm

variable [StandardBorelSpace X]

/-- A jointly measurable family of point homeomorphisms transports configurations measurably. -/
theorem measurable_mapHomeomorph_param {A : Type*} [MeasurableSpace A]
    (e : A → X ≃ₜ X) (he : Measurable (fun p : A × X ↦ e p.1 p.2)) :
    Measurable (fun p : A × LocalConfiguration base ↦ mapHomeomorph (e p.1) p.2) := by
  apply measurable_iff_countingMeasure_comp.mpr
  simp_rw [countingMeasure_mapHomeomorph]
  exact measurable_map_countingMeasure_param he

/-- Finite tuple encoding commutes with the genuine point transport. -/
theorem mapHomeomorph_ofTuple {n : ℕ} (e : X ≃ₜ X) (points : Fin n → X) :
    mapHomeomorph e (ofTuple base points) = ofTuple base (fun i ↦ e (points i)) := by
  apply countingMeasure_injective
  rw [countingMeasure_mapHomeomorph, countingMeasure_ofTuple, countingMeasure_ofTuple,
    Measure.map_finset_sum]
  · simp
  · exact e.measurable.aemeasurable

end Homeomorph
section IntegerCounts

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {base : X}

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
private theorem multiset_indicator_sum_nat (m : Multiset X) (s : Set X) :
    (m.map (s.indicator (fun _ ↦ (1 : ℝ≥0∞)))).sum =
      ((m.map (fun x ↦ if x ∈ s then (1 : ℕ) else 0)).sum : ℕ) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih => by_cases hx : x ∈ s <;> simp [hx, ih, Nat.cast_add]

omit [BorelSpace X] in
/-- Every bounded measurable window has an actual integer counting mass. -/
theorem exists_nat_countingMeasure_of_isBounded (config : LocalConfiguration base)
    {s : Set X} (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s) :
    ∃ k : ℕ, countingMeasure config s = k := by
  obtain ⟨R, hR⟩ := hbounded.subset_ball base
  obtain ⟨N, hN⟩ := exists_nat_gt R
  have hsub : s ⊆ Metric.ball base (N : ℝ) :=
    hR.trans (Metric.ball_subset_ball hN.le)
  let mass (k : ℕ) := (((config k).map Subtype.val).map
    (fun x ↦ if x ∈ s then (1 : ℕ) else 0)).sum
  refine ⟨∑ k ∈ Finset.range N, mass k, ?_⟩
  rw [countingMeasure_apply _ hs, Nat.cast_sum]
  have hshell (k : ℕ) : shellMeasure config k s = (mass k : ℝ≥0∞) := by
    rw [shellMeasure_apply _ _ hs]
    simpa only [mass, Multiset.map_map, Function.comp_def] using
      multiset_indicator_sum_nat ((config k).map Subtype.val) s
  rw [tsum_eq_sum (s := Finset.range N)]
  · exact Finset.sum_congr rfl fun k _ ↦ hshell k
  · intro k hk
    rw [shellMeasure_apply _ _ hs]
    apply Multiset.sum_eq_zero
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    apply Set.indicator_of_notMem
    intro hxs
    have hxN := (shellIndex_lt_iff base x.val N).mpr (hsub hxs)
    exact hk (Finset.mem_range.mpr (x.property ▸ hxN))

end IntegerCounts
end OTSelector.PointProcess.LocalConfiguration

namespace OTSelector.PointProcess.LocalConfiguration

/-- Marked points whose spatial positions lie in `(a,b]`. -/
def spatialIoc (a b : ℝ) : Set MatchingPoint := Prod.fst ⁻¹' Ioc a b

theorem measurableSet_spatialIoc (a b : ℝ) : MeasurableSet (spatialIoc a b) :=
  measurableSet_Ioc.preimage measurable_fst

theorem isBounded_spatialIoc (a b : ℝ) : Bornology.IsBounded (spatialIoc a b) := by
  apply (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set UnitMark))).isBounded.subset
  intro x hx
  exact ⟨⟨hx.1.le, hx.2⟩, mem_univ _⟩

/-- The actual point count in a bounded spatial interval, as an integer. -/
noncomputable def spatialCount (config : LocalConfiguration matchingPointBase) (a b : ℝ) : ℤ :=
  ⌊(countingMeasure config).real (spatialIoc a b)⌋

/-- The count is already integral, so its real value is the true counting mass. -/
theorem spatialCount_cast (config : LocalConfiguration matchingPointBase) (a b : ℝ) :
    (spatialCount config a b : ℝ) = (countingMeasure config).real (spatialIoc a b) := by
  obtain ⟨k, hk⟩ := exists_nat_countingMeasure_of_isBounded config
    (measurableSet_spatialIoc a b) (isBounded_spatialIoc a b)
  simp [spatialCount, Measure.real, hk]

@[simp]
theorem spatialCount_eq_zero_of_le (config : LocalConfiguration matchingPointBase)
    {a b : ℝ} (hba : b ≤ a) : spatialCount config a b = 0 := by
  simp [spatialCount, spatialIoc, Ioc_eq_empty_of_le hba]

theorem spatialCount_add (config : LocalConfiguration matchingPointBase)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    spatialCount config a c = spatialCount config a b + spatialCount config b c := by
  apply (Int.cast_injective (α := ℝ))
  rw [Int.cast_add, spatialCount_cast, spatialCount_cast, spatialCount_cast]
  have hunion : spatialIoc a b ∪ spatialIoc b c = spatialIoc a c := by
    simp only [spatialIoc, ← preimage_union, Ioc_union_Ioc_eq_Ioc hab hbc]
  rw [← hunion]
  apply measureReal_union
  · exact Set.disjoint_left.mpr fun x hx hy ↦ (not_lt_of_ge hx.2) hy.1
  · exact measurableSet_spatialIoc b c
  · exact (countingMeasure_lt_top_of_isBounded config (isBounded_spatialIoc a b)).ne
  · exact (countingMeasure_lt_top_of_isBounded config (isBounded_spatialIoc b c)).ne

/-- Signed count from `a` to `b`, using the right-closed cut convention. -/
noncomputable def orientedCount (config : LocalConfiguration matchingPointBase) (a b : ℝ) : ℤ :=
  spatialCount config a b - spatialCount config b a

@[simp]
theorem orientedCount_self (config : LocalConfiguration matchingPointBase) (a : ℝ) :
    orientedCount config a a = 0 := sub_self _

theorem orientedCount_antisymm (config : LocalConfiguration matchingPointBase) (a b : ℝ) :
    orientedCount config b a = -orientedCount config a b := by
  simp only [orientedCount]
  ring

/-- Signed actual interval counts are additive for all orders of the three cuts. -/
theorem orientedCount_add (config : LocalConfiguration matchingPointBase) (a b c : ℝ) :
    orientedCount config a c = orientedCount config a b + orientedCount config b c := by
  unfold orientedCount
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · have h := spatialCount_add config hab hbc
      simp only [spatialCount_eq_zero_of_le config hab,
        spatialCount_eq_zero_of_le config hbc, spatialCount_eq_zero_of_le config (hab.trans hbc),
        sub_zero]
      exact h
    · rcases le_total a c with hac | hca
      · have h := spatialCount_add config hac hcb
        simp only [spatialCount_eq_zero_of_le config hab,
          spatialCount_eq_zero_of_le config hcb, spatialCount_eq_zero_of_le config hac,
          sub_zero, zero_sub]
        omega
      · have h := spatialCount_add config hca hab
        simp only [spatialCount_eq_zero_of_le config hab,
          spatialCount_eq_zero_of_le config hcb, spatialCount_eq_zero_of_le config hca,
          sub_zero, zero_sub]
        omega
  · rcases le_total a c with hac | hca
    · have h := spatialCount_add config hba hac
      simp only [spatialCount_eq_zero_of_le config hba,
        spatialCount_eq_zero_of_le config hac, spatialCount_eq_zero_of_le config (hba.trans hac),
        sub_zero, zero_sub]
      omega
    · rcases le_total b c with hbc | hcb
      · have h := spatialCount_add config hbc hca
        simp only [spatialCount_eq_zero_of_le config hba,
          spatialCount_eq_zero_of_le config hbc, spatialCount_eq_zero_of_le config hca,
          sub_zero, zero_sub]
        omega
      · have h := spatialCount_add config hcb hba
        simp only [spatialCount_eq_zero_of_le config hba,
          spatialCount_eq_zero_of_le config hcb, spatialCount_eq_zero_of_le config hca, zero_sub]
        omega

/-- Variable endpoints and the entire underlying configuration are jointly measurable. -/
theorem measurable_spatialCount :
    Measurable (fun p : (ℝ × ℝ) × LocalConfiguration matchingPointBase ↦
      spatialCount p.2 p.1.1 p.1.2) := by
  let κ := randomCountingKernel
    (fun p : (ℝ × ℝ) × LocalConfiguration matchingPointBase ↦ p.2) measurable_snd
  have hset : MeasurableSet {p : ((ℝ × ℝ) × LocalConfiguration matchingPointBase) × MatchingPoint |
      p.1.1.1 < p.2.1 ∧ p.2.1 ≤ p.1.1.2} := by
    exact (measurableSet_lt (measurable_fst.comp (measurable_fst.comp measurable_fst))
      (measurable_fst.comp measurable_snd)).inter
        (measurableSet_le (measurable_fst.comp measurable_snd)
          (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  exact (ENNReal.measurable_toReal.comp
    (Kernel.measurable_kernel_prodMk_left (κ := κ) hset )).floor

theorem measurable_orientedCount :
    Measurable (fun p : (ℝ × ℝ) × LocalConfiguration matchingPointBase ↦
      orientedCount p.2 p.1.1 p.1.2) := by
  have hswap : Measurable (fun p : (ℝ × ℝ) × LocalConfiguration matchingPointBase ↦
      ((p.1.2, p.1.1), p.2)) :=
    ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd
  change Measurable (fun p : (ℝ × ℝ) × LocalConfiguration matchingPointBase ↦
    spatialCount p.2 p.1.1 p.1.2 - spatialCount p.2 p.1.2 p.1.1)
  have hrev := measurable_spatialCount.comp hswap
  exact Measurable.sub measurable_spatialCount hrev

end OTSelector.PointProcess.LocalConfiguration

namespace OTSelector.PointProcess.LocalConfiguration

/-- Interval counts transform exactly under the existing physical rerooting. -/
theorem spatialCount_reroot (config : LocalConfiguration matchingPointBase) (a x y : ℝ) :
    spatialCount (reroot a config) x y = spatialCount config (x + a) (y + a) := by
  unfold spatialCount
  rw [Measure.real, countingMeasure_reroot, Measure.map_apply
    (Configuration.pointTranslation (-a)).measurable (measurableSet_spatialIoc x y)]
  have hset : Configuration.pointTranslation (-a) ⁻¹' spatialIoc x y =
      spatialIoc (x + a) (y + a) := by
    ext p
    simp only [mem_preimage, Configuration.pointTranslation_apply, spatialIoc, mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [hset]
  rfl

/-- Genuine signed interval counts shift both cuts in the old coordinate frame. -/
theorem orientedCount_reroot (config : LocalConfiguration matchingPointBase) (a x y : ℝ) :
    orientedCount (reroot a config) x y = orientedCount config (x + a) (y + a) := by
  simp only [orientedCount, spatialCount_reroot]

@[simp]
theorem reroot_zero (config : LocalConfiguration matchingPointBase) : reroot 0 config = config := by
  simp [reroot]

theorem reroot_add (a b : ℝ) (config : LocalConfiguration matchingPointBase) :
    reroot b (reroot a config) = reroot (a + b) config := by
  simp only [reroot, translate_add]
  congr 1
  ring

private theorem mapHomeomorph_pointTranslation (a : ℝ)
    (config : LocalConfiguration matchingPointBase) :
    mapHomeomorph (Configuration.pointTranslation a) config = translate a config := by
  apply toLocallyFinsupp_injective
  ext p
  simp

/-- Finite point clouds are rerooted by subtracting the root displacement from each position. -/
theorem reroot_ofTuple {n : ℕ} (a : ℝ) (points : Fin n → MatchingPoint) :
    reroot a (ofTuple matchingPointBase points) =
      ofTuple matchingPointBase (fun i ↦ ((points i).1 - a, (points i).2)) := by
  rw [reroot, ← mapHomeomorph_pointTranslation, mapHomeomorph_ofTuple]
  rfl

/-- On finite arrays, the interval count is the usual sum of indicator variables. -/
theorem spatialCount_ofTuple {n : ℕ} (points : Fin n → MatchingPoint) (a b : ℝ) :
    spatialCount (ofTuple matchingPointBase points) a b =
      ∑ i, if a < (points i).1 ∧ (points i).1 ≤ b then (1 : ℤ) else 0 := by
  unfold spatialCount Measure.real
  rw [countingMeasure_ofTuple, Measure.finsetSum_apply]
  have hd (i : Fin n) : Measure.dirac (points i) (spatialIoc a b) =
      if a < (points i).1 ∧ (points i).1 ≤ b then (1 : ℝ≥0∞) else 0 := by
    rw [Measure.dirac_apply' _ (measurableSet_spatialIoc a b)]
    simp [spatialIoc, Set.indicator_apply]
  simp_rw [hd]
  rw [Finset.sum_boole, Finset.sum_boole]
  simp

/-- Finite signed interval counts are exactly differences of closed cut counts. -/
theorem orientedCount_ofTuple {n : ℕ} (points : Fin n → MatchingPoint) (a b : ℝ) :
    orientedCount (ofTuple matchingPointBase points) a b =
      (∑ i, if (points i).1 ≤ b then (1 : ℤ) else 0) -
        ∑ i, if (points i).1 ≤ a then (1 : ℤ) else 0 := by
  rw [orientedCount, spatialCount_ofTuple, spatialCount_ofTuple,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ha : (points i).1 ≤ a <;> by_cases hb : (points i).1 ≤ b <;>
    simp [ha, hb, not_lt.mpr, lt_of_not_ge]

end OTSelector.PointProcess.LocalConfiguration

namespace OTSelector.PointProcess.MatchingScene

/-- Actual source-minus-target count increment between two cuts. -/
noncomputable def currentIncrement (scene : MatchingScene) (x y : ℝ) : ℤ :=
  LocalConfiguration.orientedCount scene.source x y -
    LocalConfiguration.orientedCount scene.target x y

theorem currentIncrement_add (scene : MatchingScene) :
    FeedbackPath.IsAdditiveIntegerIncrement scene.currentIncrement := by
  intro x y z
  simp only [currentIncrement, LocalConfiguration.orientedCount_add _ x y z]
  ring

/-- Move both marked endpoints of an edge into the new root frame. -/
def edgeReroot (a : ℝ) : (MatchingPoint × MatchingPoint) ≃ₜ (MatchingPoint × MatchingPoint) :=
  (Configuration.pointTranslation (-a)).prodCongr (Configuration.pointTranslation (-a))

@[simp]
theorem edgeReroot_apply (a : ℝ) (e : MatchingPoint × MatchingPoint) :
    edgeReroot a e = ((e.1.1 - a, e.1.2), (e.2.1 - a, e.2.2)) := rfl

/-- Reroot the actual configurations and height, updating current by the observed point counts. -/
noncomputable def reroot (a : ℝ) (scene : MatchingScene) : MatchingScene where
  source := LocalConfiguration.reroot a scene.source
  target := LocalConfiguration.reroot a scene.target
  edges := LocalConfiguration.mapHomeomorph (edgeReroot a) scene.edges
  path := FeedbackPath.rerootWithIncrement scene.currentIncrement a scene.path

/-- The new count increment is the original increment in shifted coordinates. -/
theorem currentIncrement_reroot (scene : MatchingScene) (a x y : ℝ) :
    (reroot a scene).currentIncrement x y = scene.currentIncrement (x + a) (y + a) := by
  simp only [currentIncrement, reroot, LocalConfiguration.orientedCount_reroot]

@[simp]
theorem reroot_zero (scene : MatchingScene) : reroot 0 scene = scene := by
  apply MatchingScene.ext
  · exact LocalConfiguration.reroot_zero _
  · exact LocalConfiguration.reroot_zero _
  · have he : edgeReroot 0 = Homeomorph.refl (MatchingPoint × MatchingPoint) := by
      ext e <;> simp
    simp only [reroot, he, LocalConfiguration.mapHomeomorph_refl]
  · exact FeedbackPath.rerootWithIncrement_zero scene.currentIncrement_add scene.path

/-- Actual scene rerooting is an additive action, including its integer current coordinate. -/
theorem reroot_add (a b : ℝ) (scene : MatchingScene) :
    reroot b (reroot a scene) = reroot (a + b) scene := by
  apply MatchingScene.ext
  · exact LocalConfiguration.reroot_add a b scene.source
  · exact LocalConfiguration.reroot_add a b scene.target
  · change LocalConfiguration.mapHomeomorph (edgeReroot b)
        (LocalConfiguration.mapHomeomorph (edgeReroot a) scene.edges) = _
    rw [LocalConfiguration.mapHomeomorph_trans]
    have he : (edgeReroot a).trans (edgeReroot b) = edgeReroot (a + b) := by
      ext e <;> simp only [Homeomorph.trans_apply, edgeReroot_apply] <;> ring
    rw [he]
    rfl
  · change FeedbackPath.rerootWithIncrement (reroot a scene).currentIncrement b
        (FeedbackPath.rerootWithIncrement scene.currentIncrement a scene.path) = _
    have hincr : (reroot a scene).currentIncrement =
        FeedbackPath.shiftIncrement a scene.currentIncrement := by
      funext x y
      exact currentIncrement_reroot scene a x y
    rw [hincr]
    exact FeedbackPath.rerootWithIncrement_add scene.currentIncrement_add a b scene.path

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.PointProcess.MatchingScene

@[fun_prop]
theorem measurable_source : Measurable (source : MatchingScene → _) :=
  measurable_fst.comp measurableEquivCoordinates.measurable

@[fun_prop]
theorem measurable_target : Measurable (target : MatchingScene → _) :=
  (measurable_fst.comp measurable_snd).comp measurableEquivCoordinates.measurable

@[fun_prop]
theorem measurable_edges : Measurable (edges : MatchingScene → _) :=
  (measurable_fst.comp (measurable_snd.comp measurable_snd)).comp
    measurableEquivCoordinates.measurable

@[fun_prop]
theorem measurable_path : Measurable (path : MatchingScene → _) :=
  (measurable_snd.comp (measurable_snd.comp measurable_snd)).comp
    measurableEquivCoordinates.measurable

/-- The actual two-color current increment is jointly measurable in scene and cuts. -/
theorem measurable_currentIncrement :
    Measurable (fun p : (ℝ × ℝ) × MatchingScene ↦ p.2.currentIncrement p.1.1 p.1.2) := by
  have hs := LocalConfiguration.measurable_orientedCount.comp
    (measurable_fst.prodMk (measurable_source.comp measurable_snd))
  have ht := LocalConfiguration.measurable_orientedCount.comp
    (measurable_fst.prodMk (measurable_target.comp measurable_snd))
  exact hs.sub ht

/-- Joint measurability of the genuine scene action, including the count-based current update. -/
theorem measurable_uncurry_reroot :
    Measurable (fun p : ℝ × MatchingScene ↦ reroot p.1 p.2) := by
  have hs : Measurable (fun p : ℝ × MatchingScene ↦
      LocalConfiguration.reroot p.1 p.2.source) := by
    have harg : Measurable (fun p : ℝ × MatchingScene ↦ (p.1, p.2.source)) :=
      measurable_fst.prodMk (measurable_source.comp measurable_snd)
    have hcomp := (LocalConfiguration.measurable_uncurry_reroot
      (base := matchingPointBase)).comp harg
    exact hcomp
  have ht : Measurable (fun p : ℝ × MatchingScene ↦
      LocalConfiguration.reroot p.1 p.2.target) := by
    have harg : Measurable (fun p : ℝ × MatchingScene ↦ (p.1, p.2.target)) :=
      measurable_fst.prodMk (measurable_target.comp measurable_snd)
    have hcomp := (LocalConfiguration.measurable_uncurry_reroot
      (base := matchingPointBase)).comp harg
    exact hcomp
  have hpoint : Measurable (fun p : ℝ × (MatchingPoint × MatchingPoint) ↦ edgeReroot p.1 p.2) := by
    simp only [edgeReroot_apply]
    fun_prop
  have he : Measurable (fun p : ℝ × MatchingScene ↦
      LocalConfiguration.mapHomeomorph (edgeReroot p.1) p.2.edges) := by
    have harg : Measurable (fun p : ℝ × MatchingScene ↦ (p.1, p.2.edges)) :=
      measurable_fst.prodMk (measurable_edges.comp measurable_snd)
    have hmap := LocalConfiguration.measurable_mapHomeomorph_param
      (base := (matchingPointBase, matchingPointBase)) edgeReroot hpoint
    have hcomp := hmap.comp harg
    exact hcomp
  have hg : Measurable (fun p : ℝ × MatchingScene ↦ p.2.path.graphHeight.reroot p.1) :=
    GraphHeight.continuous_uncurry_reroot.measurable.comp <|
      measurable_fst.prodMk <|
        (FeedbackPath.continuous_graphHeight.measurable.comp measurable_path).comp measurable_snd
  have hi : Measurable (fun p : ℝ × MatchingScene ↦ p.2.currentIncrement 0 p.1) := by
    have harg : Measurable (fun p : ℝ × MatchingScene ↦ (((0 : ℝ), p.1), p.2)) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    have hcomp := measurable_currentIncrement.comp harg
    exact hcomp
  have hk : Measurable (fun p : ℝ × MatchingScene ↦
      p.2.path.rootCurrent + p.2.currentIncrement 0 p.1) :=
    ((FeedbackPath.continuous_rootCurrent.measurable.comp measurable_path).comp measurable_snd).add hi
  have hp : Measurable (fun p : ℝ × MatchingScene ↦
      FeedbackPath.rerootWithIncrement p.2.currentIncrement p.1 p.2.path) := by
    have hemb : MeasurableEmbedding FeedbackPath.coordinates :=
      FeedbackPath.isEmbedding_coordinates.continuous.measurable.measurableEmbedding
        FeedbackPath.equivCoordinates.injective
    apply hemb.measurable_comp_iff.mp
    exact hg.prodMk hk
  apply measurableEquivCoordinates.measurableEmbedding.measurable_comp_iff.mp
  exact hs.prodMk (ht.prodMk (he.prodMk hp))

/-- Reading current from a scene requires only its actual two-color point counts. -/
noncomputable def currentAt (scene : MatchingScene) (x : ℝ) : ℤ :=
  scene.path.rootCurrent + scene.currentIncrement 0 x

theorem currentAt_reroot (scene : MatchingScene) (a x : ℝ) :
    (reroot a scene).currentAt x = scene.currentAt (x + a) := by
  change scene.path.rootCurrent + scene.currentIncrement 0 a +
    (reroot a scene).currentIncrement 0 x = _
  rw [currentIncrement_reroot, zero_add]
  rw [currentAt, scene.currentIncrement_add 0 a (x + a)]
  ring

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)

/-- Rerooting the encoded actual assignment is exactly changing its observation root. -/
theorem reroot_rootedMatchingScene (σ : Assignment n) (z a : ℝ) :
    MatchingScene.reroot a (sample.rootedMatchingScene graph σ z) =
      sample.rootedMatchingScene graph σ (z + a) := by
  have hs : LocalConfiguration.orientedCount
      (LocalConfiguration.ofTuple matchingPointBase (sample.rootedSourcePoint graph z)) 0 a =
        (sample.sourceIntersectionCount graph (z + a) : ℤ) -
          sample.sourceIntersectionCount graph z := by
    rw [LocalConfiguration.orientedCount_ofTuple]
    simp [rootedSourcePoint, add_comm a z, sourceIntersectionCount,
      Finset.sum_boole]
  have ht : LocalConfiguration.orientedCount
      (LocalConfiguration.ofTuple matchingPointBase (sample.rootedTargetPoint graph z)) 0 a =
        (sample.targetIntersectionCount graph (z + a) : ℤ) -
          sample.targetIntersectionCount graph z := by
    rw [LocalConfiguration.orientedCount_ofTuple]
    simp [rootedTargetPoint, add_comm a z, targetIntersectionCount,
      Finset.sum_boole]
  apply MatchingScene.ext
  · change LocalConfiguration.reroot a
      (LocalConfiguration.ofTuple matchingPointBase (sample.rootedSourcePoint graph z)) = _
    rw [LocalConfiguration.reroot_ofTuple]
    congr 1
    funext i
    apply Prod.ext
    · dsimp [rootedSourcePoint]
      ring
    · rfl
  · change LocalConfiguration.reroot a
      (LocalConfiguration.ofTuple matchingPointBase (sample.rootedTargetPoint graph z)) = _
    rw [LocalConfiguration.reroot_ofTuple]
    congr 1
    funext i
    apply Prod.ext
    · dsimp [rootedTargetPoint]
      ring
    · rfl
  · change LocalConfiguration.mapHomeomorph (MatchingScene.edgeReroot a)
      (LocalConfiguration.ofTuple (matchingPointBase, matchingPointBase) _) = _
    rw [LocalConfiguration.mapHomeomorph_ofTuple]
    congr 1
    funext i
    simp only [MatchingScene.edgeReroot_apply, rootedSourcePoint, rootedTargetPoint]
    congr 2 <;> ring
  · apply FeedbackPath.ext
    · exact graph.rootedHeight_reroot z a
    · change ((sample.sourceIntersectionCount graph z : ℤ) -
          sample.targetIntersectionCount graph z) +
          (LocalConfiguration.orientedCount
            (LocalConfiguration.ofTuple matchingPointBase (sample.rootedSourcePoint graph z)) 0 a -
            LocalConfiguration.orientedCount
              (LocalConfiguration.ofTuple matchingPointBase (sample.rootedTargetPoint graph z)) 0 a) = _
      rw [hs, ht]
      change _ = (sample.sourceIntersectionCount graph (z + a) : ℤ) -
        sample.targetIntersectionCount graph (z + a)
      ring

/-- The original optimizer obeys the same exact spatial rerooting identity. -/
theorem reroot_rootedEuclideanScene (z a : ℝ) :
    MatchingScene.reroot a (sample.rootedEuclideanScene graph z) =
      sample.rootedEuclideanScene graph (z + a) :=
  sample.reroot_rootedMatchingScene graph sample.euclideanOptimizer z a

/-- Actual stopped optimizer scenes transform pointwise, including on exceptional samples. -/
theorem reroot_stoppedRootedEuclideanScene
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (eta B : ℝ) (T : ℝ≥0) (z a : ℝ) :
    MatchingScene.reroot a (sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T z) =
      sample.stoppedRootedEuclideanScene hlam0 hlamHalf eta B T (z + a) :=
  sample.reroot_rootedEuclideanScene
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) z a

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene

/-- The verified physical rerooting action, with the displacement expressed in old coordinates. -/
noncomputable instance instAddAction : AddAction ℝ MatchingScene where
  vadd := reroot
  zero_vadd := reroot_zero
  add_vadd a b scene := by
    change reroot (a + b) scene = reroot a (reroot b scene)
    simpa only [add_comm a b] using (reroot_add b a scene).symm

instance instMeasurableVAdd₂ : MeasurableVAdd₂ ℝ MatchingScene where
  measurable_vadd := measurable_uncurry_reroot

/-- Every root displacement is a measurable bijection with inverse displacement `-a`. -/
noncomputable def rerootMeasurableEquiv (a : ℝ) : MatchingScene ≃ᵐ MatchingScene where
  toFun := reroot a
  invFun := reroot (-a)
  left_inv scene := by rw [reroot_add]; simp
  right_inv scene := by rw [reroot_add]; simp
  measurable_toFun := by
    have harg : Measurable (fun scene : MatchingScene ↦ (a, scene)) :=
      measurable_const.prodMk measurable_id
    have hcomp := measurable_uncurry_reroot.comp harg
    exact hcomp
  measurable_invFun := by
    have harg : Measurable (fun scene : MatchingScene ↦ (-a, scene)) :=
      measurable_const.prodMk measurable_id
    have hcomp := measurable_uncurry_reroot.comp harg
    exact hcomp

end OTSelector.PointProcess.MatchingScene
