import OTSelector.PointProcess.MatchingSceneTopology
import OTSelector.PointProcess.LocalConfigurationProbability
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Weak subsequences of actual matching-scene laws

The three countable geometric test codes together with the feedback path separate scenes.
They make compact families of scene laws metrizable, so genuine compact containment yields
weakly convergent subsequences in the actual product-vague topology.
-/

open Filter MeasureTheory Set Topology TopologicalSpace

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance sceneProbabilityPointTopology :
    TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase
noncomputable local instance sceneProbabilityEdgeTopology : TopologicalSpace
    (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueTopology (matchingPointBase, matchingPointBase)

private abbrev TestCoordinates :=
  (ℕ × ℚ → ℝ) × (ℕ × ℚ → ℝ) × (ℕ × ℚ → ℝ) × (ℚ → ℝ) × ℤ

private noncomputable def testCode (scene : MatchingScene) : TestCoordinates :=
  (LocalConfiguration.separatingTestCode scene.source,
    LocalConfiguration.separatingTestCode scene.target,
    LocalConfiguration.separatingTestCode scene.edges,
    (fun q : ℚ ↦ scene.path.graphHeight (q : ℝ)), scene.path.rootCurrent)

private theorem continuous_testCode : Continuous testCode :=
  (LocalConfiguration.continuous_separatingTestCode.comp continuous_source).prodMk <|
    (LocalConfiguration.continuous_separatingTestCode.comp continuous_target).prodMk <|
      (LocalConfiguration.continuous_separatingTestCode.comp continuous_edges).prodMk <|
        (continuous_pi fun q : ℚ ↦ (GraphHeight.continuous_apply (q : ℝ)).comp
          continuous_graphHeight).prodMk continuous_rootCurrent

private theorem testCode_injective : Function.Injective testCode := by
  intro a b h
  have hs := congrArg Prod.fst h
  have ht := congrArg (fun p : TestCoordinates ↦ p.2.1) h
  have he := congrArg (fun p : TestCoordinates ↦ p.2.2.1) h
  have hg := congrArg (fun p : TestCoordinates ↦ p.2.2.2.1) h
  have hk := congrArg (fun p : TestCoordinates ↦ p.2.2.2.2) h
  exact MatchingScene.ext
    (LocalConfiguration.separatingTestCode_injective hs)
    (LocalConfiguration.separatingTestCode_injective ht)
    (LocalConfiguration.separatingTestCode_injective he)
    (FeedbackPath.ext (GraphHeight.measurableEmbedding_rationalValues.injective hg) hk)

private noncomputable def probabilityTestCode (μ : ProbabilityMeasure MatchingScene) :
    ProbabilityMeasure TestCoordinates := μ.map continuous_testCode.measurable.aemeasurable

private theorem continuous_probabilityTestCode : Continuous probabilityTestCode :=
  ProbabilityMeasure.continuous_map continuous_testCode

private theorem probabilityTestCode_injective : Function.Injective probabilityTestCode := by
  intro μ ν h
  apply Subtype.ext
  apply (continuous_testCode.measurable.measurableEmbedding testCode_injective).map_injective
  exact congrArg (fun ρ : ProbabilityMeasure TestCoordinates ↦ (ρ : Measure TestCoordinates)) h

/-- Actual scene-law weak limits are unique, via the separating continuous test code. -/
theorem eq_of_tendsto_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {μ : ι → ProbabilityMeasure MatchingScene} {ν ρ : ProbabilityMeasure MatchingScene}
    (hν : Tendsto μ l (𝓝 ν)) (hρ : Tendsto μ l (𝓝 ρ)) : ν = ρ :=
  probabilityTestCode_injective (tendsto_nhds_unique
    ((continuous_probabilityTestCode.tendsto ν).comp hν)
    ((continuous_probabilityTestCode.tendsto ρ).comp hρ))

/-- Compact sets of probability laws are metrizable for the genuine scene topology. -/
theorem metrizableSpace_probability_of_isCompact
    {K : Set (ProbabilityMeasure MatchingScene)} (hK : IsCompact K) : MetrizableSpace K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc := continuous_probabilityTestCode.comp
    (continuous_subtype_val : Continuous (Subtype.val : K → ProbabilityMeasure MatchingScene))
  exact (hc.isClosedEmbedding
    (probabilityTestCode_injective.comp Subtype.val_injective)).isEmbedding.metrizableSpace

/-- Tight actual scene laws have weakly convergent subsequences without imposing a different
Polish topology on the scene carrier. -/
theorem exists_tendsto_subseq_of_isTightMeasureSet
    (μ : ℕ → ProbabilityMeasure MatchingScene)
    (hμ : IsTightMeasureSet (Set.range fun n ↦ (μ n : Measure MatchingScene))) :
    ∃ ν : ProbabilityMeasure MatchingScene, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure MatchingScene) : Measure MatchingScene) |
        ν ∈ Set.range μ} := by
    convert hμ using 1
    ext ν
    simp
  have hcompact := isCompact_closure_of_isTightMeasureSet htight
  let K := closure (Set.range μ)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let : MetrizableSpace K := metrizableSpace_probability_of_isCompact hcompact
  obtain ⟨ν, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq
    (fun n ↦ (⟨μ n, subset_closure (Set.mem_range_self n)⟩ : K))
  exact ⟨ν.val, φ, hφ, (continuous_subtype_val.tendsto ν).comp hlim⟩

/-- Quantitative closed-set Portmanteau for the actual scene topology. Uniform tightness
reduces each closed set to a compact part, where the continuous injective code has closed image. -/
theorem limsup_measure_closed_le_of_tendsto_of_tight
    (μ : ℕ → ProbabilityMeasure MatchingScene) {ν : ProbabilityMeasure MatchingScene}
    (hlim : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (Set.range fun n ↦ (μ n : Measure MatchingScene)))
    {F : Set MatchingScene} (hF : IsClosed F) :
    (atTop.limsup fun n ↦ (μ n : Measure MatchingScene) F) ≤ (ν : Measure MatchingScene) F := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨K, hK, hKbound⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight ε
      (by exact_mod_cast hε)
  have hFK : IsCompact (F ∩ K) :=
    hK.of_isClosed_subset (hF.inter hK.isClosed) inter_subset_right
  have hcode : IsClosed (testCode '' (F ∩ K)) :=
    (hFK.image continuous_testCode).isClosed
  have hmap (ρ : ProbabilityMeasure MatchingScene) :
      (probabilityTestCode ρ : Measure TestCoordinates) (testCode '' (F ∩ K)) =
        (ρ : Measure MatchingScene) (F ∩ K) := by
    change ((ρ : Measure MatchingScene).map testCode) (testCode '' (F ∩ K)) = _
    rw [Measure.map_apply continuous_testCode.measurable hcode.measurableSet,
      testCode_injective.preimage_image]
  have hsmall := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    ((continuous_probabilityTestCode.tendsto ν).comp hlim) hcode
  simp only [Function.comp_apply, hmap] at hsmall
  have hbound (n : ℕ) : (μ n : Measure MatchingScene) F ≤
      (μ n : Measure MatchingScene) (F ∩ K) + ε := by
    have hsub : F ⊆ (F ∩ K) ∪ Kᶜ := by
      intro x hx
      by_cases hk : x ∈ K
      · exact Or.inl ⟨hx, hk⟩
      · exact Or.inr hk
    exact (measure_mono hsub).trans <| (measure_union_le _ _).trans <|
      add_le_add le_rfl (hKbound _ (mem_range_self n))
  calc
    _ ≤ atTop.limsup (fun n ↦ (μ n : Measure MatchingScene) (F ∩ K) + ε) :=
      Filter.limsup_le_limsup (Eventually.of_forall hbound)
    _ = (atTop.limsup fun n ↦ (μ n : Measure MatchingScene) (F ∩ K)) + ε :=
      limsup_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault)
    _ ≤ (ν : Measure MatchingScene) (F ∩ K) + ε := add_le_add hsmall le_rfl
    _ ≤ (ν : Measure MatchingScene) F + ε := add_le_add (measure_mono inter_subset_left) le_rfl

end OTSelector.PointProcess.MatchingScene
