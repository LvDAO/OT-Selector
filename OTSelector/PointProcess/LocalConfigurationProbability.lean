import OTSelector.PointProcess.LocalConfigurationBorel
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Tight sequences of actual configuration laws

The countable geometric test code is continuous and measurably injective.  Its pushforward on
probability measures is therefore continuous and injective into a metrizable probability-law
space.  Compact sets of configuration laws are consequently metrizable.  Combining this with
mathlib's Hausdorff-space Prokhorov theorem gives weakly convergent subsequences of tight
configuration laws, without imposing an unproved Polish structure on the vague carrier.
-/

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped Classical

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [StandardBorelSpace X] [SecondCountableTopology X] {base : X}

noncomputable local instance : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance : T2Space (LocalConfiguration base) := vagueT2Space

/-- The law of the countable geometric test observables. -/
noncomputable def probabilityTestCode (μ : ProbabilityMeasure (LocalConfiguration base)) :
    ProbabilityMeasure (ℕ × ℚ → ℝ) :=
  μ.map measurable_separatingTestCode.aemeasurable

theorem continuous_probabilityTestCode :
    Continuous (probabilityTestCode : ProbabilityMeasure (LocalConfiguration base) → _) :=
  ProbabilityMeasure.continuous_map continuous_separatingTestCode

/-- Equality of all joint geometric-test laws determines the complete configuration law. -/
theorem probabilityTestCode_injective :
    Function.Injective (probabilityTestCode : ProbabilityMeasure (LocalConfiguration base) → _) := by
  intro μ ν h
  apply Subtype.ext
  apply (measurable_separatingTestCode.measurableEmbedding
    (separatingTestCode_injective (base := base))).map_injective
  exact congrArg (fun ρ : ProbabilityMeasure (ℕ × ℚ → ℝ) ↦ (ρ : Measure (ℕ × ℚ → ℝ))) h

/-- Every compact family of actual configuration laws is metrizable in the weak topology. -/
theorem metrizableSpace_probability_of_isCompact
    {K : Set (ProbabilityMeasure (LocalConfiguration base))} (hK : IsCompact K) :
    MetrizableSpace K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcont := (continuous_probabilityTestCode (base := base)).comp
    (continuous_subtype_val : Continuous
      (Subtype.val : K → ProbabilityMeasure (LocalConfiguration base)))
  exact (hcont.isClosedEmbedding
    (probabilityTestCode_injective.comp Subtype.val_injective)).isEmbedding.metrizableSpace

/-- Tight sequences of laws of the actual vague configurations have weakly convergent subsequences.
The tightness premise must be supplied by genuine compact containment estimates. -/
theorem exists_tendsto_subseq_of_isTightMeasureSet
    (μ : ℕ → ProbabilityMeasure (LocalConfiguration base))
    (hμ : IsTightMeasureSet (Set.range (fun n ↦ (μ n : Measure (LocalConfiguration base))))) :
    ∃ ν : ProbabilityMeasure (LocalConfiguration base), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have htight : IsTightMeasureSet
      {((ν : ProbabilityMeasure (LocalConfiguration base)) : Measure (LocalConfiguration base)) |
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

end OTSelector.PointProcess.LocalConfiguration
