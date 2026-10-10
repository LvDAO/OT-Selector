import OTSelector.PointProcess.LocalConfigurationMeasure
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Recovering the configuration sigma algebra from its counting measure

A countable generating pi-system together with finite integer-ball masses determines each
counting measure.  Its evaluations give a measurable embedding of the standard Borel shell
code.  Consequently an arbitrary configuration-valued map is measurable exactly when its
actual counting-measure-valued map is measurable.  This result uses local finiteness and does
not assume a topology on configurations.
-/

open MeasureTheory MeasurableSpace Set
open scoped Classical ENNReal

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [StandardBorelSpace X] {base : X}

private def countGenerators (base : X) : Set (Set X) :=
  countableGeneratingSet X ∪ Set.range (fun n : ℕ ↦ Metric.ball base (n : ℝ))

omit [BorelSpace X] in
private theorem countable_countGenerators (base : X) : (countGenerators base).Countable :=
  (countable_countableGeneratingSet (α := X)).union (countable_range _)

private theorem measurableSet_countGenerators {s : Set X} (hs : s ∈ countGenerators base) :
    MeasurableSet s := by
  rcases hs with hs | ⟨n, rfl⟩
  · exact measurableSet_countableGeneratingSet hs
  · exact Metric.isOpen_ball.measurableSet

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] in
private theorem countable_generatePiSystem {G : Set (Set X)} (hG : G.Countable) :
    (generatePiSystem G).Countable := by
  let : Countable G := hG.to_subtype
  apply (countable_range (fun s : Finset G ↦ ⋂ a ∈ s, a.val)).mono
  intro s hs
  induction hs with
  | @base s hs => exact ⟨{⟨s, hs⟩}, by simp⟩
  | inter hs ht hne ihs iht =>
      obtain ⟨s, rfl⟩ := ihs
      obtain ⟨t, rfl⟩ := iht
      refine ⟨s ∪ t, ?_⟩
      ext x
      simp only [Set.mem_iInter, Finset.mem_union, Set.mem_inter_iff]
      aesop

private abbrev CountTest (base : X) := generatePiSystem (countGenerators base)

private instance countable_countTest (base : X) : Countable (CountTest base) :=
  (countable_generatePiSystem (countable_countGenerators base)).to_subtype

private theorem measurableSet_countTest (s : CountTest base) : MeasurableSet s.val :=
  generatePiSystem_measurableSet (fun _ hs ↦ measurableSet_countGenerators hs) _ s.property

private theorem generateFrom_countTest (base : X) :
    generateFrom (CountTest base) = ‹MeasurableSpace X› := by
  rw [generateFrom_generatePiSystem_eq]
  apply le_antisymm
  · exact generateFrom_le (fun _ hs ↦ measurableSet_countGenerators hs)
  · exact (generateFrom_countableGeneratingSet (α := X)).symm.le.trans
      (generateFrom_mono Set.subset_union_left)

private noncomputable def countCode (config : LocalConfiguration base)
    (s : CountTest base) : ℝ≥0∞ :=
  countingMeasure config s.val

private theorem measurable_countCode :
    Measurable (countCode : LocalConfiguration base → (CountTest base → ℝ≥0∞)) := by
  apply measurable_pi_lambda
  intro s
  exact (Measure.measurable_coe (measurableSet_countTest s)).comp measurable_countingMeasure

private theorem countCode_injective :
    Function.Injective (countCode : LocalConfiguration base → (CountTest base → ℝ≥0∞)) := by
  intro config config' h
  apply countingMeasure_injective
  apply Measure.ext_of_generateFrom_of_iUnion (CountTest base)
    (fun n : ℕ ↦ Metric.ball base (n : ℝ)) (generateFrom_countTest base).symm
    (isPiSystem_generatePiSystem _) (Metric.iUnion_ball_nat base)
  · intro n
    exact generatePiSystem.base (Or.inr ⟨n, rfl⟩)
  · intro n
    rw [countingMeasure_ball]
    exact ENNReal.natCast_ne_top _
  · intro s hs
    exact congrFun h ⟨s, hs⟩

/-- Measurability of a configuration-valued map is equivalent to measurability of its actual
counting measure.  No Borel/topology identification is assumed. -/
theorem measurable_iff_countingMeasure_comp {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → LocalConfiguration base} :
    Measurable f ↔ Measurable (fun ω ↦ countingMeasure (f ω)) := by
  constructor
  · exact fun hf ↦ measurable_countingMeasure.comp hf
  · intro hf
    apply (measurable_countCode.measurableEmbedding countCode_injective).measurable_comp_iff.mp
    apply measurable_pi_lambda
    intro s
    exact (Measure.measurable_coe (measurableSet_countTest s)).comp hf

end OTSelector.PointProcess.LocalConfiguration
