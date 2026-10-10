import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory Set

namespace OTSelector

variable {Ω A B : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]

/-- The real mass of a measurable product-space set is the outer Bochner integral of its
    real-valued sections. -/
theorem measureReal_prod_section
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {C : Set (A × B)} (hC : MeasurableSet C) :
    (μ.prod ν).real C = ∫ a, ν.real {b | (a, b) ∈ C} ∂μ := by
  change (μ.prod ν C).toReal = ∫ a, (ν {b | (a, b) ∈ C}).toReal ∂μ
  rw [Measure.prod_apply hC]
  symm
  refine integral_toReal (measurable_measure_prodMk_left hC).aemeasurable ?_
  exact Filter.Eventually.of_forall fun a => (measure_ne_top ν _).lt_top

/-- Transport a measurable pair-valued random variable to a product law, then disintegrate the
real mass into its measurable sections. -/
theorem measureReal_preimage_eq_integral_section
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {νA : Measure A} {νB : Measure B} [IsFiniteMeasure νA] [IsFiniteMeasure νB]
    {f : Ω → A × B} (hf : Measurable f)
    (hmap : Measure.map f μ = νA.prod νB)
    {C : Set (A × B)} (hC : MeasurableSet C) :
    μ.real (f ⁻¹' C) = ∫ a, νB.real {b | (a, b) ∈ C} ∂νA := by
  change (μ (f ⁻¹' C)).toReal = _
  rw [← Measure.map_apply hf hC, hmap]
  exact measureReal_prod_section hC

end OTSelector
