import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.Independence.Basic

/-!
# Null events with finite independent fibres

This file isolates the measure-theoretic fact used by the finite feedback no-tie argument.  A
measurable subset of a product has product measure zero when every section in an atomless
coordinate is finite.  Pulling the statement back along two independent random variables gives
the corresponding probability-zero result.

The result is deliberately independent of filtrations, conditional laws, and feedback data.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

variable {Ω Y X : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace X]

/-- A measurable product set with finite sections in an atomless second coordinate is null. -/
theorem measure_prod_eq_zero_of_finite_fibres
    {μ : Measure Y} {ν : Measure X} [NullSingletonClass ν]
    {s : Set (Y × X)} (hs : MeasurableSet s)
    (hfinite : ∀ y, (Prod.mk y ⁻¹' s).Finite) :
    μ.prod ν s = 0 := by
  apply Measure.measure_prod_null_of_ae_null hs
  exact Filter.Eventually.of_forall fun y ↦ (hfinite y).measure_zero ν

/-- The subsingleton-section specialization of `measure_prod_eq_zero_of_finite_fibres`. -/
theorem measure_prod_eq_zero_of_subsingleton_fibres
    {μ : Measure Y} {ν : Measure X} [NullSingletonClass ν]
    {s : Set (Y × X)} (hs : MeasurableSet s)
    (hsubsingleton : ∀ y, (Prod.mk y ⁻¹' s).Subsingleton) :
    μ.prod ν s = 0 := by
  exact measure_prod_eq_zero_of_finite_fibres hs fun y ↦ (hsubsingleton y).finite

/-- Pull a finite-fibre product-null statement back along two independent random variables. -/
theorem measure_pair_mem_eq_zero_of_indepFun_of_finite_fibres
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure X} [NullSingletonClass ν]
    {left : Ω → Y} {right : Ω → X}
    (hleft : Measurable left) (hright : Measurable right)
    (hindep : IndepFun left right μ)
    (hrightLaw : μ.map right = ν)
    {s : Set (Y × X)} (hs : MeasurableSet s)
    (hfinite : ∀ y, (Prod.mk y ⁻¹' s).Finite) :
    μ ((fun ω ↦ (left ω, right ω)) ⁻¹' s) = 0 := by
  rw [← Measure.map_apply_of_aemeasurable (hleft.prodMk hright).aemeasurable hs]
  rw [hindep.map_prod_eq_prod_map_map hleft.aemeasurable hright.aemeasurable, hrightLaw]
  exact measure_prod_eq_zero_of_finite_fibres hs hfinite

/-- If an atomless random variable is independent of another random variable, it almost surely
does not equal a measurable function of that other variable. -/
theorem measure_eq_comp_eq_zero_of_indepFun
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure X} [NullSingletonClass ν]
    [MeasurableEq X] {left : Ω → Y} {right : Ω → X} {value : Y → X}
    (hleft : Measurable left) (hright : Measurable right) (hvalue : Measurable value)
    (hindep : IndepFun left right μ)
    (hrightLaw : μ.map right = ν) :
    μ {ω | right ω = value (left ω)} = 0 := by
  let s : Set (Y × X) := {pair | pair.2 = value pair.1}
  have hs : MeasurableSet s :=
    measurableSet_eq_fun measurable_snd (hvalue.comp measurable_fst)
  have hfinite : ∀ y, (Prod.mk y ⁻¹' s).Finite := by
    intro y
    have heq : Prod.mk y ⁻¹' s = {value y} := by
      ext x
      simp [s]
    rw [heq]
    exact Set.finite_singleton _
  have hpullback : (fun ω ↦ (left ω, right ω)) ⁻¹' s =
      {ω | right ω = value (left ω)} := by
    ext ω
    simp [s]
  rw [← hpullback]
  exact measure_pair_mem_eq_zero_of_indepFun_of_finite_fibres
    hleft hright hindep hrightLaw hs hfinite

end OTSelector
