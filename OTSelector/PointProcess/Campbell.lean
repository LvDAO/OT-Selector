import OTSelector.PointProcess.StationaryIntensity
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Campbell factorization from spatial stationarity

A measure on location and rooted mark which is invariant under translations of location factors
as Lebesgue measure times its actual unit-window mark marginal.  This gives the unnormalized Palm
measure without assuming a product decomposition.  The marked measure may have infinite total mass;
only its unit spatial slab must have finite mass.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace OTSelector.PointProcess

variable {M : Type*} [MeasurableSpace M]

/-- The unnormalized Palm measure read from the spatial unit window `(0,1]`. -/
noncomputable def unitWindowPalm (C : Measure (ℝ × M)) : Measure M :=
  (C.restrict (Ioc 0 1 ×ˢ univ)).map Prod.snd

theorem unitWindowPalm_apply (C : Measure (ℝ × M)) {B : Set M}
    (hB : MeasurableSet B) : unitWindowPalm C B = C (Ioc 0 1 ×ˢ B) := by
  rw [unitWindowPalm, Measure.map_apply measurable_snd hB, Measure.restrict_apply
    (measurable_snd hB)]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  exact and_comm

/-- The spatial measure associated with a measurable class of rooted marks. -/
noncomputable def markedSpatialMeasure (C : Measure (ℝ × M)) (B : Set M) : Measure ℝ :=
  (C.restrict (Prod.snd ⁻¹' B)).map Prod.fst

theorem markedSpatialMeasure_apply (C : Measure (ℝ × M)) (B : Set M) {A : Set ℝ}
    (hA : MeasurableSet A) : markedSpatialMeasure C B A = C (A ×ˢ B) := by
  rw [markedSpatialMeasure, Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA)]
  rfl

/-- Stationarity in the location variable holds after restricting to any measurable mark class. -/
theorem invariant_markedSpatialMeasure (C : Measure (ℝ × M))
    (hstat : ∀ a : ℝ, MeasurePreserving (fun z : ℝ × M ↦ (a + z.1, z.2)) C C)
    {B : Set M} (hB : MeasurableSet B) :
    (markedSpatialMeasure C B).IsAddLeftInvariant := by
  constructor
  intro a
  have ha : Measurable (fun x : ℝ ↦ a + x) := measurable_const.add measurable_id
  ext A hA
  rw [Measure.map_apply ha hA, markedSpatialMeasure_apply C B (ha hA),
    markedSpatialMeasure_apply C B hA]
  have h := congrArg (fun μ : Measure (ℝ × M) ↦ μ (A ×ˢ B)) (hstat a).map_eq
  rw [Measure.map_apply (hstat a).measurable (hA.prod hB)] at h
  exact h

/-- Campbell factorization, proved from translation invariance and a finite unit-window mass. -/
theorem campbell_eq_volume_prod_palm (C : Measure (ℝ × M))
    (hstat : ∀ a : ℝ, MeasurePreserving (fun z : ℝ × M ↦ (a + z.1, z.2)) C C)
    (hunit : C (Ioc 0 1 ×ˢ univ) < ∞) :
    C = (volume : Measure ℝ).prod (unitWindowPalm C) := by
  have : IsFiniteMeasure (unitWindowPalm C) := by
    constructor
    rwa [unitWindowPalm_apply C MeasurableSet.univ]
  symm
  apply Measure.prod_eq
  intro A B hA hB
  let := invariant_markedSpatialMeasure C hstat hB
  have hfinite : markedSpatialMeasure C B (Ioc 0 1) < ∞ := by
    rw [markedSpatialMeasure_apply C B measurableSet_Ioc]
    exact (measure_mono (prod_mono_right (subset_univ B))).trans_lt hunit
  have h := congrArg (fun μ : Measure ℝ ↦ μ A)
    (invariant_eq_unit_smul_volume (markedSpatialMeasure C B) hfinite)
  simpa only [markedSpatialMeasure_apply C B hA, Measure.smul_apply, smul_eq_mul,
    markedSpatialMeasure_apply C B measurableSet_Ioc, unitWindowPalm_apply C hB,
    mul_comm] using h

end OTSelector.PointProcess
