import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.Independence.Basic
import OTSelector.Basic.Model

/-!
# Probability laws for the rank-scaled model

The finite feedback argument uses points `(nT,U)` with `T,U` independent uniform variables on the
unit interval.  This module keeps that law below the assumption layer so feedback regularity can
use it without importing `EFE2`.
-/

open MeasureTheory ProbabilityTheory

namespace OTSelector

/-- Uniform probability measure on the closed unit interval. -/
noncomputable def unitUniform : ProbabilityMeasure UnitMark :=
  ⟨volume, inferInstance⟩

/-- Scale a unit-interval height into a rank coordinate of width `width`. -/
def rankCoordinateMap (width : ℝ) (t : UnitMark) : ℝ :=
  width * (t : ℝ)

theorem measurable_rankCoordinateMap (width : ℝ) : Measurable (rankCoordinateMap width) := by
  exact measurable_const.mul continuous_subtype_val.measurable

/-- Uniform rank coordinate obtained by scaling a uniform unit height. -/
noncomputable def rankCoordinateLaw (width : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map unitUniform (measurable_rankCoordinateMap width).aemeasurable

theorem rankCoordinateLaw_apply_Iic (width : ℝ) (hwidth : 0 < width) (q : UnitMark) :
    (rankCoordinateLaw width : Measure ℝ) (Set.Iic (width * (q : ℝ))) =
      ENNReal.ofReal (q : ℝ) := by
  rw [rankCoordinateLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_rankCoordinateMap width) measurableSet_Iic]
  have hpre : rankCoordinateMap width ⁻¹' Set.Iic (width * (q : ℝ)) = Set.Iic q := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Iic, rankCoordinateMap]
    change width * (t : ℝ) ≤ width * (q : ℝ) ↔ (t : ℝ) ≤ (q : ℝ)
    exact mul_le_mul_iff_of_pos_left hwidth
  rw [hpre]
  exact unitInterval.volume_Iic q

theorem rankCoordinateLaw_apply_Iio (width : ℝ) (hwidth : 0 < width) (q : UnitMark) :
    (rankCoordinateLaw width : Measure ℝ) (Set.Iio (width * (q : ℝ))) =
      ENNReal.ofReal (q : ℝ) := by
  rw [rankCoordinateLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_rankCoordinateMap width) measurableSet_Iio]
  have hpre : rankCoordinateMap width ⁻¹' Set.Iio (width * (q : ℝ)) = Set.Iio q := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Iio, rankCoordinateMap]
    change width * (t : ℝ) < width * (q : ℝ) ↔ (t : ℝ) < (q : ℝ)
    exact mul_lt_mul_iff_of_pos_left hwidth
  rw [hpre]
  exact unitInterval.volume_Iio q

theorem rankCoordinateLaw_apply_Ici (width : ℝ) (hwidth : 0 < width) (q : UnitMark) :
    (rankCoordinateLaw width : Measure ℝ) (Set.Ici (width * (q : ℝ))) =
      ENNReal.ofReal (1 - (q : ℝ)) := by
  rw [rankCoordinateLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_rankCoordinateMap width) measurableSet_Ici]
  have hpre : rankCoordinateMap width ⁻¹' Set.Ici (width * (q : ℝ)) = Set.Ici q := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ici, rankCoordinateMap]
    change width * (q : ℝ) ≤ width * (t : ℝ) ↔ (q : ℝ) ≤ (t : ℝ)
    exact mul_le_mul_iff_of_pos_left hwidth
  rw [hpre]
  exact unitInterval.volume_Ici q

theorem rankCoordinateLaw_apply_Ioi (width : ℝ) (hwidth : 0 < width) (q : UnitMark) :
    (rankCoordinateLaw width : Measure ℝ) (Set.Ioi (width * (q : ℝ))) =
      ENNReal.ofReal (1 - (q : ℝ)) := by
  rw [rankCoordinateLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_rankCoordinateMap width) measurableSet_Ioi]
  have hpre : rankCoordinateMap width ⁻¹' Set.Ioi (width * (q : ℝ)) = Set.Ioi q := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioi, rankCoordinateMap]
    change width * (q : ℝ) < width * (t : ℝ) ↔ (q : ℝ) < (t : ℝ)
    exact mul_lt_mul_iff_of_pos_left hwidth
  rw [hpre]
  exact unitInterval.volume_Ioi q

theorem rankCoordinateLaw_real_Iic (width : ℝ) (hwidth : 0 < width) (q : UnitMark) :
    (rankCoordinateLaw width : Measure ℝ).real (Set.Iic (width * (q : ℝ))) = q := by
  rw [Measure.real, rankCoordinateLaw_apply_Iic width hwidth q,
    ENNReal.toReal_ofReal q.property.1]

theorem rankCoordinateLaw_real_Ioi (width : ℝ) (hwidth : 0 < width) (q : UnitMark) :
    (rankCoordinateLaw width : Measure ℝ).real (Set.Ioi (width * (q : ℝ))) = 1 - q := by
  rw [Measure.real, rankCoordinateLaw_apply_Ioi width hwidth q,
    ENNReal.toReal_ofReal (sub_nonneg.mpr q.property.2)]

/-- Distribution function of the scaled rank coordinate at an arbitrary point of its support. -/
theorem rankCoordinateLaw_real_Iic_of_mem (width a : ℝ) (hwidth : 0 < width)
    (ha0 : 0 ≤ a) (hawidth : a ≤ width) :
    (rankCoordinateLaw width : Measure ℝ).real (Set.Iic a) = a / width := by
  let q : UnitMark :=
    ⟨a / width, div_nonneg ha0 hwidth.le, (div_le_one₀ hwidth).mpr hawidth⟩
  have hscale : width * (q : ℝ) = a := by
    dsimp [q]
    field_simp
  calc
    (rankCoordinateLaw width : Measure ℝ).real (Set.Iic a) =
        (rankCoordinateLaw width : Measure ℝ).real (Set.Iic (width * (q : ℝ))) := by
      rw [hscale]
    _ = q := rankCoordinateLaw_real_Iic width hwidth q
    _ = a / width := rfl

/-- Upper-tail formula for the scaled rank coordinate at an arbitrary point of its support. -/
theorem rankCoordinateLaw_real_Ioi_of_mem (width a : ℝ) (hwidth : 0 < width)
    (ha0 : 0 ≤ a) (hawidth : a ≤ width) :
    (rankCoordinateLaw width : Measure ℝ).real (Set.Ioi a) = 1 - a / width := by
  let q : UnitMark :=
    ⟨a / width, div_nonneg ha0 hwidth.le, (div_le_one₀ hwidth).mpr hawidth⟩
  have hscale : width * (q : ℝ) = a := by
    dsimp [q]
    field_simp
  calc
    (rankCoordinateLaw width : Measure ℝ).real (Set.Ioi a) =
        (rankCoordinateLaw width : Measure ℝ).real (Set.Ioi (width * (q : ℝ))) := by
      rw [hscale]
    _ = 1 - q := rankCoordinateLaw_real_Ioi width hwidth q
    _ = 1 - a / width := rfl

/-- Joint rank coordinate and independent unit mark. -/
def rankStripMap (width : ℝ) (z : UnitMark × UnitMark) : ℝ × UnitMark :=
  (rankCoordinateMap width z.1, z.2)

theorem measurable_rankStripMap (width : ℝ) : Measurable (rankStripMap width) := by
  exact ((measurable_rankCoordinateMap width).comp measurable_fst).prodMk measurable_snd

/-- Probability law of one rank-scaled point `(width * T, U)`. -/
noncomputable def rankStripLaw (width : ℝ) : ProbabilityMeasure (ℝ × UnitMark) :=
  ProbabilityMeasure.map (unitUniform.prod unitUniform)
    (measurable_rankStripMap width).aemeasurable

@[simp] theorem rankStripMap_fst (width : ℝ) (z : UnitMark × UnitMark) :
    (rankStripMap width z).1 = rankCoordinateMap width z.1 :=
  rfl

@[simp] theorem rankStripMap_snd (width : ℝ) (z : UnitMark × UnitMark) :
    (rankStripMap width z).2 = z.2 :=
  rfl

/-- The height marginal of the strip law is the scaled uniform coordinate law. -/
theorem rankStripLaw_map_fst (width : ℝ) :
    (rankStripLaw width).map measurable_fst.aemeasurable = rankCoordinateLaw width := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map Prod.fst
      (Measure.map (rankStripMap width) (unitUniform.prod unitUniform : ProbabilityMeasure _)) =
    Measure.map (rankCoordinateMap width) (unitUniform : ProbabilityMeasure _)
  rw [Measure.map_map measurable_fst (measurable_rankStripMap width)]
  have hcomp : Prod.fst ∘ rankStripMap width = rankCoordinateMap width ∘ Prod.fst := by
    funext z
    rfl
  rw [hcomp]
  rw [← Measure.map_map (measurable_rankCoordinateMap width) measurable_fst]
  congr 1
  exact congrArg ProbabilityMeasure.toMeasure
    (ProbabilityMeasure.map_fst_prod unitUniform unitUniform)

/-- The mark marginal of the strip law remains uniform. -/
theorem rankStripLaw_map_snd (width : ℝ) :
    (rankStripLaw width).map measurable_snd.aemeasurable = unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map Prod.snd
      (Measure.map (rankStripMap width) (unitUniform.prod unitUniform : ProbabilityMeasure _)) =
    (unitUniform : Measure UnitMark)
  rw [Measure.map_map measurable_snd (measurable_rankStripMap width)]
  have hcomp : Prod.snd ∘ rankStripMap width = Prod.snd := by
    funext z
    rfl
  rw [hcomp]
  exact congrArg ProbabilityMeasure.toMeasure
    (ProbabilityMeasure.map_snd_prod unitUniform unitUniform)

/-- Canonical iid sample of `n` rank-scaled marked points. -/
noncomputable def rankStripSampleLaw (n : ℕ) (width : ℝ) :
    ProbabilityMeasure (Fin n → ℝ × UnitMark) :=
  ProbabilityMeasure.pi fun _ ↦ rankStripLaw width

/-- Every coordinate of the canonical strip sample has the one-point strip law. -/
theorem rankStripSampleLaw_map_eval (n : ℕ) (width : ℝ) (i : Fin n) :
    (rankStripSampleLaw n width).map (measurable_pi_apply i).aemeasurable =
      rankStripLaw width := by
  apply ProbabilityMeasure.toMeasure_injective
  exact (measurePreserving_eval (fun _ : Fin n ↦
    (rankStripLaw width : Measure (ℝ × UnitMark))) i).map_eq

/-- Coordinate evaluations of the canonical strip sample are jointly independent. -/
theorem rankStripSampleLaw_iIndep (n : ℕ) (width : ℝ) :
    iIndepFun (fun i (sample : Fin n → ℝ × UnitMark) ↦ sample i)
      (rankStripSampleLaw n width : Measure (Fin n → ℝ × UnitMark)) := by
  exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable

/-- Joint iid source/target rank-strip samples. -/
noncomputable def sourceTargetRankStripSampleLaw (n : ℕ) (width : ℝ) :
    ProbabilityMeasure
      ((Fin n → ℝ × UnitMark) × (Fin n → ℝ × UnitMark)) :=
  (rankStripSampleLaw n width).prod (rankStripSampleLaw n width)

end OTSelector
