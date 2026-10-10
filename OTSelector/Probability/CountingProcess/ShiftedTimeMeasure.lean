import OTSelector.Probability.CountingProcess.OccupationBound

/-!
# Shifted counting-process time measure

This file transports the counting-process time measure on a bounded `ℝ≥0` interval to Lebesgue
measure on the corresponding translated real interval.  It also records direct set-integral and
interval-integral change-of-variables formulas for real-valued functions.
-/

open Set
open scoped ENNReal NNReal MeasureTheory

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

/-- Pushing a restricted time measure along `u ↦ x0 + (u : ℝ)` gives Lebesgue measure restricted
to the corresponding translated real interval. -/
theorem map_shifted_timeMeasure_restrict (x0 : ℝ) (s t : ℝ≥0) :
    (timeMeasure.restrict (Ioc s t)).map (fun u : ℝ≥0 ↦ x0 + (u : ℝ)) =
      volume.restrict (Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ))) := by
  let shift : ℝ → ℝ := fun x ↦ x0 + x
  have hshift : MeasurableEmbedding shift :=
    (MeasurableEquiv.addLeft x0).measurableEmbedding
  have hpre : shift ⁻¹' Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)) =
      Ioc (s : ℝ) (t : ℝ) := by
    ext x
    simp [shift]
  calc
    (timeMeasure.restrict (Ioc s t)).map (fun u : ℝ≥0 ↦ x0 + (u : ℝ)) =
        Measure.map shift
          ((timeMeasure.restrict (Ioc s t)).map (fun u : ℝ≥0 ↦ (u : ℝ))) := by
      rw [Measure.map_map hshift.measurable NNReal.continuous_coe.measurable]
      rfl
    _ = Measure.map shift (volume.restrict (Ioc (s : ℝ) (t : ℝ))) := by
      rw [map_coe_timeMeasure_restrict]
    _ = volume.restrict (Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ))) := by
      rw [← hpre, ← hshift.restrict_map, map_add_left_eq_self]

/-- Integrate a measurable real function over a shifted time interval either before or after the
translation.  An `IntegrableOn` hypothesis supplies the required `AEStronglyMeasurable` condition
via `Integrable.aestronglyMeasurable`. -/
theorem integral_shifted_timeMeasure_eq_setIntegral
    (g : ℝ → ℝ) (x0 : ℝ) (s t : ℝ≥0)
    (hg : AEStronglyMeasurable g
      (volume.restrict (Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ))))) :
    (∫ u in Ioc s t, g (x0 + (u : ℝ)) ∂timeMeasure) =
      ∫ x in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), g x ∂volume := by
  have hshift : AEMeasurable (fun u : ℝ≥0 ↦ x0 + (u : ℝ))
      (timeMeasure.restrict (Ioc s t)) :=
    (continuous_const.add NNReal.continuous_coe).aemeasurable
  have hgmap : AEStronglyMeasurable g
      ((timeMeasure.restrict (Ioc s t)).map (fun u : ℝ≥0 ↦ x0 + (u : ℝ))) := by
    rw [map_shifted_timeMeasure_restrict]
    exact hg
  calc
    (∫ u in Ioc s t, g (x0 + (u : ℝ)) ∂timeMeasure) =
        ∫ x, g x ∂((timeMeasure.restrict (Ioc s t)).map
          (fun u : ℝ≥0 ↦ x0 + (u : ℝ))) :=
      (integral_map hshift hgmap).symm
    _ = ∫ x in Ioc (x0 + (s : ℝ)) (x0 + (t : ℝ)), g x ∂volume := by
      rw [map_shifted_timeMeasure_restrict]

/-- The shifted time-measure integral is the ordinary real interval integral over the translated
endpoints. -/
theorem integral_shifted_timeMeasure_eq_intervalIntegral
    (g : ℝ → ℝ) (x0 : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ u in Ioc s t, g (x0 + (u : ℝ)) ∂timeMeasure) =
      ∫ x in x0 + (s : ℝ)..x0 + (t : ℝ), g x := by
  rw [integral_timeMeasure_eq_intervalIntegral
    (fun u : ℝ≥0 ↦ g (x0 + (u : ℝ))) s t hst]
  calc
    (∫ x in (s : ℝ)..(t : ℝ), g (x0 + (Real.toNNReal x : ℝ))) =
        ∫ x in (s : ℝ)..(t : ℝ), g (x0 + x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by exact_mod_cast hst)] at hx
      have hx0 : 0 ≤ x := le_trans (by exact_mod_cast s.2) hx.1
      change g (x0 + (Real.toNNReal x : ℝ)) = g (x0 + x)
      rw [Real.coe_toNNReal x hx0]
    _ = ∫ x in x0 + (s : ℝ)..x0 + (t : ℝ), g x :=
      intervalIntegral.integral_comp_add_left g x0

end OTSelector.CountingProcess
