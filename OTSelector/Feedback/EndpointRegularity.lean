import OTSelector.Feedback.EndpointGeometry
import OTSelector.Feedback.Regularity

/-!
# Nested endpoint regularity

The endpoint complements are represented by one-dimensional score half-lines.  The source score
has an explicit sentinel branch at `u = 1`, where division by `1 - u` would be invalid.  This file
also connects complemented endpoint counts to the signed defects used by the feedback argument.
-/

open MeasureTheory

namespace OTSelector.RelativeVC

/-- Source endpoint score.  At `u = 1`, membership is independent of the shear parameter, so two
sentinel values encode the always-in and always-out cases on the prescribed shear window. -/
noncomputable def sourceEndpointScore (buffer x : ℝ) (z : ℝ × UnitMark) : ℝ :=
  if (z.2 : ℝ) < 1 then
    (x - z.1) / (1 - (z.2 : ℝ))
  else if x < z.1 then -buffer / 4 else buffer / 4

/-- Target endpoint score; its denominator lies in `[1,2]`. -/
noncomputable def targetEndpointScore (x : ℝ) (z : ℝ × UnitMark) : ℝ :=
  (z.1 - x) / (1 + (z.2 : ℝ))

theorem measurable_sourceEndpointScore (buffer x : ℝ) :
    Measurable (sourceEndpointScore buffer x) := by
  have ht : Measurable (fun z : ℝ × UnitMark ↦ z.1) := measurable_fst
  have hu : Measurable (fun z : ℝ × UnitMark ↦ (z.2 : ℝ)) :=
    measurable_subtype_coe.comp measurable_snd
  exact Measurable.ite (measurableSet_lt hu measurable_const)
    ((measurable_const.sub ht).div (measurable_const.sub hu))
    (Measurable.ite (measurableSet_lt measurable_const ht) measurable_const measurable_const)

theorem measurable_targetEndpointScore (x : ℝ) : Measurable (targetEndpointScore x) := by
  have ht : Measurable (fun z : ℝ × UnitMark ↦ z.1) := measurable_fst
  have hu : Measurable (fun z : ℝ × UnitMark ↦ (z.2 : ℝ)) :=
    measurable_subtype_coe.comp measurable_snd
  exact (ht.sub measurable_const).div (measurable_const.add hu)

/-- On the endpoint shear window, source complements are strict lower score half-lines. -/
theorem sourceEndpointComplement_eq_score_preimage {width buffer p : ℝ}
    (hbuffer : 0 < buffer) (hp : |p| ≤ buffer / 8) :
    sourceEndpointComplement width buffer p =
      sourceEndpointScore buffer (width - buffer) ⁻¹' Set.Iio p := by
  ext z
  change width - buffer < z.1 + p * (1 - (z.2 : ℝ)) ↔
    sourceEndpointScore buffer (width - buffer) z < p
  by_cases hu : (z.2 : ℝ) < 1
  · rw [sourceEndpointScore, ite_eq_left hu]
    have hdenom : 0 < 1 - (z.2 : ℝ) := sub_pos.mpr hu
    rw [div_lt_iff₀ hdenom]
    constructor <;> intro h <;> linarith
  · have hueq : (z.2 : ℝ) = 1 := by
      exact le_antisymm z.2.property.2 (not_lt.mp hu)
    by_cases hx : width - buffer < z.1
    · have hsentinel : -buffer / 4 < p := by
        have hp_lower := neg_le_of_abs_le hp
        linarith
      simp [sourceEndpointScore, hueq, hx, hsentinel]
    · have hsentinel : ¬buffer / 4 < p := by
        have hp_upper := le_of_abs_le hp
        linarith
      simp [sourceEndpointScore, hueq, hx, hsentinel]

/-- Target complements are strict upper score half-lines. -/
theorem targetEndpointComplement_eq_score_preimage (width buffer p : ℝ) :
    targetEndpointComplement width buffer p =
      targetEndpointScore (width - buffer) ⁻¹' Set.Ioi p := by
  ext z
  have hdenom : 0 < 1 + (z.2 : ℝ) := by linarith [z.2.property.1]
  change width - buffer < z.1 - p * (1 + (z.2 : ℝ)) ↔
    p < (z.1 - (width - buffer)) / (1 + (z.2 : ℝ))
  rw [lt_div_iff₀ hdenom]
  constructor <;> intro h <;> linarith

/-- Centered count of a source complement. -/
noncomputable def sourceComplementDefect
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (xs : Fin m → ℝ × UnitMark) (p x : ℝ) : ℝ :=
  centeredErrorSum P (sourceCutComplementEval (p, x)) falseCutTarget xs

/-- Centered count of a target complement. -/
noncomputable def targetComplementDefect
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (xs : Fin m → ℝ × UnitMark) (p x : ℝ) : ℝ :=
  centeredErrorSum P (targetCutComplementEval (p, x)) falseCutTarget xs

/-- A cut defect is the negative of its complement's centered count. -/
theorem sourceCutDefect_eq_neg_complementDefect
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (xs : Fin m → ℝ × UnitMark) (p x : ℝ) :
    sourceCutDefect P xs p x = -sourceComplementDefect P xs p x := by
  rw [sourceCutDefect_eq_centeredErrorSum, sourceComplementDefect]
  change centeredErrorSum P (sourceCutEval (p, x)) falseCutTarget xs =
    -centeredErrorSum P (boolNotConcept (sourceCutEval (p, x))) falseCutTarget xs
  rw [centeredErrorSum_boolNot_false P (sourceCutEval (p, x))
    (measurable_sourceCutClass _ ⟨p, x, rfl⟩) xs]
  ring

/-- Target analogue of `sourceCutDefect_eq_neg_complementDefect`. -/
theorem targetCutDefect_eq_neg_complementDefect
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (xs : Fin m → ℝ × UnitMark) (p x : ℝ) :
    targetCutDefect P xs p x = -targetComplementDefect P xs p x := by
  rw [targetCutDefect_eq_centeredErrorSum, targetComplementDefect]
  change centeredErrorSum P (targetCutEval (p, x)) falseCutTarget xs =
    -centeredErrorSum P (boolNotConcept (targetCutEval (p, x))) falseCutTarget xs
  rw [centeredErrorSum_boolNot_false P (targetCutEval (p, x))
    (measurable_targetCutClass _ ⟨p, x, rfl⟩) xs]
  ring

theorem abs_sourceCutDefect_eq_abs_complementDefect
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (xs : Fin m → ℝ × UnitMark) (p x : ℝ) :
    |sourceCutDefect P xs p x| = |sourceComplementDefect P xs p x| := by
  rw [sourceCutDefect_eq_neg_complementDefect, abs_neg]

theorem abs_targetCutDefect_eq_abs_complementDefect
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (xs : Fin m → ℝ × UnitMark) (p x : ℝ) :
    |targetCutDefect P xs p x| = |targetComplementDefect P xs p x| := by
  rw [targetCutDefect_eq_neg_complementDefect, abs_neg]

end OTSelector.RelativeVC
