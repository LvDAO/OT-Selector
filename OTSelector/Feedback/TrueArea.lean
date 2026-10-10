import OTSelector.Feedback.FeedbackHazard
import OTSelector.Feedback.SweptSets
import OTSelector.Feedback.EndpointGeometry
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# True remaining area and sweep speed

The bulk identities `n - V^±` and `1 - q/2`, `1 + 3q/2` are valid only when every vertical
section of the swept half-space lies in `(0, n)`.  Globally the compensator must use the
clipped remaining area and the corresponding sweep speed, as in the finite-dimensional
intensity route.

This file is purely deterministic.
-/

open MeasureTheory Set
open scoped ENNReal

namespace OTSelector

/-- Truncation `[z]_0^{width}`. -/
noncomputable def clipToStrip (width z : ℝ) : ℝ :=
  max 0 (min width z)

theorem clipToStrip_nonneg (width z : ℝ) :
    0 ≤ clipToStrip width z :=
  le_max_left _ _

theorem clipToStrip_le_width {width z : ℝ} (hwidth : 0 ≤ width) :
    clipToStrip width z ≤ width :=
  max_le hwidth (min_le_left _ _)

theorem clipToStrip_eq_of_mem {width z : ℝ} (hz0 : 0 ≤ z) (hzw : z ≤ width) :
    clipToStrip width z = z := by
  simp [clipToStrip, hz0, hzw]

/-- Lebesgue area of the source swept set inside the rank strip `[0, width] × [0, 1]`. -/
noncomputable def sourceSweptArea (width p x : ℝ) : ℝ :=
  ∫ u : UnitMark, clipToStrip width (sourceBoundary p x u) ∂(unitUniform : Measure UnitMark)

/-- Lebesgue area of the target swept set inside the rank strip. -/
noncomputable def targetSweptArea (width p x : ℝ) : ℝ :=
  ∫ v : UnitMark, clipToStrip width (targetBoundary p x v) ∂(unitUniform : Measure UnitMark)

/-- True source remaining area `R_-`. -/
noncomputable def sourceTrueRemaining (width p x : ℝ) : ℝ :=
  width - sourceSweptArea width p x

/-- True target remaining area `R_+`. -/
noncomputable def targetTrueRemaining (width p x : ℝ) : ℝ :=
  width - targetSweptArea width p x

theorem integrable_clipToStrip_sourceBoundary (width p x : ℝ) (hwidth : 0 ≤ width) :
    Integrable (fun u : UnitMark ↦ clipToStrip width (sourceBoundary p x u))
      (unitUniform : Measure UnitMark) := by
  have hcont : Continuous fun u : UnitMark ↦ clipToStrip width (sourceBoundary p x u) := by
    have hclip : Continuous fun z : ℝ ↦ clipToStrip width z :=
      continuous_const.max (continuous_const.min continuous_id)
    have hbound : Continuous fun u : UnitMark ↦ sourceBoundary p x u := by
      simp only [sourceBoundary]
      exact continuous_const.sub
        (continuous_const.mul (continuous_const.sub continuous_subtype_val))
    exact hclip.comp hbound
  rw [← memLp_one_iff_integrable]
  exact MemLp.of_bound hcont.aestronglyMeasurable width
    (Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (clipToStrip_nonneg _ _)]
      exact clipToStrip_le_width hwidth)

theorem integrable_clipToStrip_targetBoundary (width p x : ℝ) (hwidth : 0 ≤ width) :
    Integrable (fun v : UnitMark ↦ clipToStrip width (targetBoundary p x v))
      (unitUniform : Measure UnitMark) := by
  have hcont : Continuous fun v : UnitMark ↦ clipToStrip width (targetBoundary p x v) := by
    have hclip : Continuous fun z : ℝ ↦ clipToStrip width z :=
      continuous_const.max (continuous_const.min continuous_id)
    have hbound : Continuous fun v : UnitMark ↦ targetBoundary p x v := by
      simp only [targetBoundary]
      exact continuous_const.add
        (continuous_const.mul (continuous_const.add continuous_subtype_val))
    exact hclip.comp hbound
  rw [← memLp_one_iff_integrable]
  exact MemLp.of_bound hcont.aestronglyMeasurable width
    (Filter.Eventually.of_forall fun v ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (clipToStrip_nonneg _ _)]
      exact clipToStrip_le_width hwidth)

/-- In the unclipped bulk, the true source remaining area is `n - V^-`. -/
theorem sourceTrueRemaining_eq_sourceUnclippedRemainingMass
    {width p x : ℝ}
    (hsection0 : ∀ u : UnitMark, 0 ≤ sourceBoundary p x u)
    (hsectionW : ∀ u : UnitMark, sourceBoundary p x u ≤ width) :
    sourceTrueRemaining width p x = sourceUnclippedRemainingMass width p x := by
  dsimp [sourceTrueRemaining, sourceSweptArea, sourceUnclippedRemainingMass]
  have hclip : ∀ u : UnitMark,
      clipToStrip width (sourceBoundary p x u) = sourceBoundary p x u :=
    fun u ↦ clipToStrip_eq_of_mem (hsection0 u) (hsectionW u)
  have hcongr :
      (∫ u : UnitMark, clipToStrip width (sourceBoundary p x u)
          ∂(unitUniform : Measure UnitMark)) =
        ∫ u : UnitMark, sourceBoundary p x u ∂(unitUniform : Measure UnitMark) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hclip
  rw [hcongr]
  have havg := RelativeVC.integral_unitUniform_affine (x - p) p
  have hrewrite :
      (∫ u : UnitMark, sourceBoundary p x u ∂(unitUniform : Measure UnitMark)) =
        ∫ u : UnitMark, ((x - p) + p * (u : ℝ)) ∂(unitUniform : Measure UnitMark) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u ↦ by
      simp only [sourceBoundary]
      ring
  rw [hrewrite, havg]
  ring

/-- In the unclipped bulk, the true target remaining area is `n - V^+`. -/
theorem targetTrueRemaining_eq_targetUnclippedRemainingMass
    {width p x : ℝ}
    (hsection0 : ∀ v : UnitMark, 0 ≤ targetBoundary p x v)
    (hsectionW : ∀ v : UnitMark, targetBoundary p x v ≤ width) :
    targetTrueRemaining width p x = targetUnclippedRemainingMass width p x := by
  dsimp [targetTrueRemaining, targetSweptArea, targetUnclippedRemainingMass]
  have hclip : ∀ v : UnitMark,
      clipToStrip width (targetBoundary p x v) = targetBoundary p x v :=
    fun v ↦ clipToStrip_eq_of_mem (hsection0 v) (hsectionW v)
  have hcongr :
      (∫ v : UnitMark, clipToStrip width (targetBoundary p x v)
          ∂(unitUniform : Measure UnitMark)) =
        ∫ v : UnitMark, targetBoundary p x v ∂(unitUniform : Measure UnitMark) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hclip
  rw [hcongr]
  have havg := RelativeVC.integral_unitUniform_affine (x + p) p
  have hrewrite :
      (∫ v : UnitMark, targetBoundary p x v ∂(unitUniform : Measure UnitMark)) =
        ∫ v : UnitMark, ((x + p) + p * (v : ℝ)) ∂(unitUniform : Measure UnitMark) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v ↦ by
      simp only [targetBoundary]
      ring
  rw [hrewrite, havg]
  ring

/-- Source sweep-rate formula using strict interior sections.  At clipping kinks this definition
does not claim to be a pointwise derivative. -/
noncomputable def sourceSweepSpeed (width p x q : ℝ) : ℝ :=
  ∫ u : UnitMark,
    (if 0 < sourceBoundary p x u ∧ sourceBoundary p x u < width then
      sourceMarkedFactor q u else 0)
    ∂(unitUniform : Measure UnitMark)

/-- Target sweep-rate formula using strict interior sections.  At clipping kinks this definition
does not claim to be a pointwise derivative. -/
noncomputable def targetSweepSpeed (width p x q : ℝ) : ℝ :=
  ∫ v : UnitMark,
    (if 0 < targetBoundary p x v ∧ targetBoundary p x v < width then
      targetMarkedFactor q v else 0)
    ∂(unitUniform : Measure UnitMark)

theorem integrable_sourceSweepIntegrand (width p x q : ℝ) :
    Integrable (fun u : UnitMark ↦
      (if 0 < sourceBoundary p x u ∧ sourceBoundary p x u < width then
        sourceMarkedFactor q u else 0))
      (unitUniform : Measure UnitMark) := by
  have hset : MeasurableSet
      {u : UnitMark | 0 < sourceBoundary p x u ∧ sourceBoundary p x u < width} := by
    have hb : Continuous fun u : UnitMark ↦ sourceBoundary p x u := by
      simp only [sourceBoundary]
      exact continuous_const.sub
        (continuous_const.mul (continuous_const.sub continuous_subtype_val))
    exact (isOpen_lt continuous_const hb).measurableSet.inter
      (isOpen_lt hb continuous_const).measurableSet
  have hf : Measurable fun u : UnitMark ↦
      (if 0 < sourceBoundary p x u ∧ sourceBoundary p x u < width then
        sourceMarkedFactor q u else 0) :=
    Measurable.ite hset
      (measurable_const.sub (measurable_const.mul
        (measurable_const.sub measurable_subtype_coe)))
      measurable_const
  rw [← memLp_one_iff_integrable]
  refine MemLp.of_bound hf.aestronglyMeasurable (1 + |q|) ?_
  refine Filter.Eventually.of_forall fun u ↦ ?_
  simp only [Real.norm_eq_abs]
  split_ifs with hu
  · simp only [sourceMarkedFactor]
    have hu0 : 0 ≤ (u : ℝ) := u.property.1
    have hu1 : (u : ℝ) ≤ 1 := u.property.2
    have h1u : |1 - (u : ℝ)| = 1 - u := abs_of_nonneg (sub_nonneg.mpr hu1)
    calc
      |1 - q * (1 - (u : ℝ))| ≤ |1| + |q * (1 - (u : ℝ))| := abs_sub _ _
      _ = 1 + |q| * |1 - (u : ℝ)| := by rw [abs_one, abs_mul]
      _ = 1 + |q| * (1 - (u : ℝ)) := by rw [h1u]
      _ ≤ 1 + |q| * 1 := by
        have hmul : |q| * (1 - (u : ℝ)) ≤ |q| * 1 :=
          mul_le_mul_of_nonneg_left (sub_le_self (1 : ℝ) hu0) (abs_nonneg q)
        linarith
      _ = 1 + |q| := by simp
  · simpa [abs_zero] using add_nonneg (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg q)

/-- Unclipped interior: every section is strictly inside `(0, width)`, so the source
sweep speed is exactly `1 - q/2`. -/
theorem sourceSweepSpeed_eq_sourceFactor
    {width p x q : ℝ}
    (hsection0 : ∀ u : UnitMark, 0 < sourceBoundary p x u)
    (hsectionW : ∀ u : UnitMark, sourceBoundary p x u < width) :
    sourceSweepSpeed width p x q = 1 - q / 2 := by
  rw [sourceSweepSpeed, ← integral_sourceMarkedFactor q]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u ↦ by
    simp [hsection0 u, hsectionW u]

/-- Unclipped interior: the target sweep speed is exactly `1 + 3q/2`. -/
theorem targetSweepSpeed_eq_targetFactor
    {width p x q : ℝ}
    (hsection0 : ∀ v : UnitMark, 0 < targetBoundary p x v)
    (hsectionW : ∀ v : UnitMark, targetBoundary p x v < width) :
    targetSweepSpeed width p x q = 1 + 3 * q / 2 := by
  rw [targetSweepSpeed, ← integral_targetMarkedFactor q]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v ↦ by
    simp [hsection0 v, hsectionW v]

/-- Remaining-region form of the source complement, as a subset of the rank strip. -/
def sourceRemainingSet (width : ℝ) (g : ℝ → ℝ) (x : ℝ) : Set (ℝ × UnitMark) :=
  (Icc (0 : ℝ) width ×ˢ (univ : Set UnitMark)) ∩ (sourceSwept g x)ᶜ

/-- Remaining-region form of the target complement, as a subset of the rank strip. -/
def targetRemainingSet (width : ℝ) (g : ℝ → ℝ) (x : ℝ) : Set (ℝ × UnitMark) :=
  (Icc (0 : ℝ) width ×ˢ (univ : Set UnitMark)) ∩ (targetSwept g x)ᶜ

theorem sourceRemainingSet_eq_complement_strip (width : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    sourceRemainingSet width g x =
      (Icc (0 : ℝ) width ×ˢ (univ : Set UnitMark)) ∩
        RelativeVC.sourceCutComplementSet (g x) x := by
  ext z
  simp only [sourceRemainingSet, sourceSwept, RelativeVC.sourceCutComplementSet,
    mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_le]

theorem targetRemainingSet_eq_complement_strip (width : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    targetRemainingSet width g x =
      (Icc (0 : ℝ) width ×ˢ (univ : Set UnitMark)) ∩
        RelativeVC.targetCutComplementSet (g x) x := by
  ext z
  simp only [targetRemainingSet, targetSwept, RelativeVC.targetCutComplementSet,
    mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_le]

/-- Algebraic intensity from a nonnegative remaining-label count, remaining area, and sweep
speed.  The zero convention covers exhausted labels and zero remaining area; this definition
does not assert that any concrete counting process has this intensity. -/
noncomputable def remainingLabelIntensity (k R c : ℝ) : ℝ :=
  if k ≤ 0 ∨ R ≤ 0 then 0 else k / R * c

theorem remainingLabelIntensity_nonneg {k R c : ℝ}
    (hk : 0 ≤ k) (hR : 0 ≤ R) (hc : 0 ≤ c) :
    0 ≤ remainingLabelIntensity k R c := by
  dsimp [remainingLabelIntensity]
  split_ifs with h
  · exact le_rfl
  · exact mul_nonneg (div_nonneg hk hR) hc

end OTSelector
