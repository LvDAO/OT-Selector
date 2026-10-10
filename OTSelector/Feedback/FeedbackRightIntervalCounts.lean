import OTSelector.Probability.FiniteIntervalCountsGrid
import OTSelector.Feedback.FeedbackRightIntensityRawRectangle
import OTSelector.Feedback.FeedbackTerminalAreaGeometry
import OTSelector.Probability.IndependentFiberNull

/-!
# Conditional interval counts on the frozen right tail

The one-point law is the marked-square law conditioned on the actual remaining set at the
boundary.  Its normalization uses the raw boundary mass, so the boundary itself may be clipped.
Only the interval being counted must lie in the unclipped strip.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace OTSelector

/-- Every affine crossing with nonzero height coefficient has an atomless marked-square law. -/
theorem unitSquareUniform_affineHeight_singleton_eq_zero
    {n : ℕ} (hn : 0 < n) (f : UnitMark → ℝ) (hf : Measurable f) (y : ℝ) :
    (unitSquareUniform : Measure MarkedHeight)
      {z | (n : ℝ) * (z.1 : ℝ) + f z.2 = y} = 0 := by
  let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
    change NullSingletonClass (volume : Measure UnitMark)
    infer_instance
  let S : Set (UnitMark × UnitMark) :=
    {z | (n : ℝ) * (z.2 : ℝ) + f z.1 = y}
  have hS : MeasurableSet S := by
    apply measurableSet_eq_fun _ measurable_const
    exact (measurable_const.mul (measurable_subtype_coe.comp measurable_snd)).add
      (hf.comp measurable_fst)
  have hzero : ((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)) S =
      0 := by
    apply measure_prod_eq_zero_of_subsingleton_fibres hS
    intro u v hv w hw
    apply Subtype.ext
    change (n : ℝ) * (v : ℝ) + f u = y at hv
    change (n : ℝ) * (w : ℝ) + f u = y at hw
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    exact (mul_left_cancel₀ hnreal) (by linarith)
  have hpre : {z : MarkedHeight | (n : ℝ) * (z.1 : ℝ) + f z.2 = y} =
      Prod.swap ⁻¹' S := rfl
  rw [hpre, unitSquareUniform_toMeasure, ← Measure.map_apply measurable_swap hS,
    Measure.prod_swap]
  exact hzero

private theorem measureReal_phase_Ioo
    {A : Type*} [MeasurableSpace A] (ν : Measure A) [IsFiniteMeasure ν]
    (phase : A → ℝ) (hphase : Measurable phase) {s t : ℝ} (hst : s ≤ t)
    (hnull : ν {z | phase z = t} = 0) :
    ν.real (phase ⁻¹' Ioo s t) = ν.real {z | s < phase z} - ν.real {z | t < phase z} := by
  have hset : phase ⁻¹' Ioo s t =
      ({z | s < phase z} \ {z | t < phase z}) \ {z | phase z = t} := by
    ext z
    simp only [mem_preimage, mem_Ioo, mem_sdiff, mem_ofPred_eq, not_lt]
    constructor
    · intro hz
      exact ⟨⟨hz.1, hz.2.le⟩, ne_of_lt hz.2⟩
    · rintro ⟨⟨hs, ht⟩, hne⟩
      exact ⟨hs, lt_of_le_of_ne ht hne⟩
  rw [hset, measureReal_sdiff_null (by simp [measureReal_def, hnull])]
  exact measureReal_sdiff (fun _ hz ↦ hst.trans_lt hz)
    (measurableSet_lt measurable_const hphase)

namespace RightTail

/-- Source open-interval mass under the frozen one-point law, with its true boundary normalizer. -/
theorem sourceLaw_Ioo
    {n : ℕ} (hn : 0 < n) {q xR s t : ℝ} (hRs : xR ≤ s) (hst : s ≤ t)
    (hs : (s, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (ht : (t, q) ∈ FiniteSample.rightTailUnclippedRegion n) :
    ((unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]).real
      (sourcePhase n q ⁻¹' Ioo s t) =
      (t - s) / ((n : ℝ) *
        (unitSquareUniform : Measure MarkedHeight).real (sourceRawRemainingSet n q xR)) := by
  let ν := (unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]
  have hphase : Measurable (sourcePhase n q) := by unfold sourcePhase; fun_prop
  have hnull : ν {z | sourcePhase n q z = t} = 0 := by
    apply cond_absolutelyContinuous
    exact unitSquareUniform_affineHeight_singleton_eq_zero hn
      (fun u ↦ q * (1 - (u : ℝ))) (by fun_prop) t
  have hmass (y : ℝ) (hRy : xR ≤ y)
      (hy : (y, q) ∈ FiniteSample.rightTailUnclippedRegion n) :
      ν.real {z | y < sourcePhase n q z} = sourceUnclippedRemainingMass n q y /
        ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
          (sourceRawRemainingSet n q xR)) := by
    have hsection := FiniteSample.sourceBoundary_mem_Ioo_of_rightTailUnclippedRegion hy
    change ((unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]).real
      (sourceRawRemainingSet n q y) = _
    rw [unitSquareUniform_cond_sourceRemaining_real n q xR y hRy,
      unitSquareUniform_sourceRawRemainingSet hn
        (fun u ↦ (hsection u).1.le) (fun u ↦ (hsection u).2.le)]
    ring
  change ν.real _ = _
  rw [measureReal_phase_Ioo ν (sourcePhase n q) hphase hst hnull,
    hmass s hRs hs, hmass t (hRs.trans hst) ht, ← sub_div]
  congr 1
  unfold sourceUnclippedRemainingMass
  ring

/-- The symmetric target mass formula, also allowing a clipped initial boundary. -/
theorem targetLaw_Ioo
    {n : ℕ} (hn : 0 < n) {q xR s t : ℝ} (hRs : xR ≤ s) (hst : s ≤ t)
    (hs : (s, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (ht : (t, q) ∈ FiniteSample.rightTailUnclippedRegion n) :
    ((unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]).real
      (targetPhase n q ⁻¹' Ioo s t) =
      (t - s) / ((n : ℝ) *
        (unitSquareUniform : Measure MarkedHeight).real (targetRawRemainingSet n q xR)) := by
  let ν := (unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]
  have hphase : Measurable (targetPhase n q) := by unfold targetPhase; fun_prop
  have hnull : ν {z | targetPhase n q z = t} = 0 := by
    apply cond_absolutelyContinuous
    simpa [targetPhase, sub_eq_add_neg] using
      unitSquareUniform_affineHeight_singleton_eq_zero hn
        (fun u ↦ -(q * (1 + (u : ℝ)))) (by fun_prop) t
  have hmass (y : ℝ) (hRy : xR ≤ y)
      (hy : (y, q) ∈ FiniteSample.rightTailUnclippedRegion n) :
      ν.real {z | y < targetPhase n q z} = targetUnclippedRemainingMass n q y /
        ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
          (targetRawRemainingSet n q xR)) := by
    have hsection := FiniteSample.targetBoundary_mem_Ioo_of_rightTailUnclippedRegion hy
    change ((unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]).real
      (targetRawRemainingSet n q y) = _
    rw [unitSquareUniform_cond_targetRemaining_real n q xR y hRy,
      unitSquareUniform_targetRawRemainingSet hn
        (fun u ↦ (hsection u).1.le) (fun u ↦ (hsection u).2.le)]
    ring
  change ν.real _ = _
  rw [measureReal_phase_Ioo ν (targetPhase n q) hphase hst hnull,
    hmass s hRs hs, hmass t (hRs.trans hst) ht, ← sub_div]
  congr 1
  unfold targetUnclippedRemainingMass
  ring

/-- Uniform source interval grid bound under the genuine conditioned one-point product law. -/
theorem sourceLaw_grid_failure_le
    {n m N : ℕ} (hn : 0 < n) {q xR hi c r : ℝ}
    (hpositive : 0 < (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n q xR))
    (hstrip : ∀ u ∈ Icc xR hi, (u, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (hdensity : 2 * c * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n q xR)) ≤ m) (hr : 0 < r) :
    Measure.pi (fun _ : Fin m ↦
        (unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR])
      {sample | ¬FiniteIntervalCounts.gridGood N (sourcePhase n q) xR hi c r sample} ≤
      ((N + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp (-r / 12)) := by
  let P := (unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]
  have : IsProbabilityMeasure P :=
    cond_isProbabilityMeasure ((measureReal_ne_zero_iff).mp hpositive.ne')
  have hD : 0 < (n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n q xR) := mul_pos (by exact_mod_cast hn) hpositive
  apply FiniteIntervalCounts.measure_not_gridGood_pi_le P m N
    (by unfold sourcePhase; fun_prop) xR hi c hr
  intro a b hRa hab hbh
  rw [sourceLaw_Ioo hn hRa hab (hstrip _ ⟨hRa, hab.trans hbh⟩)
    (hstrip _ ⟨hRa.trans hab, hbh⟩)]
  calc
    2 * c * ((b.val : ℝ) - a.val) ≤
        ((m : ℝ) / ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
          (sourceRawRemainingSet n q xR))) * ((b.val : ℝ) - a.val) :=
      mul_le_mul_of_nonneg_right ((le_div_iff₀ hD).mpr hdensity) (sub_nonneg.mpr hab)
    _ = _ := by ring

/-- Symmetric target grid bound with its own actual boundary normalization. -/
theorem targetLaw_grid_failure_le
    {n m N : ℕ} (hn : 0 < n) {q xR hi c r : ℝ}
    (hpositive : 0 < (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSet n q xR))
    (hstrip : ∀ u ∈ Icc xR hi, (u, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    (hdensity : 2 * c * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSet n q xR)) ≤ m) (hr : 0 < r) :
    Measure.pi (fun _ : Fin m ↦
        (unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR])
      {sample | ¬FiniteIntervalCounts.gridGood N (targetPhase n q) xR hi c r sample} ≤
      ((N + 1 : ℕ) : ℝ≥0∞) ^ 2 * ENNReal.ofReal (2 * Real.exp (-r / 12)) := by
  let P := (unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]
  have : IsProbabilityMeasure P :=
    cond_isProbabilityMeasure ((measureReal_ne_zero_iff).mp hpositive.ne')
  have hD : 0 < (n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSet n q xR) := mul_pos (by exact_mod_cast hn) hpositive
  apply FiniteIntervalCounts.measure_not_gridGood_pi_le P m N
    (by unfold targetPhase; fun_prop) xR hi c hr
  intro a b hRa hab hbh
  rw [targetLaw_Ioo hn hRa hab (hstrip _ ⟨hRa, hab.trans hbh⟩)
    (hstrip _ ⟨hRa.trans hab, hbh⟩)]
  calc
    2 * c * ((b.val : ℝ) - a.val) ≤
        ((m : ℝ) / ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
          (targetRawRemainingSet n q xR))) * ((b.val : ℝ) - a.val) :=
      mul_le_mul_of_nonneg_right ((le_div_iff₀ hD).mpr hdensity) (sub_nonneg.mpr hab)
    _ = _ := by ring

end RightTail
end OTSelector
