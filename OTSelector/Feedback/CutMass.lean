import OTSelector.Basic.ModelLaw
import OTSelector.Feedback.EndpointTail

/-!
# Exact rank-strip cut masses and the current/defect identity

The A2 argument uses more than concentration: it needs the exact population masses of the two
affine swept half-spaces.  This file computes those masses under the rank-strip law, then derives
the pathwise identity

`2 p = DeltaMinus(p,x) - DeltaPlus(p,x) - K(p,x)`.

The endpoint hypotheses below say that every affine vertical section stays inside `[0,width]`.
They are satisfied on the bulk rectangle used in `main.tex`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace OTSelector.RelativeVC

/-- The source classification error set is exactly its affine swept half-space. -/
theorem sourceCutErrorSet_eq_swept (p x : ℝ) :
    errorSet (sourceCutEval (p, x)) falseCutTarget = sourceSwept (fun _ ↦ p) x := by
  ext z
  simp [errorSet, sourceCutEval, falseCutTarget, sourceSwept]

/-- The target classification error set is exactly its affine swept half-space. -/
theorem targetCutErrorSet_eq_swept (p x : ℝ) :
    errorSet (targetCutEval (p, x)) falseCutTarget = targetSwept (fun _ ↦ p) x := by
  ext z
  simp [errorSet, targetCutEval, falseCutTarget, targetSwept]

/-- Average of an affine function over the unit mark. -/
theorem integral_unitUniform_affine (a b : ℝ) :
    ∫ u : UnitMark, (a + b * (u : ℝ)) ∂(unitUniform : Measure UnitMark) = a + b / 2 := by
  change ∫ u : UnitMark, (a + b * (u : ℝ)) ∂volume = a + b / 2
  have hsub : (∫ u : UnitMark, (a + b * (u : ℝ)) ∂volume) =
      ∫ u : ℝ in Icc 0 1, (a + b * u) := by
    simpa only [UnitMark] using
      (integral_subtype (G := ℝ) (s := Icc (0 : ℝ) 1) measurableSet_Icc
        (fun u : ℝ ↦ a + b * u))
  rw [hsub]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have ha : IntervalIntegrable (fun _ : ℝ ↦ a) volume 0 1 := intervalIntegrable_const
  have hb : IntervalIntegrable (fun u : ℝ ↦ b * u) volume 0 1 :=
    continuousOn_id.intervalIntegrable.const_mul b
  rw [intervalIntegral.integral_add ha hb, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id]
  ring

/-- The source swept mass is `(x-p/2)/width` whenever all vertical sections remain inside the
rank strip. -/
theorem rankStripLaw_real_sourceCut
    {width p x : ℝ} (hwidth : 0 < width)
    (hsection0 : ∀ u : UnitMark, 0 ≤ x - p * (1 - (u : ℝ)))
    (hsectionW : ∀ u : UnitMark, x - p * (1 - (u : ℝ)) ≤ width) :
    (rankStripLaw width : Measure (ℝ × UnitMark)).real
        (errorSet (sourceCutEval (p, x)) falseCutTarget) =
      (x - p / 2) / width := by
  rw [sourceCutErrorSet_eq_swept, rankStripLaw_eq_rankCoordinateLaw_prod]
  have hmeas : MeasurableSet (sourceSwept (fun _ ↦ p) x) := by
    rw [← sourceCutErrorSet_eq_swept]
    exact measurableSet_errorSet
      (measurable_sourceCutClass _ ⟨p, x, rfl⟩) measurable_falseCutTarget
  rw [Measure.real, Measure.prod_apply_symm hmeas]
  have hsection : ∀ u : UnitMark,
      (rankCoordinateLaw width : Measure ℝ)
          ((fun t : ℝ ↦ (t, u)) ⁻¹' sourceSwept (fun _ ↦ p) x) =
        ENNReal.ofReal ((x - p * (1 - (u : ℝ))) / width) := by
    intro u
    have hset : ((fun t : ℝ ↦ (t, u)) ⁻¹' sourceSwept (fun _ ↦ p) x) =
        Iic (x - p * (1 - (u : ℝ))) := by
      ext t
      change t + p * (1 - (u : ℝ)) ≤ x ↔ t ≤ x - p * (1 - (u : ℝ))
      constructor <;> intro ht <;> linarith
    rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    congr 1
    simpa [Measure.real] using
      rankCoordinateLaw_real_Iic_of_mem width _ hwidth (hsection0 u) (hsectionW u)
  simp_rw [hsection]
  let q : UnitMark → ℝ := fun u ↦ (x - p * (1 - (u : ℝ))) / width
  let qnn : UnitMark → ℝ≥0 := fun u ↦ Real.toNNReal (q u)
  have hq0 : ∀ u, 0 ≤ q u := fun u ↦ div_nonneg (hsection0 u) hwidth.le
  have hq1 : ∀ u, q u ≤ 1 := fun u ↦ by
    dsimp [q]
    exact (div_le_one₀ hwidth).mpr (hsectionW u)
  have hqint : Integrable (fun u ↦ (qnn u : ℝ)) (unitUniform : Measure UnitMark) := by
    refine Integrable.of_bound ?_ 1 ?_
    · have hmeasq : StronglyMeasurable q := by
        exact ((continuous_const.sub
          (continuous_const.mul (continuous_const.sub continuous_subtype_val))).div_const _)
          |>.stronglyMeasurable
      exact hmeasq.aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun u ↦ by simp [qnn, Real.coe_toNNReal _ (hq0 u)])
    · exact Filter.Eventually.of_forall fun u ↦ by
        rw [Real.norm_eq_abs, Real.coe_toNNReal _ (hq0 u), abs_of_nonneg (hq0 u)]
        exact hq1 u
  have hlin : (∫⁻ u : UnitMark, ENNReal.ofReal (q u) ∂(unitUniform : Measure UnitMark)) =
      ENNReal.ofReal ((x - p / 2) / width) := by
    have hcoe : (fun u : UnitMark ↦ ENNReal.ofReal (q u)) =
        fun u ↦ (qnn u : ℝ≥0∞) := by
      funext u
      rfl
    rw [hcoe, lintegral_coe_eq_integral qnn hqint]
    congr 1
    simp only [qnn, Real.coe_toNNReal _ (hq0 _)]
    have havg := integral_unitUniform_affine ((x - p) / width) (p / width)
    calc
      ∫ u : UnitMark, q u ∂(unitUniform : Measure UnitMark) =
          ∫ u : UnitMark, ((x - p) / width + (p / width) * (u : ℝ))
              ∂(unitUniform : Measure UnitMark) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun u ↦ by
              dsimp [q]
              field_simp [hwidth.ne']; ring
      _ = (x - p) / width + (p / width) / 2 := havg
      _ = (x - p / 2) / width := by field_simp [hwidth.ne']; ring
  rw [hlin, ENNReal.toReal_ofReal]
  have havg_nonneg : 0 ≤ (x - p / 2) / width := by
    have h0 := hsection0 ⟨1 / 2, by constructor <;> norm_num⟩
    have hrewrite : x - p * (1 - (1 / 2 : ℝ)) = x - p / 2 := by ring
    rw [hrewrite] at h0
    exact div_nonneg h0 hwidth.le
  exact havg_nonneg

/-- The target swept mass is `(x+3p/2)/width` whenever all vertical sections remain inside the
rank strip. -/
theorem rankStripLaw_real_targetCut
    {width p x : ℝ} (hwidth : 0 < width)
    (hsection0 : ∀ v : UnitMark, 0 ≤ x + p * (1 + (v : ℝ)))
    (hsectionW : ∀ v : UnitMark, x + p * (1 + (v : ℝ)) ≤ width) :
    (rankStripLaw width : Measure (ℝ × UnitMark)).real
        (errorSet (targetCutEval (p, x)) falseCutTarget) =
      (x + 3 * p / 2) / width := by
  rw [targetCutErrorSet_eq_swept, rankStripLaw_eq_rankCoordinateLaw_prod]
  have hmeas : MeasurableSet (targetSwept (fun _ ↦ p) x) := by
    rw [← targetCutErrorSet_eq_swept]
    exact measurableSet_errorSet
      (measurable_targetCutClass _ ⟨p, x, rfl⟩) measurable_falseCutTarget
  rw [Measure.real, Measure.prod_apply_symm hmeas]
  have hsection : ∀ v : UnitMark,
      (rankCoordinateLaw width : Measure ℝ)
          ((fun t : ℝ ↦ (t, v)) ⁻¹' targetSwept (fun _ ↦ p) x) =
        ENNReal.ofReal ((x + p * (1 + (v : ℝ))) / width) := by
    intro v
    have hset : ((fun t : ℝ ↦ (t, v)) ⁻¹' targetSwept (fun _ ↦ p) x) =
        Iic (x + p * (1 + (v : ℝ))) := by
      ext t
      change t - p * (1 + (v : ℝ)) ≤ x ↔ t ≤ x + p * (1 + (v : ℝ))
      constructor <;> intro ht <;> linarith
    rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    congr 1
    simpa [Measure.real] using
      rankCoordinateLaw_real_Iic_of_mem width _ hwidth (hsection0 v) (hsectionW v)
  simp_rw [hsection]
  let q : UnitMark → ℝ := fun v ↦ (x + p * (1 + (v : ℝ))) / width
  let qnn : UnitMark → ℝ≥0 := fun v ↦ Real.toNNReal (q v)
  have hq0 : ∀ v, 0 ≤ q v := fun v ↦ div_nonneg (hsection0 v) hwidth.le
  have hq1 : ∀ v, q v ≤ 1 := fun v ↦ by
    dsimp [q]
    exact (div_le_one₀ hwidth).mpr (hsectionW v)
  have hqint : Integrable (fun v ↦ (qnn v : ℝ)) (unitUniform : Measure UnitMark) := by
    refine Integrable.of_bound ?_ 1 ?_
    · have hmeasq : StronglyMeasurable q := by
        exact ((continuous_const.add
          (continuous_const.mul (continuous_const.add continuous_subtype_val))).div_const _)
          |>.stronglyMeasurable
      exact hmeasq.aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun v ↦ by simp [qnn, Real.coe_toNNReal _ (hq0 v)])
    · exact Filter.Eventually.of_forall fun v ↦ by
        rw [Real.norm_eq_abs, Real.coe_toNNReal _ (hq0 v), abs_of_nonneg (hq0 v)]
        exact hq1 v
  have hlin : (∫⁻ v : UnitMark, ENNReal.ofReal (q v) ∂(unitUniform : Measure UnitMark)) =
      ENNReal.ofReal ((x + 3 * p / 2) / width) := by
    have hcoe : (fun v : UnitMark ↦ ENNReal.ofReal (q v)) =
        fun v ↦ (qnn v : ℝ≥0∞) := by
      funext v
      rfl
    rw [hcoe, lintegral_coe_eq_integral qnn hqint]
    congr 1
    simp only [qnn, Real.coe_toNNReal _ (hq0 _)]
    have havg := integral_unitUniform_affine ((x + p) / width) (p / width)
    calc
      ∫ v : UnitMark, q v ∂(unitUniform : Measure UnitMark) =
          ∫ v : UnitMark, ((x + p) / width + (p / width) * (v : ℝ))
              ∂(unitUniform : Measure UnitMark) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun v ↦ by
              dsimp [q]
              field_simp [hwidth.ne']; ring
      _ = (x + p) / width + (p / width) / 2 := havg
      _ = (x + 3 * p / 2) / width := by field_simp [hwidth.ne']; ring
  rw [hlin, ENNReal.toReal_ofReal]
  have havg_nonneg : 0 ≤ (x + 3 * p / 2) / width := by
    have h0 := hsection0 ⟨1 / 2, by constructor <;> norm_num⟩
    have hrewrite : x + p * (1 + (1 / 2 : ℝ)) = x + 3 * p / 2 := by ring
    rw [hrewrite] at h0
    exact div_nonneg h0 hwidth.le
  exact havg_nonneg

/-- Rank discrepancy along a deterministic curve, on the real count scale. -/
noncomputable def feedbackRankDiscrepancy {n : ℕ}
    (source target : Fin n → ℝ × UnitMark) (p x : ℝ) : ℝ :=
  sourceCutCount source p x - targetCutCount target p x

/-- Exact identity (1.29), once the two affine vertical sections stay inside the rank strip. -/
theorem two_mul_eq_sourceDefect_sub_targetDefect_sub_feedbackRankDiscrepancy
    {n : ℕ} (hn : 0 < n)
    (source target : Fin n → ℝ × UnitMark) {p x : ℝ}
    (hsource0 : ∀ u : UnitMark, 0 ≤ x - p * (1 - (u : ℝ)))
    (hsourceN : ∀ u : UnitMark, x - p * (1 - (u : ℝ)) ≤ n)
    (htarget0 : ∀ v : UnitMark, 0 ≤ x + p * (1 + (v : ℝ)))
    (htargetN : ∀ v : UnitMark, x + p * (1 + (v : ℝ)) ≤ n) :
    2 * p =
      sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) source p x -
        targetCutDefect (rankStripLaw n : Measure (ℝ × UnitMark)) target p x -
          feedbackRankDiscrepancy source target p x := by
  have hs := rankStripLaw_real_sourceCut (width := (n : ℝ))
    (by exact_mod_cast hn) hsource0 (by simpa using hsourceN)
  have ht := rankStripLaw_real_targetCut (width := (n : ℝ))
    (by exact_mod_cast hn) htarget0 (by simpa using htargetN)
  rw [sourceCutDefect, targetCutDefect, feedbackRankDiscrepancy, hs, ht]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

end OTSelector.RelativeVC
