import OTSelector.Feedback.FeedbackRightBoundaryScalar
import OTSelector.Feedback.TrueArea

/-!
# Frozen right-tail areas, including clipped sections

This deterministic layer controls the actual remaining probabilities after the right boundary.
The height is frozen, but the later cut is allowed to pass the strip endpoint.  Consequently the
proof uses clipped vertical sections rather than the bulk affine area formula at later cuts.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace OTSelector

theorem clipToStrip_abs_sub_le (width x y : ℝ) :
    |clipToStrip width x - clipToStrip width y| ≤ |x - y| := by
  have h : LipschitzWith 1 (clipToStrip width) :=
    (LipschitzWith.id.const_min width).const_max 0
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul x y

/-- The scaled uniform upper tail at an arbitrary threshold, including both clipped tails. -/
theorem rankCoordinateLaw_real_Ioi_clipped
    (width a : ℝ) (hwidth : 0 < width) :
    (rankCoordinateLaw width : Measure ℝ).real (Ioi a) =
      1 - clipToStrip width a / width := by
  by_cases ha0 : 0 ≤ a
  · by_cases haw : a ≤ width
    · rw [clipToStrip_eq_of_mem ha0 haw]
      exact rankCoordinateLaw_real_Ioi_of_mem width a hwidth ha0 haw
    · have hwa : width < a := lt_of_not_ge haw
      have hpre : rankCoordinateMap width ⁻¹' Ioi a = ∅ := by
        ext t
        simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false]
        change ¬a < width * (t : ℝ)
        have ht := mul_le_mul_of_nonneg_left t.property.2 hwidth.le
        linarith
      rw [Measure.real, rankCoordinateLaw, ProbabilityMeasure.toMeasure_map,
        Measure.map_apply (measurable_rankCoordinateMap width) measurableSet_Ioi, hpre]
      simp [clipToStrip, min_eq_left hwa.le, max_eq_right hwidth.le, hwidth.ne']
  · have ha : a < 0 := lt_of_not_ge ha0
    have hpre : rankCoordinateMap width ⁻¹' Ioi a = univ := by
      ext t
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      change a < width * (t : ℝ)
      exact ha.trans_le (mul_nonneg hwidth.le t.property.1)
    rw [Measure.real, rankCoordinateLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (measurable_rankCoordinateMap width) measurableSet_Ioi, hpre]
    simp [clipToStrip, min_eq_right (ha.le.trans hwidth.le), max_eq_left ha.le]

/-- Fubini's formula for the mass above a measurable graph in the uniform rank strip. -/
theorem unitSquareUniform_real_above_graph
    {n : ℕ} (hn : 0 < n) (f : UnitMark → ℝ) (hf : Measurable f) :
    (unitSquareUniform : Measure MarkedHeight).real
        {z | f z.2 < (n : ℝ) * (z.1 : ℝ)} =
      ∫ u : UnitMark, (1 - clipToStrip n (f u) / n)
        ∂(unitUniform : Measure UnitMark) := by
  let A : Set MarkedHeight := {z | f z.2 < (n : ℝ) * (z.1 : ℝ)}
  have hA : MeasurableSet A :=
    measurableSet_lt (hf.comp measurable_snd)
      (measurable_const.mul (measurable_subtype_coe.comp measurable_fst))
  change (((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)) A).toReal = _
  rw [Measure.prod_apply_symm hA, ← integral_toReal
    (measurable_measure_prodMk_right hA).aemeasurable
    (Filter.Eventually.of_forall fun _ ↦ measure_lt_top _ _)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun u ↦ ?_
  have hmass : (unitUniform : Measure UnitMark) ((fun t ↦ (t, u)) ⁻¹' A) =
      (rankCoordinateLaw n : Measure ℝ) (Ioi (f u)) := by
    rw [rankCoordinateLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (measurable_rankCoordinateMap (n : ℝ)) measurableSet_Ioi]
    rfl
  change ((unitUniform : Measure UnitMark) ((fun t ↦ (t, u)) ⁻¹' A)).toReal = _
  rw [hmass]
  exact rankCoordinateLaw_real_Ioi_clipped n (f u) (by exact_mod_cast hn)

theorem unitSquareUniform_real_sourceRawRemainingSet_clipped
    {n : ℕ} (hn : 0 < n) (q y : ℝ) :
    (unitSquareUniform : Measure MarkedHeight).real (sourceRawRemainingSet n q y) =
      ∫ u : UnitMark, (1 - clipToStrip n (sourceBoundary q y u) / n)
        ∂(unitUniform : Measure UnitMark) := by
  have hf : Measurable fun u : UnitMark ↦ sourceBoundary q y u := by
    unfold sourceBoundary
    fun_prop
  convert unitSquareUniform_real_above_graph hn
    (fun u : UnitMark ↦ sourceBoundary q y u) hf using 2
  ext z
  simp only [sourceRawRemainingSet, mem_ofPred_eq, sourceBoundary]
  constructor <;> intro hz <;> linarith

theorem unitSquareUniform_real_targetRawRemainingSet_clipped
    {n : ℕ} (hn : 0 < n) (q y : ℝ) :
    (unitSquareUniform : Measure MarkedHeight).real (targetRawRemainingSet n q y) =
      ∫ u : UnitMark, (1 - clipToStrip n (targetBoundary q y u) / n)
        ∂(unitUniform : Measure UnitMark) := by
  have hf : Measurable fun u : UnitMark ↦ targetBoundary q y u := by
    unfold targetBoundary
    fun_prop
  convert unitSquareUniform_real_above_graph hn
    (fun u : UnitMark ↦ targetBoundary q y u) hf using 2
  ext z
  simp only [targetRawRemainingSet, mem_ofPred_eq, targetBoundary]
  constructor <;> intro hz <;> linarith

/-- The two frozen remaining masses differ by at most `2 |q| / n`, even after clipping.
At the same mark their height thresholds differ by exactly `2 q`. -/
theorem unitSquareUniform_real_remaining_difference_le
    {n : ℕ} (hn : 0 < n) (q y : ℝ) :
    |(unitSquareUniform : Measure MarkedHeight).real (targetRawRemainingSet n q y) -
      (unitSquareUniform : Measure MarkedHeight).real (sourceRawRemainingSet n q y)| ≤
      2 * |q| / n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : Integrable (fun u : UnitMark ↦ 1 - clipToStrip n (sourceBoundary q y u) / n)
      (unitUniform : Measure UnitMark) :=
    (integrable_const (1 : ℝ)).sub
      ((integrable_clipToStrip_sourceBoundary n q y hnR.le).div_const n)
  have ht : Integrable (fun u : UnitMark ↦ 1 - clipToStrip n (targetBoundary q y u) / n)
      (unitUniform : Measure UnitMark) :=
    (integrable_const (1 : ℝ)).sub
      ((integrable_clipToStrip_targetBoundary n q y hnR.le).div_const n)
  rw [unitSquareUniform_real_targetRawRemainingSet_clipped hn,
    unitSquareUniform_real_sourceRawRemainingSet_clipped hn, ← integral_sub ht hs]
  have hbound : ∀ u : UnitMark,
      ‖(1 - clipToStrip n (targetBoundary q y u) / n) -
        (1 - clipToStrip n (sourceBoundary q y u) / n)‖ ≤ 2 * |q| / n := by
    intro u
    rw [Real.norm_eq_abs,
      show (1 - clipToStrip n (targetBoundary q y u) / n) -
          (1 - clipToStrip n (sourceBoundary q y u) / n) =
        (clipToStrip n (sourceBoundary q y u) -
          clipToStrip n (targetBoundary q y u)) / n by ring,
      abs_div, abs_of_pos hnR]
    apply div_le_div_of_nonneg_right _ hnR.le
    have h := clipToStrip_abs_sub_le n (sourceBoundary q y u) (targetBoundary q y u)
    have heq : sourceBoundary q y u - targetBoundary q y u = -(2 * q) := by
      unfold sourceBoundary targetBoundary
      ring
    simpa only [heq, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h
  simpa [Real.norm_eq_abs, Measure.real] using
    (norm_integral_le_of_norm_le_const (μ := (unitUniform : Measure UnitMark))
      (Filter.Eventually.of_forall hbound))

private theorem abs_ratio_sub_le
    {a b x y d c : ℝ} (hc : 0 < c) (hca : c ≤ a) (hb : 0 < b)
    (hy0 : 0 ≤ y) (hyb : y ≤ b) (hxy : |x - y| ≤ d) (hab : |a - b| ≤ d) :
    |x / a - y / b| ≤ 2 * d / c := by
  have ha : 0 < a := hc.trans_le hca
  have hd : 0 ≤ d := (abs_nonneg _).trans hxy
  have hyb0 : 0 ≤ y / b := div_nonneg hy0 hb.le
  have hyb1 : y / b ≤ 1 := (div_le_one₀ hb).mpr hyb
  have heq : x / a - y / b = (x - y) / a + (y / b) * ((b - a) / a) := by
    field_simp
    ring
  rw [heq]
  calc
    |(x - y) / a + (y / b) * ((b - a) / a)| ≤
        |(x - y) / a| + |(y / b) * ((b - a) / a)| := abs_add_le _ _
    _ = |x - y| / a + (y / b) * (|a - b| / a) := by
      rw [abs_div, abs_of_pos ha, abs_mul, abs_of_nonneg hyb0,
        abs_div, abs_of_pos ha, abs_sub_comm b a]
    _ ≤ d / a + 1 * (d / a) := by
      apply add_le_add (div_le_div_of_nonneg_right hxy ha.le)
      exact mul_le_mul hyb1 (div_le_div_of_nonneg_right hab ha.le)
        (div_nonneg (abs_nonneg _) ha.le) (by norm_num)
    _ = 2 * d / a := by ring
    _ ≤ 2 * d / c := div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hd) hc hca

/-- Conditional mass of a later source remaining set is the ratio of the two raw masses. -/
theorem unitSquareUniform_cond_sourceRemaining_real
    (n : ℕ) (q xR y : ℝ) (hxy : xR ≤ y) :
    ((unitSquareUniform : Measure MarkedHeight)[|sourceRawRemainingSet n q xR]).real
        (sourceRawRemainingSet n q y) =
      (unitSquareUniform : Measure MarkedHeight).real (sourceRawRemainingSet n q y) /
        (unitSquareUniform : Measure MarkedHeight).real (sourceRawRemainingSet n q xR) := by
  have hsub : sourceRawRemainingSet n q y ⊆ sourceRawRemainingSet n q xR := by
    intro z hz
    exact hxy.trans_lt hz
  rw [Measure.real, ProbabilityTheory.cond_apply
    (isOpen_sourceRawRemainingSet n q xR).measurableSet,
    inter_eq_right.mpr hsub, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [Measure.real, div_eq_mul_inv, mul_comm]

theorem unitSquareUniform_cond_targetRemaining_real
    (n : ℕ) (q xR y : ℝ) (hxy : xR ≤ y) :
    ((unitSquareUniform : Measure MarkedHeight)[|targetRawRemainingSet n q xR]).real
        (targetRawRemainingSet n q y) =
      (unitSquareUniform : Measure MarkedHeight).real (targetRawRemainingSet n q y) /
        (unitSquareUniform : Measure MarkedHeight).real (targetRawRemainingSet n q xR) := by
  have hsub : targetRawRemainingSet n q y ⊆ targetRawRemainingSet n q xR := by
    intro z hz
    exact hxy.trans_lt hz
  rw [Measure.real, ProbabilityTheory.cond_apply
    (isOpen_targetRawRemainingSet n q xR).measurableSet,
    inter_eq_right.mpr hsub, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [Measure.real, div_eq_mul_inv, mul_comm]

/-- At the right junction the small-shear hypothesis keeps every section inside the strip. -/
theorem unitSquareUniform_real_remaining_at_right_boundary
    {n : ℕ} (hn : 0 < n) {B q : ℝ} (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2)
    (hq : |q| ≤ B / 8) :
    (unitSquareUniform : Measure MarkedHeight).real
        (sourceRawRemainingSet n q ((n : ℝ) - B)) = (B + q / 2) / n ∧
      (unitSquareUniform : Measure MarkedHeight).real
        (targetRawRemainingSet n q ((n : ℝ) - B)) = (B - 3 * q / 2) / n := by
  have hs (u : UnitMark) : |q * (1 - (u : ℝ))| ≤ B / 8 := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr u.property.2)]
    calc
      |q| * (1 - (u : ℝ)) ≤ |q| * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [u.property.1]) (abs_nonneg q)
      _ ≤ B / 8 := by simpa using hq
  have ht (u : UnitMark) : |q * (1 + (u : ℝ))| ≤ B / 4 := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 + (u : ℝ) by linarith [u.property.1])]
    calc
      |q| * (1 + (u : ℝ)) ≤ |q| * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [u.property.2]) (abs_nonneg q)
      _ ≤ B / 4 := by linarith
  have hs0 (u : UnitMark) : 0 ≤ sourceBoundary q ((n : ℝ) - B) u := by
    unfold sourceBoundary
    have h := (abs_le.mp (hs u)).2
    linarith
  have hsN (u : UnitMark) : sourceBoundary q ((n : ℝ) - B) u ≤ n := by
    unfold sourceBoundary
    have h := (abs_le.mp (hs u)).1
    linarith
  have ht0 (u : UnitMark) : 0 ≤ targetBoundary q ((n : ℝ) - B) u := by
    unfold targetBoundary
    have h := (abs_le.mp (ht u)).1
    linarith
  have htN (u : UnitMark) : targetBoundary q ((n : ℝ) - B) u ≤ n := by
    unfold targetBoundary
    have h := (abs_le.mp (ht u)).2
    linarith
  rw [unitSquareUniform_sourceRawRemainingSet hn hs0 hsN,
    unitSquareUniform_targetRawRemainingSet hn ht0 htN]
  simp only [sourceUnclippedRemainingMass, targetUnclippedRemainingMass]
  constructor <;> congr 1 <;> ring

/-- Uniform conditional-probability difference along the entire frozen right tail.

This supplies the deterministic `hdifference` input to the boundary second-moment estimate;
no estimate on the difference of the conditional probabilities is assumed. -/
theorem unitSquareUniform_cond_remaining_difference_le
    {n : ℕ} (hn : 0 < n) {B q y : ℝ} (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2)
    (hq : |q| ≤ B / 8) (hy : (n : ℝ) - B ≤ y) :
    |((unitSquareUniform : Measure MarkedHeight)[|
          targetRawRemainingSet n q ((n : ℝ) - B)]).real (targetRawRemainingSet n q y) -
      ((unitSquareUniform : Measure MarkedHeight)[|
          sourceRawRemainingSet n q ((n : ℝ) - B)]).real (sourceRawRemainingSet n q y)| ≤
      8 * |q| / B := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmass := unitSquareUniform_real_remaining_at_right_boundary hn hB hBn hq
  let a := (unitSquareUniform : Measure MarkedHeight).real
    (targetRawRemainingSet n q ((n : ℝ) - B))
  let b := (unitSquareUniform : Measure MarkedHeight).real
    (sourceRawRemainingSet n q ((n : ℝ) - B))
  have ha : B / (2 * (n : ℝ)) ≤ a := by
    dsimp only [a]
    rw [hmass.2]
    have hqUpper := le_trans (le_abs_self q) hq
    apply (le_div_iff₀ hnR).mpr
    have hcancel : B / (2 * (n : ℝ)) * n = B / 2 := by field_simp
    rw [hcancel]
    linarith
  have hb : 0 < b := by
    dsimp only [b]
    rw [hmass.1]
    apply div_pos _ hnR
    have hqLower := neg_le_of_abs_le hq
    linarith
  have hyb : (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n q y) ≤ b := by
    exact measureReal_mono (fun z hz ↦ hy.trans_lt hz) (measure_ne_top _ _)
  have hab : |a - b| ≤ 2 * |q| / n :=
    unitSquareUniform_real_remaining_difference_le hn q ((n : ℝ) - B)
  have hratio := abs_ratio_sub_le (div_pos hB (mul_pos (by norm_num) hnR)) ha hb
    (measureReal_nonneg (μ := (unitSquareUniform : Measure MarkedHeight))
      (s := sourceRawRemainingSet n q y)) hyb
    (unitSquareUniform_real_remaining_difference_le hn q y) hab
  rw [unitSquareUniform_cond_targetRemaining_real n q _ y hy,
    unitSquareUniform_cond_sourceRemaining_real n q _ y hy]
  calc
    _ ≤ 2 * (2 * |q| / (n : ℝ)) / (B / (2 * (n : ℝ))) := hratio
    _ = 8 * |q| / B := by field_simp; ring

namespace FiniteSample

/-- History-state form of the right-tail difference bound, with the concrete constant `D = 8`. -/
theorem rightBoundaryHistoryProbability_difference_le
    {n : ℕ} (hn : 0 < n) (lam xR y B : ℝ) (state : FeedbackStepState n)
    (hboundary : xR = (n : ℝ) - B) (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2)
    (hq : |segmentCurve state.x state.p (state.slope lam) xR| ≤ B / 8)
    (hy : xR ≤ y) :
    |rightBoundaryHistoryTargetProbability n lam xR y state -
      rightBoundaryHistorySourceProbability n lam xR y state| ≤
      8 * |segmentCurve state.x state.p (state.slope lam) xR| / B := by
  subst xR
  exact unitSquareUniform_cond_remaining_difference_le hn hB hBn hq hy

end FiniteSample

end OTSelector
