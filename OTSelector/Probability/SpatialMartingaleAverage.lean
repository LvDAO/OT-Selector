import OTSelector.Probability.SpatialAveraging
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Spatial averaging of bounded local martingale residuals

Separated residual windows are orthogonal. Ordinary Fubini therefore gives an inverse-window
second-moment bound by the area of a diagonal strip; no stochastic Fubini theorem is needed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem integrable_bounded {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsFiniteMeasure ν] {f : A → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

private theorem integral_sq_spatialIntegral_eq_of_integrable_products
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℝ → Ω → ℝ) (a b : ℝ)
    (hi : Integrable (fun p : (ℝ × ℝ) × Ω ↦ X p.1.1 p.2 * X p.1.2 p.2)
      (((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))).prod μ)) :
    (∫ ω, (∫ x in Ioc a b, X x ω) ^ 2 ∂μ) =
      ∫ x in Ioc a b, ∫ y in Ioc a b, ∫ ω, X x ω * X y ω ∂μ := by
  let ν := volume.restrict (Ioc a b)
  calc
    _ = ∫ ω, ∫ p : ℝ × ℝ, X p.1 ω * X p.2 ω ∂ν.prod ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        dsimp only
        simpa only [pow_two] using
          (integral_prod_mul (μ := ν) (ν := ν) (fun x ↦ X x ω) (fun y ↦ X y ω)).symm
    _ = ∫ p : ℝ × ℝ, ∫ ω, X p.1 ω * X p.2 ω ∂μ ∂ν.prod ν :=
      (integral_integral_swap hi).symm
    _ = _ := integral_prod _ hi.integral_prod_left

/-- A uniformly bounded covariance supported within distance `t` has a linear window integral. -/
theorem integral_covariance_strip_le {c : ℝ → ℝ → ℝ}
    (hc : Measurable (Function.uncurry c)) {B t a b : ℝ}
    (hB : 0 ≤ B) (ht : 0 ≤ t) (hab : a ≤ b)
    (hbound : ∀ x y, ‖c x y‖ ≤ B)
    (hsep : ∀ x y, t ≤ |x - y| → c x y = 0) :
    (∫ x in Ioc a b, ∫ y in Ioc a b, c x y) ≤ (b - a) * (2 * t * B) := by
  have hi (x : ℝ) : Integrable (c x) (volume.restrict (Ioc a b)) :=
    integrable_bounded _ (hc.comp measurable_prodMk_left) (hbound x)
  have hinner (x : ℝ) : (∫ y in Ioc a b, c x y) ≤ 2 * t * B := by
    let strip := Ioo (x - t) (x + t)
    have hpoint (y : ℝ) : c x y ≤ strip.indicator (fun _ ↦ B) y := by
      by_cases hy : y ∈ strip
      · rw [indicator_of_mem hy]
        exact (le_abs_self _).trans (hbound x y)
      · rw [indicator_of_notMem hy, hsep x y]
        dsimp [strip] at hy
        rw [abs_sub_comm, le_abs]
        simp only [mem_Ioo, not_and_or, not_lt] at hy
        rcases hy with hy | hy <;> [right; left] <;> linarith
    have hg : Integrable (strip.indicator (fun _ ↦ B)) volume :=
      (integrableOn_const (by simp [strip, Real.volume_Ioo])).integrable_indicator
        measurableSet_Ioo
    calc
      _ ≤ ∫ y in Ioc a b, strip.indicator (fun _ ↦ B) y :=
        integral_mono (hi x) (hg.mono_measure Measure.restrict_le_self) hpoint
      _ ≤ ∫ y, strip.indicator (fun _ ↦ B) y :=
        integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall (fun _ ↦ indicator_nonneg (fun _ _ ↦ hB) _)) hg
      _ = 2 * t * B := by
        rw [integral_indicator measurableSet_Ioo, integral_const]
        simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo]
        rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ x + t - (x - t))]
        ring
  have hprod : Integrable (Function.uncurry c)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) :=
    integrable_bounded _ hc (fun p ↦ hbound p.1 p.2)
  calc
    _ ≤ ∫ _x in Ioc a b, (2 * t * B) :=
      integral_mono hprod.integral_prod_left (integrable_const _) hinner
    _ = _ := by simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

/-- Exact second moment of a bounded spatial average as the double integral of its covariances. -/
theorem integral_sq_spatialIntegral_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hX : Measurable (Function.uncurry X)) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ x ω, ‖X x ω‖ ≤ C) (a b : ℝ) :
    (∫ ω, (∫ x in Ioc a b, X x ω) ^ 2 ∂μ) =
      ∫ x in Ioc a b, ∫ y in Ioc a b, ∫ ω, X x ω * X y ω ∂μ := by
  let ν := volume.restrict (Ioc a b)
  have hmeas : Measurable (fun p : (ℝ × ℝ) × Ω ↦ X p.1.1 p.2 * X p.1.2 p.2) :=
    (hX.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hX.comp (measurable_fst.snd.prodMk measurable_snd))
  have hi : Integrable (fun p : (ℝ × ℝ) × Ω ↦ X p.1.1 p.2 * X p.1.2 p.2)
      ((ν.prod ν).prod μ) := by
    apply integrable_bounded _ hmeas
    intro p
    rw [norm_mul]
    exact mul_le_mul (hbound _ _) (hbound _ _) (norm_nonneg _) hC
  exact integral_sq_spatialIntegral_eq_of_integrable_products μ X a b hi

/-- Orthogonal windows yield the `1 / (b-a)` second-moment bound used in ENV. -/
theorem integral_sq_spatialAverage_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hX : Measurable (Function.uncurry X)) {C t a b : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hab : a < b)
    (hbound : ∀ x ω, ‖X x ω‖ ≤ C)
    (hsep : ∀ x y, t ≤ |x - y| → (∫ ω, X x ω * X y ω ∂μ) = 0) :
    (∫ ω, ((b - a)⁻¹ * ∫ x in Ioc a b, X x ω) ^ 2 ∂μ) ≤
      2 * t * C ^ 2 / (b - a) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × Ω ↦ X p.1.1 p.2 * X p.1.2 p.2) :=
    (hX.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hX.comp (measurable_fst.snd.prodMk measurable_snd))
  have hc : Measurable (fun p : ℝ × ℝ ↦ ∫ ω, X p.1 ω * X p.2 ω ∂μ) :=
    hm.stronglyMeasurable.integral_prod_right.measurable
  have hb (x y : ℝ) : ‖∫ ω, X x ω * X y ω ∂μ‖ ≤ C ^ 2 := by
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall fun ω ↦ show ‖X x ω * X y ω‖ ≤ C ^ 2 by
        rw [norm_mul, pow_two]
        exact mul_le_mul (hbound x ω) (hbound y ω) (norm_nonneg _) hC)
    simpa using h
  have hstrip := integral_covariance_strip_le
    (c := fun x y ↦ ∫ ω, X x ω * X y ω ∂μ) hc (sq_nonneg C) ht hab.le hb hsep
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_sq_spatialIntegral_eq μ hX hC hbound a b]
  calc
    _ ≤ (b - a)⁻¹ ^ 2 * ((b - a) * (2 * t * C ^ 2)) :=
      mul_le_mul_of_nonneg_left hstrip (sq_nonneg _)
    _ = _ := by field_simp

/-- The same estimate only needs uniformly bounded second moments, so it also applies to
marked compensated jump counts, whose values are not deterministically bounded. -/
theorem integral_sq_spatialAverage_le_of_memLp
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ℝ → Ω → ℝ}
    (hX : Measurable (Function.uncurry X)) {C t a b : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hab : a < b)
    (hLp : ∀ x, MemLp (X x) 2 μ)
    (hmean : ∀ x, (∫ ω, X x ω ^ 2 ∂μ) ≤ C)
    (hsep : ∀ x y, t ≤ |x - y| → (∫ ω, X x ω * X y ω ∂μ) = 0) :
    (∫ ω, ((b - a)⁻¹ * ∫ x in Ioc a b, X x ω) ^ 2 ∂μ) ≤
      2 * t * C / (b - a) := by
  let ν := volume.restrict (Ioc a b)
  have hm : Measurable (fun p : (ℝ × ℝ) × Ω ↦ X p.1.1 p.2 * X p.1.2 p.2) :=
    (hX.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hX.comp (measurable_fst.snd.prodMk measurable_snd))
  have hprod (x y : ℝ) : Integrable (fun ω ↦ X x ω * X y ω) μ :=
    (hLp x).integrable_mul (hLp y)
  have hn (x y : ℝ) : (∫ ω, ‖X x ω * X y ω‖ ∂μ) ≤ C := by
    calc
      _ ≤ ∫ ω, (X x ω ^ 2 + X y ω ^ 2) / 2 ∂μ := by
        apply integral_mono (hprod x y).norm
          (((hLp x).integrable_sq.add (hLp y).integrable_sq).div_const 2)
        intro ω
        change ‖X x ω * X y ω‖ ≤ (X x ω ^ 2 + X y ω ^ 2) / 2
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|X x ω| - |X y ω|), sq_abs (X x ω), sq_abs (X y ω)]
      _ = ((∫ ω, X x ω ^ 2 ∂μ) + ∫ ω, X y ω ^ 2 ∂μ) / 2 := by
        rw [integral_div, integral_add (hLp x).integrable_sq (hLp y).integrable_sq]
      _ ≤ C := by linarith [hmean x, hmean y]
  have hi : Integrable (fun p : (ℝ × ℝ) × Ω ↦ X p.1.1 p.2 * X p.1.2 p.2)
      ((ν.prod ν).prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun p ↦ hprod p.1 p.2), ?_⟩
    apply integrable_bounded _ hm.norm.stronglyMeasurable.integral_prod_right.measurable
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    exact hn p.1 p.2
  have hc : Measurable (fun p : ℝ × ℝ ↦ ∫ ω, X p.1 ω * X p.2 ω ∂μ) :=
    hm.stronglyMeasurable.integral_prod_right.measurable
  have hb (x y : ℝ) : ‖∫ ω, X x ω * X y ω ∂μ‖ ≤ C :=
    (norm_integral_le_integral_norm _).trans (hn x y)
  have hstrip := integral_covariance_strip_le
    (c := fun x y ↦ ∫ ω, X x ω * X y ω ∂μ) hc hC ht hab.le hb hsep
  simp_rw [mul_pow]
  rw [integral_const_mul,
    integral_sq_spatialIntegral_eq_of_integrable_products μ X a b hi]
  calc
    _ ≤ (b - a)⁻¹ ^ 2 * ((b - a) * (2 * t * C)) :=
      mul_le_mul_of_nonneg_left hstrip (sq_nonneg _)
    _ = _ := by field_simp

end OTSelector.Probability
