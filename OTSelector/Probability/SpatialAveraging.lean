import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ConditionalProbability

/-!
# Spatial averaging over an actual uniform root

A finite scene is rooted at an independent uniform point of `(a,b]`. Translating the root changes
bounded test integrals by at most `2 C |t| / (b-a)`. This is the boundary estimate needed to pass
spatial stationarity to local limits; it does not assume stationarity of any finite sample.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace OTSelector.Probability

/-- The actual law of a uniform spatial root in `(a,b]`. -/
noncomputable def spatialRootLaw (a b : ℝ) : Measure ℝ :=
  cond volume (Ioc a b)

theorem spatialRootLaw_isProbability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (spatialRootLaw a b) := by
  apply cond_isProbabilityMeasure_of_finite
  · simpa only [Real.volume_Ioc, ne_eq, ENNReal.ofReal_eq_zero, not_le] using sub_pos.mpr hab
  · simp [Real.volume_Ioc]

theorem integral_spatialRootLaw {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ z, f z ∂spatialRootLaw a b) = (b - a)⁻¹ * ∫ z in a..b, f z := by
  rw [spatialRootLaw, ProbabilityTheory.cond, integral_smul_measure,
    intervalIntegral.integral_of_le hab]
  simp [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

private theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hbound : ∀ z, ‖f z‖ ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  constructor <;> exact ⟨hf.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hbound)⟩

/-- Translation loses only the two boundary intervals, even when the windows do not overlap. -/
theorem norm_intervalIntegral_shift_sub_le {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hbound : ∀ z, ‖f z‖ ≤ C) (a b t : ℝ) :
    ‖(∫ z in a..b, f (z + t)) - ∫ z in a..b, f z‖ ≤ 2 * C * |t| := by
  rw [intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_interval_sub_interval_comm
      (intervalIntegrable_of_bounded hf hbound _ _)
      (intervalIntegrable_of_bounded hf hbound _ _)
      (intervalIntegrable_of_bounded hf hbound _ _)]
  have ha := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a + t) (b := a) (fun z _ ↦ hbound z)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := b + t) (b := b) (fun z _ ↦ hbound z)
  calc
    _ ≤ ‖∫ z in a + t..a, f z‖ + ‖∫ z in b + t..b, f z‖ := norm_sub_le _ _
    _ ≤ C * |a - (a + t)| + C * |b - (b + t)| := add_le_add ha hb
    _ = 2 * C * |t| := by simp; ring

/-- The actual uniform-root law is asymptotically translation invariant on bounded tests. -/
theorem norm_integral_spatialRootLaw_shift_sub_le {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hbound : ∀ z, ‖f z‖ ≤ C) {a b : ℝ} (hab : a < b) (t : ℝ) :
    ‖(∫ z, f (z + t) ∂spatialRootLaw a b) - ∫ z, f z ∂spatialRootLaw a b‖ ≤
      (2 * C * |t|) / (b - a) := by
  rw [integral_spatialRootLaw hab.le, integral_spatialRootLaw hab.le,
    ← mul_sub, norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos (sub_pos.mpr hab)]
  calc
    _ ≤ (b - a)⁻¹ * (2 * C * |t|) :=
      mul_le_mul_of_nonneg_left (norm_intervalIntegral_shift_sub_le hf hbound a b t)
        (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
    _ = _ := by ring

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- A finite scene rooted independently at a uniform point of the chosen window. -/
noncomputable def spatialAverageLaw (P : Measure Ω) (scene : Ω × ℝ → X) (a b : ℝ) :
    Measure X := (P.prod (spatialRootLaw a b)).map scene

theorem spatialAverageLaw_isProbability (P : Measure Ω) [IsProbabilityMeasure P]
    {scene : Ω × ℝ → X} (hscene : Measurable scene) {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (spatialAverageLaw P scene a b) := by
  let := spatialRootLaw_isProbability hab
  exact Measure.isProbabilityMeasure_map hscene.aemeasurable

/-- Test integrals of the constructed law are genuine independent uniform-root averages. -/
theorem integral_spatialAverageLaw (P : Measure Ω) [IsProbabilityMeasure P]
    {scene : Ω × ℝ → X} (hscene : Measurable scene) {a b : ℝ} (hab : a < b)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂spatialAverageLaw P scene a b) =
      ∫ ω, ∫ z, f (scene (ω, z)) ∂spatialRootLaw a b ∂P := by
  let := spatialRootLaw_isProbability hab
  rw [spatialAverageLaw, integral_map hscene.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ ⟨(hf.comp hscene).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun p ↦ hbound (scene p)))⟩

/-- Uniform-root averaging of any measurable finite scene has only a boundary translation error.
The original sample law is arbitrary and does not need to be stationary. -/
theorem norm_integral_spatialAverageLaw_shift_sub_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {scene : Ω × ℝ → X} (hscene : Measurable scene) {a b : ℝ} (hab : a < b)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (t : ℝ) :
    ‖(∫ x, f x ∂spatialAverageLaw P (fun p ↦ scene (p.1, p.2 + t)) a b) -
        ∫ x, f x ∂spatialAverageLaw P scene a b‖ ≤ (2 * C * |t|) / (b - a) := by
  let := spatialRootLaw_isProbability hab
  have hs : Measurable (fun p : Ω × ℝ ↦ scene (p.1, p.2 + t)) :=
    hscene.comp (measurable_fst.prodMk (measurable_snd.add_const t))
  have hi : Integrable (fun p ↦ f (scene p)) (P.prod (spatialRootLaw a b)) :=
    ⟨(hf.comp hscene).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (.of_forall (fun p ↦ hbound (scene p)))⟩
  have his : Integrable (fun p : Ω × ℝ ↦ f (scene (p.1, p.2 + t)))
      (P.prod (spatialRootLaw a b)) :=
    ⟨(hf.comp hs).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (.of_forall (fun p ↦ hbound (scene (p.1, p.2 + t))))⟩
  rw [integral_spatialAverageLaw P hs hab hf hbound,
    integral_spatialAverageLaw P hscene hab hf hbound,
    ← integral_sub his.integral_prod_left hi.integral_prod_left]
  simpa using MeasureTheory.norm_integral_le_of_norm_le_const (μ := P)
    (Filter.Eventually.of_forall (fun ω ↦
      norm_integral_spatialRootLaw_shift_sub_le
        ((hf.comp hscene).comp measurable_prodMk_left)
        (fun z ↦ hbound (scene (ω, z))) hab t))

/-- A genuine rerooting cocycle converts the boundary estimate into approximate invariance
under the scene's own translation map. -/
theorem norm_integral_spatialAverageLaw_reroot_sub_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    {scene : Ω × ℝ → X} (hscene : Measurable scene) {a b : ℝ} (hab : a < b)
    {shift : X → X} (hshift : Measurable shift) (t : ℝ)
    (hcocycle : ∀ ω z, shift (scene (ω, z)) = scene (ω, z + t))
    {f : X → ℝ} (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    ‖(∫ x, f (shift x) ∂spatialAverageLaw P scene a b) -
        ∫ x, f x ∂spatialAverageLaw P scene a b‖ ≤ (2 * C * |t|) / (b - a) := by
  have heq : (∫ x, f (shift x) ∂spatialAverageLaw P scene a b) =
      ∫ x, f x ∂spatialAverageLaw P (fun p ↦ scene (p.1, p.2 + t)) a b := by
    rw [integral_spatialAverageLaw P hscene hab (f := fun x ↦ f (shift x)) (hf.comp hshift)
      (fun x ↦ hbound (shift x)),
      integral_spatialAverageLaw P (scene := fun p ↦ scene (p.1, p.2 + t))
        (hscene.comp (measurable_fst.prodMk (measurable_snd.add_const t))) hab hf hbound]
    simp_rw [hcocycle]
  rw [heq]
  exact norm_integral_spatialAverageLaw_shift_sub_le P hscene hab hf hbound t

/-- The explicit boundary error vanishes along any sequence of windows whose lengths diverge. -/
theorem tendsto_spatialAverage_boundaryError {a b : ℕ → ℝ}
    (hlength : Tendsto (fun n ↦ b n - a n) atTop atTop) (C t : ℝ) :
    Tendsto (fun n ↦ (2 * C * |t|) / (b n - a n)) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
    tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hlength)

end OTSelector.Probability
