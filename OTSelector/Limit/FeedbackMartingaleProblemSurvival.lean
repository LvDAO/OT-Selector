import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Uniqueness of the constant-rate survival equation

Local interval integrability and the compensator integral equation imply the exponential
survival function. The proof first obtains continuity from the primitive, then applies an
integrating factor to the right derivative.
-/

open MeasureTheory Set
open scoped Topology

namespace OTSelector.Limit

/-- The continuous solution of the constant-rate survival integral equation is exponential. -/
theorem survival_eq_exp_of_integral_equation {r : ℝ} {S : ℝ → ℝ}
    (hcont : ContinuousOn S (Ici 0))
    (hS : ∀ t, 0 ≤ t → S t = 1 - r * ∫ u in 0..t, S u)
    {t : ℝ} (ht : 0 ≤ t) : S t = Real.exp (-r * t) := by
  have hzero : S 0 = 1 := by simpa using hS 0 le_rfl
  have hderiv (x : ℝ) (hx : 0 ≤ x) :
      HasDerivWithinAt S (-r * S x) (Ici x) x := by
    have hc : ContinuousOn S (Ici x) := hcont.mono (fun _ hy ↦ hx.trans hy)
    have hi : HasDerivWithinAt (fun y ↦ ∫ u in 0..y, S u) (S x) (Ici x) x :=
      intervalIntegral.integral_hasDerivWithinAt_right (s := Ici x) (t := Ioi x)
        ((hcont.mono (fun _ hy ↦ hy.1)).intervalIntegrable_of_Icc hx)
        ((hc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi x)
        ((hc x (by simp)).mono Ioi_subset_Ici_self)
    exact (((hi.const_mul r).const_sub 1).congr
      (fun y hy ↦ hS y (hx.trans hy)) (hS x hx)).congr_deriv (by ring)
  have hprod (x : ℝ) (hx : 0 ≤ x) :
      HasDerivWithinAt (fun y ↦ Real.exp (r * y) * S y) 0 (Ici x) x := by
    have he : HasDerivWithinAt (fun y ↦ Real.exp (r * y))
        (Real.exp (r * x) * r) (Ici x) x := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id x).const_mul r).exp.hasDerivWithinAt
    exact (he.mul (hderiv x hx)).congr_deriv (by ring)
  have heq : Real.exp (r * t) * S t = 1 := by
    have hc : ContinuousOn (fun y ↦ Real.exp (r * y) * S y) (Icc 0 t) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        (hcont.mono (fun _ hy ↦ hy.1))
    simpa [hzero] using
      constant_of_has_deriv_right_zero hc (fun x hx ↦ hprod x hx.1) t ⟨ht, le_rfl⟩
  apply (mul_left_cancel₀ (Real.exp_ne_zero (r * t)))
  rw [heq, ← Real.exp_add]
  simp

/-- Local interval integrability and the survival equation already imply continuity. -/
theorem continuousOn_survival_of_integral_equation {r : ℝ} {S : ℝ → ℝ}
    (hInt : ∀ t, 0 ≤ t → IntervalIntegrable S volume 0 t)
    (hS : ∀ t, 0 ≤ t → S t = 1 - r * ∫ u in 0..t, S u) :
    ContinuousOn S (Ici 0) := by
  intro x hx
  change 0 ≤ x at hx
  have hxp : 0 ≤ x + 1 := by linarith [hx]
  have hp : ContinuousOn (fun y ↦ ∫ u in 0..y, S u) (Icc 0 (x + 1)) := by
    simpa only [uIcc_of_le hxp] using
      intervalIntegral.continuousOn_primitive_interval' (hInt (x + 1) hxp)
        (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 (x + 1))
  have hc : ContinuousOn S (Icc 0 (x + 1)) :=
    (continuousOn_const.sub (continuousOn_const.mul hp)).congr
      (fun y hy ↦ hS y hy.1)
  apply (hc x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin
  apply Filter.mem_of_superset
    (inter_mem_nhdsWithin (Ici 0) (Iio_mem_nhds (show x < x + 1 by linarith)))
  intro y hy
  exact ⟨hy.1, hy.2.le⟩

/-- A locally integrable survival function satisfying the integral equation is exponential. -/
theorem survival_eq_exp_of_locally_integrable {r : ℝ} {S : ℝ → ℝ}
    (hInt : ∀ t, 0 ≤ t → IntervalIntegrable S volume 0 t)
    (hS : ∀ t, 0 ≤ t → S t = 1 - r * ∫ u in 0..t, S u)
    {t : ℝ} (ht : 0 ≤ t) : S t = Real.exp (-r * t) :=
  survival_eq_exp_of_integral_equation
    (continuousOn_survival_of_integral_equation hInt hS) hS ht

end OTSelector.Limit
