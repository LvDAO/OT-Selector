import OTSelector.Basic.EmpiricalMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scalar empirical processes

This small API is adapted from `StatLean/Stat-Lean` commit
`e1ef06bf52d2a8896439c5b59d982d9aad28a254`, files
`EmpiricalAverage.lean` and `EmpiricalProcess.lean` (Apache-2.0).  It is kept local so the project
does not acquire StatLean's older Lake dependency graph.
-/

open MeasureTheory
open scoped BigOperators

namespace OTSelector.EmpiricalProcess

variable {Ω : Type*}

/-- The empirical average `n⁻¹ ∑ i, f (X i)`. -/
noncomputable def empiricalAverage (f : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (X i)

@[simp]
theorem empiricalAverage_zero (f : Ω → ℝ) (X : Fin 0 → Ω) :
    empiricalAverage f 0 X = 0 := by
  simp [empiricalAverage]

@[simp]
theorem empiricalAverage_const_zero (n : ℕ) (X : Fin n → Ω) :
    empiricalAverage (fun _ ↦ (0 : ℝ)) n X = 0 := by
  simp [empiricalAverage]

theorem empiricalAverage_add (f g : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalAverage (fun x ↦ f x + g x) n X =
      empiricalAverage f n X + empiricalAverage g n X := by
  unfold empiricalAverage
  rw [Finset.sum_add_distrib, mul_add]

theorem empiricalAverage_smul (c : ℝ) (f : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalAverage (fun x ↦ c * f x) n X = c * empiricalAverage f n X := by
  unfold empiricalAverage
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (n : ℝ)⁻¹ c, mul_assoc]

variable [MeasurableSpace Ω]

/-- The centered empirical process `√n (Pₙ f - P f)`. -/
noncomputable def empiricalProcess
    (P : Measure Ω) (n : ℕ) (X : Fin n → Ω) (f : Ω → ℝ) : ℝ :=
  Real.sqrt n * (empiricalAverage f n X - ∫ x, f x ∂P)

@[simp]
theorem empiricalProcess_zero (P : Measure Ω) (X : Fin 0 → Ω) (f : Ω → ℝ) :
    empiricalProcess P 0 X f = 0 := by
  simp [empiricalProcess]

theorem empiricalProcess_add (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P) :
    empiricalProcess P n X (fun x ↦ f x + g x) =
      empiricalProcess P n X f + empiricalProcess P n X g := by
  unfold empiricalProcess
  rw [empiricalAverage_add, integral_add hf hg]
  ring

theorem empiricalProcess_smul (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (c : ℝ) (f : Ω → ℝ) :
    empiricalProcess P n X (fun x ↦ c * f x) = c * empiricalProcess P n X f := by
  unfold empiricalProcess
  rw [empiricalAverage_smul, integral_const_mul]
  ring

theorem empiricalProcess_sub (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P) :
    empiricalProcess P n X (fun x ↦ f x - g x) =
      empiricalProcess P n X f - empiricalProcess P n X g := by
  have havg : empiricalAverage (fun x ↦ f x - g x) n X =
      empiricalAverage f n X - empiricalAverage g n X := by
    have : (fun x ↦ f x - g x) = (fun x ↦ f x + (-1 : ℝ) * g x) := by
      funext x
      ring
    rw [this, empiricalAverage_add, empiricalAverage_smul]
    ring
  unfold empiricalProcess
  rw [havg, integral_sub hf hg]
  ring

/-- Integration against `OTSelector.empiricalMeasure` agrees with `empiricalAverage`. -/
theorem integral_empiricalMeasure_eq_empiricalAverage (X : Fin n → Ω) {f : Ω → ℝ}
    (hf : StronglyMeasurable f) :
    ∫ x, f x ∂(OTSelector.empiricalMeasure X) = empiricalAverage f n X := by
  simpa [empiricalAverage] using OTSelector.integral_empiricalMeasure X hf

end OTSelector.EmpiricalProcess
