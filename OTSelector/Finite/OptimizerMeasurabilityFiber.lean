import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Finite fibres of differences of Euclidean distances

Fixing all sample coordinates except one source height leaves a difference of two distances.
Distinct target heights and a positive horizontal gap make each level set finite.  Squaring
twice reduces the level equation to a nonzero quadratic polynomial.
-/

open Set Polynomial

namespace OTSelector

/-- A distance-difference level has finitely many height solutions when the two target heights
are distinct and the second horizontal gap is positive. -/
theorem finite_euclidean_distance_difference_fibre
    (A B s t c : ℝ) (hB : 0 < B) (hst : s ≠ t) :
    {x : ℝ | Real.sqrt (A ^ 2 + (s - x) ^ 2) -
      Real.sqrt (B ^ 2 + (t - x) ^ 2) = c}.Finite := by
  let d := s - t
  let q := A ^ 2 + d ^ 2 - B ^ 2 - c ^ 2
  let p : Polynomial ℝ :=
    C (4 * (d ^ 2 - c ^ 2)) * X ^ 2 + C (-4 * d * q) * X +
      C (q ^ 2 - 4 * c ^ 2 * B ^ 2)
  have hd : d ≠ 0 := sub_ne_zero.mpr hst
  have hp : p ≠ 0 := by
    intro hp
    have h2 := congrArg (fun f : Polynomial ℝ ↦ f.coeff 2) hp
    have h1 := congrArg (fun f : Polynomial ℝ ↦ f.coeff 1) hp
    have h0 := congrArg (fun f : Polynomial ℝ ↦ f.coeff 0) hp
    norm_num only [p, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
      coeff_C, coeff_zero, ite_true, ite_false, mul_zero, mul_one,
      add_zero, zero_add] at h2 h1 h0
    have hq : q = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact (hd h).elim
      · exact h
    have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
    have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
    have hc2 : 0 < c ^ 2 := by nlinarith
    nlinarith [mul_pos hc2 hB2]
  have hroot : ∀ x : ℝ,
      Real.sqrt (A ^ 2 + (s - x) ^ 2) -
          Real.sqrt (B ^ 2 + (t - x) ^ 2) = c → p.IsRoot (x - t) := by
    intro x hx
    have hA := Real.sq_sqrt (add_nonneg (sq_nonneg A) (sq_nonneg (s - x)))
    have hB' := Real.sq_sqrt (add_nonneg (sq_nonneg B) (sq_nonneg (t - x)))
    have heq : Real.sqrt (A ^ 2 + (s - x) ^ 2) =
        c + Real.sqrt (B ^ 2 + (t - x) ^ 2) := sub_eq_iff_eq_add.mp hx
    rw [heq] at hA
    have hlin : q - 2 * d * (x - t) =
        2 * c * Real.sqrt (B ^ 2 + (t - x) ^ 2) := by
      dsimp [q, d]
      nlinarith only [hA, hB']
    have hsq := congrArg (fun y : ℝ ↦ y ^ 2) hlin
    change p.eval (x - t) = 0
    simp only [p, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    nlinarith only [hsq, congrArg (fun y : ℝ ↦ 4 * c ^ 2 * y) hB']
  have hfinite := (Polynomial.finite_setOfPred_isRoot hp).preimage
    (f := fun x : ℝ ↦ x - t) sub_left_injective.injOn
  exact hfinite.subset (fun x hx ↦ hroot x hx)

end OTSelector
