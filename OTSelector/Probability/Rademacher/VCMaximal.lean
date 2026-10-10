/-
Copyright (c) 2026 Yuwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuwei Lu
-/

import OTSelector.Probability.Rademacher.Haussler
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Log-free fixed-sample VC maximal inequality

This file substitutes the premise-free Haussler covering estimate into the finite Dudley chain.
The result is a normalized Rademacher bound of order `v / sqrt m` for a finite Boolean family of
VC dimension at most `v`.  All entropy sums and the terminal dyadic scale are discharged here;
consumers do not supply a covering or chaining hypothesis.

The explicit constant `392` is intentionally conservative.  Its role is to keep the formal
argument elementary: the square-root entropy term is bounded by a linear function and the
remaining arithmetic-geometric series is at most four.
-/

open scoped BigOperators NNReal

namespace OTSelector.Probability.Rademacher

open Classical

/-- Every Boolean indicator vector lies in the Euclidean ball of radius `sqrt m`. -/
theorem indicatorVector_norm_le_sqrt_card {m : ℕ} (p : Fin m → Bool) :
    ‖indicatorVector p‖ ≤ Real.sqrt m := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc
    ∑ i : Fin m, ‖indicatorVector p i‖ ^ 2 ≤ ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [indicatorVector_apply]
      split <;> norm_num
    _ = (m : ℝ) := by simp

/-- The indicator family inherits the same Euclidean radius bound. -/
theorem indicatorVectors_norm_le_sqrt_card {m : ℕ} (H : Finset (Fin m → Bool))
    (v : SampleVector m) (hv : v ∈ indicatorVectors H) :
    ‖v‖ ≤ Real.sqrt m := by
  obtain ⟨p, hp, rfl⟩ := (mem_indicatorVectors_iff H v).1 hv
  exact indicatorVector_norm_le_sqrt_card p

/-- A nonempty Boolean family has a nonempty indicator image. -/
theorem indicatorVectors_nonempty {m : ℕ} {H : Finset (Fin m → Bool)}
    (hH : H.Nonempty) : (indicatorVectors H).Nonempty := by
  simpa [indicatorVectors] using hH.image indicatorVector

private lemma dyadicSqrtRadius_coe (m j : ℕ) :
  (dyadicRadius (NNReal.sqrt (m : NNReal)) j : ℝ) =
      Real.sqrt m * (1 / 2 : ℝ) ^ j := by
  simp [dyadicRadius, Real.coe_sqrt, div_eq_mul_inv, inv_pow]

private lemma dyadicSqrtRadius_pos {m j : ℕ} (hm : 0 < m) :
    0 < dyadicRadius (NNReal.sqrt (m : NNReal)) j := by
  rw [← NNReal.coe_pos]
  simp only [dyadicSqrtRadius_coe]
  positivity

private lemma dyadicSqrtRadius_sq_le_card (m j : ℕ) :
    (dyadicRadius (NNReal.sqrt (m : NNReal)) j : ℝ) ^ 2 ≤ m := by
  rw [dyadicSqrtRadius_coe]
  have hr_nonneg : 0 ≤ Real.sqrt m * (1 / 2 : ℝ) ^ j := by positivity
  have hr_le : Real.sqrt m * (1 / 2 : ℝ) ^ j ≤ Real.sqrt m := by
    apply mul_le_of_le_one_right (Real.sqrt_nonneg m)
    exact pow_le_one₀ (by norm_num) (by norm_num)
  calc
    (Real.sqrt m * (1 / 2 : ℝ) ^ j) ^ 2 ≤ (Real.sqrt m) ^ 2 :=
      pow_le_pow_left₀ hr_nonneg hr_le 2
    _ = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)

private lemma sqrtCard_div_dyadicSqrtRadius {m j : ℕ} (hm : 0 < m) :
    Real.sqrt m / (dyadicRadius (NNReal.sqrt (m : NNReal)) j : ℝ) =
      (2 : ℝ) ^ j := by
  rw [dyadicSqrtRadius_coe]
  have hsqrt : Real.sqrt m ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 hm)).ne'
  field_simp
  rw [← mul_pow]
  norm_num

private lemma vcPolynomial_dyadic_le_exp_pow (v j : ℕ) (hv : 0 < v) :
    2 * (16 * Real.exp 1) ^ v * ((2 : ℝ) ^ j) ^ (2 * v) ≤
      (Real.exp 1) ^ (8 * v * (j + 1)) := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
  have h16e : (16 : ℝ) * Real.exp 1 ≤ (Real.exp 1) ^ 5 := by
    have hpow : (16 : ℝ) ≤ (Real.exp 1) ^ 4 := by
      calc
        (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 :=
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2e 4
    calc
      (16 : ℝ) * Real.exp 1 ≤ (Real.exp 1) ^ 4 * Real.exp 1 :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos 1).le
      _ = (Real.exp 1) ^ 5 := by ring
  have hj : (2 : ℝ) ^ j ≤ (Real.exp 1) ^ j :=
    pow_le_pow_left₀ (by norm_num) h2e j
  calc
    2 * (16 * Real.exp 1) ^ v * ((2 : ℝ) ^ j) ^ (2 * v) ≤
        Real.exp 1 * ((Real.exp 1) ^ 5) ^ v *
          (((Real.exp 1) ^ j) ^ (2 * v)) := by
      gcongr
    _ = (Real.exp 1) ^ (1 + 5 * v + j * (2 * v)) := by
      simp only [pow_mul, pow_add, pow_one]
    _ ≤ (Real.exp 1) ^ (8 * v * (j + 1)) := by
      apply pow_le_pow_right₀ (Real.one_le_exp (by norm_num))
      nlinarith

/-- The logarithm of a dyadic indicator covering number is linear in the scale index. -/
theorem log_coveringCard_indicator_dyadic_le {m v j : ℕ} (hm : 0 < m)
    (hv : 0 < v) (H : Finset (Fin m → Bool)) (hH : H.Nonempty)
    (hVC : H.boolVCDim ≤ v) :
    Real.log (coveringCard (dyadicRadius (NNReal.sqrt (m : NNReal)) j)
        (indicatorVectors H)) ≤
      8 * (v : ℝ) * (j + 1) := by
  let ε := dyadicRadius (NNReal.sqrt (m : NNReal)) j
  let N := coveringCard ε (indicatorVectors H)
  have hε : 0 < ε := dyadicSqrtRadius_pos (j := j) hm
  have hεm : (ε : ℝ) ^ 2 ≤ m := dyadicSqrtRadius_sq_le_card m j
  have hcover : (N : ℝ) ≤
      2 * (16 * Real.exp 1) ^ v * ((2 : ℝ) ^ j) ^ (2 * v) := by
    have h := indicator_coveringCard_cast_le_polynomial ε H hε hεm hVC
    simpa [N, ε, sqrtCard_div_dyadicSqrtRadius (j := j) hm] using h
  have hbound : (N : ℝ) ≤ (Real.exp 1) ^ (8 * v * (j + 1)) :=
    hcover.trans (vcPolynomial_dyadic_le_exp_pow v j hv)
  have hA : (indicatorVectors H).Nonempty := indicatorVectors_nonempty hH
  have hNpos : 0 < N := by
    simpa [N] using (coveringFinset_nonempty ε hA).card_pos.trans_eq
      (coveringFinset_card ε (indicatorVectors H))
  calc
    Real.log N ≤ Real.log ((Real.exp 1) ^ (8 * v * (j + 1))) :=
      Real.log_le_log (by exact_mod_cast hNpos) hbound
    _ = 8 * (v : ℝ) * (j + 1) := by
      rw [Real.log_pow, Real.log_exp]
      norm_num

/-- Entropy of the product of two consecutive covers in the Dudley increment. -/
theorem log_coveringCard_product_indicator_dyadic_le {m v j : ℕ} (hm : 0 < m)
    (hv : 0 < v) (H : Finset (Fin m → Bool)) (hH : H.Nonempty)
    (hVC : H.boolVCDim ≤ v) :
    Real.log
        (coveringCard (dyadicRadius (NNReal.sqrt (m : NNReal)) (j + 1))
            (indicatorVectors H) *
          coveringCard (dyadicRadius (NNReal.sqrt (m : NNReal)) j)
            (indicatorVectors H)) ≤
      24 * (v : ℝ) * (j + 1) := by
  let R := NNReal.sqrt (m : NNReal)
  let Nnext := coveringCard (dyadicRadius R (j + 1)) (indicatorVectors H)
  let Ncurr := coveringCard (dyadicRadius R j) (indicatorVectors H)
  have hA : (indicatorVectors H).Nonempty := indicatorVectors_nonempty hH
  have hnext_pos : 0 < Nnext := by
    have hpos := (coveringFinset_nonempty (dyadicRadius R (j + 1)) hA).card_pos
    rw [coveringFinset_card] at hpos
    simpa [Nnext] using hpos
  have hcurr_pos : 0 < Ncurr := by
    have hpos := (coveringFinset_nonempty (dyadicRadius R j) hA).card_pos
    rw [coveringFinset_card] at hpos
    simpa [Ncurr] using hpos
  rw [show (coveringCard (dyadicRadius R (j + 1)) (indicatorVectors H) *
      coveringCard (dyadicRadius R j) (indicatorVectors H) : ℝ) =
      (Nnext : ℝ) * Ncurr by rfl]
  rw [Real.log_mul (Nat.cast_ne_zero.mpr hnext_pos.ne')
    (Nat.cast_ne_zero.mpr hcurr_pos.ne')]
  calc
    Real.log Nnext + Real.log Ncurr ≤
        8 * (v : ℝ) * (j + 2) + 8 * (v : ℝ) * (j + 1) :=
      add_le_add
        (by
          have h := log_coveringCard_indicator_dyadic_le
            (j := j + 1) hm hv H hH hVC
          norm_num [Nnext, R, add_assoc] at h ⊢
          exact h)
        (by simpa [Ncurr, R] using
          log_coveringCard_indicator_dyadic_le (j := j) hm hv H hH hVC)
    _ ≤ 24 * (v : ℝ) * (j + 1) := by
      have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
      nlinarith

/-- The square-root entropy factor in each Dudley increment has a linear envelope. -/
theorem sqrt_two_log_coveringCard_product_indicator_dyadic_le
    {m v j : ℕ} (hm : 0 < m) (hv : 0 < v)
    (H : Finset (Fin m → Bool)) (hH : H.Nonempty) (hVC : H.boolVCDim ≤ v) :
    Real.sqrt (2 * Real.log
        (coveringCard (dyadicRadius (NNReal.sqrt (m : NNReal)) (j + 1))
            (indicatorVectors H) *
          coveringCard (dyadicRadius (NNReal.sqrt (m : NNReal)) j)
            (indicatorVectors H))) ≤
      49 * (v : ℝ) * (j + 1) := by
  let N := coveringCard (dyadicRadius (NNReal.sqrt (m : NNReal)) (j + 1))
      (indicatorVectors H) *
    coveringCard (dyadicRadius (NNReal.sqrt (m : NNReal)) j) (indicatorVectors H)
  let x : ℝ := 2 * Real.log N
  have hx_nonneg : 0 ≤ x := by
    exact mul_nonneg (by norm_num) (Real.log_natCast_nonneg N)
  have hsqrt : Real.sqrt x ≤ x + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith [sq_nonneg x]
  have hx_le : x ≤ 48 * (v : ℝ) * (j + 1) := by
    have hlog := log_coveringCard_product_indicator_dyadic_le
      (j := j) hm hv H hH hVC
    dsimp [x, N]
    push_cast
    nlinarith [hlog]
  have hvj : (1 : ℝ) ≤ (v : ℝ) * (j + 1) := by
    have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
    have hjR : (1 : ℝ) ≤ (j : ℝ) + 1 := by norm_num
    nlinarith
  calc
    Real.sqrt (2 * Real.log
        (coveringCard (dyadicRadius (NNReal.sqrt (m : NNReal)) (j + 1))
            (indicatorVectors H) *
          coveringCard (dyadicRadius (NNReal.sqrt (m : NNReal)) j)
            (indicatorVectors H))) = Real.sqrt x := by
      simp [x, N, Nat.cast_mul]
    _ ≤ x + 1 := hsqrt
    _ ≤ 49 * (v : ℝ) * (j + 1) := by nlinarith

/-- The arithmetic-geometric series used after the entropy envelope is uniformly bounded. -/
theorem sum_succ_mul_inv_two_pow_le_four (L : ℕ) :
    ∑ j : Fin L, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j : ℕ) ≤ 4 := by
  let f : ℕ → ℝ := fun j ↦ ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j
  change ∑ j : Fin L, f j ≤ 4
  rw [Fin.sum_univ_eq_sum_range f L]
  dsimp [f]
  have hsummable : Summable (fun j : ℕ ↦ (j : ℝ) * (1 / 2 : ℝ) ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).summable
  have hweighted : ∑ j ∈ Finset.range L, (j : ℝ) * (1 / 2 : ℝ) ^ j ≤ 2 := by
    calc
      ∑ j ∈ Finset.range L, (j : ℝ) * (1 / 2 : ℝ) ^ j ≤
          ∑' j : ℕ, (j : ℝ) * (1 / 2 : ℝ) ^ j :=
        hsummable.sum_le_tsum (Finset.range L) (fun j _ ↦ by positivity)
      _ = 2 := by
        rw [tsum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)]
        norm_num
  calc
    ∑ j ∈ Finset.range L, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j =
        (∑ j ∈ Finset.range L, (j : ℝ) * (1 / 2 : ℝ) ^ j) +
          ∑ j ∈ Finset.range L, (1 / 2 : ℝ) ^ j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 2 + 2 := add_le_add hweighted (sum_geometric_two_le L)
    _ = 4 := by norm_num

private lemma inv_card_mul_sqrt (m : ℕ) (hm : 0 < m) :
    (m : ℝ)⁻¹ * Real.sqrt m = (Real.sqrt m)⁻¹ := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  field_simp
  nlinarith [Real.sq_sqrt hmR.le]

private lemma inv_two_pow_le_inv_sqrt_card (m : ℕ) (hm : 0 < m) :
    (1 / 2 : ℝ) ^ m ≤ (Real.sqrt m)⁻¹ := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.2 (Nat.cast_pos.2 hm)
  have hsqrt_le_m : Real.sqrt m ≤ (m : ℝ) := by
    exact Real.sqrt_le_self_iff.2 (Or.inr hmR)
  have hm_le_pow : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast Nat.le_of_lt m.lt_two_pow_self
  rw [one_div, inv_pow]
  exact (inv_le_inv₀ (pow_pos (by norm_num) m) hsqrt_pos).2
    (hsqrt_le_m.trans hm_le_pow)

/-- Log-free fixed-sample VC maximal inequality for Boolean indicator vectors.

The left side is the normalized expected signed supremum from `Dudley.lean`.  The bound is
uniform in the finite Boolean family once its VC dimension is at most the positive integer `v`.
-/
theorem fixedRademacherComplexity_indicator_le {m v : ℕ} (hm : 0 < m) (hv : 0 < v)
    (H : Finset (Fin m → Bool)) (hH : H.Nonempty) (hVC : H.boolVCDim ≤ v) :
    fixedRademacherComplexity (indicatorVectors H) (indicatorVectors_nonempty hH) ≤
      (1 + 392 * (v : ℝ)) / Real.sqrt m := by
  let R : NNReal := NNReal.sqrt (m : NNReal)
  let A : Finset (SampleVector m) := indicatorVectors H
  have hR : 0 < R := by
    rw [NNReal.sqrt_pos]
    exact_mod_cast hm
  have hA : A.Nonempty := indicatorVectors_nonempty hH
  have hA_norm : ∀ a ∈ A, ‖a‖ ≤ R := by
    intro a ha
    simpa [A, R, Real.coe_sqrt] using indicatorVectors_norm_le_sqrt_card H a ha
  have hdudley := fixedRademacherComplexity_le_dudleySum
    (L := m) hm hR hA hA_norm
  have hterm : ∀ j : Fin m,
      ((dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j) *
          Real.sqrt (2 * Real.log
            (coveringCard (dyadicRadius R (j + 1)) A *
              coveringCard (dyadicRadius R j) A)) ≤
        98 * Real.sqrt m * (v : ℝ) *
          (((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j : ℕ)) := by
    intro j
    have hradius : (dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j ≤
        2 * Real.sqrt m * (1 / 2 : ℝ) ^ (j : ℕ) := by
      simp only [R, dyadicSqrtRadius_coe]
      rw [pow_succ]
      have hnonneg : 0 ≤ Real.sqrt m * (1 / 2 : ℝ) ^ (j : ℕ) := by positivity
      nlinarith
    have hentropy := sqrt_two_log_coveringCard_product_indicator_dyadic_le
      (j := (j : ℕ)) hm hv H hH hVC
    have hradius_nonneg :
        0 ≤ (dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j := by positivity
    calc
      ((dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j) *
          Real.sqrt (2 * Real.log
            (coveringCard (dyadicRadius R (j + 1)) A *
              coveringCard (dyadicRadius R j) A)) ≤
          (2 * Real.sqrt m * (1 / 2 : ℝ) ^ (j : ℕ)) *
            Real.sqrt (2 * Real.log
              (coveringCard (dyadicRadius R (j + 1)) A *
                coveringCard (dyadicRadius R j) A)) :=
        mul_le_mul_of_nonneg_right hradius (Real.sqrt_nonneg _)
      _ ≤ (2 * Real.sqrt m * (1 / 2 : ℝ) ^ (j : ℕ)) *
          (49 * (v : ℝ) * ((j : ℕ) + 1)) := by
        apply mul_le_mul_of_nonneg_left
        · simpa [A, R] using hentropy
        · positivity
      _ = 98 * Real.sqrt m * (v : ℝ) *
          (((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j : ℕ)) := by ring
  have hsum :
      ∑ j : Fin m,
          ((dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j) *
            Real.sqrt (2 * Real.log
              (coveringCard (dyadicRadius R (j + 1)) A *
                coveringCard (dyadicRadius R j) A)) ≤
        392 * Real.sqrt m * (v : ℝ) := by
    calc
      ∑ j : Fin m,
          ((dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j) *
            Real.sqrt (2 * Real.log
              (coveringCard (dyadicRadius R (j + 1)) A *
                coveringCard (dyadicRadius R j) A)) ≤
          ∑ j : Fin m, 98 * Real.sqrt m * (v : ℝ) *
            (((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j : ℕ)) :=
        Finset.sum_le_sum fun j _ ↦ hterm j
      _ = 98 * Real.sqrt m * (v : ℝ) *
          ∑ j : Fin m, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ (j : ℕ) := by
        rw [Finset.mul_sum]
      _ ≤ 98 * Real.sqrt m * (v : ℝ) * 4 := by
        apply mul_le_mul_of_nonneg_left (sum_succ_mul_inv_two_pow_le_four m)
        positivity
      _ = 392 * Real.sqrt m * (v : ℝ) := by ring
  have hterminal :
      (m : ℝ)⁻¹ * (Real.sqrt m * (dyadicRadius R m : ℝ)) =
        (1 / 2 : ℝ) ^ m := by
    rw [show (dyadicRadius R m : ℝ) =
      Real.sqrt m * (1 / 2 : ℝ) ^ m by simp [R, dyadicSqrtRadius_coe]]
    have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
    calc
      (m : ℝ)⁻¹ *
          (Real.sqrt m * (Real.sqrt m * (1 / 2 : ℝ) ^ m)) =
          (m : ℝ)⁻¹ * (Real.sqrt m * Real.sqrt m) * (1 / 2 : ℝ) ^ m := by
        ring
      _ = (m : ℝ)⁻¹ * m * (1 / 2 : ℝ) ^ m := by
        rw [show Real.sqrt m * Real.sqrt m = (m : ℝ) by
          nlinarith [Real.sq_sqrt hmR.le]]
      _ = (1 / 2 : ℝ) ^ m := by field_simp
  calc
    fixedRademacherComplexity (indicatorVectors H) (indicatorVectors_nonempty hH) ≤
        (m : ℝ)⁻¹ *
          (Real.sqrt m * dyadicRadius R m +
            ∑ j : Fin m,
              ((dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j) *
                Real.sqrt (2 * Real.log
                  (coveringCard (dyadicRadius R (j + 1)) A *
                    coveringCard (dyadicRadius R j) A))) := by
      simpa [A] using hdudley
    _ ≤ (m : ℝ)⁻¹ *
        (Real.sqrt m * dyadicRadius R m + 392 * Real.sqrt m * (v : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add le_rfl hsum
      · positivity
    _ = (1 / 2 : ℝ) ^ m + 392 * (v : ℝ) / Real.sqrt m := by
      rw [mul_add, hterminal]
      congr 1
      calc
        (m : ℝ)⁻¹ * (392 * Real.sqrt m * (v : ℝ)) =
            392 * (v : ℝ) * ((m : ℝ)⁻¹ * Real.sqrt m) := by ring
        _ = 392 * (v : ℝ) * (Real.sqrt m)⁻¹ := by
          rw [inv_card_mul_sqrt m hm]
        _ = 392 * (v : ℝ) / Real.sqrt m := by rw [div_eq_mul_inv]
    _ ≤ (Real.sqrt m)⁻¹ + 392 * (v : ℝ) / Real.sqrt m :=
      add_le_add (inv_two_pow_le_inv_sqrt_card m hm) le_rfl
    _ = (1 + 392 * (v : ℝ)) / Real.sqrt m := by
      rw [inv_eq_one_div]
      ring

end OTSelector.Probability.Rademacher
