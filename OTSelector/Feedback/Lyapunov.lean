import Mathlib.Analysis.Complex.Exponential
import OTSelector.Feedback.CrossingRates

/-!
# Deterministic Lyapunov algebra for integer birth--death generators

This file contains only the finite-dimensional generator calculations used by A1.  The rates are
arbitrary pointwise functions on `ℤ`; no path, intensity, martingale, or stopping-time hypothesis
is introduced here.
-/

namespace OTSelector

/-! ## Generator and Lyapunov functions -/

/-- The generator with upward rate `b` and downward rate `d`. -/
def integerBirthDeathGenerator (b d f : ℤ → ℝ) (k : ℤ) : ℝ :=
  b k * (f (k + 1) - f k) + d k * (f (k - 1) - f k)

/-- The cubic current energy `V(k) = |k|^3`. -/
def cubicLyapunov (k : ℤ) : ℝ :=
  |(k : ℝ)| ^ 3

/-- The exponential current energy `W(k) = exp (θ |k|)`. -/
noncomputable def exponentialLyapunov (theta : ℝ) (k : ℤ) : ℝ :=
  Real.exp (theta * |(k : ℝ)|)

/-! ## Exact cubic differences -/

theorem cubicLyapunov_forward_diff_pos {k : ℤ} (hk : 0 < k) :
    cubicLyapunov (k + 1) - cubicLyapunov k =
      3 * (k : ℝ) ^ 2 + 3 * (k : ℝ) + 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  simp only [cubicLyapunov, Int.cast_add, Int.cast_one]
  rw [abs_of_pos hkR, abs_of_pos (by linarith : 0 < (k : ℝ) + 1)]
  ring

theorem cubicLyapunov_backward_diff_pos {k : ℤ} (hk : 0 < k) :
    cubicLyapunov (k - 1) - cubicLyapunov k =
      -3 * (k : ℝ) ^ 2 + 3 * (k : ℝ) - 1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1R : 0 ≤ (k : ℝ) - 1 := by
    have hk1 : (1 : ℤ) ≤ k := by omega
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  simp only [cubicLyapunov, Int.cast_sub, Int.cast_one]
  rw [abs_of_nonneg hk1R, abs_of_pos hkR]
  ring

theorem cubicLyapunov_forward_diff_neg {k : ℤ} (hk : k < 0) :
    cubicLyapunov (k + 1) - cubicLyapunov k =
      -3 * (-(k : ℝ)) ^ 2 + 3 * (-(k : ℝ)) - 1 := by
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hk_le : k ≤ -1 := by omega
  have hkp1R : (k : ℝ) + 1 ≤ 0 := by
    have hk_le' : (k : ℝ) ≤ -1 := by exact_mod_cast hk_le
    linarith
  simp only [cubicLyapunov, Int.cast_add, Int.cast_one]
  rw [abs_of_nonpos hkp1R, abs_of_neg hkR]
  ring

theorem cubicLyapunov_backward_diff_neg {k : ℤ} (hk : k < 0) :
    cubicLyapunov (k - 1) - cubicLyapunov k =
      3 * (-(k : ℝ)) ^ 2 + 3 * (-(k : ℝ)) + 1 := by
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hkm1R : (k : ℝ) - 1 < 0 := by linarith
  simp only [cubicLyapunov, Int.cast_sub, Int.cast_one]
  rw [abs_of_neg hkm1R, abs_of_neg hkR]
  ring

theorem cubicLyapunov_forward_diff_zero :
    cubicLyapunov (1 : ℤ) - cubicLyapunov 0 = 1 := by
  norm_num [cubicLyapunov]

theorem cubicLyapunov_backward_diff_zero :
    cubicLyapunov (-1 : ℤ) - cubicLyapunov 0 = 1 := by
  norm_num [cubicLyapunov]

/-! ## Exact exponential differences -/

theorem exponentialLyapunov_forward_diff_pos {theta : ℝ} {k : ℤ} (hk : 0 < k) :
    exponentialLyapunov theta (k + 1) - exponentialLyapunov theta k =
      exponentialLyapunov theta k * (Real.exp theta - 1) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  simp only [exponentialLyapunov, Int.cast_add, Int.cast_one]
  rw [abs_of_pos hkR, abs_of_pos (by linarith : 0 < (k : ℝ) + 1)]
  rw [show theta * ((k : ℝ) + 1) = theta * (k : ℝ) + theta by ring, Real.exp_add]
  ring

theorem exponentialLyapunov_backward_diff_pos {theta : ℝ} {k : ℤ} (hk : 0 < k) :
    exponentialLyapunov theta (k - 1) - exponentialLyapunov theta k =
      exponentialLyapunov theta k * (Real.exp (-theta) - 1) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1R : 0 ≤ (k : ℝ) - 1 := by
    have hk1 : (1 : ℤ) ≤ k := by omega
    have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  simp only [exponentialLyapunov, Int.cast_sub, Int.cast_one]
  rw [abs_of_nonneg hk1R, abs_of_pos hkR]
  rw [show theta * ((k : ℝ) - 1) = theta * (k : ℝ) + (-theta) by ring,
    Real.exp_add]
  ring

theorem exponentialLyapunov_forward_diff_neg {theta : ℝ} {k : ℤ} (hk : k < 0) :
    exponentialLyapunov theta (k + 1) - exponentialLyapunov theta k =
      exponentialLyapunov theta k * (Real.exp (-theta) - 1) := by
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hk_le : k ≤ -1 := by omega
  have hkp1R : (k : ℝ) + 1 ≤ 0 := by
    have hk_le' : (k : ℝ) ≤ -1 := by exact_mod_cast hk_le
    linarith
  simp only [exponentialLyapunov, Int.cast_add, Int.cast_one]
  rw [abs_of_nonpos hkp1R, abs_of_neg hkR]
  rw [show theta * (-((k : ℝ) + 1)) = theta * (-(k : ℝ)) + (-theta) by ring,
    Real.exp_add]
  ring

theorem exponentialLyapunov_backward_diff_neg {theta : ℝ} {k : ℤ} (hk : k < 0) :
    exponentialLyapunov theta (k - 1) - exponentialLyapunov theta k =
      exponentialLyapunov theta k * (Real.exp theta - 1) := by
  have hkR : (k : ℝ) < 0 := by exact_mod_cast hk
  have hkm1R : (k : ℝ) - 1 < 0 := by linarith
  simp only [exponentialLyapunov, Int.cast_sub, Int.cast_one]
  rw [abs_of_neg hkm1R, abs_of_neg hkR]
  rw [show theta * (-((k : ℝ) - 1)) = theta * (-(k : ℝ)) + theta by ring,
    Real.exp_add]
  ring

theorem exponentialLyapunov_forward_diff_zero (theta : ℝ) :
    exponentialLyapunov theta (1 : ℤ) - exponentialLyapunov theta 0 = Real.exp theta - 1 := by
  simp [exponentialLyapunov]

theorem exponentialLyapunov_backward_diff_zero (theta : ℝ) :
    exponentialLyapunov theta (-1 : ℤ) - exponentialLyapunov theta 0 = Real.exp theta - 1 := by
  simp [exponentialLyapunov]

/-! ## Exact generator formulas -/

theorem cubic_generator_pos (b d : ℤ → ℝ) {k : ℤ} (hk : 0 < k) :
    integerBirthDeathGenerator b d cubicLyapunov k =
      3 * (k : ℝ) ^ 2 * (b k - d k) +
        3 * (k : ℝ) * (b k + d k) + (b k - d k) := by
  rw [integerBirthDeathGenerator, cubicLyapunov_forward_diff_pos hk,
    cubicLyapunov_backward_diff_pos hk]
  ring

theorem cubic_generator_neg (b d : ℤ → ℝ) {k : ℤ} (hk : k < 0) :
    integerBirthDeathGenerator b d cubicLyapunov k =
      3 * (-(k : ℝ)) ^ 2 * (d k - b k) +
        3 * (-(k : ℝ)) * (b k + d k) + (d k - b k) := by
  rw [integerBirthDeathGenerator, cubicLyapunov_forward_diff_neg hk,
    cubicLyapunov_backward_diff_neg hk]
  ring

theorem cubic_generator_zero (b d : ℤ → ℝ) :
    integerBirthDeathGenerator b d cubicLyapunov 0 = b 0 + d 0 := by
  rw [integerBirthDeathGenerator]
  simp [cubicLyapunov]

theorem exponential_generator_pos (b d : ℤ → ℝ) {theta : ℝ} {k : ℤ} (hk : 0 < k) :
    integerBirthDeathGenerator b d (exponentialLyapunov theta) k =
      exponentialLyapunov theta k *
        (b k * (Real.exp theta - 1) + d k * (Real.exp (-theta) - 1)) := by
  rw [integerBirthDeathGenerator, exponentialLyapunov_forward_diff_pos hk,
    exponentialLyapunov_backward_diff_pos hk]
  ring

theorem exponential_generator_neg (b d : ℤ → ℝ) {theta : ℝ} {k : ℤ} (hk : k < 0) :
    integerBirthDeathGenerator b d (exponentialLyapunov theta) k =
      exponentialLyapunov theta k *
        (b k * (Real.exp (-theta) - 1) + d k * (Real.exp theta - 1)) := by
  rw [integerBirthDeathGenerator, exponentialLyapunov_forward_diff_neg hk,
    exponentialLyapunov_backward_diff_neg hk]
  ring

theorem exponential_generator_zero (b d : ℤ → ℝ) (theta : ℝ) :
    integerBirthDeathGenerator b d (exponentialLyapunov theta) 0 =
      (b 0 + d 0) * (Real.exp theta - 1) := by
  change b 0 * (exponentialLyapunov theta (1 : ℤ) - exponentialLyapunov theta 0) +
      d 0 * (exponentialLyapunov theta (-1 : ℤ) - exponentialLyapunov theta 0) = _
  rw [exponentialLyapunov_forward_diff_zero, exponentialLyapunov_backward_diff_zero]
  ring

/-! ## Cubic drift bound -/

private lemma cubic_absorb_linear {C c x : ℝ} (hc : 0 < c) :
    6 * C * x ≤ c * x ^ 2 + 9 * C ^ 2 / c := by
  have hsquare : 0 ≤ (c * x - 3 * C) ^ 2 := sq_nonneg _
  have hscaled : 6 * C * x * c ≤ (c * x) ^ 2 + 9 * C ^ 2 := by
    nlinarith [hsquare]
  have hrewrite : c * x ^ 2 + 9 * C ^ 2 / c =
      (c * (c * x ^ 2) + 9 * C ^ 2) / c := by
    field_simp [ne_of_gt hc]
  rw [hrewrite]
  apply (le_div_iff₀ hc).2
  nlinarith [hscaled]

/-- Cubic Lyapunov drift under bounded rates and a uniform inward drift.

The explicit constants are `c₁ = 2c` and `C₁ = 2C + 9 C²/c`:
`L V(k) ≤ -c₁ (k : ℝ)² + C₁`.
-/
theorem cubic_generator_drift
    (b d : ℤ → ℝ) {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c)
    (hb : ∀ k, 0 ≤ b k ∧ b k ≤ C)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ C)
    (hinward : ∀ k, k ≠ 0 →
      if 0 < k then b k - d k ≤ -c else c ≤ b k - d k)
    (k : ℤ) :
    integerBirthDeathGenerator b d cubicLyapunov k ≤
      -(2 * c) * (k : ℝ) ^ 2 + (2 * C + 9 * C ^ 2 / c) := by
  by_cases hk0 : k = 0
  · subst k
    rw [cubic_generator_zero]
    calc
      b 0 + d 0 ≤ 2 * C := by nlinarith [(hb 0).2, (hd 0).2]
      _ ≤ -(2 * c) * ((0 : ℤ) : ℝ) ^ 2 + (2 * C + 9 * C ^ 2 / c) := by
        have hfrac : 0 ≤ 9 * C ^ 2 / c := by positivity
        have hle : 2 * C ≤ 2 * C + 9 * C ^ 2 / c := by linarith
        simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, neg_zero,
          Int.cast_zero, add_zero, zero_add] using hle
  · rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
    · have hsign := hinward k (ne_of_lt hkneg)
      have hbd : d k - b k ≤ -c := by
        have hbd' : c ≤ b k - d k := by
          simpa [not_lt.mpr hkneg.le] using hsign
        linarith
      have hsum : b k + d k ≤ 2 * C := by nlinarith [(hb k).2, (hd k).2]
      have hx : 0 ≤ -(k : ℝ) := by exact_mod_cast (show 0 ≤ -k by omega)
      have hquad : 3 * (-(k : ℝ)) ^ 2 * (d k - b k) ≤
          -3 * c * (-(k : ℝ)) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hbd (by positivity : 0 ≤ 3 * (-(k : ℝ)) ^ 2)
        nlinarith
      have hlinear : 3 * (-(k : ℝ)) * (b k + d k) ≤ 6 * C * (-(k : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3 * (-(k : ℝ)))
        nlinarith
      have hlast : d k - b k ≤ 0 := by linarith
      have habsorb := cubic_absorb_linear hc (C := C) (x := -(k : ℝ))
      calc
        integerBirthDeathGenerator b d cubicLyapunov k =
            3 * (-(k : ℝ)) ^ 2 * (d k - b k) +
              3 * (-(k : ℝ)) * (b k + d k) + (d k - b k) :=
          cubic_generator_neg b d hkneg
        _ ≤ -3 * c * (-(k : ℝ)) ^ 2 + 6 * C * (-(k : ℝ)) := by
          linarith
        _ ≤ -2 * c * (-(k : ℝ)) ^ 2 + 9 * C ^ 2 / c := by
          linarith
        _ ≤ -(2 * c) * (k : ℝ) ^ 2 + (2 * C + 9 * C ^ 2 / c) := by
          have hk_sq : (-(k : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by ring
          rw [hk_sq]
          linarith
    · have hsign := hinward k (ne_of_gt hkpos)
      have hbd : b k - d k ≤ -c := by simpa [hkpos] using hsign
      have hsum : b k + d k ≤ 2 * C := by nlinarith [(hb k).2, (hd k).2]
      have hquad : 3 * (k : ℝ) ^ 2 * (b k - d k) ≤ -3 * c * (k : ℝ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hbd (by positivity : 0 ≤ 3 * (k : ℝ) ^ 2)
        nlinarith
      have hlinear : 3 * (k : ℝ) * (b k + d k) ≤ 6 * C * (k : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3 * (k : ℝ))
        nlinarith
      have hlast : b k - d k ≤ 0 := by linarith
      have habsorb := cubic_absorb_linear hc (C := C) (x := (k : ℝ))
      calc
        integerBirthDeathGenerator b d cubicLyapunov k =
            3 * (k : ℝ) ^ 2 * (b k - d k) +
              3 * (k : ℝ) * (b k + d k) + (b k - d k) :=
          cubic_generator_pos b d hkpos
        _ ≤ -3 * c * (k : ℝ) ^ 2 + 6 * C * (k : ℝ) := by
          linarith
        _ ≤ -2 * c * (k : ℝ) ^ 2 + 9 * C ^ 2 / c := by
          linarith
        _ ≤ -(2 * c) * (k : ℝ) ^ 2 + (2 * C + 9 * C ^ 2 / c) := by
          linarith

/-! ## Exponential drift bound -/

private lemma exp_sym_nonneg (theta : ℝ) :
    0 ≤ Real.exp theta + Real.exp (-theta) - 2 := by
  have h₁ := Real.add_one_le_exp theta
  have h₂ := Real.add_one_le_exp (-theta)
  linarith

private lemma exp_sub_one_pos {theta : ℝ} (hθ : 0 < theta) :
    0 < Real.exp theta - 1 := by
  have h := Real.add_one_le_exp theta
  linarith

/-- A direct small-`θ` condition implying the exponential balance inequality. -/
theorem exponential_balance_of_small_theta
    {C c theta : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (hθC : 4 * C * theta ≤ c) :
    C * (Real.exp theta + Real.exp (-theta) - 2) ≤
      (c / 2) * (Real.exp theta - 1) := by
  have hθabs : |theta| ≤ 1 := by simpa [abs_of_pos hθ] using hθ1
  have hnegabs : |-theta| ≤ 1 := by simpa [abs_neg, abs_of_pos hθ] using hθ1
  have hplus : Real.exp theta - 1 - theta ≤ theta ^ 2 := by
    exact (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hθabs)
  have hminus : Real.exp (-theta) - 1 + theta ≤ theta ^ 2 := by
    have h := (le_abs_self (Real.exp (-theta) - 1 - (-theta))).trans
      (Real.abs_exp_sub_one_sub_id_le hnegabs)
    simpa [sub_neg_eq_add] using h
  have hsym : Real.exp theta + Real.exp (-theta) - 2 ≤ 2 * theta ^ 2 := by
    linarith
  have hsym_mul := mul_le_mul_of_nonneg_left hsym hC
  have hθC_mul := mul_le_mul_of_nonneg_right hθC hθ.le
  have hquad : 2 * C * theta ^ 2 ≤ (c / 2) * theta := by
    nlinarith
  have hexp : theta ≤ Real.exp theta - 1 := by
    have h := Real.add_one_le_exp theta
    linarith
  have hexp_mul := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ c / 2)
  nlinarith

private lemma exponential_outward_bracket_le
    {rin rout C c theta : ℝ}
    (hθ : 0 < theta)
    (hbalance : C * (Real.exp theta + Real.exp (-theta) - 2) ≤
      (c / 2) * (Real.exp theta - 1))
    (hbound : rout ≤ C)
    (hinward : rin - rout ≤ -c) :
    rin * (Real.exp theta - 1) + rout * (Real.exp (-theta) - 1) ≤
      -(c / 2) * (Real.exp theta - 1) := by
  have hplus : 0 ≤ Real.exp theta - 1 := (exp_sub_one_pos hθ).le
  have hsym : 0 ≤ Real.exp theta + Real.exp (-theta) - 2 := exp_sym_nonneg theta
  have hfirst := mul_le_mul_of_nonneg_right hinward hplus
  have hsecond := mul_le_mul_of_nonneg_right hbound hsym
  calc
    rin * (Real.exp theta - 1) + rout * (Real.exp (-theta) - 1) =
        (rin - rout) * (Real.exp theta - 1) +
          rout * (Real.exp theta + Real.exp (-theta) - 2) := by ring
    _ ≤ (-c) * (Real.exp theta - 1) +
          C * (Real.exp theta + Real.exp (-theta) - 2) :=
      add_le_add hfirst hsecond
    _ ≤ -(c / 2) * (Real.exp theta - 1) := by linarith

private lemma exponential_generator_nonzero_bound
    (b d : ℤ → ℝ) {C c theta : ℝ}
    (hθ : 0 < theta)
    (hbalance : C * (Real.exp theta + Real.exp (-theta) - 2) ≤
      (c / 2) * (Real.exp theta - 1))
    (hb : ∀ k, 0 ≤ b k ∧ b k ≤ C)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ C)
    (hinward : ∀ k, k ≠ 0 →
      if 0 < k then b k - d k ≤ -c else c ≤ b k - d k)
    {k : ℤ} (hk : k ≠ 0) :
    integerBirthDeathGenerator b d (exponentialLyapunov theta) k ≤
      -(c / 2 * (Real.exp theta - 1)) * exponentialLyapunov theta k := by
  rcases lt_or_gt_of_ne hk with hkneg | hkpos
  · have hsign := hinward k (ne_of_lt hkneg)
    have hdb : d k - b k ≤ -c := by
      have hdb' : c ≤ b k - d k := by
        simpa [not_lt.mpr hkneg.le] using hsign
      linarith
    have hbracket := exponential_outward_bracket_le hθ hbalance (hb k).2 hdb
    calc
      integerBirthDeathGenerator b d (exponentialLyapunov theta) k =
          exponentialLyapunov theta k *
            (b k * (Real.exp (-theta) - 1) + d k * (Real.exp theta - 1)) :=
        exponential_generator_neg b d hkneg
      _ = exponentialLyapunov theta k *
          (d k * (Real.exp theta - 1) + b k * (Real.exp (-theta) - 1)) := by ring
      _ ≤ exponentialLyapunov theta k * (-(c / 2) * (Real.exp theta - 1)) := by
        exact mul_le_mul_of_nonneg_left hbracket (Real.exp_pos _).le
      _ = -(c / 2 * (Real.exp theta - 1)) * exponentialLyapunov theta k := by ring
  · have hsign := hinward k (ne_of_gt hkpos)
    have hbd : b k - d k ≤ -c := by simpa [hkpos] using hsign
    have hbracket := exponential_outward_bracket_le hθ hbalance (hd k).2 hbd
    calc
      integerBirthDeathGenerator b d (exponentialLyapunov theta) k =
          exponentialLyapunov theta k *
            (b k * (Real.exp theta - 1) + d k * (Real.exp (-theta) - 1)) :=
        exponential_generator_pos b d hkpos
      _ ≤ exponentialLyapunov theta k * (-(c / 2) * (Real.exp theta - 1)) := by
        exact mul_le_mul_of_nonneg_left hbracket (Real.exp_pos _).le
      _ = -(c / 2 * (Real.exp theta - 1)) * exponentialLyapunov theta k := by ring

/-- Exponential Lyapunov drift with an explicit balance condition.

For `a = c (exp θ - 1) / 2` and `b₀ = (2C + c/2)(exp θ - 1)`, this gives
`L W ≤ -a W + b₀` at every integer state, including the origin.
-/
theorem exponential_generator_drift
    (b d : ℤ → ℝ) {C c theta : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hθ : 0 < theta)
    (hbalance : C * (Real.exp theta + Real.exp (-theta) - 2) ≤
      (c / 2) * (Real.exp theta - 1))
    (hb : ∀ k, 0 ≤ b k ∧ b k ≤ C)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ C)
    (hinward : ∀ k, k ≠ 0 →
      if 0 < k then b k - d k ≤ -c else c ≤ b k - d k)
    (k : ℤ) :
    integerBirthDeathGenerator b d (exponentialLyapunov theta) k ≤
      -(c / 2 * (Real.exp theta - 1)) * exponentialLyapunov theta k +
        (2 * C + c / 2) * (Real.exp theta - 1) := by
  have hplus : 0 ≤ Real.exp theta - 1 := (exp_sub_one_pos hθ).le
  by_cases hk0 : k = 0
  · subst k
    rw [exponential_generator_zero]
    calc
      (b 0 + d 0) * (Real.exp theta - 1) ≤ 2 * C * (Real.exp theta - 1) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [(hb 0).2, (hd 0).2]) hplus
      _ = -(c / 2 * (Real.exp theta - 1)) * exponentialLyapunov theta 0 +
          (2 * C + c / 2) * (Real.exp theta - 1) := by
        simp [exponentialLyapunov]
        ring
  · have hnon := exponential_generator_nonzero_bound b d hθ hbalance hb hd hinward hk0
    have hoff : 0 ≤ (2 * C + c / 2) * (Real.exp theta - 1) := by positivity
    calc
      integerBirthDeathGenerator b d (exponentialLyapunov theta) k ≤
          -(c / 2 * (Real.exp theta - 1)) * exponentialLyapunov theta k := hnon
      _ ≤ -(c / 2 * (Real.exp theta - 1)) * exponentialLyapunov theta k +
          (2 * C + c / 2) * (Real.exp theta - 1) := by linarith

/-- The preceding exponential drift theorem under the simple sufficient conditions `0 < θ ≤ 1`
and `4 C θ ≤ c`. -/
theorem exponential_generator_drift_of_small_theta
    (b d : ℤ → ℝ) {C c theta : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (hθC : 4 * C * theta ≤ c)
    (hb : ∀ k, 0 ≤ b k ∧ b k ≤ C)
    (hd : ∀ k, 0 ≤ d k ∧ d k ≤ C)
    (hinward : ∀ k, k ≠ 0 →
      if 0 < k then b k - d k ≤ -c else c ≤ b k - d k)
    (k : ℤ) :
    integerBirthDeathGenerator b d (exponentialLyapunov theta) k ≤
      -(c / 2 * (Real.exp theta - 1)) * exponentialLyapunov theta k +
        (2 * C + c / 2) * (Real.exp theta - 1) := by
  apply exponential_generator_drift b d hC hc hθ
    (exponential_balance_of_small_theta hC hc.le hθ hθ1 hθC) hb hd hinward k

theorem exponential_decay_coefficient_pos {c theta : ℝ} (hc : 0 < c) (hθ : 0 < theta) :
    0 < c / 2 * (Real.exp theta - 1) := by
  exact mul_pos (div_pos hc (by norm_num)) (exp_sub_one_pos hθ)

end OTSelector
