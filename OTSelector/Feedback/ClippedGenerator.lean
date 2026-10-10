import OTSelector.Feedback.LyapunovCutoff

/-!
# Algebra of the clipped birth--death generator

The cutoff changes only the two one-step increments at the boundary.  This file records the
deterministic identities needed to remove that cutoff on the strict interior of the state
interval, and then transfers the existing cubic drift estimate to the clipped rate.  No
probability, filtration, or stopping-time data is used here.
 -/

namespace OTSelector

/-! ## Clipped rate and strict-interior identities -/

/-- The scalar-rate generator after clipping the integer state. -/
noncomputable def clippedGeneratorRate
    (R : ℕ) (f : ℤ → ℝ) (b d : ℝ) (k : ℤ) : ℝ :=
  b * clippedUpwardIncrement R f k + d * clippedDownwardIncrement R f k

theorem integerClip_eq_self_of_strictInterior
    (R : ℕ) {k : ℤ} (hlo : -(R : ℤ) < k) (hhi : k < (R : ℤ)) :
    integerClip R k = k := by
  apply integerClip_eq_self_of_mem
  rw [cutoffStates, Finset.mem_Icc]
  omega

theorem integerClip_succ_eq_self_of_strictInterior
    (R : ℕ) {k : ℤ} (hlo : -(R : ℤ) < k) (hhi : k < (R : ℤ)) :
    integerClip R (k + 1) = k + 1 := by
  apply integerClip_eq_self_of_mem
  rw [cutoffStates, Finset.mem_Icc]
  omega

theorem integerClip_pred_eq_self_of_strictInterior
    (R : ℕ) {k : ℤ} (hlo : -(R : ℤ) < k) (hhi : k < (R : ℤ)) :
    integerClip R (k - 1) = k - 1 := by
  apply integerClip_eq_self_of_mem
  rw [cutoffStates, Finset.mem_Icc]
  omega

/-! ## Removal of the cutoff -/

theorem clippedGeneratorRate_eq_integerBirthDeathGenerator
    (R : ℕ) (f : ℤ → ℝ) (b d : ℤ → ℝ) (k : ℤ)
    (hlo : -(R : ℤ) < k) (hhi : k < (R : ℤ)) :
    clippedGeneratorRate R f (b k) (d k) k =
      integerBirthDeathGenerator b d f k := by
  rw [clippedGeneratorRate, clippedUpwardIncrement, clippedDownwardIncrement,
    integerClip_succ_eq_self_of_strictInterior R hlo hhi,
    integerClip_eq_self_of_strictInterior R hlo hhi,
    integerClip_pred_eq_self_of_strictInterior R hlo hhi,
    integerBirthDeathGenerator]

theorem clippedGeneratorRate_eq_integerBirthDeathGenerator_const
    (R : ℕ) (f : ℤ → ℝ) (b d : ℝ) (k : ℤ)
    (hlo : -(R : ℤ) < k) (hhi : k < (R : ℤ)) :
    clippedGeneratorRate R f b d k =
      integerBirthDeathGenerator (fun _ : ℤ => b) (fun _ : ℤ => d) f k := by
  simpa using
    (clippedGeneratorRate_eq_integerBirthDeathGenerator R f
      (fun _ : ℤ => b) (fun _ : ℤ => d) k hlo hhi)

/-! ## Cubic drift transfer -/

theorem clippedGeneratorRate_cubicLyapunov_le
    (R : ℕ) (b d : ℤ → ℝ) {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ C)
    (hd : ∀ j, 0 ≤ d j ∧ d j ≤ C)
    (hinward : ∀ j, j ≠ 0 →
      if 0 < j then b j - d j ≤ -c else c ≤ b j - d j)
    (k : ℤ) (hlo : -(R : ℤ) < k) (hhi : k < (R : ℤ)) :
    clippedGeneratorRate R cubicLyapunov (b k) (d k) k ≤
      -(2 * c) * (k : ℝ) ^ 2 + (2 * C + 9 * C ^ 2 / c) := by
  rw [clippedGeneratorRate_eq_integerBirthDeathGenerator R cubicLyapunov b d k hlo hhi]
  exact cubic_generator_drift b d hC hc hb hd hinward k

/-! ## Pointwise cubic drift -/

private lemma cubic_absorb_linear_local {C c x : ℝ} (hc : 0 < c) :
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

theorem cubic_generator_drift_local
    (b d : ℝ) {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c)
    (hb : 0 ≤ b) (hbC : b ≤ C)
    (hd : 0 ≤ d) (hdC : d ≤ C)
    (k : ℤ)
    (hinward : k ≠ 0 →
      if 0 < k then b - d ≤ -c else c ≤ b - d) :
    integerBirthDeathGenerator (fun _ : ℤ => b) (fun _ : ℤ => d)
        cubicLyapunov k ≤
      -(2 * c) * (k : ℝ) ^ 2 + (2 * C + 9 * C ^ 2 / c) := by
  by_cases hk0 : k = 0
  · subst k
    rw [cubic_generator_zero]
    have h2C : 0 ≤ 2 * C := by nlinarith [hC]
    have hfrac : 0 ≤ 9 * C ^ 2 / c := by positivity
    calc
      b + d ≤ 2 * C := by linarith [h2C]
      _ ≤ -(2 * c) * ((0 : ℤ) : ℝ) ^ 2 +
          (2 * C + 9 * C ^ 2 / c) := by
        simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, neg_zero,
          Int.cast_zero, add_zero, zero_add] using le_add_of_nonneg_right hfrac
  · rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
    · have hsign := hinward (ne_of_lt hkneg)
      have hbd : d - b ≤ -c := by
        have hbd' : c ≤ b - d := by
          simpa [not_lt.mpr hkneg.le] using hsign
        linarith
      have hsum : b + d ≤ 2 * C := by linarith
      have hx : 0 ≤ -(k : ℝ) := by
        exact_mod_cast (show 0 ≤ -k by omega)
      have hquad : 3 * (-(k : ℝ)) ^ 2 * (d - b) ≤
          -3 * c * (-(k : ℝ)) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hbd
          (by positivity : 0 ≤ 3 * (-(k : ℝ)) ^ 2)
        nlinarith
      have hlinear : 3 * (-(k : ℝ)) * (b + d) ≤
          6 * C * (-(k : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hsum
          (by positivity : 0 ≤ 3 * (-(k : ℝ)))
        nlinarith
      have hlast : d - b ≤ 0 := by linarith
      have habsorb := cubic_absorb_linear_local hc (C := C) (x := -(k : ℝ))
      calc
        integerBirthDeathGenerator (fun _ : ℤ => b) (fun _ : ℤ => d)
            cubicLyapunov k =
            3 * (-(k : ℝ)) ^ 2 * (d - b) +
              3 * (-(k : ℝ)) * (b + d) + (d - b) := by
          simpa using cubic_generator_neg (fun _ : ℤ => b) (fun _ : ℤ => d) hkneg
        _ ≤ -3 * c * (-(k : ℝ)) ^ 2 + 6 * C * (-(k : ℝ)) := by
          linarith
        _ ≤ -2 * c * (-(k : ℝ)) ^ 2 + 9 * C ^ 2 / c := by
          linarith
        _ ≤ -(2 * c) * (k : ℝ) ^ 2 + (2 * C + 9 * C ^ 2 / c) := by
          have hk_sq : (-(k : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by ring
          rw [hk_sq]
          linarith
    · have hsign := hinward (ne_of_gt hkpos)
      have hbd : b - d ≤ -c := by simpa [hkpos] using hsign
      have hsum : b + d ≤ 2 * C := by linarith
      have hquad : 3 * (k : ℝ) ^ 2 * (b - d) ≤
          -3 * c * (k : ℝ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hbd
          (by positivity : 0 ≤ 3 * (k : ℝ) ^ 2)
        nlinarith
      have hlinear : 3 * (k : ℝ) * (b + d) ≤ 6 * C * (k : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hsum
          (by positivity : 0 ≤ 3 * (k : ℝ))
        nlinarith
      have hlast : b - d ≤ 0 := by linarith
      have habsorb := cubic_absorb_linear_local hc (C := C) (x := (k : ℝ))
      calc
        integerBirthDeathGenerator (fun _ : ℤ => b) (fun _ : ℤ => d)
            cubicLyapunov k =
            3 * (k : ℝ) ^ 2 * (b - d) +
              3 * (k : ℝ) * (b + d) + (b - d) := by
          simpa using cubic_generator_pos (fun _ : ℤ => b) (fun _ : ℤ => d) hkpos
        _ ≤ -3 * c * (k : ℝ) ^ 2 + 6 * C * (k : ℝ) := by
          linarith
        _ ≤ -2 * c * (k : ℝ) ^ 2 + 9 * C ^ 2 / c := by
          linarith
        _ ≤ -(2 * c) * (k : ℝ) ^ 2 + (2 * C + 9 * C ^ 2 / c) := by
          linarith

theorem clippedGeneratorRate_cubicLyapunov_le_local
    (R : ℕ) (b d : ℝ) {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c)
    (hb : 0 ≤ b) (hbC : b ≤ C)
    (hd : 0 ≤ d) (hdC : d ≤ C)
    (k : ℤ)
    (hinward : k ≠ 0 →
      if 0 < k then b - d ≤ -c else c ≤ b - d)
    (hlo : -(R : ℤ) < k) (hhi : k < (R : ℤ)) :
    clippedGeneratorRate R cubicLyapunov b d k ≤
      -(2 * c) * (k : ℝ) ^ 2 + (2 * C + 9 * C ^ 2 / c) := by
  rw [clippedGeneratorRate_eq_integerBirthDeathGenerator_const R
    cubicLyapunov b d k hlo hhi]
  exact cubic_generator_drift_local b d hC hc hb hbC hd hdC k hinward

end OTSelector
