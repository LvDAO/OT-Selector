import OTSelector.Limit.FeedbackInvariant

/-!
# Uniqueness of the normalized feedback balance equations

Summability makes the constant probability flux vanish. The resulting nearest-neighbor
detailed balance determines every mass from its value at zero, and normalization fixes that value.
-/

open Filter
open scoped Topology

namespace OTSelector.Limit

theorem birthRate_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    0 < birthRate lam k := by
  cases k with
  | ofNat n => cases n <;> simp only [birthRate, currentSign] <;> nlinarith
  | negSucc n => simp only [birthRate, currentSign]; nlinarith

theorem deathRate_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (k : ℤ) :
    0 < deathRate lam k := by
  cases k with
  | ofNat n => cases n <;> simp only [deathRate, currentSign] <;> nlinarith
  | negSucc n => simp only [deathRate, currentSign]; nlinarith

private theorem int_eq_zero_of_eq_add_one {f : ℤ → ℝ}
    (h : ∀ k, f (k + 1) = f k) (k : ℤ) : f k = f 0 := by
  induction k using Int.induction_on with
  | zero => rfl
  | succ n ih => rw [h, ih]
  | pred n ih =>
    have hh := h (-(n : ℤ) - 1)
    rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by omega, ih] at hh
    exact hh.symm

/-- Summable global balance has zero flux across each nearest-neighbor cut. -/
theorem feedback_detailed_balance_of_global_balance {lam : ℝ} {p : ℤ → ℝ}
    (hp : Summable p)
    (hbal : ∀ k, p k * (birthRate lam k + deathRate lam k) =
      p (k - 1) * birthRate lam (k - 1) + p (k + 1) * deathRate lam (k + 1)) :
    ∀ k, p k * birthRate lam k = p (k + 1) * deathRate lam (k + 1) := by
  let F : ℤ → ℝ := fun k ↦ p k * birthRate lam k - p (k + 1) * deathRate lam (k + 1)
  have hstep (k : ℤ) : F (k + 1) = F k := by
    have h := hbal (k + 1)
    simp only [add_sub_cancel_right] at h
    dsimp [F]
    nlinarith only [h]
  have hconst := int_eq_zero_of_eq_add_one hstep
  have h₁ : Summable (fun n : ℕ ↦ p ((n : ℤ) + 1)) :=
    hp.comp_injective (fun _ _ h ↦ by omega)
  have h₂ : Summable (fun n : ℕ ↦ p ((n : ℤ) + 2)) :=
    hp.comp_injective (fun _ _ h ↦ by omega)
  have hlim := (h₁.tendsto_atTop_zero.mul_const (1 - lam / 2)).sub
    (h₂.tendsto_atTop_zero.mul_const (1 + 3 * lam / 2))
  have heq : (fun n : ℕ ↦ p ((n : ℤ) + 1) * (1 - lam / 2) -
      p ((n : ℤ) + 2) * (1 + 3 * lam / 2)) = fun _ : ℕ ↦ F 0 := by
    funext n
    have h := hconst ((n : ℤ) + 1)
    have hs₁ : currentSign ((n : ℤ) + 1) = 1 := currentSign_nat_add_one n
    have hs₂ : currentSign ((n : ℤ) + 2) = 1 := by
      have he : (n : ℤ) + 2 = ((n + 1 : ℕ) : ℤ) + 1 := by omega
      rw [he]
      exact currentSign_nat_add_one (n + 1)
    simpa only [F, birthRate, deathRate,
      show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring, hs₁, hs₂, mul_one] using h
  rw [heq] at hlim
  have hz : F 0 = 0 := by simpa using hlim
  intro k
  have h := hconst k
  rw [hz] at h
  exact sub_eq_zero.mp h

/-- The explicit invariant mass is the unique summable normalized solution of the actual
feedback generator balance equations. Nonnegativity need not be assumed separately. -/
theorem feedback_invariantMass_unique {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {p : ℤ → ℝ} (hp : Summable p) (hnorm : ∑' k, p k = 1)
    (hbal : ∀ k, p k * (birthRate lam k + deathRate lam k) =
      p (k - 1) * birthRate lam (k - 1) + p (k + 1) * deathRate lam (k + 1)) :
    p = invariantMass lam := by
  have hd := feedback_detailed_balance_of_global_balance hp hbal
  have hzero : invariantMass lam 0 ≠ 0 := by
    rw [invariantMass_zero, centralMass]
    exact div_ne_zero hlam0.ne' (by linarith)
  let c := p 0 / invariantMass lam 0
  have hprop (k : ℤ) : p k = c * invariantMass lam k := by
    induction k using Int.induction_on with
    | zero => exact (div_mul_cancel₀ _ hzero).symm
    | succ n ih =>
      apply mul_right_cancel₀ (deathRate_pos hlam0 hlam ((n : ℤ) + 1)).ne'
      have h₁ := hd (n : ℤ)
      have h₂ := detailed_balance hlam0 hlam (n : ℤ)
      rw [ih] at h₁
      nlinarith only [h₁, congrArg (c * ·) h₂]
    | pred n ih =>
      apply mul_right_cancel₀ (birthRate_pos hlam0 hlam (-(n : ℤ) - 1)).ne'
      have h₁ := hd (-(n : ℤ) - 1)
      have h₂ := detailed_balance hlam0 hlam (-(n : ℤ) - 1)
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by omega] at h₁ h₂
      rw [ih] at h₁
      nlinarith only [h₁, congrArg (c * ·) h₂]
  have hc : c = 1 := by
    have heq : p = fun k ↦ c * invariantMass lam k := funext hprop
    rw [heq, tsum_mul_left, tsum_invariantMass hlam0 hlam, mul_one] at hnorm
    exact hnorm
  funext k
  rw [hprop, hc, one_mul]

end OTSelector.Limit
