import OTSelector.Gauge.PeanoHinge
import OTSelector.Feedback.Graph
import Mathlib.Algebra.Polynomial.Roots

/-!
# The kinetic gauge and finite alternating-tie fibres

The local quadratic cost differs from the kinetic cost only by source and target potentials.
Varying one source mark leaves a rational cost difference with two distinct poles. Its level
sets are finite, which is the deterministic nondegeneracy needed for the no-cycle-ties argument.
-/

open Set Polynomial MeasureTheory
open scoped BigOperators

namespace OTSelector

/-- Physical kinetic cost in the feedback coordinates, with source and target slopes `a,b`. -/
noncomputable def kineticCost (g : ℝ → ℝ) (xi eta a b : ℝ) : ℝ :=
  (eta - xi + a * g xi + b * g eta) ^ 2 / (2 * (a + b))

/-- Exact row/column decomposition, valid in either spatial endpoint order. -/
theorem quadraticCost_eq_kineticCost {g : ℝ → ℝ} (hg : Continuous g)
    {xi eta a b : ℝ} (hD : a + b ≠ 0) :
    quadraticCost g xi eta a b = kineticCost g xi eta a b +
      ((∫ x in 0..xi, g x) - a * g xi ^ 2 / 2) +
      (-(∫ x in 0..eta, g x) - b * g eta ^ 2 / 2) := by
  have hi := intervalIntegral.integral_interval_sub_left
    (hg.intervalIntegrable (μ := volume) 0 eta) (hg.intervalIntegrable (μ := volume) 0 xi)
  unfold quadraticCost gaugedFourPointCost fourPointQuotient fourPointDenominator
    fourPointGap fourPointSourceValue fourPointTargetValue kineticCost
  simp only [id_eq]
  rw [← hi]
  field_simp
  ring

/-- Finite target permutations cancel precisely the same row and column potentials. -/
theorem sum_quadraticCost_sub_eq_sum_kineticCost_sub
    {J : Type*} [Fintype J] {g : ℝ → ℝ} (hg : Continuous g)
    (xi eta a b : J → ℝ) (tau : Equiv.Perm J)
    (hD : ∀ i j, a i + b j ≠ 0) :
    (∑ i, quadraticCost g (xi i) (eta i) (a i) (b i)) -
        (∑ i, quadraticCost g (xi i) (eta (tau i)) (a i) (b (tau i))) =
      (∑ i, kineticCost g (xi i) (eta i) (a i) (b i)) -
        (∑ i, kineticCost g (xi i) (eta (tau i)) (a i) (b (tau i))) := by
  simp_rw [quadraticCost_eq_kineticCost hg (hD _ _), Finset.sum_add_distrib]
  rw [Equiv.sum_comp tau (fun i ↦ -(∫ x in 0..eta i, g x) - b i * g (eta i) ^ 2 / 2)]
  ring

/-- A nonzero pole residue makes the rational cost difference nonconstant. -/
theorem finite_kinetic_difference_fibre
    (d₁ d₂ p q₁ q₂ b₁ b₂ c : ℝ) (hb : b₁ ≠ b₂)
    (hres : d₁ + b₁ * (q₁ - p) ≠ 0) :
    {a : ℝ | a + b₁ ≠ 0 ∧ a + b₂ ≠ 0 ∧
      (d₁ + a * p + b₁ * q₁) ^ 2 / (2 * (a + b₁)) -
        (d₂ + a * p + b₂ * q₂) ^ 2 / (2 * (a + b₂)) = c}.Finite := by
  let P : Polynomial ℝ :=
    (C d₁ + X * C p + C (b₁ * q₁)) ^ 2 * (X + C b₂) -
      (C d₂ + X * C p + C (b₂ * q₂)) ^ 2 * (X + C b₁) -
      C (2 * c) * (X + C b₁) * (X + C b₂)
  have hpole : P.eval (-b₁) = (d₁ + b₁ * (q₁ - p)) ^ 2 * (b₂ - b₁) := by
    simp only [P, eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X]
    ring
  have hP : P ≠ 0 := by
    intro h
    have hz : P.eval (-b₁) = 0 := by rw [h, eval_zero]
    rw [hpole] at hz
    exact (mul_ne_zero (pow_ne_zero 2 hres) (sub_ne_zero.mpr hb.symm)) hz
  apply (Polynomial.finite_setOfPred_isRoot hP).subset
  rintro a ⟨h₁, h₂, h⟩
  change P.eval a = 0
  simp only [P, eval_sub, eval_mul, eval_pow, eval_add, eval_C, eval_X]
  field_simp at h
  nlinarith only [h]

/-- Spacelike feedback slopes keep the pole residue nonzero at distinct event coordinates. -/
theorem kinetic_pole_residue_ne_zero {g : ℝ → ℝ} {lam xi eta b : ℝ}
    (hg : RealLipschitz lam g) (hb : 0 ≤ b) (hsmall : b * lam < 1)
    (hne : eta ≠ xi) : eta - xi + b * (g eta - g xi) ≠ 0 := by
  intro hz
  have hd : 0 < |eta - xi| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hLip := hg xi eta
  have heq : |eta - xi| = b * |g eta - g xi| := by
    have h : eta - xi = -(b * (g eta - g xi)) := by linarith
    rw [h, abs_neg, abs_mul, abs_of_nonneg hb]
  have hbound := mul_le_mul_of_nonneg_left hLip hb
  have hstrict := mul_lt_mul_of_pos_right hsmall hd
  nlinarith

/-- Every admissible source-mark tie fibre is finite for the actual feedback kinetic cost. -/
theorem finite_kineticCost_difference_fibre
    {g : ℝ → ℝ} {lam xi eta₁ eta₂ b₁ b₂ c : ℝ}
    (hg : RealLipschitz lam g) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hsmall : b₁ * lam < 1) (hne : eta₁ ≠ xi) (hb : b₁ ≠ b₂) :
    {a : ℝ | 0 ≤ a ∧ kineticCost g xi eta₁ a b₁ - kineticCost g xi eta₂ a b₂ = c}.Finite := by
  apply (finite_kinetic_difference_fibre (eta₁ - xi) (eta₂ - xi) (g xi)
    (g eta₁) (g eta₂) b₁ b₂ c hb (kinetic_pole_residue_ne_zero hg hb₁.le hsmall hne)).subset
  rintro a ⟨ha, h⟩
  exact ⟨by linarith, by linarith, h⟩

/-- Varying one source slope in a finite target permutation leaves only finitely many ties.
The graph and all event coordinates are fixed, as in disintegration over the unmarked path. -/
theorem finite_kinetic_alternating_tie_fibre
    {J : Type*} [Fintype J] [DecidableEq J] {g : ℝ → ℝ} {lam : ℝ}
    (hg : RealLipschitz lam g) (xi eta a b : J → ℝ) (tau : Equiv.Perm J) (i : J)
    (hb : ∀ j, 0 < b j) (hsmall : b i * lam < 1)
    (hne : eta i ≠ xi i) (hmarks : b i ≠ b (tau i)) :
    {z : ℝ | 0 ≤ z ∧
      (∑ j, kineticCost g (xi j) (eta j) (Function.update a i z j) (b j)) =
        ∑ j, kineticCost g (xi j) (eta (tau j))
          (Function.update a i z j) (b (tau j))}.Finite := by
  classical
  let C₁ := ∑ j ∈ Finset.univ.erase i, kineticCost g (xi j) (eta j) (a j) (b j)
  let C₂ := ∑ j ∈ Finset.univ.erase i,
    kineticCost g (xi j) (eta (tau j)) (a j) (b (tau j))
  apply (finite_kineticCost_difference_fibre (c := C₂ - C₁)
    hg (hb i) (hb (tau i)) hsmall hne hmarks).subset
  rintro z ⟨hz, heq⟩
  refine ⟨hz, ?_⟩
  have hsum (e d : J → ℝ) :
      (∑ j, kineticCost g (xi j) (e j) (Function.update a i z j) (d j)) =
      kineticCost g (xi i) (e i) z (d i) +
        ∑ j ∈ Finset.univ.erase i, kineticCost g (xi j) (e j) (a j) (d j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hsum, hsum] at heq
  change kineticCost g (xi i) (eta i) z (b i) + C₁ =
    kineticCost g (xi i) (eta (tau i)) z (b (tau i)) + C₂ at heq
  linarith

end OTSelector
