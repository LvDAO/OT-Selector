import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import OTSelector.VD.EuclideanResidual

/-!
# Deterministic vertical diagonal reduction

The probabilistic DKW input in `main.tex` only supplies a comparison assignment whose vertical
error tends to zero.  This file proves the deterministic part: exact Euclidean optimality transfers
that uniform reference error to the optimizer's mean vertical displacement.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

namespace FiniteSample

/-- Mean vertical displacement of an assignment. -/
noncomputable def meanVerticalDisplacement (sample : FiniteSample n) (σ : Assignment n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, sample.verticalDisplacement σ i

theorem meanVerticalDisplacement_nonneg (sample : FiniteSample n) (σ : Assignment n) :
    0 ≤ sample.meanVerticalDisplacement σ := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

/-- The optimizer's squared vertical error is controlled by that of any comparison assignment. -/
theorem optimizer_vertical_sq_sum_le (sample : FiniteSample n) (ρ : Assignment n) :
    ∑ i, sample.verticalDisplacement sample.euclideanOptimizer i ^ 2 ≤
      (7 / 2 : ℝ) * ∑ i, sample.verticalEdgeDisplacement i (ρ i) ^ 2 := by
  have h := optimal_displacement_energy_le sample.euclideanExcess_coercivity (by norm_num)
    (σ := sample.euclideanOptimizer) (τ := ρ) sample.euclideanOptimizer_isOptimal_excess
  norm_num at h ⊢
  simpa only [verticalDisplacement_eq_edge] using h

private theorem vertical_sum_sq_le_card_mul (sample : FiniteSample n) (σ : Assignment n) :
    (∑ i, sample.verticalDisplacement σ i) ^ 2 ≤
      (n : ℝ) * ∑ i, sample.verticalDisplacement σ i ^ 2 := by
  simpa using
    (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i ↦ sample.verticalDisplacement σ i))

/-- Deterministic VD estimate.  If a comparison permutation has every vertical edge at most
`ε`, then the exact Euclidean optimizer has mean vertical displacement at most `2ε`.

The constant `2` is a convenient coarse bound for `sqrt (7/2)`.
-/
theorem meanVerticalDisplacement_optimizer_le {ε : ℝ} [NeZero n]
    (sample : FiniteSample n) (ρ : Assignment n) (hε : 0 ≤ ε)
    (href : ∀ i, sample.verticalEdgeDisplacement i (ρ i) ≤ ε) :
    sample.meanVerticalDisplacement sample.euclideanOptimizer ≤ 2 * ε := by
  have hnNat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hnNat
  have hrefSq : ∑ i, sample.verticalEdgeDisplacement i (ρ i) ^ 2 ≤
      (n : ℝ) * ε ^ 2 := by
    calc
      ∑ i, sample.verticalEdgeDisplacement i (ρ i) ^ 2 ≤ ∑ _i : Fin n, ε ^ 2 := by
        exact Finset.sum_le_sum fun i _ ↦ by
          have hd0 : 0 ≤ sample.verticalEdgeDisplacement i (ρ i) := abs_nonneg _
          nlinarith [href i]
      _ = (n : ℝ) * ε ^ 2 := by simp
  have hopt := sample.optimizer_vertical_sq_sum_le ρ
  have hopt' : ∑ i, sample.verticalDisplacement sample.euclideanOptimizer i ^ 2 ≤
      (7 / 2 : ℝ) * ((n : ℝ) * ε ^ 2) :=
    hopt.trans (mul_le_mul_of_nonneg_left hrefSq (by norm_num))
  have hcs := vertical_sum_sq_le_card_mul sample sample.euclideanOptimizer
  have hscaled := mul_le_mul_of_nonneg_left hopt' hn.le
  have hsum0 : 0 ≤ ∑ i, sample.verticalDisplacement sample.euclideanOptimizer i :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hrhs0 : 0 ≤ 2 * (n : ℝ) * ε := by positivity
  have hsum : ∑ i, sample.verticalDisplacement sample.euclideanOptimizer i ≤
      2 * (n : ℝ) * ε := by
    nlinarith [sq_nonneg ((n : ℝ) * ε)]
  unfold meanVerticalDisplacement
  calc
    (n : ℝ)⁻¹ * ∑ i, sample.verticalDisplacement sample.euclideanOptimizer i ≤
        (n : ℝ)⁻¹ * (2 * (n : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    _ = 2 * ε := by field_simp

/-- A comparison assignment with vanishing uniform vertical error forces the optimizer's mean
vertical displacement to vanish along the same filter. -/
theorem tendsto_meanVerticalDisplacement_optimizer_zero {ι : Type*} {l : Filter ι}
    {m : ι → ℕ} [∀ k, NeZero (m k)] (sample : ∀ k, FiniteSample (m k))
    (ρ : ∀ k, Assignment (m k)) (ε : ι → ℝ) (hε0 : ∀ k, 0 ≤ ε k)
    (href : ∀ k i, (sample k).verticalEdgeDisplacement i (ρ k i) ≤ ε k)
    (hε : Filter.Tendsto ε l (nhds 0)) :
    Filter.Tendsto
      (fun k ↦ (sample k).meanVerticalDisplacement (sample k).euclideanOptimizer) l (nhds 0) := by
  apply squeeze_zero
  · exact fun k ↦ (sample k).meanVerticalDisplacement_nonneg (sample k).euclideanOptimizer
  · exact fun k ↦ meanVerticalDisplacement_optimizer_le (sample k) (ρ k) (hε0 k) (href k)
  · simpa using hε.const_mul 2

end FiniteSample

end OTSelector
