import OTSelector.Finite.Assignment
import Mathlib.Analysis.Real.Sqrt

/-!
# Comparison matching and current identities

This file contains only closed deterministic identities used by the I3 and zero-flux arguments.
-/

open scoped BigOperators

namespace OTSelector

/-- Signed contribution of an oriented edge `(a,b)` at a cut `x`. -/
noncomputable def crossingSign (a b x : ℝ) : ℤ :=
  (if a ≤ x then 1 else 0) - (if b ≤ x then 1 else 0)

theorem crossingSign_eq_one {a b x : ℝ} (ha : a ≤ x) (hb : x < b) :
    crossingSign a b x = 1 := by
  simp [crossingSign, ha, not_le.mpr hb]

theorem crossingSign_eq_neg_one {a b x : ℝ} (ha : b ≤ x) (hb : x < a) :
    crossingSign a b x = -1 := by
  simp [crossingSign, ha, not_le.mpr hb]

theorem crossingSign_eq_zero_of_left {a b x : ℝ} (ha : x < a) (hb : x < b) :
    crossingSign a b x = 0 := by
  simp [crossingSign, not_le.mpr ha, not_le.mpr hb]

theorem crossingSign_eq_zero_of_right {a b x : ℝ} (ha : a ≤ x) (hb : b ≤ x) :
    crossingSign a b x = 0 := by
  simp [crossingSign, ha, hb]

/-- Oriented current of a finite assignment across a cut. -/
noncomputable def assignmentCrossingCurrent {n : ℕ} (source target : Fin n → ℝ)
    (σ : Assignment n) (x : ℝ) : ℤ :=
  ∑ i, crossingSign (source i) (target (σ i)) x

/-- Rank discrepancy written in the assignment indexing. -/
noncomputable def assignmentRankDiscrepancy {n : ℕ} (source target : Fin n → ℝ)
    (σ : Assignment n) (x : ℝ) : ℤ :=
  (∑ i, if source i ≤ x then 1 else 0) -
    ∑ i, if target (σ i) ≤ x then 1 else 0

/-- Exact finite identity `Cₙ(x)=Kₙ(x)` from (4.18). -/
theorem assignmentCrossingCurrent_eq_rankDiscrepancy {n : ℕ}
    (source target : Fin n → ℝ) (σ : Assignment n) (x : ℝ) :
    assignmentCrossingCurrent source target σ x =
      assignmentRankDiscrepancy source target σ x := by
  simp only [assignmentCrossingCurrent, assignmentRankDiscrepancy, crossingSign,
    Finset.sum_sub_distrib]

/-- The target count is independent of how it is enumerated by a permutation. -/
theorem target_count_comp_perm {n : ℕ} (target : Fin n → ℝ) (σ : Assignment n) (x : ℝ) :
    (∑ i, if target (σ i) ≤ x then (1 : ℤ) else 0) =
      ∑ j, if target j ≤ x then (1 : ℤ) else 0 := by
  exact Equiv.sum_comp σ (fun j ↦ if target j ≤ x then (1 : ℤ) else 0)

/-- Cauchy--Schwarz conversion used in the random-offset block estimate (2.15). -/
theorem sum_abs_le_sqrt_card_mul_energy {n : ℕ} (d : Fin n → ℝ) :
    ∑ i, |d i| ≤ Real.sqrt (∑ i, d i ^ 2) * Real.sqrt n := by
  simpa [sq_abs] using
    (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin n ↦ |d i|) (fun _ ↦ (1 : ℝ)))

end OTSelector
