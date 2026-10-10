import OTSelector.Finite.Assignment

/-!
# Row-column gauges for finite assignments

Subtracting one potential from each row and one from each column changes every permutation cost by
the same constant.  This is the exact deterministic gauge argument in `main.tex`.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- Subtract row and column potentials from an edge cost. -/
def rowColumnGauge (cost : Fin n → Fin n → ℝ) (row column : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j ↦ cost i j - row i - column j

theorem assignmentCost_rowColumnGauge (cost : Fin n → Fin n → ℝ)
    (row column : Fin n → ℝ) (σ : Assignment n) :
    assignmentCost (rowColumnGauge cost row column) σ =
      assignmentCost cost σ - ∑ i, row i - ∑ j, column j := by
  simp only [assignmentCost, rowColumnGauge, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp σ column]

theorem optimalAssignment_rowColumnGauge_iff (cost : Fin n → Fin n → ℝ)
    (row column : Fin n → ℝ) (σ : Assignment n) :
    OptimalAssignment (rowColumnGauge cost row column) σ ↔ OptimalAssignment cost σ := by
  simp only [OptimalAssignment]
  constructor <;> intro h τ
  · specialize h τ
    rw [assignmentCost_rowColumnGauge, assignmentCost_rowColumnGauge] at h
    linarith
  · rw [assignmentCost_rowColumnGauge, assignmentCost_rowColumnGauge]
    exact sub_le_sub_right (sub_le_sub_right (h τ) _) _

theorem OptimalAssignment.rowColumnGauge (cost : Fin n → Fin n → ℝ)
    (row column : Fin n → ℝ) {σ : Assignment n} (hσ : OptimalAssignment cost σ) :
    OptimalAssignment (rowColumnGauge cost row column) σ :=
  (optimalAssignment_rowColumnGauge_iff cost row column σ).2 hσ

end OTSelector
