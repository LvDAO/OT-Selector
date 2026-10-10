import Mathlib.Data.Finset.Max
import OTSelector.Basic.Model

/-!
# Finite assignments and optimal permutations
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- Total cost of a permutation for an arbitrary edge-cost matrix. -/
def assignmentCost (cost : Fin n → Fin n → ℝ) (σ : Assignment n) : ℝ :=
  ∑ i, cost i (σ i)

/-- A permutation is optimal when its total cost is no larger than every competitor's. -/
def OptimalAssignment (cost : Fin n → Fin n → ℝ) (σ : Assignment n) : Prop :=
  ∀ τ, assignmentCost cost σ ≤ assignmentCost cost τ

theorem exists_optimalAssignment (cost : Fin n → Fin n → ℝ) :
    ∃ σ, OptimalAssignment cost σ := by
  classical
  let _ : Fintype (Assignment n) := Fintype.ofFinite (Assignment n)
  obtain ⟨σ, -, hσ⟩ := Finset.univ.exists_min_image (assignmentCost cost) Finset.univ_nonempty
  exact ⟨σ, fun τ ↦ hσ τ (Finset.mem_univ τ)⟩

/-- A fixed noncomputable minimizing permutation. -/
noncomputable def optimalAssignment (cost : Fin n → Fin n → ℝ) : Assignment n :=
  Classical.choose (exists_optimalAssignment cost)

theorem optimalAssignment_isOptimal (cost : Fin n → Fin n → ℝ) :
    OptimalAssignment cost (optimalAssignment cost) :=
  Classical.choose_spec (exists_optimalAssignment cost)

/-- The exact empirical Euclidean optimizer used in `main.tex`. -/
noncomputable def FiniteSample.euclideanOptimizer (sample : FiniteSample n) : Assignment n :=
  optimalAssignment sample.euclideanEdgeCost

theorem FiniteSample.euclideanOptimizer_isOptimal (sample : FiniteSample n) :
    OptimalAssignment sample.euclideanEdgeCost sample.euclideanOptimizer :=
  optimalAssignment_isOptimal sample.euclideanEdgeCost

end OTSelector
