import OTSelector.Gauge.RowColumn

/-!
# Deterministic coercivity engine

Pointwise quadratic coercive bounds transfer energy estimates from a comparison assignment
to the exact cost-minimizing assignment.
In particular, the Euclidean bounds follow from the quadratic bounds by comparing the hinge
weights, matching the Peano-hinge and coercivity bounds in `main.tex`.
-/

open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- Two-sided quadratic control of a nonnegative displacement by a gauged edge cost. -/
structure EdgeCoercivity (gauge displacement : Fin n → Fin n → ℝ)
    (lower upper : ℝ) : Prop where
  lower_nonneg : 0 ≤ lower
  lower_bound : ∀ i j, lower * displacement i j ^ 2 ≤ gauge i j
  upper_bound : ∀ i j, gauge i j ≤ upper * displacement i j ^ 2

/-- Transfer quadratic coercive bounds through pointwise comparison of two gauged costs. -/
theorem EdgeCoercivity.of_comparison {quadratic euclidean displacement : Fin n → Fin n → ℝ}
    {quadLower quadUpper weightLower weightUpper : ℝ}
    (hquad : EdgeCoercivity quadratic displacement quadLower quadUpper)
    (hweightLower : 0 ≤ weightLower)
    (hweightUpper : 0 ≤ weightUpper)
    (hlower : ∀ i j, weightLower * quadratic i j ≤ euclidean i j)
    (hupper : ∀ i j, euclidean i j ≤ weightUpper * quadratic i j) :
    EdgeCoercivity euclidean displacement (weightLower * quadLower)
      (weightUpper * quadUpper) := by
  refine ⟨mul_nonneg hweightLower hquad.lower_nonneg, ?_, ?_⟩
  · intro i j
    calc
      (weightLower * quadLower) * displacement i j ^ 2 =
          weightLower * (quadLower * displacement i j ^ 2) := by ring
      _ ≤ weightLower * quadratic i j :=
        mul_le_mul_of_nonneg_left (hquad.lower_bound i j) hweightLower
      _ ≤ euclidean i j := hlower i j
  · intro i j
    calc
      euclidean i j ≤ weightUpper * quadratic i j := hupper i j
      _ ≤ weightUpper * (quadUpper * displacement i j ^ 2) := by
        exact mul_le_mul_of_nonneg_left (hquad.upper_bound i j) hweightUpper
      _ = (weightUpper * quadUpper) * displacement i j ^ 2 := by ring

/-- Sum the lower coercive bound over the edges of an assignment. -/
theorem EdgeCoercivity.sum_lower {gauge displacement : Fin n → Fin n → ℝ}
    {lower upper : ℝ} (h : EdgeCoercivity gauge displacement lower upper)
    (σ : Assignment n) :
    lower * ∑ i, displacement i (σ i) ^ 2 ≤ assignmentCost gauge σ := by
  rw [assignmentCost, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ h.lower_bound i (σ i)

/-- Sum the upper coercive bound over the edges of an assignment. -/
theorem EdgeCoercivity.sum_upper {gauge displacement : Fin n → Fin n → ℝ}
    {lower upper : ℝ} (h : EdgeCoercivity gauge displacement lower upper)
    (σ : Assignment n) :
    assignmentCost gauge σ ≤ upper * ∑ i, displacement i (σ i) ^ 2 := by
  rw [assignmentCost, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ h.upper_bound i (σ i)

/-- The deterministic FGL2 energy transfer: optimality plus coercivity controls the optimizer by
any comparison assignment. -/
theorem optimal_displacement_energy_le {gauge displacement : Fin n → Fin n → ℝ}
    {lower upper : ℝ} (hcoercive : EdgeCoercivity gauge displacement lower upper)
    (hlower : 0 < lower) {σ τ : Assignment n} (hσ : OptimalAssignment gauge σ) :
    ∑ i, displacement i (σ i) ^ 2 ≤
      (upper / lower) * ∑ i, displacement i (τ i) ^ 2 := by
  have hcost := (hcoercive.sum_lower σ).trans (hσ τ) |>.trans (hcoercive.sum_upper τ)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hlower).2 (by simpa [mul_comm] using hcost)

/-- A deliberately simple positive lower constant valid in the paper's range `λ < 1/8`. -/
noncomputable def quadraticLowerConstant (lam : ℝ) : ℝ :=
  (1 - lam) * (1 - 2 * lam) / 6 - lam / 2

theorem quadraticLowerConstant_pos {lam : ℝ} (_hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8) :
    0 < quadraticLowerConstant lam := by
  dsimp [quadraticLowerConstant]
  nlinarith [sq_nonneg (lam - 1 / 8)]

end OTSelector
