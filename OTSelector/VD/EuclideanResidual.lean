import OTSelector.Gauge.Coercivity
import OTSelector.Basic.Model

/-!
# Euclidean residual coercivity

The Euclidean edge cost is the horizontal gap plus a nonnegative residual.  The horizontal part is
a row-column gauge, so it does not alter the optimal assignment.  On the model range
`1 ≤ D ≤ 3` and `|S-T| ≤ 1`, rationalizing the square root gives uniform quadratic bounds for the
residual.  These are the deterministic estimates used by vertical diagonal concentration.
-/

namespace OTSelector

variable {n : ℕ}

namespace FiniteSample

/-- Row potential whose sum with `horizontalColumn` is the horizontal gap. -/
def horizontalRow (sample : FiniteSample n) (i : Fin n) : ℝ :=
  -(sample.sourceMark i : ℝ)

/-- Column potential whose sum with `horizontalRow` is the horizontal gap. -/
def horizontalColumn (sample : FiniteSample n) (j : Fin n) : ℝ :=
  2 + sample.targetMark j

/-- Euclidean cost after subtracting the permutation-invariant horizontal gap. -/
noncomputable def euclideanExcess (sample : FiniteSample n) (i j : Fin n) : ℝ :=
  sample.euclideanEdgeCost i j - sample.horizontalGap i j

theorem rowColumnGauge_euclideanEdgeCost (sample : FiniteSample n) :
    rowColumnGauge sample.euclideanEdgeCost sample.horizontalRow sample.horizontalColumn =
      sample.euclideanExcess := by
  funext i j
  simp [rowColumnGauge, horizontalRow, horizontalColumn, euclideanExcess, horizontalGap]
  ring

/-- The exact Euclidean optimizer also minimizes the horizontal-gauged residual. -/
theorem euclideanOptimizer_isOptimal_excess (sample : FiniteSample n) :
    OptimalAssignment sample.euclideanExcess sample.euclideanOptimizer := by
  have h := sample.euclideanOptimizer_isOptimal.rowColumnGauge sample.euclideanEdgeCost
    sample.horizontalRow sample.horizontalColumn
  rwa [rowColumnGauge_euclideanEdgeCost] at h

private theorem sqrt_residual_bounds {D y : ℝ} (hD1 : 1 ≤ D) (hD3 : D ≤ 3)
    (hyLower : -1 ≤ y) (hyUpper : y ≤ 1) :
    (1 / 7 : ℝ) * y ^ 2 ≤ Real.sqrt (D ^ 2 + y ^ 2) - D ∧
      Real.sqrt (D ^ 2 + y ^ 2) - D ≤ (1 / 2 : ℝ) * y ^ 2 := by
  let r := Real.sqrt (D ^ 2 + y ^ 2)
  have hD0 : 0 ≤ D := by linarith
  have hySq0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hrad : 0 ≤ D ^ 2 + y ^ 2 := by positivity
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = D ^ 2 + y ^ 2 := by
    simpa [r] using Real.sq_sqrt hrad
  have hDSq : D ^ 2 ≤ 9 := by nlinarith
  have hySq : y ^ 2 ≤ 1 := by nlinarith
  have hDr : D ≤ r := by nlinarith
  have hr4 : r ≤ 4 := by nlinarith
  have he0 : 0 ≤ r - D := sub_nonneg.mpr hDr
  have hdenUpper : r + D ≤ 7 := by linarith
  have hdenLower : 2 ≤ r + D := by linarith
  have hid : (r - D) * (r + D) = y ^ 2 := by nlinarith
  have hmulUpper : 0 ≤ (r - D) * (7 - (r + D)) :=
    mul_nonneg he0 (sub_nonneg.mpr hdenUpper)
  have hmulLower : 0 ≤ (r - D) * ((r + D) - 2) :=
    mul_nonneg he0 (sub_nonneg.mpr hdenLower)
  constructor <;> dsimp [r] at * <;> nlinarith

/-- Uniform quadratic coercivity of the exact Euclidean residual on `[0,1]^4`. -/
theorem euclideanExcess_coercivity (sample : FiniteSample n) :
    EdgeCoercivity sample.euclideanExcess sample.verticalEdgeDisplacement
      (1 / 7 : ℝ) (1 / 2 : ℝ) := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> intro i j
  · have hD := sample.horizontalGap_mem i j
    have hS0 := (sample.targetHeight j).property.1
    have hS1 := (sample.targetHeight j).property.2
    have hT0 := (sample.sourceHeight i).property.1
    have hT1 := (sample.sourceHeight i).property.2
    have h := sqrt_residual_bounds (D := sample.horizontalGap i j)
      (y := (sample.targetHeight j : ℝ) - sample.sourceHeight i)
      hD.1 hD.2 (by linarith) (by linarith)
    simpa [euclideanExcess, euclideanEdgeCost, verticalEdgeDisplacement, sq_abs] using h.1
  · have hD := sample.horizontalGap_mem i j
    have hS0 := (sample.targetHeight j).property.1
    have hS1 := (sample.targetHeight j).property.2
    have hT0 := (sample.sourceHeight i).property.1
    have hT1 := (sample.sourceHeight i).property.2
    have h := sqrt_residual_bounds (D := sample.horizontalGap i j)
      (y := (sample.targetHeight j : ℝ) - sample.sourceHeight i)
      hD.1 hD.2 (by linarith) (by linarith)
    simpa [euclideanExcess, euclideanEdgeCost, verticalEdgeDisplacement, sq_abs] using h.2

end FiniteSample

end OTSelector
