import OTSelector.Gauge.EuclideanCoercivity
import OTSelector.Feedback.Comparison
import OTSelector.Feedback.Graph

/-!
# Finite optimizer localization

This module connects the scalar Euclidean coercivity theorem to the actual finite Euclidean
assignment.  The graph-intersection equations turn the four-point quotient into the normalized
vertical displacement, and explicit row/column potentials transfer optimality to the gauged cost.
-/

open Set MeasureTheory
open scoped BigOperators Interval

namespace OTSelector

variable {n : ℕ}

/-- Euclidean residual after the permutation-invariant horizontal gap has been removed. -/
noncomputable def FiniteSample.euclideanResidualCost (sample : FiniteSample n)
    (i j : Fin n) : ℝ :=
  sample.horizontalGap i j * euclideanResidual
    (((sample.targetHeight j : ℝ) - sample.sourceHeight i) /
      sample.horizontalGap i j)

theorem FiniteSample.sourceSlope_add_targetSlope (sample : FiniteSample n) (i j : Fin n) :
    sample.sourceSlope i + sample.targetSlope j = sample.horizontalGap i j := by
  simp [FiniteSample.sourceSlope, FiniteSample.targetSlope, FiniteSample.horizontalGap]
  ring

theorem FiniteSample.horizontalGap_pos (sample : FiniteSample n) (i j : Fin n) :
    0 < sample.horizontalGap i j :=
  lt_of_lt_of_le zero_lt_one (sample.horizontalGap_mem i j).1

/-- The residual cost is exactly the Euclidean edge length minus the horizontal gap. -/
theorem FiniteSample.euclideanResidualCost_eq_sub (sample : FiniteSample n) (i j : Fin n) :
    sample.euclideanResidualCost i j =
      sample.euclideanEdgeCost i j - sample.horizontalGap i j := by
  let D := sample.horizontalGap i j
  let Δ := (sample.targetHeight j : ℝ) - sample.sourceHeight i
  have hD : 0 < D := sample.horizontalGap_pos i j
  have hbase : 0 ≤ 1 + (Δ / D) ^ 2 := by positivity
  have hraw : 0 ≤ D ^ 2 + Δ ^ 2 := by positivity
  have hscaled_nonneg : 0 ≤ D * Real.sqrt (1 + (Δ / D) ^ 2) := by positivity
  have hscaled_sq : (D * Real.sqrt (1 + (Δ / D) ^ 2)) ^ 2 = D ^ 2 + Δ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hbase]
    field_simp [hD.ne']
  have hsqrt_sq : Real.sqrt (D ^ 2 + Δ ^ 2) ^ 2 = D ^ 2 + Δ ^ 2 :=
    Real.sq_sqrt hraw
  have hscale : D * Real.sqrt (1 + (Δ / D) ^ 2) =
      Real.sqrt (D ^ 2 + Δ ^ 2) := by
    nlinarith [Real.sqrt_nonneg (D ^ 2 + Δ ^ 2)]
  unfold FiniteSample.euclideanResidualCost FiniteSample.euclideanEdgeCost
  dsimp [D, Δ] at hscale ⊢
  rw [euclideanResidual, mul_sub, mul_one, hscale]

/-- Removing the horizontal gap is a row/column gauge of the original Euclidean cost. -/
theorem FiniteSample.euclideanResidualCost_eq_rowColumnGauge
    (sample : FiniteSample n) :
    sample.euclideanResidualCost = rowColumnGauge sample.euclideanEdgeCost
      sample.sourceSlope sample.targetSlope := by
  funext i j
  rw [sample.euclideanResidualCost_eq_sub]
  simp only [rowColumnGauge]
  rw [← sample.sourceSlope_add_targetSlope i j]
  ring

theorem FiniteSample.euclideanResidualOptimizer
    (sample : FiniteSample n) {σ : Assignment n}
    (hσ : OptimalAssignment sample.euclideanEdgeCost σ) :
    OptimalAssignment sample.euclideanResidualCost σ := by
  rw [sample.euclideanResidualCost_eq_rowColumnGauge]
  exact hσ.rowColumnGauge sample.euclideanEdgeCost sample.sourceSlope sample.targetSlope

/-- Primitive of the derivative term appearing in the exact feedback gauge. -/
noncomputable def graphPotential (gamma : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in 0..x, euclideanResidualDeriv (gamma t)

theorem graphPotential_sub {gamma : ℝ → ℝ} (hgamma : Continuous gamma)
    (xi eta : ℝ) :
    graphPotential gamma eta - graphPotential gamma xi =
      ∫ t in xi..eta, euclideanResidualDeriv (gamma t) := by
  have hcont : Continuous (fun t ↦ euclideanResidualDeriv (gamma t)) :=
    euclideanResidualDeriv_continuous.comp hgamma
  have hleft : IntervalIntegrable
      (fun t : ℝ ↦ euclideanResidualDeriv (gamma t)) volume 0 xi :=
    hcont.intervalIntegrable 0 xi
  have hright : IntervalIntegrable
      (fun t : ℝ ↦ euclideanResidualDeriv (gamma t)) volume xi eta :=
    hcont.intervalIntegrable xi eta
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  unfold graphPotential
  linarith

/-- Row potential from the exact feedback gauge `(2.2)`. -/
noncomputable def feedbackGaugeRow (sample : FiniteSample n) (xi : Fin n → ℝ)
    (gamma : ℝ → ℝ) (i : Fin n) : ℝ :=
  sample.sourceSlope i * euclideanResidual (gamma (xi i)) - graphPotential gamma (xi i)

/-- Column potential from the exact feedback gauge `(2.2)`. -/
noncomputable def feedbackGaugeColumn (sample : FiniteSample n) (eta : Fin n → ℝ)
    (gamma : ℝ → ℝ) (j : Fin n) : ℝ :=
  sample.targetSlope j * euclideanResidual (gamma (eta j)) + graphPotential gamma (eta j)

/-- Four-point gauged matrix evaluated at the graph-intersection coordinates. -/
noncomputable def feedbackGaugedCost (sample : FiniteSample n)
    (xi eta : Fin n → ℝ) (gamma : ℝ → ℝ) (i j : Fin n) : ℝ :=
  euclideanGaugedCost gamma (xi i) (eta j)
    (sample.sourceSlope i) (sample.targetSlope j)

/-- Source graph-intersection equation from `(2.1)`. -/
def SourceIntersectionEquation (sample : FiniteSample n) (xi : Fin n → ℝ)
    (gamma : ℝ → ℝ) : Prop :=
  ∀ i, (sample.sourceHeight i : ℝ) + sample.sourceSlope i * gamma (xi i) = xi i

/-- Target graph-intersection equation from `(2.1)`. -/
def TargetIntersectionEquation (sample : FiniteSample n) (eta : Fin n → ℝ)
    (gamma : ℝ → ℝ) : Prop :=
  ∀ j, (sample.targetHeight j : ℝ) - sample.targetSlope j * gamma (eta j) = eta j

theorem fourPointQuotient_eq_sample_displacement
    (sample : FiniteSample n) (xi eta : Fin n → ℝ) (gamma : ℝ → ℝ)
    (hxi : SourceIntersectionEquation sample xi gamma)
    (heta : TargetIntersectionEquation sample eta gamma) (i j : Fin n) :
    fourPointQuotient gamma (xi i) (eta j) (sample.sourceSlope i)
        (sample.targetSlope j) =
      ((sample.targetHeight j : ℝ) - sample.sourceHeight i) /
        sample.horizontalGap i j := by
  have hD := sample.sourceSlope_add_targetSlope i j
  have hs := hxi i
  have ht := heta j
  unfold fourPointQuotient fourPointGap fourPointSourceValue fourPointTargetValue
    fourPointDenominator
  rw [hD]
  congr 1
  linarith

theorem fourPointQuotient_sample_mem
    (sample : FiniteSample n) (xi eta : Fin n → ℝ) (gamma : ℝ → ℝ)
    (hxi : SourceIntersectionEquation sample xi gamma)
    (heta : TargetIntersectionEquation sample eta gamma) (i j : Fin n) :
    fourPointQuotient gamma (xi i) (eta j) (sample.sourceSlope i)
        (sample.targetSlope j) ∈ Icc (-1 : ℝ) 1 := by
  rw [fourPointQuotient_eq_sample_displacement sample xi eta gamma hxi heta]
  let D := sample.horizontalGap i j
  let Δ := (sample.targetHeight j : ℝ) - sample.sourceHeight i
  have hD : 1 ≤ D := (sample.horizontalGap_mem i j).1
  have hΔ : |Δ| ≤ 1 := by
    rw [abs_le]
    constructor <;>
      linarith [(sample.sourceHeight i).property.1, (sample.sourceHeight i).property.2,
        (sample.targetHeight j).property.1, (sample.targetHeight j).property.2]
  have habs : |Δ / D| ≤ 1 := by
    rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ D)]
    exact (div_le_one (by linarith : (0 : ℝ) < D)).2 (hΔ.trans hD)
  exact abs_le.mp habs

/-! ## Finite pointwise coercivity -/

theorem euclideanGaugedCost_eq_zero_of_eq
    {gamma : ℝ → ℝ} {xi a b : ℝ} (hab : a + b ≠ 0) :
    euclideanGaugedCost gamma xi xi a b = 0 := by
  unfold euclideanGaugedCost gaugedFourPointCost
  dsimp [fourPointQuotient, fourPointGap, fourPointSourceValue, fourPointTargetValue,
    fourPointDenominator]
  simp only [sub_self, zero_add]
  have hq : (a * gamma xi + b * gamma xi) / (a + b) = gamma xi := by
    field_simp [hab]
  rw [hq]
  simp
  ring

theorem feedbackGaugedCost_lower_bound_pointwise
    (sample : FiniteSample n) (xi eta : Fin n → ℝ) (gamma : ℝ → ℝ)
    {lam : ℝ} (hgamma : Continuous gamma)
    (hgammaLip : ScalarLipschitz lam gamma) (hlam0 : 0 ≤ lam)
    (hlam : lam < 1 / 8) (hrange : ∀ x, gamma x ∈ Icc (-1 : ℝ) 1)
    (hxi : SourceIntersectionEquation sample xi gamma)
    (heta : TargetIntersectionEquation sample eta gamma) :
    ∀ i j, euclideanCurvatureLower * quadraticLowerConstant' lam *
        (eta j - xi i) ^ 2 ≤ feedbackGaugedCost sample xi eta gamma i j := by
  intro i j
  have ha : sample.sourceSlope i ∈ Icc (0 : ℝ) 1 := sample.sourceSlope_mem i
  have hb : sample.targetSlope j ∈ Icc (1 : ℝ) 2 := sample.targetSlope_mem j
  have hbpos : 0 < sample.targetSlope j := lt_of_lt_of_le zero_lt_one hb.1
  have hq := fourPointQuotient_sample_mem sample xi eta gamma hxi heta i j
  by_cases hforward : xi i < eta j
  · exact euclideanGauge_lower_bound_forward hforward hgamma hgammaLip hlam0 hlam
      (fun x _ ↦ hrange x) hq ha hb
  · by_cases hreverse : eta j < xi i
    · exact euclideanGauge_lower_bound_reverse hreverse hgamma hgammaLip hlam0 hlam
        (fun x _ ↦ hrange x) hq ha hb
    · have heq : eta j = xi i := by linarith
      have hz0 : euclideanGaugedCost gamma (xi i) (xi i)
          (sample.sourceSlope i) (sample.targetSlope j) = 0 :=
        euclideanGaugedCost_eq_zero_of_eq
          (ne_of_gt (add_pos_of_nonneg_of_pos ha.1 hbpos))
      change euclideanCurvatureLower * quadraticLowerConstant' lam *
          (eta j - xi i) ^ 2 ≤ euclideanGaugedCost gamma (xi i) (eta j)
            (sample.sourceSlope i) (sample.targetSlope j)
      rw [heq, hz0]
      simp

theorem feedbackGaugedCost_upper_bound_pointwise
    (sample : FiniteSample n) (xi eta : Fin n → ℝ) (gamma : ℝ → ℝ)
    {lam : ℝ} (hgamma : Continuous gamma)
    (hgammaLip : ScalarLipschitz lam gamma) (hlam0 : 0 ≤ lam)
    (hlam : lam < 1 / 8) (hrange : ∀ x, gamma x ∈ Icc (-1 : ℝ) 1)
    (hxi : SourceIntersectionEquation sample xi gamma)
    (heta : TargetIntersectionEquation sample eta gamma) :
    ∀ i j, feedbackGaugedCost sample xi eta gamma i j ≤
      quadraticUpperConstant lam * (eta j - xi i) ^ 2 := by
  intro i j
  have ha : sample.sourceSlope i ∈ Icc (0 : ℝ) 1 := sample.sourceSlope_mem i
  have hb : sample.targetSlope j ∈ Icc (1 : ℝ) 2 := sample.targetSlope_mem j
  have hbpos : 0 < sample.targetSlope j := lt_of_lt_of_le zero_lt_one hb.1
  have hq := fourPointQuotient_sample_mem sample xi eta gamma hxi heta i j
  by_cases hforward : xi i < eta j
  · exact euclideanGauge_upper_bound_forward hforward hgamma hgammaLip hlam0 hlam
      (fun x _ ↦ hrange x) hq ha hb
  · by_cases hreverse : eta j < xi i
    · exact euclideanGauge_upper_bound_reverse hreverse hgamma hgammaLip hlam0 hlam
        (fun x _ ↦ hrange x) hq ha hb
    · have heq : eta j = xi i := by linarith
      have hz0 : euclideanGaugedCost gamma (xi i) (xi i)
          (sample.sourceSlope i) (sample.targetSlope j) = 0 :=
        euclideanGaugedCost_eq_zero_of_eq
          (ne_of_gt (add_pos_of_nonneg_of_pos ha.1 hbpos))
      change euclideanGaugedCost gamma (xi i) (eta j)
          (sample.sourceSlope i) (sample.targetSlope j) ≤
        quadraticUpperConstant lam * (eta j - xi i) ^ 2
      rw [heq, hz0]
      simp

/-- The scalar four-point matrix is the explicit row/column gauge of the finite residual cost. -/
theorem feedbackGaugedCost_eq_rowColumnGauge
    (sample : FiniteSample n) (xi eta : Fin n → ℝ) (gamma : ℝ → ℝ)
    (hgamma : Continuous gamma)
    (hxi : SourceIntersectionEquation sample xi gamma)
    (heta : TargetIntersectionEquation sample eta gamma) :
    feedbackGaugedCost sample xi eta gamma =
      rowColumnGauge sample.euclideanResidualCost
        (feedbackGaugeRow sample xi gamma) (feedbackGaugeColumn sample eta gamma) := by
  funext i j
  rw [rowColumnGauge]
  unfold feedbackGaugedCost FiniteSample.euclideanResidualCost feedbackGaugeRow
    feedbackGaugeColumn euclideanGaugedCost gaugedFourPointCost
    fourPointSourceValue fourPointTargetValue
  dsimp only
  rw [fourPointQuotient_eq_sample_displacement sample xi eta gamma hxi heta]
  rw [← sample.sourceSlope_add_targetSlope i j]
  rw [← graphPotential_sub hgamma]
  simp only [fourPointDenominator]
  ring

theorem feedbackGaugedOptimizer
    (sample : FiniteSample n) (xi eta : Fin n → ℝ) (gamma : ℝ → ℝ)
    (hgamma : Continuous gamma)
    (hxi : SourceIntersectionEquation sample xi gamma)
    (heta : TargetIntersectionEquation sample eta gamma)
    {σ : Assignment n} (hσ : OptimalAssignment sample.euclideanEdgeCost σ) :
    OptimalAssignment (feedbackGaugedCost sample xi eta gamma) σ := by
  rw [feedbackGaugedCost_eq_rowColumnGauge sample xi eta gamma hgamma hxi heta]
  exact (sample.euclideanResidualOptimizer hσ).rowColumnGauge sample.euclideanResidualCost
    (feedbackGaugeRow sample xi gamma) (feedbackGaugeColumn sample eta gamma)

/-! ## Direct finite FGL2 transfer -/

theorem feedback_finite_energy_transfer
    (sample : FiniteSample n) (xi eta : Fin n → ℝ) (gamma : ℝ → ℝ)
    {lam : ℝ} (hgamma : Continuous gamma)
    (hgammaLip : ScalarLipschitz lam gamma) (hlam0 : 0 ≤ lam)
    (hlam : lam < 1 / 8) (hrange : ∀ x, gamma x ∈ Icc (-1 : ℝ) 1)
    (hxi : SourceIntersectionEquation sample xi gamma)
    (heta : TargetIntersectionEquation sample eta gamma)
    {σ τ : Assignment n} (hσ : OptimalAssignment sample.euclideanEdgeCost σ) :
    ∑ i, (eta (σ i) - xi i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
        ∑ i, (eta (τ i) - xi i) ^ 2 := by
  have hopt : OptimalAssignment (feedbackGaugedCost sample xi eta gamma) σ :=
    feedbackGaugedOptimizer sample xi eta gamma hgamma hxi heta hσ
  have hlowerpos : 0 < euclideanCurvatureLower * quadraticLowerConstant' lam :=
    mul_pos euclideanCurvatureLower_pos (quadraticLowerConstant'_pos hlam0 hlam)
  have hcost :
      (euclideanCurvatureLower * quadraticLowerConstant' lam) *
          ∑ i, (eta (σ i) - xi i) ^ 2 ≤
        quadraticUpperConstant lam * ∑ i, (eta (τ i) - xi i) ^ 2 := by
    calc
      (euclideanCurvatureLower * quadraticLowerConstant' lam) *
          ∑ i, (eta (σ i) - xi i) ^ 2 =
          ∑ i, (euclideanCurvatureLower * quadraticLowerConstant' lam) *
            (eta (σ i) - xi i) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i, feedbackGaugedCost sample xi eta gamma i (σ i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact feedbackGaugedCost_lower_bound_pointwise sample xi eta gamma hgamma
          hgammaLip hlam0 hlam hrange hxi heta i (σ i)
      _ = assignmentCost (feedbackGaugedCost sample xi eta gamma) σ := rfl
      _ ≤ assignmentCost (feedbackGaugedCost sample xi eta gamma) τ := hopt τ
      _ = ∑ i, feedbackGaugedCost sample xi eta gamma i (τ i) := rfl
      _ ≤ ∑ i, (quadraticUpperConstant lam) * (eta (τ i) - xi i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact feedbackGaugedCost_upper_bound_pointwise sample xi eta gamma hgamma
          hgammaLip hlam0 hlam hrange hxi heta i (τ i)
      _ = quadraticUpperConstant lam * ∑ i, (eta (τ i) - xi i) ^ 2 := by
        rw [Finset.mul_sum]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hlowerpos).2 (by simpa [mul_comm] using hcost)

/-! ## Random-offset algebra -/

theorem randomOffset_mean_abs_le
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (d : Fin n → ℝ) :
    (1 / ((n : ℝ) * R)) * ∑ i, |d i| ≤
      (1 / R) * Real.sqrt ((1 / (n : ℝ)) * ∑ i, d i ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum := sum_abs_le_sqrt_card_mul_energy d
  have hsq : 0 ≤ ∑ i, d i ^ 2 := by
    exact Finset.sum_nonneg fun i hi ↦ sq_nonneg (d i)
  have hsqrt_n : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsqrt_norm :
      Real.sqrt ((1 / (n : ℝ)) * ∑ i, d i ^ 2) =
        Real.sqrt (∑ i, d i ^ 2) / Real.sqrt (n : ℝ) := by
    have hform : (1 / (n : ℝ)) * ∑ i, d i ^ 2 =
        (∑ i, d i ^ 2) / (n : ℝ) := by
      field_simp [ne_of_gt hn0]
    rw [hform, Real.sqrt_div hsq]
  rw [hsqrt_norm]
  have hmain :
      (∑ i, |d i|) / (n : ℝ) ≤
        Real.sqrt (∑ i, d i ^ 2) / Real.sqrt (n : ℝ) := by
    apply (div_le_div_iff₀ hn0 hsqrt_n).2
    calc
      (∑ i, |d i|) * Real.sqrt (n : ℝ) ≤
          (Real.sqrt (∑ i, d i ^ 2) * Real.sqrt (n : ℝ)) *
            Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg _)
      _ = Real.sqrt (∑ i, d i ^ 2) * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = Real.sqrt (∑ i, d i ^ 2) * (n : ℝ) := by
        rw [Real.sq_sqrt hn0.le]
  calc
    (1 / ((n : ℝ) * R)) * ∑ i, |d i| =
        (1 / R) * ((∑ i, |d i|) / (n : ℝ)) := by
          field_simp [ne_of_gt hn0, ne_of_gt hR]
    _ ≤ (1 / R) *
        (Real.sqrt (∑ i, d i ^ 2) / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)

end OTSelector
