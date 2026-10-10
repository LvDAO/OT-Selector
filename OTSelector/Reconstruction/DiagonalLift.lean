import Mathlib.MeasureTheory.Measure.Portmanteau
import OTSelector.Finite.EmpiricalPlan
import OTSelector.VD.VerticalDiagonal

/-!
# Lifting a diagonal-plan limit to the full empirical plan

The reduced plan replaces the target height by the matched source height.  Its pointwise distance
from the original plan is exactly the vertical displacement.  Consequently, Lipschitz test
integrals differ by at most the Lipschitz constant times the mean vertical displacement.  The
uniform continuity of bounded continuous tests on the compact plan space then lifts any weak
limit of the reduced plans to the full plans, for arbitrary filters.
-/

open MeasureTheory
open scoped NNReal

namespace OTSelector

variable {n : ℕ}

namespace FiniteSample

/-- The reduced empirical plan supported on the vertical diagonal `S = T`. -/
noncomputable def diagonalPlan [NeZero n] (sample : FiniteSample n) (σ : Assignment n) :
    ProbabilityMeasure PlanPoint :=
  empiricalProbabilityMeasure (sample.diagonalMatchedPoint σ)

@[simp]
theorem diagonalPlan_toMeasure [NeZero n] (sample : FiniteSample n) (σ : Assignment n) :
    (sample.diagonalPlan σ : Measure PlanPoint) =
      empiricalMeasure (sample.diagonalMatchedPoint σ) :=
  rfl

/-- Quantitative reconstruction bound for a Lipschitz test function. -/
theorem abs_integral_empiricalPlan_sub_diagonalPlan_le [NeZero n]
    (sample : FiniteSample n) (σ : Assignment n) {K : ℝ≥0} {f : PlanPoint → ℝ}
    (hf : LipschitzWith K f) :
    |∫ z, f z ∂(sample.empiricalPlan σ : Measure PlanPoint) -
        ∫ z, f z ∂(sample.diagonalPlan σ : Measure PlanPoint)| ≤
      (K : ℝ) * sample.meanVerticalDisplacement σ := by
  have hfmeas : StronglyMeasurable f := hf.continuous.stronglyMeasurable
  rw [empiricalPlan_toMeasure, diagonalPlan_toMeasure,
    integral_empiricalMeasure _ hfmeas, integral_empiricalMeasure _ hfmeas]
  have hnInv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  calc
    |(n : ℝ)⁻¹ * ∑ i, f (sample.matchedPoint σ i) -
        (n : ℝ)⁻¹ * ∑ i, f (sample.diagonalMatchedPoint σ i)| =
        (n : ℝ)⁻¹ *
          |∑ i, (f (sample.matchedPoint σ i) - f (sample.diagonalMatchedPoint σ i))| := by
      rw [← mul_sub, Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hnInv]
    _ ≤ (n : ℝ)⁻¹ *
        ∑ i, |f (sample.matchedPoint σ i) - f (sample.diagonalMatchedPoint σ i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hnInv
    _ ≤ (n : ℝ)⁻¹ *
        ∑ i, (K : ℝ) * sample.verticalDisplacement σ i := by
      apply mul_le_mul_of_nonneg_left _ hnInv
      exact Finset.sum_le_sum fun i _ ↦ by
        simpa [Real.dist_eq, sample.planPoint_dist_diagonalMatchedPoint σ i] using
          hf.dist_le_mul (sample.matchedPoint σ i) (sample.diagonalMatchedPoint σ i)
    _ = (K : ℝ) * sample.meanVerticalDisplacement σ := by
      simp [meanVerticalDisplacement, Finset.mul_sum]
      ring_nf

/-- Abstract macroscopic reconstruction: weak convergence of reduced plans plus VD implies weak
convergence of the original empirical plans. -/
theorem tendsto_empiricalPlan_of_diagonalPlan {ι : Type*} {l : Filter ι}
    {m : ι → ℕ} [∀ k, NeZero (m k)]
    (sample : ∀ k, FiniteSample (m k)) (σ : ∀ k, Assignment (m k))
    (limitPlan : ProbabilityMeasure PlanPoint)
    (hdiag : Filter.Tendsto (fun k ↦ (sample k).diagonalPlan (σ k)) l (nhds limitPlan))
    (hvd : Filter.Tendsto (fun k ↦ (sample k).meanVerticalDisplacement (σ k)) l (nhds 0)) :
    Filter.Tendsto (fun k ↦ (sample k).empiricalPlan (σ k)) l (nhds limitPlan) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hdiagTest := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hdiag) f
  have hdiff : Filter.Tendsto
      (fun k ↦
        (∫ z, f z ∂((sample k).empiricalPlan (σ k) : Measure PlanPoint)) -
        (∫ z, f z ∂((sample k).diagonalPlan (σ k) : Measure PlanPoint))) l (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 2) (by positivity)
    let K := 2 * ‖f‖ / δ
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hpoint (x y : PlanPoint) : |f x - f y| ≤ ε / 2 + K * dist x y := by
      rw [← Real.dist_eq]
      by_cases hxy : dist x y < δ
      · exact (hclose hxy).le.trans (le_add_of_nonneg_right (mul_nonneg hK dist_nonneg))
      · have hlarge : 2 * ‖f‖ ≤ K * dist x y := by
          calc
            _ = K * δ := (div_mul_cancel₀ _ hδ.ne').symm
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_not_gt hxy) hK
        exact (f.dist_le_two_norm x y).trans (hlarge.trans (by linarith))
    have hscale : Filter.Tendsto
        (fun k ↦ K * (sample k).meanVerticalDisplacement (σ k)) l (nhds 0) := by
      simpa using hvd.const_mul K
    filter_upwards [hscale.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))]
      with k hk
    rw [Real.dist_eq, sub_zero]
    have hnInv : 0 ≤ ((m k : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hn : ((m k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
    have hfmeas : StronglyMeasurable f := f.continuous.stronglyMeasurable
    rw [empiricalPlan_toMeasure, diagonalPlan_toMeasure,
      integral_empiricalMeasure _ hfmeas, integral_empiricalMeasure _ hfmeas]
    calc
      |((m k : ℕ) : ℝ)⁻¹ * ∑ i, f ((sample k).matchedPoint (σ k) i) -
          ((m k : ℕ) : ℝ)⁻¹ * ∑ i, f ((sample k).diagonalMatchedPoint (σ k) i)| =
          ((m k : ℕ) : ℝ)⁻¹ * |∑ i, (f ((sample k).matchedPoint (σ k) i) -
            f ((sample k).diagonalMatchedPoint (σ k) i))| := by
        rw [← mul_sub, Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hnInv]
      _ ≤ ((m k : ℕ) : ℝ)⁻¹ * ∑ i, |f ((sample k).matchedPoint (σ k) i) -
          f ((sample k).diagonalMatchedPoint (σ k) i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hnInv
      _ ≤ ((m k : ℕ) : ℝ)⁻¹ * ∑ i, (ε / 2 + K * (sample k).verticalDisplacement (σ k) i) := by
        apply mul_le_mul_of_nonneg_left _ hnInv
        apply Finset.sum_le_sum
        intro i _
        simpa only [(sample k).planPoint_dist_diagonalMatchedPoint (σ k) i] using
          hpoint ((sample k).matchedPoint (σ k) i) ((sample k).diagonalMatchedPoint (σ k) i)
      _ = ε / 2 + K * (sample k).meanVerticalDisplacement (σ k) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, meanVerticalDisplacement]
        field_simp
      _ < ε := by linarith
  simpa only [sub_add_cancel, zero_add] using hdiff.add hdiagTest

end FiniteSample

end OTSelector
