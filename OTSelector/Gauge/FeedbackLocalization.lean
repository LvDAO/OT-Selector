import OTSelector.Gauge.FGL2
import OTSelector.Feedback.FeedbackCurve
import OTSelector.Feedback.Intersections
import OTSelector.Feedback.NormalizedGraph
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Feedback localization for the finite Euclidean optimizer

This module instantiates the deterministic FGL2 transfer with the feedback curve constructed from
an actual finite sample.  The rank-scale intersections are divided by `n`, and the feedback curve
is rescaled by the same factor.  Thus the rank-scale intersection identities become exactly the
normalized source and target equations used by `feedback_finite_energy_transfer`.

The increasing comparison assignment is constructed by sorting the two intersection arrays.
Its energy bound and the normalized graph range event supply the quantitative inputs to the
optimizer energy transfer.
-/

open Set
open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

namespace FiniteSample

variable (sample : FiniteSample n)

/-! ## Actual normalized curve and intersections -/

/-- The actual normalized feedback curve `gamma(z) = g(n z) / n`. -/
noncomputable def normalizedFeedbackCurve
    {lam : ℝ} (_hlam0 : 0 ≤ lam) (_hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) : ℝ → ℝ :=
  normalizedGraph
    (fun _ : ℕ ↦ feedbackCurve sample lam x0 p0) n

/-- The source intersection in normalized coordinates. -/
noncomputable def normalizedSourceIntersection
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) : ℝ :=
  sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i / (n : ℝ)

/-- The target intersection in normalized coordinates. -/
noncomputable def normalizedTargetIntersection
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) : ℝ :=
  sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j / (n : ℝ)

theorem normalizedFeedbackCurve_lipschitz
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (x0 p0 : ℝ) :
    RealLipschitz lam (sample.normalizedFeedbackCurve hlam0 hlamHalf x0 p0) := by
  exact normalizedGraph_lipschitz hn
    (sample.feedbackCurve_realLipschitz hlam0 hlamHalf x0 p0)

theorem normalizedFeedbackCurve_continuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (x0 p0 : ℝ) :
    Continuous (sample.normalizedFeedbackCurve hlam0 hlamHalf x0 p0) := by
  have hLip : LipschitzWith (Real.toNNReal lam)
      (sample.normalizedFeedbackCurve hlam0 hlamHalf x0 p0) := by
    apply LipschitzWith.of_dist_le'
    intro x y
    simpa only [Real.dist_eq, Real.toNNReal_of_nonneg hlam0, abs_sub_comm] using
      sample.normalizedFeedbackCurve_lipschitz hlam0 hlamHalf hn x0 p0 x y
  exact hLip.continuous

/-- Dividing the rank-scale source intersection identity by `n` gives the exact FGL2 equation. -/
theorem normalizedSourceIntersection_equation
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (x0 p0 : ℝ) :
    SourceIntersectionEquation sample
      (sample.normalizedSourceIntersection hlam0 hlamHalf x0 p0)
      (sample.normalizedFeedbackCurve hlam0 hlamHalf x0 p0) := by
  intro i
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hspec := sample.sourceIntersection_spec
    (sample.feedbackGraph hlam0 hlamHalf x0 p0) i
  simp only [sourcePhase, feedbackGraph_curve] at hspec
  unfold normalizedSourceIntersection normalizedFeedbackCurve normalizedGraph rescaleGraph
  rw [show (n : ℝ) *
      (sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i / (n : ℝ)) =
        sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i by
      field_simp]
  field_simp [hnR]
  nlinarith

/-- Dividing the rank-scale target intersection identity by `n` gives the exact FGL2 equation. -/
theorem normalizedTargetIntersection_equation
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) (x0 p0 : ℝ) :
    TargetIntersectionEquation sample
      (sample.normalizedTargetIntersection hlam0 hlamHalf x0 p0)
      (sample.normalizedFeedbackCurve hlam0 hlamHalf x0 p0) := by
  intro j
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hspec := sample.targetIntersection_spec
    (sample.feedbackGraph hlam0 hlamHalf x0 p0) j
  simp only [targetPhase, feedbackGraph_curve] at hspec
  unfold normalizedTargetIntersection normalizedFeedbackCurve normalizedGraph rescaleGraph
  rw [show (n : ℝ) *
      (sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j / (n : ℝ)) =
        sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j by
      field_simp]
  field_simp [hnR]
  nlinarith

/-! ## Explicit increasing comparison assignment -/

/-- Match the `k`-th smallest source coordinate to the `k`-th smallest target coordinate. -/
noncomputable def increasingAssignment (source target : Fin n → ℝ) : Assignment n :=
  (Tuple.sort source).symm.trans (Tuple.sort target)

@[simp]
theorem increasingAssignment_apply_sourceSort
    (source target : Fin n → ℝ) (k : Fin n) :
    increasingAssignment source target (Tuple.sort source k) = Tuple.sort target k := by
  simp [increasingAssignment]

/-- The targets paired with sorted sources are themselves in increasing order. -/
theorem increasingAssignment_target_monotone (source target : Fin n → ℝ) :
    Monotone (fun k ↦ target (increasingAssignment source target (Tuple.sort source k))) := by
  intro i j hij
  change target (increasingAssignment source target (Tuple.sort source i)) ≤
    target (increasingAssignment source target (Tuple.sort source j))
  rw [increasingAssignment_apply_sourceSort, increasingAssignment_apply_sourceSort]
  exact Tuple.monotone_sort target hij

/-- The increasing assignment for the actual normalized feedback intersections. -/
noncomputable def feedbackComparisonAssignment
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) : Assignment n :=
  increasingAssignment
    (sample.normalizedSourceIntersection hlam0 hlamHalf x0 p0)
    (sample.normalizedTargetIntersection hlam0 hlamHalf x0 p0)

/-! ## Concrete finite-energy transfer -/

/-- FGL2 for the exact Euclidean optimizer and any explicit comparison assignment, in normalized
intersection coordinates.  The range premise is exactly the deterministic content of the I4 good
event; the theorem does not assume the desired optimizer-energy conclusion. -/
theorem euclideanOptimizer_normalizedFeedbackEnergy_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (x0 p0 : ℝ)
    (hrange : ∀ z, sample.normalizedFeedbackCurve hlam0
      (hlam.trans (by norm_num)) x0 p0 z ∈ Icc (-1 : ℝ) 1)
    (tau : Assignment n) :
    ∑ i, (sample.normalizedTargetIntersection hlam0
          (hlam.trans (by norm_num)) x0 p0 (sample.euclideanOptimizer i) -
        sample.normalizedSourceIntersection hlam0
          (hlam.trans (by norm_num)) x0 p0 i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
        ∑ i, (sample.normalizedTargetIntersection hlam0
              (hlam.trans (by norm_num)) x0 p0 (tau i) -
            sample.normalizedSourceIntersection hlam0
              (hlam.trans (by norm_num)) x0 p0 i) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := hlam.trans (by norm_num)
  exact feedback_finite_energy_transfer sample
    (sample.normalizedSourceIntersection hlam0 hlamHalf x0 p0)
    (sample.normalizedTargetIntersection hlam0 hlamHalf x0 p0)
    (sample.normalizedFeedbackCurve hlam0 hlamHalf x0 p0)
    (sample.normalizedFeedbackCurve_continuous hlam0 hlamHalf hn x0 p0)
    (sample.normalizedFeedbackCurve_lipschitz hlam0 hlamHalf hn x0 p0)
    hlam0 hlam hrange
    (sample.normalizedSourceIntersection_equation hlam0 hlamHalf hn x0 p0)
    (sample.normalizedTargetIntersection_equation hlam0 hlamHalf hn x0 p0)
    sample.euclideanOptimizer_isOptimal

/-- The concrete FGL2 bound with the increasing graph matching as comparison. -/
theorem euclideanOptimizer_normalizedFeedbackEnergy_le_increasing
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (x0 p0 : ℝ)
    (hrange : ∀ z, sample.normalizedFeedbackCurve hlam0
      (hlam.trans (by norm_num)) x0 p0 z ∈ Icc (-1 : ℝ) 1) :
    ∑ i, (sample.normalizedTargetIntersection hlam0
          (hlam.trans (by norm_num)) x0 p0 (sample.euclideanOptimizer i) -
        sample.normalizedSourceIntersection hlam0
          (hlam.trans (by norm_num)) x0 p0 i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
        ∑ i, (sample.normalizedTargetIntersection hlam0
              (hlam.trans (by norm_num)) x0 p0
                (sample.feedbackComparisonAssignment hlam0
                  (hlam.trans (by norm_num)) x0 p0 i) -
            sample.normalizedSourceIntersection hlam0
              (hlam.trans (by norm_num)) x0 p0 i) ^ 2 := by
  exact sample.euclideanOptimizer_normalizedFeedbackEnergy_le
    hlam0 hlam hn x0 p0 hrange
    (sample.feedbackComparisonAssignment hlam0 (hlam.trans (by norm_num)) x0 p0)

/-- Rank-scale form of the concrete transfer.  This is `(2.14)` before the probabilistic I3 bound
on the right-hand side is inserted. -/
theorem euclideanOptimizer_feedbackEnergy_le_increasing
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (x0 p0 : ℝ)
    (hrange : ∀ z, sample.normalizedFeedbackCurve hlam0
      (hlam.trans (by norm_num)) x0 p0 z ∈ Icc (-1 : ℝ) 1) :
    ∑ i, (sample.targetIntersection
          (sample.feedbackGraph hlam0 (hlam.trans (by norm_num)) x0 p0)
            (sample.euclideanOptimizer i) -
        sample.sourceIntersection
          (sample.feedbackGraph hlam0 (hlam.trans (by norm_num)) x0 p0) i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
        ∑ i, (sample.targetIntersection
              (sample.feedbackGraph hlam0 (hlam.trans (by norm_num)) x0 p0)
                (sample.feedbackComparisonAssignment hlam0
                  (hlam.trans (by norm_num)) x0 p0 i) -
            sample.sourceIntersection
              (sample.feedbackGraph hlam0 (hlam.trans (by norm_num)) x0 p0) i) ^ 2 := by
  let hlamHalf : lam < 1 / 2 := hlam.trans (by norm_num)
  have hnormalized := sample.euclideanOptimizer_normalizedFeedbackEnergy_le_increasing
    hlam0 hlam hn x0 p0 hrange
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnSq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hnormalized hnSq
  have hoptimizerScale :
      (n : ℝ) ^ 2 *
          ∑ i, (sample.normalizedTargetIntersection hlam0 hlamHalf x0 p0
                (sample.euclideanOptimizer i) -
              sample.normalizedSourceIntersection hlam0 hlamHalf x0 p0 i) ^ 2 =
        ∑ i, (sample.targetIntersection
              (sample.feedbackGraph hlam0 hlamHalf x0 p0) (sample.euclideanOptimizer i) -
            sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [normalizedSourceIntersection, normalizedTargetIntersection, div_sub_div_same]
    field_simp [hnR]
  have hcomparisonScale :
      (n : ℝ) ^ 2 *
          ∑ i, (sample.normalizedTargetIntersection hlam0 hlamHalf x0 p0
                (sample.feedbackComparisonAssignment hlam0 hlamHalf x0 p0 i) -
              sample.normalizedSourceIntersection hlam0 hlamHalf x0 p0 i) ^ 2 =
        ∑ i, (sample.targetIntersection
              (sample.feedbackGraph hlam0 hlamHalf x0 p0)
                (sample.feedbackComparisonAssignment hlam0 hlamHalf x0 p0 i) -
            sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [normalizedSourceIntersection, normalizedTargetIntersection, div_sub_div_same]
    field_simp [hnR]
  calc
    ∑ i, (sample.targetIntersection
          (sample.feedbackGraph hlam0 hlamHalf x0 p0) (sample.euclideanOptimizer i) -
        sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i) ^ 2 =
        (n : ℝ) ^ 2 *
          ∑ i, (sample.normalizedTargetIntersection hlam0 hlamHalf x0 p0
                (sample.euclideanOptimizer i) -
              sample.normalizedSourceIntersection hlam0 hlamHalf x0 p0 i) ^ 2 :=
      hoptimizerScale.symm
    _ ≤ (n : ℝ) ^ 2 *
        ((quadraticUpperConstant lam /
            (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
          ∑ i, (sample.normalizedTargetIntersection hlam0 hlamHalf x0 p0
                (sample.feedbackComparisonAssignment hlam0 hlamHalf x0 p0 i) -
              sample.normalizedSourceIntersection hlam0 hlamHalf x0 p0 i) ^ 2) := hscaled
    _ = (quadraticUpperConstant lam /
          (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
        ∑ i, (sample.targetIntersection
              (sample.feedbackGraph hlam0 hlamHalf x0 p0)
                (sample.feedbackComparisonAssignment hlam0 hlamHalf x0 p0 i) -
            sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i) ^ 2 := by
      calc
        (n : ℝ) ^ 2 *
            ((quadraticUpperConstant lam /
                (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
              ∑ i, (sample.normalizedTargetIntersection hlam0 hlamHalf x0 p0
                    (sample.feedbackComparisonAssignment hlam0 hlamHalf x0 p0 i) -
                  sample.normalizedSourceIntersection hlam0 hlamHalf x0 p0 i) ^ 2) =
            (quadraticUpperConstant lam /
                (euclideanCurvatureLower * quadraticLowerConstant' lam)) *
              ((n : ℝ) ^ 2 *
                ∑ i, (sample.normalizedTargetIntersection hlam0 hlamHalf x0 p0
                      (sample.feedbackComparisonAssignment hlam0 hlamHalf x0 p0 i) -
                    sample.normalizedSourceIntersection hlam0 hlamHalf x0 p0 i) ^ 2) := by ring
        _ = _ := by rw [hcomparisonScale]

/-- Insert an ordinary I3 comparison-energy bound into the concrete rank-scale FGL2 transfer. -/
theorem euclideanOptimizer_feedbackEnergy_le_of_comparisonEnergy
    {lam C : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (x0 p0 : ℝ)
    (hrange : ∀ z, sample.normalizedFeedbackCurve hlam0
      (hlam.trans (by norm_num)) x0 p0 z ∈ Icc (-1 : ℝ) 1)
    (hcomparison :
      ∑ i, (sample.targetIntersection
            (sample.feedbackGraph hlam0 (hlam.trans (by norm_num)) x0 p0)
              (sample.feedbackComparisonAssignment hlam0
                (hlam.trans (by norm_num)) x0 p0 i) -
          sample.sourceIntersection
            (sample.feedbackGraph hlam0 (hlam.trans (by norm_num)) x0 p0) i) ^ 2 ≤
        C * (n : ℝ)) :
    ∑ i, (sample.targetIntersection
          (sample.feedbackGraph hlam0 (hlam.trans (by norm_num)) x0 p0)
            (sample.euclideanOptimizer i) -
        sample.sourceIntersection
          (sample.feedbackGraph hlam0 (hlam.trans (by norm_num)) x0 p0) i) ^ 2 ≤
      (quadraticUpperConstant lam /
        (euclideanCurvatureLower * quadraticLowerConstant' lam)) * (C * (n : ℝ)) := by
  have htransfer := sample.euclideanOptimizer_feedbackEnergy_le_increasing
    hlam0 hlam hn x0 p0 hrange
  have hupper0 : 0 ≤ quadraticUpperConstant lam := by
    dsimp [quadraticUpperConstant]
    nlinarith
  have hlower0 : 0 ≤ euclideanCurvatureLower * quadraticLowerConstant' lam :=
    mul_nonneg euclideanCurvatureLower_pos.le (quadraticLowerConstant'_pos hlam0 hlam).le
  exact htransfer.trans (mul_le_mul_of_nonneg_left hcomparison (div_nonneg hupper0 hlower0))

end FiniteSample

end OTSelector
