import OTSelector.Feedback.FeedbackMarkedMean
import OTSelector.Feedback.FiniteEventBulkIntensity

/-!
# Predictable conditional-mark transforms of the actual counts

The feedback slope has only three possible values. Its conditional mark means are therefore
bounded simple predictable transforms, and the already proved actual count intensities give
their compensated martingales directly.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace OTSelector.FiniteSample

open CountingProcess
variable {n : ℕ}

private theorem finite_range_safePreFeedbackSlope {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) :
    (Set.range (Function.uncurry (safePreFeedbackSlope (n := n) hlam0 hlamHalf x0 p0))).Finite := by
  apply (show ({lam, -lam, 0} : Set ℝ).Finite by simp).subset
  rintro q ⟨⟨t, sample⟩, rfl⟩
  simp only [Function.uncurry, safePreFeedbackSlope, feedbackSlope]
  split_ifs <;> simp

private theorem boundedSimplePredictable_markMean {lam C : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) (hC : 0 ≤ C)
    (hbound : ∀ q, |q| ≤ lam → ‖f q‖ ≤ C) :
    IsBoundedSimplePredictable (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ f (safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample)) := by
  refine ⟨(hf.comp (safePreFeedbackSlope_predictable hlam0 hlamHalf x0 p0).measurable).stronglyMeasurable,
    ?_, C, hC, ?_⟩
  · have h := (finite_range_safePreFeedbackSlope (n := n) hlam0 hlamHalf x0 p0).image f
    change (Set.range (fun p : ℝ≥0 × FiniteSample n ↦
      f (safePreFeedbackSlope hlam0 hlamHalf x0 p0 p.1 p.2))).Finite
    simpa only [← Set.range_comp, Function.comp_def, Function.uncurry] using h
  · intro t sample
    simpa only [Real.norm_eq_abs, safePreFeedbackSlope] using
      hbound _ (abs_feedbackSlope_le hlam0)

theorem sourceFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
    {lam C : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ)
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    IsBoundedSimplePredictable (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ sourceFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample) ψ) :=
  boundedSimplePredictable_markMean hlam0 hlamHalf x0 p0 _
    (measurable_sourceFeedbackMarkMean ψ hψ) hC
    (fun _ hq ↦ norm_sourceFeedbackMarkMean_le hlam0 hlamHalf hq ψ hψ hbound)

theorem targetFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
    {lam C : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ)
    (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    IsBoundedSimplePredictable (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ targetFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample) ψ) :=
  boundedSimplePredictable_markMean hlam0 hlamHalf x0 p0 _
    (measurable_targetFeedbackMarkMean ψ hψ) hC
    (fun _ hq ↦ norm_targetFeedbackMarkMean_le hlam0 hlamHalf hq ψ hψ hbound)

theorem safeSourceBulk_markMean_compensated_martingale {lam B x0 p0 C : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hn : 0 < n) (hB : 0 < B)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Martingale (compensatedIntegral
      (fun t sample ↦ safeSourceBulkCount hlam0 hlamHalf B x0 p0 t sample)
      (fun t sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample)
      (fun t sample ↦ sourceFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample) ψ))
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (finiteSampleLaw n : Measure (FiniteSample n)) :=
  (safeSourceBulkCount_hasPredictableIntensity hlam0 hlamHalf hn hB).2.2.2 _
    (sourceFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
      hlam0 hlamHalf x0 p0 ψ hψ hC hbound)

theorem safeTargetBulk_markMean_compensated_martingale {lam B x0 p0 C : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hn : 0 < n) (hB : 0 < B)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hC : 0 ≤ C) (hbound : ∀ u, ‖ψ u‖ ≤ C) :
    Martingale (compensatedIntegral
      (fun t sample ↦ safeTargetBulkCount hlam0 hlamHalf B x0 p0 t sample)
      (fun t sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample)
      (fun t sample ↦ targetFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample) ψ))
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (finiteSampleLaw n : Measure (FiniteSample n)) :=
  (safeTargetBulkCount_hasPredictableIntensity hlam0 hlamHalf hn hB).2.2.2 _
    (targetFeedbackMarkMean_safePreFeedbackSlope_boundedSimplePredictable
      hlam0 hlamHalf x0 p0 ψ hψ hC hbound)

end OTSelector.FiniteSample
