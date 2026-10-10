import OTSelector.Feedback.FeedbackCurve
import OTSelector.Feedback.GraphExtension

/-!
# Deterministic-horizon feedback graph

The full recursive feedback curve is restricted to the deterministic interval `[B, B + T]` and
extended by its endpoint values.  In particular, because the recursive curve starts from height
zero at `B`, the left extension is zero.  This is the graph used on the A2 survival event; the
unconditioned stopped continuation is defined separately in `StoppedContinuationGraph`.
-/

open Set
open scoped NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-- The recursive feedback graph frozen outside the deterministic elapsed horizon `T`. -/
noncomputable def horizonFeedbackGraph
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) : FeedbackGraph lam :=
  let graph := sample.feedbackGraph hlam0 hlamHalf B 0
  let hBT : B ≤ B + (T : ℝ) := le_add_of_nonneg_right T.2
  { curve := graph.extendedCurve hBT
    lam_nonneg := hlam0
    lam_lt_half := hlamHalf
    lipschitz := graph.extendedCurve_realLipschitz hBT }

/-- On the deterministic horizon, the horizon graph is the original recursive graph. -/
theorem horizonFeedbackGraph_curve_eq_of_mem
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) {x : ℝ} (hx : x ∈ Icc B (B + (T : ℝ))) :
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T).curve x =
      feedbackCurve sample lam B 0 x := by
  let graph := sample.feedbackGraph hlam0 hlamHalf B 0
  let hBT : B ≤ B + (T : ℝ) := le_add_of_nonneg_right T.2
  change graph.extendedCurve hBT x = feedbackCurve sample lam B 0 x
  rw [graph.extendedCurve_eq_of_mem hBT hx]
  rfl

/-- To the left of `B`, the horizon graph has the constant value zero. -/
@[simp] theorem horizonFeedbackGraph_curve_eq_left
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) {x : ℝ} (hx : x ≤ B) :
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T).curve x = 0 := by
  let graph := sample.feedbackGraph hlam0 hlamHalf B 0
  let hBT : B ≤ B + (T : ℝ) := le_add_of_nonneg_right T.2
  change graph.extendedCurve hBT x = 0
  rw [graph.extendedCurve_eq_left hBT hx]
  simp [graph, feedbackGraph, feedbackCurve]

/-- To the right of `B + T`, the horizon graph has its right-endpoint value. -/
theorem horizonFeedbackGraph_curve_eq_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) {x : ℝ} (hx : B + (T : ℝ) ≤ x) :
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T).curve x =
      feedbackCurve sample lam B 0 (B + (T : ℝ)) := by
  let graph := sample.feedbackGraph hlam0 hlamHalf B 0
  let hBT : B ≤ B + (T : ℝ) := le_add_of_nonneg_right T.2
  change graph.extendedCurve hBT x = feedbackCurve sample lam B 0 (B + (T : ℝ))
  rw [graph.extendedCurve_eq_right hBT hx]
  rfl

/-- The horizon graph agrees with the full recursive graph at its left endpoint. -/
@[simp] theorem horizonFeedbackGraph_curve_at_left
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) :
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T).curve B = 0 :=
  sample.horizonFeedbackGraph_curve_eq_left hlam0 hlamHalf B T le_rfl

/-- The horizon graph agrees with the full recursive graph at its right endpoint. -/
theorem horizonFeedbackGraph_curve_at_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) :
    (sample.horizonFeedbackGraph hlam0 hlamHalf B T).curve (B + (T : ℝ)) =
      feedbackCurve sample lam B 0 (B + (T : ℝ)) :=
  sample.horizonFeedbackGraph_curve_eq_right hlam0 hlamHalf B T le_rfl

end FiniteSample

end OTSelector
