import OTSelector.Feedback.Graph
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UnitInterval

/-!
# Constant extension of a feedback graph outside a closed interval

The extension is obtained by composing the graph curve with `Set.projIcc`.  Thus it takes
the left endpoint on the left of the interval, the right endpoint on the right, and is
unchanged on the interval itself.
-/

namespace OTSelector

namespace FeedbackGraph

variable {lam a b : ℝ} (graph : FeedbackGraph lam) (hab : a ≤ b)

/-- Constant endpoint extension of `graph.curve` from `[a,b]` to the whole real line. -/
noncomputable def extendedCurve : ℝ → ℝ :=
  Set.IccExtend hab (fun x : Set.Icc a b => graph.curve x)

theorem extendedCurve_eq_of_mem {x : ℝ} (hx : x ∈ Set.Icc a b) :
    graph.extendedCurve hab x = graph.curve x := by
  simp [extendedCurve, Set.IccExtend, Set.projIcc_of_mem hab hx]

theorem extendedCurve_eq_left {x : ℝ} (hx : x ≤ a) :
    graph.extendedCurve hab x = graph.curve a := by
  simp [extendedCurve, Set.IccExtend, Set.projIcc_of_le_left hab hx]

theorem extendedCurve_eq_right {x : ℝ} (hx : b ≤ x) :
    graph.extendedCurve hab x = graph.curve b := by
  simp [extendedCurve, Set.IccExtend, Set.projIcc_of_right_le hab hx]

theorem extendedCurve_realLipschitz :
    RealLipschitz lam (graph.extendedCurve hab) := by
  intro x y
  change |graph.curve (Set.projIcc a b hab y) -
      graph.curve (Set.projIcc a b hab x)| ≤ lam * |y - x|
  calc
    |graph.curve (Set.projIcc a b hab y) -
        graph.curve (Set.projIcc a b hab x)| ≤
        lam * |(Set.projIcc a b hab y : ℝ) - Set.projIcc a b hab x| :=
      graph.lipschitz (Set.projIcc a b hab x) (Set.projIcc a b hab y)
    _ ≤ lam * |y - x| := by
      exact mul_le_mul_of_nonneg_left
        (Set.abs_projIcc_sub_projIcc hab (c := y) (d := x)) graph.lam_nonneg

theorem extendedCurve_lipschitzWith :
    LipschitzWith (Real.toNNReal lam) (graph.extendedCurve hab) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  simpa only [Real.dist_eq, abs_sub_comm] using
    graph.extendedCurve_realLipschitz hab x y

theorem extendedCurve_continuous :
    Continuous (graph.extendedCurve hab) :=
  (graph.extendedCurve_lipschitzWith hab).continuous

end FeedbackGraph

end OTSelector
