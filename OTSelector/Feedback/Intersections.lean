import OTSelector.Feedback.Graph
import OTSelector.Feedback.Regularity
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Intersections of rank-scale phase lines with a spacelike graph

Every source or target trajectory meets a `FeedbackGraph` exactly once.  The proof uses the
Banach fixed-point theorem: the source fixed-point map has Lipschitz constant `a * lam`, while the
target map has constant `b * lam`; the mark ranges and `lam < 1 / 2` make both strict contractions.
The resulting order characterizations identify crossing-coordinate counts with the swept
half-space counts used by the empirical-process layer.
-/

open Set
open scoped BigOperators

namespace OTSelector

namespace FeedbackGraph

variable {lam : ℝ} (graph : FeedbackGraph lam)

private theorem realLipschitzWith :
    LipschitzWith (Real.toNNReal lam) graph.curve := by
  apply LipschitzWith.of_dist_le'
  intro x y
  simpa only [Real.dist_eq, abs_sub_comm] using graph.lipschitz x y

/-- The source intersection is a fixed point of `x ↦ t + a g(x)`. -/
theorem existsUnique_sourceIntersection (t : ℝ) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ∃! x, t + a * graph.curve x = x := by
  let K : NNReal := Real.toNNReal (a * lam)
  let f : ℝ → ℝ := fun x ↦ t + a * graph.curve x
  have halam0 : 0 ≤ a * lam := mul_nonneg ha.1 graph.lam_nonneg
  have hKcoe : (K : ℝ) = a * lam := by
    simp [K, Real.coe_toNNReal _ halam0]
  have hKlt : K < 1 := by
    change (K : ℝ) < 1
    rw [hKcoe]
    calc
      a * lam ≤ 1 * lam := mul_le_mul_of_nonneg_right ha.2 graph.lam_nonneg
      _ < 1 := by linarith [graph.lam_lt_half]
  have hLip : LipschitzWith K f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (t + a * graph.curve x) (t + a * graph.curve y) ≤
      (K : ℝ) * dist x y
    rw [Real.dist_eq, Real.dist_eq, add_sub_add_left_eq_sub, ← mul_sub, abs_mul,
      abs_of_nonneg ha.1, hKcoe]
    simpa only [mul_assoc, abs_sub_comm] using mul_le_mul_of_nonneg_left
      (graph.lipschitz x y) ha.1
  have hcontract : ContractingWith K f := ⟨hKlt, hLip⟩
  obtain ⟨x, hx, _⟩ := hcontract.exists_fixedPoint 0 (edist_ne_top _ _)
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hcontract.fixedPoint_unique' hy hx

/-- The target intersection is a fixed point of `x ↦ s - b g(x)`. -/
theorem existsUnique_targetIntersection (s : ℝ) {b : ℝ} (hb : b ∈ Icc (1 : ℝ) 2) :
    ∃! x, s - b * graph.curve x = x := by
  let K : NNReal := Real.toNNReal (b * lam)
  let f : ℝ → ℝ := fun x ↦ s - b * graph.curve x
  have hblam0 : 0 ≤ b * lam := mul_nonneg (le_trans zero_le_one hb.1) graph.lam_nonneg
  have hKcoe : (K : ℝ) = b * lam := by
    simp [K, Real.coe_toNNReal _ hblam0]
  have hKlt : K < 1 := by
    change (K : ℝ) < 1
    rw [hKcoe]
    calc
      b * lam ≤ 2 * lam := mul_le_mul_of_nonneg_right hb.2 graph.lam_nonneg
      _ < 1 := by linarith [graph.lam_lt_half]
  have hLip : LipschitzWith K f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (s - b * graph.curve x) (s - b * graph.curve y) ≤
      (K : ℝ) * dist x y
    rw [Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_left, ← mul_sub, abs_mul,
      abs_of_nonneg (le_trans zero_le_one hb.1), hKcoe]
    simpa only [mul_assoc, abs_sub_comm] using mul_le_mul_of_nonneg_left
      (graph.lipschitz x y) (le_trans zero_le_one hb.1)
  have hcontract : ContractingWith K f := ⟨hKlt, hLip⟩
  obtain ⟨x, hx, _⟩ := hcontract.exists_fixedPoint 0 (edist_ne_top _ _)
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hcontract.fixedPoint_unique' hy hx

/-- The source inverse coordinate `x - a g(x)` is strictly increasing. -/
theorem strictMono_sourceTransform {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    StrictMono fun x ↦ x - a * graph.curve x := by
  intro x y hxy
  have hdist : |y - x| = y - x := abs_of_pos (sub_pos.mpr hxy)
  have hcurve : graph.curve y - graph.curve x ≤ lam * (y - x) := by
    calc
      graph.curve y - graph.curve x ≤ |graph.curve y - graph.curve x| := le_abs_self _
      _ ≤ lam * |y - x| := graph.lipschitz x y
      _ = lam * (y - x) := by rw [hdist]
  have hscaled : a * (graph.curve y - graph.curve x) ≤ lam * (y - x) := by
    calc
      a * (graph.curve y - graph.curve x) ≤ a * (lam * (y - x)) :=
        mul_le_mul_of_nonneg_left hcurve ha.1
      _ ≤ lam * (y - x) := by
        have hnonneg : 0 ≤ lam * (y - x) :=
          mul_nonneg graph.lam_nonneg (sub_nonneg.mpr hxy.le)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right ha.2 hnonneg
  nlinarith [graph.lam_lt_half]

/-- The target inverse coordinate `x + b g(x)` is strictly increasing. -/
theorem strictMono_targetTransform {b : ℝ} (hb : b ∈ Icc (1 : ℝ) 2) :
    StrictMono fun x ↦ x + b * graph.curve x := by
  intro x y hxy
  have hdist : |y - x| = y - x := abs_of_pos (sub_pos.mpr hxy)
  have hcurve : graph.curve x - graph.curve y ≤ lam * (y - x) := by
    calc
      graph.curve x - graph.curve y ≤ |graph.curve y - graph.curve x| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ lam * |y - x| := graph.lipschitz x y
      _ = lam * (y - x) := by rw [hdist]
  have hb0 : 0 ≤ b := le_trans zero_le_one hb.1
  have hscaled : b * (graph.curve x - graph.curve y) ≤ 2 * lam * (y - x) := by
    calc
      b * (graph.curve x - graph.curve y) ≤ b * (lam * (y - x)) :=
        mul_le_mul_of_nonneg_left hcurve hb0
      _ ≤ 2 * lam * (y - x) := by
        have hnonneg : 0 ≤ lam * (y - x) :=
          mul_nonneg graph.lam_nonneg (sub_nonneg.mpr hxy.le)
        calc
          b * (lam * (y - x)) ≤ 2 * (lam * (y - x)) :=
            mul_le_mul_of_nonneg_right hb.2 hnonneg
          _ = 2 * lam * (y - x) := by ring
  nlinarith [graph.lam_lt_half]

end FeedbackGraph

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)

/-- Rank-scale source point `(n Tᵢ,Uᵢ)`. -/
def rankSourcePoint (i : Fin n) : ℝ × UnitMark :=
  (n * sample.sourceHeight i, sample.sourceMark i)

/-- Rank-scale target point `(n Sⱼ,Vⱼ)`. -/
def rankTargetPoint (j : Fin n) : ℝ × UnitMark :=
  (n * sample.targetHeight j, sample.targetMark j)

/-- Unique coordinate at which source trajectory `i` meets the graph. -/
noncomputable def sourceIntersection (i : Fin n) : ℝ :=
  Classical.choose <| graph.existsUnique_sourceIntersection
    (n * sample.sourceHeight i) (sample.sourceSlope_mem i)

/-- Unique coordinate at which target trajectory `j` meets the graph. -/
noncomputable def targetIntersection (j : Fin n) : ℝ :=
  Classical.choose <| graph.existsUnique_targetIntersection
    (n * sample.targetHeight j) (sample.targetSlope_mem j)

theorem sourceIntersection_spec (i : Fin n) :
    sample.sourcePhase i (graph.curve (sample.sourceIntersection graph i)) =
      sample.sourceIntersection graph i := by
  exact (Classical.choose_spec <| graph.existsUnique_sourceIntersection
    (n * sample.sourceHeight i) (sample.sourceSlope_mem i)).1

theorem targetIntersection_spec (j : Fin n) :
    sample.targetPhase j (graph.curve (sample.targetIntersection graph j)) =
      sample.targetIntersection graph j := by
  exact (Classical.choose_spec <| graph.existsUnique_targetIntersection
    (n * sample.targetHeight j) (sample.targetSlope_mem j)).1

theorem sourceIntersection_unique (i : Fin n) {x : ℝ}
    (hx : sample.sourcePhase i (graph.curve x) = x) :
    x = sample.sourceIntersection graph i := by
  exact (Classical.choose_spec <| graph.existsUnique_sourceIntersection
    (n * sample.sourceHeight i) (sample.sourceSlope_mem i)).2 x hx

theorem targetIntersection_unique (j : Fin n) {x : ℝ}
    (hx : sample.targetPhase j (graph.curve x) = x) :
    x = sample.targetIntersection graph j := by
  exact (Classical.choose_spec <| graph.existsUnique_targetIntersection
    (n * sample.targetHeight j) (sample.targetSlope_mem j)).2 x hx

/-- A source trajectory has crossed by `x` exactly when its point is in the source swept set. -/
theorem sourceIntersection_le_iff (i : Fin n) (x : ℝ) :
    sample.sourceIntersection graph i ≤ x ↔
      sample.sourcePhase i (graph.curve x) ≤ x := by
  let φ : ℝ → ℝ := fun y ↦ y - sample.sourceSlope i * graph.curve y
  have hmono : StrictMono φ := graph.strictMono_sourceTransform (sample.sourceSlope_mem i)
  have hspec : φ (sample.sourceIntersection graph i) = n * sample.sourceHeight i := by
    have h := sample.sourceIntersection_spec graph i
    simp only [sourcePhase] at h
    dsimp [φ]
    linarith
  rw [← hmono.le_iff_le, hspec]
  simp only [sourcePhase]
  constructor <;> intro h <;> linarith

/-- A target trajectory has crossed by `x` exactly when its point is in the target swept set. -/
theorem targetIntersection_le_iff (j : Fin n) (x : ℝ) :
    sample.targetIntersection graph j ≤ x ↔
      sample.targetPhase j (graph.curve x) ≤ x := by
  let φ : ℝ → ℝ := fun y ↦ y + sample.targetSlope j * graph.curve y
  have hmono : StrictMono φ := graph.strictMono_targetTransform (sample.targetSlope_mem j)
  have hspec : φ (sample.targetIntersection graph j) = n * sample.targetHeight j := by
    have h := sample.targetIntersection_spec graph j
    simp only [targetPhase] at h
    dsimp [φ]
    linarith
  rw [← hmono.le_iff_le, hspec]
  simp only [targetPhase]
  constructor <;> intro h <;> linarith

/-- Number of source intersections at or before a coordinate. -/
noncomputable def sourceIntersectionCount (x : ℝ) : ℕ :=
  Finset.card <| Finset.univ.filter fun i ↦ sample.sourceIntersection graph i ≤ x

/-- Number of target intersections at or before a coordinate. -/
noncomputable def targetIntersectionCount (x : ℝ) : ℕ :=
  Finset.card <| Finset.univ.filter fun j ↦ sample.targetIntersection graph j ≤ x

theorem sourceIntersectionCount_eq_filter_phase (x : ℝ) :
    sample.sourceIntersectionCount graph x =
      Finset.card (Finset.univ.filter fun i ↦ sample.sourcePhase i (graph.curve x) ≤ x) := by
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact sample.sourceIntersection_le_iff graph i x

theorem targetIntersectionCount_eq_filter_phase (x : ℝ) :
    sample.targetIntersectionCount graph x =
      Finset.card (Finset.univ.filter fun j ↦ sample.targetPhase j (graph.curve x) ≤ x) := by
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact sample.targetIntersection_le_iff graph j x

end FiniteSample

end OTSelector
