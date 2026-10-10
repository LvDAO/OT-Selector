import OTSelector.Reconstruction.PhysicalBlockLift

/-!
# Vertical concentration from the actual feedback energy

The intersection equations turn a uniform graph envelope and a linear rank-energy bound into
vanishing mean vertical displacement. Specializing to the actual FGL2 graph uses its already
proved I4 envelope and needs no further comparison assignment or law of large numbers.
-/

open MeasureTheory Filter Set
open scoped BigOperators Topology

set_option maxHeartbeats 1000000

namespace OTSelector.FiniteSample

variable {n : ℕ} {lam : ℝ}

/-- The target slope is at most two, so its rank-height error is at most twice the envelope. -/
theorem abs_targetIntersection_sub_rankHeight_le (sample : FiniteSample n)
    (graph : FeedbackGraph lam) {G : ℝ} (hgraph : ∀ x, |graph.curve x| ≤ G) (j : Fin n) :
    |sample.targetIntersection graph j - (n : ℝ) * sample.targetHeight j| ≤ 2 * G := by
  have hi := sample.targetIntersection_spec graph j
  change (n : ℝ) * sample.targetHeight j -
    sample.targetSlope j * graph.curve (sample.targetIntersection graph j) = _ at hi
  have hb : 0 ≤ sample.targetSlope j := (by norm_num : (0 : ℝ) ≤ 1).trans
    (sample.targetSlope_mem j).1
  have hG : 0 ≤ G := (abs_nonneg (graph.curve 0)).trans (hgraph 0)
  rw [abs_sub_comm, show (n : ℝ) * sample.targetHeight j -
    sample.targetIntersection graph j =
    sample.targetSlope j * graph.curve (sample.targetIntersection graph j) by linarith,
    abs_mul, abs_of_nonneg hb]
  exact (mul_le_mul_of_nonneg_left (hgraph _) hb).trans
    (mul_le_mul_of_nonneg_right (sample.targetSlope_mem j).2 hG)

/-- Original vertical displacement is controlled by the same edge's graph displacement. -/
theorem rank_mul_verticalDisplacement_le_graph_displacement (sample : FiniteSample n)
    (graph : FeedbackGraph lam) (σ : Assignment n) {G : ℝ}
    (hgraph : ∀ x, |graph.curve x| ≤ G) (i : Fin n) :
    (n : ℝ) * sample.verticalDisplacement σ i ≤
      |sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i| + 3 * G := by
  have hs := sample.abs_sourceIntersection_sub_rankHeight_le graph hgraph i
  have ht := sample.abs_targetIntersection_sub_rankHeight_le graph hgraph (σ i)
  have htriangle := abs_sub_le ((n : ℝ) * sample.targetHeight (σ i))
    (sample.targetIntersection graph (σ i)) ((n : ℝ) * sample.sourceHeight i)
  have htriangle' := abs_sub_le (sample.targetIntersection graph (σ i))
    (sample.sourceIntersection graph i) ((n : ℝ) * sample.sourceHeight i)
  rw [abs_sub_comm (sample.targetIntersection graph (σ i))] at ht
  rw [verticalDisplacement, ← abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n), ← abs_mul, mul_sub]
  linarith

/-- A linear rank-energy bound gives an explicit vertical estimate on the original assignment. -/
theorem meanVerticalDisplacement_le_of_graph_energy (sample : FiniteSample n)
    (graph : FeedbackGraph lam) (σ : Assignment n) (hn : 0 < n) {C G : ℝ}
    (hgraph : ∀ x, |graph.curve x| ≤ G)
    (henergy : (∑ i, (sample.targetIntersection graph (σ i) -
      sample.sourceIntersection graph i) ^ 2) ≤ C * n) :
    sample.meanVerticalDisplacement σ ≤ (Real.sqrt C + 3 * G) / n := by
  let d (i : Fin n) := sample.targetIntersection graph (σ i) -
    sample.sourceIntersection graph i
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have henergy' : (∑ i, d i ^ 2) ≤ C * n := henergy
  have hC : 0 ≤ C := by
    have hnonneg : 0 ≤ ∑ i, d i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    nlinarith
  have hcs : (∑ i, |d i|) ^ 2 ≤ (n : ℝ) * ∑ i, d i ^ 2 := by
    simpa only [sq_abs, Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun i ↦ |d i|))
  have hscaled := mul_le_mul_of_nonneg_left henergy' hnR.le
  have hsquare : (Real.sqrt C * n) ^ 2 = C * (n : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
  have habs : (∑ i, |d i|) ≤ Real.sqrt C * n := by
    have hright : 0 ≤ Real.sqrt C * n := mul_nonneg (Real.sqrt_nonneg _) hnR.le
    nlinarith [sq_nonneg ((∑ i, |d i|) - Real.sqrt C * n)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ ↦ sample.rank_mul_verticalDisplacement_le_graph_displacement graph σ hgraph i)
  have hsum' : (n : ℝ) * ∑ i, sample.verticalDisplacement σ i ≤
      (∑ i, |d i|) + n * (3 * G) := by
    simpa only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, d, mul_left_comm, mul_assoc] using hsum
  have hvertical : (∑ i, sample.verticalDisplacement σ i) ≤ Real.sqrt C + 3 * G := by
    nlinarith
  simpa only [meanVerticalDisplacement, div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hvertical (inv_nonneg.mpr hnR.le)

/-- The actual stopped FGL2 graph supplies its envelope on every no-tie sample. -/
theorem meanVerticalDisplacement_optimizer_le_of_feedbackFGL2_energy
    (sample : FiniteSample n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {amplitude C : ℝ} (hn : 0 < n) (hamp : 0 < amplitude)
    (hNoTie : sample.NoFeedbackTies lam (amplitude * Real.sqrt n) 0)
    (henergy : sample.feedbackFGL2OptimizerEnergy hlam0 hlamHalf amplitude ≤ C * n) :
    sample.meanVerticalDisplacement sample.euclideanOptimizer ≤
      Real.sqrt C / n + (3 * amplitude / 8) * (Real.sqrt n / n) := by
  have hgraph : ∀ x, |(sample.feedbackFGL2Graph hlam0 hlamHalf amplitude).curve x| ≤
      amplitude * Real.sqrt n / 8 := by
    intro x
    exact sample.abs_stoppedContinuationFeedbackGraph_curve_le hlam0 hlamHalf _
      (mul_pos hamp (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))) _ hNoTie x
  have h := sample.meanVerticalDisplacement_le_of_graph_energy
    (sample.feedbackFGL2Graph hlam0 hlamHalf amplitude) sample.euclideanOptimizer hn hgraph
    henergy
  convert h using 1; ring

/-- Along actual rows with bounded FGL2 energy, the original optimizer becomes vertical-diagonal. -/
theorem tendsto_meanVerticalDisplacement_optimizer_zero_of_feedbackFGL2_energy
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (sample : ∀ k, FiniteSample (N k))
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) {amplitude C : ℝ}
    (hamp : 0 < amplitude)
    (hNoTie : ∀ᶠ k in atTop,
      (sample k).NoFeedbackTies lam (amplitude * Real.sqrt (N k)) 0)
    (henergy : ∀ᶠ k in atTop,
      (sample k).feedbackFGL2OptimizerEnergy hlam0 hlamHalf amplitude ≤ C * N k) :
    Tendsto (fun k ↦ (sample k).meanVerticalDisplacement (sample k).euclideanOptimizer)
      atTop (𝓝 0) := by
  have hbound : Tendsto (fun k ↦ Real.sqrt C / N k +
      (3 * amplitude / 8) * (Real.sqrt (N k) / N k)) atTop (𝓝 0) := by
    have h1 := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hN)).const_mul (Real.sqrt C)
    have h2 := (tendsto_sqrt_nat_div_nat.comp hN).const_mul (3 * amplitude / 8)
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero, add_zero] using h1.add h2
  apply squeeze_zero' (Filter.Eventually.of_forall fun k ↦
    (sample k).meanVerticalDisplacement_nonneg (sample k).euclideanOptimizer) ?_ hbound
  filter_upwards [hN.eventually (eventually_gt_atTop (0 : ℕ)), hNoTie, henergy]
    with k hn ht he
  exact (sample k).meanVerticalDisplacement_optimizer_le_of_feedbackFGL2_energy
    hlam0 hlamHalf hn hamp ht he

/-- Actual physical height blocks and the same graph's energy identify the full optimizer plan. -/
theorem tendsto_empiricalPlan_optimizer_of_feedbackFGL2_sourceHeightBlockMarks
    {N : ℕ → ℕ} [∀ k, NeZero (N k)] (hN : Tendsto N atTop atTop)
    (sample : ∀ k, FiniteSample (N k)) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {amplitude C : ℝ} (hamp : 0 < amplitude)
    (hNoTie : ∀ᶠ k in atTop,
      (sample k).NoFeedbackTies lam (amplitude * Real.sqrt (N k)) 0)
    (henergy : ∀ᶠ k in atTop,
      (sample k).feedbackFGL2OptimizerEnergy hlam0 hlamHalf amplitude ≤ C * N k)
    (κ : ProbabilityMeasure (UnitMark × UnitMark))
    (hblock : ∀ (u v : ℝ), 0 < u → u < v → v < 1 →
      ∀ ψ : C(UnitMark × UnitMark, ℝ),
        Tendsto (fun k ↦ (sample k).sourceHeightBlockMarks
          (sample k).euclideanOptimizer ψ u v) atTop
          (𝓝 (∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark))))) :
    Tendsto (fun k ↦ (sample k).empiricalPlan (sample k).euclideanOptimizer)
      atTop (𝓝 (reconstructedPlan κ)) := by
  exact tendsto_empiricalPlan_of_sourceHeightBlockMarks sample
    (fun k ↦ (sample k).euclideanOptimizer) κ hblock
    (tendsto_meanVerticalDisplacement_optimizer_zero_of_feedbackFGL2_energy
      hN sample hlam0 hlamHalf hamp hNoTie henergy)

end OTSelector.FiniteSample
