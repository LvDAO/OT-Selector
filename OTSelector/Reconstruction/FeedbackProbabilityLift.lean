import OTSelector.Reconstruction.FeedbackVerticalDiagonal
import OTSelector.Feedback.FeedbackSelectorGood
import OTSelector.Probability.RowProbabilityFilter
import OTSelector.Finite.EmpiricalConvergence

/-!
# Reconstruction in probability under the original iid laws

The same actual good event implies vertical concentration in probability. The row probability
filter then applies the deterministic physical-block reconstruction directly to the original
empirical optimizer, without introducing any independence between rows.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace OTSelector

open FiniteSample

/-- Actual linear FGL2 energy and its graph envelope force vertical concentration under the
original finite-sample law. -/
theorem tendsto_measureReal_meanVerticalDisplacement_optimizer
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
      {sample | ε ≤ sample.meanVerticalDisplacement sample.euclideanOptimizer}) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨A, q, qE, C, hA, _, _, _, _, hgood⟩ :=
    exists_feedbackSelectorGood_parameters hlam0 hlam hδ
  have hbound : Tendsto (fun n : ℕ ↦ Real.sqrt C / (n + 1 : ℕ) +
      (3 * A / 8) * (Real.sqrt (n + 1 : ℕ) / (n + 1 : ℕ))) atTop (𝓝 0) := by
    have h1 := (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).const_mul (Real.sqrt C)
    have h2 := (tendsto_sqrt_nat_div_nat.comp (tendsto_add_atTop_nat 1)).const_mul (3 * A / 8)
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero, add_zero] using h1.add h2
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hgood,
    hbound.eventually (gt_mem_nhds hε)] with n hg hb
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  apply lt_of_le_of_lt (measureReal_mono (μ :=
    (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1)))) ?_) hg
  intro sample hs
  change sample ∉ feedbackSelectorGoodEvent hlam0 hlam A q qE C (n + 1)
  intro hgoodSample
  have ht := feedbackSelectorGoodEvent.noFeedbackTies hgoodSample
  have he := feedbackSelectorGoodEvent.energy hgoodSample
  have hv := sample.meanVerticalDisplacement_optimizer_le_of_feedbackFGL2_energy
    hlam0.le (hlam.trans (by norm_num)) (Nat.succ_pos _) hA ht he
  exact (not_lt_of_ge (show ε ≤ sample.meanVerticalDisplacement sample.euclideanOptimizer from hs))
    (hv.trans_lt hb)

/-- Physical block convergence under the actual row laws determines the full empirical
Euclidean plan in probability. -/
theorem euclideanEmpiricalWeakTendstoInProbability_of_sourceHeightBlockMarks
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (κ : ProbabilityMeasure (UnitMark × UnitMark))
    (hblock : ∀ (u v : ℝ), 0 < u → u < v → v < 1 →
      ∀ ψ : C(UnitMark × UnitMark, ℝ), ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ ↦
          (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
            {sample | ε ≤ |sample.sourceHeightBlockMarks sample.euclideanOptimizer ψ u v -
              ∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark))|}) atTop (𝓝 0)) :
    EuclideanEmpiricalWeakTendstoInProbability (reconstructedPlan κ) := by
  let P (n : ℕ) : Measure (FiniteSample (n + 1)) := finiteSampleLaw (n + 1)
  let l := Probability.rowProbabilityFilter P
  let sample (z : Σ n : ℕ, FiniteSample (n + 1)) := z.2
  have hblocks : ∀ (u v : ℝ), 0 < u → u < v → v < 1 →
      ∀ ψ : C(UnitMark × UnitMark, ℝ),
        Tendsto (fun z ↦ (sample z).sourceHeightBlockMarks
          (sample z).euclideanOptimizer ψ u v) l
          (𝓝 (∫ m, ψ m ∂(κ : Measure (UnitMark × UnitMark)))) := by
    intro u v hu huv hv ψ
    exact (Probability.tendsto_rowProbabilityFilter_real_iff P _ _).mpr
      (hblock u v hu huv hv ψ)
  have hvd : Tendsto (fun z ↦ (sample z).meanVerticalDisplacement
      (sample z).euclideanOptimizer) l (𝓝 0) := by
    apply (Probability.tendsto_rowProbabilityFilter_real_iff P _ _).mpr
    intro ε hε
    simpa only [sample, sub_zero,
      abs_of_nonneg (FiniteSample.meanVerticalDisplacement_nonneg _ _)] using
      tendsto_measureReal_meanVerticalDisplacement_optimizer hlam0 hlam hε
  have hfull := FiniteSample.tendsto_empiricalPlan_of_sourceHeightBlockMarks sample
    (fun z ↦ (sample z).euclideanOptimizer) κ hblocks hvd
  intro f ε hε
  exact (Probability.tendsto_rowProbabilityFilter_real_iff P _ _).mp
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hfull f) ε hε

end OTSelector
