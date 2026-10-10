import OTSelector.Basic.Convergence
import OTSelector.Finite.OptimizerMeasurability
import OTSelector.Assumptions.BlockIdentification

/-!
# Weak convergence of the actual finite-sample optimizer laws

Each row uses its own canonical `finiteSampleLaw (n + 1)` and the original Euclidean optimizer.
Convergence is tested by bounded continuous integrals, exactly as in
`WeakTendstoInProbability`.  Indexing by `n + 1` keeps the empty sample out of the definition.

The row-map equivalence requires only the correct individual pushforward laws; no independence
between rows is assumed. The reconstruction theorem combines `EFE2`, almost-everywhere
`BlockIdentification`, and a comparison assignment with vanishing vertical error. The complete
iid Selector is exposed in `Main.lean`.
-/

open Filter MeasureTheory Set

namespace OTSelector

/-- Weak convergence in probability of the original Euclidean empirical plans, directly under
their individual iid sample laws. -/
def EuclideanEmpiricalWeakTendstoInProbability (ν : ProbabilityMeasure PlanPoint) : Prop :=
  ∀ f : BoundedContinuousFunction PlanPoint ℝ, ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ ↦
      (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
        {sample | ε ≤ |(∫ z, f z ∂(sample.empiricalPlan sample.euclideanOptimizer :
          Measure PlanPoint)) - ∫ z, f z ∂(ν : Measure PlanPoint)|}) atTop (nhds 0)

/-- The actual optimizer-test exceedance event is measurable up to a null set under the
original iid law. -/
theorem nullMeasurableSet_euclideanEmpiricalTest_exceedance {n : ℕ} [NeZero n]
    (ν : ProbabilityMeasure PlanPoint) (f : BoundedContinuousFunction PlanPoint ℝ) (ε : ℝ) :
    NullMeasurableSet
      {sample : FiniteSample n | ε ≤
        |(∫ z, f z ∂(sample.empiricalPlan sample.euclideanOptimizer : Measure PlanPoint)) -
          ∫ z, f z ∂(ν : Measure PlanPoint)|}
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  have hm : AEMeasurable (fun sample : FiniteSample n ↦
      (∫ z, f z ∂(sample.empiricalPlan sample.euclideanOptimizer : Measure PlanPoint)) -
        ∫ z, f z ∂(ν : Measure PlanPoint)) (finiteSampleLaw n : Measure (FiniteSample n)) :=
    (FiniteSample.aemeasurable_integral_euclideanEmpiricalPlan f f.continuous.measurable).sub
      aemeasurable_const
  exact nullMeasurableSet_le aemeasurable_const
    (continuous_abs.measurable.comp_aemeasurable hm)

private theorem tendsto_row_measureReal_le_iff_lt
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (P n)] (X : ∀ n, Ω n → ℝ) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real {ω | ε ≤ X n ω}) atTop (nhds 0)) ↔
      (∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real {ω | ε < X n ω}) atTop (nhds 0)) := by
  constructor
  · intro h ε hε
    refine squeeze_zero (fun _ ↦ measureReal_nonneg) ?_ (h ε hε)
    intro n
    have hsub : {ω : Ω n | ε < X n ω} ⊆ {ω | ε ≤ X n ω} := by
      intro ω hx
      change ε ≤ X n ω
      exact (show ε < X n ω from hx).le
    exact measureReal_mono hsub (measure_ne_top _ _)
  · intro h ε hε
    refine squeeze_zero (fun _ ↦ measureReal_nonneg) ?_ (h (ε / 2) (by linarith))
    intro n
    have hsub : {ω : Ω n | ε ≤ X n ω} ⊆ {ω | ε / 2 < X n ω} := by
      intro ω hs
      change ε ≤ X n ω at hs
      change ε / 2 < X n ω
      linarith
    exact measureReal_mono hsub (measure_ne_top _ _)

/-- Strict exceedances give the same convergence criterion as the non-strict thresholds used
by mathlib's convergence-in-measure interface. -/
theorem euclideanEmpiricalWeakTendstoInProbability_iff_strict
    (ν : ProbabilityMeasure PlanPoint) :
    EuclideanEmpiricalWeakTendstoInProbability ν ↔
      ∀ f : BoundedContinuousFunction PlanPoint ℝ, ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ ↦
          (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))).real
            {sample | ε < |(∫ z, f z ∂(sample.empiricalPlan sample.euclideanOptimizer :
              Measure PlanPoint)) - ∫ z, f z ∂(ν : Measure PlanPoint)|}) atTop (nhds 0) := by
  unfold EuclideanEmpiricalWeakTendstoInProbability
  apply forall_congr'
  intro f
  exact tendsto_row_measureReal_le_iff_lt
    (fun n ↦ (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))))
    (fun n sample ↦ |(∫ z, f z ∂(sample.empiricalPlan sample.euclideanOptimizer :
      Measure PlanPoint)) - ∫ z, f z ∂(ν : Measure PlanPoint)|)

/-- A row having the exact canonical sample law has the exact same optimizer-test
exceedance probabilities, including for the original choice-based optimizer. -/
theorem euclideanEmpiricalTest_exceedance_probability_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} [NeZero n] (row : Ω → FiniteSample n) (hrow : AEMeasurable row P)
    (hlaw : P.map row = (finiteSampleLaw n : Measure (FiniteSample n)))
    (ν : ProbabilityMeasure PlanPoint) (f : BoundedContinuousFunction PlanPoint ℝ) (ε : ℝ) :
    P.real {ω | ε ≤
      |(∫ z, f z ∂((row ω).empiricalPlan (row ω).euclideanOptimizer : Measure PlanPoint)) -
        ∫ z, f z ∂(ν : Measure PlanPoint)|} =
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample | ε ≤
          |(∫ z, f z ∂(sample.empiricalPlan sample.euclideanOptimizer : Measure PlanPoint)) -
            ∫ z, f z ∂(ν : Measure PlanPoint)|} := by
  have hs := nullMeasurableSet_euclideanEmpiricalTest_exceedance ν f ε (n := n)
  rw [← hlaw] at hs
  have hmap := Measure.map_apply₀ hrow hs
  rw [hlaw] at hmap
  exact (congrArg ENNReal.toReal hmap).symm

/-- The varying-sample-space definition is equivalent to the existing common-space definition
for any realization with the correct row marginals. -/
theorem euclideanEmpiricalWeakTendstoInProbability_iff_rows
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (row : ∀ n : ℕ, Ω → FiniteSample (n + 1))
    (hrow : ∀ n, AEMeasurable (row n) P)
    (hlaw : ∀ n, P.map (row n) =
      (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))))
    (ν : ProbabilityMeasure PlanPoint) :
    EuclideanEmpiricalWeakTendstoInProbability ν ↔
      WeakTendstoInProbability P
        (fun n ω ↦ (row n ω).empiricalPlan (row n ω).euclideanOptimizer) atTop ν := by
  constructor
  · intro h f
    apply tendstoInProbability_iff_measureReal_dist.mpr
    intro ε hε
    have heq := fun n ↦ euclideanEmpiricalTest_exceedance_probability_eq
      (row n) (hrow n) (hlaw n) ν f ε
    simpa only [Real.dist_eq, heq] using h f ε hε
  · intro h f ε hε
    have ht := tendstoInProbability_iff_measureReal_dist.mp (h f) ε hε
    have heq := fun n ↦ euclideanEmpiricalTest_exceedance_probability_eq
      (row n) (hrow n) (hlaw n) ν f ε
    simpa only [Real.dist_eq, heq] using ht

/-- The explicit test random variable on a common probability space is almost everywhere
measurable as soon as its row map has the actual canonical sample law. -/
theorem aemeasurable_euclideanEmpiricalTest_row
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} [NeZero n] (row : Ω → FiniteSample n) (hrow : AEMeasurable row P)
    (hlaw : P.map row = (finiteSampleLaw n : Measure (FiniteSample n)))
    (f : BoundedContinuousFunction PlanPoint ℝ) :
    AEMeasurable (fun ω ↦
      ∫ z, f z ∂((row ω).empiricalPlan (row ω).euclideanOptimizer : Measure PlanPoint)) P := by
  have hm := FiniteSample.aemeasurable_integral_euclideanEmpiricalPlan
    (n := n) f f.continuous.measurable
  rw [← hlaw] at hm
  exact hm.comp_aemeasurable hrow

/-- Almost-everywhere block identification and a comparison assignment with vanishing vertical
error imply weak convergence in probability under the actual varying-row iid laws. -/
theorem euclideanEmpiricalWeakTendstoInProbability_of_reconstruction_rows
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (row : ∀ n : ℕ, Ω → FiniteSample (n + 1))
    (hrow : ∀ n, AEMeasurable (row n) P)
    (hlaw : ∀ n, P.map (row n) =
      (finiteSampleLaw (n + 1) : Measure (FiniteSample (n + 1))))
    (κ : ProbabilityMeasure (UnitMark × UnitMark)) (hEFE2 : EFE2 κ)
    (hBlock : ∀ᵐ ω ∂P,
      BlockIdentification (l := atTop) (fun n ↦ row n ω) κ hEFE2)
    (reference : ∀ n : ℕ, Ω → Assignment (n + 1))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n)
    (href : ∀ᵐ ω ∂P, ∀ n i,
      (row n ω).verticalEdgeDisplacement i (reference n ω i) ≤ ε n)
    (hε : Tendsto ε atTop (nhds 0)) :
    EuclideanEmpiricalWeakTendstoInProbability (reconstructedPlan κ) := by
  apply (euclideanEmpiricalWeakTendstoInProbability_iff_rows
    P row hrow hlaw (reconstructedPlan κ)).mpr
  intro f
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (aemeasurable_euclideanEmpiricalTest_row
      (row n) (hrow n) (hlaw n) f).aestronglyMeasurable
  · filter_upwards [hBlock, href] with ω hBlockω hrefω
    have hplan := FiniteSample.tendsto_empiricalPlan_of_diagonalPlan
      (fun n ↦ row n ω) (fun n ↦ (row n ω).euclideanOptimizer) (reconstructedPlan κ)
      hBlockω.diagonal_tendsto
      (FiniteSample.tendsto_meanVerticalDisplacement_optimizer_zero
        (fun n ↦ row n ω) (fun n ↦ reference n ω) ε hε0 hrefω hε)
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).tendsto
      (reconstructedPlan κ) |>.comp hplan

end OTSelector
