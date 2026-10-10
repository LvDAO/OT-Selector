import OTSelector.Finite.Assignment
import OTSelector.Finite.EmpiricalPlan
import OTSelector.Finite.OptimizerMeasurabilityFiber
import OTSelector.Basic.FiniteSampleLeaveOneOut
import OTSelector.Probability.IndependentFiberNull

/-!
# Almost-everywhere measurability of the original Euclidean optimizer

The optimizer remains the original `Classical.choose` definition.  Distinct assignments have
different costs almost surely under the actual iid sample law.  A measurable finite minimizer
therefore agrees almost everywhere with that original optimizer.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

@[fun_prop]
theorem measurable_euclideanEdgeCost (i j : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.euclideanEdgeCost i j) := by
  unfold euclideanEdgeCost horizontalGap
  fun_prop

@[fun_prop]
theorem measurable_euclideanAssignmentCost (σ : Assignment n) :
    Measurable (fun sample : FiniteSample n ↦ assignmentCost sample.euclideanEdgeCost σ) := by
  unfold assignmentCost
  exact Finset.measurable_sum _ (fun i _ ↦ measurable_euclideanEdgeCost i (σ i))

private theorem euclideanEdgeCost_coordinateRestore_sourceHeight
    (rest : FiniteSample n) (i k j : Fin n) (x : UnitMark) :
    (coordinateRestore (1, i) rest x).euclideanEdgeCost k j =
      if k = i then
        Real.sqrt (rest.horizontalGap k j ^ 2 + ((rest.targetHeight j : ℝ) - x) ^ 2)
      else rest.euclideanEdgeCost k j := by
  by_cases hki : k = i
  · subst k
    simp [coordinateRestore, ofFourArrays, toFourArrays, euclideanEdgeCost, horizontalGap]
  · simp [coordinateRestore, ofFourArrays, toFourArrays, euclideanEdgeCost,
      horizontalGap, hki]

private theorem euclideanAssignmentCost_coordinateRestore_sourceHeight
    (rest : FiniteSample n) (i : Fin n) (σ : Assignment n) (x : UnitMark) :
    assignmentCost (coordinateRestore (1, i) rest x).euclideanEdgeCost σ =
      (∑ k ∈ Finset.univ.erase i, rest.euclideanEdgeCost k (σ k)) +
        Real.sqrt (rest.horizontalGap i (σ i) ^ 2 +
          ((rest.targetHeight (σ i) : ℝ) - x) ^ 2) := by
  classical
  rw [assignmentCost, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [euclideanEdgeCost_coordinateRestore_sourceHeight, ite_eq_right (Finset.ne_of_mem_erase hk)]
  · simp only [euclideanEdgeCost_coordinateRestore_sourceHeight, ite_true]

private theorem finite_assignment_tie_sourceHeight_fibre
    (rest : FiniteSample n) (i : Fin n) (σ τ : Assignment n)
    (hheight : rest.targetHeight (σ i) ≠ rest.targetHeight (τ i)) :
    {x : UnitMark |
      assignmentCost (coordinateRestore (1, i) rest x).euclideanEdgeCost σ =
        assignmentCost (coordinateRestore (1, i) rest x).euclideanEdgeCost τ}.Finite := by
  let c := (∑ k ∈ Finset.univ.erase i, rest.euclideanEdgeCost k (τ k)) -
    ∑ k ∈ Finset.univ.erase i, rest.euclideanEdgeCost k (σ k)
  have hB : 0 < rest.horizontalGap i (τ i) :=
    lt_of_lt_of_le zero_lt_one (rest.horizontalGap_mem i (τ i)).1
  have hne : (rest.targetHeight (σ i) : ℝ) ≠ rest.targetHeight (τ i) := by
    exact fun h ↦ hheight (Subtype.ext h)
  have hf := finite_euclidean_distance_difference_fibre
    (rest.horizontalGap i (σ i)) (rest.horizontalGap i (τ i))
    (rest.targetHeight (σ i)) (rest.targetHeight (τ i)) c hB hne
  apply (hf.preimage (f := fun x : UnitMark ↦ (x : ℝ)) Subtype.val_injective.injOn).subset
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  rw [euclideanAssignmentCost_coordinateRestore_sourceHeight,
    euclideanAssignmentCost_coordinateRestore_sourceHeight] at hx
  change _ - _ = c
  dsimp [c]
  linarith

/-- Two distinct target labels have different heights almost surely in the original iid law. -/
theorem measure_targetHeight_eq_zero (j k : Fin n) (hjk : j ≠ k) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | sample.targetHeight j = sample.targetHeight k} = 0 := by
  let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
    change NullSingletonClass (volume : Measure UnitMark)
    infer_instance
  exact measure_eq_comp_eq_zero_of_indepFun
    (measurable_targetHeight k) (measurable_targetHeight j) measurable_id
    ((finiteSampleLaw_targetHeight_iIndep n).indepFun hjk.symm)
    (congrArg ProbabilityMeasure.toMeasure (targetHeight_marginal j))

/-- Distinct permutations almost surely have different total Euclidean costs. -/
theorem measure_euclideanAssignmentCost_eq_zero (σ τ : Assignment n) (hne : σ ≠ τ) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | assignmentCost sample.euclideanEdgeCost σ =
        assignmentCost sample.euclideanEdgeCost τ} = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin n, σ i ≠ τ i := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext h)
  let s : Set (FiniteSample n × UnitMark) := {pair |
    pair.1.targetHeight (σ i) ≠ pair.1.targetHeight (τ i) ∧
      assignmentCost (coordinateRestore (1, i) pair.1 pair.2).euclideanEdgeCost σ =
        assignmentCost (coordinateRestore (1, i) pair.1 pair.2).euclideanEdgeCost τ}
  have hs : MeasurableSet s := by
    exact ((measurableSet_eq_fun
      ((measurable_targetHeight (σ i)).comp measurable_fst)
      ((measurable_targetHeight (τ i)).comp measurable_fst)).compl).inter
      (measurableSet_eq_fun
        ((measurable_euclideanAssignmentCost σ).comp (measurable_coordinateRestore (1, i)))
        ((measurable_euclideanAssignmentCost τ).comp (measurable_coordinateRestore (1, i))))
  let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
    change NullSingletonClass (volume : Measure UnitMark)
    infer_instance
  have hnull : (finiteSampleLaw n : Measure (FiniteSample n))
      ((fun sample ↦ (coordinateLeaveOneOut (1, i) sample, coordinate (1, i) sample)) ⁻¹' s)
        = 0 := by
    apply measure_pair_mem_eq_zero_of_indepFun_of_finite_fibres
      (ν := (unitUniform : Measure UnitMark))
      (measurable_coordinateLeaveOneOut (1, i)) (measurable_coordinate (1, i))
      (coordinateLeaveOneOut_indepFun_coordinate (1, i))
    · exact congrArg ProbabilityMeasure.toMeasure (coordinate_marginal (1, i))
    · exact hs
    · intro rest
      by_cases hh : rest.targetHeight (σ i) = rest.targetHeight (τ i)
      · simp [s, hh]
      · exact (finite_assignment_tie_sourceHeight_fibre rest i σ τ hh).subset
          (fun x hx ↦ hx.2)
  have hheight := measure_targetHeight_eq_zero (σ i) (τ i) hi
  apply measure_mono_null (t :=
    ((fun sample ↦ (coordinateLeaveOneOut (1, i) sample, coordinate (1, i) sample)) ⁻¹' s) ∪
      {sample | sample.targetHeight (σ i) = sample.targetHeight (τ i)}) ?_
    (measure_union_null hnull hheight)
  intro sample hcost
  by_cases hh : sample.targetHeight (σ i) = sample.targetHeight (τ i)
  · exact Or.inr hh
  · left
    change _ ∧ _
    constructor
    · simpa [coordinateLeaveOneOut, ofFourArrays, toFourArrays] using hh
    · simpa only [coordinateRestore_coordinateLeaveOneOut, Set.mem_ofPred_eq] using hcost

/-- Almost surely the original Euclidean objective has no assignment-cost ties. -/
theorem ae_euclideanAssignmentCost_injective :
    ∀ᵐ sample : FiniteSample n ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      Function.Injective (assignmentCost sample.euclideanEdgeCost) := by
  have h : ∀ σ τ : Assignment n,
      ∀ᵐ sample : FiniteSample n ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      σ ≠ τ → assignmentCost sample.euclideanEdgeCost σ ≠
        assignmentCost sample.euclideanEdgeCost τ := by
    intro σ τ
    by_cases hne : σ = τ
    · exact Filter.Eventually.of_forall (fun _ h ↦ (h hne).elim)
    · have ha : ∀ᵐ sample : FiniteSample n ∂(finiteSampleLaw n : Measure (FiniteSample n)),
          assignmentCost sample.euclideanEdgeCost σ ≠
            assignmentCost sample.euclideanEdgeCost τ := by
        rw [ae_iff]
        simpa only [not_not] using measure_euclideanAssignmentCost_eq_zero σ τ hne
      exact ha.mono (fun _ h _ ↦ h)
  filter_upwards [ae_all_iff.mpr (fun σ ↦ ae_all_iff.mpr (h σ))] with sample hs
  intro σ τ heq
  by_contra hne
  exact hs σ τ hne heq

/-- Every optimal assignment equals the original chosen optimizer almost surely. -/
theorem ae_unique_euclideanOptimizer :
    ∀ᵐ sample : FiniteSample n ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      ∀ σ, OptimalAssignment sample.euclideanEdgeCost σ → σ = sample.euclideanOptimizer := by
  filter_upwards [ae_euclideanAssignmentCost_injective (n := n)] with sample hsample
  intro σ hσ
  apply hsample
  exact le_antisymm (hσ _) (sample.euclideanOptimizer_isOptimal σ)

private theorem exists_measurable_euclidean_minimizer
    [MeasurableSpace (Assignment n)] :
    ∃ f : FiniteSample n → Assignment n, Measurable f ∧
      ∀ sample, OptimalAssignment sample.euclideanEdgeCost (f sample) := by
  classical
  let _ : Encodable (Assignment n) := Encodable.ofCountable _
  let decode : ℕ → Assignment n := fun k ↦ (Encodable.decode k).getD (Equiv.refl _)
  have hdecode : Function.Surjective decode :=
    Encodable.surjective_decode_getD _ (Equiv.refl _)
  have hex : ∀ sample : FiniteSample n,
      ∃ k, OptimalAssignment sample.euclideanEdgeCost (decode k) := by
    intro sample
    obtain ⟨σ, hσ⟩ := exists_optimalAssignment sample.euclideanEdgeCost
    obtain ⟨k, rfl⟩ := hdecode σ
    exact ⟨k, hσ⟩
  have hm (k : ℕ) : MeasurableSet
      {sample : FiniteSample n | OptimalAssignment sample.euclideanEdgeCost (decode k)} := by
    simp only [OptimalAssignment, Set.ofPred_forall]
    exact MeasurableSet.iInter (fun τ ↦ measurableSet_le
      (measurable_euclideanAssignmentCost (decode k)) (measurable_euclideanAssignmentCost τ))
  refine ⟨fun sample ↦ decode (Nat.find (hex sample)), ?_, fun sample ↦ Nat.find_spec (hex sample)⟩
  exact (measurable_of_countable decode).comp (measurable_find hex hm)

/-- The original choice-based Euclidean optimizer is almost everywhere measurable under its
actual finite iid sample law, for any measurable structure on the finite assignment space. -/
theorem aemeasurable_euclideanOptimizer [MeasurableSpace (Assignment n)] :
    AEMeasurable (euclideanOptimizer : FiniteSample n → Assignment n)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  obtain ⟨f, hf, hopt⟩ := exists_measurable_euclidean_minimizer (n := n)
  apply hf.aemeasurable.congr
  filter_upwards [ae_unique_euclideanOptimizer (n := n)] with sample hs
  exact hs (f sample) (hopt sample)

/-- Each original selected target label is an almost everywhere measurable finite random
variable; this statement requires no assignment-space measurable instance. -/
theorem aemeasurable_euclideanOptimizer_apply (i : Fin n) :
    AEMeasurable (fun sample : FiniteSample n ↦ sample.euclideanOptimizer i)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  let _ : MeasurableSpace (Assignment n) := ⊤
  let _ : MeasurableSingletonClass (Assignment n) := ⟨fun _ ↦ trivial⟩
  exact (measurable_of_countable (fun σ : Assignment n ↦ σ i)).comp_aemeasurable
    aemeasurable_euclideanOptimizer

/-- The original optimizer's selected plan point is an actual measurable random point up to a
null set under the iid sample law. -/
@[fun_prop]
theorem aemeasurable_euclideanMatchedPoint (i : Fin n) :
    AEMeasurable (fun sample : FiniteSample n ↦ sample.matchedPoint sample.euclideanOptimizer i)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  have htarget : Measurable (fun pair : FiniteSample n × Fin n ↦
      pair.1.targetPoint pair.2) := by
    apply measurable_from_prod_countable_left
    intro j
    exact (measurable_targetHeight j).prodMk (measurable_targetMark j)
  exact ((measurable_sourceHeight i).prodMk (measurable_sourceMark i)).aemeasurable.prodMk
    (htarget.comp_aemeasurable (aemeasurable_id.prodMk (aemeasurable_euclideanOptimizer_apply i)))

/-- Every measurable real test integral of the original empirical optimizer plan is almost
everywhere measurable.  In particular this covers the bounded continuous tests in Selector. -/
theorem aemeasurable_integral_euclideanEmpiricalPlan [NeZero n]
    (f : PlanPoint → ℝ) (hf : Measurable f) :
    AEMeasurable (fun sample : FiniteSample n ↦
      ∫ z, f z ∂(sample.empiricalPlan sample.euclideanOptimizer : Measure PlanPoint))
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  simp only [empiricalPlan_toMeasure, integral_empiricalMeasure _ hf.stronglyMeasurable]
  apply AEMeasurable.const_mul
  exact Finset.aemeasurable_fun_sum _ (fun i _ ↦
    hf.comp_aemeasurable (aemeasurable_euclideanMatchedPoint i))

private theorem measurable_empiricalProbabilityMeasure_points [NeZero n] :
    Measurable (empiricalProbabilityMeasure :
      (Fin n → PlanPoint) → ProbabilityMeasure PlanPoint) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    smul_eq_mul]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact (Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp (measurable_pi_apply i))

/-- The empirical plan of the original choice-based optimizer is an almost everywhere
measurable probability-measure-valued random variable under the actual iid sample law. -/
theorem aemeasurable_euclideanEmpiricalPlan [NeZero n] :
    AEMeasurable (fun sample : FiniteSample n ↦ sample.empiricalPlan sample.euclideanOptimizer)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  exact measurable_empiricalProbabilityMeasure_points.comp_aemeasurable
    (aemeasurable_pi_lambda _ aemeasurable_euclideanMatchedPoint)

end FiniteSample

end OTSelector
