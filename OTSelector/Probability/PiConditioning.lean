import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ConditionalProbability
import OTSelector.Feedback.DeferredDecision

/-!
# Conditioning a finite product measure coordinatewise

This file packages the finite-product calculation used for coordinatewise deferred decisions.
Under the product law `Measure.pi (fun _ : ι ↦ P)`, conditioning on
`Set.univ.pi remaining` leaves the coordinate evaluations independent, with coordinate `i` having
law `P[|remaining i]`.  The proofs use the product-measure evaluation theorem and the existing
`OTSelector.deferredDecision_*` lemmas; no extra conditional-law postulate is introduced.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace OTSelector.Probability

set_option linter.style.haveILetI false

variable {ι E : Type*} [Fintype ι] [MeasurableSpace E]

omit [Fintype ι] in
private theorem coordinateEval_measurable (i : ι) :
    Measurable (fun ω : ι → E ↦ ω i) := by
  exact measurable_pi_apply i

private theorem coordinateEval_preimage_measure (P : Measure E) [IsProbabilityMeasure P]
    (i : ι) (s : Set E) (hs : MeasurableSet s) :
    Measure.pi (fun _ : ι ↦ P) ((fun ω : ι → E ↦ ω i) ⁻¹' s) = P s := by
  rw [← Measure.map_apply (coordinateEval_measurable i) hs,
    (measurePreserving_eval (fun _ : ι ↦ P) i).map_eq]

private theorem coordinateEval_preimage_cond
    (P : Measure E) [IsProbabilityMeasure P] (i : ι) (s t : Set E)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (Measure.pi (fun _ : ι ↦ P))[(fun ω : ι → E ↦ ω i) ⁻¹' s |
      (fun ω : ι → E ↦ ω i) ⁻¹' t] =
      P[s | t] := by
  rw [cond_apply (ht.preimage (coordinateEval_measurable i)), cond_apply ht,
    coordinateEval_preimage_measure P i t ht, ← Set.preimage_inter,
    coordinateEval_preimage_measure P i (t ∩ s) (ht.inter hs)]

omit [Fintype ι] [MeasurableSpace E] in
private theorem coordinateEval_condition_set (remaining : ι → Set E) :
    (⋂ i, (fun ω : ι → E ↦ ω i) ⁻¹' remaining i) = Set.univ.pi remaining := by
  ext ω
  simp [Set.mem_pi]

/-- The coordinate evaluations are independent after conditioning on a measurable rectangle. -/
theorem eval_iIndep_cond_univ_pi (P : Measure E) [IsProbabilityMeasure P]
    (remaining : ι → Set E) (hremaining : ∀ i, MeasurableSet (remaining i))
    (hpositive : ∀ i, P (remaining i) ≠ 0) :
    iIndepFun (fun i (ω : ι → E) ↦ ω i)
      (Measure.pi (fun _ : ι ↦ P))[|Set.univ.pi remaining] := by
  let μ : Measure (ι → E) := Measure.pi (fun _ : ι ↦ P)
  have h_indep : iIndepFun (fun i (ω : ι → E) ↦ ω i) μ := by
    simpa [μ] using
      (iIndepFun_pi (X := fun _ : ι ↦ id)
        (fun _ ↦ measurable_id.aemeasurable (μ := P)))
  have hZ : ∀ i, Measurable (fun ω : ι → E ↦ ω i) := coordinateEval_measurable
  have hpositive' : ∀ i, μ ((fun ω : ι → E ↦ ω i) ⁻¹' remaining i) ≠ 0 := by
    intro i
    rw [show μ ((fun ω : ι → E ↦ ω i) ⁻¹' remaining i) = P (remaining i) by
      simpa [μ] using coordinateEval_preimage_measure P i (remaining i) (hremaining i)]
    exact hpositive i
  have hcond := OTSelector.deferredDecision_independent hZ h_indep remaining hremaining hpositive'
  simpa [μ, coordinateEval_condition_set remaining] using hcond

/-- The conditional law of one coordinate is the corresponding one-coordinate conditional law. -/
theorem map_eval_cond_univ_pi (P : Measure E) [IsProbabilityMeasure P]
    (remaining : ι → Set E) (hremaining : ∀ i, MeasurableSet (remaining i))
    (hpositive : ∀ i, P (remaining i) ≠ 0) (i : ι) :
    Measure.map (fun ω : ι → E ↦ ω i)
        ((Measure.pi (fun _ : ι ↦ P))[|Set.univ.pi remaining]) = P[|remaining i] := by
  let μ : Measure (ι → E) := Measure.pi (fun _ : ι ↦ P)
  have h_indep : iIndepFun (fun j (ω : ι → E) ↦ ω j) μ := by
    simpa [μ] using
      (iIndepFun_pi (X := fun _ : ι ↦ id)
        (fun _ ↦ measurable_id.aemeasurable (μ := P)))
  have hZ : ∀ j, Measurable (fun ω : ι → E ↦ ω j) := coordinateEval_measurable
  have hpositive' : ∀ j, μ ((fun ω : ι → E ↦ ω j) ⁻¹' remaining j) ≠ 0 := by
    intro j
    rw [show μ ((fun ω : ι → E ↦ ω j) ⁻¹' remaining j) = P (remaining j) by
      simpa [μ] using coordinateEval_preimage_measure P j (remaining j) (hremaining j)]
    exact hpositive j
  have hcond := OTSelector.deferredDecision_marginal hZ h_indep remaining hremaining hpositive'
    i
  ext s hs
  rw [Measure.map_apply (coordinateEval_measurable i) hs]
  rw [coordinateEval_condition_set remaining] at hcond
  calc
    (μ[|Set.univ.pi remaining]) ((fun ω : ι → E ↦ ω i) ⁻¹' s) =
        μ[(fun ω : ι → E ↦ ω i) ⁻¹' s |
          (fun ω : ι → E ↦ ω i) ⁻¹' remaining i] := hcond s hs
    _ = P[s | remaining i] := coordinateEval_preimage_cond P i s (remaining i) hs (hremaining i)

/-- The conditioned rectangle has the product of its coordinate probabilities. -/
theorem measure_univ_pi (P : Measure E) [IsProbabilityMeasure P]
    (remaining : ι → Set E) (_hremaining : ∀ i, MeasurableSet (remaining i)) :
    Measure.pi (fun _ : ι ↦ P) (Set.univ.pi remaining) = ∏ i, P (remaining i) := by
  rw [Measure.pi_pi]

/-- A rectangle with non-null coordinate factors is non-null under the product law. -/
theorem measure_univ_pi_ne_zero (P : Measure E) [IsProbabilityMeasure P]
    (remaining : ι → Set E) (hremaining : ∀ i, MeasurableSet (remaining i))
    (hpositive : ∀ i, P (remaining i) ≠ 0) :
    Measure.pi (fun _ : ι ↦ P) (Set.univ.pi remaining) ≠ 0 := by
  rw [measure_univ_pi P remaining hremaining, Finset.prod_ne_zero_iff]
  intro i _
  exact hpositive i

/-- The conditioned joint evaluation law is the product of the coordinate conditional laws. -/
theorem map_eval_cond_univ_pi_eq_pi_map (P : Measure E) [IsProbabilityMeasure P]
    (remaining : ι → Set E) (hremaining : ∀ i, MeasurableSet (remaining i))
    (hpositive : ∀ i, P (remaining i) ≠ 0) :
    Measure.map (fun (ω : ι → E) i ↦ ω i)
        ((Measure.pi (fun _ : ι ↦ P))[|Set.univ.pi remaining]) =
      Measure.pi (fun i ↦ P[|remaining i]) := by
  let μ : Measure (ι → E) := Measure.pi (fun _ : ι ↦ P)
  have hcond0 : μ (Set.univ.pi remaining) ≠ 0 := by
    simpa [μ] using measure_univ_pi_ne_zero P remaining hremaining hpositive
  haveI : IsProbabilityMeasure (μ[|Set.univ.pi remaining]) :=
    cond_isProbabilityMeasure hcond0
  have h_indep : iIndepFun (fun i (ω : ι → E) ↦ ω i) μ[|Set.univ.pi remaining] := by
    simpa [μ] using eval_iIndep_cond_univ_pi P remaining hremaining hpositive
  have hmap :=
    (iIndepFun_iff_map_fun_eq_pi_map
      (μ := μ[|Set.univ.pi remaining])
      (f := fun i (ω : ι → E) ↦ ω i)
      (fun i ↦ (coordinateEval_measurable i).aemeasurable)).mp h_indep
  calc
    Measure.map (fun (ω : ι → E) i ↦ ω i) (μ[|Set.univ.pi remaining]) =
        Measure.pi (fun i ↦ Measure.map (fun ω : ι → E ↦ ω i)
          (μ[|Set.univ.pi remaining])) := by
          simpa using hmap
    _ = Measure.pi (fun i ↦ P[|remaining i]) := by
      congr 1
      funext i
      exact map_eval_cond_univ_pi P remaining hremaining hpositive i

/-- Conditioning the finite product itself on a coordinate rectangle gives the product of the
one-coordinate conditional measures. -/
theorem cond_univ_pi_eq_pi_cond (P : Measure E) [IsProbabilityMeasure P]
    (remaining : ι → Set E) (hremaining : ∀ i, MeasurableSet (remaining i))
    (hpositive : ∀ i, P (remaining i) ≠ 0) :
    (Measure.pi (fun _ : ι ↦ P))[|Set.univ.pi remaining] =
      Measure.pi (fun i ↦ P[|remaining i]) := by
  simpa using map_eval_cond_univ_pi_eq_pi_map P remaining hremaining hpositive

/-- Under rectangle conditioning, the probability of another measurable rectangle factors into
the conditional coordinate probabilities. -/
theorem cond_univ_pi_apply_univ_pi (P : Measure E) [IsProbabilityMeasure P]
    (remaining future : ι → Set E)
    (hremaining : ∀ i, MeasurableSet (remaining i))
    (hpositive : ∀ i, P (remaining i) ≠ 0)
    (_hfuture : ∀ i, MeasurableSet (future i)) :
    ((Measure.pi (fun _ : ι ↦ P))[|Set.univ.pi remaining])
        (Set.univ.pi future) =
      ∏ i, (P[|remaining i]) (future i) := by
  rw [cond_univ_pi_eq_pi_cond P remaining hremaining hpositive]
  rw [Measure.pi_pi]

end OTSelector.Probability
