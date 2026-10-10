import OTSelector.Feedback.SweptSets
import Mathlib.Probability.Independence.Basic

/-!
# Product conditioning for deferred decisions

Mathlib already proves that a finite independent family remains independent after conditioning each
coordinate to a measurable event (`ProbabilityTheory.iIndepFun.cond`).  The results below specialize
that theorem to the self-conditioning used by a predictable frontier.  There is no project-local
conditional-law postulate.
-/

open MeasureTheory ProbabilityTheory

namespace OTSelector

variable {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {P : Measure Ω} {Z : ι → Ω → E}

/-- Coordinatewise independence survives conditioning all coordinates to their current unswept
regions. -/
theorem deferredDecision_independent [Finite ι] (hZ : ∀ i, Measurable (Z i))
    (h_indep : iIndepFun Z P) (remaining : ι → Set E)
    (hremaining : ∀ i, MeasurableSet (remaining i))
    (hpositive : ∀ i, P (Z i ⁻¹' remaining i) ≠ 0) :
    iIndepFun Z P[|⋂ i, Z i ⁻¹' remaining i] := by
  have hpair : iIndepFun (fun i ω ↦ (Z i ω, Z i ω)) P := by
    simpa [Function.comp_def] using
      h_indep.comp (fun _ z ↦ (z, z)) (fun _ ↦ measurable_id.prodMk measurable_id)
  exact ProbabilityTheory.iIndepFun.cond hZ hpair hpositive hremaining

/-- Explicit finite-dimensional factorization of the conditional law on unswept regions. -/
theorem deferredDecision_factorization [Finite ι] (hZ : ∀ i, Measurable (Z i))
    (h_indep : iIndepFun Z P) (remaining : ι → Set E)
    (hremaining : ∀ i, MeasurableSet (remaining i))
    (hpositive : ∀ i, P (Z i ⁻¹' remaining i) ≠ 0)
    (s : Finset ι) (test : ι → Set E) (htest : ∀ i ∈ s, MeasurableSet (test i)) :
    P[|⋂ i, Z i ⁻¹' remaining i] (⋂ i ∈ s, Z i ⁻¹' test i) =
      ∏ i ∈ s, P[|⋂ i, Z i ⁻¹' remaining i] (Z i ⁻¹' test i) := by
  exact (deferredDecision_independent hZ h_indep remaining hremaining hpositive)
    |>.measure_inter_preimage_eq_mul s htest

/-- Each remaining coordinate has exactly its original law conditioned to its own unswept set. -/
theorem deferredDecision_marginal [Finite ι] (hZ : ∀ i, Measurable (Z i))
    (h_indep : iIndepFun Z P) (remaining : ι → Set E)
    (hremaining : ∀ i, MeasurableSet (remaining i))
    (hpositive : ∀ i, P (Z i ⁻¹' remaining i) ≠ 0)
    (i : ι) (test : Set E) (htest : MeasurableSet test) :
    P[Z i ⁻¹' test | ⋂ j, Z j ⁻¹' remaining j] =
      P[Z i ⁻¹' test | Z i in remaining i] := by
  have hpair : iIndepFun (fun j ω ↦ (Z j ω, Z j ω)) P := by
    simpa [Function.comp_def] using
      h_indep.comp (fun _ z ↦ (z, z)) (fun _ ↦ measurable_id.prodMk measurable_id)
  have h := ProbabilityTheory.cond_iInter (X := Z) (Y := Z) (t := remaining)
    (f := fun j ↦ Z j ⁻¹' test)
    (s := {i}) hZ hpair (fun j hj ↦ by
      have hji : j = i := Finset.mem_singleton.mp hj
      subst j
      exact ⟨test, htest, rfl⟩) (fun j _ ↦ hpositive j) hremaining
  simpa using h

end OTSelector
