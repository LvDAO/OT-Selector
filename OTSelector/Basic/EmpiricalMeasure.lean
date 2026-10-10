import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Generic empirical probability measures

The definition is the normalized finite sum of Dirac measures.  It is deliberately independent of
the transport model so later point-process layers can reuse the same API.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace OTSelector

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {n : ℕ}

/-- The empirical measure `(1/n) • ∑ i, δ_{x i}`. -/
noncomputable def empiricalMeasure (x : Fin n → α) : Measure α :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

instance empiricalMeasure.instIsProbabilityMeasure [NeZero n] (x : Fin n → α) :
    IsProbabilityMeasure (empiricalMeasure x) := by
  constructor
  rw [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n)

/-- The empirical measure bundled as a `ProbabilityMeasure`. -/
noncomputable def empiricalProbabilityMeasure [NeZero n] (x : Fin n → α) :
    ProbabilityMeasure α :=
  ⟨empiricalMeasure x, inferInstance⟩

@[simp]
theorem empiricalProbabilityMeasure_toMeasure [NeZero n] (x : Fin n → α) :
    (empiricalProbabilityMeasure x : Measure α) = empiricalMeasure x :=
  rfl

/-- Integration against an empirical measure is a finite average. -/
theorem integral_empiricalMeasure (x : Fin n → α) {f : α → ℝ}
    (hf : StronglyMeasurable f) :
    ∫ z, f z ∂(empiricalMeasure x) = (n : ℝ)⁻¹ * ∑ i, f (x i) := by
  have hint : ∀ i : Fin n, Integrable f (Measure.dirac (x i)) :=
    fun i ↦ integrable_dirac' hf (by simp)
  rw [empiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure fun i _ ↦ hint i]
  simp only [integral_dirac' _ _ hf, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul]

/-- Empirical measures commute with measurable pushforwards. -/
theorem map_empiricalMeasure (x : Fin n → α) (f : α → β) (hf : Measurable f) :
    Measure.map f (empiricalMeasure x) = empiricalMeasure (f ∘ x) := by
  rw [empiricalMeasure, empiricalMeasure, Measure.map_smul, Measure.map_finset_sum']
  · congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by
      simpa [Function.comp_apply] using Measure.map_dirac' hf (x i)
  · exact hf.aemeasurable

/-- Reindexing a sample by a permutation leaves its empirical measure unchanged. -/
theorem empiricalMeasure_comp_perm (x : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    empiricalMeasure (x ∘ σ) = empiricalMeasure x := by
  rw [empiricalMeasure, empiricalMeasure]
  congr 1
  exact Equiv.sum_comp σ (fun i ↦ Measure.dirac (x i))

end OTSelector
