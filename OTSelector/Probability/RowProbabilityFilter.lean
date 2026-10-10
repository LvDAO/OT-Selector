import OTSelector.Probability.TriangularArray
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A filter for convergence in probability on varying sample spaces

A property of a row and its sample holds eventually in this filter exactly when the
probability of its failure tends to zero. This lets deterministic filter-level convergence
theorems apply directly to triangular arrays, without coupling the rows.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace OTSelector.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Events whose rowwise complement probabilities vanish. -/
noncomputable def rowProbabilityFilter (P : ∀ n, Measure (Ω n))
    [∀ n, IsFiniteMeasure (P n)] : Filter (Σ n, Ω n) where
  sets := {s | Tendsto (fun n ↦ (P n).real {ω | (⟨n, ω⟩ : Σ n, Ω n) ∉ s})
    atTop (𝓝 0)}
  univ_sets := by
    change Tendsto (fun n ↦ (P n).real {ω | (⟨n, ω⟩ : Σ n, Ω n) ∉ univ}) atTop (𝓝 0)
    simpa only [mem_univ, not_true_eq_false, ofPred_false, measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  sets_of_superset := by
    intro s t hs hst
    exact squeeze_zero (fun _ ↦ measureReal_nonneg)
      (fun n ↦ measureReal_mono (fun ω hω hsω ↦ hω (hst hsω))) hs
  inter_sets := by
    intro s t hs ht
    have hsum : Tendsto (fun n ↦ (P n).real {ω | (⟨n, ω⟩ : Σ n, Ω n) ∉ s} +
        (P n).real {ω | (⟨n, ω⟩ : Σ n, Ω n) ∉ t}) atTop (𝓝 0) := by
      simpa only [add_zero] using hs.add ht
    apply squeeze_zero (fun _ ↦ measureReal_nonneg) _ hsum
    intro n
    have heq : {ω | (⟨n, ω⟩ : Σ n, Ω n) ∉ s ∩ t} =
        {ω | (⟨n, ω⟩ : Σ n, Ω n) ∉ s} ∪ {ω | (⟨n, ω⟩ : Σ n, Ω n) ∉ t} := by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq, mem_union, not_and_or]
    rw [heq]
    exact measureReal_union_le _ _

theorem eventually_rowProbabilityFilter_iff (P : ∀ n, Measure (Ω n))
    [∀ n, IsFiniteMeasure (P n)] (p : (Σ n, Ω n) → Prop) :
    (∀ᶠ z in rowProbabilityFilter P, p z) ↔
      Tendsto (fun n ↦ (P n).real {ω | ¬ p ⟨n, ω⟩}) atTop (𝓝 0) := Iff.rfl

/-- The filter formulation is exactly the usual positive-distance probability criterion. -/
theorem tendsto_rowProbabilityFilter_iff (P : ∀ n, Measure (Ω n))
    [∀ n, IsFiniteMeasure (P n)] {E : Type*} [PseudoMetricSpace E]
    (X : (Σ n, Ω n) → E) (x : E) :
    Tendsto X (rowProbabilityFilter P) (𝓝 x) ↔
      ∀ ε, 0 < ε → Tendsto (fun n ↦ (P n).real {ω | ε ≤ dist (X ⟨n, ω⟩) x})
        atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  simp only [eventually_rowProbabilityFilter_iff, not_lt]

/-- Real-valued row convergence is the absolute-error formulation used by the selector. -/
theorem tendsto_rowProbabilityFilter_real_iff (P : ∀ n, Measure (Ω n))
    [∀ n, IsFiniteMeasure (P n)] (X : (Σ n, Ω n) → ℝ) (x : ℝ) :
    Tendsto X (rowProbabilityFilter P) (𝓝 x) ↔
      ∀ ε, 0 < ε → Tendsto (fun n ↦ (P n).real {ω | ε ≤ |X ⟨n, ω⟩ - x|})
        atTop (𝓝 0) := by
  simpa only [Real.dist_eq] using tendsto_rowProbabilityFilter_iff P X x

end OTSelector.Probability
