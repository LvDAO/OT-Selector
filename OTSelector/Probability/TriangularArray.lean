import Mathlib.MeasureTheory.Measure.Real

/-!
# Tight stochastic scales on varying sample spaces

The finite-`n` estimates used in the feedback construction live on a different product space for
each `n`.  This module gives the triangular-array meaning of `Xₙ = Oₚ(aₙ)` directly in terms of
uniform tail probabilities; it does not force all rows onto one artificial sample space.
-/

open Filter MeasureTheory
open scoped Topology

namespace OTSelector.Probability

/-- `Xₙ = Oₚ(aₙ)` for a triangular array whose row `n` may have its own sample space and law. -/
def IsBigOInProbability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) (scale : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop, (P n).real {ω | C * scale n < |X n ω|} ≤ ε

/-- A uniform `K / d` tail at threshold `d aₙ` implies `Oₚ(aₙ)`, even when the sample space
depends on `n`. -/
theorem isBigOInProbability_of_uniform_inv_tail
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → ℝ) (scale : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (htail : ∀ d : ℝ, 0 < d → ∀ n,
      (P n).real {ω | d * scale n ≤ |X n ω|} ≤ K / d) :
    IsBigOInProbability P X scale := by
  intro ε hε
  let C := (K + 1) / ε
  have hC : 0 < C := div_pos (by linarith) hε
  refine ⟨C, hC, Filter.Eventually.of_forall fun n ↦ ?_⟩
  have hsubset : {ω | C * scale n < |X n ω|} ⊆
      {ω | C * scale n ≤ |X n ω|} := by
    intro ω hω
    change C * scale n < |X n ω| at hω
    change C * scale n ≤ |X n ω|
    exact hω.le
  have hratio : K / C < ε := by
    rw [div_lt_iff₀ hC]
    change K < ε * ((K + 1) / ε)
    calc
      K < K + 1 := lt_add_one K
      _ = ε * ((K + 1) / ε) := by field_simp
  exact (measureReal_mono hsubset).trans ((htail C hC n).trans hratio.le)

end OTSelector.Probability
