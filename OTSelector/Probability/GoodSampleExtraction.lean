import OTSelector.Probability.TriangularArray
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# Deterministic witnesses to a failure of empirical convergence

A persistent bad probability survives three finite-prefix budgets: the complement of the good
set, countably many eventual constraints with summable bounds, and masked residual errors tending
to zero. The increasing extraction imposes only finitely many constraints in any fixed row.
No annealed moment or simultaneous infinite-row good event is inferred.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators Classical

namespace OTSelector.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Extract actual bad samples satisfying the good event, every eventual constraint, and all
vanishing masked residuals. Each stage uses only a finite prefix. The constraint probabilities
already imply nonnegativity of their weight bounds, so a separate sign premise is unnecessary. -/
theorem exists_good_bad_samples_with_constraints_of_frequently
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (good bad : ∀ n, Set (Ω n)) (constraint : ∀ _m n : ℕ, Set (Ω n))
    (residual : ∀ _m n : ℕ, Ω n → ℝ) (weight : ℕ → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hbad : ∃ᶠ n in atTop, δ ≤ (P n).real (bad n))
    (hgood : ∀ᶠ n in atTop, (P n).real (good n)ᶜ ≤ δ / 4)
    (hweight : ∀ j, ∑ m ∈ Finset.range (j + 1), weight m ≤ δ / 4)
    (hconstraint : ∀ m, ∀ᶠ n in atTop,
      (P n).real (good n ∩ (constraint m n)ᶜ) ≤ weight m)
    (hres : ∀ m ε, 0 < ε → Tendsto
      (fun n ↦ (P n).real (good n ∩ {ω | ε < |residual m n ω|})) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ sample : ∀ j, Ω (φ j),
      (∀ j, sample j ∈ good (φ j) ∧ sample j ∈ bad (φ j)) ∧
      (∀ m, ∀ᶠ j in atTop, sample j ∈ constraint m (φ j)) ∧
      ∀ m, Tendsto (fun j ↦ residual m (φ j) (sample j)) atTop (𝓝 0) := by
  have hchoice (j : ℕ) : ∃ᶠ n in atTop, ∃ ω : Ω n,
      ω ∈ good n ∧ ω ∈ bad n ∧
        (∀ m ∈ Finset.range (j + 1), ω ∈ constraint m n) ∧
        ∀ m ∈ Finset.range (j + 1), |residual m n ω| ≤ 1 / ((j : ℝ) + 1) := by
    have hcon : ∀ᶠ n in atTop, ∀ m ∈ Finset.range (j + 1),
        (P n).real (good n ∩ (constraint m n)ᶜ) ≤ weight m := by
      apply (eventually_all_finset _).mpr
      intro m _
      exact hconstraint m
    have hres' : ∀ᶠ n in atTop, ∀ m ∈ Finset.range (j + 1),
        (P n).real (good n ∩ {ω | 1 / ((j : ℝ) + 1) < |residual m n ω|}) <
          δ / (4 * ((j : ℝ) + 1)) := by
      apply (eventually_all_finset _).mpr
      intro m _
      exact (hres m _ (by positivity)).eventually (gt_mem_nhds (by positivity))
    apply (hbad.and_eventually (hgood.and (hcon.and hres'))).mono
    intro n hn
    by_contra hnone
    let C : ℕ → Set (Ω n) := fun m ↦ good n ∩ (constraint m n)ᶜ
    let E : ℕ → Set (Ω n) := fun m ↦
      good n ∩ {ω | 1 / ((j : ℝ) + 1) < |residual m n ω|}
    have hsub : bad n ⊆ (good n)ᶜ ∪
        ((⋃ m ∈ Finset.range (j + 1), C m) ∪ ⋃ m ∈ Finset.range (j + 1), E m) := by
      intro ω hω
      by_cases hg : ω ∈ good n
      · right
        by_contra hno
        simp only [mem_union, not_or] at hno
        apply hnone
        refine ⟨ω, hg, hω, fun m hm ↦ ?_, fun m hm ↦ le_of_not_gt ?_⟩
        · by_contra hc
          exact hno.1 (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hm, ⟨hg, hc⟩⟩⟩)
        · intro hr
          exact hno.2 (mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hm, ⟨hg, hr⟩⟩⟩)
      · exact Or.inl hg
    have hsumC : ∑ m ∈ Finset.range (j + 1), (P n).real (C m) ≤ δ / 4 :=
      (Finset.sum_le_sum (fun m hm ↦ hn.2.2.1 m hm)).trans (hweight j)
    have hsumE : ∑ m ∈ Finset.range (j + 1), (P n).real (E m) ≤ δ / 4 := by
      calc
        _ ≤ ∑ _m ∈ Finset.range (j + 1), δ / (4 * ((j : ℝ) + 1)) :=
          Finset.sum_le_sum (fun m hm ↦ (hn.2.2.2 m hm).le)
        _ = δ / 4 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          field_simp
    have hm := (measureReal_mono (μ := P n) hsub).trans (measureReal_union_le _ _)
    have hCE := measureReal_union_le (μ := P n)
      (⋃ m ∈ Finset.range (j + 1), C m) (⋃ m ∈ Finset.range (j + 1), E m)
    have hC := measureReal_biUnion_finset_le (μ := P n) (Finset.range (j + 1)) C
    have hE := measureReal_biUnion_finset_le (μ := P n) (Finset.range (j + 1)) E
    linarith [hn.1, hn.2.1]
  obtain ⟨φ, hφ, hs⟩ := extraction_forall_of_frequently hchoice
  choose sample hsample using hs
  refine ⟨φ, hφ, sample, fun j ↦ ⟨(hsample j).1, (hsample j).2.1⟩, ?_, ?_⟩
  · intro m
    filter_upwards [eventually_ge_atTop m] with j hj
    exact (hsample j).2.2.1 m (Finset.mem_range.mpr (by omega))
  · intro m
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
    refine ⟨max m N, fun j hj ↦ ?_⟩
    rw [Real.dist_eq, sub_zero]
    apply ((hsample j).2.2.2 m (Finset.mem_range.mpr (by omega))).trans_lt
    have hh := hN j ((le_max_right m N).trans hj)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      0 ≤ 1 / ((j : ℝ) + 1))] using hh

/-- The version without extra constraints follows by taking every constraint to be universal.
Unmasked residual convergence implies the masked convergence required by the stronger theorem. -/
theorem exists_good_bad_samples_of_frequently
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (good bad : ∀ n, Set (Ω n)) (residual : ∀ _m n : ℕ, Ω n → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hbad : ∃ᶠ n in atTop, δ ≤ (P n).real (bad n))
    (hgood : ∀ᶠ n in atTop, (P n).real (good n)ᶜ ≤ δ / 4)
    (hres : ∀ m ε, 0 < ε → Tendsto
      (fun n ↦ (P n).real {ω | ε < |residual m n ω|}) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ sample : ∀ j, Ω (φ j),
      (∀ j, sample j ∈ good (φ j) ∧ sample j ∈ bad (φ j)) ∧
      ∀ m, Tendsto (fun j ↦ residual m (φ j) (sample j)) atTop (𝓝 0) := by
  have hmasked (m : ℕ) (ε : ℝ) (hε : 0 < ε) : Tendsto
      (fun n ↦ (P n).real (good n ∩ {ω | ε < |residual m n ω|})) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ measureReal_nonneg)
      (fun n ↦ measureReal_mono (μ := P n) inter_subset_right) (hres m ε hε)
  obtain ⟨φ, hφ, sample, hs, _, hr⟩ :=
    exists_good_bad_samples_with_constraints_of_frequently P good bad
      (fun _ _ ↦ univ) residual (fun _ ↦ 0) hδ hbad hgood
      (fun _ ↦ by simp; positivity) (fun _ ↦ by simp) hmasked
  exact ⟨φ, hφ, sample, hs, hr⟩

end OTSelector.Probability
