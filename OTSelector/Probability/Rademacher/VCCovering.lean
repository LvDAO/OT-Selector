/-
Copyright (c) 2026 Yuwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuwei Lu
-/

import OTSelector.Probability.Rademacher.Dudley
import LeanPool.FormalLearningTheory.PureMath.FiniteVCApprox
import Mathlib.InformationTheory.Hamming

/-!
# Fixed-sample Boolean covering infrastructure

This file supplies the deterministic bridge between Boolean patterns on a fixed sample and the
Euclidean covering numbers consumed by `fixedRademacherComplexity_le_dudleySum`.

The local `lean-pool` provides VC dimension and Sauer--Shelah restriction bounds, while mathlib
provides `Metric.coveringNumber`, `Metric.packingNumber`, and their comparison.  Neither library
currently proves Haussler's VC packing lemma.  Accordingly this module proves the exact geometry
and packing-to-covering reduction, but does not replace Haussler's log-free estimate by the weaker
cardinality bound from Sauer--Shelah.
-/

open scoped ENNReal NNReal

namespace OTSelector.Probability.Rademacher

open Classical

/-- Embed a Boolean pattern as its `0`/`1` evaluation vector in Euclidean sample space. -/
noncomputable def indicatorVector {m : ℕ} (p : Fin m → Bool) : SampleVector m :=
  WithLp.toLp 2 fun i ↦ if p i then 1 else 0

/-- The finite set of Euclidean indicator vectors associated with a finite Boolean family. -/
noncomputable def indicatorVectors {m : ℕ} (H : Finset (Fin m → Bool)) :
    Finset (SampleVector m) :=
  H.image indicatorVector

/-- The distinct Boolean restrictions of a finite concept class to a fixed sample. -/
noncomputable def samplePatterns {Ω : Type*} {m : ℕ}
    (C : Finset (Concept Ω Bool)) (z : Fin m → Ω) : Finset (Fin m → Bool) :=
  C.image fun h i ↦ h (z i)

/-- Indicator evaluation vectors of a finite concept class on a fixed sample. -/
noncomputable def sampleIndicatorVectors {Ω : Type*} {m : ℕ}
    (C : Finset (Concept Ω Bool)) (z : Fin m → Ω) : Finset (SampleVector m) :=
  indicatorVectors (samplePatterns C z)

@[simp]
theorem indicatorVector_apply {m : ℕ} (p : Fin m → Bool) (i : Fin m) :
    indicatorVector p i = if p i then 1 else 0 := rfl

theorem indicatorVector_injective {m : ℕ} : Function.Injective (@indicatorVector m) := by
  intro p q hpq
  funext i
  have hi := congr_arg (fun v : SampleVector m ↦ v i) hpq
  simp only [indicatorVector_apply] at hi
  cases hpi : p i <;> cases hqi : q i <;> simp_all

@[simp]
theorem indicatorVectors_card {m : ℕ} (H : Finset (Fin m → Bool)) :
    (indicatorVectors H).card = H.card := by
  rw [indicatorVectors, Finset.card_image_of_injective _ indicatorVector_injective]

@[simp]
theorem mem_indicatorVectors_iff {m : ℕ} (H : Finset (Fin m → Bool))
    (v : SampleVector m) :
    v ∈ indicatorVectors H ↔ ∃ p ∈ H, indicatorVector p = v := by
  simp [indicatorVectors]

@[simp]
theorem mem_samplePatterns_iff {Ω : Type*} {m : ℕ}
    (C : Finset (Concept Ω Bool)) (z : Fin m → Ω) (p : Fin m → Bool) :
    p ∈ samplePatterns C z ↔ ∃ h ∈ C, (∀ i, h (z i) = p i) := by
  simp only [samplePatterns, Finset.mem_image]
  constructor
  · rintro ⟨h, hhC, rfl⟩
    exact ⟨h, hhC, fun _ ↦ rfl⟩
  · rintro ⟨h, hhC, hp⟩
    exact ⟨h, hhC, funext hp⟩

theorem samplePatterns_card_le {Ω : Type*} {m : ℕ}
    (C : Finset (Concept Ω Bool)) (z : Fin m → Ω) :
    (samplePatterns C z).card ≤ C.card := by
  exact Finset.card_image_le

/-- Squared Euclidean distance of indicator vectors is exactly their Hamming distance. -/
theorem indicatorVector_dist_sq {m : ℕ} (p q : Fin m → Bool) :
    dist (indicatorVector p) (indicatorVector q) ^ 2 = (hammingDist p q : ℝ) := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [indicatorVector_apply, Real.dist_eq, hammingDist]
  rw [Finset.cast_card, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpq : p i = q i
  · simp [hpq]
  · cases hpi : p i <;> cases hqi : q i <;> simp_all

/-- Euclidean separation of a finite indicator family is exactly squared Hamming separation.
This is the geometric input expected by the projection step in Haussler's packing proof. -/
theorem indicatorVectors_isSeparated_iff {m : ℕ} (ε : ℝ≥0)
    (H : Finset (Fin m → Bool)) :
    Metric.IsSeparated ε (indicatorVectors H : Set (SampleVector m)) ↔
      ∀ p ∈ H, ∀ q ∈ H, p ≠ q →
        (ε : ℝ) ^ 2 < (hammingDist p q : ℝ) := by
  constructor
  · intro hsep p hp q hq hpq
    have hp_mem : indicatorVector p ∈ indicatorVectors H := by
      exact (mem_indicatorVectors_iff H _).2 ⟨p, hp, rfl⟩
    have hq_mem : indicatorVector q ∈ indicatorVectors H := by
      exact (mem_indicatorVectors_iff H _).2 ⟨q, hq, rfl⟩
    have hpq_vec : indicatorVector p ≠ indicatorVector q :=
      fun h ↦ hpq (indicatorVector_injective h)
    have hed := hsep hp_mem hq_mem hpq_vec
    have hnn : ε < nndist (indicatorVector p) (indicatorVector q) := by
      simpa only [edist_nndist, ENNReal.coe_lt_coe] using hed
    have hreal : (ε : ℝ) < dist (indicatorVector p) (indicatorVector q) := by
      exact_mod_cast hnn
    rw [← indicatorVector_dist_sq]
    exact (sq_lt_sq₀ ε.coe_nonneg dist_nonneg).2 hreal
  · intro hham v hv w hw hvw
    obtain ⟨p, hp, rfl⟩ := (mem_indicatorVectors_iff H v).mp hv
    obtain ⟨q, hq, rfl⟩ := (mem_indicatorVectors_iff H w).mp hw
    have hpq : p ≠ q := fun h ↦ hvw (congr_arg indicatorVector h)
    have hsq := hham p hp q hq hpq
    rw [← indicatorVector_dist_sq] at hsq
    have hreal : (ε : ℝ) < dist (indicatorVector p) (indicatorVector q) :=
      (sq_lt_sq₀ ε.coe_nonneg dist_nonneg).1 hsq
    have hnn : ε < nndist (indicatorVector p) (indicatorVector q) := by
      exact_mod_cast hreal
    simpa only [edist_nndist, ENNReal.coe_lt_coe] using hnn

/-- Restricting a finite Boolean family cannot increase its finite VC dimension. -/
theorem boolVCDim_mono {m : ℕ} {H K : Finset (Fin m → Bool)} (hHK : H ⊆ K) :
    H.boolVCDim ≤ K.boolVCDim := by
  unfold Finset.boolVCDim
  exact Finset.vcDim_mono (Finset.image_subset_image hHK)

/-- Every finite Euclidean set has a finite packing number. -/
private lemma packingNumber_ne_top {m : ℕ} (ε : ℝ≥0) (A : Finset (SampleVector m)) :
    Metric.packingNumber ε (A : Set (SampleVector m)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr A.finite_toSet)
  exact Metric.packingNumber_le_encard_self (A : Set (SampleVector m))

/-- A finite set contains an `ε`-separated subfamily whose cardinality bounds its internal
covering number.  This packages mathlib's canonical maximal separated set as a `Finset`. -/
theorem exists_separated_subfamily_coveringCard_le {m : ℕ} (ε : ℝ≥0)
    (A : Finset (SampleVector m)) :
    ∃ P : Finset (SampleVector m), P ⊆ A ∧
      Metric.IsSeparated ε (P : Set (SampleVector m)) ∧ coveringCard ε A ≤ P.card := by
  have hpacking_ne_top := packingNumber_ne_top ε A
  have hmax_finite :
      (Metric.maximalSeparatedSet ε (A : Set (SampleVector m))).Finite := by
    rw [← Set.encard_ne_top_iff, Metric.encard_maximalSeparatedSet hpacking_ne_top]
    exact hpacking_ne_top
  let P : Finset (SampleVector m) :=
    hmax_finite.toFinset
  have hP_subset : P ⊆ A := by
    intro x hx
    simp only [P, Set.Finite.mem_toFinset] at hx
    exact Metric.maximalSeparatedSet_subset hx
  have hP_sep : Metric.IsSeparated ε (P : Set (SampleVector m)) := by
    simpa [P] using
      (Metric.isSeparated_maximalSeparatedSet
        (X := SampleVector m) (ε := ε) (A := (A : Set (SampleVector m))))
  have hcover_pack := Metric.coveringNumber_le_packingNumber ε (A : Set (SampleVector m))
  have hpack_eq : Metric.packingNumber ε (A : Set (SampleVector m)) = P.card := by
    calc
      Metric.packingNumber ε (A : Set (SampleVector m)) =
          (Metric.maximalSeparatedSet ε (A : Set (SampleVector m))).encard :=
        (Metric.encard_maximalSeparatedSet hpacking_ne_top).symm
      _ = P.card := by
        simpa only [P] using hmax_finite.encard_eq_coe_toFinset_card
  refine ⟨P, hP_subset, hP_sep, ?_⟩
  exact ENat.toNat_le_of_le_natCast (hcover_pack.trans_eq hpack_eq)

/-- A bound for every separated subfamily bounds mathlib's internal covering number.

This is the exact deterministic handoff required from a future packing theorem.  Its hypothesis
concerns ordinary `Finset`s rather than a bundled interface. -/
theorem coveringCard_le_of_separated_subfamily_bound {m M : ℕ} (ε : ℝ≥0)
    (A : Finset (SampleVector m))
    (hpack : ∀ P : Finset (SampleVector m), P ⊆ A →
      Metric.IsSeparated ε (P : Set (SampleVector m)) → P.card ≤ M) :
    coveringCard ε A ≤ M := by
  obtain ⟨P, hP_subset, hP_sep, hcover⟩ := exists_separated_subfamily_coveringCard_le ε A
  exact hcover.trans (hpack P hP_subset hP_sep)

/-- The Boolean image contains a separated Boolean subfamily whose cardinality controls its
Euclidean covering number.  Injectivity of `indicatorVector` ensures no patterns are lost. -/
theorem exists_separated_indicator_subfamily_coveringCard_le {m : ℕ} (ε : ℝ≥0)
    (H : Finset (Fin m → Bool)) :
    ∃ Q : Finset (Fin m → Bool), Q ⊆ H ∧
      Metric.IsSeparated ε (indicatorVectors Q : Set (SampleVector m)) ∧
        coveringCard ε (indicatorVectors H) ≤ Q.card := by
  obtain ⟨P, hP_subset, hP_sep, hcover⟩ :=
    exists_separated_subfamily_coveringCard_le ε (indicatorVectors H)
  let Q := H.filter (fun p ↦ indicatorVector p ∈ P)
  have hQ_subset : Q ⊆ H := Finset.filter_subset _ _
  have hQ_image : indicatorVectors Q = P := by
    apply Finset.Subset.antisymm
    · intro v hv
      rw [mem_indicatorVectors_iff] at hv
      obtain ⟨p, hpQ, rfl⟩ := hv
      exact (Finset.mem_filter.mp hpQ).2
    · intro v hv
      obtain ⟨p, hpH, hpv⟩ := (mem_indicatorVectors_iff H v).mp (hP_subset hv)
      rw [← hpv]
      exact (mem_indicatorVectors_iff Q (indicatorVector p)).2
        ⟨p, Finset.mem_filter.mpr ⟨hpH, hpv ▸ hv⟩, rfl⟩
  refine ⟨Q, hQ_subset, hQ_image.symm ▸ hP_sep, ?_⟩
  simpa [← hQ_image] using hcover

/-- Boolean-pattern version of `coveringCard_le_of_separated_subfamily_bound`.

The premise is precisely the missing combinatorial step: it asks for the cardinality bound only
on separated Boolean subfamilies of `H`.  The conclusion is already in the `coveringCard` form
used by fixed-sample Dudley chaining. -/
theorem indicator_coveringCard_le_of_separated_subfamily_bound {m M : ℕ} (ε : ℝ≥0)
    (H : Finset (Fin m → Bool))
    (hpack : ∀ Q : Finset (Fin m → Bool), Q ⊆ H →
      Metric.IsSeparated ε (indicatorVectors Q : Set (SampleVector m)) → Q.card ≤ M) :
    coveringCard ε (indicatorVectors H) ≤ M := by
  obtain ⟨Q, hQ_subset, hQ_sep, hcover⟩ :=
    exists_separated_indicator_subfamily_coveringCard_le ε H
  exact hcover.trans (hpack Q hQ_subset hQ_sep)

/-- Polynomial-form handoff from Haussler packing to the covering cardinality used by Dudley.

For `0`/`1` vectors the Euclidean radius `ε` corresponds to normalized Hamming radius
`ε² / m`, hence the exponent `2 * v`.  This theorem performs all geometric, VC-monotonicity,
and covering-number steps; its sole premise `hhaussler` is the still-missing combinatorial
separated-subfamily estimate. -/
theorem indicator_coveringCard_cast_le_polynomial_of_haussler_subfamily_bound
    {m v : ℕ} (ε : ℝ≥0) (H : Finset (Fin m → Bool)) (C : ℝ)
    (hVC : H.boolVCDim ≤ v)
    (hhaussler : ∀ Q : Finset (Fin m → Bool), Q ⊆ H → Q.boolVCDim ≤ v →
      Metric.IsSeparated ε (indicatorVectors Q : Set (SampleVector m)) →
        (Q.card : ℝ) ≤ C * (Real.sqrt m / (ε : ℝ)) ^ (2 * v)) :
    (coveringCard ε (indicatorVectors H) : ℝ) ≤
      C * (Real.sqrt m / (ε : ℝ)) ^ (2 * v) := by
  obtain ⟨Q, hQ_subset, hQ_sep, hcover⟩ :=
    exists_separated_indicator_subfamily_coveringCard_le ε H
  exact (Nat.cast_le.mpr hcover).trans
    (hhaussler Q hQ_subset ((boolVCDim_mono hQ_subset).trans hVC) hQ_sep)

/-- Fixed-sample concept-class specialization of the polynomial covering handoff.  Its conclusion
can be substituted directly for each `coveringCard (dyadicRadius R j) A` in Dudley chaining by
taking `H = samplePatterns C z` and `A = sampleIndicatorVectors C z`. -/
theorem sampleIndicator_coveringCard_cast_le_polynomial_of_haussler_subfamily_bound
    {Ω : Type*} {m v : ℕ} (ε : ℝ≥0) (C : Finset (Concept Ω Bool))
    (z : Fin m → Ω) (Cvc : ℝ)
    (hVC : (samplePatterns C z).boolVCDim ≤ v)
    (hhaussler : ∀ Q : Finset (Fin m → Bool), Q ⊆ samplePatterns C z →
      Q.boolVCDim ≤ v →
      Metric.IsSeparated ε (indicatorVectors Q : Set (SampleVector m)) →
        (Q.card : ℝ) ≤ Cvc * (Real.sqrt m / (ε : ℝ)) ^ (2 * v)) :
    (coveringCard ε (sampleIndicatorVectors C z) : ℝ) ≤
      Cvc * (Real.sqrt m / (ε : ℝ)) ^ (2 * v) := by
  exact indicator_coveringCard_cast_le_polynomial_of_haussler_subfamily_bound
    ε (samplePatterns C z) Cvc hVC hhaussler

end OTSelector.Probability.Rademacher
