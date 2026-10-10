/-
Copyright (c) 2026 Yuwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuwei Lu

The dyadic chaining architecture is adapted from
`auto-res/lean-rademacher` commit bc33376, `FoML/Entropy/Dudley.lean` (MIT).
This version uses mathlib's `Metric.coveringNumber` and `Metric.minimalCover`.
-/

import LeanPool.FormalLearningTheory.Complexity.Rademacher
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Fixed-sample Dudley chaining

This file proves the deterministic, finite-level part of Dudley's chaining argument.  A class on
a sample of size `m` is represented by a finite nonempty set of vectors in the Euclidean sample
space `EuclideanSpace ℝ (Fin m)`.  The covers are mathlib's canonical internal minimal covers.

The main theorem `fixedRademacherComplexity_le_dudleySum` bounds the normalized Rademacher
supremum by a terminal approximation error plus a dyadic sum of square-root log covering
numbers.  It is the abstract fixed-sample input for the empirical-Hamming VC entropy layer:
that later layer only has to bound `coveringCard (dyadicRadius R j) A`; it does not have to
re-prove chaining or a finite maximal inequality.

The theorem is deliberately a finite sum.  No measurability or improper-integral hypothesis is
hidden in the interface, and no assertion about VC entropy is made in this module.
-/

open scoped BigOperators ENNReal NNReal

namespace OTSelector.Probability.Rademacher

open Classical

set_option linter.style.haveILetI false

/-- Euclidean vectors of evaluations on a fixed sample of size `m`. -/
abbrev SampleVector (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The unnormalized signed evaluation of a sample vector. -/
noncomputable def signedSum {m : ℕ} (σ : SignVector m) (v : SampleVector m) : ℝ :=
  ∑ i, boolToSign (σ i) * v i

/-- The expected signed supremum of a finite nonempty set of sample vectors. -/
noncomputable def fixedRademacherSup {m : ℕ} (A : Finset (SampleVector m))
    (hA : A.Nonempty) : ℝ :=
  (1 / (Fintype.card (SignVector m) : ℝ)) *
    ∑ σ : SignVector m, A.sup' hA (signedSum σ)

/-- The normalized fixed-sample Rademacher complexity. -/
noncomputable def fixedRademacherComplexity {m : ℕ} (A : Finset (SampleVector m))
    (hA : A.Nonempty) : ℝ :=
  (m : ℝ)⁻¹ * fixedRademacherSup A hA

/-- The dyadic radii `R / 2^j`, in the nonnegative reals used by mathlib covering numbers. -/
noncomputable def dyadicRadius (R : ℝ≥0) (j : ℕ) : ℝ≥0 := R / 2 ^ j

/-- The finite cardinality of mathlib's internal covering number. -/
noncomputable def coveringCard {m : ℕ} (ε : ℝ≥0) (A : Finset (SampleVector m)) : ℕ :=
  (Metric.coveringNumber ε (A : Set (SampleVector m))).toNat

private lemma coveringNumber_ne_top {m : ℕ} (ε : ℝ≥0)
    (A : Finset (SampleVector m)) :
    Metric.coveringNumber ε (A : Set (SampleVector m)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr A.finite_toSet)
  exact Metric.coveringNumber_le_encard_self (A : Set (SampleVector m))

/-- The canonical finite minimal internal cover supplied by mathlib. -/
noncomputable def coveringFinset {m : ℕ} (ε : ℝ≥0)
    (A : Finset (SampleVector m)) : Finset (SampleVector m) :=
  (Metric.finite_minimalCover
    (X := SampleVector m) (ε := ε) (A := (A : Set (SampleVector m)))).toFinset

theorem coveringFinset_card {m : ℕ} (ε : ℝ≥0) (A : Finset (SampleVector m)) :
    (coveringFinset ε A).card = coveringCard ε A := by
  rw [coveringFinset, coveringCard]
  have hfinite := Metric.finite_minimalCover
    (X := SampleVector m) (ε := ε) (A := (A : Set (SampleVector m)))
  rw [← ENat.natCast_toNat (coveringNumber_ne_top ε A), ← Metric.encard_minimalCover
    (coveringNumber_ne_top ε A), hfinite.encard_eq_coe_toFinset_card]
  exact ENat.natCast_inj.mp rfl

theorem coveringFinset_nonempty {m : ℕ} (ε : ℝ≥0)
    {A : Finset (SampleVector m)} (hA : A.Nonempty) :
    (coveringFinset ε A).Nonempty := by
  change (Metric.finite_minimalCover
    (X := SampleVector m) (ε := ε) (A := (A : Set (SampleVector m)))).toFinset.Nonempty
  rw [Set.Finite.toFinset_nonempty]
  have hcover := Metric.isCover_minimalCover (coveringNumber_ne_top ε A)
  exact hcover.nonempty (by simpa using hA)

private noncomputable def coverApprox {m : ℕ} (ε : ℝ≥0)
    (A : Finset (SampleVector m)) (a : ↑A) : SampleVector m :=
  Classical.choose
    (Metric.isCover_minimalCover (coveringNumber_ne_top ε A) a.property)

private lemma coverApprox_mem {m : ℕ} (ε : ℝ≥0)
    (A : Finset (SampleVector m)) (a : ↑A) :
    coverApprox ε A a ∈ coveringFinset ε A := by
  change coverApprox ε A a ∈
    (Metric.finite_minimalCover
      (X := SampleVector m) (ε := ε) (A := (A : Set (SampleVector m)))).toFinset
  rw [Set.Finite.mem_toFinset]
  exact (Classical.choose_spec
    (Metric.isCover_minimalCover (coveringNumber_ne_top ε A) a.property)).1

private lemma dist_coverApprox_le {m : ℕ} (ε : ℝ≥0)
    (A : Finset (SampleVector m)) (a : ↑A) :
    dist (a : SampleVector m) (coverApprox ε A a) ≤ ε := by
  have h := (Classical.choose_spec
    (Metric.isCover_minimalCover (coveringNumber_ne_top ε A) a.property)).2
  have h' : ENNReal.ofReal (dist (a : SampleVector m) (coverApprox ε A a)) ≤
      ENNReal.ofReal (ε : ℝ) := by
    change edist (a : SampleVector m) (coverApprox ε A a) ≤ ε at h
    simpa only [edist_dist, ENNReal.ofReal_coe_nnreal] using h
  exact (ENNReal.ofReal_le_ofReal_iff ε.coe_nonneg).mp h'

private noncomputable def chainApprox {m : ℕ} (R : ℝ≥0)
    (A : Finset (SampleVector m)) (a : ↑A) : ℕ → SampleVector m
  | 0 => 0
  | j + 1 => coverApprox (dyadicRadius R (j + 1)) A a

@[simp] private lemma chainApprox_zero {m : ℕ} (R : ℝ≥0)
    (A : Finset (SampleVector m)) (a : ↑A) :
    chainApprox R A a 0 = 0 := rfl

@[simp] private lemma chainApprox_succ {m : ℕ} (R : ℝ≥0)
    (A : Finset (SampleVector m)) (a : ↑A) (j : ℕ) :
    chainApprox R A a (j + 1) = coverApprox (dyadicRadius R (j + 1)) A a := rfl

private lemma chainApprox_mem_cover {m : ℕ} (R : ℝ≥0)
    (A : Finset (SampleVector m)) (a : ↑A) (j : ℕ) :
    chainApprox R A a (j + 1) ∈ coveringFinset (dyadicRadius R (j + 1)) A := by
  rw [chainApprox_succ]
  exact coverApprox_mem _ _ _

private lemma dist_chainApprox_succ_le {m : ℕ} (R : ℝ≥0)
    (A : Finset (SampleVector m)) (a : ↑A) (j : ℕ) :
    dist (a : SampleVector m) (chainApprox R A a (j + 1)) ≤ dyadicRadius R (j + 1) := by
  rw [chainApprox_succ]
  exact dist_coverApprox_le _ _ _

private lemma chain_decomposition {m L : ℕ} (R : ℝ≥0)
    (A : Finset (SampleVector m)) (a : ↑A) :
    (a : SampleVector m) =
      (a - chainApprox R A a L) +
        ∑ j : Fin L, (chainApprox R A a (j + 1) - chainApprox R A a j) := by
  induction L with
  | zero => simp
  | succ L ih =>
      nth_rewrite 1 [ih]
      rw [Fin.sum_univ_castSucc]
      simp
      module

private lemma signedSum_le_sqrt_card_mul_norm {m : ℕ} (σ : SignVector m)
    (v : SampleVector m) :
    signedSum σ v ≤ Real.sqrt m * ‖v‖ := by
  let s : SampleVector m := WithLp.toLp 2 fun i ↦ boolToSign (σ i)
  have hsigned : signedSum σ v = @inner ℝ (SampleVector m) _ s v := by
    simp only [signedSum, s, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  rw [hsigned]
  calc
    @inner ℝ (SampleVector m) _ s v ≤ ‖s‖ * ‖v‖ := real_inner_le_norm _ _
    _ = Real.sqrt m * ‖v‖ := by
      congr 1
      rw [EuclideanSpace.norm_eq]
      simp [s, boolToSign_sq]

private lemma signedSum_add {m : ℕ} (σ : SignVector m) (u v : SampleVector m) :
    signedSum σ (u + v) = signedSum σ u + signedSum σ v := by
  simp only [signedSum, WithLp.ofLp_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma signedSum_finset_sum {m : ℕ} {ι : Type*} [Fintype ι]
    (σ : SignVector m) (v : ι → SampleVector m) :
    signedSum σ (∑ j, v j) = ∑ j, signedSum σ (v j) := by
  simp only [signedSum, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Exact Euclidean-variance MGF bound for a fixed Rademacher signed sum. -/
theorem rademacher_mgf_signedSum_le {m : ℕ} (v : SampleVector m) (t : ℝ) :
    (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ σ : SignVector m, Real.exp (t * signedSum σ v) ≤
      Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
  have hstep : ∀ σ : SignVector m,
      Real.exp (t * signedSum σ v) =
        ∏ i : Fin m, Real.exp (t * v i * boolToSign (σ i)) := by
    intro σ
    rw [signedSum, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    ring
  simp_rw [hstep]
  rw [show ∑ σ : SignVector m, ∏ i : Fin m, Real.exp (t * v i * boolToSign (σ i)) =
      ∏ i : Fin m, ∑ b : Bool, Real.exp (t * v i * boolToSign b) from by
    rw [← Fintype.piFinset_univ (β := fun _ : Fin m ↦ Bool)]
    exact Finset.sum_prod_piFinset Finset.univ
      (fun (i : Fin m) (b : Bool) ↦ Real.exp (t * v i * boolToSign b))]
  have hcard : (Fintype.card (SignVector m) : ℝ) = (2 : ℝ) ^ m := by simp
  have hinv : (1 : ℝ) / (Fintype.card (SignVector m) : ℝ) = (1 / 2 : ℝ) ^ m := by
    rw [hcard, one_div, one_div, inv_pow]
  rw [hinv]
  have hprod_const : ((1 / 2 : ℝ) ^ m : ℝ) = ∏ _i : Fin m, (1 / 2 : ℝ) := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprod_const, ← Finset.prod_mul_distrib]
  have hfactor : ∀ i : Fin m,
      (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * v i * boolToSign b) ≤
        Real.exp ((t * v i) ^ 2 / 2) := by
    intro i
    have hsum : ∑ b : Bool, Real.exp (t * v i * boolToSign b) =
        Real.exp (t * v i) + Real.exp (-(t * v i)) := by
      simp only [Fintype.sum_bool, boolToSign, ↓reduceIte, Bool.false_eq_true]
      congr 1 <;> ring_nf
    rw [hsum]
    rw [show (1 / 2 : ℝ) * (Real.exp (t * v i) + Real.exp (-(t * v i))) =
      Real.cosh (t * v i) by rw [Real.cosh_eq]; ring]
    exact cosh_le_exp_sq_half _
  have hnonneg : ∀ i ∈ Finset.univ (α := Fin m),
      0 ≤ (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * v i * boolToSign b) := by
    intro i _
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun b _ ↦ (Real.exp_pos _).le)
  calc
    ∏ i : Fin m, (1 / 2 : ℝ) * ∑ b : Bool, Real.exp (t * v i * boolToSign b)
        ≤ ∏ i : Fin m, Real.exp ((t * v i) ^ 2 / 2) :=
          Finset.prod_le_prod hnonneg fun i _ ↦ hfactor i
    _ = Real.exp (∑ i : Fin m, (t * v i) ^ 2 / 2) :=
      (Real.exp_sum Finset.univ _).symm
    _ = Real.exp (t ^ 2 * ‖v‖ ^ 2 / 2) := by
      congr 1
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        (∑ i : Fin m, (t * v i) ^ 2 / 2) = ∑ i : Fin m, t ^ 2 * v i ^ 2 / 2 := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = t ^ 2 * (∑ i : Fin m, v i ^ 2) / 2 := by
          rw [← Finset.sum_div, ← Finset.mul_sum]

/-- Massart's finite maximal inequality in the Euclidean metric of the fixed sample. -/
theorem fixedRademacherSup_le_massart {m : ℕ} (hm : 0 < m)
    {A : Finset (SampleVector m)} (hA : A.Nonempty) {R : ℝ} (hR : 0 < R)
    (hA_norm : ∀ v ∈ A, ‖v‖ ≤ R) :
    fixedRademacherSup A hA ≤ R * Real.sqrt (2 * Real.log A.card) := by
  let N := A.card
  have hN : 0 < N := hA.card_pos
  have hcard_A : Fintype.card {v // v ∈ A} = N := Fintype.card_coe A
  let e : {v // v ∈ A} ≃ Fin N := hcard_A ▸ Fintype.equivFin _
  let Z : Fin N → SignVector m → ℝ := fun j σ ↦ signedSum σ (e.symm j).val
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hsup : ∀ σ : SignVector m,
      A.sup' hA (signedSum σ) =
        Finset.univ.sup' Finset.univ_nonempty (fun j ↦ Z j σ) := by
    intro σ
    apply le_antisymm
    · rw [Finset.sup'_le_iff]
      intro v hv
      exact Finset.le_sup'_of_le (f := fun j ↦ Z j σ) (Finset.mem_univ (e ⟨v, hv⟩)) (by
        change signedSum σ v ≤ signedSum σ (e.symm (e ⟨v, hv⟩)).val
        simp)
    · rw [Finset.sup'_le_iff]
      intro j _
      exact Finset.le_sup' (signedSum σ) (e.symm j).property
  have hmgf : ∀ j t, 0 ≤ t →
      (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ σ : SignVector m, Real.exp (t * Z j σ) ≤
        Real.exp (t ^ 2 * R ^ 2 / 2) := by
    intro j t _
    calc
      (1 / (Fintype.card (SignVector m) : ℝ)) *
          ∑ σ : SignVector m, Real.exp (t * Z j σ) ≤
          Real.exp (t ^ 2 * ‖(e.symm j).val‖ ^ 2 / 2) := by
        simpa [Z] using rademacher_mgf_signedSum_le (e.symm j).val t
      _ ≤ Real.exp (t ^ 2 * R ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have hnorm := hA_norm (e.symm j).val (e.symm j).property
        have hsquare : ‖(e.symm j).val‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (e.symm j).val]
        gcongr
  have hmassart := finite_massart_lemma hm hN Z R hR hmgf
  simpa only [fixedRademacherSup, hsup, N] using hmassart

private lemma chainApprox_error_le {m : ℕ} {R : ℝ≥0}
    (A : Finset (SampleVector m)) (hA_norm : ∀ a ∈ A, ‖a‖ ≤ R)
    (a : ↑A) (j : ℕ) :
    ‖(a : SampleVector m) - chainApprox R A a j‖ ≤ dyadicRadius R j := by
  cases j with
  | zero => simpa [dyadicRadius] using hA_norm a a.property
  | succ j =>
      simpa [dist_eq_norm] using dist_chainApprox_succ_le R A a j

private lemma chainApprox_increment_norm_le {m : ℕ} {R : ℝ≥0}
    (A : Finset (SampleVector m)) (hA_norm : ∀ a ∈ A, ‖a‖ ≤ R)
    (a : ↑A) (j : ℕ) :
    ‖chainApprox R A a (j + 1) - chainApprox R A a j‖ ≤
      dyadicRadius R (j + 1) + dyadicRadius R j := by
  calc
    ‖chainApprox R A a (j + 1) - chainApprox R A a j‖ =
        ‖(chainApprox R A a (j + 1) - a) + (a - chainApprox R A a j)‖ := by
      congr 1
      module
    _ ≤
        ‖chainApprox R A a (j + 1) - a‖ + ‖a - chainApprox R A a j‖ := by
      exact norm_add_le _ _
    _ ≤ dyadicRadius R (j + 1) + dyadicRadius R j := by
      apply add_le_add
      · simpa [norm_sub_rev] using chainApprox_error_le A hA_norm a (j + 1)
      · exact chainApprox_error_le A hA_norm a j

private noncomputable def incrementFinset {m L : ℕ} (R : ℝ≥0)
    (A : Finset (SampleVector m)) (j : Fin L) : Finset (SampleVector m) :=
  Finset.univ.image fun a : ↑A ↦
    chainApprox R A a (j + 1) - chainApprox R A a j

private lemma incrementFinset_nonempty {m L : ℕ} (R : ℝ≥0)
    {A : Finset (SampleVector m)} (hA : A.Nonempty) (j : Fin L) :
    (incrementFinset R A j).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨chainApprox R A ⟨a, ha⟩ (j + 1) - chainApprox R A ⟨a, ha⟩ j, ?_⟩
  rw [incrementFinset, Finset.mem_image]
  exact ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩

private lemma incrementFinset_norm_le {m L : ℕ} {R : ℝ≥0}
    (A : Finset (SampleVector m)) (hA_norm : ∀ a ∈ A, ‖a‖ ≤ R)
    (j : Fin L) (v : SampleVector m) (hv : v ∈ incrementFinset R A j) :
    ‖v‖ ≤ dyadicRadius R (j + 1) + dyadicRadius R j := by
  rw [incrementFinset, Finset.mem_image] at hv
  obtain ⟨a, _, rfl⟩ := hv
  exact chainApprox_increment_norm_le A hA_norm a j

private lemma incrementFinset_card_le_coveringCard_mul {m L : ℕ} (R : ℝ≥0)
    {A : Finset (SampleVector m)} (hA : A.Nonempty) (j : Fin L) :
    (incrementFinset R A j).card ≤
      coveringCard (dyadicRadius R (j + 1)) A * coveringCard (dyadicRadius R j) A := by
  let nextCover := coveringFinset (dyadicRadius R (j + 1)) A
  let currCover := coveringFinset (dyadicRadius R j) A
  by_cases hj : (j : ℕ) = 0
  · have hsubset : incrementFinset R A j ⊆ nextCover := by
      intro v hv
      rw [incrementFinset, Finset.mem_image] at hv
      obtain ⟨a, _, rfl⟩ := hv
      simpa [nextCover, hj] using chainApprox_mem_cover R A a 0
    have hnext : (incrementFinset R A j).card ≤ nextCover.card :=
      Finset.card_le_card hsubset
    have hcurr_pos : 0 < currCover.card :=
      (coveringFinset_nonempty (dyadicRadius R j) hA).card_pos
    calc
      (incrementFinset R A j).card ≤ nextCover.card := hnext
      _ = nextCover.card * 1 := by simp
      _ ≤ nextCover.card * currCover.card := by
        exact Nat.mul_le_mul_left _ hcurr_pos
      _ = coveringCard (dyadicRadius R (j + 1)) A *
          coveringCard (dyadicRadius R j) A := by
        simp [nextCover, currCover, coveringFinset_card]
  · let pairs : Finset (SampleVector m × SampleVector m) :=
      Finset.univ.image fun a : ↑A ↦
        (chainApprox R A a (j + 1), chainApprox R A a j)
    have hpairs_subset : pairs ⊆ nextCover.product currCover := by
      intro p hp
      change p ∈ Finset.univ.image (fun a : ↑A ↦
        (chainApprox R A a (j + 1), chainApprox R A a j)) at hp
      rw [Finset.mem_image] at hp
      obtain ⟨a, _, rfl⟩ := hp
      apply Finset.mk_mem_product
      · simpa [nextCover] using chainApprox_mem_cover R A a j
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
        simpa [currCover, hk] using chainApprox_mem_cover R A a k
    have hincrement_image : incrementFinset R A j = pairs.image (fun p ↦ p.1 - p.2) := by
      ext v
      simp only [incrementFinset, pairs, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(chainApprox R A a (j + 1), chainApprox R A a j), ⟨a, rfl⟩, rfl⟩
      · rintro ⟨p, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    calc
      (incrementFinset R A j).card = (pairs.image (fun p ↦ p.1 - p.2)).card := by
        rw [hincrement_image]
      _ ≤ pairs.card := Finset.card_image_le
      _ ≤ (nextCover.product currCover).card := Finset.card_le_card hpairs_subset
      _ = nextCover.card * currCover.card := Finset.card_product _ _
      _ = coveringCard (dyadicRadius R (j + 1)) A *
          coveringCard (dyadicRadius R j) A := by
        simp [nextCover, currCover, coveringFinset_card]

private lemma dyadicRadius_pos {R : ℝ≥0} (hR : 0 < R) (j : ℕ) :
    0 < (dyadicRadius R j : ℝ) := by
  rw [dyadicRadius]
  positivity

private noncomputable def incrementRademacherSup {m L : ℕ} (R : ℝ≥0)
    (A : Finset (SampleVector m)) (hA : A.Nonempty) (j : Fin L) : ℝ :=
  fixedRademacherSup (incrementFinset R A j) (incrementFinset_nonempty R hA j)

private lemma incrementRademacherSup_le {m L : ℕ} (hm : 0 < m)
    {R : ℝ≥0} (hR : 0 < R) {A : Finset (SampleVector m)} (hA : A.Nonempty)
    (hA_norm : ∀ a ∈ A, ‖a‖ ≤ R) (j : Fin L) :
    incrementRademacherSup R A hA j ≤
      ((dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j) *
        Real.sqrt (2 * Real.log
          (coveringCard (dyadicRadius R (j + 1)) A *
            coveringCard (dyadicRadius R j) A)) := by
  let B := incrementFinset R A j
  have hB : B.Nonempty := incrementFinset_nonempty R hA j
  let radius : ℝ := (dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith [dyadicRadius_pos hR (j + 1), dyadicRadius_pos hR j]
  have hmassart : fixedRademacherSup B hB ≤
      radius * Real.sqrt (2 * Real.log B.card) := by
    apply fixedRademacherSup_le_massart hm hB hradius
    intro v hv
    simpa [B, radius] using incrementFinset_norm_le A hA_norm j v hv
  calc
    incrementRademacherSup R A hA j = fixedRademacherSup B hB := by
      rfl
    _ ≤ radius * Real.sqrt (2 * Real.log B.card) := hmassart
    _ ≤ radius * Real.sqrt (2 * Real.log
        (coveringCard (dyadicRadius R (j + 1)) A *
          coveringCard (dyadicRadius R j) A)) := by
      apply mul_le_mul_of_nonneg_left _ hradius.le
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.log_le_log
      · exact_mod_cast hB.card_pos
      · exact_mod_cast incrementFinset_card_le_coveringCard_mul R hA j

private lemma fixedRademacherSup_le_terminal_add_increments {m L : ℕ}
    {R : ℝ≥0} {A : Finset (SampleVector m)} (hA : A.Nonempty)
    (hA_norm : ∀ a ∈ A, ‖a‖ ≤ R) :
    fixedRademacherSup A hA ≤
      Real.sqrt m * dyadicRadius R L + ∑ j : Fin L, incrementRademacherSup R A hA j := by
  have hpoint : ∀ σ : SignVector m,
      A.sup' hA (signedSum σ) ≤
        Real.sqrt m * dyadicRadius R L +
          ∑ j : Fin L,
            (incrementFinset R A j).sup' (incrementFinset_nonempty R hA j)
              (signedSum σ) := by
    intro σ
    rw [Finset.sup'_le_iff]
    intro a ha
    let a' : ↑A := ⟨a, ha⟩
    have hsigned_decomp : signedSum σ (a : SampleVector m) =
        signedSum σ (a' - chainApprox R A a' L) +
          ∑ j : Fin L,
            signedSum σ (chainApprox R A a' (j + 1) - chainApprox R A a' j) := by
      calc
        signedSum σ (a : SampleVector m) = signedSum σ
            ((a' - chainApprox R A a' L) +
              ∑ j : Fin L,
                (chainApprox R A a' (j + 1) - chainApprox R A a' j)) := by
          exact congrArg (signedSum σ) (chain_decomposition (L := L) R A a')
        _ = signedSum σ (a' - chainApprox R A a' L) +
            ∑ j : Fin L,
              signedSum σ (chainApprox R A a' (j + 1) - chainApprox R A a' j) := by
          rw [signedSum_add, signedSum_finset_sum]
    rw [hsigned_decomp]
    apply add_le_add
    · calc
        signedSum σ (a' - chainApprox R A a' L) ≤
            Real.sqrt m * ‖a' - chainApprox R A a' L‖ :=
          signedSum_le_sqrt_card_mul_norm σ _
        _ ≤ Real.sqrt m * dyadicRadius R L := by
          gcongr
          exact chainApprox_error_le A hA_norm a' L
    · apply Finset.sum_le_sum
      intro j _
      exact Finset.le_sup' (signedSum σ) (by
        rw [incrementFinset, Finset.mem_image]
        exact ⟨a', Finset.mem_univ _, rfl⟩)
  unfold fixedRademacherSup incrementRademacherSup
  calc
    (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ σ : SignVector m, A.sup' hA (signedSum σ) ≤
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ σ : SignVector m,
          (Real.sqrt m * dyadicRadius R L +
            ∑ j : Fin L,
              (incrementFinset R A j).sup' (incrementFinset_nonempty R hA j)
                (signedSum σ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun σ _ ↦ hpoint σ
      · positivity
    _ = Real.sqrt m * dyadicRadius R L +
        ∑ j : Fin L,
          (1 / (Fintype.card (SignVector m) : ℝ)) *
            ∑ σ : SignVector m,
              (incrementFinset R A j).sup' (incrementFinset_nonempty R hA j)
                (signedSum σ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.sum_comm, mul_add, Finset.mul_sum]
      have hcard : (Fintype.card (SignVector m) : ℝ) ≠ 0 := by positivity
      rw [← mul_assoc, show (1 / (Fintype.card (SignVector m) : ℝ)) *
          Fintype.card (SignVector m) = 1 by field_simp, one_mul]

/--
Finite-level fixed-sample Dudley chaining using mathlib's internal covering numbers.

The next layer supplies entropy estimates for the two `coveringCard` factors.  In particular,
an empirical-Hamming/VC bound can be substituted directly into this theorem; no additional
Rademacher maximal inequality or chaining construction is required.
-/
theorem fixedRademacherComplexity_le_dudleySum {m L : ℕ} (hm : 0 < m)
    {R : ℝ≥0} (hR : 0 < R) {A : Finset (SampleVector m)} (hA : A.Nonempty)
    (hA_norm : ∀ a ∈ A, ‖a‖ ≤ R) :
    fixedRademacherComplexity A hA ≤
      (m : ℝ)⁻¹ *
        (Real.sqrt m * dyadicRadius R L +
          ∑ j : Fin L,
            ((dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j) *
              Real.sqrt (2 * Real.log
                (coveringCard (dyadicRadius R (j + 1)) A *
                  coveringCard (dyadicRadius R j) A))) := by
  unfold fixedRademacherComplexity
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    fixedRademacherSup A hA ≤
        Real.sqrt m * dyadicRadius R L +
          ∑ j : Fin L, incrementRademacherSup R A hA j :=
      fixedRademacherSup_le_terminal_add_increments hA hA_norm
    _ ≤ Real.sqrt m * dyadicRadius R L +
        ∑ j : Fin L,
          ((dyadicRadius R (j + 1) : ℝ) + dyadicRadius R j) *
            Real.sqrt (2 * Real.log
              (coveringCard (dyadicRadius R (j + 1)) A *
                coveringCard (dyadicRadius R j) A)) := by
      exact add_le_add (le_refl _) <|
        Finset.sum_le_sum fun j _ ↦ incrementRademacherSup_le hm hR hA hA_norm j

end OTSelector.Probability.Rademacher
