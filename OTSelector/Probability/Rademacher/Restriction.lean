/-
Copyright (c) 2026 Yuwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuwei Lu
-/

import OTSelector.Probability.Rademacher.VCMaximal
import LeanPool.FormalLearningTheory.Complexity.VCDimension

/-!
# Finite restrictions of an arbitrary VC class

An infinite concept class realizes only finitely many Boolean patterns on a fixed finite sample.
This file packages that finite family and proves that its mathlib `Finset.boolVCDim` is bounded by
the learning-theoretic `VCDim` of the original class.

Repeated sample coordinates require care: a shattered coordinate set forces evaluation to be
injective on that set.  The proof establishes this fact explicitly before transporting the
shattered set back to the ambient domain.
-/

namespace OTSelector.Probability.Rademacher

open Classical

universe u

/-! ## Absolute fixed-sample Rademacher suprema -/

/-- Flip every Rademacher sign. -/
def flipSigns {m : ℕ} (sigma : SignVector m) : SignVector m := fun i ↦ !sigma i

@[simp]
theorem flipSigns_apply {m : ℕ} (sigma : SignVector m) (i : Fin m) :
    flipSigns sigma i = !sigma i := rfl

theorem flipSigns_involutive {m : ℕ} : Function.Involutive (@flipSigns m) := by
  intro sigma
  funext i
  simp [flipSigns]

/-- Flipping every sign is a permutation of the finite sign cube. -/
noncomputable def flipSignsEquiv (m : ℕ) : SignVector m ≃ SignVector m :=
  Equiv.ofBijective flipSigns flipSigns_involutive.bijective

@[simp]
theorem boolToSign_not (b : Bool) : boolToSign (!b) = -boolToSign b := by
  cases b <;> simp [boolToSign]

/-- Global sign reversal negates every signed evaluation. -/
theorem signedSum_flipSigns {m : ℕ} (sigma : SignVector m) (v : SampleVector m) :
    signedSum (flipSigns sigma) v = -signedSum sigma v := by
  rw [signedSum, signedSum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [flipSigns_apply, boolToSign_not]
  ring

/-- The expected unnormalized absolute signed supremum of a finite vector family. -/
noncomputable def fixedRademacherAbsSup {m : ℕ} (A : Finset (SampleVector m))
    (hA : A.Nonempty) : ℝ :=
  (1 / (Fintype.card (SignVector m) : ℝ)) *
    ∑ sigma : SignVector m, A.sup' hA (fun v ↦ |signedSum sigma v|)

/-- The normalized absolute fixed-sample Rademacher complexity. -/
noncomputable def fixedRademacherAbsComplexity {m : ℕ} (A : Finset (SampleVector m))
    (hA : A.Nonempty) : ℝ :=
  (m : ℝ)⁻¹ * fixedRademacherAbsSup A hA

/-- If the vector family contains zero, its absolute signed supremum costs at most a factor two
over the one-sided signed supremum. -/
theorem fixedRademacherAbsSup_le_two_mul {m : ℕ} (A : Finset (SampleVector m))
    (hA : A.Nonempty) (hzero : (0 : SampleVector m) ∈ A) :
    fixedRademacherAbsSup A hA ≤ 2 * fixedRademacherSup A hA := by
  have hpoint : ∀ sigma : SignVector m,
      A.sup' hA (fun v ↦ |signedSum sigma v|) ≤
        A.sup' hA (signedSum sigma) + A.sup' hA (fun v ↦ -signedSum sigma v) := by
    intro sigma
    have hpos : 0 ≤ A.sup' hA (signedSum sigma) := by
      calc
        0 = signedSum sigma 0 := by simp [signedSum]
        _ ≤ A.sup' hA (signedSum sigma) := Finset.le_sup' (signedSum sigma) hzero
    have hneg : 0 ≤ A.sup' hA (fun v ↦ -signedSum sigma v) := by
      calc
        0 = -signedSum sigma 0 := by simp [signedSum]
        _ ≤ A.sup' hA (fun v ↦ -signedSum sigma v) :=
          Finset.le_sup' (fun v ↦ -signedSum sigma v) hzero
    apply Finset.sup'_le hA
    intro v hv
    have hvpos : signedSum sigma v ≤ A.sup' hA (signedSum sigma) :=
      Finset.le_sup' (signedSum sigma) hv
    have hvneg : -signedSum sigma v ≤ A.sup' hA (fun w ↦ -signedSum sigma w) :=
      Finset.le_sup' (fun w ↦ -signedSum sigma w) hv
    rw [abs_le]
    constructor <;> linarith
  have hneg_point : ∀ sigma : SignVector m,
      A.sup' hA (fun v ↦ -signedSum sigma v) =
        A.sup' hA (signedSum (flipSigns sigma)) := by
    intro sigma
    apply congrArg (A.sup' hA)
    funext v
    exact (signedSum_flipSigns sigma v).symm
  have hneg_sum :
      ∑ sigma : SignVector m, A.sup' hA (fun v ↦ -signedSum sigma v) =
        ∑ sigma : SignVector m, A.sup' hA (signedSum sigma) := by
    simp_rw [hneg_point]
    simpa [flipSignsEquiv] using Equiv.sum_comp (flipSignsEquiv m)
      (fun sigma ↦ A.sup' hA (signedSum sigma))
  rw [fixedRademacherAbsSup, fixedRademacherSup]
  calc
    (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sigma : SignVector m, A.sup' hA (fun v ↦ |signedSum sigma v|) ≤
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sigma : SignVector m,
          (A.sup' hA (signedSum sigma) +
            A.sup' hA (fun v ↦ -signedSum sigma v)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun sigma _ ↦ hpoint sigma
      · positivity
    _ = 2 * ((1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sigma : SignVector m, A.sup' hA (signedSum sigma)) := by
      rw [Finset.sum_add_distrib, hneg_sum]
      ring

/-- Normalization preserves the factor-two comparison. -/
theorem fixedRademacherAbsComplexity_le_two_mul {m : ℕ}
    (A : Finset (SampleVector m)) (hA : A.Nonempty) (hzero : (0 : SampleVector m) ∈ A) :
    fixedRademacherAbsComplexity A hA ≤ 2 * fixedRademacherComplexity A hA := by
  rw [fixedRademacherAbsComplexity, fixedRademacherComplexity]
  calc
    (m : ℝ)⁻¹ * fixedRademacherAbsSup A hA ≤
        (m : ℝ)⁻¹ * (2 * fixedRademacherSup A hA) := by
      apply mul_le_mul_of_nonneg_left (fixedRademacherAbsSup_le_two_mul A hA hzero)
      positivity
    _ = 2 * ((m : ℝ)⁻¹ * fixedRademacherSup A hA) := by ring

/-- The identically false Boolean pattern. -/
def zeroPattern (m : ℕ) : Fin m → Bool := fun _ ↦ false

@[simp]
theorem indicatorVector_zeroPattern (m : ℕ) : indicatorVector (zeroPattern m) = 0 := by
  ext i
  simp [zeroPattern, indicatorVector_apply]

/-- A zero Boolean pattern supplies the zero vector required by the absolute comparison. -/
theorem zero_mem_indicatorVectors {m : ℕ} (H : Finset (Fin m → Bool))
    (hzero : zeroPattern m ∈ H) : (0 : SampleVector m) ∈ indicatorVectors H := by
  rw [mem_indicatorVectors_iff]
  exact ⟨zeroPattern m, hzero, indicatorVector_zeroPattern m⟩

/-- Log-free absolute fixed-sample VC maximal inequality. -/
theorem fixedRademacherAbsComplexity_indicator_le {m v : ℕ} (hm : 0 < m) (hv : 0 < v)
    (H : Finset (Fin m → Bool)) (hH : H.Nonempty) (hzero : zeroPattern m ∈ H)
    (hVC : H.boolVCDim ≤ v) :
    fixedRademacherAbsComplexity (indicatorVectors H) (indicatorVectors_nonempty hH) ≤
      2 * (1 + 392 * (v : ℝ)) / Real.sqrt m := by
  calc
    fixedRademacherAbsComplexity (indicatorVectors H) (indicatorVectors_nonempty hH) ≤
        2 * fixedRademacherComplexity (indicatorVectors H)
          (indicatorVectors_nonempty hH) :=
      fixedRademacherAbsComplexity_le_two_mul _ _ (zero_mem_indicatorVectors H hzero)
    _ ≤ 2 * ((1 + 392 * (v : ℝ)) / Real.sqrt m) := by
      gcongr
      exact fixedRademacherComplexity_indicator_le hm hv H hH hVC
    _ = 2 * (1 + 392 * (v : ℝ)) / Real.sqrt m := by ring

/-- Distinct Boolean patterns realized by an arbitrary concept class on a finite sample. -/
noncomputable def realizedPatterns {Ω : Type u} (C : ConceptClass Ω Bool)
    {m : ℕ} (z : Fin m → Ω) : Finset (Fin m → Bool) :=
  (Set.toFinite {p : Fin m → Bool | ∃ h ∈ C, ∀ i, p i = h (z i)}).toFinset

@[simp]
theorem mem_realizedPatterns_iff {Ω : Type u} (C : ConceptClass Ω Bool)
    {m : ℕ} (z : Fin m → Ω) (p : Fin m → Bool) :
    p ∈ realizedPatterns C z ↔ ∃ h ∈ C, ∀ i, p i = h (z i) := by
  simp [realizedPatterns]

/-- A nonempty concept class realizes a nonempty pattern family on every finite sample. -/
theorem realizedPatterns_nonempty {Ω : Type u} {C : ConceptClass Ω Bool}
    {m : ℕ} (z : Fin m → Ω) (hC : C.Nonempty) : (realizedPatterns C z).Nonempty := by
  obtain ⟨h, hh⟩ := hC
  refine ⟨fun i ↦ h (z i), (mem_realizedPatterns_iff C z _).2 ?_⟩
  exact ⟨h, hh, fun _ ↦ rfl⟩

/-- If a set of sample coordinates is shattered by the realized patterns, then the sample map is
injective on those coordinates. -/
theorem injOn_of_realizedPatterns_shatters {Ω : Type u} (C : ConceptClass Ω Bool)
    {m : ℕ} (z : Fin m → Ω) (T : Finset (Fin m))
    (hT : (boolFamilyToFinsetFamily (realizedPatterns C z)).Shatters T) :
    Set.InjOn z (T : Set (Fin m)) := by
  intro i hi j hj hij
  by_contra hijne
  obtain ⟨A, hA, htrace⟩ := hT.exists_inter_eq_singleton hi
  rw [boolFamilyToFinsetFamily, Finset.mem_image] at hA
  obtain ⟨p, hp, rfl⟩ := hA
  have hpi : p i = true := by
    have hiTrace := Finset.ext_iff.mp htrace i
    have hmem : i ∈ T ∧ p i = true := by simpa using hiTrace
    exact hmem.2
  have hpj : p j = false := by
    have hjTrace := Finset.ext_iff.mp htrace j
    have hji : j ≠ i := fun hji ↦ hijne hji.symm
    have hmem : j ∈ T → p j = false := by simpa [hji] using hjTrace
    exact hmem hj
  obtain ⟨h, hhC, hpval⟩ := (mem_realizedPatterns_iff C z p).1 hp
  have hpij : p i = p j := by
    calc
      p i = h (z i) := hpval i
      _ = h (z j) := congrArg h hij
      _ = p j := (hpval j).symm
  rw [hpi, hpj] at hpij
  contradiction

/-- Restriction to a finite sample cannot increase VC dimension, even when the sample has
repeated coordinates. -/
theorem realizedPatterns_boolVCDim_le {Ω : Type u} (C : ConceptClass Ω Bool)
    {m v : ℕ} (z : Fin m → Ω) (hVC : VCDim Ω C ≤ (v : WithTop ℕ)) :
    (realizedPatterns C z).boolVCDim ≤ v := by
  unfold Finset.boolVCDim Finset.vcDim
  apply Finset.sup_le
  intro T hTmem
  have hT : (boolFamilyToFinsetFamily (realizedPatterns C z)).Shatters T :=
    Finset.mem_shatterer.1 hTmem
  have hzinj : Set.InjOn z (T : Set (Fin m)) :=
    injOn_of_realizedPatterns_shatters C z T hT
  let e : T ↪ Ω :=
    ⟨fun i ↦ z i, fun i j hij ↦ Subtype.ext (hzinj i.property j.property hij)⟩
  let S : Finset Ω := (Finset.univ : Finset T).map e
  have hzS : ∀ i : T, z i ∈ S := by
    intro i
    exact Finset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩
  have hScard : S.card = T.card := by
    simp [S]
  have hS : Shatters Ω C S := by
    intro f
    let g : T → Bool := fun i ↦ f ⟨z i, hzS i⟩
    let U : Finset (Fin m) := T.filter fun i ↦
      if hi : i ∈ T then g ⟨i, hi⟩ = true else False
    have hUT : U ⊆ T := Finset.filter_subset _ _
    obtain ⟨A, hA, htrace⟩ := hT hUT
    rw [boolFamilyToFinsetFamily, Finset.mem_image] at hA
    obtain ⟨p, hpPatterns, rfl⟩ := hA
    obtain ⟨h, hhC, hpval⟩ := (mem_realizedPatterns_iff C z p).1 hpPatterns
    refine ⟨h, hhC, ?_⟩
    intro x
    obtain ⟨i, hi, hix⟩ := Finset.mem_map.1 x.property
    have hpg : p i = g i := by
      have hiTrace := Finset.ext_iff.mp htrace i
      have hiT : (i : Fin m) ∈ T := i.property
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
        U, hiT, true_and] at hiTrace
      cases hp : p i <;> cases hg : g i <;> simp_all
    have hx : x = ⟨z i, hzS i⟩ := by
      apply Subtype.ext
      change (x : Ω) = e i
      exact hix.symm
    subst x
    simpa [g] using (hpval i).symm.trans hpg
  have hdim : (S.card : WithTop ℕ) ≤ VCDim Ω C := by
    exact le_iSup₂
      (f := fun (S : Finset Ω) (_ : Shatters Ω C S) ↦ (S.card : WithTop ℕ)) S hS
  have hcard : (T.card : WithTop ℕ) ≤ (v : WithTop ℕ) := by
    rw [← hScard]
    exact hdim.trans hVC
  exact WithTop.coe_le_coe.mp hcard

/-- Indicator-vector form of an arbitrary class restricted to one finite sample. -/
noncomputable def realizedIndicatorVectors {Ω : Type u} (C : ConceptClass Ω Bool)
    {m : ℕ} (z : Fin m → Ω) : Finset (SampleVector m) :=
  indicatorVectors (realizedPatterns C z)

/-- An actually realized all-false restriction provides the zero pattern needed by the absolute
maximal inequality. -/
theorem zeroPattern_mem_realizedPatterns {Ω : Type u} {C : ConceptClass Ω Bool}
    {m : ℕ} (z : Fin m → Ω) (hzero : ∃ h ∈ C, ∀ i, h (z i) = false) :
    zeroPattern m ∈ realizedPatterns C z := by
  rw [mem_realizedPatterns_iff]
  obtain ⟨h, hhC, hh⟩ := hzero
  exact ⟨h, hhC, fun i ↦ by simp [zeroPattern, hh i]⟩

/-- Infinite-class restriction form of the log-free absolute VC maximal inequality. -/
theorem fixedRademacherAbsComplexity_realizedPatterns_le {Ω : Type u} {m v : ℕ}
    (hm : 0 < m) (hv : 0 < v) (C : ConceptClass Ω Bool) (z : Fin m → Ω)
    (hC : C.Nonempty) (hVC : VCDim Ω C ≤ (v : WithTop ℕ))
    (hzero : ∃ h ∈ C, ∀ i, h (z i) = false) :
    fixedRademacherAbsComplexity (realizedIndicatorVectors C z)
        (indicatorVectors_nonempty (realizedPatterns_nonempty z hC)) ≤
      2 * (1 + 392 * (v : ℝ)) / Real.sqrt m := by
  apply fixedRademacherAbsComplexity_indicator_le hm hv
  · exact realizedPatterns_nonempty z hC
  · exact zeroPattern_mem_realizedPatterns z hzero
  · exact realizedPatterns_boolVCDim_le C z hVC

end OTSelector.Probability.Rademacher
