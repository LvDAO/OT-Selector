/-
Copyright (c) 2026 Yuwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuwei Lu
-/

import OTSelector.Feedback.VCMaximal

/-!
# Global double-sample VC maximal bounds

For a fixed paired sample, pairwise swapping turns every empirical gap into the difference of two
Rademacher signed indicator sums.  The absolute fixed-sample VC bound controls their average, and
a finite Markov argument controls the fraction of bad sign assignments.  The existing
exchangeability and analytic-measurability infrastructure then gives an actual double-sample
probability bound for the source and target cut classes.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace OTSelector.RelativeVC

open Classical
open OTSelector.Probability.Rademacher

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Absolute signed supremum of one finite disagreement restriction at one sign vector. -/
noncomputable def restrictionSignedAbsSup {m : ℕ}
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (z : Fin m → Ω)
    (hC : C.Nonempty) (sigma : SignVector m) : ℝ :=
  (indicatorVectors (restrictionPatterns C c m z)).sup'
    (indicatorVectors_nonempty (restrictionPatterns_nonempty c z hC))
    (fun v ↦ |signedSum sigma v|)

theorem restrictionSignedAbsSup_nonneg {m : ℕ}
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (z : Fin m → Ω)
    (hC : C.Nonempty) (sigma : SignVector m) :
    0 ≤ restrictionSignedAbsSup C c z hC sigma := by
  obtain ⟨v, hv⟩ := indicatorVectors_nonempty (restrictionPatterns_nonempty c z hC)
  exact (abs_nonneg (signedSum sigma v)).trans
    (Finset.le_sup' (fun w ↦ |signedSum sigma w|) hv)

private theorem sum_restrictionSignedAbsSup_eq_card_mul {m : ℕ}
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (z : Fin m → Ω)
    (hC : C.Nonempty) :
    (∑ sigma : SignVector m, restrictionSignedAbsSup C c z hC sigma) =
      (Fintype.card (SignVector m) : ℝ) *
        fixedRademacherAbsSup (indicatorVectors (restrictionPatterns C c m z))
          (indicatorVectors_nonempty (restrictionPatterns_nonempty c z hC)) := by
  rw [fixedRademacherAbsSup]
  simp only [restrictionSignedAbsSup]
  have hcard : (Fintype.card (SignVector m) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Raw sign-sum form of the absolute VC maximal inequality. -/
theorem sum_restrictionSignedAbsSup_le {m v : ℕ} (hm : 0 < m) (hv : 0 < v)
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (z : Fin m → Ω)
    (hC : C.Nonempty) (hVC : VCDim Ω C ≤ (v : WithTop ℕ))
    (hzero : zeroPattern m ∈ restrictionPatterns C c m z) :
    (∑ sigma : SignVector m, restrictionSignedAbsSup C c z hC sigma) ≤
      (Fintype.card (SignVector m) : ℝ) *
        (2 * (1 + 392 * (v : ℝ)) * Real.sqrt m) := by
  let A := indicatorVectors (restrictionPatterns C c m z)
  let hA : A.Nonempty := indicatorVectors_nonempty (restrictionPatterns_nonempty c z hC)
  have hcomplexity : fixedRademacherAbsComplexity A hA ≤
      2 * (1 + 392 * (v : ℝ)) / Real.sqrt m := by
    simpa [A, hA] using fixedRademacherAbsComplexity_restrictionPatterns_le
      hm hv C c z hC hVC hzero
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hscale : fixedRademacherAbsSup A hA =
      (m : ℝ) * fixedRademacherAbsComplexity A hA := by
    rw [fixedRademacherAbsComplexity]
    field_simp
  have habs : fixedRademacherAbsSup A hA ≤
      2 * (1 + 392 * (v : ℝ)) * Real.sqrt m := by
    rw [hscale]
    calc
      (m : ℝ) * fixedRademacherAbsComplexity A hA ≤
          (m : ℝ) * (2 * (1 + 392 * (v : ℝ)) / Real.sqrt m) :=
        mul_le_mul_of_nonneg_left hcomplexity hmR.le
      _ = 2 * (1 + 392 * (v : ℝ)) * Real.sqrt m := by
        field_simp
        nlinarith [Real.sq_sqrt hmR.le]
  rw [sum_restrictionSignedAbsSup_eq_card_mul]
  exact mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg _)

private def firstPattern {m : ℕ} (p : Fin (2 * m) → Bool) : Fin m → Bool :=
  fun i ↦ p ⟨i.val, by omega⟩

private def secondPattern {m : ℕ} (p : Fin (2 * m) → Bool) : Fin m → Bool :=
  fun i ↦ p ⟨i.val + m, by omega⟩

private theorem pairPattern_signedSum_sub {m : ℕ} (p : Fin (2 * m) → Bool)
    (sigma : SignVector m) :
    (∑ i : Fin m, pairPatternCoeff p i * boolToSign (sigma i)) =
      signedSum sigma (indicatorVector (firstPattern p)) -
        signedSum sigma (indicatorVector (secondPattern p)) := by
  rw [signedSum, signedSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let i0 : Fin (2 * m) := ⟨i.val, by omega⟩
  let i1 : Fin (2 * m) := ⟨i.val + m, by omega⟩
  change -((if p i1 then (1 : ℝ) else 0) - (if p i0 then 1 else 0)) *
      boolToSign (sigma i) =
    boolToSign (sigma i) * (if p i0 then 1 else 0) -
      boolToSign (sigma i) * (if p i1 then 1 else 0)
  ring

/-- Sum of the two half-sample absolute suprema controlling all swapped pair gaps. -/
noncomputable def pairRestrictionEnvelope {m : ℕ}
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (z : Fin m → Ω × Ω)
    (hC : C.Nonempty) (sigma : SignVector m) : ℝ :=
  restrictionSignedAbsSup C c (fun i ↦ (z i).1) hC sigma +
    restrictionSignedAbsSup C c (fun i ↦ (z i).2) hC sigma

theorem pairRestrictionEnvelope_nonneg {m : ℕ}
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (z : Fin m → Ω × Ω)
    (hC : C.Nonempty) (sigma : SignVector m) :
    0 ≤ pairRestrictionEnvelope C c z hC sigma := by
  exact add_nonneg
    (restrictionSignedAbsSup_nonneg C c (fun i ↦ (z i).1) hC sigma)
    (restrictionSignedAbsSup_nonneg C c (fun i ↦ (z i).2) hC sigma)

/-- Every swapped gap is bounded by the two half-sample restriction suprema. -/
theorem abs_pairGap_pairSwap_le_pairRestrictionEnvelope {m : ℕ}
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (z : Fin m → Ω × Ω)
    (hC : C.Nonempty) (h : Concept Ω Bool) (hhC : h ∈ C) (sigma : SignVector m) :
    |pairGap h c (pairSwap sigma z)| ≤ pairRestrictionEnvelope C c z hC sigma := by
  let p : Fin (2 * m) → Bool :=
    fun j ↦ decide (h (mergedPairSample z j) ≠ c (mergedPairSample z j))
  have hpFirst : firstPattern p ∈ restrictionPatterns C c m (fun i ↦ (z i).1) := by
    rw [mem_restrictionPatterns_iff]
    refine ⟨h, hhC, fun i ↦ ?_⟩
    simp [firstPattern, p, mergedPairSample]
  have hpSecond : secondPattern p ∈ restrictionPatterns C c m (fun i ↦ (z i).2) := by
    rw [mem_restrictionPatterns_iff]
    refine ⟨h, hhC, fun i ↦ ?_⟩
    simp [secondPattern, p, mergedPairSample]
  have hvFirst : indicatorVector (firstPattern p) ∈
      indicatorVectors (restrictionPatterns C c m (fun i ↦ (z i).1)) :=
    (mem_indicatorVectors_iff _ _).2 ⟨firstPattern p, hpFirst, rfl⟩
  have hvSecond : indicatorVector (secondPattern p) ∈
      indicatorVectors (restrictionPatterns C c m (fun i ↦ (z i).2)) :=
    (mem_indicatorVectors_iff _ _).2 ⟨secondPattern p, hpSecond, rfl⟩
  have hfirst : |signedSum sigma (indicatorVector (firstPattern p))| ≤
      restrictionSignedAbsSup C c (fun i ↦ (z i).1) hC sigma :=
    Finset.le_sup' (fun v ↦ |signedSum sigma v|) hvFirst
  have hsecond : |signedSum sigma (indicatorVector (secondPattern p))| ≤
      restrictionSignedAbsSup C c (fun i ↦ (z i).2) hC sigma :=
    Finset.le_sup' (fun v ↦ |signedSum sigma v|) hvSecond
  calc
    |pairGap h c (pairSwap sigma z)| =
        |signedSum sigma (indicatorVector (firstPattern p)) -
          signedSum sigma (indicatorVector (secondPattern p))| := by
      rw [pairGap_pairSwap_eq_rademacher]
      exact congrArg abs (pairPattern_signedSum_sub p sigma)
    _ ≤ |signedSum sigma (indicatorVector (firstPattern p))| +
        |signedSum sigma (indicatorVector (secondPattern p))| := abs_sub _ _
    _ ≤ pairRestrictionEnvelope C c z hC sigma := add_le_add hfirst hsecond

/-- Finite Markov bound for bad pair-swap signs. -/
theorem pairSwap_badSigns_card_le {m v : ℕ} (hm : 0 < m) (hv : 0 < v)
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (z : Fin m → Ω × Ω)
    (hC : C.Nonempty) (hVC : VCDim Ω C ≤ (v : WithTop ℕ))
    (hzero : ∀ sample : Fin m → Ω,
      zeroPattern m ∈ restrictionPatterns C c m sample)
    {u varianceCap : ℝ} (hu : 0 < u) :
    ((Finset.univ.filter (fun sigma : SignVector m ↦
        pairSwap sigma z ∈ relativeDoubleSampleEvent C c u varianceCap)).card : ℝ) ≤
      (4 * (1 + 392 * (v : ℝ)) * Real.sqrt m / u) *
        (Fintype.card (SignVector m) : ℝ) := by
  let bad := Finset.univ.filter (fun sigma : SignVector m ↦
    pairSwap sigma z ∈ relativeDoubleSampleEvent C c u varianceCap)
  let envelope := pairRestrictionEnvelope C c z hC
  have hbad : ∀ sigma ∈ bad, u ≤ envelope sigma := by
    intro sigma hsigma
    have hsigma' := (Finset.mem_filter.1 hsigma).2
    obtain ⟨h, hhC, hgap, _⟩ := hsigma'
    exact hgap.trans (abs_pairGap_pairSwap_le_pairRestrictionEnvelope C c z hC h hhC sigma)
  have hbad_sum : (bad.card : ℝ) * u ≤ ∑ sigma ∈ bad, envelope sigma := by
    simpa [nsmul_eq_mul] using Finset.card_nsmul_le_sum bad envelope u hbad
  have hsubset_sum : (∑ sigma ∈ bad, envelope sigma) ≤ ∑ sigma : SignVector m, envelope sigma := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [bad])
      (fun sigma _ _ ↦ pairRestrictionEnvelope_nonneg C c z hC sigma)
  have hfirst := sum_restrictionSignedAbsSup_le hm hv C c (fun i ↦ (z i).1)
    hC hVC (hzero fun i ↦ (z i).1)
  have hsecond := sum_restrictionSignedAbsSup_le hm hv C c (fun i ↦ (z i).2)
    hC hVC (hzero fun i ↦ (z i).2)
  have henvelope : (∑ sigma : SignVector m, envelope sigma) ≤
      (Fintype.card (SignVector m) : ℝ) *
        (4 * (1 + 392 * (v : ℝ)) * Real.sqrt m) := by
    simp only [envelope, pairRestrictionEnvelope, Finset.sum_add_distrib]
    calc
      (∑ sigma : SignVector m,
          restrictionSignedAbsSup C c (fun i ↦ (z i).1) hC sigma) +
          ∑ sigma : SignVector m,
            restrictionSignedAbsSup C c (fun i ↦ (z i).2) hC sigma ≤
        (Fintype.card (SignVector m) : ℝ) *
            (2 * (1 + 392 * (v : ℝ)) * Real.sqrt m) +
          (Fintype.card (SignVector m) : ℝ) *
            (2 * (1 + 392 * (v : ℝ)) * Real.sqrt m) := add_le_add hfirst hsecond
      _ = (Fintype.card (SignVector m) : ℝ) *
          (4 * (1 + 392 * (v : ℝ)) * Real.sqrt m) := by ring
  have hcard_mul : (bad.card : ℝ) * u ≤
      (Fintype.card (SignVector m) : ℝ) *
        (4 * (1 + 392 * (v : ℝ)) * Real.sqrt m) :=
    hbad_sum.trans (hsubset_sum.trans henvelope)
  calc
    (bad.card : ℝ) ≤
        ((Fintype.card (SignVector m) : ℝ) *
          (4 * (1 + 392 * (v : ℝ)) * Real.sqrt m)) / u :=
      (le_div_iff₀ hu).2 hcard_mul
    _ = (4 * (1 + 392 * (v : ℝ)) * Real.sqrt m / u) *
        (Fintype.card (SignVector m) : ℝ) := by ring

/-- Exchangeability turns the conditional bad-sign fraction into a genuine paired-sample bound. -/
theorem doubleSample_vc_markov_bound {m v : ℕ} (hm : 0 < m) (hv : 0 < v)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (hC : C.Nonempty) (hVC : VCDim Ω C ≤ (v : WithTop ℕ))
    (hzero : ∀ sample : Fin m → Ω,
      zeroPattern m ∈ restrictionPatterns C c m sample)
    {u varianceCap : ℝ} (hu : 0 < u)
    (hnull : NullMeasurableSet (relativeDoubleSampleEvent C c u varianceCap)
      (Measure.pi (fun _ : Fin m ↦ P.prod P))) :
    Measure.pi (fun _ : Fin m ↦ P.prod P)
        (relativeDoubleSampleEvent C c u varianceCap) ≤
      ENNReal.ofReal (4 * (1 + 392 * (v : ℝ)) * Real.sqrt m / u) := by
  let nu := Measure.pi (fun _ : Fin m ↦ P.prod P)
  let S := relativeDoubleSampleEvent (m := m) C c u varianceCap
  let bound := 4 * (1 + 392 * (v : ℝ)) * Real.sqrt m / u
  have hbound_nonneg : 0 ≤ bound := by dsimp [bound]; positivity
  have hper : ∀ z : Fin m → Ω × Ω,
      ((Finset.univ.filter (fun sigma : SignVector m ↦ pairSwap sigma z ∈ S)).card : ℝ) ≤
        bound * (Fintype.card (SignVector m) : ℝ) := by
    intro z
    exact pairSwap_badSigns_card_le hm hv C c z hC hVC hzero hu
  have hpointwise : ∀ z : Fin m → Ω × Ω,
      (∑ sigma : SignVector m,
        ((pairSwap sigma ⁻¹' S).indicator (1 : (Fin m → Ω × Ω) → ENNReal)) z) ≤
          ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
    intro z
    have hsum :
        (∑ sigma : SignVector m,
          ((pairSwap sigma ⁻¹' S).indicator (1 : (Fin m → Ω × Ω) → ENNReal)) z) =
            ((Finset.univ.filter (fun sigma : SignVector m ↦ pairSwap sigma z ∈ S)).card :
              ENNReal) := by
      simp only [Set.indicator_apply, Pi.one_apply, Set.mem_preimage]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum]
    calc
      ((Finset.univ.filter (fun sigma : SignVector m ↦ pairSwap sigma z ∈ S)).card :
          ENNReal) ≤ ENNReal.ofReal
            (bound * (Fintype.card (SignVector m) : ℝ)) := by
              exact_mod_cast ENNReal.ofReal_le_ofReal (hper z)
      _ = ENNReal.ofReal bound * ENNReal.ofReal (Fintype.card (SignVector m) : ℝ) := by
        rw [ENNReal.ofReal_mul hbound_nonneg]
      _ = ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
        congr 1
        rw [ENNReal.ofReal_natCast]
  have hmp : ∀ sigma : SignVector m, MeasurePreserving (pairSwap sigma) nu nu :=
    fun sigma ↦ measurePreserving_pairSwap P sigma
  have hresult := finite_exchangeability_bound
    (fun sigma : SignVector m ↦ pairSwap sigma) S hmp hnull
      (ENNReal.ofReal bound) hpointwise
  simpa only [nu, S, bound] using hresult

/-- Product-of-samples form of the global VC double-sample bound. -/
theorem doubleSample_vc_markov_bound_prod {m v : ℕ} (hm : 0 < m) (hv : 0 < v)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (hC : C.Nonempty) (hVC : VCDim Ω C ≤ (v : WithTop ℕ))
    (hzero : ∀ sample : Fin m → Ω,
      zeroPattern m ∈ restrictionPatterns C c m sample)
    {u varianceCap : ℝ} (hu : 0 < u)
    (hnull : NullMeasurableSet (relativeDoubleSampleEventProd C c u varianceCap)
      ((Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P)))) :
    (Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P))
        (relativeDoubleSampleEventProd C c u varianceCap) ≤
      ENNReal.ofReal (4 * (1 + 392 * (v : ℝ)) * Real.sqrt m / u) := by
  let mu := Measure.pi (fun _ : Fin m ↦ P)
  let nu := Measure.pi (fun _ : Fin m ↦ P.prod P)
  let eqv := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin m)
  have hmp : MeasurePreserving (⇑eqv) nu (mu.prod mu) := by
    dsimp [nu, mu, eqv]
    exact measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin m)
      (fun _ ↦ P) (fun _ ↦ P)
  have hpre : eqv ⁻¹' relativeDoubleSampleEventProd C c u varianceCap =
      relativeDoubleSampleEvent C c u varianceCap :=
    arrowProd_preimage_relativeDoubleSampleEventProd C c u varianceCap
  have hnull_pair : NullMeasurableSet (relativeDoubleSampleEvent C c u varianceCap) nu := by
    rw [← hpre]
    exact hnull.preimage hmp.quasiMeasurePreserving
  have hmeasure : (mu.prod mu) (relativeDoubleSampleEventProd C c u varianceCap) =
      nu (relativeDoubleSampleEvent C c u varianceCap) := by
    rw [← hpre, ← hmp.map_eq]
    exact eqv.map_apply _
  rw [show (Measure.pi (fun _ : Fin m ↦ P)).prod
      (Measure.pi (fun _ : Fin m ↦ P)) = mu.prod mu from rfl, hmeasure]
  exact doubleSample_vc_markov_bound hm hv P C c hC hVC hzero hu hnull_pair

/-- Source-cut double-sample maximal bound with no VC or measurability premise left to callers. -/
theorem sourceCut_doubleSample_vc_markov_bound
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 0 < m) {u varianceCap : ℝ} (hu : 0 < u) :
    (Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P))
        (relativeDoubleSampleEventProd sourceCutClass falseCutTarget u varianceCap) ≤
      ENNReal.ofReal (4 * (1 + 392 * (3 : ℝ)) * Real.sqrt m / u) := by
  exact doubleSample_vc_markov_bound_prod hm (by norm_num) P
    sourceCutClass falseCutTarget sourceCutClass_nonempty vcdim_sourceCutClass_le_three
    sourceCut_zeroPattern_mem_restrictionPatterns hu
    (sourceCut_relativeDoubleSample_nullMeasurable P m u varianceCap)

/-- Target-cut analogue of `sourceCut_doubleSample_vc_markov_bound`. -/
theorem targetCut_doubleSample_vc_markov_bound
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 0 < m) {u varianceCap : ℝ} (hu : 0 < u) :
    (Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P))
        (relativeDoubleSampleEventProd targetCutClass falseCutTarget u varianceCap) ≤
      ENNReal.ofReal (4 * (1 + 392 * (3 : ℝ)) * Real.sqrt m / u) := by
  exact doubleSample_vc_markov_bound_prod hm (by norm_num) P
    targetCutClass falseCutTarget targetCutClass_nonempty vcdim_targetCutClass_le_three
    targetCut_zeroPattern_mem_restrictionPatterns hu
    (targetCut_relativeDoubleSample_nullMeasurable P m u varianceCap)

end OTSelector.RelativeVC
