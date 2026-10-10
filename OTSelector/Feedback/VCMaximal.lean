/-
Copyright (c) 2026 Yuwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuwei Lu
-/

import OTSelector.Probability.Rademacher.Restriction
import OTSelector.Feedback.HalfspaceVC

/-!
# Fixed-sample VC maximal bounds for the feedback cut classes

The restriction patterns used by the feedback layer are disagreement patterns against a fixed
target.  Pointwise Boolean XOR by that target preserves shattering, so these patterns inherit the
VC dimension of the original concept class.  This file combines that bridge with the log-free
absolute Rademacher bound and discharges the all-false-pattern condition for the source and target
half-space families on every finite sample.
-/

open MeasureTheory

namespace OTSelector.RelativeVC

open Classical
open OTSelector.Probability.Rademacher

universe u

/-! ## Fixed-target disagreement classes -/

/-- Pointwise disagreement with a fixed target concept. -/
def fixedTargetXor {Ω : Type u} (c h : Concept Ω Bool) : Concept Ω Bool :=
  fun x ↦ decide (h x ≠ c x)

/-- The image of a concept class under pointwise disagreement with a fixed target. -/
def fixedTargetXorClass {Ω : Type u} (C : ConceptClass Ω Bool) (c : Concept Ω Bool) :
    ConceptClass Ω Bool :=
  {g | ∃ h ∈ C, g = fixedTargetXor c h}

@[simp]
theorem fixedTargetXor_involutive (a b : Bool) :
    decide (decide (a ≠ b) ≠ b) = a := by
  cases a <;> cases b <;> simp

/-- Pointwise XOR with a fixed target preserves every shattered finite set. -/
theorem shatters_fixedTargetXorClass_iff {Ω : Type u} (C : ConceptClass Ω Bool)
    (c : Concept Ω Bool) (S : Finset Ω) :
    Shatters Ω (fixedTargetXorClass C c) S ↔ Shatters Ω C S := by
  constructor
  · intro hS label
    let xorLabel : S → Bool := fun x ↦ decide (label x ≠ c x)
    obtain ⟨_, ⟨h, hhC, rfl⟩, hrealize⟩ := hS xorLabel
    refine ⟨h, hhC, ?_⟩
    intro x
    have hx : decide (h x ≠ c x) = decide (label x ≠ c x) := by
      simpa [fixedTargetXor, xorLabel] using hrealize x
    calc
      h x = decide (decide (h x ≠ c x) ≠ c x) :=
        (fixedTargetXor_involutive (h x) (c x)).symm
      _ = decide (decide (label x ≠ c x) ≠ c x) := by
        rw [hx]
      _ = label x := fixedTargetXor_involutive (label x) (c x)
  · intro hS label
    let xorLabel : S → Bool := fun x ↦ decide (label x ≠ c x)
    obtain ⟨h, hhC, hrealize⟩ := hS xorLabel
    refine ⟨fixedTargetXor c h, ⟨h, hhC, rfl⟩, ?_⟩
    intro x
    rw [fixedTargetXor, hrealize x]
    exact fixedTargetXor_involutive (label x) (c x)

/-- Pointwise disagreement with a fixed target does not change VC dimension. -/
theorem vcdim_fixedTargetXorClass_eq {Ω : Type u} (C : ConceptClass Ω Bool)
    (c : Concept Ω Bool) :
    VCDim Ω (fixedTargetXorClass C c) = VCDim Ω C := by
  apply le_antisymm
  · exact vcdim_le_of_shatters_imp fun S ↦ (shatters_fixedTargetXorClass_iff C c S).1
  · exact vcdim_le_of_shatters_imp fun S ↦ (shatters_fixedTargetXorClass_iff C c S).2

/-- Feedback restriction patterns are the ordinary realized patterns of the fixed-target XOR
class. -/
theorem restrictionPatterns_eq_realizedPatterns_fixedTargetXor {Ω : Type u}
    [MeasurableSpace Ω] (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    {m : ℕ} (z : Fin m → Ω) :
    restrictionPatterns C c m z = realizedPatterns (fixedTargetXorClass C c) z := by
  ext p
  rw [mem_restrictionPatterns_iff, mem_realizedPatterns_iff]
  constructor
  · rintro ⟨h, hhC, hp⟩
    exact ⟨fixedTargetXor c h, ⟨h, hhC, rfl⟩, hp⟩
  · rintro ⟨_, ⟨h, hhC, rfl⟩, hp⟩
    exact ⟨h, hhC, hp⟩

/-- A nonempty concept class has a nonempty finite disagreement-pattern family. -/
theorem restrictionPatterns_nonempty {Ω : Type u} [MeasurableSpace Ω]
    {C : ConceptClass Ω Bool} (c : Concept Ω Bool) {m : ℕ} (z : Fin m → Ω)
    (hC : C.Nonempty) : (restrictionPatterns C c m z).Nonempty := by
  obtain ⟨h, hhC⟩ := hC
  refine ⟨fun i ↦ decide (h (z i) ≠ c (z i)), ?_⟩
  exact (mem_restrictionPatterns_iff C c m z _).2 ⟨h, hhC, fun _ ↦ rfl⟩

/-- The finite disagreement restriction cannot have larger Boolean VC dimension than the
original concept class. -/
theorem restrictionPatterns_boolVCDim_le {Ω : Type u} [MeasurableSpace Ω]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) {m v : ℕ} (z : Fin m → Ω)
    (hVC : VCDim Ω C ≤ (v : WithTop ℕ)) :
    (restrictionPatterns C c m z).boolVCDim ≤ v := by
  rw [restrictionPatterns_eq_realizedPatterns_fixedTargetXor]
  apply realizedPatterns_boolVCDim_le
  rwa [vcdim_fixedTargetXorClass_eq]

/-- Restriction-pattern form of the absolute fixed-sample VC maximal inequality. -/
theorem fixedRademacherAbsComplexity_restrictionPatterns_le
    {Ω : Type u} [MeasurableSpace Ω] {m v : ℕ} (hm : 0 < m) (hv : 0 < v)
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (z : Fin m → Ω)
    (hC : C.Nonempty) (hVC : VCDim Ω C ≤ (v : WithTop ℕ))
    (hzero : zeroPattern m ∈ restrictionPatterns C c m z) :
    fixedRademacherAbsComplexity (indicatorVectors (restrictionPatterns C c m z))
        (indicatorVectors_nonempty (restrictionPatterns_nonempty c z hC)) ≤
      2 * (1 + 392 * (v : ℝ)) / Real.sqrt m := by
  apply fixedRademacherAbsComplexity_indicator_le hm hv
  · exact restrictionPatterns_nonempty c z hC
  · exact hzero
  · exact restrictionPatterns_boolVCDim_le C c z hVC

/-! ## Source and target cut instances -/

/-- Every finite real family has a strict common lower bound. -/
theorem exists_real_below_fin {m : ℕ} (a : Fin m → ℝ) : ∃ x : ℝ, ∀ i, x < a i := by
  classical
  by_cases h : Nonempty (Fin m)
  · let _ : Nonempty (Fin m) := h
    let x : ℝ := Finset.univ.inf' Finset.univ_nonempty a - 1
    refine ⟨x, fun i ↦ ?_⟩
    have hle : Finset.univ.inf' Finset.univ_nonempty a ≤ a i :=
      Finset.inf'_le a (Finset.mem_univ i)
    dsimp [x]
    linarith
  · refine ⟨0, fun i ↦ ?_⟩
    exact (h ⟨i⟩).elim

theorem sourceCutClass_nonempty : sourceCutClass.Nonempty :=
  ⟨sourceCutEval (0, 0), ⟨0, 0, rfl⟩⟩

theorem targetCutClass_nonempty : targetCutClass.Nonempty :=
  ⟨targetCutEval (0, 0), ⟨0, 0, rfl⟩⟩

/-- On any finite sample, a source threshold below every first coordinate realizes the all-false
pattern. -/
theorem sourceCut_zeroPattern_mem_restrictionPatterns {m : ℕ}
    (z : Fin m → ℝ × UnitMark) :
    zeroPattern m ∈ restrictionPatterns sourceCutClass falseCutTarget m z := by
  obtain ⟨x, hx⟩ := exists_real_below_fin fun i ↦ (z i).1
  rw [mem_restrictionPatterns_iff]
  refine ⟨sourceCutEval (0, x), ⟨0, x, rfl⟩, fun i ↦ ?_⟩
  have hnot : ¬(z i).1 ≤ x := not_le_of_gt (hx i)
  simp [zeroPattern, sourceCutEval, falseCutTarget, hnot]

/-- On any finite sample, a target threshold below every first coordinate realizes the all-false
pattern. -/
theorem targetCut_zeroPattern_mem_restrictionPatterns {m : ℕ}
    (z : Fin m → ℝ × UnitMark) :
    zeroPattern m ∈ restrictionPatterns targetCutClass falseCutTarget m z := by
  obtain ⟨x, hx⟩ := exists_real_below_fin fun i ↦ (z i).1
  rw [mem_restrictionPatterns_iff]
  refine ⟨targetCutEval (0, x), ⟨0, x, rfl⟩, fun i ↦ ?_⟩
  have hnot : ¬(z i).1 ≤ x := not_le_of_gt (hx i)
  simp [zeroPattern, targetCutEval, falseCutTarget, hnot]

/-- Absolute fixed-sample maximal inequality for the source cut restriction. -/
theorem sourceCut_fixedRademacherAbsComplexity_le {m : ℕ} (hm : 0 < m)
    (z : Fin m → ℝ × UnitMark) :
    fixedRademacherAbsComplexity
        (indicatorVectors (restrictionPatterns sourceCutClass falseCutTarget m z))
        (indicatorVectors_nonempty
          (restrictionPatterns_nonempty falseCutTarget z sourceCutClass_nonempty)) ≤
      2 * (1 + 392 * (3 : ℝ)) / Real.sqrt m := by
  exact fixedRademacherAbsComplexity_restrictionPatterns_le hm (by norm_num)
    sourceCutClass falseCutTarget z sourceCutClass_nonempty
    vcdim_sourceCutClass_le_three (sourceCut_zeroPattern_mem_restrictionPatterns z)

/-- Absolute fixed-sample maximal inequality for the target cut restriction. -/
theorem targetCut_fixedRademacherAbsComplexity_le {m : ℕ} (hm : 0 < m)
    (z : Fin m → ℝ × UnitMark) :
    fixedRademacherAbsComplexity
        (indicatorVectors (restrictionPatterns targetCutClass falseCutTarget m z))
        (indicatorVectors_nonempty
          (restrictionPatterns_nonempty falseCutTarget z targetCutClass_nonempty)) ≤
      2 * (1 + 392 * (3 : ℝ)) / Real.sqrt m := by
  exact fixedRademacherAbsComplexity_restrictionPatterns_le hm (by norm_num)
    targetCutClass falseCutTarget z targetCutClass_nonempty
    vcdim_targetCutClass_le_three (targetCut_zeroPattern_mem_restrictionPatterns z)

end OTSelector.RelativeVC
