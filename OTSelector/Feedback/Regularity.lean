import OTSelector.Feedback.HalfspaceVC

/-!
# Count-scale half-space regularity

`HalfspaceVC` states its concentration bounds in the normalized empirical-process scale.  The
paper's defects `Δ⁻` and `Δ⁺` are unnormalized counts.  This module provides the exact
deterministic conversion and count-scale versions of the balanced source/target bounds.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace OTSelector.RelativeVC

/-- Number of sample points in a source half-space. -/
noncomputable def sourceCutCount {m : ℕ} (xs : Fin m → ℝ × UnitMark) (p x : ℝ) : ℝ :=
  sampleErrorSum (sourceCutEval (p, x)) falseCutTarget xs

/-- Number of sample points in a target half-space. -/
noncomputable def targetCutCount {m : ℕ} (xs : Fin m → ℝ × UnitMark) (p x : ℝ) : ℝ :=
  sampleErrorSum (targetCutEval (p, x)) falseCutTarget xs

/-- Source count minus its exact population expectation. -/
noncomputable def sourceCutDefect
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (xs : Fin m → ℝ × UnitMark) (p x : ℝ) : ℝ :=
  sourceCutCount xs p x -
    (m : ℝ) * P.real (errorSet (sourceCutEval (p, x)) falseCutTarget)

/-- Target count minus its exact population expectation. -/
noncomputable def targetCutDefect
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (xs : Fin m → ℝ × UnitMark) (p x : ℝ) : ℝ :=
  targetCutCount xs p x -
    (m : ℝ) * P.real (errorSet (targetCutEval (p, x)) falseCutTarget)

theorem sourceCutDefect_eq_centeredErrorSum
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (xs : Fin m → ℝ × UnitMark) (p x : ℝ) :
    sourceCutDefect P xs p x =
      centeredErrorSum P (sourceCutEval (p, x)) falseCutTarget xs := by
  rfl

theorem targetCutDefect_eq_centeredErrorSum
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (xs : Fin m → ℝ × UnitMark) (p x : ℝ) :
    targetCutDefect P xs p x =
      centeredErrorSum P (targetCutEval (p, x)) falseCutTarget xs := by
  rfl

/-- Exact source-defect conversion from normalized empirical process to count scale. -/
theorem sourceCutDefect_eq_sqrt_mul_empiricalProcess
    (P : Measure (ℝ × UnitMark)) {m : ℕ} (hm : 0 < m)
    (xs : Fin m → ℝ × UnitMark) (p x : ℝ) :
    sourceCutDefect P xs p x = Real.sqrt m *
      EmpiricalProcess.empiricalProcess P m xs
        (indicatorReal (errorSet (sourceCutEval (p, x)) falseCutTarget)) := by
  rw [sourceCutDefect_eq_centeredErrorSum]
  exact centeredErrorSum_eq_sqrt_mul_empiricalProcess P hm _ _
    (measurableSet_errorSet
      (measurable_sourceCutClass _ ⟨p, x, rfl⟩) measurable_falseCutTarget) xs

/-- Exact target-defect conversion from normalized empirical process to count scale. -/
theorem targetCutDefect_eq_sqrt_mul_empiricalProcess
    (P : Measure (ℝ × UnitMark)) {m : ℕ} (hm : 0 < m)
    (xs : Fin m → ℝ × UnitMark) (p x : ℝ) :
    targetCutDefect P xs p x = Real.sqrt m *
      EmpiricalProcess.empiricalProcess P m xs
        (indicatorReal (errorSet (targetCutEval (p, x)) falseCutTarget)) := by
  rw [targetCutDefect_eq_centeredErrorSum]
  exact centeredErrorSum_eq_sqrt_mul_empiricalProcess P hm _ _
    (measurableSet_errorSet
      (measurable_targetCutClass _ ⟨p, x, rfl⟩) measurable_falseCutTarget) xs

/-- Balanced localized event in the paper's unnormalized centered-count scale. -/
noncomputable def balancedLocalizedCutCountEvent
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (C : ConceptClass (ℝ × UnitMark) Bool)
    (countThreshold trueMassCap sampleMassCap : ℝ) : Set (Fin m → ℝ × UnitMark) :=
  {xs | ∃ h ∈ C,
    balancedMass P (errorSet h falseCutTarget) ≤ trueMassCap ∧
    countThreshold ≤ |centeredErrorSum P h falseCutTarget xs| ∧
    populationOrientedSampleErrorSum P h xs ≤ sampleMassCap}

/-- The count event is exactly the normalized event at threshold `countThreshold / √m`. -/
theorem balancedLocalizedCutCountEvent_eq
    (P : Measure (ℝ × UnitMark))
    (C : ConceptClass (ℝ × UnitMark) Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h)
    {m : ℕ} (hm : 0 < m) (countThreshold trueMassCap sampleMassCap : ℝ) :
    balancedLocalizedCutCountEvent (m := m) P C countThreshold trueMassCap sampleMassCap =
      balancedLocalizedCutEvent (m := m) P C (countThreshold / Real.sqrt m)
        trueMassCap sampleMassCap := by
  ext xs
  constructor
  · rintro ⟨h, hhC, hmass, hcount, hsample⟩
    refine ⟨h, hhC, hmass, ?_, hsample⟩
    have hs : MeasurableSet (errorSet h falseCutTarget) :=
      measurableSet_errorSet (hmeas_C h hhC) measurable_falseCutTarget
    rw [centeredErrorSum_eq_sqrt_mul_empiricalProcess P hm h falseCutTarget hs xs,
      abs_mul, abs_of_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hm))] at hcount
    have hcount' : countThreshold ≤
        |EmpiricalProcess.empiricalProcess P m xs
          (indicatorReal (errorSet h falseCutTarget))| * Real.sqrt m := by
      simpa [mul_comm] using hcount
    exact (div_le_iff₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hm))).mpr hcount'
  · rintro ⟨h, hhC, hmass, hproc, hsample⟩
    refine ⟨h, hhC, hmass, ?_, hsample⟩
    have hs : MeasurableSet (errorSet h falseCutTarget) :=
      measurableSet_errorSet (hmeas_C h hhC) measurable_falseCutTarget
    rw [centeredErrorSum_eq_sqrt_mul_empiricalProcess P hm h falseCutTarget hs xs,
      abs_mul, abs_of_pos (Real.sqrt_pos.2 (Nat.cast_pos.2 hm))]
    simpa [mul_comm] using
      (div_le_iff₀ (Real.sqrt_pos.2 (Nat.cast_pos.2 hm))).mp hproc

/-- Source balanced relative-VC Bernstein inequality on the unnormalized count scale. -/
theorem sourceCut_balanced_count_bernstein
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m)
    (countThreshold trueMassCap sampleMassCap : ℝ) (hthreshold : 0 < countThreshold)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp (-(((countThreshold / Real.sqrt m) / 2) ^ 2) /
          (4 * (trueMassCap +
            ((countThreshold / Real.sqrt m) / 2) / Real.sqrt m)))) ≤
        (1 : ENNReal) / 2)
    (hvarianceCap :
      0 < sampleMassCap + (m : ℝ) * trueMassCap +
        Real.sqrt m * ((countThreshold / Real.sqrt m) / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        (balancedLocalizedCutCountEvent P sourceCutClass countThreshold
          trueMassCap sampleMassCap) ≤
      2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * (countThreshold / Real.sqrt m) / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * ((countThreshold / Real.sqrt m) / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * (countThreshold / Real.sqrt m) / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * ((countThreshold / Real.sqrt m) / 2))))) := by
  rw [balancedLocalizedCutCountEvent_eq P sourceCutClass measurable_sourceCutClass hm]
  exact sourceCut_balanced_localized_relative_vc_bernstein P m hm
    (countThreshold / Real.sqrt m) trueMassCap sampleMassCap
    (div_pos hthreshold (Real.sqrt_pos.2 (Nat.cast_pos.2 hm)))
    hghostBernstein hvarianceCap

/-- Target balanced relative-VC Bernstein inequality on the unnormalized count scale. -/
theorem targetCut_balanced_count_bernstein
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m)
    (countThreshold trueMassCap sampleMassCap : ℝ) (hthreshold : 0 < countThreshold)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp (-(((countThreshold / Real.sqrt m) / 2) ^ 2) /
          (4 * (trueMassCap +
            ((countThreshold / Real.sqrt m) / 2) / Real.sqrt m)))) ≤
        (1 : ENNReal) / 2)
    (hvarianceCap :
      0 < sampleMassCap + (m : ℝ) * trueMassCap +
        Real.sqrt m * ((countThreshold / Real.sqrt m) / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        (balancedLocalizedCutCountEvent P targetCutClass countThreshold
          trueMassCap sampleMassCap) ≤
      2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * (countThreshold / Real.sqrt m) / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * ((countThreshold / Real.sqrt m) / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * (countThreshold / Real.sqrt m) / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * ((countThreshold / Real.sqrt m) / 2))))) := by
  rw [balancedLocalizedCutCountEvent_eq P targetCutClass measurable_targetCutClass hm]
  exact targetCut_balanced_localized_relative_vc_bernstein P m hm
    (countThreshold / Real.sqrt m) trueMassCap sampleMassCap
    (div_pos hthreshold (Real.sqrt_pos.2 (Nat.cast_pos.2 hm)))
    hghostBernstein hvarianceCap

end OTSelector.RelativeVC
