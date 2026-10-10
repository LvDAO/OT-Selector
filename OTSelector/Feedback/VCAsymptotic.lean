import OTSelector.Feedback.VCGlobal
import OTSelector.Feedback.Regularity
import OTSelector.Basic.ModelLaw
import OTSelector.Probability.TriangularArray
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Global VC control on the count scale

This module completes the ordinary VC maximal estimate used in (1.11).  A fixed-concept
Bernstein estimate makes a ghost sample good with probability at least one half.  The global
double-sample estimate from `VCGlobal` then controls the whole source or target cut class.  The
last theorem packages the resulting uniform inverse tail as `O_P(√n)` for the rank-strip rows.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace OTSelector.RelativeVC

open OTSelector.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A fixed centered indicator is inside the radius `32` with probability at least one half. -/
theorem centeredIndicator_thirtyTwo_tail_le_half
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Set Ω) (hs : MeasurableSet s) {m : ℕ} (hm : 0 < m) :
    Measure.pi (fun _ : Fin m ↦ P)
        {sample : Fin m → Ω |
          32 < |EmpiricalProcess.empiricalProcess P m sample (indicatorReal s)|} ≤
      (1 : ENNReal) / 2 := by
  have hm_one : 1 ≤ m := hm
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_one
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hm_real
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 hm)
  have hdiv : (32 : ℝ) / Real.sqrt (m : ℝ) ≤ 32 := by
    apply (div_le_iff₀ hsqrt_pos).2
    nlinarith [hsqrt_ge_one]
  have hden_pos :
      0 < 4 * (1 + (32 : ℝ) / Real.sqrt (m : ℝ)) := by
    positivity
  have hfrac :
      (3 : ℝ) ≤ (32 : ℝ) ^ 2 /
        (4 * (1 + (32 : ℝ) / Real.sqrt (m : ℝ))) := by
    apply (le_div_iff₀ hden_pos).2
    nlinarith [hdiv]
  have hexp_arg :
      -((32 : ℝ) ^ 2) /
          (4 * (1 + (32 : ℝ) / Real.sqrt (m : ℝ))) ≤ (-3 : ℝ) := by
    simpa only [neg_div] using neg_le_neg hfrac
  have hexp_neg_three : Real.exp (-3 : ℝ) ≤ (1 / 8 : ℝ) := by
    have h_exp_three : (8 : ℝ) ≤ Real.exp 3 := by
      calc
        (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
        _ ≤ (Real.exp 1) ^ 3 := by
          have htwo : (2 : ℝ) ≤ Real.exp 1 := by
            nlinarith [Real.add_one_le_exp (1 : ℝ)]
          exact pow_le_pow_left₀ (by norm_num) htwo 3
        _ = Real.exp 3 := by
          simp
    have hinv : (Real.exp 3)⁻¹ ≤ (1 / 8 : ℝ) := by
      simpa [one_div] using
        (inv_le_inv₀ (Real.exp_pos 3) (by norm_num : (0 : ℝ) < 8)).2 h_exp_three
    simpa [Real.exp_neg] using hinv
  have hreal :
      2 * Real.exp (-((32 : ℝ) ^ 2) /
          (4 * (1 + (32 : ℝ) / Real.sqrt (m : ℝ)))) ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ 2 * Real.exp (-3) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) (by norm_num)
      _ ≤ (1 / 2 : ℝ) := by nlinarith [hexp_neg_three]
  have hbern := centeredIndicator_bernstein_pi_of_mass_le
    P s hs m hm_one (by norm_num : (0 : ℝ) < 32) (measureReal_le_one)
  refine hbern.trans ?_
  calc
    ENNReal.ofReal
        (2 * Real.exp (-((32 : ℝ) ^ 2) /
          (4 * (1 + (32 : ℝ) / Real.sqrt m)))) ≤
        ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hreal
    _ = (1 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num

omit [MeasurableSpace Ω] in
/-- Across two samples there are at most `2m` Boolean errors. -/
theorem pairErrorMass_le_two_mul_card {m : ℕ}
    (h c : Concept Ω Bool) (z : Fin m → Ω × Ω) :
    pairErrorMass h c z ≤ 2 * (m : ℝ) := by
  unfold pairErrorMass
  calc
    ∑ i : Fin m,
        (zeroOneLoss Bool (h (z i).1) (c (z i).1) +
          zeroOneLoss Bool (h (z i).2) (c (z i).2)) ≤
        ∑ _i : Fin m, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hfirst :
          zeroOneLoss Bool (h (z i).1) (c (z i).1) ≤ (1 : ℝ) := by
        cases hxi : h (z i).1 <;>
          cases cxi : c (z i).1 <;>
          norm_num [zeroOneLoss]
      have hsecond :
          zeroOneLoss Bool (h (z i).2) (c (z i).2) ≤ (1 : ℝ) := by
        cases hxi : h (z i).2 <;>
          cases cxi : c (z i).2 <;>
          norm_num [zeroOneLoss]
      linarith
    _ = 2 * (m : ℝ) := by simp [mul_comm]

/-- The event that some concept has an unnormalized centered error above `threshold`. -/
noncomputable def globalCenteredErrorEvent
    (P : Measure Ω) {m : ℕ} (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (threshold : ℝ) : Set (Fin m → Ω) :=
  {sample | ∃ h ∈ C, threshold < |centeredErrorSum P h c sample|}

/-- Ghost symmetrization for the unlocalized global centered-error event. -/
theorem globalCenteredErrorEvent_ghost_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc : Measurable c)
    {m : ℕ} (hm : 0 < m) {q : ℝ} :
    Measure.pi (fun _ : Fin m ↦ P)
        (globalCenteredErrorEvent P C c ((q + 32) * Real.sqrt m)) ≤
      2 * ((Measure.pi (fun _ : Fin m ↦ P)).prod
        (Measure.pi (fun _ : Fin m ↦ P)))
          (relativeDoubleSampleEventProd C c (q * Real.sqrt m) (2 * m)) := by
  let mu := Measure.pi (fun _ : Fin m ↦ P)
  let A := globalCenteredErrorEvent (m := m) P C c ((q + 32) * Real.sqrt m)
  let B := relativeDoubleSampleEventProd (m := m) C c
    (q * Real.sqrt m) (2 * (m : ℝ))
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 hm)
  change mu A ≤ 2 * (mu.prod mu) B
  apply ghost_half_symmetrization mu A B
  intro sample hsample
  change sample ∈ globalCenteredErrorEvent P C c
    ((q + 32) * Real.sqrt m) at hsample
  obtain ⟨h, hhC, hbad⟩ := hsample
  let H : Set (Fin m → Ω) :=
    {ghost | 32 <
      |EmpiricalProcess.empiricalProcess P m ghost (indicatorReal (errorSet h c))|}
  refine ⟨Hᶜ, ?_, ?_⟩
  · have hH : mu H ≤ (1 : ENNReal) / 2 := by
      exact centeredIndicator_thirtyTwo_tail_le_half P (errorSet h c)
        (measurableSet_errorSet (hmeas_C h hhC) hc) hm
    exact half_le_measure_compl_of_measure_le_half mu H hH
  · intro ghost hghost
    have hgoodProcess :
        |EmpiricalProcess.empiricalProcess P m ghost
          (indicatorReal (errorSet h c))| ≤ 32 := by
      simpa only [H, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] using hghost
    have hs := measurableSet_errorSet (hmeas_C h hhC) hc
    have hgoodCentered :
        |centeredErrorSum P h c ghost| ≤ 32 * Real.sqrt m := by
      rw [centeredErrorSum_eq_sqrt_mul_empiricalProcess P hm h c hs ghost,
        abs_mul, abs_of_pos hsqrt_pos]
      nlinarith [mul_le_mul_of_nonneg_left hgoodProcess hsqrt_pos.le]
    have hreverse :
        q * Real.sqrt m <
          |centeredErrorSum P h c ghost - centeredErrorSum P h c sample| := by
      calc
        q * Real.sqrt m =
            (q + 32) * Real.sqrt m - 32 * Real.sqrt m := by ring
        _ < |centeredErrorSum P h c sample| -
            |centeredErrorSum P h c ghost| := by linarith
        _ ≤ |centeredErrorSum P h c sample - centeredErrorSum P h c ghost| :=
          abs_sub_abs_le_abs_sub _ _
        _ = |centeredErrorSum P h c ghost - centeredErrorSum P h c sample| :=
          abs_sub_comm _ _
    change (sample, ghost) ∈ B
    change (sample, ghost) ∈ relativeDoubleSampleEventProd C c
      (q * Real.sqrt m) (2 * (m : ℝ))
    refine ⟨h, hhC, ?_, ?_⟩
    · change q * Real.sqrt m ≤
        |pairGap h c (fun i ↦ (sample i, ghost i))|
      have hgap :
          pairGap h c (fun i ↦ (sample i, ghost i)) =
            centeredErrorSum P h c ghost - centeredErrorSum P h c sample := by
        simp only [pairGap, centeredErrorSum, sampleErrorSum]
        ring
      rw [hgap]
      exact hreverse.le
    · change pairErrorMass h c (fun i ↦ (sample i, ghost i)) ≤ 2 * (m : ℝ)
      exact pairErrorMass_le_two_mul_card h c _

/-- Source-cut global centered-error tail after the ghost sample has been eliminated. -/
theorem sourceCut_globalCenteredErrorEvent_measure_le
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 0 < m) {q : ℝ} (hq : 0 < q) :
    Measure.pi (fun _ : Fin m ↦ P)
        (globalCenteredErrorEvent P sourceCutClass falseCutTarget
          ((q + 32) * Real.sqrt m)) ≤
      2 * ENNReal.ofReal (4708 / q) := by
  have hghost := globalCenteredErrorEvent_ghost_le (q := q)
    P sourceCutClass falseCutTarget
    measurable_sourceCutClass measurable_falseCutTarget hm
  have hsqrt_ne : Real.sqrt (m : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (Nat.cast_pos.2 hm)).ne'
  have hdouble := sourceCut_doubleSample_vc_markov_bound P hm
    (u := q * Real.sqrt m) (varianceCap := 2 * (m : ℝ)) (mul_pos hq (by positivity))
  have hratio :
      4 * (1 + 392 * (3 : ℝ)) * Real.sqrt m / (q * Real.sqrt m) = 4708 / q := by
    field_simp [hq.ne', hsqrt_ne]
    ring
  rw [hratio] at hdouble
  exact hghost.trans (mul_le_mul_of_nonneg_left hdouble (by positivity))

/-- Target-cut analogue of `sourceCut_globalCenteredErrorEvent_measure_le`. -/
theorem targetCut_globalCenteredErrorEvent_measure_le
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 0 < m) {q : ℝ} (hq : 0 < q) :
    Measure.pi (fun _ : Fin m ↦ P)
        (globalCenteredErrorEvent P targetCutClass falseCutTarget
          ((q + 32) * Real.sqrt m)) ≤
      2 * ENNReal.ofReal (4708 / q) := by
  have hghost := globalCenteredErrorEvent_ghost_le (q := q)
    P targetCutClass falseCutTarget
    measurable_targetCutClass measurable_falseCutTarget hm
  have hsqrt_ne : Real.sqrt (m : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (Nat.cast_pos.2 hm)).ne'
  have hdouble := targetCut_doubleSample_vc_markov_bound P hm
    (u := q * Real.sqrt m) (varianceCap := 2 * (m : ℝ)) (mul_pos hq (by positivity))
  have hratio :
      4 * (1 + 392 * (3 : ℝ)) * Real.sqrt m / (q * Real.sqrt m) = 4708 / q := by
    field_simp [hq.ne', hsqrt_ne]
    ring
  rw [hratio] at hdouble
  exact hghost.trans (mul_le_mul_of_nonneg_left hdouble (by positivity))

/-- Absolute centered-error values realized by a concept class on one sample. -/
noncomputable def globalCenteredErrorValueSet
    (P : Measure Ω) {m : ℕ} (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (sample : Fin m → Ω) : Set ℝ :=
  {y | ∃ h ∈ C, y = |centeredErrorSum P h c sample|}

/-- Supremum of absolute centered errors over a concept class. -/
noncomputable def globalCenteredErrorSup
    (P : Measure Ω) {m : ℕ} (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (sample : Fin m → Ω) : ℝ :=
  sSup (globalCenteredErrorValueSet P C c sample)

omit [MeasurableSpace Ω] in
theorem sampleErrorSum_nonneg {m : ℕ} (h c : Concept Ω Bool) (sample : Fin m → Ω) :
    0 ≤ sampleErrorSum h c sample := by
  unfold sampleErrorSum
  apply Finset.sum_nonneg
  intro i _
  cases hxi : h (sample i) <;>
    cases cxi : c (sample i) <;>
    norm_num [zeroOneLoss]

omit [MeasurableSpace Ω] in
theorem sampleErrorSum_le_card {m : ℕ} (h c : Concept Ω Bool) (sample : Fin m → Ω) :
    sampleErrorSum h c sample ≤ (m : ℝ) := by
  unfold sampleErrorSum
  calc
    ∑ i : Fin m, zeroOneLoss Bool (h (sample i)) (c (sample i)) ≤
        ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      cases hxi : h (sample i) <;>
        cases cxi : c (sample i) <;>
        norm_num [zeroOneLoss]
    _ = (m : ℝ) := by simp

/-- Every centered Boolean count is bounded by twice the sample size. -/
theorem abs_centeredErrorSum_le_two_mul_card
    (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (h c : Concept Ω Bool) (sample : Fin m → Ω) :
    |centeredErrorSum P h c sample| ≤ 2 * (m : ℝ) := by
  have hsample0 := sampleErrorSum_nonneg h c sample
  have hsample := sampleErrorSum_le_card h c sample
  have hmass0 : 0 ≤ P.real (errorSet h c) := measureReal_nonneg
  have hmass : P.real (errorSet h c) ≤ 1 := measureReal_le_one
  rw [centeredErrorSum]
  calc
    |sampleErrorSum h c sample - (m : ℝ) * P.real (errorSet h c)| ≤
        |sampleErrorSum h c sample| + |(m : ℝ) * P.real (errorSet h c)| := abs_sub _ _
    _ = sampleErrorSum h c sample + (m : ℝ) * P.real (errorSet h c) := by
      rw [abs_of_nonneg hsample0, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg m) hmass0)]
    _ ≤ (m : ℝ) + (m : ℝ) :=
      add_le_add hsample (by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg m)))
    _ = 2 * (m : ℝ) := by ring

/-- The global centered-error value set is nonempty when the class is. -/
theorem globalCenteredErrorValueSet_nonempty
    (P : Measure Ω) {m : ℕ} (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (sample : Fin m → Ω) (hC : C.Nonempty) :
    (globalCenteredErrorValueSet P C c sample).Nonempty := by
  obtain ⟨h, hhC⟩ := hC
  exact ⟨|centeredErrorSum P h c sample|, h, hhC, rfl⟩

/-- The global centered-error value set has a deterministic finite upper bound. -/
theorem globalCenteredErrorValueSet_bddAbove
    (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (sample : Fin m → Ω) :
    BddAbove (globalCenteredErrorValueSet P C c sample) := by
  refine ⟨2 * (m : ℝ), ?_⟩
  intro y hy
  obtain ⟨h, _, rfl⟩ := hy
  exact abs_centeredErrorSum_le_two_mul_card P h c sample

/-- A nonempty class has a nonnegative global centered-error supremum. -/
theorem globalCenteredErrorSup_nonneg
    (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (sample : Fin m → Ω) (hC : C.Nonempty) :
    0 ≤ globalCenteredErrorSup P C c sample := by
  obtain ⟨h, hhC⟩ := hC
  have hmem : |centeredErrorSum P h c sample| ∈
      globalCenteredErrorValueSet P C c sample := ⟨h, hhC, rfl⟩
  exact (abs_nonneg _).trans
    (le_csSup (globalCenteredErrorValueSet_bddAbove P C c sample) hmem)

/-- Any individual concept error lies below the global supremum. -/
theorem abs_centeredErrorSum_le_globalCenteredErrorSup
    (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (sample : Fin m → Ω) {h : Concept Ω Bool} (hhC : h ∈ C) :
    |centeredErrorSum P h c sample| ≤ globalCenteredErrorSup P C c sample := by
  apply le_csSup (globalCenteredErrorValueSet_bddAbove P C c sample)
  exact ⟨h, hhC, rfl⟩

/-- A large supremum produces a witness in the global centered-error event. -/
theorem globalCenteredErrorSup_largeEvent_subset
    (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (hC : C.Nonempty) (threshold : ℝ) :
    {sample : Fin m → Ω |
      threshold < |globalCenteredErrorSup P C c sample|} ⊆
      globalCenteredErrorEvent (m := m) P C c threshold := by
  intro sample hlarge
  have hnonneg := globalCenteredErrorSup_nonneg P C c sample hC
  change threshold < |globalCenteredErrorSup P C c sample| at hlarge
  rw [abs_of_nonneg hnonneg] at hlarge
  obtain ⟨y, hy, hty⟩ := exists_lt_of_lt_csSup
    (globalCenteredErrorValueSet_nonempty P C c sample hC) hlarge
  obtain ⟨h, hhC, rfl⟩ := hy
  exact ⟨h, hhC, hty⟩

/-- Global source-cut centered-error supremum. -/
noncomputable def globalSourceCutSup
    (P : Measure (ℝ × UnitMark)) {m : ℕ} (sample : Fin m → ℝ × UnitMark) : ℝ :=
  globalCenteredErrorSup P sourceCutClass falseCutTarget sample

/-- Global target-cut centered-error supremum. -/
noncomputable def globalTargetCutSup
    (P : Measure (ℝ × UnitMark)) {m : ℕ} (sample : Fin m → ℝ × UnitMark) : ℝ :=
  globalCenteredErrorSup P targetCutClass falseCutTarget sample

/-- Sum of the separate global source and target suprema. -/
noncomputable def globalJointCutSup
    (P : Measure (ℝ × UnitMark)) {m : ℕ} (sample : Fin m → ℝ × UnitMark) : ℝ :=
  globalSourceCutSup P sample + globalTargetCutSup P sample

theorem globalSourceCutSup_nonneg
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (sample : Fin m → ℝ × UnitMark) :
    0 ≤ globalSourceCutSup P sample :=
  globalCenteredErrorSup_nonneg P sourceCutClass falseCutTarget sample
    sourceCutClass_nonempty

theorem globalTargetCutSup_nonneg
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (sample : Fin m → ℝ × UnitMark) :
    0 ≤ globalTargetCutSup P sample :=
  globalCenteredErrorSup_nonneg P targetCutClass falseCutTarget sample
    targetCutClass_nonempty

/-- The global envelope dominates every source defect. -/
theorem abs_sourceCutDefect_le_globalSourceCutSup
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (sample : Fin m → ℝ × UnitMark) (p x : ℝ) :
    |sourceCutDefect P sample p x| ≤ globalSourceCutSup P sample := by
  rw [sourceCutDefect_eq_centeredErrorSum]
  exact abs_centeredErrorSum_le_globalCenteredErrorSup P sourceCutClass
    falseCutTarget sample ⟨p, x, rfl⟩

/-- The global envelope dominates every target defect. -/
theorem abs_targetCutDefect_le_globalTargetCutSup
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (sample : Fin m → ℝ × UnitMark) (p x : ℝ) :
    |targetCutDefect P sample p x| ≤ globalTargetCutSup P sample := by
  rw [targetCutDefect_eq_centeredErrorSum]
  exact abs_centeredErrorSum_le_globalCenteredErrorSup P targetCutClass
    falseCutTarget sample ⟨p, x, rfl⟩

/-- The joint global envelope dominates the paper's pointwise source-plus-target defect. -/
theorem sourceTargetCutDefect_sum_le_globalJointCutSup
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (sample : Fin m → ℝ × UnitMark) (p x : ℝ) :
    |sourceCutDefect P sample p x| + |targetCutDefect P sample p x| ≤
      globalJointCutSup P sample := by
  exact add_le_add
    (abs_sourceCutDefect_le_globalSourceCutSup P sample p x)
    (abs_targetCutDefect_le_globalTargetCutSup P sample p x)

/-- Source supremum tail in real-probability notation. -/
theorem sourceCut_globalSup_tail_le
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 0 < m) {q : ℝ} (hq : 0 < q) :
    (Measure.pi (fun _ : Fin m ↦ P)).real
        {sample | (q + 32) * Real.sqrt m < |globalSourceCutSup P sample|} ≤
      9416 / q := by
  let mu := Measure.pi (fun _ : Fin m ↦ P)
  have hsubset := globalCenteredErrorSup_largeEvent_subset (m := m)
    P sourceCutClass falseCutTarget sourceCutClass_nonempty
      ((q + 32) * Real.sqrt m)
  have henn :
      mu {sample | (q + 32) * Real.sqrt m < |globalSourceCutSup P sample|} ≤
        2 * ENNReal.ofReal (4708 / q) := by
    exact (measure_mono hsubset).trans
      (sourceCut_globalCenteredErrorEvent_measure_le P hm hq)
  have hfinite : 2 * ENNReal.ofReal (4708 / q) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  have hreal := ENNReal.toReal_mono hfinite henn
  have hratio0 : 0 ≤ 4708 / q := div_nonneg (by norm_num) hq.le
  change ENNReal.toReal
      (mu {sample | (q + 32) * Real.sqrt m < |globalSourceCutSup P sample|}) ≤
    9416 / q
  calc
    ENNReal.toReal
        (mu {sample | (q + 32) * Real.sqrt m < |globalSourceCutSup P sample|}) ≤
        ENNReal.toReal (2 * ENNReal.ofReal (4708 / q)) := hreal
    _ = 9416 / q := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hratio0]
      norm_num
      ring

/-- Target supremum tail in real-probability notation. -/
theorem targetCut_globalSup_tail_le
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 0 < m) {q : ℝ} (hq : 0 < q) :
    (Measure.pi (fun _ : Fin m ↦ P)).real
        {sample | (q + 32) * Real.sqrt m < |globalTargetCutSup P sample|} ≤
      9416 / q := by
  let mu := Measure.pi (fun _ : Fin m ↦ P)
  have hsubset := globalCenteredErrorSup_largeEvent_subset (m := m)
    P targetCutClass falseCutTarget targetCutClass_nonempty
      ((q + 32) * Real.sqrt m)
  have henn :
      mu {sample | (q + 32) * Real.sqrt m < |globalTargetCutSup P sample|} ≤
        2 * ENNReal.ofReal (4708 / q) := by
    exact (measure_mono hsubset).trans
      (targetCut_globalCenteredErrorEvent_measure_le P hm hq)
  have hfinite : 2 * ENNReal.ofReal (4708 / q) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  have hreal := ENNReal.toReal_mono hfinite henn
  have hratio0 : 0 ≤ 4708 / q := div_nonneg (by norm_num) hq.le
  change ENNReal.toReal
      (mu {sample | (q + 32) * Real.sqrt m < |globalTargetCutSup P sample|}) ≤
    9416 / q
  calc
    ENNReal.toReal
        (mu {sample | (q + 32) * Real.sqrt m < |globalTargetCutSup P sample|}) ≤
        ENNReal.toReal (2 * ENNReal.ofReal (4708 / q)) := hreal
    _ = 9416 / q := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hratio0]
      norm_num
      ring

/-- A large joint envelope forces one of the two component suprema to be large. -/
theorem globalJointCutSup_largeEvent_subset
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} {q : ℝ} :
    {sample : Fin m → ℝ × UnitMark |
      2 * (q + 32) * Real.sqrt m < |globalJointCutSup P sample|} ⊆
      {sample : Fin m → ℝ × UnitMark |
        (q + 32) * Real.sqrt m < |globalSourceCutSup P sample|} ∪
        {sample : Fin m → ℝ × UnitMark |
          (q + 32) * Real.sqrt m < |globalTargetCutSup P sample|} := by
  intro sample hlarge
  have hsource0 := globalSourceCutSup_nonneg P sample
  have htarget0 := globalTargetCutSup_nonneg P sample
  have hjoint0 : 0 ≤ globalJointCutSup P sample := by
    exact add_nonneg hsource0 htarget0
  change 2 * (q + 32) * Real.sqrt m < |globalJointCutSup P sample| at hlarge
  rw [abs_of_nonneg hjoint0] at hlarge
  by_contra hnot
  rw [Set.mem_union, not_or] at hnot
  have hsourceAbs :
      |globalSourceCutSup P sample| ≤ (q + 32) * Real.sqrt m := by
    simpa only [Set.mem_ofPred_eq, not_lt] using hnot.1
  have hsource : globalSourceCutSup P sample ≤ (q + 32) * Real.sqrt m := by
    rwa [abs_of_nonneg hsource0] at hsourceAbs
  have htargetAbs :
      |globalTargetCutSup P sample| ≤ (q + 32) * Real.sqrt m := by
    simpa only [Set.mem_ofPred_eq, not_lt] using hnot.2
  have htarget : globalTargetCutSup P sample ≤ (q + 32) * Real.sqrt m := by
    rwa [abs_of_nonneg htarget0] at htargetAbs
  dsimp [globalJointCutSup] at hlarge
  nlinarith

/-- Uniform inverse tail for the joint global source/target envelope. -/
theorem globalJointCutSup_tail_le
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 0 < m) {q : ℝ} (hq : 0 < q) :
    (Measure.pi (fun _ : Fin m ↦ P)).real
        {sample | 2 * (q + 32) * Real.sqrt m < |globalJointCutSup P sample|} ≤
      18832 / q := by
  let mu := Measure.pi (fun _ : Fin m ↦ P)
  let S := {sample : Fin m → ℝ × UnitMark |
    (q + 32) * Real.sqrt m < |globalSourceCutSup P sample|}
  let T := {sample : Fin m → ℝ × UnitMark |
    (q + 32) * Real.sqrt m < |globalTargetCutSup P sample|}
  have hsubset :
      {sample | 2 * (q + 32) * Real.sqrt m < |globalJointCutSup P sample|} ⊆ S ∪ T :=
    globalJointCutSup_largeEvent_subset P
  have hmono :
      mu.real {sample | 2 * (q + 32) * Real.sqrt m < |globalJointCutSup P sample|} ≤
        mu.real (S ∪ T) := measureReal_mono hsubset (measure_ne_top mu (S ∪ T))
  have hunion := measureReal_union_le (μ := mu) S T
  calc
    mu.real {sample | 2 * (q + 32) * Real.sqrt m < |globalJointCutSup P sample|} ≤
        mu.real (S ∪ T) := hmono
    _ ≤ mu.real S + mu.real T := hunion
    _ ≤ 9416 / q + 9416 / q := add_le_add
      (by simpa [mu, S] using sourceCut_globalSup_tail_le P hm hq)
      (by simpa [mu, T] using targetCut_globalSup_tail_le P hm hq)
    _ = 18832 / q := by ring

/-- Product law for the rank-strip sample in row `n`. -/
noncomputable def globalCutRowLaw (n : ℕ) : Measure (Fin n → ℝ × UnitMark) :=
  Measure.pi (fun _ : Fin n ↦ (rankStripLaw n : Measure (ℝ × UnitMark)))

/-- Equation (1.11): the global source-plus-target cut envelope is tight on scale `√n`. -/
theorem globalJointCutSup_isBigOInProbability :
    IsBigOInProbability globalCutRowLaw
      (fun n ↦ globalJointCutSup (rankStripLaw n : Measure (ℝ × UnitMark)))
      (fun n ↦ Real.sqrt n) := by
  intro ε hε
  let q : ℝ := max 1 (18832 / ε + 1)
  have hq : 1 ≤ q := le_max_left _ _
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let C : ℝ := 2 * (q + 32)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have htail := globalJointCutSup_tail_le
    (rankStripLaw n : Measure (ℝ × UnitMark)) hn hq0
  have hqLower : 18832 / ε + 1 ≤ q := le_max_right _ _
  have hratio : 18832 / q < ε := by
    rw [div_lt_iff₀ hq0]
    have hmul := mul_le_mul_of_nonneg_left hqLower hε.le
    field_simp at hmul
    nlinarith
  simpa [globalCutRowLaw, C] using htail.trans hratio.le

end OTSelector.RelativeVC
