import OTSelector.Feedback.RelativeSymmetrization
import OTSelector.Feedback.SweptSets
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Radon
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# VC dimension of feature half-spaces

Radon's theorem gives a short reusable proof that affine half-spaces pulled back along any feature
map into a finite-dimensional real vector space have finite VC dimension.  The proof does not
assume that the feature map is injective; shattering itself forces the required affine
independence.
-/

open MeasureTheory
open scoped BigOperators

namespace OTSelector.RelativeVC

universe u v

/-- Boolean sublevel sets of linear functionals after a feature map. -/
def featureHalfspaceClass (Ω : Type u) (E : Type v) [AddCommGroup E] [Module ℝ E]
    (feature : Ω → E) : ConceptClass Ω Bool :=
  {h | ∃ (l : E →ₗ[ℝ] ℝ) (b : ℝ), h = fun x ↦ decide (l (feature x) ≤ b)}

theorem shatters_mono {Ω : Type u} {C D : ConceptClass Ω Bool} (hCD : C ⊆ D)
    {S : Finset Ω} (hS : Shatters Ω C S) : Shatters Ω D S := by
  intro label
  obtain ⟨h, hhC, hlabel⟩ := hS label
  exact ⟨h, hCD hhC, hlabel⟩

theorem vcdim_mono {Ω : Type u} {C D : ConceptClass Ω Bool} (hCD : C ⊆ D) :
    VCDim Ω C ≤ VCDim Ω D := by
  unfold VCDim
  refine iSup_le fun S ↦ iSup_le fun hS ↦ ?_
  have hSD := shatters_mono hCD hS
  exact le_iSup_of_le S (le_iSup_of_le hSD le_rfl)

theorem vcdim_le_of_shatters_imp {Ω : Type u} {C D : ConceptClass Ω Bool}
    (himp : ∀ S : Finset Ω, Shatters Ω C S → Shatters Ω D S) :
    VCDim Ω C ≤ VCDim Ω D := by
  unfold VCDim
  refine iSup_le fun S ↦ iSup_le fun hS ↦ ?_
  exact le_iSup_of_le S (le_iSup_of_le (himp S hS) le_rfl)

/-- Pointwise Boolean complements of a concept class. -/
def boolComplementClass {Ω : Type u} (C : ConceptClass Ω Bool) : ConceptClass Ω Bool :=
  {h | ∃ g ∈ C, h = fun x ↦ !g x}

theorem shatters_boolComplementClass_iff {Ω : Type u} (C : ConceptClass Ω Bool)
    (S : Finset Ω) :
    Shatters Ω (boolComplementClass C) S ↔ Shatters Ω C S := by
  constructor
  · intro hS label
    let negLabel : S → Bool := fun x ↦ !label x
    obtain ⟨_, ⟨g, hgC, rfl⟩, hrealize⟩ := hS negLabel
    refine ⟨g, hgC, ?_⟩
    intro x
    apply Bool.not_inj
    simpa [negLabel] using hrealize x
  · intro hS label
    let negLabel : S → Bool := fun x ↦ !label x
    obtain ⟨g, hgC, hrealize⟩ := hS negLabel
    refine ⟨fun x ↦ !g x, ⟨g, hgC, rfl⟩, ?_⟩
    intro x
    have := congrArg Bool.not (hrealize x)
    simpa [negLabel] using this

theorem vcdim_boolComplementClass {Ω : Type u} (C : ConceptClass Ω Bool) :
    VCDim Ω (boolComplementClass C) = VCDim Ω C := by
  apply le_antisymm
  · exact vcdim_le_of_shatters_imp fun S ↦ (shatters_boolComplementClass_iff C S).1
  · exact vcdim_le_of_shatters_imp fun S ↦ (shatters_boolComplementClass_iff C S).2

/-- A set shattered by feature half-spaces maps to an affinely independent family. -/
theorem affineIndependent_of_shatters_featureHalfspace
    {Ω : Type u} {E : Type v} [AddCommGroup E] [Module ℝ E]
    (feature : Ω → E) {S : Finset Ω}
    (hS : Shatters Ω (featureHalfspaceClass Ω E feature) S) :
    AffineIndependent ℝ (fun x : S ↦ feature x) := by
  classical
  by_contra hdep
  obtain ⟨I, p, hpI, hpIc⟩ := Convex.radon_partition hdep
  let label : S → Bool := fun x ↦ decide (x ∈ I)
  obtain ⟨h, hhClass, hlabel⟩ := hS label
  obtain ⟨l, b, rfl⟩ := hhClass
  have himage_le : (fun x : S ↦ feature x) '' I ⊆ {y : E | l y ≤ b} := by
    rintro y ⟨x, hxI, rfl⟩
    have hx := hlabel x
    have hright : label x = true := by simp [label, hxI]
    rw [hright] at hx
    exact decide_eq_true_eq.mp hx
  have himage_gt : (fun x : S ↦ feature x) '' Iᶜ ⊆ {y : E | b < l y} := by
    rintro y ⟨x, hxIc, rfl⟩
    have hxnot : x ∉ I := hxIc
    have hx := hlabel x
    have hright : label x = false := by simp [label, hxnot]
    rw [hright] at hx
    exact lt_of_not_ge (decide_eq_false_iff_not.mp hx)
  have hconvex_le : Convex ℝ {y : E | l y ≤ b} := by
    simpa only [Set.mem_ofPred_eq, Set.mem_univ, true_and] using
      (l.convexOn (convex_univ : Convex ℝ (Set.univ : Set E))).convex_le b
  have hconvex_gt : Convex ℝ {y : E | b < l y} := by
    simpa only [Set.mem_ofPred_eq, Set.mem_univ, true_and] using
      (l.concaveOn (convex_univ : Convex ℝ (Set.univ : Set E))).convex_gt b
  have hp_le : l p ≤ b := convexHull_min himage_le hconvex_le hpI
  have hp_gt : b < l p := convexHull_min himage_gt hconvex_gt hpIc
  exact (not_lt_of_ge hp_le) hp_gt

/-- Finite-dimensional feature half-spaces have VC dimension at most `finrank E + 1`. -/
theorem vcdim_featureHalfspace_le_finrank_succ
    (Ω : Type u) (E : Type v) [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    (feature : Ω → E) :
    VCDim Ω (featureHalfspaceClass Ω E feature) ≤
      (Module.finrank ℝ E + 1 : ℕ) := by
  unfold VCDim
  refine iSup_le fun S ↦ iSup_le fun hS ↦ ?_
  have hAI := affineIndependent_of_shatters_featureHalfspace feature hS
  have hcard : S.card ≤ Module.finrank ℝ E + 1 := by
    calc
      S.card = Fintype.card S := by simp
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range fun x : S ↦ feature x)) + 1 :=
        hAI.card_le_finrank_succ
      _ ≤ Module.finrank ℝ E + 1 := Nat.add_le_add_right (Submodule.finrank_le _) 1
  exact_mod_cast hcard

/-- In particular, finite-dimensional feature half-spaces have finite VC dimension. -/
theorem vcdim_featureHalfspace_finite
    (Ω : Type u) (E : Type v) [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    (feature : Ω → E) :
    VCDim Ω (featureHalfspaceClass Ω E feature) < ⊤ :=
  (vcdim_featureHalfspace_le_finrank_succ Ω E feature).trans_lt (WithTop.coe_lt_top _)

/-! ## Source and target cut families from `main.tex` -/

/-- Feature vector for source half-spaces: `(t, 1-u)`. -/
def sourceCutFeature (z : ℝ × UnitMark) : ℝ × ℝ := (z.1, 1 - (z.2 : ℝ))

/-- Feature vector for target half-spaces: `(s, 1+v)`. -/
def targetCutFeature (z : ℝ × UnitMark) : ℝ × ℝ := (z.1, 1 + (z.2 : ℝ))

/-- Source half-space class from equations (1.3)--(1.7). -/
def sourceCutClass : ConceptClass (ℝ × UnitMark) Bool :=
  {h | ∃ p x : ℝ, h = fun z ↦ decide (z.1 + p * (1 - (z.2 : ℝ)) ≤ x)}

/-- Target half-space class from equations (1.3)--(1.7). -/
def targetCutClass : ConceptClass (ℝ × UnitMark) Bool :=
  {h | ∃ p x : ℝ, h = fun z ↦ decide (z.1 - p * (1 + (z.2 : ℝ)) ≤ x)}

/-- Standard-Borel parameterization of the source cut class. -/
noncomputable def sourceCutEval (θ : ℝ × ℝ) : Concept (ℝ × UnitMark) Bool :=
  fun z ↦ decide (z.1 + θ.1 * (1 - (z.2 : ℝ)) ≤ θ.2)

/-- Standard-Borel parameterization of the target cut class. -/
noncomputable def targetCutEval (θ : ℝ × ℝ) : Concept (ℝ × UnitMark) Bool :=
  fun z ↦ decide (z.1 - θ.1 * (1 + (z.2 : ℝ)) ≤ θ.2)

def falseCutTarget : Concept (ℝ × UnitMark) Bool := fun _ ↦ false

def boolNotConcept {Ω : Type u} (h : Concept Ω Bool) : Concept Ω Bool := fun x ↦ !h x

@[simp] theorem errorSet_boolNot_false (h : Concept (ℝ × UnitMark) Bool) :
    errorSet (boolNotConcept h) falseCutTarget = (errorSet h falseCutTarget)ᶜ := by
  ext z
  cases hz : h z <;> simp [errorSet, boolNotConcept, falseCutTarget, hz]

private theorem zeroOneLoss_boolNot_false (b : Bool) :
    zeroOneLoss Bool (!b) false = 1 - zeroOneLoss Bool b false := by
  cases b <;> simp [zeroOneLoss]

theorem sampleErrorSum_boolNot_false {m : ℕ} (h : Concept (ℝ × UnitMark) Bool)
    (xs : Fin m → ℝ × UnitMark) :
    sampleErrorSum (boolNotConcept h) falseCutTarget xs =
      (m : ℝ) - sampleErrorSum h falseCutTarget xs := by
  simp only [sampleErrorSum, boolNotConcept, falseCutTarget, zeroOneLoss_boolNot_false,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

theorem centeredErrorSum_boolNot_false
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (h : Concept (ℝ × UnitMark) Bool)
    (hh : Measurable h) (xs : Fin m → ℝ × UnitMark) :
    centeredErrorSum P (boolNotConcept h) falseCutTarget xs =
      -centeredErrorSum P h falseCutTarget xs := by
  have hs : MeasurableSet (errorSet h falseCutTarget) :=
    measurableSet_errorSet hh measurable_const
  rw [centeredErrorSum, centeredErrorSum, sampleErrorSum_boolNot_false,
    errorSet_boolNot_false, measureReal_compl hs, probReal_univ]
  ring

theorem abs_centeredErrorSum_boolNot_false
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (h : Concept (ℝ × UnitMark) Bool)
    (hh : Measurable h) (xs : Fin m → ℝ × UnitMark) :
    |centeredErrorSum P (boolNotConcept h) falseCutTarget xs| =
      |centeredErrorSum P h falseCutTarget xs| := by
  rw [centeredErrorSum_boolNot_false P h hh xs, abs_neg]

/-- Complementing a Boolean cut preserves the absolute normalized empirical fluctuation. -/
theorem abs_empiricalProcess_boolNot_false
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 0 < m) (h : Concept (ℝ × UnitMark) Bool)
    (hh : Measurable h) (xs : Fin m → ℝ × UnitMark) :
    |EmpiricalProcess.empiricalProcess P m xs
        (indicatorReal (errorSet (boolNotConcept h) falseCutTarget))| =
      |EmpiricalProcess.empiricalProcess P m xs
        (indicatorReal (errorSet h falseCutTarget))| := by
  have hs : MeasurableSet (errorSet h falseCutTarget) :=
    measurableSet_errorSet hh measurable_const
  have hsnot : MeasurableSet (errorSet (boolNotConcept h) falseCutTarget) := by
    rw [errorSet_boolNot_false]
    exact hs.compl
  have hnot := centeredErrorSum_eq_sqrt_mul_empiricalProcess P hm
    (boolNotConcept h) falseCutTarget hsnot xs
  have horig := centeredErrorSum_eq_sqrt_mul_empiricalProcess P hm
    h falseCutTarget hs xs
  have habs := abs_centeredErrorSum_boolNot_false P h hh xs
  rw [hnot, horig, abs_mul, abs_mul] at habs
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hm)
  rw [abs_of_pos hsqrt] at habs
  exact mul_left_cancel₀ hsqrt.ne' habs

/-- Observed error count in the population-selected smaller orientation. -/
noncomputable def populationOrientedSampleErrorSum
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (h : Concept (ℝ × UnitMark) Bool) (xs : Fin m → ℝ × UnitMark) : ℝ :=
  if P.real (errorSet h falseCutTarget) ≤ 1 / 2 then
    sampleErrorSum h falseCutTarget xs
  else (m : ℝ) - sampleErrorSum h falseCutTarget xs

/-- Choose the set or its Boolean complement according to the smaller population mass.  The
centered count keeps the same absolute value, while the selected population mass is exactly
`balancedMass`. -/
theorem exists_balanced_orientation
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (C : ConceptClass (ℝ × UnitMark) Bool)
    {m : ℕ} (h : Concept (ℝ × UnitMark) Bool) (hhC : h ∈ C)
    (hh : Measurable h) (xs : Fin m → ℝ × UnitMark) :
    ∃ g ∈ C ∪ boolComplementClass C,
      P.real (errorSet g falseCutTarget) = balancedMass P (errorSet h falseCutTarget) ∧
      |centeredErrorSum P g falseCutTarget xs| =
        |centeredErrorSum P h falseCutTarget xs| ∧
      sampleErrorSum g falseCutTarget xs = populationOrientedSampleErrorSum P h xs := by
  have hs : MeasurableSet (errorSet h falseCutTarget) :=
    measurableSet_errorSet hh measurable_const
  have hcompl : P.real (errorSet h falseCutTarget)ᶜ =
      1 - P.real (errorSet h falseCutTarget) := by
    rw [measureReal_compl hs, probReal_univ]
  by_cases hp : P.real (errorSet h falseCutTarget) ≤ 1 / 2
  · refine ⟨h, Set.mem_union_left _ hhC, ?_, rfl, ?_⟩
    · rw [balancedMass, min_eq_left]
      rw [hcompl]
      linarith
    · rw [populationOrientedSampleErrorSum, ite_eq_left hp]
  · let g := boolNotConcept h
    refine ⟨g, Set.mem_union_right _ ⟨h, hhC, rfl⟩, ?_, ?_, ?_⟩
    · rw [show errorSet g falseCutTarget = (errorSet h falseCutTarget)ᶜ by
        exact errorSet_boolNot_false h]
      rw [balancedMass, min_eq_right]
      rw [hcompl]
      linarith
    · exact abs_centeredErrorSum_boolNot_false P h hh xs
    · rw [sampleErrorSum_boolNot_false]
      rw [populationOrientedSampleErrorSum, ite_eq_right hp]

/-- The balanced orientation also preserves the absolute normalized empirical process. -/
theorem exists_balanced_orientation_empirical
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (C : ConceptClass (ℝ × UnitMark) Bool)
    {m : ℕ} (hm : 0 < m) (h : Concept (ℝ × UnitMark) Bool) (hhC : h ∈ C)
    (hh : Measurable h) (xs : Fin m → ℝ × UnitMark) :
    ∃ g ∈ C ∪ boolComplementClass C,
      P.real (errorSet g falseCutTarget) = balancedMass P (errorSet h falseCutTarget) ∧
      |EmpiricalProcess.empiricalProcess P m xs
          (indicatorReal (errorSet g falseCutTarget))| =
        |EmpiricalProcess.empiricalProcess P m xs
          (indicatorReal (errorSet h falseCutTarget))| ∧
      sampleErrorSum g falseCutTarget xs = populationOrientedSampleErrorSum P h xs := by
  have hs : MeasurableSet (errorSet h falseCutTarget) :=
    measurableSet_errorSet hh measurable_const
  have hcompl : P.real (errorSet h falseCutTarget)ᶜ =
      1 - P.real (errorSet h falseCutTarget) := by
    rw [measureReal_compl hs, probReal_univ]
  by_cases hp : P.real (errorSet h falseCutTarget) ≤ 1 / 2
  · refine ⟨h, Set.mem_union_left _ hhC, ?_, rfl, ?_⟩
    · rw [balancedMass, min_eq_left]
      rw [hcompl]
      linarith
    · rw [populationOrientedSampleErrorSum, ite_eq_left hp]
  · let g := boolNotConcept h
    refine ⟨g, Set.mem_union_right _ ⟨h, hhC, rfl⟩, ?_, ?_, ?_⟩
    · rw [show errorSet g falseCutTarget = (errorSet h falseCutTarget)ᶜ by
        exact errorSet_boolNot_false h]
      rw [balancedMass, min_eq_right]
      rw [hcompl]
      linarith
    · exact abs_empiricalProcess_boolNot_false P hm h hh xs
    · rw [sampleErrorSum_boolNot_false]
      rw [populationOrientedSampleErrorSum, ite_eq_right hp]

/-- A relative-VC shell oriented by the smaller population side of every cut.  Its observed count
is oriented by the same population decision, so no sample-dependent choice is hidden in the event. -/
noncomputable def balancedLocalizedCutEvent
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (C : ConceptClass (ℝ × UnitMark) Bool)
    (x trueMassCap sampleMassCap : ℝ) : Set (Fin m → ℝ × UnitMark) :=
  {xs | ∃ h ∈ C,
    balancedMass P (errorSet h falseCutTarget) ≤ trueMassCap ∧
    x ≤ |EmpiricalProcess.empiricalProcess P m xs
      (indicatorReal (errorSet h falseCutTarget))| ∧
    populationOrientedSampleErrorSum P h xs ≤ sampleMassCap}

/-- Balanced shells reduce to the original class or its Boolean complement. -/
theorem balancedLocalizedCutEvent_subset_union
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (C : ConceptClass (ℝ × UnitMark) Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h)
    {m : ℕ} (hm : 0 < m) (x trueMassCap sampleMassCap : ℝ) :
    balancedLocalizedCutEvent (m := m) P C x trueMassCap sampleMassCap ⊆
      localizedRelativeVCEvent (m := m) P C falseCutTarget x trueMassCap sampleMassCap ∪
        localizedRelativeVCEvent (m := m) P (boolComplementClass C) falseCutTarget
          x trueMassCap sampleMassCap := by
  rintro xs ⟨h, hhC, hmass, hdev, hsample⟩
  obtain ⟨g, hg, hgmass, hgdev, hgsample⟩ :=
    exists_balanced_orientation_empirical P C hm h hhC (hmeas_C h hhC) xs
  have htrue : P.real (errorSet g falseCutTarget) ≤ trueMassCap := by
    rw [hgmass]
    exact hmass
  have hbad : x ≤ |EmpiricalProcess.empiricalProcess P m xs
      (indicatorReal (errorSet g falseCutTarget))| := by
    rw [hgdev]
    exact hdev
  have hcount : sampleErrorSum g falseCutTarget xs ≤ sampleMassCap := by
    rw [hgsample]
    exact hsample
  rcases hg with hgC | hgC
  · exact Set.mem_union_left _ ⟨g, hgC, htrue, hbad, hcount⟩
  · exact Set.mem_union_right _ ⟨g, hgC, htrue, hbad, hcount⟩

def sourceCutComplementClass : ConceptClass (ℝ × UnitMark) Bool :=
  boolComplementClass sourceCutClass

def targetCutComplementClass : ConceptClass (ℝ × UnitMark) Bool :=
  boolComplementClass targetCutClass

noncomputable def sourceCutComplementEval (θ : ℝ × ℝ) : Concept (ℝ × UnitMark) Bool :=
  fun z ↦ !(sourceCutEval θ z)

noncomputable def targetCutComplementEval (θ : ℝ × ℝ) : Concept (ℝ × UnitMark) Bool :=
  fun z ↦ !(targetCutEval θ z)

@[simp] theorem sourceCutEval_eq_true_iff_swept (p x : ℝ) (z : ℝ × UnitMark) :
    sourceCutEval (p, x) z = true ↔ z ∈ sourceSwept (fun _ ↦ p) x := by
  simp [sourceCutEval, sourceSwept]

@[simp] theorem targetCutEval_eq_true_iff_swept (p x : ℝ) (z : ℝ × UnitMark) :
    targetCutEval (p, x) z = true ↔ z ∈ targetSwept (fun _ ↦ p) x := by
  simp [targetCutEval, targetSwept]

theorem sourceCutClass_eq_range : sourceCutClass = Set.range sourceCutEval := by
  ext h
  constructor
  · rintro ⟨p, x, rfl⟩
    exact ⟨(p, x), rfl⟩
  · rintro ⟨⟨p, x⟩, rfl⟩
    exact ⟨p, x, rfl⟩

theorem targetCutClass_eq_range : targetCutClass = Set.range targetCutEval := by
  ext h
  constructor
  · rintro ⟨p, x, rfl⟩
    exact ⟨(p, x), rfl⟩
  · rintro ⟨⟨p, x⟩, rfl⟩
    exact ⟨p, x, rfl⟩

theorem sourceCutComplementClass_eq_range :
    sourceCutComplementClass = Set.range sourceCutComplementEval := by
  rw [sourceCutComplementClass, sourceCutClass_eq_range]
  ext h
  constructor
  · rintro ⟨_, ⟨θ, rfl⟩, rfl⟩
    exact ⟨θ, rfl⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨sourceCutEval θ, ⟨θ, rfl⟩, rfl⟩

theorem targetCutComplementClass_eq_range :
    targetCutComplementClass = Set.range targetCutComplementEval := by
  rw [targetCutComplementClass, targetCutClass_eq_range]
  ext h
  constructor
  · rintro ⟨_, ⟨θ, rfl⟩, rfl⟩
    exact ⟨θ, rfl⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨targetCutEval θ, ⟨θ, rfl⟩, rfl⟩

theorem measurable_sourceCutEval_joint :
    Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ sourceCutEval q.1 q.2) := by
  have ht : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  have hp : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ q.1.1) :=
    measurable_fst.comp measurable_fst
  have hu : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ (q.2.2 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hx : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ q.1.2) :=
    measurable_snd.comp measurable_fst
  have hleft : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦
      q.2.1 + q.1.1 * (1 - (q.2.2 : ℝ))) := ht.add (hp.mul (measurable_const.sub hu))
  change Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦
    if q.2.1 + q.1.1 * (1 - (q.2.2 : ℝ)) ≤ q.1.2 then true else false)
  exact Measurable.ite (measurableSet_le hleft hx) measurable_const measurable_const

theorem measurable_targetCutEval_joint :
    Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ targetCutEval q.1 q.2) := by
  have ht : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  have hp : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ q.1.1) :=
    measurable_fst.comp measurable_fst
  have hv : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ (q.2.2 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hx : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ q.1.2) :=
    measurable_snd.comp measurable_fst
  have hleft : Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦
      q.2.1 - q.1.1 * (1 + (q.2.2 : ℝ))) := ht.sub (hp.mul (measurable_const.add hv))
  change Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦
    if q.2.1 - q.1.1 * (1 + (q.2.2 : ℝ)) ≤ q.1.2 then true else false)
  exact Measurable.ite (measurableSet_le hleft hx) measurable_const measurable_const

theorem measurable_sourceCutComplementEval_joint :
    Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ sourceCutComplementEval q.1 q.2) := by
  exact (measurable_of_finite Bool.not).comp measurable_sourceCutEval_joint

theorem measurable_targetCutComplementEval_joint :
    Measurable (fun q : (ℝ × ℝ) × (ℝ × UnitMark) ↦ targetCutComplementEval q.1 q.2) := by
  exact (measurable_of_finite Bool.not).comp measurable_targetCutEval_joint

theorem measurable_falseCutTarget : Measurable falseCutTarget := measurable_const

noncomputable def sourceCutFunctional (p : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ ℝ + p • LinearMap.snd ℝ ℝ ℝ

noncomputable def targetCutFunctional (p : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ ℝ - p • LinearMap.snd ℝ ℝ ℝ

@[simp] theorem sourceCutFunctional_apply (p : ℝ) (z : ℝ × ℝ) :
    sourceCutFunctional p z = z.1 + p * z.2 := by
  simp [sourceCutFunctional]

@[simp] theorem targetCutFunctional_apply (p : ℝ) (z : ℝ × ℝ) :
    targetCutFunctional p z = z.1 - p * z.2 := by
  simp [targetCutFunctional]

theorem sourceCutClass_subset_featureHalfspace :
    sourceCutClass ⊆ featureHalfspaceClass (ℝ × UnitMark) (ℝ × ℝ) sourceCutFeature := by
  intro h hh
  obtain ⟨p, x, rfl⟩ := hh
  exact ⟨sourceCutFunctional p, x, by
    funext z
    simp [sourceCutFeature]⟩

theorem targetCutClass_subset_featureHalfspace :
    targetCutClass ⊆ featureHalfspaceClass (ℝ × UnitMark) (ℝ × ℝ) targetCutFeature := by
  intro h hh
  obtain ⟨p, x, rfl⟩ := hh
  exact ⟨targetCutFunctional p, x, by
    funext z
    simp [targetCutFeature]⟩

/-- The source cut class has VC dimension at most three. -/
theorem vcdim_sourceCutClass_le_three : VCDim (ℝ × UnitMark) sourceCutClass ≤ 3 := by
  calc
    VCDim (ℝ × UnitMark) sourceCutClass ≤
        VCDim (ℝ × UnitMark)
          (featureHalfspaceClass (ℝ × UnitMark) (ℝ × ℝ) sourceCutFeature) :=
      vcdim_mono sourceCutClass_subset_featureHalfspace
    _ ≤ (Module.finrank ℝ (ℝ × ℝ) + 1 : ℕ) :=
      vcdim_featureHalfspace_le_finrank_succ (ℝ × UnitMark) (ℝ × ℝ) sourceCutFeature
    _ = 3 := by norm_num [Module.finrank_prod]

/-- The target cut class has VC dimension at most three. -/
theorem vcdim_targetCutClass_le_three : VCDim (ℝ × UnitMark) targetCutClass ≤ 3 := by
  calc
    VCDim (ℝ × UnitMark) targetCutClass ≤
        VCDim (ℝ × UnitMark)
          (featureHalfspaceClass (ℝ × UnitMark) (ℝ × ℝ) targetCutFeature) :=
      vcdim_mono targetCutClass_subset_featureHalfspace
    _ ≤ (Module.finrank ℝ (ℝ × ℝ) + 1 : ℕ) :=
      vcdim_featureHalfspace_le_finrank_succ (ℝ × UnitMark) (ℝ × ℝ) targetCutFeature
    _ = 3 := by norm_num [Module.finrank_prod]

theorem vcdim_sourceCutClass_finite : VCDim (ℝ × UnitMark) sourceCutClass < ⊤ :=
  vcdim_sourceCutClass_le_three.trans_lt (WithTop.coe_lt_top 3)

theorem vcdim_targetCutClass_finite : VCDim (ℝ × UnitMark) targetCutClass < ⊤ :=
  vcdim_targetCutClass_le_three.trans_lt (WithTop.coe_lt_top 3)

theorem vcdim_sourceCutComplementClass_le_three :
    VCDim (ℝ × UnitMark) sourceCutComplementClass ≤ 3 := by
  rw [sourceCutComplementClass, vcdim_boolComplementClass]
  exact vcdim_sourceCutClass_le_three

theorem vcdim_targetCutComplementClass_le_three :
    VCDim (ℝ × UnitMark) targetCutComplementClass ≤ 3 := by
  rw [targetCutComplementClass, vcdim_boolComplementClass]
  exact vcdim_targetCutClass_le_three

/-- Every source cut is Borel measurable. -/
theorem measurable_sourceCutClass : ∀ h ∈ sourceCutClass, Measurable h := by
  intro h hh
  obtain ⟨p, x, rfl⟩ := hh
  have hf : Continuous (fun z : ℝ × UnitMark ↦ z.1 + p * (1 - (z.2 : ℝ))) :=
    continuous_fst.add (continuous_const.mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd)))
  have hs : MeasurableSet
      {z : ℝ × UnitMark | z.1 + p * (1 - (z.2 : ℝ)) ≤ x} :=
    (isClosed_le hf continuous_const).measurableSet
  change Measurable (fun z : ℝ × UnitMark ↦
    if z.1 + p * (1 - (z.2 : ℝ)) ≤ x then true else false)
  exact Measurable.ite hs measurable_const measurable_const

/-- Every target cut is Borel measurable. -/
theorem measurable_targetCutClass : ∀ h ∈ targetCutClass, Measurable h := by
  intro h hh
  obtain ⟨p, x, rfl⟩ := hh
  have hf : Continuous (fun z : ℝ × UnitMark ↦ z.1 - p * (1 + (z.2 : ℝ))) :=
    continuous_fst.sub (continuous_const.mul
      (continuous_const.add (continuous_subtype_val.comp continuous_snd)))
  have hs : MeasurableSet
      {z : ℝ × UnitMark | z.1 - p * (1 + (z.2 : ℝ)) ≤ x} :=
    (isClosed_le hf continuous_const).measurableSet
  change Measurable (fun z : ℝ × UnitMark ↦
    if z.1 - p * (1 + (z.2 : ℝ)) ≤ x then true else false)
  exact Measurable.ite hs measurable_const measurable_const

theorem measurable_sourceCutComplementClass :
    ∀ h ∈ sourceCutComplementClass, Measurable h := by
  rintro _ ⟨g, hg, rfl⟩
  exact (measurable_of_finite Bool.not).comp (measurable_sourceCutClass g hg)

theorem measurable_targetCutComplementClass :
    ∀ h ∈ targetCutComplementClass, Measurable h := by
  rintro _ ⟨g, hg, rfl⟩
  exact (measurable_of_finite Bool.not).comp (measurable_targetCutClass g hg)

/-- The source localized double-sample event is universally measurable; this is discharged from
the concrete `ℝ²` Borel parameterization rather than assumed. -/
theorem sourceCut_relativeDoubleSample_nullMeasurable
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (u varianceCap : ℝ) :
    NullMeasurableSet
      (relativeDoubleSampleEventProd sourceCutClass falseCutTarget u varianceCap)
      ((Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P))) := by
  rw [sourceCutClass_eq_range]
  exact relativeDoubleSampleEventProd_nullMeasurable_of_borelParam
    sourceCutEval measurable_sourceCutEval_joint falseCutTarget measurable_falseCutTarget
    P m u varianceCap

/-- The target localized double-sample event is universally measurable from its concrete Borel
parameterization. -/
theorem targetCut_relativeDoubleSample_nullMeasurable
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (u varianceCap : ℝ) :
    NullMeasurableSet
      (relativeDoubleSampleEventProd targetCutClass falseCutTarget u varianceCap)
      ((Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P))) := by
  rw [targetCutClass_eq_range]
  exact relativeDoubleSampleEventProd_nullMeasurable_of_borelParam
    targetCutEval measurable_targetCutEval_joint falseCutTarget measurable_falseCutTarget
    P m u varianceCap

theorem sourceCutComplement_relativeDoubleSample_nullMeasurable
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (u varianceCap : ℝ) :
    NullMeasurableSet
      (relativeDoubleSampleEventProd sourceCutComplementClass falseCutTarget u varianceCap)
      ((Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P))) := by
  rw [sourceCutComplementClass_eq_range]
  exact relativeDoubleSampleEventProd_nullMeasurable_of_borelParam
    sourceCutComplementEval measurable_sourceCutComplementEval_joint
    falseCutTarget measurable_falseCutTarget P m u varianceCap

theorem targetCutComplement_relativeDoubleSample_nullMeasurable
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (u varianceCap : ℝ) :
    NullMeasurableSet
      (relativeDoubleSampleEventProd targetCutComplementClass falseCutTarget u varianceCap)
      ((Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P))) := by
  rw [targetCutComplementClass_eq_range]
  exact relativeDoubleSampleEventProd_nullMeasurable_of_borelParam
    targetCutComplementEval measurable_targetCutComplementEval_joint
    falseCutTarget measurable_falseCutTarget P m u varianceCap

theorem sourceCut_growth_sauer :
    ∃ d : ℕ, ∀ m : ℕ, d ≤ m →
      GrowthFunction (ℝ × UnitMark) sourceCutClass m ≤
        ∑ i ∈ Finset.range (d + 1), Nat.choose m i :=
  vcdim_finite_imp_growth_bounded (ℝ × UnitMark) sourceCutClass
    vcdim_sourceCutClass_finite

theorem targetCut_growth_sauer :
    ∃ d : ℕ, ∀ m : ℕ, d ≤ m →
      GrowthFunction (ℝ × UnitMark) targetCutClass m ≤
        ∑ i ∈ Finset.range (d + 1), Nat.choose m i :=
  vcdim_finite_imp_growth_bounded (ℝ × UnitMark) targetCutClass
    vcdim_targetCutClass_finite

/-- Source-family specialization of the localized relative-VC Bernstein theorem.  VC finiteness,
hypothesis measurability, and analytic-event null measurability are all concrete theorems. -/
theorem sourceCut_localized_relative_vc_bernstein
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m)
    (x trueMassCap sampleMassCap : ℝ) (hx : 0 < x)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp (-((x / 2) ^ 2) /
          (4 * (trueMassCap + (x / 2) / Real.sqrt m)))) ≤ (1 : ENNReal) / 2)
    (hvarianceCap :
      0 < sampleMassCap + (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        (localizedRelativeVCEvent P sourceCutClass falseCutTarget
          x trueMassCap sampleMassCap) ≤
      2 * ENNReal.ofReal
        (2 * (GrowthFunction (ℝ × UnitMark) sourceCutClass (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
            (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
              Real.sqrt m * (x / 2))))) := by
  exact localized_relative_vc_bernstein P sourceCutClass falseCutTarget
    measurable_sourceCutClass measurable_falseCutTarget m hm x trueMassCap sampleMassCap hx
    hghostBernstein hvarianceCap
    (sourceCut_relativeDoubleSample_nullMeasurable P m _ _)

/-- Target-family specialization of the localized relative-VC Bernstein theorem. -/
theorem targetCut_localized_relative_vc_bernstein
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m)
    (x trueMassCap sampleMassCap : ℝ) (hx : 0 < x)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp (-((x / 2) ^ 2) /
          (4 * (trueMassCap + (x / 2) / Real.sqrt m)))) ≤ (1 : ENNReal) / 2)
    (hvarianceCap :
      0 < sampleMassCap + (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        (localizedRelativeVCEvent P targetCutClass falseCutTarget
          x trueMassCap sampleMassCap) ≤
      2 * ENNReal.ofReal
        (2 * (GrowthFunction (ℝ × UnitMark) targetCutClass (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
            (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
              Real.sqrt m * (x / 2))))) := by
  exact localized_relative_vc_bernstein P targetCutClass falseCutTarget
    measurable_targetCutClass measurable_falseCutTarget m hm x trueMassCap sampleMassCap hx
    hghostBernstein hvarianceCap
    (targetCut_relativeDoubleSample_nullMeasurable P m _ _)

theorem sourceCutComplement_localized_relative_vc_bernstein
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m)
    (x trueMassCap sampleMassCap : ℝ) (hx : 0 < x)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp (-((x / 2) ^ 2) /
          (4 * (trueMassCap + (x / 2) / Real.sqrt m)))) ≤ (1 : ENNReal) / 2)
    (hvarianceCap :
      0 < sampleMassCap + (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        (localizedRelativeVCEvent P sourceCutComplementClass falseCutTarget
          x trueMassCap sampleMassCap) ≤
      2 * ENNReal.ofReal
        (2 * (GrowthFunction (ℝ × UnitMark) sourceCutComplementClass (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
            (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
              Real.sqrt m * (x / 2))))) := by
  exact localized_relative_vc_bernstein P sourceCutComplementClass falseCutTarget
    measurable_sourceCutComplementClass measurable_falseCutTarget
    m hm x trueMassCap sampleMassCap hx hghostBernstein hvarianceCap
    (sourceCutComplement_relativeDoubleSample_nullMeasurable P m _ _)

theorem targetCutComplement_localized_relative_vc_bernstein
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m)
    (x trueMassCap sampleMassCap : ℝ) (hx : 0 < x)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp (-((x / 2) ^ 2) /
          (4 * (trueMassCap + (x / 2) / Real.sqrt m)))) ≤ (1 : ENNReal) / 2)
    (hvarianceCap :
      0 < sampleMassCap + (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        (localizedRelativeVCEvent P targetCutComplementClass falseCutTarget
          x trueMassCap sampleMassCap) ≤
      2 * ENNReal.ofReal
        (2 * (GrowthFunction (ℝ × UnitMark) targetCutComplementClass (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
            (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
              Real.sqrt m * (x / 2))))) := by
  exact localized_relative_vc_bernstein P targetCutComplementClass falseCutTarget
    measurable_targetCutComplementClass measurable_falseCutTarget
    m hm x trueMassCap sampleMassCap hx hghostBernstein hvarianceCap
    (targetCutComplement_relativeDoubleSample_nullMeasurable P m _ _)

/-- Source cuts localized by the smaller side of each half-space.  The two summands are the
original and complemented VC classes; hence the orientation step introduces no auxiliary proof
input. -/
theorem sourceCut_balanced_localized_relative_vc_bernstein
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m)
    (x trueMassCap sampleMassCap : ℝ) (hx : 0 < x)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp (-((x / 2) ^ 2) /
          (4 * (trueMassCap + (x / 2) / Real.sqrt m)))) ≤ (1 : ENNReal) / 2)
    (hvarianceCap :
      0 < sampleMassCap + (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        (balancedLocalizedCutEvent P sourceCutClass x trueMassCap sampleMassCap) ≤
      2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * (x / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * (x / 2))))) := by
  let μ := Measure.pi (fun _ : Fin m ↦ P)
  let A := localizedRelativeVCEvent (m := m) P sourceCutClass falseCutTarget
    x trueMassCap sampleMassCap
  let B := localizedRelativeVCEvent (m := m) P sourceCutComplementClass falseCutTarget
    x trueMassCap sampleMassCap
  calc
    μ (balancedLocalizedCutEvent P sourceCutClass x trueMassCap sampleMassCap)
        ≤ μ (A ∪ B) := measure_mono
          (balancedLocalizedCutEvent_subset_union P sourceCutClass
            measurable_sourceCutClass hm x trueMassCap sampleMassCap)
    _ ≤ μ A + μ B := measure_union_le A B
    _ ≤ 2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * (x / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * (x / 2))))) := by
      exact add_le_add
        (sourceCut_localized_relative_vc_bernstein P m hm x trueMassCap sampleMassCap
          hx hghostBernstein hvarianceCap)
        (sourceCutComplement_localized_relative_vc_bernstein P m hm x trueMassCap sampleMassCap
          hx hghostBernstein hvarianceCap)

/-- Target-cut counterpart of `sourceCut_balanced_localized_relative_vc_bernstein`. -/
theorem targetCut_balanced_localized_relative_vc_bernstein
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m)
    (x trueMassCap sampleMassCap : ℝ) (hx : 0 < x)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp (-((x / 2) ^ 2) /
          (4 * (trueMassCap + (x / 2) / Real.sqrt m)))) ≤ (1 : ENNReal) / 2)
    (hvarianceCap :
      0 < sampleMassCap + (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        (balancedLocalizedCutEvent P targetCutClass x trueMassCap sampleMassCap) ≤
      2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * (x / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * (x / 2))))) := by
  let μ := Measure.pi (fun _ : Fin m ↦ P)
  let A := localizedRelativeVCEvent (m := m) P targetCutClass falseCutTarget
    x trueMassCap sampleMassCap
  let B := localizedRelativeVCEvent (m := m) P targetCutComplementClass falseCutTarget
    x trueMassCap sampleMassCap
  calc
    μ (balancedLocalizedCutEvent P targetCutClass x trueMassCap sampleMassCap)
        ≤ μ (A ∪ B) := measure_mono
          (balancedLocalizedCutEvent_subset_union P targetCutClass
            measurable_targetCutClass hm x trueMassCap sampleMassCap)
    _ ≤ μ A + μ B := measure_union_le A B
    _ ≤ 2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * (x / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
              (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
                Real.sqrt m * (x / 2))))) := by
      exact add_le_add
        (targetCut_localized_relative_vc_bernstein P m hm x trueMassCap sampleMassCap
          hx hghostBernstein hvarianceCap)
        (targetCutComplement_localized_relative_vc_bernstein P m hm x trueMassCap sampleMassCap
          hx hghostBernstein hvarianceCap)

/-- Source cut family: finite localized peeling with analytic measurability discharged. -/
theorem sourceCut_finite_localized_relative_vc_peeling
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m) (K : ℕ)
    (threshold trueMassCap sampleMassCap : Fin K → ℝ)
    (hthreshold : ∀ k, 0 < threshold k)
    (hghostBernstein : ∀ k,
      ENNReal.ofReal
        (2 * Real.exp (-((threshold k / 2) ^ 2) /
          (4 * (trueMassCap k + (threshold k / 2) / Real.sqrt m)))) ≤
        (1 : ENNReal) / 2)
    (hvarianceCap : ∀ k,
      0 < sampleMassCap k + (m : ℝ) * trueMassCap k +
        Real.sqrt m * (threshold k / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        {xs | ∃ k : Fin K,
          xs ∈ localizedRelativeVCEvent P sourceCutClass falseCutTarget (threshold k)
            (trueMassCap k) (sampleMassCap k)} ≤
      ∑ k : Fin K, 2 * ENNReal.ofReal
        (2 * (GrowthFunction (ℝ × UnitMark) sourceCutClass (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
            (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
              Real.sqrt m * (threshold k / 2))))) := by
  rw [sourceCutClass_eq_range]
  exact finite_localized_relative_vc_peeling_of_borelParam
    sourceCutEval measurable_sourceCutEval_joint falseCutTarget measurable_falseCutTarget
    P m hm K threshold trueMassCap sampleMassCap hthreshold hghostBernstein hvarianceCap

/-- Target cut family: finite localized peeling with analytic measurability discharged. -/
theorem targetCut_finite_localized_relative_vc_peeling
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m) (K : ℕ)
    (threshold trueMassCap sampleMassCap : Fin K → ℝ)
    (hthreshold : ∀ k, 0 < threshold k)
    (hghostBernstein : ∀ k,
      ENNReal.ofReal
        (2 * Real.exp (-((threshold k / 2) ^ 2) /
          (4 * (trueMassCap k + (threshold k / 2) / Real.sqrt m)))) ≤
        (1 : ENNReal) / 2)
    (hvarianceCap : ∀ k,
      0 < sampleMassCap k + (m : ℝ) * trueMassCap k +
        Real.sqrt m * (threshold k / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        {xs | ∃ k : Fin K,
          xs ∈ localizedRelativeVCEvent P targetCutClass falseCutTarget (threshold k)
            (trueMassCap k) (sampleMassCap k)} ≤
      ∑ k : Fin K, 2 * ENNReal.ofReal
        (2 * (GrowthFunction (ℝ × UnitMark) targetCutClass (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
            (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
              Real.sqrt m * (threshold k / 2))))) := by
  rw [targetCutClass_eq_range]
  exact finite_localized_relative_vc_peeling_of_borelParam
    targetCutEval measurable_targetCutEval_joint falseCutTarget measurable_falseCutTarget
    P m hm K threshold trueMassCap sampleMassCap hthreshold hghostBernstein hvarianceCap

/-- Finite peeling for source half-spaces after orienting every shell by its smaller side. -/
theorem sourceCut_finite_balanced_relative_vc_peeling
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m) (K : ℕ)
    (threshold trueMassCap sampleMassCap : Fin K → ℝ)
    (hthreshold : ∀ k, 0 < threshold k)
    (hghostBernstein : ∀ k,
      ENNReal.ofReal
        (2 * Real.exp (-((threshold k / 2) ^ 2) /
          (4 * (trueMassCap k + (threshold k / 2) / Real.sqrt m)))) ≤
        (1 : ENNReal) / 2)
    (hvarianceCap : ∀ k,
      0 < sampleMassCap k + (m : ℝ) * trueMassCap k +
        Real.sqrt m * (threshold k / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        {xs | ∃ k : Fin K,
          xs ∈ balancedLocalizedCutEvent P sourceCutClass (threshold k)
            (trueMassCap k) (sampleMassCap k)} ≤
      ∑ k : Fin K,
        (2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
              (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
                Real.sqrt m * (threshold k / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
              (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
                Real.sqrt m * (threshold k / 2)))))) := by
  let μ := Measure.pi (fun _ : Fin m ↦ P)
  let event : Fin K → Set (Fin m → ℝ × UnitMark) := fun k ↦
    balancedLocalizedCutEvent P sourceCutClass (threshold k)
      (trueMassCap k) (sampleMassCap k)
  have hsubset : {xs | ∃ k : Fin K, xs ∈ event k} ⊆ ⋃ k, event k := by
    rintro xs ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  calc
    μ {xs | ∃ k : Fin K, xs ∈ event k} ≤ μ (⋃ k, event k) := measure_mono hsubset
    _ ≤ ∑ k : Fin K, μ (event k) := by
      simpa using measure_iUnion_le (μ := μ) event
    _ ≤ ∑ k : Fin K,
        (2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
              (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
                Real.sqrt m * (threshold k / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) sourceCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
              (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
                Real.sqrt m * (threshold k / 2)))))) := by
      exact Finset.sum_le_sum fun k _ ↦
        sourceCut_balanced_localized_relative_vc_bernstein P m hm
          (threshold k) (trueMassCap k) (sampleMassCap k)
          (hthreshold k) (hghostBernstein k) (hvarianceCap k)

/-- Finite peeling for target half-spaces after orienting every shell by its smaller side. -/
theorem targetCut_finite_balanced_relative_vc_peeling
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m) (K : ℕ)
    (threshold trueMassCap sampleMassCap : Fin K → ℝ)
    (hthreshold : ∀ k, 0 < threshold k)
    (hghostBernstein : ∀ k,
      ENNReal.ofReal
        (2 * Real.exp (-((threshold k / 2) ^ 2) /
          (4 * (trueMassCap k + (threshold k / 2) / Real.sqrt m)))) ≤
        (1 : ENNReal) / 2)
    (hvarianceCap : ∀ k,
      0 < sampleMassCap k + (m : ℝ) * trueMassCap k +
        Real.sqrt m * (threshold k / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        {xs | ∃ k : Fin K,
          xs ∈ balancedLocalizedCutEvent P targetCutClass (threshold k)
            (trueMassCap k) (sampleMassCap k)} ≤
      ∑ k : Fin K,
        (2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
              (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
                Real.sqrt m * (threshold k / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
              (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
                Real.sqrt m * (threshold k / 2)))))) := by
  let μ := Measure.pi (fun _ : Fin m ↦ P)
  let event : Fin K → Set (Fin m → ℝ × UnitMark) := fun k ↦
    balancedLocalizedCutEvent P targetCutClass (threshold k)
      (trueMassCap k) (sampleMassCap k)
  have hsubset : {xs | ∃ k : Fin K, xs ∈ event k} ⊆ ⋃ k, event k := by
    rintro xs ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  calc
    μ {xs | ∃ k : Fin K, xs ∈ event k} ≤ μ (⋃ k, event k) := measure_mono hsubset
    _ ≤ ∑ k : Fin K, μ (event k) := by
      simpa using measure_iUnion_le (μ := μ) event
    _ ≤ ∑ k : Fin K,
        (2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
              (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
                Real.sqrt m * (threshold k / 2))))) +
        2 * ENNReal.ofReal
          (2 * (GrowthFunction (ℝ × UnitMark) targetCutComplementClass (2 * m) : ℝ) *
            Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
              (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
                Real.sqrt m * (threshold k / 2)))))) := by
      exact Finset.sum_le_sum fun k _ ↦
        targetCut_balanced_localized_relative_vc_bernstein P m hm
          (threshold k) (trueMassCap k) (sampleMassCap k)
          (hthreshold k) (hghostBernstein k) (hvarianceCap k)

end OTSelector.RelativeVC
