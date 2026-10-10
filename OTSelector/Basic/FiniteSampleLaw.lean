import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.FinCases
import OTSelector.Basic.ModelLaw

/-!
# The canonical finite-sample law

This file puts the four coordinate arrays of `FiniteSample n` on their canonical product
measurable space.  The probability law is the pushforward of four independent product laws of
`unitUniform`; all statements below are consequences of that construction.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

abbrev SampleArray (n : ℕ) := Fin n → UnitMark

abbrev FourSampleArrays (n : ℕ) := Fin 4 → SampleArray n

namespace FiniteSample

variable {n : ℕ}

/-- The four coordinate arrays, in the order source mark, source height, target mark, target
height. -/
def toFourArrays (sample : FiniteSample n) : FourSampleArrays n :=
  ![sample.sourceMark, sample.sourceHeight, sample.targetMark, sample.targetHeight]

/-- Reconstruct a finite sample from four coordinate arrays. -/
def ofFourArrays (arrays : FourSampleArrays n) : FiniteSample n :=
  { sourceMark := arrays 0
    sourceHeight := arrays 1
    targetMark := arrays 2
    targetHeight := arrays 3 }

@[simp] theorem ofFourArrays_toFourArrays (sample : FiniteSample n) :
    ofFourArrays (toFourArrays sample) = sample := by
  cases sample
  rfl

@[simp] theorem toFourArrays_ofFourArrays (arrays : FourSampleArrays n) :
    toFourArrays (ofFourArrays arrays) = arrays := by
  funext k
  fin_cases k <;> rfl

/-- The explicit coding equivalence between finite samples and four coordinate arrays. -/
def finiteSampleEquiv (n : ℕ) : FiniteSample n ≃ FourSampleArrays n where
  toFun := toFourArrays
  invFun := ofFourArrays
  left_inv := ofFourArrays_toFourArrays
  right_inv := toFourArrays_ofFourArrays

noncomputable instance instMeasurableSpace : MeasurableSpace (FiniteSample n) :=
  MeasurableSpace.comap (finiteSampleEquiv n) inferInstance

/-- The coding equivalence is measurable in both directions for the canonical sample space. -/
noncomputable def finiteSampleMeasurableEquiv (n : ℕ) :
    FiniteSample n ≃ᵐ FourSampleArrays n where
  toEquiv := finiteSampleEquiv n
  measurable_toFun := comap_measurable (finiteSampleEquiv n)
  measurable_invFun := by
    rw [measurable_comap_iff]
    convert measurable_id using 1
    funext arrays
    exact (finiteSampleEquiv n).right_inv arrays

theorem toFourArrays_comp_symm :
    (toFourArrays : FiniteSample n → FourSampleArrays n) ∘
      (finiteSampleMeasurableEquiv n).symm = id := by
  funext arrays
  exact (finiteSampleMeasurableEquiv n).right_inv arrays

theorem ofFourArrays_comp_toFourArrays :
    (finiteSampleMeasurableEquiv n).symm ∘
      (toFourArrays : FiniteSample n → FourSampleArrays n) = id := by
  funext sample
  exact (finiteSampleMeasurableEquiv n).left_inv sample

@[fun_prop]
theorem measurable_toFourArrays :
    Measurable (toFourArrays : FiniteSample n → FourSampleArrays n) :=
  (finiteSampleMeasurableEquiv n).measurable

@[fun_prop]
theorem measurable_ofFourArrays :
    Measurable (ofFourArrays : FourSampleArrays n → FiniteSample n) :=
  (finiteSampleMeasurableEquiv n).symm.measurable

@[fun_prop]
theorem measurable_sourceMark (i : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.sourceMark i) := by
  have h := (measurable_pi_apply i).comp
    ((measurable_pi_apply (0 : Fin 4)).comp measurable_toFourArrays)
  convert h using 1; rfl

@[fun_prop]
theorem measurable_sourceHeight (i : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.sourceHeight i) := by
  have h := (measurable_pi_apply i).comp
    ((measurable_pi_apply (1 : Fin 4)).comp measurable_toFourArrays)
  convert h using 1; rfl

@[fun_prop]
theorem measurable_targetMark (i : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.targetMark i) := by
  have h := (measurable_pi_apply i).comp
    ((measurable_pi_apply (2 : Fin 4)).comp measurable_toFourArrays)
  convert h using 1; rfl

@[fun_prop]
theorem measurable_targetHeight (i : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ sample.targetHeight i) := by
  have h := (measurable_pi_apply i).comp
    ((measurable_pi_apply (3 : Fin 4)).comp measurable_toFourArrays)
  convert h using 1; rfl

private theorem standardBorelSpace_of_measurableEquiv {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] (e : A ≃ᵐ B) :
    StandardBorelSpace A := by
  let _ := upgradeStandardBorel B
  let topologyA : TopologicalSpace A := TopologicalSpace.induced e inferInstance
  let _ : TopologicalSpace A := topologyA
  let _ : PolishSpace A := e.toEquiv.polishSpace_induced
  let _ : BorelSpace A := e.measurableEmbedding.borelSpace ⟨rfl⟩
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩⟩

noncomputable instance instStandardBorelSpace : StandardBorelSpace (FiniteSample n) :=
  standardBorelSpace_of_measurableEquiv (finiteSampleMeasurableEquiv n)

end FiniteSample

section CanonicalLaw

variable (n : ℕ)

/-- The iid `unitUniform` law on one coordinate array. -/
noncomputable def unitUniformArrayLaw : ProbabilityMeasure (SampleArray n) :=
  ProbabilityMeasure.pi (fun _ : Fin n ↦ unitUniform)

/-- The product law of the four independent coordinate arrays. -/
noncomputable def fourUnitUniformArrayLaw : ProbabilityMeasure (FourSampleArrays n) :=
  ProbabilityMeasure.pi (fun _ : Fin 4 ↦ unitUniformArrayLaw n)

theorem fourUnitUniformArrayLaw_toMeasure :
    (fourUnitUniformArrayLaw n : Measure (FourSampleArrays n)) =
      Measure.pi fun _ : Fin 4 ↦ (unitUniformArrayLaw n : Measure (SampleArray n)) :=
  rfl

theorem unitUniformArrayLaw_toMeasure :
    (unitUniformArrayLaw n : Measure (SampleArray n)) =
      Measure.pi fun _ : Fin n ↦ (unitUniform : Measure UnitMark) :=
  rfl

/-- The canonical law of a finite sample with four independent iid unit-uniform families. -/
noncomputable def finiteSampleLaw : ProbabilityMeasure (FiniteSample n) :=
  ProbabilityMeasure.map (fourUnitUniformArrayLaw n)
    (FiniteSample.finiteSampleMeasurableEquiv n).symm.measurable.aemeasurable

@[simp] theorem finiteSampleLaw_toMeasure :
    (finiteSampleLaw n : Measure (FiniteSample n)) =
      Measure.map (FiniteSample.finiteSampleMeasurableEquiv n).symm
        (fourUnitUniformArrayLaw n : Measure (FourSampleArrays n)) := by
  rw [finiteSampleLaw, ProbabilityMeasure.toMeasure_map]

theorem finiteSampleLaw_map_toFourArrays_measure :
    Measure.map FiniteSample.toFourArrays (finiteSampleLaw n : Measure (FiniteSample n)) =
      (fourUnitUniformArrayLaw n : Measure (FourSampleArrays n)) := by
  rw [finiteSampleLaw_toMeasure]
  rw [Measure.map_map FiniteSample.measurable_toFourArrays
      (FiniteSample.finiteSampleMeasurableEquiv n).symm.measurable]
  rw [FiniteSample.toFourArrays_comp_symm, Measure.map_id]

theorem finiteSampleLaw_map_toFourArrays :
    (finiteSampleLaw n).map FiniteSample.measurable_toFourArrays.aemeasurable =
      fourUnitUniformArrayLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  exact finiteSampleLaw_map_toFourArrays_measure n

theorem finiteSampleLaw_map_array_measure (k : Fin 4) :
    Measure.map ((fun arrays : FourSampleArrays n ↦ arrays k) ∘ FiniteSample.toFourArrays)
        (finiteSampleLaw n : Measure (FiniteSample n)) =
      (unitUniformArrayLaw n : Measure (SampleArray n)) := by
  rw [← Measure.map_map (measurable_pi_apply k) FiniteSample.measurable_toFourArrays,
    finiteSampleLaw_map_toFourArrays_measure]
  exact (measurePreserving_eval
    (fun _ : Fin 4 ↦ (unitUniformArrayLaw n : Measure (SampleArray n))) k).map_eq

theorem finiteSampleLaw_map_array (k : Fin 4) :
    (finiteSampleLaw n).map
        ((measurable_pi_apply k).comp FiniteSample.measurable_toFourArrays).aemeasurable =
      unitUniformArrayLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  exact finiteSampleLaw_map_array_measure n k

theorem finiteSampleLaw_map_coordinate_measure (k : Fin 4) (i : Fin n) :
    Measure.map ((fun array : SampleArray n ↦ array i) ∘
        (fun arrays : FourSampleArrays n ↦ arrays k) ∘ FiniteSample.toFourArrays)
        (finiteSampleLaw n : Measure (FiniteSample n)) =
      (unitUniform : Measure UnitMark) := by
  rw [← Measure.map_map (measurable_pi_apply i)
      ((measurable_pi_apply k).comp FiniteSample.measurable_toFourArrays),
    finiteSampleLaw_map_array_measure]
  exact (measurePreserving_eval
    (fun _ : Fin n ↦ (unitUniform : Measure UnitMark)) i).map_eq

theorem finiteSampleLaw_map_sourceMark (i : Fin n) :
    (finiteSampleLaw n).map (FiniteSample.measurable_sourceMark i).aemeasurable = unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  have hfun : (fun sample : FiniteSample n ↦ sample.sourceMark i) =
      (fun array : SampleArray n ↦ array i) ∘
        (fun arrays : FourSampleArrays n ↦ arrays 0) ∘ FiniteSample.toFourArrays := by
    funext sample
    rfl
  change Measure.map (fun sample : FiniteSample n ↦ sample.sourceMark i)
      (finiteSampleLaw n : Measure (FiniteSample n)) = (unitUniform : Measure UnitMark)
  rw [hfun]
  exact finiteSampleLaw_map_coordinate_measure n (0 : Fin 4) i

theorem finiteSampleLaw_map_sourceHeight (i : Fin n) :
    (finiteSampleLaw n).map (FiniteSample.measurable_sourceHeight i).aemeasurable =
      unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  have hfun : (fun sample : FiniteSample n ↦ sample.sourceHeight i) =
      (fun array : SampleArray n ↦ array i) ∘
        (fun arrays : FourSampleArrays n ↦ arrays 1) ∘ FiniteSample.toFourArrays := by
    funext sample
    rfl
  change Measure.map (fun sample : FiniteSample n ↦ sample.sourceHeight i)
      (finiteSampleLaw n : Measure (FiniteSample n)) = (unitUniform : Measure UnitMark)
  rw [hfun]
  exact finiteSampleLaw_map_coordinate_measure n (1 : Fin 4) i

theorem finiteSampleLaw_map_targetMark (i : Fin n) :
    (finiteSampleLaw n).map (FiniteSample.measurable_targetMark i).aemeasurable = unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  have hfun : (fun sample : FiniteSample n ↦ sample.targetMark i) =
      (fun array : SampleArray n ↦ array i) ∘
        (fun arrays : FourSampleArrays n ↦ arrays 2) ∘ FiniteSample.toFourArrays := by
    funext sample
    rfl
  change Measure.map (fun sample : FiniteSample n ↦ sample.targetMark i)
      (finiteSampleLaw n : Measure (FiniteSample n)) = (unitUniform : Measure UnitMark)
  rw [hfun]
  exact finiteSampleLaw_map_coordinate_measure n (2 : Fin 4) i

theorem finiteSampleLaw_map_targetHeight (i : Fin n) :
    (finiteSampleLaw n).map (FiniteSample.measurable_targetHeight i).aemeasurable =
      unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  have hfun : (fun sample : FiniteSample n ↦ sample.targetHeight i) =
      (fun array : SampleArray n ↦ array i) ∘
        (fun arrays : FourSampleArrays n ↦ arrays 3) ∘ FiniteSample.toFourArrays := by
    funext sample
    rfl
  change Measure.map (fun sample : FiniteSample n ↦ sample.targetHeight i)
      (finiteSampleLaw n : Measure (FiniteSample n)) = (unitUniform : Measure UnitMark)
  rw [hfun]
  exact finiteSampleLaw_map_coordinate_measure n (3 : Fin 4) i

@[fun_prop]
theorem measurable_fourArray (k : Fin 4) (i : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ FiniteSample.toFourArrays sample k i) :=
  (measurable_pi_apply i).comp
    ((measurable_pi_apply k).comp FiniteSample.measurable_toFourArrays)

/-- The four coordinate arrays are independent under the canonical sample law. -/
theorem finiteSampleLaw_arrays_iIndep :
    iIndepFun (fun k (sample : FiniteSample n) ↦ FiniteSample.toFourArrays sample k)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  refine (iIndepFun_iff_map_fun_eq_pi_map
    (fun k ↦ ((measurable_pi_apply k).comp FiniteSample.measurable_toFourArrays).aemeasurable)).2 ?_
  change Measure.map FiniteSample.toFourArrays
      (finiteSampleLaw n : Measure (FiniteSample n)) =
    Measure.pi fun k : Fin 4 ↦
      Measure.map ((fun arrays : FourSampleArrays n ↦ arrays k) ∘ FiniteSample.toFourArrays)
        (finiteSampleLaw n : Measure (FiniteSample n))
  rw [finiteSampleLaw_map_toFourArrays_measure, fourUnitUniformArrayLaw_toMeasure]
  congr 1
  funext k
  exact (finiteSampleLaw_map_array_measure n k).symm

theorem finiteSampleLaw_family_iIndep (k : Fin 4) :
    iIndepFun (fun i (sample : FiniteSample n) ↦ FiniteSample.toFourArrays sample k i)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  refine (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ (measurable_fourArray n k i).aemeasurable)).2 ?_
  have hjoint :
      Measure.map ((fun arrays : FourSampleArrays n ↦ arrays k) ∘ FiniteSample.toFourArrays)
          (finiteSampleLaw n : Measure (FiniteSample n)) =
        Measure.map (fun sample i ↦ FiniteSample.toFourArrays sample k i)
          (finiteSampleLaw n : Measure (FiniteSample n)) :=
    rfl
  rw [← hjoint, finiteSampleLaw_map_array_measure, unitUniformArrayLaw_toMeasure]
  congr 1
  funext i
  exact (finiteSampleLaw_map_coordinate_measure n k i).symm

theorem finiteSampleLaw_sourceMark_iIndep :
    iIndepFun (fun i (sample : FiniteSample n) ↦ sample.sourceMark i)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  simpa [FiniteSample.toFourArrays] using
    (finiteSampleLaw_family_iIndep n (0 : Fin 4))

theorem finiteSampleLaw_sourceHeight_iIndep :
    iIndepFun (fun i (sample : FiniteSample n) ↦ sample.sourceHeight i)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  simpa [FiniteSample.toFourArrays] using
    (finiteSampleLaw_family_iIndep n (1 : Fin 4))

theorem finiteSampleLaw_targetMark_iIndep :
    iIndepFun (fun i (sample : FiniteSample n) ↦ sample.targetMark i)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  simpa [FiniteSample.toFourArrays] using
    (finiteSampleLaw_family_iIndep n (2 : Fin 4))

theorem finiteSampleLaw_targetHeight_iIndep :
    iIndepFun (fun i (sample : FiniteSample n) ↦ sample.targetHeight i)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  simpa [FiniteSample.toFourArrays] using
    (finiteSampleLaw_family_iIndep n (3 : Fin 4))

/-- Nested product measures uncurry to a single product over the index pair. -/
theorem map_uncurry_nested_pi {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    Measure.map (fun (x : ι → κ → α) (p : ι × κ) ↦ x p.1 p.2)
      (Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ μ) =
      Measure.pi fun _ : ι × κ ↦ μ := by
  have hmeas : Measurable (fun (x : ι → κ → α) (p : ι × κ) ↦ x p.1 p.2) :=
    measurable_pi_lambda _ fun p ↦
      (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre :
      (fun (x : ι → κ → α) (p : ι × κ) ↦ x p.1 p.2) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun k ↦ Set.univ.pi fun i ↦ s (k, i) := by
    ext x
    simp
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  calc
    (∏ k : ι, ∏ i : κ, μ (s (k, i))) =
        ∏ p ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset κ), μ (s p) :=
      (Finset.prod_product _ _ (fun p : ι × κ ↦ μ (s p))).symm
    _ = ∏ p : ι × κ, μ (s p) := by rw [Finset.univ_product_univ]

/-- All `4n` scalar coordinates are jointly independent under the canonical sample law. -/
theorem finiteSampleLaw_coordinates_iIndep :
    iIndepFun (fun p : Fin 4 × Fin n ↦ fun sample : FiniteSample n ↦
        FiniteSample.toFourArrays sample p.1 p.2)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  refine (iIndepFun_iff_map_fun_eq_pi_map
    (fun p : Fin 4 × Fin n ↦ (measurable_fourArray n p.1 p.2).aemeasurable)).2 ?_
  have huncurry :
      Measure.map (fun sample : FiniteSample n ↦
          fun p : Fin 4 × Fin n ↦ FiniteSample.toFourArrays sample p.1 p.2)
        (finiteSampleLaw n : Measure (FiniteSample n)) =
      Measure.map (fun (x : FourSampleArrays n) (p : Fin 4 × Fin n) ↦ x p.1 p.2)
        (Measure.map FiniteSample.toFourArrays
          (finiteSampleLaw n : Measure (FiniteSample n))) := by
    rw [Measure.map_map]
    · rfl
    · exact measurable_pi_lambda _ fun p ↦
        (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
    · exact FiniteSample.measurable_toFourArrays
  rw [huncurry, finiteSampleLaw_map_toFourArrays_measure, fourUnitUniformArrayLaw_toMeasure]
  simp_rw [unitUniformArrayLaw_toMeasure]
  have hrhs :
      (Measure.pi fun i : Fin 4 × Fin n ↦
        Measure.map (fun sample : FiniteSample n ↦ sample.toFourArrays i.1 i.2)
          (finiteSampleLaw n : Measure (FiniteSample n))) =
        Measure.pi fun _ ↦ (unitUniform : Measure UnitMark) := by
    congr 1
    funext p
    exact finiteSampleLaw_map_coordinate_measure n p.1 p.2
  rw [hrhs]
  exact map_uncurry_nested_pi (unitUniform : Measure UnitMark)

end CanonicalLaw

end OTSelector
