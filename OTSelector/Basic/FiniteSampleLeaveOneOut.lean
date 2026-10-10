import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.FinCases
import OTSelector.Basic.FiniteSampleLaw

/-!
# Finite-sample leave-one-out coordinates

For a coordinate `(k, i)` we replace that scalar coordinate by the fixed point `0` and
leave every other scalar coordinate unchanged.  The product-coordinate independence theorem
in `FiniteSampleLaw` then gives independence of the resulting sample and the original replaced
coordinate.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

abbrev CoordinateIndex (n : ℕ) := Fin 4 × Fin n

/-- One of the four scalar coordinate families of a finite sample. -/
def coordinate (p : CoordinateIndex n) (sample : FiniteSample n) : UnitMark :=
  toFourArrays sample p.1 p.2

@[fun_prop]
theorem measurable_coordinate (p : CoordinateIndex n) :
    Measurable (coordinate p : FiniteSample n → UnitMark) :=
  measurable_fourArray n p.1 p.2

@[simp] theorem coordinate_sourceMark (i : Fin n) (sample : FiniteSample n) :
    coordinate (0, i) sample = sample.sourceMark i := by
  rfl

@[simp] theorem coordinate_sourceHeight (i : Fin n) (sample : FiniteSample n) :
    coordinate (1, i) sample = sample.sourceHeight i := by
  rfl

@[simp] theorem coordinate_targetMark (i : Fin n) (sample : FiniteSample n) :
    coordinate (2, i) sample = sample.targetMark i := by
  rfl

@[simp] theorem coordinate_targetHeight (i : Fin n) (sample : FiniteSample n) :
    coordinate (3, i) sample = sample.targetHeight i := by
  rfl

/-- Replace one scalar coordinate of a finite sample by `0`. -/
def coordinateLeaveOneOut (p : CoordinateIndex n) (sample : FiniteSample n) : FiniteSample n :=
  ofFourArrays (fun k j ↦ if (k, j) = p then (0 : UnitMark) else toFourArrays sample k j)

@[simp] theorem coordinateLeaveOneOut_coordinate_eq (p : CoordinateIndex n)
    (sample : FiniteSample n) :
    coordinate p (coordinateLeaveOneOut p sample) = (0 : UnitMark) := by
  simp [coordinateLeaveOneOut, coordinate]

theorem coordinateLeaveOneOut_coordinate_eq_of_ne (p q : CoordinateIndex n)
    (hqp : q ≠ p) (sample : FiniteSample n) :
    coordinate q (coordinateLeaveOneOut p sample) = coordinate q sample := by
  simp [coordinateLeaveOneOut, coordinate, hqp]

@[fun_prop]
theorem measurable_coordinateLeaveOneOut (p : CoordinateIndex n) :
    Measurable (coordinateLeaveOneOut p : FiniteSample n → FiniteSample n) := by
  refine measurable_ofFourArrays.comp ?_
  refine measurable_pi_lambda _ ?_
  intro k
  refine measurable_pi_lambda _ ?_
  intro j
  by_cases h : (k, j) = p
  · simp only [h]
    exact measurable_const
  · simp only [h]
    exact (measurable_pi_apply j).comp
      ((measurable_pi_apply k).comp FiniteSample.measurable_toFourArrays)

/-- Restore one scalar coordinate of a leave-one-out sample to an arbitrary value. -/
def coordinateRestore (p : CoordinateIndex n) (rest : FiniteSample n) (x : UnitMark) :
    FiniteSample n :=
  ofFourArrays (fun k j ↦ if (k, j) = p then x else toFourArrays rest k j)

@[fun_prop]
theorem measurable_coordinateRestore (p : CoordinateIndex n) :
    Measurable (fun z : FiniteSample n × UnitMark ↦
      coordinateRestore p z.1 z.2) := by
  refine measurable_ofFourArrays.comp ?_
  refine measurable_pi_lambda _ ?_
  intro k
  refine measurable_pi_lambda _ ?_
  intro j
  by_cases h : (k, j) = p
  · simp only [h]
    exact measurable_snd
  · simp only [h]
    exact (measurable_pi_apply j).comp
      ((measurable_pi_apply k).comp
        (FiniteSample.measurable_toFourArrays.comp measurable_fst))

@[simp] theorem coordinateRestore_coordinate_eq (p : CoordinateIndex n)
    (rest : FiniteSample n) (x : UnitMark) :
    coordinate p (coordinateRestore p rest x) = x := by
  simp [coordinateRestore, coordinate]

theorem coordinateRestore_coordinate_eq_of_ne (p q : CoordinateIndex n)
    (hqp : q ≠ p) (rest : FiniteSample n) (x : UnitMark) :
    coordinate q (coordinateRestore p rest x) = coordinate q rest := by
  simp [coordinateRestore, coordinate, hqp]

theorem coordinateRestore_coordinateLeaveOneOut (p : CoordinateIndex n)
    (sample : FiniteSample n) :
    coordinateRestore p (coordinateLeaveOneOut p sample) (coordinate p sample) = sample := by
  rw [← ofFourArrays_toFourArrays sample]
  apply congrArg ofFourArrays
  funext k j
  by_cases h : (k, j) = p
  · subst p
    simp [coordinate]
  · simp [coordinateLeaveOneOut, h]

theorem coordinateLeaveOneOut_coordinateRestore (p : CoordinateIndex n)
    (rest : FiniteSample n) (x : UnitMark) :
    coordinateLeaveOneOut p (coordinateRestore p rest x) =
      coordinateLeaveOneOut p rest := by
  apply congrArg ofFourArrays
  funext k j
  by_cases h : (k, j) = p
  · simp [h]
  · simp [coordinateRestore, h]

/-- The tuple of all scalar coordinates, used as the source of the product law. -/
def coordinateTuple (sample : FiniteSample n) : CoordinateIndex n → UnitMark :=
  fun p ↦ coordinate p sample

@[fun_prop]
theorem measurable_coordinateTuple :
    Measurable (coordinateTuple : FiniteSample n → CoordinateIndex n → UnitMark) := by
  exact measurable_pi_lambda _ (fun p ↦ measurable_coordinate p)

private def leaveOneOutFromOthers (p : CoordinateIndex n)
    (x : (Finset.univ.erase p) → UnitMark) : FiniteSample n :=
  ofFourArrays (fun k j ↦
    if h : (k, j) = p then (0 : UnitMark)
    else x ⟨(k, j), by simp [h]⟩)

@[fun_prop]
private theorem measurable_leaveOneOutFromOthers (p : CoordinateIndex n) :
    Measurable (leaveOneOutFromOthers p : (Finset.univ.erase p → UnitMark) → FiniteSample n) := by
  refine measurable_ofFourArrays.comp ?_
  refine measurable_pi_lambda _ ?_
  intro k
  refine measurable_pi_lambda _ ?_
  intro j
  by_cases h : (k, j) = p
  · simp only [h]
    exact measurable_const
  · simp only [h]
    have hmem : (k, j) ∈ Finset.univ.erase p := by simp [h]
    let q : (Finset.univ.erase p) := ⟨(k, j), hmem⟩
    exact measurable_pi_apply q

theorem coordinateLeaveOneOut_indepFun_coordinate (p : CoordinateIndex n) :
    IndepFun (coordinateLeaveOneOut p)
      (coordinate p) (finiteSampleLaw n : Measure (FiniteSample n)) := by
  let S : Finset (CoordinateIndex n) := Finset.univ.erase p
  let T : Finset (CoordinateIndex n) := {p}
  have hST : Disjoint S T := by
    simp [S, T]
  have htuple := (finiteSampleLaw_coordinates_iIndep n).indepFun_finset S T hST
    (fun q ↦ measurable_coordinate q)
  have hpT : p ∈ T := by simp [T]
  let pT : T := ⟨p, hpT⟩
  let ψ : (T → UnitMark) → UnitMark := fun x => x pT
  have hψ : Measurable ψ := measurable_pi_apply pT
  have hcomp := htuple.comp (measurable_leaveOneOutFromOthers p) hψ
  have hleft :
      (leaveOneOutFromOthers p) ∘
          (fun sample q ↦ FiniteSample.toFourArrays sample (q : CoordinateIndex n).1
            (q : CoordinateIndex n).2) =
        coordinateLeaveOneOut p := by
    funext sample
    simp only [Function.comp_apply]
    unfold leaveOneOutFromOthers coordinateLeaveOneOut
    apply congrArg ofFourArrays
    funext k j
    by_cases h : (k, j) = p
    · simp [h]
    · simp [h]
  have hright :
      ψ ∘ (fun sample q ↦ FiniteSample.toFourArrays sample (q : CoordinateIndex n).1
        (q : CoordinateIndex n).2) = coordinate p := by
    funext sample
    rfl
  rw [hleft, hright] at hcomp
  exact hcomp

theorem coordinate_marginal (p : CoordinateIndex n) :
    (finiteSampleLaw n).map (measurable_coordinate p).aemeasurable = unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (coordinate p) (finiteSampleLaw n : Measure (FiniteSample n)) =
    (unitUniform : Measure UnitMark)
  have hcoord : coordinate p =
      (fun array : SampleArray n ↦ array p.2) ∘
        (fun arrays : FourSampleArrays n ↦ arrays p.1) ∘ FiniteSample.toFourArrays := by
    funext sample
    rfl
  rw [hcoord]
  exact finiteSampleLaw_map_coordinate_measure n p.1 p.2

theorem coordinateLeaveOneOut_marginal_of_ne (p q : CoordinateIndex n) (hqp : q ≠ p) :
    (finiteSampleLaw n).map
        ((measurable_coordinate q).comp (measurable_coordinateLeaveOneOut p)).aemeasurable =
      unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (coordinate q ∘ coordinateLeaveOneOut p)
      (finiteSampleLaw n : Measure (FiniteSample n)) = (unitUniform : Measure UnitMark)
  rw [show (coordinate q ∘ coordinateLeaveOneOut p) = coordinate q by
    funext sample
    exact coordinateLeaveOneOut_coordinate_eq_of_ne p q hqp sample]
  exact congrArg ProbabilityMeasure.toMeasure (coordinate_marginal q)

def sourceHeightLeaveOneOut (i : Fin n) : FiniteSample n → FiniteSample n :=
  coordinateLeaveOneOut (1, i)

def targetHeightLeaveOneOut (i : Fin n) : FiniteSample n → FiniteSample n :=
  coordinateLeaveOneOut (3, i)

@[fun_prop]
theorem measurable_sourceHeightLeaveOneOut (i : Fin n) :
    Measurable (sourceHeightLeaveOneOut i : FiniteSample n → FiniteSample n) :=
  measurable_coordinateLeaveOneOut (1, i)

@[fun_prop]
theorem measurable_targetHeightLeaveOneOut (i : Fin n) :
    Measurable (targetHeightLeaveOneOut i : FiniteSample n → FiniteSample n) :=
  measurable_coordinateLeaveOneOut (3, i)

theorem sourceHeightLeaveOneOut_indepFun (i : Fin n) :
    IndepFun (sourceHeightLeaveOneOut i)
      (fun sample : FiniteSample n ↦ sample.sourceHeight i)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  change IndepFun (coordinateLeaveOneOut (1, i)) (coordinate (1, i))
    (finiteSampleLaw n : Measure (FiniteSample n))
  exact coordinateLeaveOneOut_indepFun_coordinate (n := n) (1, i)

theorem targetHeightLeaveOneOut_indepFun (i : Fin n) :
    IndepFun (targetHeightLeaveOneOut i)
      (fun sample : FiniteSample n ↦ sample.targetHeight i)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  change IndepFun (coordinateLeaveOneOut (3, i)) (coordinate (3, i))
    (finiteSampleLaw n : Measure (FiniteSample n))
  exact coordinateLeaveOneOut_indepFun_coordinate (n := n) (3, i)

theorem sourceHeight_marginal (i : Fin n) :
    (finiteSampleLaw n).map
        (FiniteSample.measurable_sourceHeight i).aemeasurable = unitUniform :=
  finiteSampleLaw_map_sourceHeight n i

theorem targetHeight_marginal (i : Fin n) :
    (finiteSampleLaw n).map
        (FiniteSample.measurable_targetHeight i).aemeasurable = unitUniform :=
  finiteSampleLaw_map_targetHeight n i

theorem sourceHeightLeaveOneOut_coordinate_marginal_of_ne (i j : Fin n) (hji : j ≠ i) :
    (finiteSampleLaw n).map
        ((FiniteSample.measurable_sourceHeight j).comp
          (measurable_sourceHeightLeaveOneOut i)).aemeasurable = unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  simpa [sourceHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using
    congrArg ProbabilityMeasure.toMeasure
      (coordinateLeaveOneOut_marginal_of_ne (n := n) (1, i) (1, j) (by simpa using hji))

theorem targetHeightLeaveOneOut_coordinate_marginal_of_ne (i j : Fin n) (hji : j ≠ i) :
    (finiteSampleLaw n).map
        ((FiniteSample.measurable_targetHeight j).comp
          (measurable_targetHeightLeaveOneOut i)).aemeasurable = unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  simpa [targetHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using
    congrArg ProbabilityMeasure.toMeasure
      (coordinateLeaveOneOut_marginal_of_ne (n := n) (3, i) (3, j) (by simpa using hji))

end FiniteSample

end OTSelector
