import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.FinCases
import LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.Independence.Basic
import OTSelector.Basic.FiniteSampleLaw

/-!
# The canonical finite-sample point law

The four scalar coordinates of `FiniteSample` are grouped below into the marked source and target
points.  The point product law is derived from the already-proved scalar product law; no extra
postulate is introduced.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

/-- The canonical product-uniform law on one marked point `(height, mark)`. -/
noncomputable def unitSquareUniform : ProbabilityMeasure MarkedHeight :=
  ProbabilityMeasure.prod unitUniform unitUniform

@[simp] theorem unitSquareUniform_toMeasure :
    (unitSquareUniform : Measure MarkedHeight) =
      (unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark) :=
  rfl

/-! ## A small product-law helper -/

/-- The inverse direction of `map_uncurry_nested_pi`. -/
theorem map_curry_nested_pi {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    Measure.map (fun (x : ι × κ → α) (i : ι) (j : κ) ↦ x (i, j))
      (Measure.pi fun _ : ι × κ ↦ μ) =
      Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ μ := by
  let uncurry : (ι → κ → α) → (ι × κ → α) := fun x p ↦ x p.1 p.2
  let curry : (ι × κ → α) → (ι → κ → α) := fun x i j ↦ x (i, j)
  have huncurry := map_uncurry_nested_pi (ι := ι) (κ := κ) (α := α) μ
  have hmeas_uncurry : Measurable uncurry := by
    exact measurable_pi_lambda _ fun p ↦
      (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hmeas_curry : Measurable curry := by
    exact measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦
      measurable_pi_apply (i, j)
  have hcomp : curry ∘ uncurry = id := by
    funext x
    rfl
  rw [← huncurry]
  rw [Measure.map_map hmeas_curry hmeas_uncurry, hcomp, Measure.map_id]

/-! ## Labels, scalar blocks, and measurable point maps -/

/-- A two-colour label: `0` is source and `1` is target. -/
abbrev PointLabel (n : ℕ) := Fin 2 × Fin n

/-- The four-array scalar coordinate attached to a label in `Fin 4 × Fin n`. -/
def scalarCoordinate (q : Fin 4 × Fin n) (sample : FiniteSample n) : UnitMark :=
  FiniteSample.toFourArrays sample q.1 q.2

@[fun_prop]
theorem measurable_scalarCoordinate (q : Fin 4 × Fin n) :
    Measurable (scalarCoordinate q : FiniteSample n → UnitMark) :=
  measurable_fourArray n q.1 q.2

def pointLabelHeightCoordinate (p : PointLabel n) : Fin 4 × Fin n :=
  ![((1 : Fin 4), p.2), ((3 : Fin 4), p.2)] p.1

def pointLabelMarkCoordinate (p : PointLabel n) : Fin 4 × Fin n :=
  ![((0 : Fin 4), p.2), ((2 : Fin 4), p.2)] p.1

def pointBlock (p : PointLabel n) : Finset (Fin 4 × Fin n) :=
  {pointLabelHeightCoordinate p, pointLabelMarkCoordinate p}

theorem pointBlock_pairwiseDisjoint :
    Set.PairwiseDisjoint Set.univ (pointBlock (n := n)) := by
  intro p _ q _ hpq
  change Disjoint (pointBlock p) (pointBlock q)
  rcases p with ⟨c, i⟩
  rcases q with ⟨d, j⟩
  fin_cases c <;> fin_cases d <;>
    simp [pointBlock, pointLabelHeightCoordinate, pointLabelMarkCoordinate] at hpq ⊢ <;>
    exact Ne.symm hpq

def pointLabelCoordinate (p : PointLabel n) (sample : FiniteSample n) : MarkedHeight :=
  (scalarCoordinate (pointLabelHeightCoordinate p) sample,
    scalarCoordinate (pointLabelMarkCoordinate p) sample)

@[fun_prop]
theorem measurable_pointLabelCoordinate (p : PointLabel n) :
    Measurable (pointLabelCoordinate p : FiniteSample n → MarkedHeight) :=
  (measurable_scalarCoordinate (pointLabelHeightCoordinate p)).prodMk
    (measurable_scalarCoordinate (pointLabelMarkCoordinate p))

/-- The two-colour point array, in `(height, mark)` order. -/
def pointArray (sample : FiniteSample n) : Fin 2 → Fin n → MarkedHeight :=
  fun c i ↦ pointLabelCoordinate (c, i) sample

@[simp] theorem pointArray_zero (sample : FiniteSample n) (i : Fin n) :
    pointArray sample 0 i = FiniteSample.sourcePoint sample i := by
  rfl

@[simp] theorem pointArray_one (sample : FiniteSample n) (i : Fin n) :
    pointArray sample 1 i = FiniteSample.targetPoint sample i := by
  rfl

@[fun_prop]
theorem measurable_pointArray :
    Measurable (pointArray : FiniteSample n → Fin 2 → Fin n → MarkedHeight) := by
  exact measurable_pi_lambda _ fun c ↦ measurable_pi_lambda _ fun i ↦
    measurable_pointLabelCoordinate (c, i)

@[fun_prop]
theorem measurable_pointArray_coordinate (c : Fin 2) (i : Fin n) :
    Measurable (fun sample : FiniteSample n ↦ pointArray sample c i) :=
  measurable_pointLabelCoordinate (c, i)

/-! ## Point marginals -/

theorem finiteSampleLaw_map_scalarCoordinate_measure (q : Fin 4 × Fin n) :
    Measure.map (scalarCoordinate q) (finiteSampleLaw n : Measure (FiniteSample n)) =
      (unitUniform : Measure UnitMark) := by
  have hfun : scalarCoordinate q =
      (fun array : SampleArray n ↦ array q.2) ∘
        (fun arrays : FourSampleArrays n ↦ arrays q.1) ∘ FiniteSample.toFourArrays := by
    rfl
  rw [hfun]
  exact finiteSampleLaw_map_coordinate_measure n q.1 q.2

theorem finiteSampleLaw_map_scalarCoordinate (q : Fin 4 × Fin n) :
    (finiteSampleLaw n).map (measurable_scalarCoordinate q).aemeasurable = unitUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  exact finiteSampleLaw_map_scalarCoordinate_measure q

theorem finiteSampleLaw_map_pointLabel (p : PointLabel n) :
    (finiteSampleLaw n).map (measurable_pointLabelCoordinate p).aemeasurable =
      unitSquareUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (pointLabelCoordinate p) (finiteSampleLaw n : Measure (FiniteSample n)) =
    (unitSquareUniform : Measure MarkedHeight)
  have hpair := (finiteSampleLaw_coordinates_iIndep n).indepFun
    (f := fun q ↦ scalarCoordinate q)
    (i := pointLabelHeightCoordinate p) (j := pointLabelMarkCoordinate p)
    (by
      intro h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      rcases p with ⟨c, i⟩
      fin_cases c <;>
        simp [pointLabelHeightCoordinate, pointLabelMarkCoordinate] at h₁ h₂)
  have hmap := hpair.map_prod_eq_prod_map_map
    (measurable_scalarCoordinate (pointLabelHeightCoordinate p)).aemeasurable
    (measurable_scalarCoordinate (pointLabelMarkCoordinate p)).aemeasurable
  change Measure.map (fun sample : FiniteSample n ↦
      (scalarCoordinate (pointLabelHeightCoordinate p) sample,
        scalarCoordinate (pointLabelMarkCoordinate p) sample))
      (finiteSampleLaw n : Measure (FiniteSample n)) =
    (unitSquareUniform : Measure MarkedHeight)
  rw [hmap, finiteSampleLaw_map_scalarCoordinate_measure,
    finiteSampleLaw_map_scalarCoordinate_measure]
  rfl

/-! ## Joint independence of all labelled points -/

theorem finiteSampleLaw_pointLabels_iIndep :
    iIndepFun (fun p : PointLabel n ↦
      fun sample : FiniteSample n ↦ pointLabelCoordinate p sample)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  let S : PointLabel n → Finset (Fin 4 × Fin n) := pointBlock
  let φ : (p : PointLabel n) → ((q : S p) → UnitMark) → MarkedHeight :=
    fun p x ↦
      (x ⟨pointLabelHeightCoordinate p, by simp [S, pointBlock]⟩,
        x ⟨pointLabelMarkCoordinate p, by simp [S, pointBlock]⟩)
  have hφ : ∀ p, Measurable (φ p) := by
    intro p
    exact (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have h := (finiteSampleLaw_coordinates_iIndep n).finsets_comp
    S (by simpa [S] using (pointBlock_pairwiseDisjoint (n := n)))
    (fun q ↦ measurable_scalarCoordinate q)
    φ hφ
  simpa [φ, S, pointLabelCoordinate, scalarCoordinate] using h

theorem finiteSampleLaw_pointLabels_map_measure :
    Measure.map
        (fun sample : FiniteSample n ↦
          fun p : PointLabel n ↦ pointLabelCoordinate p sample)
        (finiteSampleLaw n : Measure (FiniteSample n)) =
      Measure.pi fun _ : PointLabel n ↦ (unitSquareUniform : Measure MarkedHeight) := by
  have h := finiteSampleLaw_pointLabels_iIndep (n := n)
  have hmap := h.map_fun_eq_pi_map
    (fun p ↦ (measurable_pointLabelCoordinate p).aemeasurable)
  rw [hmap]
  congr 1
  funext p
  exact congrArg ProbabilityMeasure.toMeasure (finiteSampleLaw_map_pointLabel p)

theorem finiteSampleLaw_pointLabels_map :
    (finiteSampleLaw n).map
        (measurable_pi_lambda _ fun p ↦ measurable_pointLabelCoordinate p).aemeasurable =
      ProbabilityMeasure.pi fun _ : PointLabel n ↦ unitSquareUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  exact finiteSampleLaw_pointLabels_map_measure (n := n)

/-! ## Nested point-array law and coordinate marginals -/

noncomputable def pointArrayLaw (n : ℕ) :
    ProbabilityMeasure (Fin 2 → Fin n → MarkedHeight) :=
  ProbabilityMeasure.pi fun _ : Fin 2 ↦ ProbabilityMeasure.pi fun _ : Fin n ↦ unitSquareUniform

theorem finiteSampleLaw_map_pointArray_measure :
    Measure.map (pointArray : FiniteSample n → Fin 2 → Fin n → MarkedHeight)
        (finiteSampleLaw n : Measure (FiniteSample n)) =
      Measure.pi fun _ : Fin 2 ↦
        Measure.pi fun _ : Fin n ↦ (unitSquareUniform : Measure MarkedHeight) := by
  let curry : (PointLabel n → MarkedHeight) → Fin 2 → Fin n → MarkedHeight :=
    fun x c i ↦ x (c, i)
  have hcurry : Measurable curry := by
    exact measurable_pi_lambda _ fun c ↦ measurable_pi_lambda _ fun i ↦
      measurable_pi_apply (c, i)
  have hcomp : pointArray = curry ∘
      (fun sample : FiniteSample n ↦
        fun p : PointLabel n ↦ pointLabelCoordinate p sample) := by
    funext sample c i
    rfl
  have hflat : Measurable (fun sample : FiniteSample n ↦
      fun p : PointLabel n ↦ pointLabelCoordinate p sample) := by
    exact measurable_pi_lambda _ fun p ↦ measurable_pointLabelCoordinate p
  rw [hcomp, ← Measure.map_map hcurry hflat]
  rw [finiteSampleLaw_pointLabels_map_measure (n := n)]
  exact map_curry_nested_pi (unitSquareUniform : Measure MarkedHeight)

theorem finiteSampleLaw_map_pointArray :
    (finiteSampleLaw n).map measurable_pointArray.aemeasurable = pointArrayLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  exact finiteSampleLaw_map_pointArray_measure (n := n)

theorem finiteSampleLaw_map_pointArray_coordinate (c : Fin 2) (i : Fin n) :
    (finiteSampleLaw n).map (measurable_pointArray_coordinate c i).aemeasurable =
      unitSquareUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun sample : FiniteSample n ↦ pointArray sample c i)
      (finiteSampleLaw n : Measure (FiniteSample n)) =
      (unitSquareUniform : Measure MarkedHeight)
  have hfun : (fun sample : FiniteSample n ↦ pointArray sample c i) =
      (fun z : Fin 2 → Fin n → MarkedHeight ↦ z c i) ∘ pointArray := by
    rfl
  have h_eval : Measurable (fun z : Fin 2 → Fin n → MarkedHeight ↦ z c i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply c)
  have h_eval' : (fun z : Fin 2 → Fin n → MarkedHeight ↦ z c i) =
      (fun f : Fin n → MarkedHeight ↦ f i) ∘
        (fun z : Fin 2 → Fin n → MarkedHeight ↦ z c) := by
    rfl
  rw [hfun, ← Measure.map_map h_eval measurable_pointArray,
    finiteSampleLaw_map_pointArray_measure (n := n), h_eval',
    ← Measure.map_map (measurable_pi_apply i) (measurable_pi_apply c)]
  rw [(measurePreserving_eval
    (fun _ : Fin 2 ↦ (Measure.pi fun _ : Fin n ↦
      (unitSquareUniform : Measure MarkedHeight))) c).map_eq]
  exact (measurePreserving_eval
    (fun _ : Fin n ↦ (unitSquareUniform : Measure MarkedHeight)) i).map_eq

theorem finiteSampleLaw_pointArray_coordinates_iIndep :
    iIndepFun (fun p : PointLabel n ↦
      fun sample : FiniteSample n ↦ pointArray sample p.1 p.2)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  simpa [pointArray] using finiteSampleLaw_pointLabels_iIndep (n := n)

end OTSelector
