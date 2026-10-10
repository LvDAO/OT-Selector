import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Finite ordered point clouds

This file gives finite marked samples a concrete measurable carrier.  A cloud consists of a
length and a point at each index below that length.  Its measurable structure is pulled back from
the canonical padded code

`(n, x) : ℕ × (ℕ → Option X)`,

where `x k` is present exactly when `k < n`.  The ambient code is standard Borel whenever `X` is,
and the canonical codes form a measurable subset.  This avoids putting a measurable structure on
an unordered quotient before such a quotient is needed.

Equality of `FinitePointCloud` values remembers the enumeration.  Thus this carrier is suitable
for finite samples and integer-cell codes, but it is not itself an unordered point-configuration
carrier.  The `toMultiset` projection below forgets the order without asserting a standard Borel
measurable structure on the multiset quotient.
-/

open Set

namespace OTSelector.PointProcess

/-- A finite ordered cloud, represented by its length and its indexed points. -/
@[ext]
structure FinitePointCloud (X : Type*) where
  card : ℕ
  point : Fin card → X

namespace FinitePointCloud

variable {X Y Z : Type*}

/-- The standard-Borel ambient space used to encode finite clouds. -/
abbrev PaddedCode (X : Type*) := ℕ × (ℕ → Option X)

/-- The `k`-th point, padded by `none` outside the finite range. -/
def point? (cloud : FinitePointCloud X) (k : ℕ) : Option X :=
  if hk : k < cloud.card then some (cloud.point ⟨k, hk⟩) else none

@[simp]
theorem point?_of_lt (cloud : FinitePointCloud X) {k : ℕ} (hk : k < cloud.card) :
    cloud.point? k = some (cloud.point ⟨k, hk⟩) := by
  simp [point?, hk]

@[simp]
theorem point?_of_ge (cloud : FinitePointCloud X) {k : ℕ} (hk : cloud.card ≤ k) :
    cloud.point? k = none := by
  simp [point?, Nat.not_lt.mpr hk]

/-- A finite cloud as a padded sequence. -/
def paddedCode (cloud : FinitePointCloud X) : PaddedCode X :=
  (cloud.card, cloud.point?)

/-- A padded code is canonical when its present coordinates are exactly its initial segment. -/
def IsCanonical (code : PaddedCode X) : Prop :=
  ∀ k, (code.2 k).isSome = true ↔ k < code.1

@[simp]
theorem isCanonical_paddedCode (cloud : FinitePointCloud X) :
    IsCanonical cloud.paddedCode := by
  intro k
  simp only [paddedCode, point?]
  split_ifs with hk
  · simp [hk]
  · simp [hk]

theorem paddedCode_injective : Function.Injective (paddedCode (X := X)) := by
  rintro ⟨n, x⟩ ⟨m, y⟩ hcode
  have hcard : n = m := congr_arg Prod.fst hcode
  subst m
  have hpoints :
      (fun k ↦ (FinitePointCloud.mk n x).point? k) =
        fun k ↦ (FinitePointCloud.mk n y).point? k :=
    congr_arg Prod.snd hcode
  congr 1
  funext i
  have hi := congr_fun hpoints i
  simpa [point?, i.isLt] using hi

theorem range_paddedCode :
    range (paddedCode (X := X)) = {code | IsCanonical code} := by
  ext code
  constructor
  · rintro ⟨cloud, rfl⟩
    exact isCanonical_paddedCode cloud
  · intro hcode
    let pointValue (i : Fin code.1) : X :=
      (code.2 i).get ((hcode i).2 i.isLt)
    let cloud : FinitePointCloud X := ⟨code.1, pointValue⟩
    refine ⟨cloud, ?_⟩
    apply Prod.ext
    · rfl
    · funext k
      by_cases hk : k < code.1
      · have hsome : (code.2 k).isSome = true := (hcode k).2 hk
        change (if h : k < code.1 then some (pointValue ⟨k, h⟩) else none) = code.2 k
        rw [dite_eq_left hk]
        exact Option.some_get hsome
      · have hnone : code.2 k = none :=
          Option.not_isSome_iff_eq_none.1 (fun hsome ↦ hk ((hcode k).1 hsome))
        simp [paddedCode, point?, cloud, hk, hnone]

section Measurable

variable [MeasurableSpace X]

/-- The measurable structure inherited from the canonical padded encoding. -/
instance instMeasurableSpace : MeasurableSpace (FinitePointCloud X) :=
  MeasurableSpace.comap paddedCode inferInstance

@[fun_prop]
theorem measurable_paddedCode : Measurable (paddedCode (X := X)) :=
  comap_measurable paddedCode

theorem measurable_isCanonical : Measurable (IsCanonical (X := X)) := by
  apply Measurable.forall
  intro k
  apply Measurable.iff
  · apply Measurable.eq_const
    exact MeasureTheory.Option.measurable_isSome.comp
      ((measurable_pi_apply k).comp measurable_snd)
  · exact (measurable_of_countable (fun n : ℕ ↦ k < n)).comp measurable_fst

theorem measurableSet_isCanonical : MeasurableSet {code : PaddedCode X | IsCanonical code} :=
  measurable_isCanonical.setOf

theorem measurableSet_range_paddedCode :
    MeasurableSet (range (paddedCode (X := X))) := by
  rw [range_paddedCode]
  exact measurableSet_isCanonical

theorem measurableEmbedding_paddedCode :
    MeasurableEmbedding (paddedCode (X := X)) := by
  rw [MeasurableEmbedding.iff_comap_eq]
  exact ⟨paddedCode_injective, rfl, measurableSet_range_paddedCode⟩

@[fun_prop]
theorem measurable_card : Measurable (card : FinitePointCloud X → ℕ) :=
  measurable_fst.comp measurable_paddedCode

@[fun_prop]
theorem measurable_point?_apply (k : ℕ) :
    Measurable (fun cloud : FinitePointCloud X ↦ cloud.point? k) :=
  ((measurable_pi_apply k).comp measurable_snd).comp measurable_paddedCode

end Measurable

private theorem standardBorelSpace_of_measurableEquiv {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] (e : A ≃ᵐ B) :
    StandardBorelSpace A := by
  let _ := upgradeStandardBorel B
  let topologyA : TopologicalSpace A := TopologicalSpace.induced e inferInstance
  let _ : TopologicalSpace A := topologyA
  let _ : PolishSpace A := e.toEquiv.polishSpace_induced
  let _ : BorelSpace A := e.measurableEmbedding.borelSpace ⟨rfl⟩
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- Finite ordered clouds over a standard Borel mark space are standard Borel. -/
instance instStandardBorelSpace [MeasurableSpace X] [StandardBorelSpace X] :
    StandardBorelSpace (FinitePointCloud X) := by
  let embedding := measurableEmbedding_paddedCode (X := X)
  let _ : StandardBorelSpace (range (paddedCode (X := X))) :=
    measurableSet_range_paddedCode.standardBorel
  exact standardBorelSpace_of_measurableEquiv embedding.equivRange

/-- Convert an indexed cloud to the list in its stored order. -/
def toList (cloud : FinitePointCloud X) : List X :=
  List.ofFn cloud.point

@[simp]
theorem length_toList (cloud : FinitePointCloud X) : cloud.toList.length = cloud.card := by
  simp [toList]

/-- Forget the enumeration while retaining multiplicities. -/
def toMultiset (cloud : FinitePointCloud X) : Multiset X :=
  cloud.toList

@[simp]
theorem card_toMultiset (cloud : FinitePointCloud X) : cloud.toMultiset.card = cloud.card := by
  simp [toMultiset]

/-- Fold a cloud in its stored order. -/
def foldl (step : Z → X → Z) (initial : Z) (cloud : FinitePointCloud X) : Z :=
  cloud.toList.foldl step initial

/-- Count the points satisfying a Boolean predicate. -/
def count (cloud : FinitePointCloud X) (predicate : X → Bool) : ℕ :=
  (cloud.toMultiset.filter fun x ↦ predicate x).card

/-- Multiplicity of a point in a finite cloud. -/
def multiplicity [DecidableEq X] (cloud : FinitePointCloud X) (x : X) : ℕ :=
  cloud.toMultiset.count x

theorem count_le_card (cloud : FinitePointCloud X) (predicate : X → Bool) :
    cloud.count predicate ≤ cloud.card := by
  rw [count, ← card_toMultiset]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

theorem multiplicity_le_card [DecidableEq X] (cloud : FinitePointCloud X) (x : X) :
    cloud.multiplicity x ≤ cloud.card := by
  rw [multiplicity, ← card_toMultiset]
  exact Multiset.count_le_card x cloud.toMultiset

/-- Apply a function pointwise without changing the indexing. -/
def map (f : X → Y) (cloud : FinitePointCloud X) : FinitePointCloud Y :=
  ⟨cloud.card, fun i ↦ f (cloud.point i)⟩

@[simp]
theorem card_map (f : X → Y) (cloud : FinitePointCloud X) :
    (cloud.map f).card = cloud.card :=
  rfl

@[simp]
theorem point_map (f : X → Y) (cloud : FinitePointCloud X) (i : Fin cloud.card) :
    (cloud.map f).point i = f (cloud.point i) :=
  rfl

@[simp]
theorem point?_map (f : X → Y) (cloud : FinitePointCloud X) (k : ℕ) :
    (cloud.map f).point? k = (cloud.point? k).map f := by
  by_cases hk : k < cloud.card <;> simp [point?, hk]

@[simp]
theorem toList_map (f : X → Y) (cloud : FinitePointCloud X) :
    (cloud.map f).toList = cloud.toList.map f := by
  exact List.ofFn_comp' cloud.point f

@[simp]
theorem toMultiset_map (f : X → Y) (cloud : FinitePointCloud X) :
    (cloud.map f).toMultiset = cloud.toMultiset.map f := by
  simp [toMultiset]

section MeasurableMap

variable [MeasurableSpace X] [MeasurableSpace Y]

private theorem measurable_option_map {f : X → Y} (hf : Measurable f) :
    Measurable (Option.map f) := by
  have heq : Option.map f = fun value ↦ value.elim none (fun x ↦ some (f x)) := by
    funext value
    cases value <;> rfl
  rw [heq]
  exact MeasureTheory.Option.measurable_elim none
    (MeasureTheory.Option.measurable_some.comp hf)

private def mapPaddedCode (f : X → Y) (code : PaddedCode X) : PaddedCode Y :=
  (code.1, fun k ↦ (code.2 k).map f)

private theorem measurable_mapPaddedCode {f : X → Y} (hf : Measurable f) :
    Measurable (mapPaddedCode f) := by
  apply Measurable.prodMk measurable_fst
  apply measurable_pi_lambda
  intro k
  exact (measurable_option_map hf).comp ((measurable_pi_apply k).comp measurable_snd)

theorem measurable_map {f : X → Y} (hf : Measurable f) :
    Measurable (map f : FinitePointCloud X → FinitePointCloud Y) := by
  rw [measurable_comap_iff]
  have h := (measurable_mapPaddedCode hf).comp (measurable_paddedCode (X := X))
  have heq : paddedCode ∘ map f = mapPaddedCode f ∘ paddedCode := by
    funext cloud
    apply Prod.ext
    · rfl
    · funext k
      exact point?_map f cloud k
  rw [heq]
  exact h

end MeasurableMap

end FinitePointCloud

end OTSelector.PointProcess
