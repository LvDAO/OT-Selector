import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Ambient-null augmentation of a filtration

Mathlib supplies `Filtration`, `Filtration.natural`, right-continuity, and
`Measure.completion` on the type tag `NullMeasurableSpace`.  It does not supply the
small augmentation that keeps the original sample type and enlarges every `ℱ_t` by the
*ambient-measurable terminal null sets* of `μ`.

That is the construction required by the feedback intensity argument: a global Borel
null event such as a label tie must already be `ℱ_0`-measurable, so that a zero-jump
fallback remains adapted.  Completing each `(ℱ_t, μ)` separately does not achieve this,
because the tie set need not sit inside an `ℱ_0`-null set.

The generators are restricted to sets that are already measurable in the ambient
σ-algebra `m`, so the augmented filtration remains a `Filtration ι m`.  This is not
the full usual completion: subsets of null sets that fail to be `m`-measurable are not
included.  Borel null events (in particular the tie set, once it is proved Borel and
null) are included.  The `usualAugmentation` below then applies mathlib's right
continuation to this ambient augmentation; it supplies right continuity without
claiming any additional completion beyond the ambient-measurable null generators.
-/

open MeasureTheory Set

namespace OTSelector

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

/-- Ambient measurable null sets of `μ`.  These play the role of `𝒩_∞` after the
tie event has been proved Borel. -/
def terminalNullSets (μ : Measure Ω) : Set (Set Ω) :=
  {s | MeasurableSet[m] s ∧ μ s = 0}

/-- Smallest σ-algebra containing `ℱ i` and every ambient measurable `μ`-null set. -/
@[instance_reducible]
noncomputable def ambientNullAugmentationSeq [Preorder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) (i : ι) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom
    ({s | MeasurableSet[ℱ i] s} ∪ terminalNullSets (m := m) μ)

lemma ambientNullAugmentationSeq_le [Preorder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) (i : ι) :
    ambientNullAugmentationSeq ℱ μ i ≤ m := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s (hs | hs)
  · exact ℱ.le i s hs
  · exact hs.1

lemma ambientNullAugmentationSeq_mono [Preorder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) {i j : ι} (hij : i ≤ j) :
    ambientNullAugmentationSeq ℱ μ i ≤ ambientNullAugmentationSeq ℱ μ j := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s (hs | hs)
  · exact MeasurableSpace.measurableSet_generateFrom (Or.inl (ℱ.mono hij s hs))
  · exact MeasurableSpace.measurableSet_generateFrom (Or.inr hs)

/-- Ambient-null augmentation `ℱ^μ_t = σ(ℱ_t ∪ 𝒩_∞^{m})`. -/
noncomputable def ambientNullAugmentation [Preorder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) : Filtration ι m where
  seq := ambientNullAugmentationSeq ℱ μ
  mono' := fun _ _ hij ↦ ambientNullAugmentationSeq_mono ℱ μ hij
  le' := ambientNullAugmentationSeq_le ℱ μ

lemma le_ambientNullAugmentation [Preorder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) :
    ℱ ≤ ambientNullAugmentation ℱ μ := by
  intro i s hs
  exact MeasurableSpace.measurableSet_generateFrom (Or.inl hs)

lemma ambientNullAugmentation_measurableSet_of_original [Preorder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) {i : ι} {s : Set Ω}
    (hs : MeasurableSet[ℱ i] s) :
    MeasurableSet[ambientNullAugmentation ℱ μ i] s :=
  MeasurableSpace.measurableSet_generateFrom (Or.inl hs)

lemma ambientNullAugmentation_measurableSet_null [Preorder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) {i : ι} {s : Set Ω}
    (hs : MeasurableSet[m] s) (hμ : μ s = 0) :
    MeasurableSet[ambientNullAugmentation ℱ μ i] s :=
  MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨hs, hμ⟩)

/-- A terminal measurable null set is measurable at time `⊥`, when the index type
has a bottom element.  This is the `Tie ∈ ℱ_0` clause. -/
lemma ambientNullAugmentation_measurableSet_null_bot [Preorder ι] [OrderBot ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) {s : Set Ω}
    (hs : MeasurableSet[m] s) (hμ : μ s = 0) :
    MeasurableSet[ambientNullAugmentation ℱ μ ⊥] s :=
  ambientNullAugmentation_measurableSet_null ℱ μ hs hμ

/-- The usual augmentation: first add all ambient-measurable terminal null sets,
then take the right-continuous continuation supplied by mathlib. -/
noncomputable def usualAugmentation [PartialOrder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) : Filtration ι m :=
  Filtration.rightCont (ambientNullAugmentation ℱ μ)

lemma ambientNullAugmentation_le_usualAugmentation [PartialOrder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) :
    ambientNullAugmentation ℱ μ ≤ usualAugmentation ℱ μ := by
  exact Filtration.le_rightCont (ambientNullAugmentation ℱ μ)

/-- The original filtration embeds into both stages of the augmentation. -/
lemma le_usualAugmentation [PartialOrder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) :
    ℱ ≤ usualAugmentation ℱ μ := by
  exact (le_ambientNullAugmentation ℱ μ).trans
    (ambientNullAugmentation_le_usualAugmentation ℱ μ)

lemma usualAugmentation_measurableSet_of_original [PartialOrder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) {i : ι} {s : Set Ω}
    (hs : MeasurableSet[ℱ i] s) :
    MeasurableSet[usualAugmentation ℱ μ i] s :=
  (le_usualAugmentation ℱ μ i) s hs

/-- Every ambient-measurable terminal null set is measurable at every usual time. -/
lemma usualAugmentation_measurableSet_null [PartialOrder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) {i : ι} {s : Set Ω}
    (hs : MeasurableSet[m] s) (hμ : μ s = 0) :
    MeasurableSet[usualAugmentation ℱ μ i] s :=
  (ambientNullAugmentation_le_usualAugmentation ℱ μ i) s
    (ambientNullAugmentation_measurableSet_null ℱ μ hs hμ)

/-- The terminal-null measurability statement at the bottom time. -/
lemma usualAugmentation_measurableSet_null_bot [PartialOrder ι] [OrderBot ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) {s : Set Ω}
    (hs : MeasurableSet[m] s) (hμ : μ s = 0) :
    MeasurableSet[usualAugmentation ℱ μ ⊥] s :=
  usualAugmentation_measurableSet_null ℱ μ hs hμ

/-- `usualAugmentation` is right-continuous by mathlib's automatic instance for
the right-continuation operation. -/
lemma usualAugmentation_isRightContinuous [PartialOrder ι]
    (ℱ : Filtration ι m) (μ : Measure Ω) :
    Filtration.IsRightContinuous (usualAugmentation ℱ μ) := by
  unfold usualAugmentation
  infer_instance

end OTSelector
