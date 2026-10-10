import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.Order.Compact

/-!
# Locally finite marked configurations on the real line

A marked configuration is a natural-valued function on `ℝ × M` with locally finite support.
The natural value can retain a
multiplicity, while `supportCountingMeasure` counts occupied marked sites.  For the simple point
configurations used in the paper, `IsSimple` says that every occupied site has value one.

Only the elementary configuration layer is constructed here.  In particular, this file does not
equip configurations with a vague topology or a standard Borel structure, and it makes no
stationarity, Campbell, or Palm assertion.
-/

open Set
open scoped ENNReal

namespace OTSelector.PointProcess

/-- A point on the real line carrying a mark in `M`. -/
abbrev RealMarkedPoint (M : Type*) := ℝ × M

/-- A locally finite, natural-valued marked configuration on the real line. -/
abbrev Configuration (M : Type*) [TopologicalSpace M] :=
  Function.locallyFinsupp (RealMarkedPoint M) ℕ

namespace Configuration

variable {M : Type*} [TopologicalSpace M]

/-- Simplicity is an external property: every marked site occurs at most once. -/
def IsSimple (config : Configuration M) : Prop :=
  ∀ z, config z ≤ 1

/-- The support is locally finite by construction of the carrier. -/
theorem locallyFiniteSupport (config : Configuration M) :
    LocallyFiniteSupport (config : RealMarkedPoint M → ℕ) :=
  Function.locallyFinsupp.locallyFiniteSupport config

/-- A locally finite support meets every compact marked window in finitely many points. -/
theorem finite_support_inter_compact (config : Configuration M) {K : Set (RealMarkedPoint M)}
    (hK : IsCompact K) : (K ∩ config.support).Finite :=
  config.locallyFiniteSupport.finite_inter_support_of_isCompact hK

/-- The support of a configuration is closed in a T1 marked space. -/
theorem isClosed_support [T1Space M] (config : Configuration M) : IsClosed config.support :=
  config.closedSupport isClosed_univ

section CountingMeasure

variable [MeasurableSpace M] [MeasurableSingletonClass M]

/-- Counting measure on the occupied marked sites.

For a simple configuration this is its point-process counting measure.  Multiplicities stored in
the natural-valued carrier are deliberately not repeated by this support-level measure.
-/
noncomputable def supportCountingMeasure (config : Configuration M) :
    MeasureTheory.Measure (RealMarkedPoint M) :=
  MeasureTheory.Measure.count.restrict config.support

omit [MeasurableSingletonClass M] in
/-- Evaluation of the support counting measure reduces to `Measure.count` on the occupied part. -/
theorem supportCountingMeasure_apply (config : Configuration M) {s : Set (RealMarkedPoint M)}
    (hs : MeasurableSet s) :
    config.supportCountingMeasure s = MeasureTheory.Measure.count (s ∩ config.support) := by
  simp [supportCountingMeasure, MeasureTheory.Measure.restrict_apply hs]

/-- Compact measurable marked windows have finite point count. -/
theorem supportCountingMeasure_lt_top_of_isCompact (config : Configuration M)
    {K : Set (RealMarkedPoint M)} (hK : IsCompact K) (hKm : MeasurableSet K) :
    config.supportCountingMeasure K < ∞ := by
  rw [supportCountingMeasure_apply config hKm, MeasureTheory.Measure.count_apply_lt_top]
  exact config.finite_support_inter_compact hK

/-- On a compact measurable window, the counting measure is the cardinality of the finite
intersection with the support. -/
theorem supportCountingMeasure_eq_card (config : Configuration M)
    {K : Set (RealMarkedPoint M)} (hK : IsCompact K) (hKm : MeasurableSet K) :
    config.supportCountingMeasure K =
      ((config.finite_support_inter_compact hK).toFinset.card : ℝ≥0∞) := by
  rw [supportCountingMeasure_apply config hKm,
    MeasureTheory.Measure.count_apply_finite _ (config.finite_support_inter_compact hK)]

/-- An occupied site has counting mass one. -/
theorem supportCountingMeasure_singleton_of_mem (config : Configuration M)
    {z : RealMarkedPoint M} (hz : z ∈ config.support) :
    config.supportCountingMeasure {z} = 1 := by
  simp [supportCountingMeasure, hz]

/-- An unoccupied site has counting mass zero. -/
theorem supportCountingMeasure_singleton_of_not_mem (config : Configuration M)
    {z : RealMarkedPoint M} (hz : z ∉ config.support) :
    config.supportCountingMeasure {z} = 0 := by
  simp [supportCountingMeasure, hz]

/-- Forget the mark by pushing the marked counting measure to the real coordinate.  Distinct marked
sites at the same spatial coordinate retain their count under this projection. -/
noncomputable def spatialCountingMeasure (config : Configuration M) :
    MeasureTheory.Measure ℝ :=
  MeasureTheory.Measure.map Prod.fst config.supportCountingMeasure

omit [MeasurableSingletonClass M] in
/-- Spatial counts are marked counts in the inverse-image window. -/
theorem spatialCountingMeasure_apply (config : Configuration M) {s : Set ℝ}
    (hs : MeasurableSet s) :
    config.spatialCountingMeasure s =
      config.supportCountingMeasure (Prod.fst ⁻¹' s) := by
  rw [spatialCountingMeasure, MeasureTheory.Measure.map_apply measurable_fst hs]

/-- Every bounded closed spatial window contains finitely many marked points when the mark space
is compact. -/
theorem spatialCountingMeasure_Icc_lt_top [CompactSpace M] (config : Configuration M)
    (a b : ℝ) : config.spatialCountingMeasure (Icc a b) < ∞ := by
  rw [spatialCountingMeasure_apply config measurableSet_Icc]
  apply config.supportCountingMeasure_lt_top_of_isCompact
  · rw [show Prod.fst ⁻¹' Icc a b = Icc a b ×ˢ (univ : Set M) by ext z; simp]
    exact isCompact_Icc.prod isCompact_univ
  · exact measurableSet_Icc.preimage measurable_fst

end CountingMeasure

section Translation

/-- Translation of the real coordinate, leaving the mark unchanged. -/
def pointTranslation (a : ℝ) : RealMarkedPoint M ≃ₜ RealMarkedPoint M :=
  (Homeomorph.addRight a).prodCongr (Homeomorph.refl M)

@[simp]
theorem pointTranslation_apply (a : ℝ) (z : RealMarkedPoint M) :
    pointTranslation a z = (z.1 + a, z.2) :=
  rfl

@[simp]
theorem pointTranslation_symm_apply (a : ℝ) (z : RealMarkedPoint M) :
    (pointTranslation a).symm z = (z.1 - a, z.2) := by
  change ((Homeomorph.addRight a).symm z.1, z.2) = (z.1 - a, z.2)
  rw [Homeomorph.addRight_symm]
  rfl

/-- Translate a locally finite configuration along the real coordinate. -/
noncomputable def translate (a : ℝ) (config : Configuration M) : Configuration M where
  toFun z := config ((pointTranslation a).symm z)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := by
    obtain ⟨t, ht, hfin⟩ := config.locallyFiniteSupport ((pointTranslation a).symm z)
    refine ⟨pointTranslation a '' t, ?_, ?_⟩
    · simpa using (pointTranslation a).isOpenMap.image_mem_nhds ht
    · refine (hfin.image (pointTranslation a)).subset ?_
      rintro y ⟨⟨x, hxt, rfl⟩, hy⟩
      refine ⟨x, ⟨hxt, ?_⟩, rfl⟩
      simpa [Function.mem_support] using hy

@[simp]
theorem translate_apply (a : ℝ) (config : Configuration M) (z : RealMarkedPoint M) :
    translate a config z = config (z.1 - a, z.2) := by
  simp [translate]

/-- Translation carries the support by the corresponding point homeomorphism. -/
theorem support_translate (a : ℝ) (config : Configuration M) :
    (translate a config).support = pointTranslation a '' config.support := by
  ext z
  constructor
  · intro hz
    refine ⟨(pointTranslation a).symm z, ?_, (pointTranslation a).apply_symm_apply z⟩
    simpa [Function.mem_support, translate] using hz
  · rintro ⟨x, hx, rfl⟩
    simpa [Function.mem_support, translate] using hx

@[simp]
theorem translate_zero (config : Configuration M) : translate 0 config = config := by
  ext z
  simp

/-- Successive translations add their displacements. -/
theorem translate_add (a b : ℝ) (config : Configuration M) :
    translate a (translate b config) = translate (a + b) config := by
  ext z
  simp only [translate_apply]
  congr 2
  ring

end Translation

end Configuration

end OTSelector.PointProcess
