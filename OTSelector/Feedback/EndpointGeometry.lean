import OTSelector.Basic.ModelLaw
import OTSelector.Feedback.HalfspaceVC

/-!
# Endpoint complement geometry

At the deterministic right endpoint `x = width - buffer`, the complements of the source and
target cut families are nested in the shear parameter.  This module proves that geometry and
places the largest complements inside explicit upper rank slabs.  The sharper nested empirical
CDF estimate is built on top of these deterministic statements.
-/

open MeasureTheory

namespace OTSelector.RelativeVC

/-- Complement of a source cut, written directly as a real sublevel complement. -/
def sourceCutComplementSet (p x : ℝ) : Set (ℝ × UnitMark) :=
  {z | x < z.1 + p * (1 - (z.2 : ℝ))}

/-- Complement of a target cut, written directly as a real sublevel complement. -/
def targetCutComplementSet (p x : ℝ) : Set (ℝ × UnitMark) :=
  {z | x < z.1 - p * (1 + (z.2 : ℝ))}

theorem measurableSet_sourceCutComplementSet (p x : ℝ) :
    MeasurableSet (sourceCutComplementSet p x) := by
  have ht : Measurable (fun z : ℝ × UnitMark ↦ z.1) := measurable_fst
  have hu : Measurable (fun z : ℝ × UnitMark ↦ (z.2 : ℝ)) :=
    measurable_subtype_coe.comp measurable_snd
  exact measurableSet_lt measurable_const (ht.add (measurable_const.mul (measurable_const.sub hu)))

theorem measurableSet_targetCutComplementSet (p x : ℝ) :
    MeasurableSet (targetCutComplementSet p x) := by
  have ht : Measurable (fun z : ℝ × UnitMark ↦ z.1) := measurable_fst
  have hv : Measurable (fun z : ℝ × UnitMark ↦ (z.2 : ℝ)) :=
    measurable_subtype_coe.comp measurable_snd
  exact measurableSet_lt measurable_const (ht.sub (measurable_const.mul (measurable_const.add hv)))

/-- The direct source complement agrees with the complement of the Boolean error set. -/
theorem sourceCutComplementSet_eq_errorSet_compl (p x : ℝ) :
    sourceCutComplementSet p x =
      (errorSet (sourceCutEval (p, x)) falseCutTarget)ᶜ := by
  ext z
  simp [sourceCutComplementSet, errorSet, sourceCutEval, falseCutTarget]

/-- The direct target complement agrees with the complement of the Boolean error set. -/
theorem targetCutComplementSet_eq_errorSet_compl (p x : ℝ) :
    targetCutComplementSet p x =
      (errorSet (targetCutEval (p, x)) falseCutTarget)ᶜ := by
  ext z
  by_cases h : z.1 - p * (1 + (z.2 : ℝ)) ≤ x
  · have hn : ¬x < z.1 - p * (1 + (z.2 : ℝ)) := not_lt_of_ge h
    simp [targetCutComplementSet, errorSet, targetCutEval, falseCutTarget, hn]
    linarith
  · have hp : x < z.1 - p * (1 + (z.2 : ℝ)) := lt_of_not_ge h
    simp [targetCutComplementSet, errorSet, targetCutEval, falseCutTarget, hp]
    linarith

/-- Source complement as the error set of the complemented Boolean cut. -/
theorem sourceCutComplementSet_eq_errorSet (p x : ℝ) :
    sourceCutComplementSet p x =
      errorSet (sourceCutComplementEval (p, x)) falseCutTarget := by
  rw [sourceCutComplementSet_eq_errorSet_compl]
  change (errorSet (sourceCutEval (p, x)) falseCutTarget)ᶜ =
    errorSet (boolNotConcept (sourceCutEval (p, x))) falseCutTarget
  exact (errorSet_boolNot_false _).symm

/-- Target complement as the error set of the complemented Boolean cut. -/
theorem targetCutComplementSet_eq_errorSet (p x : ℝ) :
    targetCutComplementSet p x =
      errorSet (targetCutComplementEval (p, x)) falseCutTarget := by
  rw [targetCutComplementSet_eq_errorSet_compl]
  change (errorSet (targetCutEval (p, x)) falseCutTarget)ᶜ =
    errorSet (boolNotConcept (targetCutEval (p, x))) falseCutTarget
  exact (errorSet_boolNot_false _).symm

/-- Source complements increase with the shear parameter. -/
theorem sourceCutComplementSet_mono (x : ℝ) : Monotone fun p ↦ sourceCutComplementSet p x := by
  intro p q hpq z hz
  have hu : 0 ≤ 1 - (z.2 : ℝ) := sub_nonneg.mpr z.2.property.2
  change x < z.1 + p * (1 - (z.2 : ℝ)) at hz
  change x < z.1 + q * (1 - (z.2 : ℝ))
  have hmul := mul_le_mul_of_nonneg_right hpq hu
  nlinarith

/-- Target complements decrease with the shear parameter. -/
theorem targetCutComplementSet_antitone (x : ℝ) :
    Antitone fun p ↦ targetCutComplementSet p x := by
  intro p q hpq z hz
  have hv : 0 ≤ 1 + (z.2 : ℝ) := by linarith [z.2.property.1]
  exact hz.trans_le (sub_le_sub_left (mul_le_mul_of_nonneg_right hpq hv) z.1)

/-- Source complement at the deterministic right endpoint. -/
def sourceEndpointComplement (width buffer p : ℝ) : Set (ℝ × UnitMark) :=
  sourceCutComplementSet p (width - buffer)

/-- Target complement at the deterministic right endpoint. -/
def targetEndpointComplement (width buffer p : ℝ) : Set (ℝ × UnitMark) :=
  targetCutComplementSet p (width - buffer)

/-- An upper slab in the rank coordinate. -/
def upperRankSlab (a : ℝ) : Set (ℝ × UnitMark) :=
  {z | a < z.1}

theorem measurableSet_upperRankSlab (a : ℝ) : MeasurableSet (upperRankSlab a) := by
  exact measurableSet_lt measurable_const measurable_fst

/-- All endpoint source complements in the prescribed shear window lie in the largest one. -/
theorem sourceEndpointComplement_subset_max {width buffer p : ℝ}
    (hp : |p| ≤ buffer / 8) :
    sourceEndpointComplement width buffer p ⊆
      sourceEndpointComplement width buffer (buffer / 8) := by
  exact sourceCutComplementSet_mono (width - buffer) (le_of_abs_le hp)

/-- All endpoint target complements in the prescribed shear window lie in the largest one. -/
theorem targetEndpointComplement_subset_max {width buffer p : ℝ}
    (hp : |p| ≤ buffer / 8) :
    targetEndpointComplement width buffer p ⊆
      targetEndpointComplement width buffer (-buffer / 8) := by
  apply targetCutComplementSet_antitone (width - buffer)
  linarith [neg_le_of_abs_le hp]

/-- The largest source complement is contained in a rank slab of width `9 buffer / 8`. -/
theorem sourceEndpointComplement_max_subset_slab {width buffer : ℝ} (hbuffer : 0 ≤ buffer) :
    sourceEndpointComplement width buffer (buffer / 8) ⊆
      upperRankSlab (width - 9 * buffer / 8) := by
  intro z hz
  have hu0 : 0 ≤ 1 - (z.2 : ℝ) := sub_nonneg.mpr z.2.property.2
  have hu1 : 1 - (z.2 : ℝ) ≤ 1 := by linarith [z.2.property.1]
  have hcoef : 0 ≤ buffer / 8 := by positivity
  have hmul : buffer / 8 * (1 - (z.2 : ℝ)) ≤ buffer / 8 := by
    simpa using mul_le_mul_of_nonneg_left hu1 hcoef
  change width - buffer < z.1 + buffer / 8 * (1 - (z.2 : ℝ)) at hz
  change width - 9 * buffer / 8 < z.1
  linarith

/-- The largest target complement is contained in a rank slab of width `5 buffer / 4`. -/
theorem targetEndpointComplement_max_subset_slab {width buffer : ℝ} (hbuffer : 0 ≤ buffer) :
    targetEndpointComplement width buffer (-buffer / 8) ⊆
      upperRankSlab (width - 5 * buffer / 4) := by
  intro z hz
  have hv0 : 0 ≤ 1 + (z.2 : ℝ) := by linarith [z.2.property.1]
  have hv2 : 1 + (z.2 : ℝ) ≤ 2 := by linarith [z.2.property.2]
  have hcoef : 0 ≤ buffer / 8 := by positivity
  have hmul : buffer / 8 * (1 + (z.2 : ℝ)) ≤ buffer / 4 := by
    have := mul_le_mul_of_nonneg_left hv2 hcoef
    linarith
  change width - buffer < z.1 - (-buffer / 8) * (1 + (z.2 : ℝ)) at hz
  change width - 5 * buffer / 4 < z.1
  linarith

/-- Probability of an upper rank slab under the rank-strip law. -/
theorem rankStripLaw_real_upperRankSlab (width a : ℝ) (hwidth : 0 < width)
    (ha0 : 0 ≤ a) (hawidth : a ≤ width) :
    (rankStripLaw width : Measure (ℝ × UnitMark)).real (upperRankSlab a) =
      1 - a / width := by
  rw [upperRankSlab]
  change ENNReal.toReal ((rankStripLaw width : Measure (ℝ × UnitMark))
    (Prod.fst ⁻¹' Set.Ioi a)) = 1 - a / width
  rw [← Measure.map_apply measurable_fst measurableSet_Ioi]
  change (((rankStripLaw width).map measurable_fst.aemeasurable : ProbabilityMeasure ℝ) :
      Measure ℝ).real (Set.Ioi a) = 1 - a / width
  rw [rankStripLaw_map_fst]
  exact rankCoordinateLaw_real_Ioi_of_mem width a hwidth ha0 hawidth

/-- Uniform population bound for source endpoint complements in the shear window. -/
theorem rankStripLaw_real_sourceEndpointComplement_le {width buffer p : ℝ}
    (hwidth : 0 < width) (hbuffer : 0 ≤ buffer) (hfit : 9 * buffer / 8 ≤ width)
    (hp : |p| ≤ buffer / 8) :
    (rankStripLaw width : Measure (ℝ × UnitMark)).real
        (sourceEndpointComplement width buffer p) ≤ 9 * buffer / (8 * width) := by
  have hsubset : sourceEndpointComplement width buffer p ⊆
      upperRankSlab (width - 9 * buffer / 8) :=
    (sourceEndpointComplement_subset_max (width := width) hp).trans
      (sourceEndpointComplement_max_subset_slab (width := width) hbuffer)
  calc
    (rankStripLaw width : Measure (ℝ × UnitMark)).real
        (sourceEndpointComplement width buffer p) ≤
        (rankStripLaw width : Measure (ℝ × UnitMark)).real
          (upperRankSlab (width - 9 * buffer / 8)) := measureReal_mono hsubset
    _ = 1 - (width - 9 * buffer / 8) / width := by
      exact rankStripLaw_real_upperRankSlab width (width - 9 * buffer / 8) hwidth
        (sub_nonneg.mpr hfit) (sub_le_self width (by positivity))
    _ = 9 * buffer / (8 * width) := by field_simp; ring

/-- Uniform population bound for target endpoint complements in the shear window. -/
theorem rankStripLaw_real_targetEndpointComplement_le {width buffer p : ℝ}
    (hwidth : 0 < width) (hbuffer : 0 ≤ buffer) (hfit : 5 * buffer / 4 ≤ width)
    (hp : |p| ≤ buffer / 8) :
    (rankStripLaw width : Measure (ℝ × UnitMark)).real
        (targetEndpointComplement width buffer p) ≤ 5 * buffer / (4 * width) := by
  have hsubset : targetEndpointComplement width buffer p ⊆
      upperRankSlab (width - 5 * buffer / 4) :=
    (targetEndpointComplement_subset_max (width := width) hp).trans
      (targetEndpointComplement_max_subset_slab (width := width) hbuffer)
  calc
    (rankStripLaw width : Measure (ℝ × UnitMark)).real
        (targetEndpointComplement width buffer p) ≤
        (rankStripLaw width : Measure (ℝ × UnitMark)).real
          (upperRankSlab (width - 5 * buffer / 4)) := measureReal_mono hsubset
    _ = 1 - (width - 5 * buffer / 4) / width := by
      exact rankStripLaw_real_upperRankSlab width (width - 5 * buffer / 4) hwidth
        (sub_nonneg.mpr hfit) (sub_le_self width (by positivity))
    _ = 5 * buffer / (4 * width) := by field_simp; ring

end OTSelector.RelativeVC
