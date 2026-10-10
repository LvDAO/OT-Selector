import OTSelector.Feedback.FiniteHistoryHazardSection
import OTSelector.Feedback.CrossingFibre

/-!
# Weighted one-point affine slab identities

For a fixed affine feedback section, the source and target crossing coordinates are affine in
the rank-scaled height once the mark is fixed.  The first results below identify the strict
`(s,t]` slab exactly with the corresponding crossing interval.  The weighted integral lemmas
then give the change-of-variables formula needed by the one-point compensator calculation.

All statements in this file are deterministic.  They concern one fixed state and one point law;
they do not assert an adaptive conditional law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-! ## Fixed-state crossing coordinates -/

/-- Source crossing coordinate of one marked point on a fixed affine state continuation. -/
noncomputable def sourceFixedStateCrossing
    (n : ℕ) (lam : ℝ) (state : FeedbackStepState n) (z : MarkedHeight) : ℝ :=
  sourceSegmentCrossing state.x state.p (state.slope lam)
    ((n : ℝ) * (z.1 : ℝ)) (1 - (z.2 : ℝ))

/-- Target crossing coordinate of one marked point on a fixed affine state continuation. -/
noncomputable def targetFixedStateCrossing
    (n : ℕ) (lam : ℝ) (state : FeedbackStepState n) (z : MarkedHeight) : ℝ :=
  targetSegmentCrossing state.x state.p (state.slope lam)
    ((n : ℝ) * (z.1 : ℝ)) (1 + (z.2 : ℝ))

theorem continuous_sourceFixedStateCrossing
    (state : FeedbackStepState n) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    Continuous (sourceFixedStateCrossing n lam state) := by
  have hq : |state.slope lam| ≤ lam :=
    abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0
  have hz1 : Continuous fun z : MarkedHeight ↦ (z.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz2 : Continuous fun z : MarkedHeight ↦ (z.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have ha : Continuous fun z : MarkedHeight ↦ 1 - (z.2 : ℝ) :=
    continuous_const.sub hz2
  have hnum : Continuous fun z : MarkedHeight ↦
      (n : ℝ) * (z.1 : ℝ) + (1 - (z.2 : ℝ)) *
        (state.p - state.slope lam * state.x) := by
    exact (continuous_const.mul hz1).add
      (ha.mul continuous_const)
  have hden : Continuous fun z : MarkedHeight ↦
      1 - (1 - (z.2 : ℝ)) * state.slope lam :=
    continuous_const.sub (ha.mul continuous_const)
  have hden0 : ∀ z : MarkedHeight,
      1 - (1 - (z.2 : ℝ)) * state.slope lam ≠ 0 := by
    intro z
    have ha0 : 0 ≤ 1 - (z.2 : ℝ) := sub_nonneg.mpr z.2.property.2
    have ha1 : 1 - (z.2 : ℝ) ≤ 1 := by linarith [z.2.property.1]
    exact (ne_of_gt (sourceSegment_denominator_pos ha0 ha1 hq hlam0 hlamHalf))
  have hquot := hnum.div hden hden0
  convert hquot using 1
  funext z
  simp [sourceFixedStateCrossing, sourceSegmentCrossing, FeedbackStepState.slope]

theorem sourceFixedStateCrossing_measurable
    (state : FeedbackStepState n) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    Measurable (sourceFixedStateCrossing n lam state) :=
  (continuous_sourceFixedStateCrossing state lam hlam0 hlamHalf).measurable

theorem continuous_targetFixedStateCrossing
    (state : FeedbackStepState n) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    Continuous (targetFixedStateCrossing n lam state) := by
  have hq : |state.slope lam| ≤ lam :=
    abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0
  have hz1 : Continuous fun z : MarkedHeight ↦ (z.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz2 : Continuous fun z : MarkedHeight ↦ (z.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  have hb : Continuous fun z : MarkedHeight ↦ 1 + (z.2 : ℝ) :=
    continuous_const.add hz2
  have hnum : Continuous fun z : MarkedHeight ↦
      (n : ℝ) * (z.1 : ℝ) - (1 + (z.2 : ℝ)) *
        (state.p - state.slope lam * state.x) := by
    exact (continuous_const.mul hz1).sub
      (hb.mul continuous_const)
  have hden : Continuous fun z : MarkedHeight ↦
      1 + (1 + (z.2 : ℝ)) * state.slope lam :=
    continuous_const.add (hb.mul continuous_const)
  have hden0 : ∀ z : MarkedHeight,
      1 + (1 + (z.2 : ℝ)) * state.slope lam ≠ 0 := by
    intro z
    have hb0 : 1 ≤ 1 + (z.2 : ℝ) := by linarith [z.2.property.1]
    have hb2 : 1 + (z.2 : ℝ) ≤ 2 := by linarith [z.2.property.2]
    exact (ne_of_gt (targetSegment_denominator_pos hb0 hb2 hq hlam0 hlamHalf))
  have hquot := hnum.div hden hden0
  convert hquot using 1
  funext z
  simp [targetFixedStateCrossing, targetSegmentCrossing, FeedbackStepState.slope]
  ring

theorem targetFixedStateCrossing_measurable
    (state : FeedbackStepState n) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    Measurable (targetFixedStateCrossing n lam state) :=
  (continuous_targetFixedStateCrossing state lam hlam0 hlamHalf).measurable

/-! ## Exact crossing-interval membership -/

theorem mem_sourceRawRemainingSetAt_iff_lt_sourceFixedStateCrossing
    (state : FeedbackStepState n) (lam : ℝ) (z : MarkedHeight)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (y : ℝ) :
    z ∈ sourceRawRemainingSetAt n lam state y ↔
      y < sourceFixedStateCrossing n lam state z := by
  have hq : |state.slope lam| ≤ lam :=
    abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0
  have ha0 : 0 ≤ 1 - (z.2 : ℝ) := sub_nonneg.mpr z.2.property.2
  have ha1 : 1 - (z.2 : ℝ) ≤ 1 := by linarith [z.2.property.1]
  simpa [sourceRawRemainingSetAt, sourceRawRemainingSet, sourceFixedStateCrossing,
    FiniteSample.sourcePoint, segmentCurve, mul_comm] using
    ((x_lt_sourceSegmentCrossing_iff (lam := lam) (x0 := state.x)
      (p0 := state.p) (q := state.slope lam)
      (t := (n : ℝ) * (z.1 : ℝ)) (a := 1 - (z.2 : ℝ)) (x := y)
      ha0 ha1 hq hlam0 hlamHalf).symm)

theorem mem_targetRawRemainingSetAt_iff_lt_targetFixedStateCrossing
    (state : FeedbackStepState n) (lam : ℝ) (z : MarkedHeight)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (y : ℝ) :
    z ∈ targetRawRemainingSetAt n lam state y ↔
      y < targetFixedStateCrossing n lam state z := by
  have hq : |state.slope lam| ≤ lam :=
    abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0
  have hb0 : 1 ≤ 1 + (z.2 : ℝ) := by linarith [z.2.property.1]
  have hb2 : 1 + (z.2 : ℝ) ≤ 2 := by linarith [z.2.property.2]
  simpa [targetRawRemainingSetAt, targetRawRemainingSet, targetFixedStateCrossing,
    FiniteSample.targetPoint, segmentCurve, mul_comm] using
    ((x_lt_targetSegmentCrossing_iff (lam := lam) (x0 := state.x)
      (p0 := state.p) (q := state.slope lam)
      (s := (n : ℝ) * (z.1 : ℝ)) (b := 1 + (z.2 : ℝ)) (x := y)
      hb0 hb2 hq hlam0 hlamHalf).symm)

theorem mem_sourceFixedStateCrossing_Ioc_iff
    (state : FeedbackStepState n) (lam s t : ℝ) (z : MarkedHeight)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (_hst : s ≤ t) :
    z ∈ sourceRawRemainingSetAt n lam state s \
        sourceRawRemainingSetAt n lam state t ↔
      sourceFixedStateCrossing n lam state z ∈ Ioc s t := by
  have hs := mem_sourceRawRemainingSetAt_iff_lt_sourceFixedStateCrossing
    state lam z hlam0 hlamHalf s
  have ht := mem_sourceRawRemainingSetAt_iff_lt_sourceFixedStateCrossing
    state lam z hlam0 hlamHalf t
  constructor
  · intro hz
    have hs' : s < sourceFixedStateCrossing n lam state z := hs.1 hz.1
    have hnt : ¬ t < sourceFixedStateCrossing n lam state z := by
      intro htc
      exact hz.2 (ht.2 htc)
    exact ⟨hs', le_of_not_gt hnt⟩
  · intro hz
    refine ⟨hs.2 hz.1, ?_⟩
    intro ht'
    exact (not_lt_of_ge hz.2) (ht.1 ht')

theorem mem_targetFixedStateCrossing_Ioc_iff
    (state : FeedbackStepState n) (lam s t : ℝ) (z : MarkedHeight)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (_hst : s ≤ t) :
    z ∈ targetRawRemainingSetAt n lam state s \
        targetRawRemainingSetAt n lam state t ↔
      targetFixedStateCrossing n lam state z ∈ Ioc s t := by
  have hs := mem_targetRawRemainingSetAt_iff_lt_targetFixedStateCrossing
    state lam z hlam0 hlamHalf s
  have ht := mem_targetRawRemainingSetAt_iff_lt_targetFixedStateCrossing
    state lam z hlam0 hlamHalf t
  constructor
  · intro hz
    have hs' : s < targetFixedStateCrossing n lam state z := hs.1 hz.1
    have hnt : ¬ t < targetFixedStateCrossing n lam state z := by
      intro htc
      exact hz.2 (ht.2 htc)
    exact ⟨hs', le_of_not_gt hnt⟩
  · intro hz
    refine ⟨hs.2 hz.1, ?_⟩
    intro ht'
    exact (not_lt_of_ge hz.2) (ht.1 ht')

theorem measurableSet_sourceFixedStateSlab
    (state : FeedbackStepState n) (lam s t : ℝ) :
    MeasurableSet
      (sourceRawRemainingSetAt n lam state s \
        sourceRawRemainingSetAt n lam state t) := by
  exact (isOpen_sourceRawRemainingSetAt lam state s).measurableSet.diff
    (isOpen_sourceRawRemainingSetAt lam state t).measurableSet

theorem measurableSet_targetFixedStateSlab
    (state : FeedbackStepState n) (lam s t : ℝ) :
    MeasurableSet
      (targetRawRemainingSetAt n lam state s \
        targetRawRemainingSetAt n lam state t) := by
  exact (isOpen_targetRawRemainingSetAt lam state s).measurableSet.diff
    (isOpen_targetRawRemainingSetAt lam state t).measurableSet

theorem measurableSet_sourceFixedStateCrossing_preimage_Ioc
    (state : FeedbackStepState n) (lam s t : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t) :
    MeasurableSet
      ((sourceFixedStateCrossing n lam state) ⁻¹' Ioc s t) := by
  have hset :
      (sourceFixedStateCrossing n lam state) ⁻¹' Ioc s t =
        sourceRawRemainingSetAt n lam state s \
          sourceRawRemainingSetAt n lam state t := by
    ext z
    exact (mem_sourceFixedStateCrossing_Ioc_iff state lam s t z hlam0 hlamHalf hst).symm
  rw [hset]
  exact measurableSet_sourceFixedStateSlab state lam s t

theorem measurableSet_targetFixedStateCrossing_preimage_Ioc
    (state : FeedbackStepState n) (lam s t : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t) :
    MeasurableSet
      ((targetFixedStateCrossing n lam state) ⁻¹' Ioc s t) := by
  have hset :
      (targetFixedStateCrossing n lam state) ⁻¹' Ioc s t =
        targetRawRemainingSetAt n lam state s \
          targetRawRemainingSetAt n lam state t := by
    ext z
    exact (mem_targetFixedStateCrossing_Ioc_iff state lam s t z hlam0 hlamHalf hst).symm
  rw [hset]
  exact measurableSet_targetFixedStateSlab state lam s t

/-! ## One-dimensional affine substitution -/

private theorem intervalIntegral_sourceNatHeightCrossing
    (n : ℕ) (x0 p0 q lam a hs ht s t : ℝ) (hn : 0 < n)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hhs : sourceNatHeightCrossing n x0 p0 q a hs = s)
    (hht : sourceNatHeightCrossing n x0 p0 q a ht = t)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    (∫ r in hs..ht, φ (sourceNatHeightCrossing n x0 p0 q a r)) =
      (1 - a * q) / (n : ℝ) * (∫ y in s..t, φ y) := by
  have hden : 0 < 1 - a * q := by
    exact sourceSegment_denominator_pos ha0 ha1 hq hlam0 hlamHalf
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hderiv : ∀ r : ℝ,
      HasDerivAt (sourceNatHeightCrossing n x0 p0 q a)
        ((n : ℝ) / (1 - a * q)) r := by
    intro r
    have hlin := (hasDerivAt_id r).const_mul (n : ℝ)
    have hconst := hasDerivAt_const r (a * (p0 - q * x0))
    have hadd := hlin.add hconst
    have hdiv := hadd.div_const (1 - a * q)
    have hfun : sourceNatHeightCrossing n x0 p0 q a =
        (fun x : ℝ ↦
          ((n : ℝ) * x + a * (p0 - q * x0)) / (1 - a * q)) := by
      funext x
      simp [sourceNatHeightCrossing, sourceSegmentCrossing]
    rw [hfun]
    simpa [id] using hdiv
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (a := hs) (b := ht)
    (f := sourceNatHeightCrossing n x0 p0 q a)
    (f' := fun _ : ℝ ↦ (n : ℝ) / (1 - a * q)) (g := φ)
    (fun r _ ↦ hderiv r) continuousOn_const hφ
  have hscaled :
      (∫ r in hs..ht,
        φ (sourceNatHeightCrossing n x0 p0 q a r) *
          ((n : ℝ) / (1 - a * q))) =
        ∫ y in s..t, φ y := by
    simpa [Function.comp_def, hhs, hht] using hchange
  have hmul := intervalIntegral.integral_mul_const
    (μ := volume) (a := hs) (b := ht)
    ((n : ℝ) / (1 - a * q))
    (fun r : ℝ ↦ φ (sourceNatHeightCrossing n x0 p0 q a r))
  have hcoeff :
      (1 - a * q) / (n : ℝ) * ((n : ℝ) / (1 - a * q)) = 1 := by
    field_simp [ne_of_gt hnreal, ne_of_gt hden]
  have hscaled' :
      ((n : ℝ) / (1 - a * q)) *
          (∫ r in hs..ht, φ (sourceNatHeightCrossing n x0 p0 q a r)) =
        ∫ y in s..t, φ y := by
    calc
      ((n : ℝ) / (1 - a * q)) *
          (∫ r in hs..ht, φ (sourceNatHeightCrossing n x0 p0 q a r)) =
          (∫ r in hs..ht,
            φ (sourceNatHeightCrossing n x0 p0 q a r) *
              ((n : ℝ) / (1 - a * q))) := by
            rw [hmul]
            ring
      _ = ∫ y in s..t, φ y := hscaled
  calc
    (∫ r in hs..ht, φ (sourceNatHeightCrossing n x0 p0 q a r)) =
        (1 - a * q) / (n : ℝ) *
          ((n : ℝ) / (1 - a * q) *
            ∫ r in hs..ht, φ (sourceNatHeightCrossing n x0 p0 q a r)) := by
      calc
        _ = 1 * (∫ r in hs..ht,
            φ (sourceNatHeightCrossing n x0 p0 q a r)) := by simp
        _ = ((1 - a * q) / (n : ℝ) *
              ((n : ℝ) / (1 - a * q))) *
            (∫ r in hs..ht, φ (sourceNatHeightCrossing n x0 p0 q a r)) := by
              rw [hcoeff]
        _ = (1 - a * q) / (n : ℝ) *
            ((n : ℝ) / (1 - a * q) *
              ∫ r in hs..ht, φ (sourceNatHeightCrossing n x0 p0 q a r)) := by
              rw [mul_assoc]
    _ = (1 - a * q) / (n : ℝ) *
          (∫ y in s..t, φ y) := by rw [hscaled']

theorem unitUniform_sourceFixedStateCrossing_slab_integral
    (state : FeedbackStepState n) (lam s t : ℝ) (u : UnitMark)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
      sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    (∫ h : UnitMark,
      (sourceRawRemainingSetAt n lam state s \
        sourceRawRemainingSetAt n lam state t).indicator
        (fun z ↦ φ (sourceFixedStateCrossing n lam state z)) (h, u)
        ∂(unitUniform : Measure UnitMark)) =
      ∫ y in s..t,
        φ y * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ) := by
  let q : ℝ := state.slope lam
  let a : ℝ := 1 - (u : ℝ)
  let hs : ℝ :=
    sourceBoundary (segmentCurve state.x state.p q s) s u / (n : ℝ)
  let ht : ℝ :=
    sourceBoundary (segmentCurve state.x state.p q t) t u / (n : ℝ)
  have hq : |q| ≤ lam := by
    simpa [q, FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact sub_nonneg.mpr u.property.2
  have ha1 : a ≤ 1 := by
    dsimp [a]
    linarith [u.property.1]
  have hfactor : 0 ≤ sourceMarkedFactor q (u : ℝ) := by
    have hq' := (abs_le.mp hq)
    have hu0 : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
    have hu1 : 1 - (u : ℝ) ≤ 1 := by linarith [u.property.1]
    have hprod₁ : q * (1 - (u : ℝ)) ≤ lam * (1 - (u : ℝ)) :=
      mul_le_mul_of_nonneg_right hq'.2 hu0
    have hprod₂ : lam * (1 - (u : ℝ)) ≤ lam := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 hlam0
    dsimp [sourceMarkedFactor]
    nlinarith
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbs := hbulk s ⟨le_rfl, hst⟩
  have hbt := hbulk t ⟨hst, le_rfl⟩
  have hhs0 : 0 ≤ hs := by
    dsimp [hs]
    exact div_nonneg hbs.1 hnreal.le
  have hhs1 : hs ≤ 1 := by
    dsimp [hs]
    exact (div_le_one₀ hnreal).mpr hbs.2
  have hht0 : 0 ≤ ht := by
    dsimp [ht]
    exact div_nonneg hbt.1 hnreal.le
  have hht1 : ht ≤ 1 := by
    dsimp [ht]
    exact (div_le_one₀ hnreal).mpr hbt.2
  have hbst :
      sourceBoundary (segmentCurve state.x state.p q s) s u ≤
        sourceBoundary (segmentCurve state.x state.p q t) t u := by
    have hdiff := sourceBoundary_segment_sub state.x state.p q s t (u : ℝ)
    have hinc : 0 ≤ (t - s) * sourceMarkedFactor q (u : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hst) hfactor
    linarith
  have hst' : hs ≤ ht := by
    dsimp [hs, ht]
    exact (div_le_div_iff_of_pos_right hnreal).2 hbst
  have hhsn : (n : ℝ) * hs =
      sourceBoundary (segmentCurve state.x state.p q s) s u := by
    dsimp [hs]
    field_simp
  have hhtn : (n : ℝ) * ht =
      sourceBoundary (segmentCurve state.x state.p q t) t u := by
    dsimp [ht]
    field_simp
  have hq' : |q| ≤ lam := hq
  have hhs_cross :
      sourceNatHeightCrossing n state.x state.p q a hs = s := by
    have huniq : s = sourceSegmentCrossing state.x state.p q
        ((n : ℝ) * hs) a := by
      apply sourceSegmentCrossing_unique (lam := lam) (x0 := state.x)
        (p0 := state.p) (q := q) (t := (n : ℝ) * hs) (a := a) (x := s)
        ha0 ha1 hq' hlam0 hlamHalf
      rw [hhsn]
      simp [sourceBoundary, a]
      ring
    simpa [sourceNatHeightCrossing] using huniq.symm
  have hht_cross :
      sourceNatHeightCrossing n state.x state.p q a ht = t := by
    have huniq : t = sourceSegmentCrossing state.x state.p q
        ((n : ℝ) * ht) a := by
      apply sourceSegmentCrossing_unique (lam := lam) (x0 := state.x)
        (p0 := state.p) (q := q) (t := (n : ℝ) * ht) (a := a) (x := t)
        ha0 ha1 hq' hlam0 hlamHalf
      rw [hhtn]
      simp [sourceBoundary, a]
      ring
    simpa [sourceNatHeightCrossing] using huniq.symm
  let hsU : UnitMark := ⟨hs, hhs0, hhs1⟩
  let htU : UnitMark := ⟨ht, hht0, hht1⟩
  have hmono : StrictMono (sourceNatHeightCrossing n state.x state.p q a) :=
    sourceNatHeightCrossing_strictMono hn ha0 ha1 hq' hlam0 hlamHalf
  have hmem (h : UnitMark) :
      (h, u) ∈ sourceRawRemainingSetAt n lam state s \
          sourceRawRemainingSetAt n lam state t ↔
        h ∈ Ioc hsU htU := by
    constructor
    · intro hz
      have hc := (mem_sourceFixedStateCrossing_Ioc_iff state lam s t
        (h, u) hlam0 hlamHalf hst).1 hz
      have hhslt : hs < (h : ℝ) := by
        have hc' : sourceNatHeightCrossing n state.x state.p q a hs <
            sourceNatHeightCrossing n state.x state.p q a (h : ℝ) := by
          rw [hhs_cross]
          simpa [sourceFixedStateCrossing, sourceNatHeightCrossing, q, a] using hc.1
        exact (hmono.lt_iff_lt).1 hc'
      have hhlt : (h : ℝ) ≤ ht := by
        have hc' : sourceNatHeightCrossing n state.x state.p q a (h : ℝ) ≤
            sourceNatHeightCrossing n state.x state.p q a ht := by
          rw [hht_cross]
          simpa [sourceFixedStateCrossing, sourceNatHeightCrossing, q, a] using hc.2
        exact (hmono.le_iff_le).1 hc'
      exact ⟨hhslt, hhlt⟩
    · intro hh
      have hc : sourceNatHeightCrossing n state.x state.p q a (h : ℝ) ∈ Ioc s t := by
        rw [← hhs_cross, ← hht_cross]
        exact ⟨hmono hh.1, hmono.monotone hh.2⟩
      exact (mem_sourceFixedStateCrossing_Ioc_iff state lam s t
        (h, u) hlam0 hlamHalf hst).2 hc
  have hindicator :
      (∫ h : UnitMark,
        (sourceRawRemainingSetAt n lam state s \
          sourceRawRemainingSetAt n lam state t).indicator
          (fun z ↦ φ (sourceFixedStateCrossing n lam state z)) (h, u)
          ∂(unitUniform : Measure UnitMark)) =
      ∫ h : UnitMark,
        (Ioc hsU htU).indicator
          (fun h ↦ φ (sourceNatHeightCrossing n state.x state.p q a (h : ℝ))) h
          ∂(unitUniform : Measure UnitMark) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun h ↦ by
      change (sourceRawRemainingSetAt n lam state s \
          sourceRawRemainingSetAt n lam state t).indicator
          (fun z ↦ φ (sourceFixedStateCrossing n lam state z)) (h, u) =
        (Ioc hsU htU).indicator
          (fun h ↦ φ (sourceNatHeightCrossing n state.x state.p q a (h : ℝ))) h
      by_cases hh : (h, u) ∈
          sourceRawRemainingSetAt n lam state s \
            sourceRawRemainingSetAt n lam state t
      · rw [Set.indicator_of_mem hh]
        rw [Set.indicator_of_mem ((hmem h).1 hh)]
        simp [sourceFixedStateCrossing, sourceNatHeightCrossing, q, a]
      · have hhn : h ∉ Ioc hsU htU := by
          intro hcontr
          exact hh ((hmem h).2 hcontr)
        simp [Set.indicator, hh, hhn]
  have hsub :
      (∫ h : UnitMark,
        (Ioc hsU htU).indicator
          (fun h ↦ φ (sourceNatHeightCrossing n state.x state.p q a (h : ℝ))) h
          ∂(unitUniform : Measure UnitMark)) =
      ∫ r : ℝ in Icc (0 : ℝ) 1,
        (Ioc hs ht).indicator
          (fun r ↦ φ (sourceNatHeightCrossing n state.x state.p q a r)) r := by
    change (∫ h : UnitMark,
      (Ioc hsU htU).indicator
        (fun h ↦ φ (sourceNatHeightCrossing n state.x state.p q a (h : ℝ))) h
        ∂(volume : Measure UnitMark)) = _
    have hpoint : ∀ h : UnitMark,
        (Ioc hsU htU).indicator
            (fun h ↦ φ (sourceNatHeightCrossing n state.x state.p q a (h : ℝ))) h =
          (Ioc hs ht).indicator
            (fun r ↦ φ (sourceNatHeightCrossing n state.x state.p q a r)) (h : ℝ) := by
      intro h
      by_cases hh : h ∈ Ioc hsU htU
      · have hh' : (h : ℝ) ∈ Ioc hs ht := by
          exact hh
        simp [Set.indicator_of_mem hh, Set.indicator_of_mem hh', hsU, htU]
      · have hh' : (h : ℝ) ∉ Ioc hs ht := by
          intro hcontr
          exact hh hcontr
        simp [Set.indicator, hh, hh', hsU, htU]
    calc
      (∫ h : UnitMark,
        (Ioc hsU htU).indicator
          (fun h ↦ φ (sourceNatHeightCrossing n state.x state.p q a (h : ℝ))) h
          ∂(volume : Measure UnitMark)) =
        ∫ h : UnitMark,
          (Ioc hs ht).indicator
            (fun r ↦ φ (sourceNatHeightCrossing n state.x state.p q a r)) (h : ℝ)
            ∂(volume : Measure UnitMark) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hpoint
      _ = ∫ r : ℝ in Icc (0 : ℝ) 1,
          (Ioc hs ht).indicator
            (fun r ↦ φ (sourceNatHeightCrossing n state.x state.p q a r)) r := by
        simpa [UnitMark] using
          (integral_subtype (G := ℝ) (s := Icc (0 : ℝ) 1) measurableSet_Icc
            (fun r : ℝ ↦
              (Ioc hs ht).indicator
                (fun r ↦ φ (sourceNatHeightCrossing n state.x state.p q a r)) r))
  have hIoc_sub : Ioc hs ht ⊆ Ioc (0 : ℝ) 1 := by
    intro r hr
    exact ⟨lt_of_le_of_lt hhs0 hr.1, hr.2.trans hht1⟩
  have hreal :
      (∫ r : ℝ in Icc (0 : ℝ) 1,
        (Ioc hs ht).indicator
          (fun r ↦ φ (sourceNatHeightCrossing n state.x state.p q a r)) r) =
      ∫ r : ℝ in Ioc hs ht,
        φ (sourceNatHeightCrossing n state.x state.p q a r) := by
    rw [integral_Icc_eq_integral_Ioc]
    change (∫ r : ℝ,
      (Ioc hs ht).indicator
        (fun r ↦ φ (sourceNatHeightCrossing n state.x state.p q a r)) r
        ∂(volume.restrict (Ioc (0 : ℝ) 1))) = _
    rw [integral_indicator measurableSet_Ioc]
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr hIoc_sub]
  calc
    (∫ h : UnitMark,
        (sourceRawRemainingSetAt n lam state s \
          sourceRawRemainingSetAt n lam state t).indicator
          (fun z ↦ φ (sourceFixedStateCrossing n lam state z)) (h, u)
          ∂(unitUniform : Measure UnitMark)) =
      ∫ h : UnitMark,
        (Ioc hsU htU).indicator
          (fun h ↦ φ (sourceNatHeightCrossing n state.x state.p q a (h : ℝ))) h
          ∂(unitUniform : Measure UnitMark) := hindicator
    _ =
      ∫ r : ℝ in Icc (0 : ℝ) 1,
        (Ioc hs ht).indicator
          (fun r ↦ φ (sourceNatHeightCrossing n state.x state.p q a r)) r := hsub
    _ = ∫ r : ℝ in Ioc hs ht,
        φ (sourceNatHeightCrossing n state.x state.p q a r) := hreal
    _ = ∫ r in hs..ht,
        φ (sourceNatHeightCrossing n state.x state.p q a r) :=
          (intervalIntegral.integral_of_le hst').symm
    _ = (1 - a * q) / (n : ℝ) * (∫ y in s..t, φ y) :=
      intervalIntegral_sourceNatHeightCrossing n state.x state.p q lam a hs ht s t
        hn ha0 ha1 hq hlam0 hlamHalf hhs_cross hht_cross φ hφ
    _ = ∫ y in s..t,
        φ y * sourceMarkedFactor q (u : ℝ) / (n : ℝ) := by
      simp [a, sourceMarkedFactor]; ring

private theorem intervalIntegral_targetNatHeightCrossing_pre
    (n : ℕ) (x0 p0 q lam b hs ht s t : ℝ) (hn : 0 < n)
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hhs : targetNatHeightCrossing n x0 p0 q b hs = s)
    (hht : targetNatHeightCrossing n x0 p0 q b ht = t)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    (∫ r in hs..ht, φ (targetNatHeightCrossing n x0 p0 q b r)) =
      (1 + b * q) / (n : ℝ) * (∫ y in s..t, φ y) := by
  have hden : 0 < 1 + b * q := by
    exact targetSegment_denominator_pos hb0 hb2 hq hlam0 hlamHalf
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hderiv : ∀ r : ℝ,
      HasDerivAt (targetNatHeightCrossing n x0 p0 q b)
        ((n : ℝ) / (1 + b * q)) r := by
    intro r
    have hlin := (hasDerivAt_id r).const_mul (n : ℝ)
    have hconst := hasDerivAt_const r (-b * p0 + b * q * x0)
    have hadd := hlin.add hconst
    have hdiv := hadd.div_const (1 + b * q)
    have hfun : targetNatHeightCrossing n x0 p0 q b =
        (fun x : ℝ ↦
          ((n : ℝ) * x + (-b * p0 + b * q * x0)) / (1 + b * q)) := by
      funext x
      simp [targetNatHeightCrossing, targetSegmentCrossing]
      ring
    rw [hfun]
    simpa [id] using hdiv
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (a := hs) (b := ht)
    (f := targetNatHeightCrossing n x0 p0 q b)
    (f' := fun _ : ℝ ↦ (n : ℝ) / (1 + b * q)) (g := φ)
    (fun r _ ↦ hderiv r) continuousOn_const hφ
  have hscaled :
      (∫ r in hs..ht,
        φ (targetNatHeightCrossing n x0 p0 q b r) *
          ((n : ℝ) / (1 + b * q))) =
        ∫ y in s..t, φ y := by
    simpa [Function.comp_def, hhs, hht] using hchange
  have hmul := intervalIntegral.integral_mul_const
    (μ := volume) (a := hs) (b := ht)
    ((n : ℝ) / (1 + b * q))
    (fun r : ℝ ↦ φ (targetNatHeightCrossing n x0 p0 q b r))
  have hcoeff :
      (1 + b * q) / (n : ℝ) * ((n : ℝ) / (1 + b * q)) = 1 := by
    field_simp [ne_of_gt hnreal, ne_of_gt hden]
  have hscaled' :
      ((n : ℝ) / (1 + b * q)) *
          (∫ r in hs..ht, φ (targetNatHeightCrossing n x0 p0 q b r)) =
        ∫ y in s..t, φ y := by
    calc
      ((n : ℝ) / (1 + b * q)) *
          (∫ r in hs..ht, φ (targetNatHeightCrossing n x0 p0 q b r)) =
          (∫ r in hs..ht,
            φ (targetNatHeightCrossing n x0 p0 q b r) *
              ((n : ℝ) / (1 + b * q))) := by
            rw [hmul]
            ring
      _ = ∫ y in s..t, φ y := hscaled
  calc
    (∫ r in hs..ht, φ (targetNatHeightCrossing n x0 p0 q b r)) =
        (1 + b * q) / (n : ℝ) *
          ((n : ℝ) / (1 + b * q) *
            ∫ r in hs..ht, φ (targetNatHeightCrossing n x0 p0 q b r)) := by
      calc
        _ = 1 * (∫ r in hs..ht,
            φ (targetNatHeightCrossing n x0 p0 q b r)) := by simp
        _ = ((1 + b * q) / (n : ℝ) *
              ((n : ℝ) / (1 + b * q))) *
            (∫ r in hs..ht, φ (targetNatHeightCrossing n x0 p0 q b r)) := by
              rw [hcoeff]
        _ = (1 + b * q) / (n : ℝ) *
            ((n : ℝ) / (1 + b * q) *
              ∫ r in hs..ht, φ (targetNatHeightCrossing n x0 p0 q b r)) := by
              rw [mul_assoc]
    _ = (1 + b * q) / (n : ℝ) *
          (∫ y in s..t, φ y) := by rw [hscaled']

theorem unitUniform_targetFixedStateCrossing_slab_integral
    (state : FeedbackStepState n) (lam s t : ℝ) (v : UnitMark)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
      targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    (∫ h : UnitMark,
      (targetRawRemainingSetAt n lam state s \
        targetRawRemainingSetAt n lam state t).indicator
        (fun z ↦ φ (targetFixedStateCrossing n lam state z)) (h, v)
        ∂(unitUniform : Measure UnitMark)) =
      ∫ y in s..t,
        φ y * targetMarkedFactor (state.slope lam) (v : ℝ) / (n : ℝ) := by
  let q : ℝ := state.slope lam
  let b : ℝ := 1 + (v : ℝ)
  let hs : ℝ :=
    targetBoundary (segmentCurve state.x state.p q s) s v / (n : ℝ)
  let ht : ℝ :=
    targetBoundary (segmentCurve state.x state.p q t) t v / (n : ℝ)
  have hq : |q| ≤ lam := by
    simpa [q, FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0)
  have hb0 : 1 ≤ b := by
    dsimp [b]
    linarith [v.property.1]
  have hb2 : b ≤ 2 := by
    dsimp [b]
    linarith [v.property.2]
  have hfactor : 0 ≤ targetMarkedFactor q (v : ℝ) := by
    have hden := targetSegment_denominator_pos hb0 hb2 hq hlam0 hlamHalf
    dsimp [targetMarkedFactor, b]
    linarith
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbs := hbulk s ⟨le_rfl, hst⟩
  have hbt := hbulk t ⟨hst, le_rfl⟩
  have hhs0 : 0 ≤ hs := by
    dsimp [hs]
    exact div_nonneg hbs.1 hnreal.le
  have hhs1 : hs ≤ 1 := by
    dsimp [hs]
    exact (div_le_one₀ hnreal).mpr hbs.2
  have hht0 : 0 ≤ ht := by
    dsimp [ht]
    exact div_nonneg hbt.1 hnreal.le
  have hht1 : ht ≤ 1 := by
    dsimp [ht]
    exact (div_le_one₀ hnreal).mpr hbt.2
  have hbst :
      targetBoundary (segmentCurve state.x state.p q s) s v ≤
        targetBoundary (segmentCurve state.x state.p q t) t v := by
    have hdiff := targetBoundary_segment_sub state.x state.p q s t (v : ℝ)
    have hinc : 0 ≤ (t - s) * targetMarkedFactor q (v : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hst) hfactor
    linarith
  have hst' : hs ≤ ht := by
    dsimp [hs, ht]
    exact (div_le_div_iff_of_pos_right hnreal).2 hbst
  have hhsn : (n : ℝ) * hs =
      targetBoundary (segmentCurve state.x state.p q s) s v := by
    dsimp [hs]
    field_simp
  have hhtn : (n : ℝ) * ht =
      targetBoundary (segmentCurve state.x state.p q t) t v := by
    dsimp [ht]
    field_simp
  have hhs_cross :
      targetNatHeightCrossing n state.x state.p q b hs = s := by
    have huniq : s = targetSegmentCrossing state.x state.p q
        ((n : ℝ) * hs) b := by
      apply targetSegmentCrossing_unique (lam := lam) (x0 := state.x)
        (p0 := state.p) (q := q) (s := (n : ℝ) * hs) (b := b) (x := s)
        hb0 hb2 hq hlam0 hlamHalf
      rw [hhsn]
      simp [targetBoundary, b]
      ring
    simpa [targetNatHeightCrossing] using huniq.symm
  have hht_cross :
      targetNatHeightCrossing n state.x state.p q b ht = t := by
    have huniq : t = targetSegmentCrossing state.x state.p q
        ((n : ℝ) * ht) b := by
      apply targetSegmentCrossing_unique (lam := lam) (x0 := state.x)
        (p0 := state.p) (q := q) (s := (n : ℝ) * ht) (b := b) (x := t)
        hb0 hb2 hq hlam0 hlamHalf
      rw [hhtn]
      simp [targetBoundary, b]
      ring
    simpa [targetNatHeightCrossing] using huniq.symm
  let hsU : UnitMark := ⟨hs, hhs0, hhs1⟩
  let htU : UnitMark := ⟨ht, hht0, hht1⟩
  have hmono : StrictMono (targetNatHeightCrossing n state.x state.p q b) :=
    targetNatHeightCrossing_strictMono hn hb0 hb2 hq hlam0 hlamHalf
  have hmem (h : UnitMark) :
      (h, v) ∈ targetRawRemainingSetAt n lam state s \
          targetRawRemainingSetAt n lam state t ↔
        h ∈ Ioc hsU htU := by
    constructor
    · intro hz
      have hc := (mem_targetFixedStateCrossing_Ioc_iff state lam s t
        (h, v) hlam0 hlamHalf hst).1 hz
      have hhslt : hs < (h : ℝ) := by
        have hc' : targetNatHeightCrossing n state.x state.p q b hs <
            targetNatHeightCrossing n state.x state.p q b (h : ℝ) := by
          rw [hhs_cross]
          simpa [targetFixedStateCrossing, targetNatHeightCrossing, q, b] using hc.1
        exact (hmono.lt_iff_lt).1 hc'
      have hhlt : (h : ℝ) ≤ ht := by
        have hc' : targetNatHeightCrossing n state.x state.p q b (h : ℝ) ≤
            targetNatHeightCrossing n state.x state.p q b ht := by
          rw [hht_cross]
          simpa [targetFixedStateCrossing, targetNatHeightCrossing, q, b] using hc.2
        exact (hmono.le_iff_le).1 hc'
      exact ⟨hhslt, hhlt⟩
    · intro hh
      have hc : targetNatHeightCrossing n state.x state.p q b (h : ℝ) ∈ Ioc s t := by
        rw [← hhs_cross, ← hht_cross]
        exact ⟨hmono hh.1, hmono.monotone hh.2⟩
      exact (mem_targetFixedStateCrossing_Ioc_iff state lam s t
        (h, v) hlam0 hlamHalf hst).2 hc
  have hindicator :
      (∫ h : UnitMark,
        (targetRawRemainingSetAt n lam state s \
          targetRawRemainingSetAt n lam state t).indicator
          (fun z ↦ φ (targetFixedStateCrossing n lam state z)) (h, v)
          ∂(unitUniform : Measure UnitMark)) =
      ∫ h : UnitMark,
        (Ioc hsU htU).indicator
          (fun h ↦ φ (targetNatHeightCrossing n state.x state.p q b (h : ℝ))) h
          ∂(unitUniform : Measure UnitMark) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun h ↦ by
      change (targetRawRemainingSetAt n lam state s \
          targetRawRemainingSetAt n lam state t).indicator
          (fun z ↦ φ (targetFixedStateCrossing n lam state z)) (h, v) =
        (Ioc hsU htU).indicator
          (fun h ↦ φ (targetNatHeightCrossing n state.x state.p q b (h : ℝ))) h
      by_cases hh : (h, v) ∈
          targetRawRemainingSetAt n lam state s \
            targetRawRemainingSetAt n lam state t
      · rw [Set.indicator_of_mem hh]
        rw [Set.indicator_of_mem ((hmem h).1 hh)]
        simp [targetFixedStateCrossing, targetNatHeightCrossing, q, b]
      · have hhn : h ∉ Ioc hsU htU := by
          intro hcontr
          exact hh ((hmem h).2 hcontr)
        simp [Set.indicator, hh, hhn]
  have hsub :
      (∫ h : UnitMark,
        (Ioc hsU htU).indicator
          (fun h ↦ φ (targetNatHeightCrossing n state.x state.p q b (h : ℝ))) h
          ∂(unitUniform : Measure UnitMark)) =
      ∫ r : ℝ in Icc (0 : ℝ) 1,
        (Ioc hs ht).indicator
          (fun r ↦ φ (targetNatHeightCrossing n state.x state.p q b r)) r := by
    change (∫ h : UnitMark,
      (Ioc hsU htU).indicator
        (fun h ↦ φ (targetNatHeightCrossing n state.x state.p q b (h : ℝ))) h
        ∂(volume : Measure UnitMark)) = _
    have hpoint : ∀ h : UnitMark,
        (Ioc hsU htU).indicator
            (fun h ↦ φ (targetNatHeightCrossing n state.x state.p q b (h : ℝ))) h =
          (Ioc hs ht).indicator
            (fun r ↦ φ (targetNatHeightCrossing n state.x state.p q b r)) (h : ℝ) := by
      intro h
      by_cases hh : h ∈ Ioc hsU htU
      · have hh' : (h : ℝ) ∈ Ioc hs ht := by exact hh
        simp [Set.indicator_of_mem hh, Set.indicator_of_mem hh', hsU, htU]
      · have hh' : (h : ℝ) ∉ Ioc hs ht := by
          intro hcontr
          exact hh hcontr
        simp [Set.indicator, hh, hh', hsU, htU]
    calc
      (∫ h : UnitMark,
        (Ioc hsU htU).indicator
          (fun h ↦ φ (targetNatHeightCrossing n state.x state.p q b (h : ℝ))) h
          ∂(volume : Measure UnitMark)) =
        ∫ h : UnitMark,
          (Ioc hs ht).indicator
            (fun r ↦ φ (targetNatHeightCrossing n state.x state.p q b r)) (h : ℝ)
            ∂(volume : Measure UnitMark) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hpoint
      _ = ∫ r : ℝ in Icc (0 : ℝ) 1,
          (Ioc hs ht).indicator
            (fun r ↦ φ (targetNatHeightCrossing n state.x state.p q b r)) r := by
        simpa [UnitMark] using
          (integral_subtype (G := ℝ) (s := Icc (0 : ℝ) 1) measurableSet_Icc
            (fun r : ℝ ↦
              (Ioc hs ht).indicator
                (fun r ↦ φ (targetNatHeightCrossing n state.x state.p q b r)) r))
  have hIoc_sub : Ioc hs ht ⊆ Ioc (0 : ℝ) 1 := by
    intro r hr
    exact ⟨lt_of_le_of_lt hhs0 hr.1, hr.2.trans hht1⟩
  have hreal :
      (∫ r : ℝ in Icc (0 : ℝ) 1,
        (Ioc hs ht).indicator
          (fun r ↦ φ (targetNatHeightCrossing n state.x state.p q b r)) r) =
      ∫ r : ℝ in Ioc hs ht,
        φ (targetNatHeightCrossing n state.x state.p q b r) := by
    rw [integral_Icc_eq_integral_Ioc]
    change (∫ r : ℝ,
      (Ioc hs ht).indicator
        (fun r ↦ φ (targetNatHeightCrossing n state.x state.p q b r)) r
        ∂(volume.restrict (Ioc (0 : ℝ) 1))) = _
    rw [integral_indicator measurableSet_Ioc]
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr hIoc_sub]
  calc
    (∫ h : UnitMark,
        (targetRawRemainingSetAt n lam state s \
          targetRawRemainingSetAt n lam state t).indicator
          (fun z ↦ φ (targetFixedStateCrossing n lam state z)) (h, v)
          ∂(unitUniform : Measure UnitMark)) =
      ∫ h : UnitMark,
        (Ioc hsU htU).indicator
          (fun h ↦ φ (targetNatHeightCrossing n state.x state.p q b (h : ℝ))) h
          ∂(unitUniform : Measure UnitMark) := hindicator
    _ =
      ∫ r : ℝ in Icc (0 : ℝ) 1,
        (Ioc hs ht).indicator
          (fun r ↦ φ (targetNatHeightCrossing n state.x state.p q b r)) r := hsub
    _ = ∫ r : ℝ in Ioc hs ht,
        φ (targetNatHeightCrossing n state.x state.p q b r) := hreal
    _ = ∫ r in hs..ht,
        φ (targetNatHeightCrossing n state.x state.p q b r) :=
          (intervalIntegral.integral_of_le hst').symm
    _ = (1 + b * q) / (n : ℝ) * (∫ y in s..t, φ y) :=
      intervalIntegral_targetNatHeightCrossing_pre n state.x state.p q lam b hs ht s t
        hn hb0 hb2 hq hlam0 hlamHalf hhs_cross hht_cross φ hφ
    _ = ∫ y in s..t,
        φ y * targetMarkedFactor q (v : ℝ) / (n : ℝ) := by
      simp [b, targetMarkedFactor]; ring

end OTSelector
