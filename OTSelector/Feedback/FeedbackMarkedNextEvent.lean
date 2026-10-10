import OTSelector.Feedback.FiniteHistoryNextEvent

/-!
# Mark-weighted next-event laws for finite feedback histories

Keep a continuous test of the actual geometric mark in the one-point affine change of variables
and the full product law of the unseen points. The mark is never replaced by an independent draw.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace OTSelector

variable {n : ℕ}

/-- The one-point source crossing law retains an arbitrary continuous mark test. -/
theorem unitSquareUniform_sourceFixedStateCrossing_marked_slab_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t, ∀ u : UnitMark,
      0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
      sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    (∫ z : MarkedHeight,
      (sourceRawRemainingSetAt n lam state s \
        sourceRawRemainingSetAt n lam state t).indicator
        (fun z ↦ φ (sourceFixedStateCrossing n lam state z) * ψ z.2) z
        ∂(unitSquareUniform : Measure MarkedHeight)) =
      (∫ y in s..t, φ y) *
        (∫ u : UnitMark, ψ u * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)
          ∂(unitUniform : Measure UnitMark)) := by
  let slab : Set MarkedHeight :=
    sourceRawRemainingSetAt n lam state s \ sourceRawRemainingSetAt n lam state t
  let f : MarkedHeight → ℝ := slab.indicator
    (fun z ↦ φ (sourceFixedStateCrossing n lam state z) * ψ z.2)
  have hc : Continuous (fun z : MarkedHeight ↦
      φ (sourceFixedStateCrossing n lam state z) * ψ z.2) :=
    (hφ.comp (continuous_sourceFixedStateCrossing state lam hlam0 hlamHalf)).mul
      (hψ.comp continuous_snd)
  have hfull : Integrable (fun z : MarkedHeight ↦
      φ (sourceFixedStateCrossing n lam state z) * ψ z.2)
      (unitSquareUniform : Measure MarkedHeight) := by
    simpa [integrableOn_univ] using hc.continuousOn.integrableOn_compact
      (K := (univ : Set MarkedHeight)) (μ := (unitSquareUniform : Measure MarkedHeight)) isCompact_univ
  have hf : Integrable f ((unitUniform : Measure UnitMark).prod unitUniform) := by
    simpa [unitSquareUniform_toMeasure] using
      hfull.indicator (measurableSet_sourceFixedStateSlab state lam s t)
  have hfixed (u : UnitMark) :
      (∫ h : UnitMark, f (h, u) ∂(unitUniform : Measure UnitMark)) =
        (∫ y in s..t, φ y) * (ψ u * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)) := by
    have h := unitUniform_sourceFixedStateCrossing_slab_integral state lam s t u hn hst
      hlam0 hlamHalf (fun y hy ↦ hbulk y hy u) (fun y ↦ φ y * ψ u) (hφ.mul continuous_const)
    change (∫ h : UnitMark, f (h, u) ∂(unitUniform : Measure UnitMark)) = _
    calc
      _ = ∫ y in s..t, (φ y * ψ u) * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ) := h
      _ = _ := by
        simp_rw [mul_div_assoc, mul_assoc]
        rw [intervalIntegral.integral_mul_const]
  calc
    _ = ∫ u : UnitMark, ∫ h : UnitMark, f (h, u)
        ∂(unitUniform : Measure UnitMark) ∂(unitUniform : Measure UnitMark) := by
      rw [unitSquareUniform_toMeasure]
      exact integral_prod_symm f hf
    _ = ∫ u : UnitMark, (∫ y in s..t, φ y) *
        (ψ u * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ))
        ∂(unitUniform : Measure UnitMark) :=
      integral_congr_ae (Filter.Eventually.of_forall hfixed)
    _ = _ := integral_const_mul _ _

/-- The one-point target crossing law retains an arbitrary continuous mark test. -/
theorem unitSquareUniform_targetFixedStateCrossing_marked_slab_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t, ∀ u : UnitMark,
      0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
      targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    (∫ z : MarkedHeight,
      (targetRawRemainingSetAt n lam state s \
        targetRawRemainingSetAt n lam state t).indicator
        (fun z ↦ φ (targetFixedStateCrossing n lam state z) * ψ z.2) z
        ∂(unitSquareUniform : Measure MarkedHeight)) =
      (∫ y in s..t, φ y) *
        (∫ u : UnitMark, ψ u * targetMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)
          ∂(unitUniform : Measure UnitMark)) := by
  let slab : Set MarkedHeight :=
    targetRawRemainingSetAt n lam state s \ targetRawRemainingSetAt n lam state t
  let f : MarkedHeight → ℝ := slab.indicator
    (fun z ↦ φ (targetFixedStateCrossing n lam state z) * ψ z.2)
  have hc : Continuous (fun z : MarkedHeight ↦
      φ (targetFixedStateCrossing n lam state z) * ψ z.2) :=
    (hφ.comp (continuous_targetFixedStateCrossing state lam hlam0 hlamHalf)).mul
      (hψ.comp continuous_snd)
  have hfull : Integrable (fun z : MarkedHeight ↦
      φ (targetFixedStateCrossing n lam state z) * ψ z.2)
      (unitSquareUniform : Measure MarkedHeight) := by
    simpa [integrableOn_univ] using hc.continuousOn.integrableOn_compact
      (K := (univ : Set MarkedHeight)) (μ := (unitSquareUniform : Measure MarkedHeight)) isCompact_univ
  have hf : Integrable f ((unitUniform : Measure UnitMark).prod unitUniform) := by
    simpa [unitSquareUniform_toMeasure] using
      hfull.indicator (measurableSet_targetFixedStateSlab state lam s t)
  have hfixed (u : UnitMark) :
      (∫ h : UnitMark, f (h, u) ∂(unitUniform : Measure UnitMark)) =
        (∫ y in s..t, φ y) * (ψ u * targetMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)) := by
    have h := unitUniform_targetFixedStateCrossing_slab_integral state lam s t u hn hst
      hlam0 hlamHalf (fun y hy ↦ hbulk y hy u) (fun y ↦ φ y * ψ u) (hφ.mul continuous_const)
    change (∫ h : UnitMark, f (h, u) ∂(unitUniform : Measure UnitMark)) = _
    calc
      _ = ∫ y in s..t, (φ y * ψ u) * targetMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ) := h
      _ = _ := by
        simp_rw [mul_div_assoc, mul_assoc]
        rw [intervalIntegral.integral_mul_const]
  calc
    _ = ∫ u : UnitMark, ∫ h : UnitMark, f (h, u)
        ∂(unitUniform : Measure UnitMark) ∂(unitUniform : Measure UnitMark) := by
      rw [unitSquareUniform_toMeasure]
      exact integral_prod_symm f hf
    _ = ∫ u : UnitMark, (∫ y in s..t, φ y) *
        (ψ u * targetMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ))
        ∂(unitUniform : Measure UnitMark) :=
      integral_congr_ae (Filter.Eventually.of_forall hfixed)
    _ = _ := integral_const_mul _ _

/-- The full unseen product law preserves the value of the selected point when the remaining
coordinates are integrated out. This supplies the actual geometric mark, including next-event
selection bias. -/
theorem feedbackUnseenTupleLaw_feedbackNextEventSet_test_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (g : MarkedHeight → ℝ) (hg : Continuous g) :
    (∫ unseen in feedbackNextEventSet lam state s t S label,
        g (unseen label) ∂feedbackUnseenTupleLaw S) =
      ∫ z : MarkedHeight,
        (feedbackLabelRemainingSetAt lam state s label \
          feedbackLabelRemainingSetAt lam state t label).indicator
          (fun z ↦ g z * feedbackOtherSurvivalMassAt lam state
            (feedbackLabelFixedStateCrossing n lam state label z) S label) z
          ∂(unitSquareUniform : Measure MarkedHeight) := by
  let A := feedbackNextEventSet lam state s t S label
  let slab := feedbackLabelRemainingSetAt lam state s label \
    feedbackLabelRemainingSetAt lam state t label
  let otherLaw := Measure.pi fun _ : feedbackOtherUnseenLabels S label ↦
    (unitSquareUniform : Measure MarkedHeight)
  let : IsProbabilityMeasure (feedbackUnseenTupleLaw S) := by
    unfold feedbackUnseenTupleLaw
    infer_instance
  have hA : MeasurableSet A :=
    measurableSet_feedbackNextEventSet state lam s t S label hlam0 hlamHalf
  have hgc : Continuous (fun unseen : feedbackUnseenFinset S → MarkedHeight ↦ g (unseen label)) :=
    hg.comp (continuous_apply label)
  have hgi : Integrable (fun unseen : feedbackUnseenFinset S → MarkedHeight ↦ g (unseen label))
      (feedbackUnseenTupleLaw S) := by
    simpa only [integrableOn_univ] using hgc.continuousOn.integrableOn_compact
      (K := univ) (μ := feedbackUnseenTupleLaw S) isCompact_univ
  have hF := hgi.indicator hA
  rw [← integral_indicator hA]
  change (∫ unseen, A.indicator (fun unseen ↦ g (unseen label)) unseen
    ∂(Measure.pi fun _ : feedbackUnseenFinset S ↦ (unitSquareUniform : Measure MarkedHeight))) = _
  rw [Probability.integral_piSplitAt (unitSquareUniform : Measure MarkedHeight) label hF]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z ↦ by
    have hfiber (rest : feedbackOtherUnseenLabels S label → MarkedHeight) :
        A.indicator (fun unseen ↦ g (unseen label)) (Probability.piMergeAt label z rest) =
          if z ∈ slab then (feedbackNextEventRestSet lam state S label z).indicator
            (fun _ ↦ g z) rest else 0 := by
      have hm := piMergeAt_mem_feedbackNextEventSet_iff
        state lam s t S label z rest hlam0 hlamHalf hst
      change Probability.piMergeAt label z rest ∈ A ↔
        z ∈ slab ∧ rest ∈ feedbackNextEventRestSet lam state S label z at hm
      simp only [Set.indicator, Probability.piMergeAt_at]
      by_cases hz : z ∈ slab <;>
        by_cases hr : rest ∈ feedbackNextEventRestSet lam state S label z <;>
        simp [hm, hz, hr]
    by_cases hz : z ∈ slab
    · have hcross := (mem_feedbackLabelRemainingSetAt_sdiff_iff_crossing_Ioc
        state lam s t label z hlam0 hlamHalf hst).mp hz
      have hmass := feedbackNextEventRestSet_real_eq_feedbackOtherSurvivalMassAt
        state lam s t S label z hn ⟨hcross.1.le, hcross.2⟩ hbulk
      simp_rw [hfiber, ite_eq_left hz]
      rw [integral_indicator (measurableSet_feedbackNextEventRestSet lam state S label z),
        integral_const]
      simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
      change otherLaw.real (feedbackNextEventRestSet lam state S label z) * g z =
        slab.indicator (fun z ↦ g z * feedbackOtherSurvivalMassAt lam state
          (feedbackLabelFixedStateCrossing n lam state label z) S label) z
      rw [Set.indicator_of_mem hz, hmass, mul_comm]
    · simp_rw [hfiber, ite_eq_right hz]
      rw [integral_zero]
      exact (Set.indicator_of_notMem hz _).symm

/-- Actual product-law next-event identity for a specified unseen source, retaining its mark. -/
theorem feedbackUnseenTupleLaw_sourceNextEvent_marked_integral
    (state : FeedbackStepState n) (lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (i : Fin n) (hi : (Sum.inl i : FeedbackLabel n) ∈ feedbackUnseenFinset S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    (∫ unseen in feedbackNextEventSet lam state s t S ⟨Sum.inl i, hi⟩,
        ψ (unseen ⟨Sum.inl i, hi⟩).2 ∂feedbackUnseenTupleLaw S) =
      (∫ y in s..t, feedbackOtherSurvivalMassAt lam state y S (Sum.inl i)) *
        (∫ u : UnitMark, ψ u * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)
          ∂(unitUniform : Measure UnitMark)) := by
  rw [feedbackUnseenTupleLaw_feedbackNextEventSet_test_integral
    state lam s t S ⟨Sum.inl i, hi⟩ hn hst hlam0 hlamHalf hbulk
    (fun z : MarkedHeight ↦ ψ z.2) (hψ.comp continuous_snd)]
  simpa only [feedbackLabelRemainingSetAt, feedbackLabelFixedStateCrossing, mul_comm] using
    unitSquareUniform_sourceFixedStateCrossing_marked_slab_integral
      state lam s t hn hst hlam0 hlamHalf (fun y hy ↦ (hbulk y hy).1)
      (fun y ↦ feedbackOtherSurvivalMassAt lam state y S (Sum.inl i))
      (continuous_feedbackOtherSurvivalMassAt hn lam state S (Sum.inl i)) ψ hψ

/-- Actual product-law next-event identity for a specified unseen target, retaining its mark. -/
theorem feedbackUnseenTupleLaw_targetNextEvent_marked_integral
    (state : FeedbackStepState n) (lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (i : Fin n) (hi : (Sum.inr i : FeedbackLabel n) ∈ feedbackUnseenFinset S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    (∫ unseen in feedbackNextEventSet lam state s t S ⟨Sum.inr i, hi⟩,
        ψ (unseen ⟨Sum.inr i, hi⟩).2 ∂feedbackUnseenTupleLaw S) =
      (∫ y in s..t, feedbackOtherSurvivalMassAt lam state y S (Sum.inr i)) *
        (∫ u : UnitMark, ψ u * targetMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)
          ∂(unitUniform : Measure UnitMark)) := by
  rw [feedbackUnseenTupleLaw_feedbackNextEventSet_test_integral
    state lam s t S ⟨Sum.inr i, hi⟩ hn hst hlam0 hlamHalf hbulk
    (fun z : MarkedHeight ↦ ψ z.2) (hψ.comp continuous_snd)]
  simpa only [feedbackLabelRemainingSetAt, feedbackLabelFixedStateCrossing, mul_comm] using
    unitSquareUniform_targetFixedStateCrossing_marked_slab_integral
      state lam s t hn hst hlam0 hlamHalf (fun y hy ↦ (hbulk y hy).2)
      (fun y ↦ feedbackOtherSurvivalMassAt lam state y S (Sum.inr i))
      (continuous_feedbackOtherSurvivalMassAt hn lam state S (Sum.inr i)) ψ hψ

/-- Conditional source mark average on an affine feedback segment. -/
noncomputable def sourceFeedbackMarkMean (q : ℝ) (ψ : UnitMark → ℝ) : ℝ :=
  (∫ u : UnitMark, ψ u * sourceMarkedFactor q u ∂(unitUniform : Measure UnitMark)) / (1 - q / 2)

/-- Conditional target mark average on an affine feedback segment. -/
noncomputable def targetFeedbackMarkMean (q : ℝ) (ψ : UnitMark → ℝ) : ℝ :=
  (∫ u : UnitMark, ψ u * targetMarkedFactor q u ∂(unitUniform : Measure UnitMark)) / (1 + 3 * q / 2)

private theorem integral_centered_markFactor_eq_zero
    (F ψ : UnitMark → ℝ) (hF : Continuous F) (hψ : Continuous ψ)
    (hden : (∫ u, F u ∂(unitUniform : Measure UnitMark)) ≠ 0) (d : ℝ) :
    (∫ u, (ψ u - (∫ v, ψ v * F v ∂(unitUniform : Measure UnitMark)) /
        (∫ v, F v ∂(unitUniform : Measure UnitMark))) * F u / d
      ∂(unitUniform : Measure UnitMark)) = 0 := by
  have hFi : Integrable F (unitUniform : Measure UnitMark) := by
    simpa only [integrableOn_univ] using hF.continuousOn.integrableOn_compact
      (K := univ) (μ := (unitUniform : Measure UnitMark)) isCompact_univ
  have hpi : Integrable (fun u ↦ ψ u * F u) (unitUniform : Measure UnitMark) := by
    change Integrable (ψ * F) (unitUniform : Measure UnitMark)
    simpa only [integrableOn_univ] using (hψ.mul hF).continuousOn.integrableOn_compact
      (K := univ) (μ := (unitUniform : Measure UnitMark)) isCompact_univ
  simp_rw [sub_mul]
  rw [integral_div, integral_sub hpi (hFi.const_mul _), integral_const_mul]
  field_simp
  ring

/-- A selected next source mark, centered by its actual slope-dependent mean, has zero
integral under the full unseen product law. -/
theorem feedbackUnseenTupleLaw_sourceNextEvent_centered_mark_eq_zero
    (state : FeedbackStepState n) (lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (i : Fin n) (hi : (Sum.inl i : FeedbackLabel n) ∈ feedbackUnseenFinset S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    (∫ unseen in feedbackNextEventSet lam state s t S ⟨Sum.inl i, hi⟩,
        (ψ (unseen ⟨Sum.inl i, hi⟩).2 - sourceFeedbackMarkMean (state.slope lam) ψ)
          ∂feedbackUnseenTupleLaw S) = 0 := by
  rw [feedbackUnseenTupleLaw_sourceNextEvent_marked_integral
    state lam s t S i hi hn hst hlam0 hlamHalf hbulk
    (fun u ↦ ψ u - sourceFeedbackMarkMean (state.slope lam) ψ)
    (hψ.sub continuous_const)]
  have hq := abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0
  have hden : (∫ u : UnitMark, sourceMarkedFactor (state.slope lam) u
      ∂(unitUniform : Measure UnitMark)) ≠ 0 := by
    rw [integral_sourceMarkedFactor]
    have hqb : -lam ≤ state.slope lam ∧ state.slope lam ≤ lam := abs_le.mp hq
    linarith [hqb.1, hqb.2]
  have hF : Continuous (fun u : UnitMark ↦ sourceMarkedFactor (state.slope lam) u) := by
    unfold sourceMarkedFactor
    fun_prop
  have hz := integral_centered_markFactor_eq_zero
    (fun u : UnitMark ↦ sourceMarkedFactor (state.slope lam) u) ψ hF hψ hden (n : ℝ)
  rw [integral_sourceMarkedFactor] at hz
  change (∫ y in s..t, feedbackOtherSurvivalMassAt lam state y S (Sum.inl i)) * _ = 0
  rw [show (∫ u : UnitMark, (ψ u - sourceFeedbackMarkMean (state.slope lam) ψ) *
      sourceMarkedFactor (state.slope lam) u / (n : ℝ) ∂(unitUniform : Measure UnitMark)) = 0
      from hz, mul_zero]

/-- A selected next target mark, centered by its actual slope-dependent mean, has zero
integral under the full unseen product law. -/
theorem feedbackUnseenTupleLaw_targetNextEvent_centered_mark_eq_zero
    (state : FeedbackStepState n) (lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (i : Fin n) (hi : (Sum.inr i : FeedbackLabel n) ∈ feedbackUnseenFinset S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    (∫ unseen in feedbackNextEventSet lam state s t S ⟨Sum.inr i, hi⟩,
        (ψ (unseen ⟨Sum.inr i, hi⟩).2 - targetFeedbackMarkMean (state.slope lam) ψ)
          ∂feedbackUnseenTupleLaw S) = 0 := by
  rw [feedbackUnseenTupleLaw_targetNextEvent_marked_integral
    state lam s t S i hi hn hst hlam0 hlamHalf hbulk
    (fun u ↦ ψ u - targetFeedbackMarkMean (state.slope lam) ψ)
    (hψ.sub continuous_const)]
  have hq := abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0
  have hden : (∫ u : UnitMark, targetMarkedFactor (state.slope lam) u
      ∂(unitUniform : Measure UnitMark)) ≠ 0 := by
    rw [integral_targetMarkedFactor]
    have hqb : -lam ≤ state.slope lam ∧ state.slope lam ≤ lam := abs_le.mp hq
    linarith [hqb.1, hqb.2]
  have hF : Continuous (fun u : UnitMark ↦ targetMarkedFactor (state.slope lam) u) := by
    unfold targetMarkedFactor
    fun_prop
  have hz := integral_centered_markFactor_eq_zero
    (fun u : UnitMark ↦ targetMarkedFactor (state.slope lam) u) ψ hF hψ hden (n : ℝ)
  rw [integral_targetMarkedFactor] at hz
  change (∫ y in s..t, feedbackOtherSurvivalMassAt lam state y S (Sum.inr i)) * _ = 0
  rw [show (∫ u : UnitMark, (ψ u - targetFeedbackMarkMean (state.slope lam) ψ) *
      targetMarkedFactor (state.slope lam) u / (n : ℝ) ∂(unitUniform : Measure UnitMark)) = 0
      from hz, mul_zero]

/-- The color-specific actual mark mean for a feedback label. -/
noncomputable def feedbackLabelMarkMean (q : ℝ) (ψ : UnitMark → ℝ) : FeedbackLabel n → ℝ
  | Sum.inl _ => sourceFeedbackMarkMean q ψ
  | Sum.inr _ => targetFeedbackMarkMean q ψ

/-- Centering works for either color and any specified unseen label. -/
theorem feedbackUnseenTupleLaw_nextEvent_centered_mark_eq_zero
    (state : FeedbackStepState n) (lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (label : feedbackUnseenFinset S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    (∫ unseen in feedbackNextEventSet lam state s t S label,
        (ψ (unseen label).2 - feedbackLabelMarkMean (n := n) (state.slope lam) ψ label)
          ∂feedbackUnseenTupleLaw S) = 0 := by
  rcases label with ⟨label, hlabel⟩
  cases label with
  | inl i =>
      exact feedbackUnseenTupleLaw_sourceNextEvent_centered_mark_eq_zero
        state lam s t S i hlabel hn hst hlam0 hlamHalf hbulk ψ hψ
  | inr i =>
      exact feedbackUnseenTupleLaw_targetNextEvent_centered_mark_eq_zero
        state lam s t S i hlabel hn hst hlam0 hlamHalf hbulk ψ hψ

end OTSelector
