import OTSelector.Feedback.FiniteHistoryNextEvent
import OTSelector.Feedback.AdaptiveDeferredDecision
import OTSelector.Probability.IndependentFiberNull

/-!
# Atomless crossing coordinates on finite-history sections

For a fixed affine state, a prescribed crossing coordinate is affine and strictly monotone in the
height once its mark is fixed.  Hence a singleton crossing level has zero unit-square measure.
The same fact is transported to every unseen product law by a coordinate marginal, and then to
next-event sections by monotonicity of measure.  These are endpoint-null facts only; no
certificate or conditional-law interface is introduced here.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## One marked point -/

private theorem measurableSet_feedbackLabelFixedStateCrossing_singleton_preimage
    (state : FeedbackStepState n) (lam : ℝ) (label : FeedbackLabel n)
    (y : ℝ) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet
      {z : MarkedHeight |
        feedbackLabelFixedStateCrossing n lam state label z = y} := by
  exact measurable_feedbackLabelFixedStateCrossing state lam label hlam0 hlamHalf
    (measurableSet_singleton y)

private theorem feedbackLabelFixedStateCrossing_swapped_fibre_subsingleton
    (state : FeedbackStepState n) (lam : ℝ) (label : FeedbackLabel n)
    (y : ℝ) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hn : 0 < n) :
    ∀ m : UnitMark,
      (Prod.mk m ⁻¹'
        {pair : UnitMark × UnitMark |
          feedbackLabelFixedStateCrossing n lam state label (pair.2, pair.1) = y}).Subsingleton := by
  intro m h₁ h₁mem h₂ h₂mem
  cases label with
  | inl i =>
      have ha0 : 0 ≤ 1 - (m : ℝ) := by linarith [m.property.2]
      have ha1 : 1 - (m : ℝ) ≤ 1 := by linarith [m.property.1]
      have hsub := state.sourceHeightCrossing_unit_fibre_subsingleton
        (lam := lam) hlam0 hlamHalf ha0 ha1 hn y
      apply hsub
      · simpa [feedbackLabelFixedStateCrossing, sourceFixedStateCrossing,
          sourceNatHeightCrossing] using h₁mem
      · simpa [feedbackLabelFixedStateCrossing, sourceFixedStateCrossing,
          sourceNatHeightCrossing] using h₂mem
  | inr j =>
      have hm0 : 0 ≤ (m : ℝ) := m.property.1
      have hm1 : (m : ℝ) ≤ 1 := m.property.2
      have hb0 : 1 ≤ 1 + (m : ℝ) := by linarith
      have hb2 : 1 + (m : ℝ) ≤ 2 := by linarith
      have hsub := state.targetHeightCrossing_unit_fibre_subsingleton
        (lam := lam) hlam0 hlamHalf hb0 hb2 hn y
      apply hsub
      · simpa [feedbackLabelFixedStateCrossing, targetFixedStateCrossing,
          targetNatHeightCrossing] using h₁mem
      · simpa [feedbackLabelFixedStateCrossing, targetFixedStateCrossing,
          targetNatHeightCrossing] using h₂mem

theorem unitSquareUniform_feedbackLabelFixedStateCrossing_singleton_eq_zero
    (state : FeedbackStepState n) (lam : ℝ) (label : FeedbackLabel n)
    (y : ℝ) (hn : 0 < n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    (unitSquareUniform : Measure MarkedHeight)
      {z | feedbackLabelFixedStateCrossing n lam state label z = y} = 0 := by
  let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
    change NullSingletonClass (volume : Measure UnitMark)
    infer_instance
  let swapped : Set (UnitMark × UnitMark) :=
    {pair | feedbackLabelFixedStateCrossing n lam state label (pair.2, pair.1) = y}
  have hswapped : MeasurableSet swapped := by
    have hswap : Measurable (fun pair : UnitMark × UnitMark ↦ (pair.2, pair.1)) :=
      measurable_snd.prodMk measurable_fst
    have hcross := (measurable_feedbackLabelFixedStateCrossing state lam label
      hlam0 hlamHalf).comp hswap
    change MeasurableSet
      ((fun pair : UnitMark × UnitMark ↦
        feedbackLabelFixedStateCrossing n lam state label (pair.2, pair.1)) ⁻¹' {y})
    exact measurableSet_preimage hcross (measurableSet_singleton y)
  have hzero :
      ((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)) swapped = 0 := by
    exact measure_prod_eq_zero_of_subsingleton_fibres hswapped
      (feedbackLabelFixedStateCrossing_swapped_fibre_subsingleton
        state lam label y hlam0 hlamHalf hn)
  let original : Set MarkedHeight :=
    {z | feedbackLabelFixedStateCrossing n lam state label z = y}
  have hpre :
      (Prod.swap : MarkedHeight → UnitMark × UnitMark) ⁻¹' swapped = original := by
    ext z
    simp [swapped, original]
  rw [unitSquareUniform_toMeasure]
  change ((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)) original = 0
  rw [← hpre]
  rw [← Measure.map_apply measurable_swap hswapped]
  rw [Measure.prod_swap]
  exact hzero

/-! ## A fixed unseen coordinate under the product law -/

theorem feedbackUnseenTupleLaw_fixedStateCrossing_singleton_eq_zero
    (state : FeedbackStepState n) (lam : ℝ) (S : Finset (FeedbackLabel n))
    (label : feedbackUnseenFinset S) (y : ℝ)
    (hn : 0 < n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    feedbackUnseenTupleLaw S
      {unseen |
        feedbackLabelFixedStateCrossing n lam state (label : FeedbackLabel n)
            (unseen label) = y} = 0 := by
  let C : Set (feedbackUnseenFinset S → MarkedHeight) :=
    {unseen |
      feedbackLabelFixedStateCrossing n lam state (label : FeedbackLabel n)
          (unseen label) = y}
  have hC : MeasurableSet C := by
    have heval : Measurable
        (fun unseen : feedbackUnseenFinset S → MarkedHeight ↦ unseen label) :=
      measurable_pi_apply label
    have hcross := (measurable_feedbackLabelFixedStateCrossing state lam
      (label : FeedbackLabel n) hlam0 hlamHalf).comp heval
    change MeasurableSet
      ((fun unseen : feedbackUnseenFinset S → MarkedHeight ↦
        feedbackLabelFixedStateCrossing n lam state (label : FeedbackLabel n)
          (unseen label)) ⁻¹' {y})
    exact measurableSet_preimage hcross (measurableSet_singleton y)
  have hmap :
      Measure.map (fun unseen : feedbackUnseenFinset S → MarkedHeight ↦ unseen label)
          (feedbackUnseenTupleLaw S) = (unitSquareUniform : Measure MarkedHeight) := by
    simpa [feedbackUnseenTupleLaw] using
      (measurePreserving_eval
        (fun _ : feedbackUnseenFinset S ↦ (unitSquareUniform : Measure MarkedHeight)) label).map_eq
  have hpoint := unitSquareUniform_feedbackLabelFixedStateCrossing_singleton_eq_zero
    state lam (label : FeedbackLabel n) y hn hlam0 hlamHalf
  change (feedbackUnseenTupleLaw S)
      ((fun unseen : feedbackUnseenFinset S → MarkedHeight ↦ unseen label) ⁻¹'
        {z : MarkedHeight |
          feedbackLabelFixedStateCrossing n lam state (label : FeedbackLabel n) z = y}) = 0
  rw [← Measure.map_apply_of_aemeasurable (measurable_pi_apply label).aemeasurable
      (measurableSet_feedbackLabelFixedStateCrossing_singleton_preimage
        state lam (label : FeedbackLabel n) y hlam0 hlamHalf), hmap]
  exact hpoint

/-! ## Endpoint-null parts of next-event sections -/

theorem feedbackUnseenTupleLaw_real_feedbackNextEventSet_inter_fixedStateCrossing_singleton_eq_zero
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S) (y : ℝ)
    (hn : 0 < n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    (feedbackUnseenTupleLaw S).real
      (feedbackNextEventSet lam state s t S label ∩
        {unseen |
          feedbackLabelFixedStateCrossing n lam state (label : FeedbackLabel n)
              (unseen label) = y}) = 0 := by
  rw [Measure.real]
  rw [measure_mono_null
    (inter_subset_right :
      feedbackNextEventSet lam state s t S label ∩
        {unseen |
          feedbackLabelFixedStateCrossing n lam state (label : FeedbackLabel n)
              (unseen label) = y} ⊆
      {unseen |
        feedbackLabelFixedStateCrossing n lam state (label : FeedbackLabel n)
            (unseen label) = y})
    (feedbackUnseenTupleLaw_fixedStateCrossing_singleton_eq_zero
      state lam S label y hn hlam0 hlamHalf)]
  rfl

/-! ## Ambient-label wrapper -/

noncomputable def feedbackLabelFixedStateCrossingCylinder
    (state : FeedbackStepState n) (lam : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) (y : ℝ) :
    Set (feedbackUnseenFinset S → MarkedHeight) :=
  if hlabel : label ∈ feedbackUnseenFinset S then
    {unseen |
      feedbackLabelFixedStateCrossing n lam state label
        (unseen ⟨label, hlabel⟩) = y}
  else ∅

theorem feedbackUnseenTupleLaw_feedbackLabelFixedStateCrossingCylinder_eq_zero
    (state : FeedbackStepState n) (lam : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) (y : ℝ)
    (hn : 0 < n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    feedbackUnseenTupleLaw S
      (feedbackLabelFixedStateCrossingCylinder state lam S label y) = 0 := by
  classical
  by_cases hlabel : label ∈ feedbackUnseenFinset S
  · let ulabel : feedbackUnseenFinset S := ⟨label, hlabel⟩
    have hset :
        feedbackLabelFixedStateCrossingCylinder state lam S label y =
          {unseen |
            feedbackLabelFixedStateCrossing n lam state (ulabel : FeedbackLabel n)
              (unseen ulabel) = y} := by
      ext unseen
      simp only [feedbackLabelFixedStateCrossingCylinder, dite_eq_left hlabel]
      rfl
    rw [hset]
    exact feedbackUnseenTupleLaw_fixedStateCrossing_singleton_eq_zero
      state lam S ulabel y hn hlam0 hlamHalf
  · simp [feedbackLabelFixedStateCrossingCylinder, hlabel]

theorem feedbackUnseenTupleLaw_real_feedbackNextEventSetOfLabel_inter_fixedStateCrossingCylinder_eq_zero
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) (y : ℝ)
    (hn : 0 < n) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    (feedbackUnseenTupleLaw S).real
      (feedbackNextEventSetOfLabel lam state s t S label ∩
        feedbackLabelFixedStateCrossingCylinder state lam S label y) = 0 := by
  have hzero := feedbackUnseenTupleLaw_feedbackLabelFixedStateCrossingCylinder_eq_zero
    state lam S label y hn hlam0 hlamHalf
  have hinter := measure_mono_null
    (μ := feedbackUnseenTupleLaw S) (s :=
      feedbackNextEventSetOfLabel lam state s t S label ∩
        feedbackLabelFixedStateCrossingCylinder state lam S label y)
    (t := feedbackLabelFixedStateCrossingCylinder state lam S label y)
    inter_subset_right hzero
  simpa [Measure.real] using congrArg ENNReal.toReal hinter

end OTSelector
