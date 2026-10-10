import OTSelector.Feedback.FiniteHistoryHazardIntegral
import OTSelector.Feedback.FiniteHistorySurvivalFlux
import OTSelector.Probability.FinitePiCoordinate

/-!
# One-point next-event identities on a fixed feedback section

The height substitution in `FiniteHistoryHazardIntegral` is first stated at a fixed mark.  This
file integrates the mark as well.  The result is the exact one-point law needed when one unseen
label is selected as the next source or target event.

No adaptive conditioning is used here: the state, interval, and test function are deterministic.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## Unified crossing coordinate and next-event set -/

/-- Crossing coordinate of a labelled point on one fixed affine state continuation. -/
noncomputable def feedbackLabelFixedStateCrossing
    (n : ℕ) (lam : ℝ) (state : FeedbackStepState n) :
    FeedbackLabel n → MarkedHeight → ℝ
  | Sum.inl _, z => sourceFixedStateCrossing n lam state z
  | Sum.inr _, z => targetFixedStateCrossing n lam state z

theorem continuous_feedbackLabelFixedStateCrossing
    (state : FeedbackStepState n) (lam : ℝ) (label : FeedbackLabel n)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    Continuous (feedbackLabelFixedStateCrossing n lam state label) := by
  cases label with
  | inl i => exact continuous_sourceFixedStateCrossing state lam hlam0 hlamHalf
  | inr j => exact continuous_targetFixedStateCrossing state lam hlam0 hlamHalf

theorem measurable_feedbackLabelFixedStateCrossing
    (state : FeedbackStepState n) (lam : ℝ) (label : FeedbackLabel n)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    Measurable (feedbackLabelFixedStateCrossing n lam state label) :=
  (continuous_feedbackLabelFixedStateCrossing state lam label hlam0 hlamHalf).measurable

theorem mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
    (state : FeedbackStepState n) (lam : ℝ) (label : FeedbackLabel n)
    (z : MarkedHeight) (x : ℝ)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    z ∈ feedbackLabelRemainingSetAt lam state x label ↔
      x < feedbackLabelFixedStateCrossing n lam state label z := by
  cases label with
  | inl i =>
      exact mem_sourceRawRemainingSetAt_iff_lt_sourceFixedStateCrossing
        state lam z hlam0 hlamHalf x
  | inr j =>
      exact mem_targetRawRemainingSetAt_iff_lt_targetFixedStateCrossing
        state lam z hlam0 hlamHalf x

theorem mem_feedbackLabelRemainingSetAt_sdiff_iff_crossing_Ioc
    (state : FeedbackStepState n) (lam s t : ℝ) (label : FeedbackLabel n)
    (z : MarkedHeight) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hst : s ≤ t) :
    z ∈ feedbackLabelRemainingSetAt lam state s label \
        feedbackLabelRemainingSetAt lam state t label ↔
      feedbackLabelFixedStateCrossing n lam state label z ∈ Ioc s t := by
  cases label with
  | inl i =>
      exact mem_sourceFixedStateCrossing_Ioc_iff state lam s t z
        hlam0 hlamHalf hst
  | inr j =>
      exact mem_targetFixedStateCrossing_Ioc_iff state lam s t z
        hlam0 hlamHalf hst

/-- The selected unseen label crosses in `(s,t]` and strictly precedes every other unseen label.
Ties are excluded here; the point law later shows that tie configurations are null. -/
def feedbackNextEventSet
    (lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S) :
    Set (feedbackUnseenFinset S → MarkedHeight) :=
  {unseen |
    feedbackLabelFixedStateCrossing n lam state label (unseen label) ∈ Ioc s t ∧
      ∀ other : feedbackUnseenFinset S, other ≠ label →
        feedbackLabelFixedStateCrossing n lam state label (unseen label) <
          feedbackLabelFixedStateCrossing n lam state other (unseen other)}

/-- The next-event set indexed by an ambient label.  Labels already present in `S` contribute the
empty set; this proof-independent wrapper is convenient for finite sums over source or target
labels. -/
noncomputable def feedbackNextEventSetOfLabel
    (lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) :
    Set (feedbackUnseenFinset S → MarkedHeight) :=
  if hlabel : label ∈ feedbackUnseenFinset S then
    feedbackNextEventSet lam state s t S ⟨label, hlabel⟩
  else ∅

theorem measurableSet_feedbackNextEventSet
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet (feedbackNextEventSet lam state s t S label) := by
  let crossing (other : feedbackUnseenFinset S) :=
    fun unseen : feedbackUnseenFinset S → MarkedHeight ↦
      feedbackLabelFixedStateCrossing n lam state other (unseen other)
  have hcrossing (other : feedbackUnseenFinset S) : Measurable (crossing other) :=
    (measurable_feedbackLabelFixedStateCrossing state lam other hlam0 hlamHalf).comp
      (measurable_pi_apply other)
  have hslab : MeasurableSet {unseen | crossing label unseen ∈ Ioc s t} :=
    hcrossing label measurableSet_Ioc
  have hother (other : feedbackUnseenFinset S) :
      MeasurableSet {unseen | other ≠ label → crossing label unseen < crossing other unseen} := by
    by_cases hEq : other = label
    · simp [hEq]
    · simpa [hEq] using measurableSet_lt (hcrossing label) (hcrossing other)
  have hall : MeasurableSet
      {unseen | ∀ other : feedbackUnseenFinset S,
        other ≠ label → crossing label unseen < crossing other unseen} := by
    rw [show {unseen | ∀ other : feedbackUnseenFinset S,
        other ≠ label → crossing label unseen < crossing other unseen} =
      ⋂ other, {unseen | other ≠ label →
        crossing label unseen < crossing other unseen} by
          ext unseen
          simp]
    exact MeasurableSet.iInter hother
  change MeasurableSet
    ({unseen | crossing label unseen ∈ Ioc s t} ∩
      {unseen | ∀ other : feedbackUnseenFinset S,
        other ≠ label → crossing label unseen < crossing other unseen})
  exact hslab.inter hall

theorem measurableSet_feedbackNextEventSetOfLabel
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet (feedbackNextEventSetOfLabel lam state s t S label) := by
  classical
  unfold feedbackNextEventSetOfLabel
  split_ifs with hlabel
  · exact measurableSet_feedbackNextEventSet state lam s t S ⟨label, hlabel⟩
      hlam0 hlamHalf
  · exact MeasurableSet.empty

theorem mem_feedbackNextEventSet_iff_remaining
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t) :
    unseen ∈ feedbackNextEventSet lam state s t S label ↔
      unseen label ∈
          feedbackLabelRemainingSetAt lam state s label \
            feedbackLabelRemainingSetAt lam state t label ∧
        ∀ other : feedbackUnseenFinset S, other ≠ label →
          unseen other ∈ feedbackLabelRemainingSetAt lam state
            (feedbackLabelFixedStateCrossing n lam state label (unseen label)) other := by
  constructor
  · intro h
    refine ⟨(mem_feedbackLabelRemainingSetAt_sdiff_iff_crossing_Ioc
      state lam s t label (unseen label) hlam0 hlamHalf hst).2 h.1, ?_⟩
    intro other hne
    exact (mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
      state lam other (unseen other)
        (feedbackLabelFixedStateCrossing n lam state label (unseen label))
        hlam0 hlamHalf).2 (h.2 other hne)
  · intro h
    refine ⟨(mem_feedbackLabelRemainingSetAt_sdiff_iff_crossing_Ioc
      state lam s t label (unseen label) hlam0 hlamHalf hst).1 h.1, ?_⟩
    intro other hne
    exact (mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
      state lam other (unseen other)
        (feedbackLabelFixedStateCrossing n lam state label (unseen label))
        hlam0 hlamHalf).1 (h.2 other hne)

/-- Unseen labels other than one selected label. -/
abbrev feedbackOtherUnseenLabels
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S) :=
  {other : feedbackUnseenFinset S // other ≠ label}

/-- Product of the remaining masses of every unseen label except `label`. -/
noncomputable def feedbackOtherSurvivalMassAt
    (lam : ℝ) (state : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) : ℝ :=
  ∏ label' ∈ (feedbackUnseenFinset S).erase label,
    feedbackLabelRemainingRealMassAt lam state x label'

/-- Remaining-coordinate fibre after the selected point has fixed the next crossing coordinate. -/
def feedbackNextEventRestSet
    (lam : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (z : MarkedHeight) :
    Set (feedbackOtherUnseenLabels S label → MarkedHeight) :=
  Set.univ.pi fun other ↦
    feedbackLabelRemainingSetAt lam state
      (feedbackLabelFixedStateCrossing n lam state label z) other.1

theorem measurableSet_feedbackNextEventRestSet
    (lam : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (z : MarkedHeight) :
    MeasurableSet (feedbackNextEventRestSet lam state S label z) := by
  exact MeasurableSet.univ_pi fun other ↦
    measurableSet_feedbackLabelRemainingSetAt lam state
      (feedbackLabelFixedStateCrossing n lam state label z) other.1

/-- Splitting off the selected coordinate turns the next-event condition into the selected slab
and the rectangular survival condition for all other unseen labels. -/
theorem piMergeAt_mem_feedbackNextEventSet_iff
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (z : MarkedHeight) (rest : feedbackOtherUnseenLabels S label → MarkedHeight)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hst : s ≤ t) :
    OTSelector.Probability.piMergeAt label z rest ∈
        feedbackNextEventSet lam state s t S label ↔
      z ∈ feedbackLabelRemainingSetAt lam state s label \
          feedbackLabelRemainingSetAt lam state t label ∧
        rest ∈ feedbackNextEventRestSet lam state S label z := by
  rw [mem_feedbackNextEventSet_iff_remaining state lam s t S label
    (OTSelector.Probability.piMergeAt label z rest) hlam0 hlamHalf hst]
  simp only [OTSelector.Probability.piMergeAt_at]
  constructor
  · rintro ⟨hz, hrest⟩
    refine ⟨hz, Set.mem_pi.mpr fun other _hother ↦ ?_⟩
    have hmem := hrest other.1 other.2
    rw [OTSelector.Probability.piMergeAt_other label other.1 z rest other.2] at hmem
    exact hmem
  · rintro ⟨hz, hrest⟩
    refine ⟨hz, fun other hne ↦ ?_⟩
    have hmem := Set.mem_pi.mp hrest ⟨other, hne⟩ (Set.mem_univ _)
    rw [OTSelector.Probability.piMergeAt_other label other z rest hne]
    exact hmem

theorem prod_feedbackOtherUnseenLabels_eq_feedbackOtherSurvivalMassAt
    (lam : ℝ) (state : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S) :
    (∏ other : feedbackOtherUnseenLabels S label,
      feedbackLabelRemainingRealMassAt lam state x other.1) =
      feedbackOtherSurvivalMassAt lam state x S label := by
  classical
  calc
    (∏ other : feedbackOtherUnseenLabels S label,
        feedbackLabelRemainingRealMassAt lam state x other.1) =
        ∏ other ∈ (Finset.univ.erase label),
          feedbackLabelRemainingRealMassAt lam state x other := by
      symm
      apply Finset.prod_subtype
      intro other
      simp
    _ = ∏ other ∈ (feedbackUnseenFinset S).erase (label : FeedbackLabel n),
        feedbackLabelRemainingRealMassAt lam state x other := by
      simpa [Finset.univ_eq_attach] using
        (Finset.prod_erase_attach
          (fun other : FeedbackLabel n ↦
            feedbackLabelRemainingRealMassAt lam state x other) label)
    _ = feedbackOtherSurvivalMassAt lam state x S label := by
      rfl

/-- The product law of all other unseen labels gives exactly their survival-mass product at the
selected crossing coordinate. -/
theorem feedbackNextEventRestSet_real_eq_feedbackOtherSurvivalMassAt
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (z : MarkedHeight) (hn : 0 < n)
    (hcross : feedbackLabelFixedStateCrossing n lam state label z ∈ Icc s t)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n) :
    (Measure.pi fun _ : feedbackOtherUnseenLabels S label ↦
        (unitSquareUniform : Measure MarkedHeight)).real
        (feedbackNextEventRestSet lam state S label z) =
      feedbackOtherSurvivalMassAt lam state
        (feedbackLabelFixedStateCrossing n lam state label z) S label := by
  classical
  let x := feedbackLabelFixedStateCrossing n lam state label z
  let remaining : feedbackOtherUnseenLabels S label → Set MarkedHeight := fun other ↦
    feedbackLabelRemainingSetAt lam state x other.1
  have hfactor (other : feedbackOtherUnseenLabels S label) :
      (unitSquareUniform : Measure MarkedHeight).real (remaining other) =
        feedbackLabelRemainingRealMassAt lam state x other.1 := by
    exact (feedbackLabelRemainingRealMassAt_eq_unitSquareUniform_real
      hn lam state x other.1 (hbulk x hcross)).symm
  calc
    (Measure.pi fun _ : feedbackOtherUnseenLabels S label ↦
        (unitSquareUniform : Measure MarkedHeight)).real
        (feedbackNextEventRestSet lam state S label z) =
        ∏ other : feedbackOtherUnseenLabels S label,
          (unitSquareUniform : Measure MarkedHeight).real (remaining other) := by
      simp only [feedbackNextEventRestSet, remaining, x, measureReal_def,
        Measure.pi_pi, ENNReal.toReal_prod]
    _ = ∏ other : feedbackOtherUnseenLabels S label,
        feedbackLabelRemainingRealMassAt lam state x other.1 := by
      apply Finset.prod_congr rfl
      intro other _hother
      exact hfactor other
    _ = feedbackOtherSurvivalMassAt lam state x S label :=
      prod_feedbackOtherUnseenLabels_eq_feedbackOtherSurvivalMassAt lam state x S label

/-- Exact full-product law for one selected next event.  After exposing the selected coordinate,
the other unseen coordinates contribute their survival-mass product. -/
theorem feedbackUnseenTupleLaw_real_feedbackNextEventSet_eq_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n) :
    (feedbackUnseenTupleLaw S).real (feedbackNextEventSet lam state s t S label) =
      ∫ z : MarkedHeight,
        (feedbackLabelRemainingSetAt lam state s label \
          feedbackLabelRemainingSetAt lam state t label).indicator
          (fun z ↦ feedbackOtherSurvivalMassAt lam state
            (feedbackLabelFixedStateCrossing n lam state label z) S label) z
        ∂(unitSquareUniform : Measure MarkedHeight) := by
  classical
  let A := feedbackNextEventSet lam state s t S label
  let slab := feedbackLabelRemainingSetAt lam state s label \
    feedbackLabelRemainingSetAt lam state t label
  let otherLaw := Measure.pi fun _ : feedbackOtherUnseenLabels S label ↦
    (unitSquareUniform : Measure MarkedHeight)
  have hA : MeasurableSet A :=
    measurableSet_feedbackNextEventSet state lam s t S label hlam0 hlamHalf
  have hfinite : (feedbackUnseenTupleLaw S) Set.univ ≠ ⊤ := by
    simp [feedbackUnseenTupleLaw]
  have hone : Integrable
      (fun _ : feedbackUnseenFinset S → MarkedHeight ↦ (1 : ℝ))
      (feedbackUnseenTupleLaw S) := by
    simpa [integrableOn_univ] using
      (integrableOn_const (μ := feedbackUnseenTupleLaw S)
        (s := Set.univ) (C := (1 : ℝ)) hfinite)
  have hF : Integrable (A.indicator fun _ ↦ (1 : ℝ)) (feedbackUnseenTupleLaw S) :=
    hone.indicator hA
  have hsplit := OTSelector.Probability.integral_piSplitAt
    (ι := feedbackUnseenFinset S) (α := MarkedHeight)
    (unitSquareUniform : Measure MarkedHeight) label hF
  rw [← integral_indicator_one hA]
  change (∫ unseen, A.indicator (fun _ ↦ (1 : ℝ)) unseen
      ∂(Measure.pi fun _ : feedbackUnseenFinset S ↦
        (unitSquareUniform : Measure MarkedHeight))) = _
  rw [hsplit]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z ↦ by
    by_cases hz : z ∈ slab
    · have hcrossIoc :
          feedbackLabelFixedStateCrossing n lam state label z ∈ Ioc s t :=
        (mem_feedbackLabelRemainingSetAt_sdiff_iff_crossing_Ioc
          state lam s t label z hlam0 hlamHalf hst).1 hz
      have hcross :
          feedbackLabelFixedStateCrossing n lam state label z ∈ Icc s t :=
        ⟨le_of_lt hcrossIoc.1, hcrossIoc.2⟩
      have hrestMeas := measurableSet_feedbackNextEventRestSet lam state S label z
      calc
        (∫ rest,
            A.indicator (fun _ ↦ (1 : ℝ))
              (OTSelector.Probability.piMergeAt label z rest) ∂otherLaw) =
            ∫ rest, (feedbackNextEventRestSet lam state S label z).indicator
              (fun _ ↦ (1 : ℝ)) rest ∂otherLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun rest ↦ by
            by_cases hr : rest ∈ feedbackNextEventRestSet lam state S label z
            · have hmerge : OTSelector.Probability.piMergeAt label z rest ∈ A :=
                (piMergeAt_mem_feedbackNextEventSet_iff
                  state lam s t S label z rest hlam0 hlamHalf hst).2 ⟨hz, hr⟩
              change A.indicator (fun _ ↦ (1 : ℝ))
                  (OTSelector.Probability.piMergeAt label z rest) =
                (feedbackNextEventRestSet lam state S label z).indicator
                  (fun _ ↦ (1 : ℝ)) rest
              rw [Set.indicator_of_mem hmerge, Set.indicator_of_mem hr]
            · have hmerge : OTSelector.Probability.piMergeAt label z rest ∉ A := by
                intro hmem
                exact hr ((piMergeAt_mem_feedbackNextEventSet_iff
                  state lam s t S label z rest hlam0 hlamHalf hst).1 hmem).2
              change A.indicator (fun _ ↦ (1 : ℝ))
                  (OTSelector.Probability.piMergeAt label z rest) =
                (feedbackNextEventRestSet lam state S label z).indicator
                  (fun _ ↦ (1 : ℝ)) rest
              rw [Set.indicator_of_notMem hmerge, Set.indicator_of_notMem hr]
        _ = otherLaw.real (feedbackNextEventRestSet lam state S label z) := by
          change (∫ rest, (feedbackNextEventRestSet lam state S label z).indicator
            (1 : (feedbackOtherUnseenLabels S label → MarkedHeight) → ℝ) rest ∂otherLaw) = _
          exact integral_indicator_one (μ := otherLaw) hrestMeas
        _ = feedbackOtherSurvivalMassAt lam state
            (feedbackLabelFixedStateCrossing n lam state label z) S label := by
          exact feedbackNextEventRestSet_real_eq_feedbackOtherSurvivalMassAt
            state lam s t S label z hn hcross hbulk
        _ = slab.indicator
            (fun z ↦ feedbackOtherSurvivalMassAt lam state
              (feedbackLabelFixedStateCrossing n lam state label z) S label) z := by
          symm
          exact Set.indicator_of_mem hz _
    · have hnever (rest : feedbackOtherUnseenLabels S label → MarkedHeight) :
          OTSelector.Probability.piMergeAt label z rest ∉ A := by
        intro hmem
        exact hz ((piMergeAt_mem_feedbackNextEventSet_iff
          state lam s t S label z rest hlam0 hlamHalf hst).1 hmem).1
      have hzero :
          (fun rest : feedbackOtherUnseenLabels S label → MarkedHeight ↦
            A.indicator (fun _ ↦ (1 : ℝ))
              (OTSelector.Probability.piMergeAt label z rest)) = 0 := by
        funext rest
        exact Set.indicator_of_notMem (hnever rest) _
      change (∫ rest : feedbackOtherUnseenLabels S label → MarkedHeight,
          A.indicator (fun _ ↦ (1 : ℝ))
            (OTSelector.Probability.piMergeAt label z rest) ∂otherLaw) =
        slab.indicator
          (fun z ↦ feedbackOtherSurvivalMassAt lam state
            (feedbackLabelFixedStateCrossing n lam state label z) S label) z
      rw [hzero]
      simp [Set.indicator_of_notMem hz]

/-- Under the product-uniform point law, one source crossing in `(s,t]` has the total source
sweep density `(1-q/2)/n`. -/
theorem unitSquareUniform_sourceFixedStateCrossing_slab_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t, ∀ u : UnitMark,
      0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
      sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    (∫ z : MarkedHeight,
      (sourceRawRemainingSetAt n lam state s \
        sourceRawRemainingSetAt n lam state t).indicator
        (fun z ↦ φ (sourceFixedStateCrossing n lam state z)) z
        ∂(unitSquareUniform : Measure MarkedHeight)) =
      ∫ y in s..t, φ y * (1 - state.slope lam / 2) / (n : ℝ) := by
  let slab : Set MarkedHeight :=
    sourceRawRemainingSetAt n lam state s \
      sourceRawRemainingSetAt n lam state t
  let f : MarkedHeight → ℝ := slab.indicator
    (fun z ↦ φ (sourceFixedStateCrossing n lam state z))
  have hslab : MeasurableSet slab :=
    measurableSet_sourceFixedStateSlab state lam s t
  have hcontinuous : Continuous
      (fun z : MarkedHeight ↦ φ (sourceFixedStateCrossing n lam state z)) :=
    hφ.comp (continuous_sourceFixedStateCrossing state lam hlam0 hlamHalf)
  have hfull : Integrable
      (fun z : MarkedHeight ↦ φ (sourceFixedStateCrossing n lam state z))
      (unitSquareUniform : Measure MarkedHeight) := by
    simpa [integrableOn_univ] using
      hcontinuous.continuousOn.integrableOn_compact
        (K := (Set.univ : Set MarkedHeight)) (μ := (unitSquareUniform : Measure MarkedHeight))
        isCompact_univ
  have hf : Integrable f (unitSquareUniform : Measure MarkedHeight) :=
    hfull.integrableOn.integrable_indicator hslab
  have hfprod : Integrable f
      ((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)) := by
    simpa [unitSquareUniform_toMeasure] using hf
  have hfixed (u : UnitMark) :
      (∫ h : UnitMark, f (h, u) ∂(unitUniform : Measure UnitMark)) =
        ∫ y in s..t,
          φ y * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ) := by
    simpa [f, slab] using
      unitUniform_sourceFixedStateCrossing_slab_integral state lam s t u hn hst
        hlam0 hlamHalf (fun y hy ↦ hbulk y hy u) φ hφ
  have hpull (u : UnitMark) :
      (∫ y in s..t,
          φ y * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)) =
        (∫ y in s..t, φ y) *
          (sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)) := by
    rw [show (fun y : ℝ ↦
        φ y * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)) =
      (fun y : ℝ ↦
        φ y * (sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ))) by
      funext y
      ring]
    rw [intervalIntegral.integral_mul_const]
  calc
    (∫ z : MarkedHeight, f z ∂(unitSquareUniform : Measure MarkedHeight)) =
        ∫ u : UnitMark, ∫ h : UnitMark, f (h, u)
          ∂(unitUniform : Measure UnitMark) ∂(unitUniform : Measure UnitMark) := by
      rw [unitSquareUniform_toMeasure]
      exact integral_prod_symm f hfprod
    _ = ∫ u : UnitMark,
        (∫ y in s..t,
          φ y * sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ))
          ∂(unitUniform : Measure UnitMark) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hfixed
    _ = ∫ u : UnitMark,
        (∫ y in s..t, φ y) *
          (sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ))
          ∂(unitUniform : Measure UnitMark) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpull
    _ = (∫ y in s..t, φ y) *
        (∫ u : UnitMark,
          sourceMarkedFactor (state.slope lam) (u : ℝ) / (n : ℝ)
          ∂(unitUniform : Measure UnitMark)) := by
      rw [integral_const_mul]
    _ = (∫ y in s..t, φ y) *
        ((1 - state.slope lam / 2) / (n : ℝ)) := by
      rw [integral_div, integral_sourceMarkedFactor]
    _ = ∫ y in s..t, φ y * (1 - state.slope lam / 2) / (n : ℝ) := by
      rw [show (fun y : ℝ ↦ φ y * (1 - state.slope lam / 2) / (n : ℝ)) =
        (fun y : ℝ ↦ φ y * ((1 - state.slope lam / 2) / (n : ℝ))) by
          funext y
          ring]
      rw [intervalIntegral.integral_mul_const]

/-- Under the product-uniform point law, one target crossing in `(s,t]` has the total target
sweep density `(1+3q/2)/n`. -/
theorem unitSquareUniform_targetFixedStateCrossing_slab_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t, ∀ v : UnitMark,
      0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
      targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    (∫ z : MarkedHeight,
      (targetRawRemainingSetAt n lam state s \
        targetRawRemainingSetAt n lam state t).indicator
        (fun z ↦ φ (targetFixedStateCrossing n lam state z)) z
        ∂(unitSquareUniform : Measure MarkedHeight)) =
      ∫ y in s..t, φ y * (1 + 3 * state.slope lam / 2) / (n : ℝ) := by
  let slab : Set MarkedHeight :=
    targetRawRemainingSetAt n lam state s \
      targetRawRemainingSetAt n lam state t
  let f : MarkedHeight → ℝ := slab.indicator
    (fun z ↦ φ (targetFixedStateCrossing n lam state z))
  have hslab : MeasurableSet slab :=
    measurableSet_targetFixedStateSlab state lam s t
  have hcontinuous : Continuous
      (fun z : MarkedHeight ↦ φ (targetFixedStateCrossing n lam state z)) :=
    hφ.comp (continuous_targetFixedStateCrossing state lam hlam0 hlamHalf)
  have hfull : Integrable
      (fun z : MarkedHeight ↦ φ (targetFixedStateCrossing n lam state z))
      (unitSquareUniform : Measure MarkedHeight) := by
    simpa [integrableOn_univ] using
      hcontinuous.continuousOn.integrableOn_compact
        (K := (Set.univ : Set MarkedHeight)) (μ := (unitSquareUniform : Measure MarkedHeight))
        isCompact_univ
  have hf : Integrable f (unitSquareUniform : Measure MarkedHeight) :=
    hfull.integrableOn.integrable_indicator hslab
  have hfprod : Integrable f
      ((unitUniform : Measure UnitMark).prod (unitUniform : Measure UnitMark)) := by
    simpa [unitSquareUniform_toMeasure] using hf
  have hfixed (v : UnitMark) :
      (∫ h : UnitMark, f (h, v) ∂(unitUniform : Measure UnitMark)) =
        ∫ y in s..t,
          φ y * targetMarkedFactor (state.slope lam) (v : ℝ) / (n : ℝ) := by
    simpa [f, slab] using
      unitUniform_targetFixedStateCrossing_slab_integral state lam s t v hn hst
        hlam0 hlamHalf (fun y hy ↦ hbulk y hy v) φ hφ
  have hpull (v : UnitMark) :
      (∫ y in s..t,
          φ y * targetMarkedFactor (state.slope lam) (v : ℝ) / (n : ℝ)) =
        (∫ y in s..t, φ y) *
          (targetMarkedFactor (state.slope lam) (v : ℝ) / (n : ℝ)) := by
    rw [show (fun y : ℝ ↦
        φ y * targetMarkedFactor (state.slope lam) (v : ℝ) / (n : ℝ)) =
      (fun y : ℝ ↦
        φ y * (targetMarkedFactor (state.slope lam) (v : ℝ) / (n : ℝ))) by
      funext y
      ring]
    rw [intervalIntegral.integral_mul_const]
  calc
    (∫ z : MarkedHeight, f z ∂(unitSquareUniform : Measure MarkedHeight)) =
        ∫ v : UnitMark, ∫ h : UnitMark, f (h, v)
          ∂(unitUniform : Measure UnitMark) ∂(unitUniform : Measure UnitMark) := by
      rw [unitSquareUniform_toMeasure]
      exact integral_prod_symm f hfprod
    _ = ∫ v : UnitMark,
        (∫ y in s..t,
          φ y * targetMarkedFactor (state.slope lam) (v : ℝ) / (n : ℝ))
          ∂(unitUniform : Measure UnitMark) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hfixed
    _ = ∫ v : UnitMark,
        (∫ y in s..t, φ y) *
          (targetMarkedFactor (state.slope lam) (v : ℝ) / (n : ℝ))
          ∂(unitUniform : Measure UnitMark) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpull
    _ = (∫ y in s..t, φ y) *
        (∫ v : UnitMark,
          targetMarkedFactor (state.slope lam) (v : ℝ) / (n : ℝ)
          ∂(unitUniform : Measure UnitMark)) := by
      rw [integral_const_mul]
    _ = (∫ y in s..t, φ y) *
        ((1 + 3 * state.slope lam / 2) / (n : ℝ)) := by
      rw [integral_div, integral_targetMarkedFactor]
    _ = ∫ y in s..t, φ y * (1 + 3 * state.slope lam / 2) / (n : ℝ) := by
      rw [show (fun y : ℝ ↦ φ y * (1 + 3 * state.slope lam / 2) / (n : ℝ)) =
        (fun y : ℝ ↦ φ y * ((1 + 3 * state.slope lam / 2) / (n : ℝ))) by
          funext y
          ring]
      rw [intervalIntegral.integral_mul_const]

/-! ## One selected label and survival of all other unseen labels -/

theorem continuous_feedbackOtherSurvivalMassAt
    (hn : 0 < n) (lam : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) :
    Continuous (fun x : ℝ ↦ feedbackOtherSurvivalMassAt lam state x S label) := by
  unfold feedbackOtherSurvivalMassAt
  apply continuous_finsetProd
  intro label' _hlabel'
  cases label' with
  | inl i =>
      simpa [feedbackLabelRemainingRealMassAt] using
        (continuous_iff_continuousAt.mpr fun x ↦
          (hasDerivAt_feedbackSourceRemainingRealMassAt hn lam state x).continuousAt)
  | inr j =>
      simpa [feedbackLabelRemainingRealMassAt] using
        (continuous_iff_continuousAt.mpr fun x ↦
          (hasDerivAt_feedbackTargetRemainingRealMassAt hn lam state x).continuousAt)

/-- Cause-specific density for one unseen source label. -/
noncomputable def feedbackSourceLabelNextDensityAt
    (lam : ℝ) (state : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) : ℝ :=
  feedbackOtherSurvivalMassAt lam state x S label *
    (1 - state.slope lam / 2) / (n : ℝ)

/-- Cause-specific density for one unseen target label. -/
noncomputable def feedbackTargetLabelNextDensityAt
    (lam : ℝ) (state : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) : ℝ :=
  feedbackOtherSurvivalMassAt lam state x S label *
    (1 + 3 * state.slope lam / 2) / (n : ℝ)

theorem continuous_feedbackSourceLabelNextDensityAt
    (hn : 0 < n) (lam : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) :
    Continuous (fun x : ℝ ↦ feedbackSourceLabelNextDensityAt lam state x S label) := by
  unfold feedbackSourceLabelNextDensityAt
  exact ((continuous_feedbackOtherSurvivalMassAt hn lam state S label).mul
    continuous_const).div_const (n : ℝ)

theorem continuous_feedbackTargetLabelNextDensityAt
    (hn : 0 < n) (lam : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) :
    Continuous (fun x : ℝ ↦ feedbackTargetLabelNextDensityAt lam state x S label) := by
  unfold feedbackTargetLabelNextDensityAt
  exact ((continuous_feedbackOtherSurvivalMassAt hn lam state S label).mul
    continuous_const).div_const (n : ℝ)

/-- Summing the source cause-specific densities recovers the source survival-loss flux. -/
theorem sum_feedbackSourceLabelNextDensityAt_eq
    (hn : 0 < n) (lam : ℝ) (state : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (hsource : 0 < feedbackSourceRemainingRealMassAt lam state x) :
    ∑ label ∈ feedbackUnseenSourceLabels S,
        feedbackSourceLabelNextDensityAt lam state x S label =
      feedbackSourceSurvivalLossFluxAt lam state x S := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have harea : feedbackSourceRemainingAreaAt lam state x ≠ 0 := by
    intro hzero
    have : feedbackSourceRemainingRealMassAt lam state x = 0 := by
      simp [feedbackSourceRemainingRealMassAt, hzero]
    linarith
  have hterm : ∀ label ∈ feedbackUnseenSourceLabels S,
      feedbackSourceLabelNextDensityAt lam state x S label =
        feedbackUnseenSurvivalMassAt lam state x S *
          (1 / feedbackSourceRemainingAreaAt lam state x) *
            (1 - state.slope lam / 2) := by
    intro label hlabel
    have hmem : label ∈ feedbackUnseenFinset S := (Finset.mem_filter.mp hlabel).1
    have hprod := Finset.mul_prod_erase (feedbackUnseenFinset S)
      (fun z : FeedbackLabel n ↦ feedbackLabelRemainingRealMassAt lam state x z) hmem
    have hprod' :
        feedbackLabelRemainingRealMassAt lam state x label *
            feedbackOtherSurvivalMassAt lam state x S label =
          feedbackUnseenSurvivalMassAt lam state x S := by
      simpa [feedbackOtherSurvivalMassAt, feedbackUnseenSurvivalMassAt] using hprod
    cases label with
    | inl i =>
        rw [← hprod']
        simp only [feedbackLabelRemainingRealMassAt,
          feedbackSourceLabelNextDensityAt, feedbackSourceRemainingRealMassAt]
        field_simp [hn0, harea]
    | inr j =>
        have : ¬ (∃ i : Fin n, (Sum.inr j : FeedbackLabel n) = Sum.inl i) := by simp
        exact False.elim (this (Finset.mem_filter.mp hlabel).2)
  calc
    (∑ label ∈ feedbackUnseenSourceLabels S,
        feedbackSourceLabelNextDensityAt lam state x S label) =
        ∑ label ∈ feedbackUnseenSourceLabels S,
          feedbackUnseenSurvivalMassAt lam state x S *
            (1 / feedbackSourceRemainingAreaAt lam state x) *
              (1 - state.slope lam / 2) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = feedbackUnseenSurvivalMassAt lam state x S *
        ((feedbackUnseenSourceCount S : ℝ) /
          feedbackSourceRemainingAreaAt lam state x) *
          (1 - state.slope lam / 2) := by
      simp [feedbackUnseenSourceCount]
      ring
    _ = feedbackSourceSurvivalLossFluxAt lam state x S := by
      rw [feedbackSourceSurvivalLossFluxAt,
        feedbackSourceSurvivalFluxAt_eq hn lam state x S hsource]
      ring

/-- Summing the target cause-specific densities recovers the target survival-loss flux. -/
theorem sum_feedbackTargetLabelNextDensityAt_eq
    (hn : 0 < n) (lam : ℝ) (state : FeedbackStepState n) (x : ℝ)
    (S : Finset (FeedbackLabel n))
    (htarget : 0 < feedbackTargetRemainingRealMassAt lam state x) :
    ∑ label ∈ feedbackUnseenTargetLabels S,
        feedbackTargetLabelNextDensityAt lam state x S label =
      feedbackTargetSurvivalLossFluxAt lam state x S := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have harea : feedbackTargetRemainingAreaAt lam state x ≠ 0 := by
    intro hzero
    have : feedbackTargetRemainingRealMassAt lam state x = 0 := by
      simp [feedbackTargetRemainingRealMassAt, hzero]
    linarith
  have hterm : ∀ label ∈ feedbackUnseenTargetLabels S,
      feedbackTargetLabelNextDensityAt lam state x S label =
        feedbackUnseenSurvivalMassAt lam state x S *
          (1 / feedbackTargetRemainingAreaAt lam state x) *
            (1 + 3 * state.slope lam / 2) := by
    intro label hlabel
    have hmem : label ∈ feedbackUnseenFinset S := (Finset.mem_filter.mp hlabel).1
    have hprod := Finset.mul_prod_erase (feedbackUnseenFinset S)
      (fun z : FeedbackLabel n ↦ feedbackLabelRemainingRealMassAt lam state x z) hmem
    have hprod' :
        feedbackLabelRemainingRealMassAt lam state x label *
            feedbackOtherSurvivalMassAt lam state x S label =
          feedbackUnseenSurvivalMassAt lam state x S := by
      simpa [feedbackOtherSurvivalMassAt, feedbackUnseenSurvivalMassAt] using hprod
    cases label with
    | inl i =>
        have : ¬ (∃ j : Fin n, (Sum.inl i : FeedbackLabel n) = Sum.inr j) := by simp
        exact False.elim (this (Finset.mem_filter.mp hlabel).2)
    | inr j =>
        rw [← hprod']
        simp only [feedbackLabelRemainingRealMassAt,
          feedbackTargetLabelNextDensityAt, feedbackTargetRemainingRealMassAt]
        field_simp [hn0, harea]
  calc
    (∑ label ∈ feedbackUnseenTargetLabels S,
        feedbackTargetLabelNextDensityAt lam state x S label) =
        ∑ label ∈ feedbackUnseenTargetLabels S,
          feedbackUnseenSurvivalMassAt lam state x S *
            (1 / feedbackTargetRemainingAreaAt lam state x) *
              (1 + 3 * state.slope lam / 2) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = feedbackUnseenSurvivalMassAt lam state x S *
        ((feedbackUnseenTargetCount S : ℝ) /
          feedbackTargetRemainingAreaAt lam state x) *
          (1 + 3 * state.slope lam / 2) := by
      simp [feedbackUnseenTargetCount]
      ring
    _ = feedbackTargetSurvivalLossFluxAt lam state x S := by
      rw [feedbackTargetSurvivalLossFluxAt,
        feedbackTargetSurvivalFluxAt_eq hn lam state x S htarget]
      ring

/-- A selected unseen source label crosses in `(s,t]`, weighted by survival of every other
unseen label up to its crossing coordinate. -/
theorem unitSquareUniform_sourceNextCrossing_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (i : Fin n)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t, ∀ u : UnitMark,
      0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
      sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) :
    (∫ z : MarkedHeight,
      (sourceRawRemainingSetAt n lam state s \
        sourceRawRemainingSetAt n lam state t).indicator
        (fun z ↦ feedbackOtherSurvivalMassAt lam state
          (sourceFixedStateCrossing n lam state z) S (Sum.inl i)) z
        ∂(unitSquareUniform : Measure MarkedHeight)) =
      ∫ y in s..t,
        feedbackOtherSurvivalMassAt lam state y S (Sum.inl i) *
          (1 - state.slope lam / 2) / (n : ℝ) := by
  exact unitSquareUniform_sourceFixedStateCrossing_slab_integral state lam s t hn hst
    hlam0 hlamHalf hbulk
    (fun y ↦ feedbackOtherSurvivalMassAt lam state y S (Sum.inl i))
    (continuous_feedbackOtherSurvivalMassAt hn lam state S (Sum.inl i))

/-- A selected unseen target label crosses in `(s,t]`, weighted by survival of every other
unseen label up to its crossing coordinate. -/
theorem unitSquareUniform_targetNextCrossing_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (j : Fin n)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t, ∀ v : UnitMark,
      0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
      targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n) :
    (∫ z : MarkedHeight,
      (targetRawRemainingSetAt n lam state s \
        targetRawRemainingSetAt n lam state t).indicator
        (fun z ↦ feedbackOtherSurvivalMassAt lam state
          (targetFixedStateCrossing n lam state z) S (Sum.inr j)) z
        ∂(unitSquareUniform : Measure MarkedHeight)) =
      ∫ y in s..t,
        feedbackOtherSurvivalMassAt lam state y S (Sum.inr j) *
          (1 + 3 * state.slope lam / 2) / (n : ℝ) := by
  exact unitSquareUniform_targetFixedStateCrossing_slab_integral state lam s t hn hst
    hlam0 hlamHalf hbulk
    (fun y ↦ feedbackOtherSurvivalMassAt lam state y S (Sum.inr j))
    (continuous_feedbackOtherSurvivalMassAt hn lam state S (Sum.inr j))

/-- Source next-crossing identity indexed by the actual source-label finset. -/
theorem unitSquareUniform_sourceLabelNextCrossing_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlabel : label ∈ feedbackUnseenSourceLabels S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t, ∀ u : UnitMark,
      0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
      sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) :
    (∫ z : MarkedHeight,
      (sourceRawRemainingSetAt n lam state s \
        sourceRawRemainingSetAt n lam state t).indicator
        (fun z ↦ feedbackOtherSurvivalMassAt lam state
          (sourceFixedStateCrossing n lam state z) S label) z
        ∂(unitSquareUniform : Measure MarkedHeight)) =
      ∫ y in s..t, feedbackSourceLabelNextDensityAt lam state y S label := by
  cases label with
  | inl i =>
      simpa [feedbackSourceLabelNextDensityAt] using
        unitSquareUniform_sourceNextCrossing_integral state lam s t S i hn hst
          hlam0 hlamHalf hbulk
  | inr j =>
      have : ¬ (∃ i : Fin n, (Sum.inr j : FeedbackLabel n) = Sum.inl i) := by simp
      exact False.elim (this (Finset.mem_filter.mp hlabel).2)

/-- Target next-crossing identity indexed by the actual target-label finset. -/
theorem unitSquareUniform_targetLabelNextCrossing_integral
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlabel : label ∈ feedbackUnseenTargetLabels S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t, ∀ v : UnitMark,
      0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
      targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n) :
    (∫ z : MarkedHeight,
      (targetRawRemainingSetAt n lam state s \
        targetRawRemainingSetAt n lam state t).indicator
        (fun z ↦ feedbackOtherSurvivalMassAt lam state
          (targetFixedStateCrossing n lam state z) S label) z
        ∂(unitSquareUniform : Measure MarkedHeight)) =
      ∫ y in s..t, feedbackTargetLabelNextDensityAt lam state y S label := by
  cases label with
  | inl i =>
      have : ¬ (∃ j : Fin n, (Sum.inl i : FeedbackLabel n) = Sum.inr j) := by simp
      exact False.elim (this (Finset.mem_filter.mp hlabel).2)
  | inr j =>
      simpa [feedbackTargetLabelNextDensityAt] using
        unitSquareUniform_targetNextCrossing_integral state lam s t S j hn hst
          hlam0 hlamHalf hbulk

/-- Under the full unseen product law, a specified unseen source label is the next event in
`(s,t]` with mass equal to its cause-specific integrated density. -/
theorem feedbackUnseenTupleLaw_real_sourceNextEventSetOfLabel_eq
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlabel : label ∈ feedbackUnseenSourceLabels S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n) :
    (feedbackUnseenTupleLaw S).real
        (feedbackNextEventSetOfLabel lam state s t S label) =
      ∫ y in s..t, feedbackSourceLabelNextDensityAt lam state y S label := by
  classical
  have hunseen : label ∈ feedbackUnseenFinset S := (Finset.mem_filter.mp hlabel).1
  cases label with
  | inl i =>
      let selected : feedbackUnseenFinset S := ⟨Sum.inl i, hunseen⟩
      calc
        (feedbackUnseenTupleLaw S).real
            (feedbackNextEventSetOfLabel lam state s t S (Sum.inl i)) =
            (feedbackUnseenTupleLaw S).real
              (feedbackNextEventSet lam state s t S selected) := by
          simp [feedbackNextEventSetOfLabel, hunseen, selected]
        _ = ∫ z : MarkedHeight,
            (feedbackLabelRemainingSetAt lam state s selected \
              feedbackLabelRemainingSetAt lam state t selected).indicator
              (fun z ↦ feedbackOtherSurvivalMassAt lam state
                (feedbackLabelFixedStateCrossing n lam state selected z) S selected) z
              ∂(unitSquareUniform : Measure MarkedHeight) :=
          feedbackUnseenTupleLaw_real_feedbackNextEventSet_eq_integral
            state lam s t S selected hn hst hlam0 hlamHalf hbulk
        _ = ∫ y in s..t,
            feedbackSourceLabelNextDensityAt lam state y S (Sum.inl i) := by
          simpa [selected, feedbackLabelRemainingSetAt,
            feedbackLabelFixedStateCrossing] using
            unitSquareUniform_sourceLabelNextCrossing_integral
              state lam s t S (Sum.inl i) hlabel hn hst hlam0 hlamHalf
              (fun y hy ↦ (hbulk y hy).1)
  | inr j =>
      have : ¬ (∃ i : Fin n, (Sum.inr j : FeedbackLabel n) = Sum.inl i) := by simp
      exact False.elim (this (Finset.mem_filter.mp hlabel).2)

/-- Under the full unseen product law, a specified unseen target label is the next event in
`(s,t]` with mass equal to its cause-specific integrated density. -/
theorem feedbackUnseenTupleLaw_real_targetNextEventSetOfLabel_eq
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlabel : label ∈ feedbackUnseenTargetLabels S)
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n) :
    (feedbackUnseenTupleLaw S).real
        (feedbackNextEventSetOfLabel lam state s t S label) =
      ∫ y in s..t, feedbackTargetLabelNextDensityAt lam state y S label := by
  classical
  have hunseen : label ∈ feedbackUnseenFinset S := (Finset.mem_filter.mp hlabel).1
  cases label with
  | inl i =>
      have : ¬ (∃ j : Fin n, (Sum.inl i : FeedbackLabel n) = Sum.inr j) := by simp
      exact False.elim (this (Finset.mem_filter.mp hlabel).2)
  | inr j =>
      let selected : feedbackUnseenFinset S := ⟨Sum.inr j, hunseen⟩
      calc
        (feedbackUnseenTupleLaw S).real
            (feedbackNextEventSetOfLabel lam state s t S (Sum.inr j)) =
            (feedbackUnseenTupleLaw S).real
              (feedbackNextEventSet lam state s t S selected) := by
          simp [feedbackNextEventSetOfLabel, hunseen, selected]
        _ = ∫ z : MarkedHeight,
            (feedbackLabelRemainingSetAt lam state s selected \
              feedbackLabelRemainingSetAt lam state t selected).indicator
              (fun z ↦ feedbackOtherSurvivalMassAt lam state
                (feedbackLabelFixedStateCrossing n lam state selected z) S selected) z
              ∂(unitSquareUniform : Measure MarkedHeight) :=
          feedbackUnseenTupleLaw_real_feedbackNextEventSet_eq_integral
            state lam s t S selected hn hst hlam0 hlamHalf hbulk
        _ = ∫ y in s..t,
            feedbackTargetLabelNextDensityAt lam state y S (Sum.inr j) := by
          simpa [selected, feedbackLabelRemainingSetAt,
            feedbackLabelFixedStateCrossing] using
            unitSquareUniform_targetLabelNextCrossing_integral
              state lam s t S (Sum.inr j) hlabel hn hst hlam0 hlamHalf
              (fun y hy ↦ (hbulk y hy).2)

/-- The sum of all source-label next-event integrals is the cumulative source survival loss. -/
theorem sum_intervalIntegral_feedbackSourceLabelNextDensityAt_eq
    (hn : 0 < n) (lam : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (s t : ℝ) (hst : s ≤ t)
    (hsource : ∀ y ∈ Icc s t,
      0 < feedbackSourceRemainingRealMassAt lam state y) :
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (∫ y in s..t, feedbackSourceLabelNextDensityAt lam state y S label) =
      ∫ y in s..t, feedbackSourceSurvivalLossFluxAt lam state y S := by
  have hint : ∀ label ∈ feedbackUnseenSourceLabels S,
      IntervalIntegrable
        (fun y ↦ feedbackSourceLabelNextDensityAt lam state y S label) volume s t := by
    intro label _hlabel
    exact (continuous_feedbackSourceLabelNextDensityAt hn lam state S label).continuousOn
      |>.intervalIntegrable
  rw [← intervalIntegral.integral_finsetSum hint]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Icc s t := by simpa [uIcc_of_le hst] using hy
  exact sum_feedbackSourceLabelNextDensityAt_eq hn lam state y S (hsource y hy')

/-- The sum of all target-label next-event integrals is the cumulative target survival loss. -/
theorem sum_intervalIntegral_feedbackTargetLabelNextDensityAt_eq
    (hn : 0 < n) (lam : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n)) (s t : ℝ) (hst : s ≤ t)
    (htarget : ∀ y ∈ Icc s t,
      0 < feedbackTargetRemainingRealMassAt lam state y) :
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (∫ y in s..t, feedbackTargetLabelNextDensityAt lam state y S label) =
      ∫ y in s..t, feedbackTargetSurvivalLossFluxAt lam state y S := by
  have hint : ∀ label ∈ feedbackUnseenTargetLabels S,
      IntervalIntegrable
        (fun y ↦ feedbackTargetLabelNextDensityAt lam state y S label) volume s t := by
    intro label _hlabel
    exact (continuous_feedbackTargetLabelNextDensityAt hn lam state S label).continuousOn
      |>.intervalIntegrable
  rw [← intervalIntegral.integral_finsetSum hint]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy' : y ∈ Icc s t := by simpa [uIcc_of_le hst] using hy
  exact sum_feedbackTargetLabelNextDensityAt_eq hn lam state y S (htarget y hy')

/-- The expected number of source-labelled next events in `(s,t]` under the unseen product law is
the integrated source survival-loss flux. -/
theorem sum_feedbackUnseenTupleLaw_real_sourceNextEventSetOfLabel_eq_flux
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n))
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (hsource : ∀ y ∈ Icc s t,
      0 < feedbackSourceRemainingRealMassAt lam state y) :
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (feedbackUnseenTupleLaw S).real
          (feedbackNextEventSetOfLabel lam state s t S label) =
      ∫ y in s..t, feedbackSourceSurvivalLossFluxAt lam state y S := by
  calc
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (feedbackUnseenTupleLaw S).real
          (feedbackNextEventSetOfLabel lam state s t S label) =
        ∑ label ∈ feedbackUnseenSourceLabels S,
          (∫ y in s..t, feedbackSourceLabelNextDensityAt lam state y S label) := by
      apply Finset.sum_congr rfl
      intro label hlabel
      exact feedbackUnseenTupleLaw_real_sourceNextEventSetOfLabel_eq
        state lam s t S label hlabel hn hst hlam0 hlamHalf hbulk
    _ = ∫ y in s..t, feedbackSourceSurvivalLossFluxAt lam state y S :=
      sum_intervalIntegral_feedbackSourceLabelNextDensityAt_eq
        hn lam state S s t hst hsource

/-- The expected number of target-labelled next events in `(s,t]` under the unseen product law is
the integrated target survival-loss flux. -/
theorem sum_feedbackUnseenTupleLaw_real_targetNextEventSetOfLabel_eq_flux
    (state : FeedbackStepState n) (lam s t : ℝ)
    (S : Finset (FeedbackLabel n))
    (hn : 0 < n) (hst : s ≤ t) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)
    (htarget : ∀ y ∈ Icc s t,
      0 < feedbackTargetRemainingRealMassAt lam state y) :
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (feedbackUnseenTupleLaw S).real
          (feedbackNextEventSetOfLabel lam state s t S label) =
      ∫ y in s..t, feedbackTargetSurvivalLossFluxAt lam state y S := by
  calc
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (feedbackUnseenTupleLaw S).real
          (feedbackNextEventSetOfLabel lam state s t S label) =
        ∑ label ∈ feedbackUnseenTargetLabels S,
          (∫ y in s..t, feedbackTargetLabelNextDensityAt lam state y S label) := by
      apply Finset.sum_congr rfl
      intro label hlabel
      exact feedbackUnseenTupleLaw_real_targetNextEventSetOfLabel_eq
        state lam s t S label hlabel hn hst hlam0 hlamHalf hbulk
    _ = ∫ y in s..t, feedbackTargetSurvivalLossFluxAt lam state y S :=
      sum_intervalIntegral_feedbackTargetLabelNextDensityAt_eq
        hn lam state S s t hst htarget

end OTSelector
