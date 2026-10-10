import OTSelector.Feedback.FiniteHistoryBulkNextEvent
import OTSelector.Feedback.StateMeasurable

/-!
# Joint measurability of finite-history bulk next-event sections

The fixed-state next-event measurability lemmas do not by themselves cover a varying state.  This
module records the corresponding product-space statement for a state and an unseen tuple.
-/

open MeasureTheory Set
open scoped Classical

namespace OTSelector

variable {n : ℕ}

private theorem measurable_feedbackLabelFixedStateCrossing_joint
    (lam : ℝ) (label : FeedbackLabel n)
    (_hlam0 : 0 ≤ lam) (_hlamHalf : lam < 1 / 2) :
    Measurable (fun p : FeedbackStepState n × MarkedHeight ↦
      feedbackLabelFixedStateCrossing n lam p.1 label p.2) := by
  cases label with
  | inl i =>
      have hx : Measurable fun p : FeedbackStepState n × MarkedHeight ↦ p.1.x :=
        FeedbackStepState.measurable_x.comp measurable_fst
      have hp : Measurable fun p : FeedbackStepState n × MarkedHeight ↦ p.1.p :=
        FeedbackStepState.measurable_p.comp measurable_fst
      have hq : Measurable fun p : FeedbackStepState n × MarkedHeight ↦ p.1.slope lam :=
        (FeedbackStepState.measurable_slope lam).comp measurable_fst
      have ht : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          (n : ℝ) * (p.2.1 : ℝ) :=
        measurable_const.mul (measurable_subtype_coe.comp
          (measurable_fst.comp measurable_snd))
      have ha : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          1 - (p.2.2 : ℝ) :=
        measurable_const.sub (measurable_subtype_coe.comp
          (measurable_snd.comp measurable_snd))
      have hnum : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          (n : ℝ) * (p.2.1 : ℝ) + (1 - (p.2.2 : ℝ)) *
            (p.1.p - p.1.slope lam * p.1.x) := by
        exact ht.add (ha.mul (hp.sub (hq.mul hx)))
      have hden : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          1 - (1 - (p.2.2 : ℝ)) * p.1.slope lam := by
        exact measurable_const.sub (ha.mul hq)
      have hquot : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          ((n : ℝ) * (p.2.1 : ℝ) + (1 - (p.2.2 : ℝ)) *
            (p.1.p - p.1.slope lam * p.1.x)) /
            (1 - (1 - (p.2.2 : ℝ)) * p.1.slope lam) :=
        hnum.div hden
      simpa [feedbackLabelFixedStateCrossing, sourceFixedStateCrossing,
        sourceSegmentCrossing, FeedbackStepState.slope] using hquot
  | inr j =>
      have hx : Measurable fun p : FeedbackStepState n × MarkedHeight ↦ p.1.x :=
        FeedbackStepState.measurable_x.comp measurable_fst
      have hp : Measurable fun p : FeedbackStepState n × MarkedHeight ↦ p.1.p :=
        FeedbackStepState.measurable_p.comp measurable_fst
      have hq : Measurable fun p : FeedbackStepState n × MarkedHeight ↦ p.1.slope lam :=
        (FeedbackStepState.measurable_slope lam).comp measurable_fst
      have hs : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          (n : ℝ) * (p.2.1 : ℝ) :=
        measurable_const.mul (measurable_subtype_coe.comp
          (measurable_fst.comp measurable_snd))
      have hb : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          1 + (p.2.2 : ℝ) :=
        measurable_const.add (measurable_subtype_coe.comp
          (measurable_snd.comp measurable_snd))
      have hnum : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          (n : ℝ) * (p.2.1 : ℝ) - (1 + (p.2.2 : ℝ)) *
            (p.1.p - p.1.slope lam * p.1.x) := by
        exact hs.sub (hb.mul (hp.sub (hq.mul hx)))
      have hden : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          1 + (1 + (p.2.2 : ℝ)) * p.1.slope lam := by
        exact measurable_const.add (hb.mul hq)
      have hquot : Measurable fun p : FeedbackStepState n × MarkedHeight ↦
          ((n : ℝ) * (p.2.1 : ℝ) - (1 + (p.2.2 : ℝ)) *
            (p.1.p - p.1.slope lam * p.1.x)) /
            (1 + (1 + (p.2.2 : ℝ)) * p.1.slope lam) :=
        hnum.div hden
      convert hquot using 1
      · funext p
        simp only [feedbackLabelFixedStateCrossing, targetFixedStateCrossing,
          targetSegmentCrossing, FeedbackStepState.slope]
        ring

private theorem measurable_feedbackLabelFixedStateCrossing_parts
    (lam : ℝ) (S : Finset (FeedbackLabel n))
    (label : feedbackUnseenFinset S)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    Measurable (fun parts : FeedbackStepState n ×
        (feedbackUnseenFinset S → MarkedHeight) ↦
      feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
        (parts.2 label)) := by
  exact (measurable_feedbackLabelFixedStateCrossing_joint lam
    (label : FeedbackLabel n) hlam0 hlamHalf).comp
    (measurable_fst.prodMk ((measurable_pi_apply label).comp measurable_snd))

private theorem measurableSet_feedbackUnseenRectangularSetAt_joint
    (lam : ℝ) (S : Finset (FeedbackLabel n))
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet {parts : FeedbackStepState n ×
        (feedbackUnseenFinset S → MarkedHeight) |
      parts.2 ∈ feedbackUnseenRectangularSetAt lam parts.1 parts.1.x S} := by
  have hstatex : Measurable fun parts : FeedbackStepState n ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ parts.1.x :=
    FeedbackStepState.measurable_x.comp measurable_fst
  have hother (other : feedbackUnseenFinset S) :
      MeasurableSet {parts : FeedbackStepState n ×
          (feedbackUnseenFinset S → MarkedHeight) |
        parts.1.x < feedbackLabelFixedStateCrossing n lam parts.1
          (other : FeedbackLabel n) (parts.2 other)} := by
    exact measurableSet_lt hstatex
      (measurable_feedbackLabelFixedStateCrossing_parts lam S other hlam0 hlamHalf)
  have hall : MeasurableSet (⋂ other : feedbackUnseenFinset S,
      {parts : FeedbackStepState n × (feedbackUnseenFinset S → MarkedHeight) |
        parts.1.x < feedbackLabelFixedStateCrossing n lam parts.1
          (other : FeedbackLabel n) (parts.2 other)}) :=
    MeasurableSet.iInter hother
  have heq : {parts : FeedbackStepState n ×
      (feedbackUnseenFinset S → MarkedHeight) |
      parts.2 ∈ feedbackUnseenRectangularSetAt lam parts.1 parts.1.x S} =
      ⋂ other : feedbackUnseenFinset S,
        {parts : FeedbackStepState n × (feedbackUnseenFinset S → MarkedHeight) |
          parts.1.x < feedbackLabelFixedStateCrossing n lam parts.1
            (other : FeedbackLabel n) (parts.2 other)} := by
    ext parts
    constructor
    · intro hrect
      rw [Set.mem_iInter]
      intro other
      have hmem := (mem_feedbackUnseenRectangularSetAt_iff lam parts.1 parts.1.x S
        parts.2).1 hrect other
      exact (mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
        parts.1 lam (other : FeedbackLabel n) (parts.2 other) parts.1.x
        hlam0 hlamHalf).1 hmem
    · intro hright
      rw [Set.mem_iInter] at hright
      apply (mem_feedbackUnseenRectangularSetAt_iff lam parts.1 parts.1.x S parts.2).2
      intro other
      exact (mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
        parts.1 lam (other : FeedbackLabel n) (parts.2 other) parts.1.x
        hlam0 hlamHalf).2 (hright other)
  rw [heq]
  exact hall

private theorem measurableSet_feedbackNextEventSet_joint
    (lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (label : feedbackUnseenFinset S)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet {parts : FeedbackStepState n ×
        (feedbackUnseenFinset S → MarkedHeight) |
      parts.2 ∈ feedbackNextEventSet lam parts.1 s t S label} := by
  have hcross (other : feedbackUnseenFinset S) :
      Measurable (fun parts : FeedbackStepState n ×
          (feedbackUnseenFinset S → MarkedHeight) ↦
        feedbackLabelFixedStateCrossing n lam parts.1
          (other : FeedbackLabel n) (parts.2 other)) :=
    measurable_feedbackLabelFixedStateCrossing_parts lam S other hlam0 hlamHalf
  have hslab : MeasurableSet {parts : FeedbackStepState n ×
      (feedbackUnseenFinset S → MarkedHeight) |
    feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
        (parts.2 label) ∈ Ioc s t} :=
    hcross label measurableSet_Ioc
  have hother (other : feedbackUnseenFinset S) :
      MeasurableSet {parts : FeedbackStepState n ×
          (feedbackUnseenFinset S → MarkedHeight) |
        other ≠ label →
          feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
              (parts.2 label) <
            feedbackLabelFixedStateCrossing n lam parts.1 (other : FeedbackLabel n)
              (parts.2 other)} := by
    by_cases hEq : other = label
    · simp [hEq]
    · simpa [hEq] using measurableSet_lt (hcross label) (hcross other)
  have hall : MeasurableSet {parts : FeedbackStepState n ×
      (feedbackUnseenFinset S → MarkedHeight) |
    ∀ other : feedbackUnseenFinset S, other ≠ label →
      feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
          (parts.2 label) <
        feedbackLabelFixedStateCrossing n lam parts.1 (other : FeedbackLabel n)
          (parts.2 other)} := by
    rw [show {parts : FeedbackStepState n ×
        (feedbackUnseenFinset S → MarkedHeight) |
      ∀ other : feedbackUnseenFinset S, other ≠ label →
        feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
            (parts.2 label) <
          feedbackLabelFixedStateCrossing n lam parts.1 (other : FeedbackLabel n)
            (parts.2 other)} =
      ⋂ other : feedbackUnseenFinset S,
        {parts : FeedbackStepState n × (feedbackUnseenFinset S → MarkedHeight) |
          other ≠ label →
            feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
                (parts.2 label) <
              feedbackLabelFixedStateCrossing n lam parts.1 (other : FeedbackLabel n)
                (parts.2 other)} by
          ext parts
          simp]
    exact MeasurableSet.iInter hother
  change MeasurableSet
    ({parts : FeedbackStepState n × (feedbackUnseenFinset S → MarkedHeight) |
      feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
          (parts.2 label) ∈ Ioc s t} ∩
      {parts : FeedbackStepState n × (feedbackUnseenFinset S → MarkedHeight) |
        ∀ other : feedbackUnseenFinset S, other ≠ label →
          feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
              (parts.2 label) <
            feedbackLabelFixedStateCrossing n lam parts.1 (other : FeedbackLabel n)
              (parts.2 other)})
  exact hslab.inter hall

private theorem measurableSet_feedbackBulkRegion_joint
    (B lam : ℝ) (S : Finset (FeedbackLabel n))
    (label : feedbackUnseenFinset S)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet {parts : FeedbackStepState n ×
        (feedbackUnseenFinset S → MarkedHeight) |
      feedbackBulkRegion n B
        (feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
          (parts.2 label))
        (segmentCurve parts.1.x parts.1.p (parts.1.slope lam)
          (feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
            (parts.2 label)))} := by
  have hcross := measurable_feedbackLabelFixedStateCrossing_parts lam S label hlam0 hlamHalf
  have hx : Measurable fun parts : FeedbackStepState n ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ parts.1.x :=
    FeedbackStepState.measurable_x.comp measurable_fst
  have hp : Measurable fun parts : FeedbackStepState n ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ parts.1.p :=
    FeedbackStepState.measurable_p.comp measurable_fst
  have hq : Measurable fun parts : FeedbackStepState n ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ parts.1.slope lam :=
    (FeedbackStepState.measurable_slope lam).comp measurable_fst
  have hcurve : Measurable fun parts : FeedbackStepState n ×
      (feedbackUnseenFinset S → MarkedHeight) ↦
      segmentCurve parts.1.x parts.1.p (parts.1.slope lam)
        (feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
          (parts.2 label)) := by
    simp only [segmentCurve]
    exact hp.add (hq.mul (hcross.sub hx))
  exact (feedbackBulkRegion_measurableSet n B).preimage (hcross.prodMk hcurve)

private theorem measurableSet_feedbackBulkNextEventSet_joint
    (B lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (label : feedbackUnseenFinset S)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet {parts : FeedbackStepState n ×
        (feedbackUnseenFinset S → MarkedHeight) |
      parts.2 ∈ feedbackBulkNextEventSet B lam parts.1 s t S label} := by
  change MeasurableSet
    ({parts : FeedbackStepState n × (feedbackUnseenFinset S → MarkedHeight) |
      parts.2 ∈ feedbackUnseenRectangularSetAt lam parts.1 parts.1.x S} ∩
      {parts : FeedbackStepState n × (feedbackUnseenFinset S → MarkedHeight) |
        parts.2 ∈ feedbackNextEventSet lam parts.1 s t S label} ∩
      {parts : FeedbackStepState n × (feedbackUnseenFinset S → MarkedHeight) |
        feedbackBulkRegion n B
          (feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
            (parts.2 label))
          (segmentCurve parts.1.x parts.1.p (parts.1.slope lam)
            (feedbackLabelFixedStateCrossing n lam parts.1 (label : FeedbackLabel n)
              (parts.2 label)))})
  exact (measurableSet_feedbackUnseenRectangularSetAt_joint lam S hlam0 hlamHalf).inter
    (measurableSet_feedbackNextEventSet_joint lam s t S label hlam0 hlamHalf) |>.inter
      (measurableSet_feedbackBulkRegion_joint B lam S label hlam0 hlamHalf)

theorem measurableSet_feedbackBulkNextEventSetOfLabel_joint
    (B lam s t : ℝ) (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet {parts : FeedbackStepState n ×
        (feedbackUnseenFinset S → MarkedHeight) |
      parts.2 ∈ feedbackBulkNextEventSetOfLabel B lam parts.1 s t S label} := by
  classical
  by_cases hlabel : label ∈ feedbackUnseenFinset S
  · simpa [feedbackBulkNextEventSetOfLabel, hlabel] using
      measurableSet_feedbackBulkNextEventSet_joint B lam s t S ⟨label, hlabel⟩
        hlam0 hlamHalf
  · simp [feedbackBulkNextEventSetOfLabel, hlabel]

end OTSelector
