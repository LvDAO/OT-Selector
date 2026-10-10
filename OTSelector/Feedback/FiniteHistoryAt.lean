import OTSelector.Feedback.FiniteHistorySection

/-!
# Finite feedback histories observed at a deterministic coordinate

The terminal state of a prescribed history is the state at its last crossing.  A snapshot at a
later deterministic coordinate also records that no unseen label has crossed the affine
continuation in the meantime.  This file adds precisely that missing strict remaining-region
condition.

The statements are deterministic.  In particular, they neither construct a conditional law nor
identify a compensator.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## Remaining regions along the active affine segment -/

/-- The source region still unseen at coordinate `x` on the affine continuation of `state`. -/
def sourceRawRemainingSetAt (n : ℕ) (lam : ℝ) (state : FeedbackStepState n)
    (x : ℝ) : Set MarkedHeight :=
  sourceRawRemainingSet n (segmentCurve state.x state.p (state.slope lam) x) x

/-- The target region still unseen at coordinate `x` on the affine continuation of `state`. -/
def targetRawRemainingSetAt (n : ℕ) (lam : ℝ) (state : FeedbackStepState n)
    (x : ℝ) : Set MarkedHeight :=
  targetRawRemainingSet n (segmentCurve state.x state.p (state.slope lam) x) x

/-- Every label not recorded in `state` remains strictly beyond coordinate `x`. -/
def LiesInStateRemainingAt (lam : ℝ) (state : FeedbackStepState n) (x : ℝ)
    (sample : FiniteSample n) : Prop :=
  (∀ i, i ∉ state.seenSource →
      sample.sourcePoint i ∈ sourceRawRemainingSetAt n lam state x) ∧
    ∀ j, j ∉ state.seenTarget →
      sample.targetPoint j ∈ targetRawRemainingSetAt n lam state x

/-- The one-label strict remaining region at a coordinate on the active segment. -/
def feedbackLabelRemainingSetAt (lam : ℝ) (state : FeedbackStepState n) (x : ℝ) :
    FeedbackLabel n → Set MarkedHeight
  | Sum.inl _ => sourceRawRemainingSetAt n lam state x
  | Sum.inr _ => targetRawRemainingSetAt n lam state x

theorem isOpen_sourceRawRemainingSetAt
    (lam : ℝ) (state : FeedbackStepState n) (x : ℝ) :
    IsOpen (sourceRawRemainingSetAt n lam state x) :=
  isOpen_sourceRawRemainingSet n _ _

theorem isOpen_targetRawRemainingSetAt
    (lam : ℝ) (state : FeedbackStepState n) (x : ℝ) :
    IsOpen (targetRawRemainingSetAt n lam state x) :=
  isOpen_targetRawRemainingSet n _ _

theorem measurableSet_feedbackLabelRemainingSetAt
    (lam : ℝ) (state : FeedbackStepState n) (x : ℝ) (label : FeedbackLabel n) :
    MeasurableSet (feedbackLabelRemainingSetAt lam state x label) := by
  cases label with
  | inl i => exact (isOpen_sourceRawRemainingSetAt lam state x).measurableSet
  | inr j => exact (isOpen_targetRawRemainingSetAt lam state x).measurableSet

/-- The later strict remaining condition is measurable jointly in the sample and the state. -/
theorem measurableSet_liesInStateRemainingAt_pair (lam x : ℝ) :
    MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
      LiesInStateRemainingAt lam pair.2 x pair.1} := by
  classical
  have hsource (i : Fin n) :
      MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
        i ∉ pair.2.seenSource →
          pair.1.sourcePoint i ∈ sourceRawRemainingSetAt n lam pair.2 x} := by
    have hseen := FiniteSample.measurableSet_mem_seenSource (n := n) i
    have hheight : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
        (n : ℝ) * (pair.1.sourceHeight i : ℝ) :=
      measurable_const.mul <|
        (measurable_subtype_coe.comp (FiniteSample.measurable_sourceHeight i)).comp
          measurable_fst
    have hslope : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
        pair.1.sourceSlope i :=
      (FiniteSample.measurable_sourceSlope i).comp measurable_fst
    have hstatex : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.x :=
      FeedbackStepState.measurable_x.comp measurable_snd
    have hstatep : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.p :=
      FeedbackStepState.measurable_p.comp measurable_snd
    have hstateslope : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
        pair.2.slope lam :=
      (FeedbackStepState.measurable_slope lam).comp measurable_snd
    have hcurve : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
        segmentCurve pair.2.x pair.2.p (pair.2.slope lam) x := by
      simp only [segmentCurve]
      exact hstatep.add (hstateslope.mul (measurable_const.sub hstatex))
    have hfuture : MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
        x < (n : ℝ) * (pair.1.sourceHeight i : ℝ) +
          pair.1.sourceSlope i * segmentCurve pair.2.x pair.2.p (pair.2.slope lam) x} :=
      measurableSet_lt measurable_const (hheight.add (hslope.mul hcurve))
    have hset :
        {pair : FiniteSample n × FeedbackStepState n |
            i ∉ pair.2.seenSource →
              pair.1.sourcePoint i ∈ sourceRawRemainingSetAt n lam pair.2 x} =
          {pair : FiniteSample n × FeedbackStepState n | i ∈ pair.2.seenSource} ∪
            {pair : FiniteSample n × FeedbackStepState n |
              x < (n : ℝ) * (pair.1.sourceHeight i : ℝ) +
                pair.1.sourceSlope i *
                  segmentCurve pair.2.x pair.2.p (pair.2.slope lam) x} := by
      ext pair
      simp only [mem_union, mem_ofPred_eq]
      by_cases hi : i ∈ pair.2.seenSource
      · simp [hi]
      · simp [hi, sourceRawRemainingSetAt, sourceRawRemainingSet,
          FiniteSample.sourcePoint, FiniteSample.sourceSlope, mul_comm]
    rw [hset]
    exact hseen.union hfuture
  have htarget (j : Fin n) :
      MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
        j ∉ pair.2.seenTarget →
          pair.1.targetPoint j ∈ targetRawRemainingSetAt n lam pair.2 x} := by
    have hseen := FiniteSample.measurableSet_mem_seenTarget (n := n) j
    have hheight : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
        (n : ℝ) * (pair.1.targetHeight j : ℝ) :=
      measurable_const.mul <|
        (measurable_subtype_coe.comp (FiniteSample.measurable_targetHeight j)).comp
          measurable_fst
    have hslope : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
        pair.1.targetSlope j :=
      (FiniteSample.measurable_targetSlope j).comp measurable_fst
    have hstatex : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.x :=
      FeedbackStepState.measurable_x.comp measurable_snd
    have hstatep : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.p :=
      FeedbackStepState.measurable_p.comp measurable_snd
    have hstateslope : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
        pair.2.slope lam :=
      (FeedbackStepState.measurable_slope lam).comp measurable_snd
    have hcurve : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
        segmentCurve pair.2.x pair.2.p (pair.2.slope lam) x := by
      simp only [segmentCurve]
      exact hstatep.add (hstateslope.mul (measurable_const.sub hstatex))
    have hfuture : MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
        x < (n : ℝ) * (pair.1.targetHeight j : ℝ) -
          pair.1.targetSlope j * segmentCurve pair.2.x pair.2.p (pair.2.slope lam) x} :=
      measurableSet_lt measurable_const (hheight.sub (hslope.mul hcurve))
    have hset :
        {pair : FiniteSample n × FeedbackStepState n |
            j ∉ pair.2.seenTarget →
              pair.1.targetPoint j ∈ targetRawRemainingSetAt n lam pair.2 x} =
          {pair : FiniteSample n × FeedbackStepState n | j ∈ pair.2.seenTarget} ∪
            {pair : FiniteSample n × FeedbackStepState n |
              x < (n : ℝ) * (pair.1.targetHeight j : ℝ) -
                pair.1.targetSlope j *
                  segmentCurve pair.2.x pair.2.p (pair.2.slope lam) x} := by
      ext pair
      simp only [mem_union, mem_ofPred_eq]
      by_cases hj : j ∈ pair.2.seenTarget
      · simp [hj]
      · simp [hj, targetRawRemainingSetAt, targetRawRemainingSet,
          FiniteSample.targetPoint, FiniteSample.targetSlope, mul_comm]
    rw [hset]
    exact hseen.union hfuture
  have hsource_all : MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
      ∀ i, i ∉ pair.2.seenSource →
        pair.1.sourcePoint i ∈ sourceRawRemainingSetAt n lam pair.2 x} := by
    have hset :
        {pair : FiniteSample n × FeedbackStepState n |
            ∀ i, i ∉ pair.2.seenSource →
              pair.1.sourcePoint i ∈ sourceRawRemainingSetAt n lam pair.2 x} =
          ⋂ i : Fin n, {pair : FiniteSample n × FeedbackStepState n |
            i ∉ pair.2.seenSource →
              pair.1.sourcePoint i ∈ sourceRawRemainingSetAt n lam pair.2 x} := by
      ext pair
      simp
    rw [hset]
    exact MeasurableSet.iInter hsource
  have htarget_all : MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
      ∀ j, j ∉ pair.2.seenTarget →
        pair.1.targetPoint j ∈ targetRawRemainingSetAt n lam pair.2 x} := by
    have hset :
        {pair : FiniteSample n × FeedbackStepState n |
            ∀ j, j ∉ pair.2.seenTarget →
              pair.1.targetPoint j ∈ targetRawRemainingSetAt n lam pair.2 x} =
          ⋂ j : Fin n, {pair : FiniteSample n × FeedbackStepState n |
            j ∉ pair.2.seenTarget →
              pair.1.targetPoint j ∈ targetRawRemainingSetAt n lam pair.2 x} := by
      ext pair
      simp
    rw [hset]
    exact MeasurableSet.iInter htarget
  change MeasurableSet ({pair : FiniteSample n × FeedbackStepState n |
      ∀ i, i ∉ pair.2.seenSource →
        pair.1.sourcePoint i ∈ sourceRawRemainingSetAt n lam pair.2 x} ∩
    {pair : FiniteSample n × FeedbackStepState n |
      ∀ j, j ∉ pair.2.seenTarget →
        pair.1.targetPoint j ∈ targetRawRemainingSetAt n lam pair.2 x})
  exact hsource_all.inter htarget_all

/-- Fixed-state later remaining regions give a measurable event in the sample. -/
theorem measurableSet_liesInStateRemainingAt
    (lam : ℝ) (state : FeedbackStepState n) (x : ℝ) :
    MeasurableSet {sample : FiniteSample n |
      LiesInStateRemainingAt lam state x sample} := by
  have hpair : Measurable fun sample : FiniteSample n ↦ (sample, state) :=
    measurable_id.prodMk measurable_const
  exact hpair (measurableSet_liesInStateRemainingAt_pair (n := n) lam x)

/-! ## Returning from a later coordinate to the terminal knot -/

private theorem sourceRawRemainingAt_imp_terminal
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) {x : ℝ} (hstatex : state.x ≤ x) (i : Fin n)
    (hi : sample.sourcePoint i ∈ sourceRawRemainingSetAt n lam state x) :
    sample.sourcePoint i ∈ sourceRawRemainingSet n state.p state.x := by
  have ha := sample.sourceSlope_mem i
  have hcross : x < state.sourceCoordinate sample lam i := by
    rw [FeedbackStepState.sourceCoordinate]
    apply (x_lt_sourceSegmentCrossing_iff ha.1 ha.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2
    simpa [sourceRawRemainingSetAt, sourceRawRemainingSet, FiniteSample.sourcePoint,
      FiniteSample.sourcePhase, FiniteSample.sourceSlope, FeedbackStepState.slope,
      mul_comm] using hi
  have hterminalCross : state.x < state.sourceCoordinate sample lam i :=
    lt_of_le_of_lt hstatex hcross
  have hterminalPhase := (x0_lt_sourceSegmentCrossing_iff ha.1 ha.2
    (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).1 (by
      simpa [FeedbackStepState.sourceCoordinate, FeedbackStepState.slope] using hterminalCross)
  simpa [sourceRawRemainingSet, FiniteSample.sourcePoint, FiniteSample.sourcePhase,
    FiniteSample.sourceSlope, mul_comm] using hterminalPhase

private theorem targetRawRemainingAt_imp_terminal
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) {x : ℝ} (hstatex : state.x ≤ x) (j : Fin n)
    (hj : sample.targetPoint j ∈ targetRawRemainingSetAt n lam state x) :
    sample.targetPoint j ∈ targetRawRemainingSet n state.p state.x := by
  have hb := sample.targetSlope_mem j
  have hcross : x < state.targetCoordinate sample lam j := by
    rw [FeedbackStepState.targetCoordinate]
    apply (x_lt_targetSegmentCrossing_iff hb.1 hb.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2
    simpa [targetRawRemainingSetAt, targetRawRemainingSet, FiniteSample.targetPoint,
      FiniteSample.targetPhase, FiniteSample.targetSlope, FeedbackStepState.slope,
      mul_comm] using hj
  have hterminalCross : state.x < state.targetCoordinate sample lam j :=
    lt_of_le_of_lt hstatex hcross
  have hterminalPhase := (x0_lt_targetSegmentCrossing_iff hb.1 hb.2
    (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).1 (by
      simpa [FeedbackStepState.targetCoordinate, FeedbackStepState.slope] using hterminalCross)
  simpa [targetRawRemainingSet, FiniteSample.targetPoint, FiniteSample.targetPhase,
    FiniteSample.targetSlope, mul_comm] using hterminalPhase

/-- If all unseen labels remain beyond a later point of the active segment, they also satisfy the
terminal-knot remaining condition used by `FiniteHistoryFibre`. -/
theorem LiesInStateRemainingAt.liesInStateRemaining
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) {x : ℝ} (hstatex : state.x ≤ x)
    (hremaining : LiesInStateRemainingAt lam state x sample) :
    LiesInStateRemaining lam state sample := by
  constructor
  · intro i hi
    apply (mem_sourceRawRemainingSet_iff sample state lam i).1
    exact sourceRawRemainingAt_imp_terminal sample hlam0 hlamHalf state hstatex i
      (hremaining.1 i hi)
  · intro j hj
    apply (mem_targetRawRemainingSet_iff sample state lam j).1
    exact targetRawRemainingAt_imp_terminal sample hlam0 hlamHalf state hstatex j
      (hremaining.2 j hj)

/-! ## Coordinate cells -/

/-- A prescribed finite history is exactly the revealed history at coordinate `x`: the history is
realized, its terminal knot is at or before `x`, and every other label remains strictly beyond
`x` on the terminal affine segment. -/
def HistoryAtCoordinate (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (x : ℝ) : Prop :=
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
    terminal.x ≤ x ∧ LiesInStateRemainingAt lam terminal x sample

/-- A fixed prescribed history observed at a deterministic coordinate is a measurable event. -/
theorem measurableSet_historyAtCoordinate
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (x : ℝ) :
    MeasurableSet {sample : FiniteSample n |
      HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x} := by
  let terminal : FiniteSample n → FeedbackStepState n := fun sample ↦
    sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hterminal : Measurable terminal := by
    simpa [terminal] using FiniteSample.measurable_scheduledState
      (n := n) lam x0 p0 sourcePattern targetPattern history
  have hbranch := measurableSet_historyBranch (n := n) lam x0 p0
    sourcePattern targetPattern history
  have hbefore : MeasurableSet {sample : FiniteSample n | (terminal sample).x ≤ x} :=
    measurableSet_le (FeedbackStepState.measurable_x.comp hterminal) measurable_const
  have hpair : Measurable fun sample : FiniteSample n ↦ (sample, terminal sample) :=
    measurable_id.prodMk hterminal
  have hremaining : MeasurableSet {sample : FiniteSample n |
      LiesInStateRemainingAt lam (terminal sample) x sample} :=
    hpair (measurableSet_liesInStateRemainingAt_pair (n := n) lam x)
  change MeasurableSet ({sample : FiniteSample n |
      HistoryBranch sample lam x0 p0 sourcePattern targetPattern history} ∩
    ({sample : FiniteSample n | (terminal sample).x ≤ x} ∩
      {sample : FiniteSample n |
        LiesInStateRemainingAt lam (terminal sample) x sample}))
  exact hbranch.inter (hbefore.inter hremaining)

/-- Equality of the terminal seen tuple fixes the scheduled terminal state. -/
theorem scheduledState_eq_of_feedbackSeenTuple_eq
    (sample₁ sample₂ : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) sample₁ =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample₂) :
    sample₁.scheduledState lam x0 p0 sourcePattern targetPattern history =
      sample₂.scheduledState lam x0 p0 sourcePattern targetPattern history := by
  apply FiniteSample.scheduledState_eq_of_history_points_eq
  intro label hlabel
  have hlabelS : label ∈ feedbackTerminalLabelSet sourcePattern targetPattern history := by
    cases label with
    | inl i =>
        simp only [mem_feedbackTerminalLabelSet_inl]
        exact Finset.mem_union_right _
          (FiniteSample.mem_sourceHistorySet_of_mem history i hlabel)
    | inr j =>
        simp only [mem_feedbackTerminalLabelSet_inr]
        exact Finset.mem_union_right _
          (FiniteSample.mem_targetHistorySet_of_mem history j hlabel)
  have hpoint := congrFun htuple ⟨label, hlabelS⟩
  simpa [feedbackSeenTuple, feedbackLabelTuple] using hpoint

/-- In a fixed seen-coordinate section containing a realized coordinate cell, membership in that
cell is exactly the later strict remaining-region condition. -/
theorem historyAtCoordinate_iff_liesInStateRemainingAt_of_seenTuple_eq
    (reference sample : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history x)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x ↔
      LiesInStateRemainingAt lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) x sample := by
  let terminal :=
    reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hstateEq := scheduledState_eq_of_feedbackSeenTuple_eq reference sample lam x0 p0
    sourcePattern targetPattern history htuple
  have hbranchReference :
      HistoryBranch reference lam x0 p0 sourcePattern targetPattern history := href.1
  have hterminalx : terminal.x ≤ x := href.2.1
  constructor
  · intro hsample
    change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x ∧
      LiesInStateRemainingAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x sample at hsample
    simpa [terminal, hstateEq] using hsample.2.2
  · intro hremainingAt
    have hremainingTerminal : LiesInStateRemaining lam terminal sample :=
      hremainingAt.liesInStateRemaining sample hlam0 hlamHalf terminal hterminalx
    have hbranchSample :
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history :=
      (historyBranch_iff_liesInStateRemaining_of_seenTuple_eq
        reference sample hlam0 hlamHalf hbranchReference htuple).2 hremainingTerminal
    change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤ x ∧
      LiesInStateRemainingAt lam
        (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) x sample
    refine ⟨hbranchSample, ?_, ?_⟩
    · simpa [terminal, ← hstateEq] using hterminalx
    · simpa [terminal, ← hstateEq] using hremainingAt

end OTSelector
