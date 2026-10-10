import OTSelector.Feedback.FiniteHistoryCoverage

/-!
# Strict pre-jump history cells

`HistoryAtCoordinate` uses a right-continuous convention: a knot at `x` is already
included in the history at `x`.  Predictable quantities need the complementary strict
cell.  This file records that cell as an ordinary proposition, with no auxiliary witness.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

namespace FiniteSample

/-! ## The event-free condition at a deterministic coordinate -/

/--
There is no feedback knot at `x` in the non-initial finite horizon.

The explicit bounds avoid treating the initial knot `x₀` as an event and also cover
the stable plateau after the last genuine crossing.
-/
def NoFeedbackEventAt (sample : FiniteSample n) (lam x0 p0 x : ℝ) : Prop :=
  ∀ m, 0 < m → m ≤ 2 * n → sample.feedbackKnot lam x0 p0 m ≠ x

end FiniteSample

/-! ## Strict coordinate cells -/

/--
A prescribed history is the strict pre-jump history at `x`: it is a realized branch,
its terminal knot is strictly before `x`, and every terminal-unseen label has a
candidate crossing strictly after `x`; the no-tie condition is part of the same Prop.
-/
def HistoryBeforeCoordinate (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (x : ℝ) : Prop :=
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  (HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      terminal.x < x ∧
      (∀ i, i ∉ terminal.seenSource →
        x < terminal.sourceCoordinate sample lam i) ∧
      (∀ j, j ∉ terminal.seenTarget →
        x < terminal.targetCoordinate sample lam j)) ∧
    sample.NoFeedbackTies lam x0 p0

/-! ## Measurability -/

theorem measurableSet_historyBeforeCoordinate
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (x : ℝ) :
    MeasurableSet {sample : FiniteSample n |
      HistoryBeforeCoordinate sample lam x0 p0 sourcePattern targetPattern history x} := by
  classical
  let terminal : FiniteSample n → FeedbackStepState n := fun sample ↦
    sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hterminal : Measurable terminal := by
    simpa [terminal] using FiniteSample.measurable_scheduledState
      (n := n) lam x0 p0 sourcePattern targetPattern history
  have hpair : Measurable fun sample : FiniteSample n ↦ (sample, terminal sample) :=
    measurable_id.prodMk hterminal
  have hbranch := measurableSet_historyBranch (n := n) lam x0 p0
    sourcePattern targetPattern history
  have hterminal_lt : MeasurableSet {sample : FiniteSample n | (terminal sample).x < x} :=
    measurableSet_lt (FeedbackStepState.measurable_x.comp hterminal) measurable_const
  have hsource (i : Fin n) :
      MeasurableSet {sample : FiniteSample n |
        i ∉ (terminal sample).seenSource →
          x < (terminal sample).sourceCoordinate sample lam i} := by
    have hseen : MeasurableSet {sample : FiniteSample n |
        i ∈ (terminal sample).seenSource} :=
      hpair (FiniteSample.measurableSet_mem_seenSource i)
    have hcoord : Measurable fun sample : FiniteSample n ↦
        (terminal sample).sourceCoordinate sample lam i := by
      exact (FiniteSample.measurable_sourceCoordinate lam i).comp hpair
    have hlt : MeasurableSet {sample : FiniteSample n |
        x < (terminal sample).sourceCoordinate sample lam i} :=
      measurableSet_lt measurable_const hcoord
    have hset : {sample : FiniteSample n |
        i ∉ (terminal sample).seenSource →
          x < (terminal sample).sourceCoordinate sample lam i} =
        {sample : FiniteSample n | i ∈ (terminal sample).seenSource} ∪
          {sample : FiniteSample n |
          x < (terminal sample).sourceCoordinate sample lam i} := by
      ext sample
      by_cases hi : i ∈ (terminal sample).seenSource <;> simp [hi]
    rw [hset]
    exact hseen.union hlt
  have htarget (j : Fin n) :
      MeasurableSet {sample : FiniteSample n |
        j ∉ (terminal sample).seenTarget →
          x < (terminal sample).targetCoordinate sample lam j} := by
    have hseen : MeasurableSet {sample : FiniteSample n |
        j ∈ (terminal sample).seenTarget} :=
      hpair (FiniteSample.measurableSet_mem_seenTarget j)
    have hcoord : Measurable fun sample : FiniteSample n ↦
        (terminal sample).targetCoordinate sample lam j := by
      exact (FiniteSample.measurable_targetCoordinate lam j).comp hpair
    have hlt : MeasurableSet {sample : FiniteSample n |
        x < (terminal sample).targetCoordinate sample lam j} :=
      measurableSet_lt measurable_const hcoord
    have hset : {sample : FiniteSample n |
        j ∉ (terminal sample).seenTarget →
          x < (terminal sample).targetCoordinate sample lam j} =
        {sample : FiniteSample n | j ∈ (terminal sample).seenTarget} ∪
          {sample : FiniteSample n |
          x < (terminal sample).targetCoordinate sample lam j} := by
      ext sample
      by_cases hj : j ∈ (terminal sample).seenTarget <;> simp [hj]
    rw [hset]
    exact hseen.union hlt
  have hsourceAll : MeasurableSet {sample : FiniteSample n |
      ∀ i, i ∉ (terminal sample).seenSource →
        x < (terminal sample).sourceCoordinate sample lam i} := by
    have hset : {sample : FiniteSample n |
        ∀ i, i ∉ (terminal sample).seenSource →
          x < (terminal sample).sourceCoordinate sample lam i} =
        ⋂ i : Fin n, {sample : FiniteSample n |
          i ∉ (terminal sample).seenSource →
            x < (terminal sample).sourceCoordinate sample lam i} := by
      ext sample
      simp
    rw [hset]
    exact MeasurableSet.iInter hsource
  have htargetAll : MeasurableSet {sample : FiniteSample n |
      ∀ j, j ∉ (terminal sample).seenTarget →
        x < (terminal sample).targetCoordinate sample lam j} := by
    have hset : {sample : FiniteSample n |
        ∀ j, j ∉ (terminal sample).seenTarget →
          x < (terminal sample).targetCoordinate sample lam j} =
        ⋂ j : Fin n, {sample : FiniteSample n |
          j ∉ (terminal sample).seenTarget →
            x < (terminal sample).targetCoordinate sample lam j} := by
      ext sample
      simp
    rw [hset]
    exact MeasurableSet.iInter htarget
  have hbase : MeasurableSet ({sample : FiniteSample n |
      HistoryBranch sample lam x0 p0 sourcePattern targetPattern history} ∩
    ({sample : FiniteSample n | (terminal sample).x < x} ∩
      ({sample : FiniteSample n |
          ∀ i, i ∉ (terminal sample).seenSource →
            x < (terminal sample).sourceCoordinate sample lam i} ∩
        {sample : FiniteSample n |
          ∀ j, j ∉ (terminal sample).seenTarget →
            x < (terminal sample).targetCoordinate sample lam j}))) :=
    hbranch.inter (hterminal_lt.inter (hsourceAll.inter htargetAll))
  change MeasurableSet
    (({sample : FiniteSample n |
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history} ∩
      ({sample : FiniteSample n | (terminal sample).x < x} ∩
        ({sample : FiniteSample n |
            ∀ i, i ∉ (terminal sample).seenSource →
              x < (terminal sample).sourceCoordinate sample lam i} ∩
          {sample : FiniteSample n |
            ∀ j, j ∉ (terminal sample).seenTarget →
              x < (terminal sample).targetCoordinate sample lam j}))) ∩
      {sample : FiniteSample n | sample.NoFeedbackTies lam x0 p0})
  exact hbase.inter (FiniteSample.measurableSet_noFeedbackTies lam x0 p0)

/-! ## Strict cell implies the usual right-continuous cell -/

theorem historyBeforeCoordinate_imp_historyAtCoordinate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x) :
    HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x := by
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  change (HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      terminal.x < x ∧
      (∀ i, i ∉ terminal.seenSource →
        x < terminal.sourceCoordinate sample lam i) ∧
      (∀ j, j ∉ terminal.seenTarget →
        x < terminal.targetCoordinate sample lam j)) ∧
      sample.NoFeedbackTies lam x0 p0 at hbefore
  change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      terminal.x ≤ x ∧ LiesInStateRemainingAt lam terminal x sample
  have hbase := hbefore.1
  refine ⟨hbase.1, hbase.2.1.le, ?_⟩
  constructor
  · intro i hi
    have hcross : x < terminal.sourceCoordinate sample lam i := hbase.2.2.1 i hi
    have hcross' : x < sourceSegmentCrossing terminal.x terminal.p
        (terminal.slope lam) ((n : ℝ) * (sample.sourceHeight i : ℝ))
        (sample.sourceSlope i) := by
      simpa only [FeedbackStepState.sourceCoordinate, FeedbackStepState.slope] using hcross
    have ha := sample.sourceSlope_mem i
    have hphase := (x_lt_sourceSegmentCrossing_iff ha.1 ha.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).1 hcross'
    simpa [sourceRawRemainingSetAt, sourceRawRemainingSet, FiniteSample.sourcePoint,
      FiniteSample.sourceSlope, FeedbackStepState.slope, mul_comm] using hphase
  · intro j hj
    have hcross : x < terminal.targetCoordinate sample lam j := hbase.2.2.2 j hj
    have hcross' : x < targetSegmentCrossing terminal.x terminal.p
        (terminal.slope lam) ((n : ℝ) * (sample.targetHeight j : ℝ))
        (sample.targetSlope j) := by
      simpa only [FeedbackStepState.targetCoordinate, FeedbackStepState.slope] using hcross
    have hb := sample.targetSlope_mem j
    have hphase := (x_lt_targetSegmentCrossing_iff hb.1 hb.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).1 hcross'
    simpa [targetRawRemainingSetAt, targetRawRemainingSet, FiniteSample.targetPoint,
      FiniteSample.targetSlope, FeedbackStepState.slope, mul_comm] using hphase

/-! ## Coverage by strict cells -/

namespace FiniteSample

theorem exists_historyBeforeCoordinate_of_noFeedbackTies_of_noFeedbackEventAt
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hNoEvent : sample.NoFeedbackEventAt lam x0 p0 x) :
    ∃ history : List (FeedbackLabel n),
      HistoryBeforeCoordinate sample lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x ∧
      history.length ≤ 2 * n := by
  classical
  obtain ⟨history, hcell, hlen⟩ := sample.exists_historyAtCoordinate_of_noFeedbackTies
    hlam0 hlamHalf hx0x.le hNoTie
  let sourcePattern := sample.initialSeenSource x0 p0
  let targetPattern := sample.initialSeenTarget x0 p0
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hcell' : HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x := by
    simpa [sourcePattern, targetPattern] using hcell
  have hbranch := hcell'.1
  have hstate : sample.feedbackState lam x0 p0 history.length = terminal := by
    exact FiniteSample.feedbackState_eq_scheduledState_of_history sample lam x0 p0
      sourcePattern targetPattern history hbranch.1 hbranch.2
  have htermKnot : sample.feedbackKnot lam x0 p0 history.length = terminal.x := by
    simpa [FiniteSample.feedbackKnot, terminal] using
      congrArg FeedbackStepState.x hstate
  have hterminal_lt : terminal.x < x := by
    have hterminal_le : terminal.x ≤ x := hcell'.2.1
    by_cases heq : terminal.x = x
    · have hknot : sample.feedbackKnot lam x0 p0 history.length = x := by
        rw [htermKnot, heq]
      have hpos : 0 < history.length := by
        by_contra hnotpos
        have hzero : history.length = 0 := Nat.eq_zero_of_not_pos hnotpos
        have hx0eq : x0 = x := by
          simpa [FiniteSample.feedbackKnot, feedbackState_zero,
            initialFeedbackState, hzero] using hknot
        linarith
      exact False.elim (hNoEvent history.length hpos hlen hknot)
    · exact lt_of_le_of_ne hterminal_le heq
  have hsource : ∀ i, i ∉ terminal.seenSource →
      x < terminal.sourceCoordinate sample lam i := by
    intro i hi
    have hrem := hcell'.2.2.1 i hi
    have hline : x <
        (n : ℝ) * (sample.sourceHeight i : ℝ) +
          sample.sourceSlope i *
            segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
      simpa [sourceRawRemainingSetAt, sourceRawRemainingSet, FiniteSample.sourcePoint,
        FiniteSample.sourceSlope, FeedbackStepState.slope, mul_comm] using hrem
    have ha := sample.sourceSlope_mem i
    have hcross := (x_lt_sourceSegmentCrossing_iff ha.1 ha.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2 hline
    simpa only [FeedbackStepState.sourceCoordinate, FeedbackStepState.slope] using hcross
  have htarget : ∀ j, j ∉ terminal.seenTarget →
      x < terminal.targetCoordinate sample lam j := by
    intro j hj
    have hrem := hcell'.2.2.2 j hj
    have hline : x <
        (n : ℝ) * (sample.targetHeight j : ℝ) -
          sample.targetSlope j *
            segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
      simpa [targetRawRemainingSetAt, targetRawRemainingSet, FiniteSample.targetPoint,
        FiniteSample.targetSlope, FeedbackStepState.slope, mul_comm] using hrem
    have hb := sample.targetSlope_mem j
    have hcross := (x_lt_targetSegmentCrossing_iff hb.1 hb.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2 hline
    simpa only [FeedbackStepState.targetCoordinate, FeedbackStepState.slope] using hcross
  have hbefore : HistoryBeforeCoordinate sample lam x0 p0 sourcePattern targetPattern history x := by
    exact ⟨⟨hbranch, hterminal_lt, hsource, htarget⟩, hNoTie⟩
  refine ⟨history, ?_, hlen⟩
  simpa [sourcePattern, targetPattern] using hbefore

end FiniteSample

/-! ## The elapsed state on a strict cell -/

namespace HistoryBeforeCoordinate

theorem feedbackStateAtElapsed_eq_scheduledState
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ =
      sample.scheduledState lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history := by
  exact HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState sample hlam0 hlamHalf
    hx0x.le history
    (historyBeforeCoordinate_imp_historyAtCoordinate sample hlam0 hlamHalf hbefore)

end HistoryBeforeCoordinate

end OTSelector
