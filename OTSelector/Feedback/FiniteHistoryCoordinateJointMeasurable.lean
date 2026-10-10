import OTSelector.Feedback.FiniteHistoryBefore

/-!
# Joint measurability of finite-history coordinate cells

For a fixed prescribed history, both the right-continuous history cell and its strict
pre-jump counterpart are measurable jointly in the observation coordinate and the finite
sample.  The proof writes the remaining-label conditions as finite intersections of explicit
measurable inequalities.
-/

open MeasureTheory Set
open scoped Classical

namespace OTSelector

variable {n : ℕ}

/-- A fixed prescribed history observed at a varying coordinate is jointly measurable in the
coordinate and the sample. -/
theorem measurableSet_historyAtCoordinate_joint
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    MeasurableSet {pair : ℝ × FiniteSample n |
      HistoryAtCoordinate pair.2 lam x0 p0 sourcePattern targetPattern history pair.1} := by
  classical
  let terminal : ℝ × FiniteSample n → FeedbackStepState n := fun pair ↦
    pair.2.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hterminal : Measurable terminal := by
    exact (FiniteSample.measurable_scheduledState
      (n := n) lam x0 p0 sourcePattern targetPattern history).comp measurable_snd
  have hsampleState : Measurable fun pair : ℝ × FiniteSample n ↦
      (pair.2, terminal pair) :=
    measurable_snd.prodMk hterminal
  have hbranch : MeasurableSet {pair : ℝ × FiniteSample n |
      HistoryBranch pair.2 lam x0 p0 sourcePattern targetPattern history} :=
    measurable_snd <| measurableSet_historyBranch
      (n := n) lam x0 p0 sourcePattern targetPattern history
  have hterminal_le : MeasurableSet {pair : ℝ × FiniteSample n |
      (terminal pair).x ≤ pair.1} :=
    measurableSet_le (FeedbackStepState.measurable_x.comp hterminal) measurable_fst
  have hsource (i : Fin n) :
      MeasurableSet {pair : ℝ × FiniteSample n |
        i ∉ (terminal pair).seenSource →
          pair.2.sourcePoint i ∈ sourceRawRemainingSetAt n lam (terminal pair) pair.1} := by
    have hseen : MeasurableSet {pair : ℝ × FiniteSample n |
        i ∈ (terminal pair).seenSource} :=
      hsampleState (FiniteSample.measurableSet_mem_seenSource i)
    have hheight : Measurable fun pair : ℝ × FiniteSample n ↦
        (n : ℝ) * (pair.2.sourceHeight i : ℝ) :=
      measurable_const.mul <|
        (measurable_subtype_coe.comp (FiniteSample.measurable_sourceHeight i)).comp
          measurable_snd
    have hslope : Measurable fun pair : ℝ × FiniteSample n ↦ pair.2.sourceSlope i :=
      (FiniteSample.measurable_sourceSlope i).comp measurable_snd
    have hstatex : Measurable fun pair : ℝ × FiniteSample n ↦ (terminal pair).x :=
      FeedbackStepState.measurable_x.comp hterminal
    have hstatep : Measurable fun pair : ℝ × FiniteSample n ↦ (terminal pair).p :=
      FeedbackStepState.measurable_p.comp hterminal
    have hstateslope : Measurable fun pair : ℝ × FiniteSample n ↦
        (terminal pair).slope lam :=
      (FeedbackStepState.measurable_slope lam).comp hterminal
    have hcurve : Measurable fun pair : ℝ × FiniteSample n ↦
        segmentCurve (terminal pair).x (terminal pair).p ((terminal pair).slope lam) pair.1 := by
      simp only [segmentCurve]
      exact hstatep.add (hstateslope.mul (measurable_fst.sub hstatex))
    have hfuture : MeasurableSet {pair : ℝ × FiniteSample n |
        pair.1 < (n : ℝ) * (pair.2.sourceHeight i : ℝ) +
          pair.2.sourceSlope i *
            segmentCurve (terminal pair).x (terminal pair).p
              ((terminal pair).slope lam) pair.1} :=
      measurableSet_lt measurable_fst (hheight.add (hslope.mul hcurve))
    have hset :
        {pair : ℝ × FiniteSample n |
            i ∉ (terminal pair).seenSource →
              pair.2.sourcePoint i ∈
                sourceRawRemainingSetAt n lam (terminal pair) pair.1} =
          {pair : ℝ × FiniteSample n | i ∈ (terminal pair).seenSource} ∪
            {pair : ℝ × FiniteSample n |
              pair.1 < (n : ℝ) * (pair.2.sourceHeight i : ℝ) +
                pair.2.sourceSlope i *
                  segmentCurve (terminal pair).x (terminal pair).p
                    ((terminal pair).slope lam) pair.1} := by
      ext pair
      simp only [mem_union, mem_ofPred_eq]
      by_cases hi : i ∈ (terminal pair).seenSource
      · simp [hi]
      · simp [hi, sourceRawRemainingSetAt, sourceRawRemainingSet,
          FiniteSample.sourcePoint, FiniteSample.sourceSlope, mul_comm]
    rw [hset]
    exact hseen.union hfuture
  have htarget (j : Fin n) :
      MeasurableSet {pair : ℝ × FiniteSample n |
        j ∉ (terminal pair).seenTarget →
          pair.2.targetPoint j ∈ targetRawRemainingSetAt n lam (terminal pair) pair.1} := by
    have hseen : MeasurableSet {pair : ℝ × FiniteSample n |
        j ∈ (terminal pair).seenTarget} :=
      hsampleState (FiniteSample.measurableSet_mem_seenTarget j)
    have hheight : Measurable fun pair : ℝ × FiniteSample n ↦
        (n : ℝ) * (pair.2.targetHeight j : ℝ) :=
      measurable_const.mul <|
        (measurable_subtype_coe.comp (FiniteSample.measurable_targetHeight j)).comp
          measurable_snd
    have hslope : Measurable fun pair : ℝ × FiniteSample n ↦ pair.2.targetSlope j :=
      (FiniteSample.measurable_targetSlope j).comp measurable_snd
    have hstatex : Measurable fun pair : ℝ × FiniteSample n ↦ (terminal pair).x :=
      FeedbackStepState.measurable_x.comp hterminal
    have hstatep : Measurable fun pair : ℝ × FiniteSample n ↦ (terminal pair).p :=
      FeedbackStepState.measurable_p.comp hterminal
    have hstateslope : Measurable fun pair : ℝ × FiniteSample n ↦
        (terminal pair).slope lam :=
      (FeedbackStepState.measurable_slope lam).comp hterminal
    have hcurve : Measurable fun pair : ℝ × FiniteSample n ↦
        segmentCurve (terminal pair).x (terminal pair).p ((terminal pair).slope lam) pair.1 := by
      simp only [segmentCurve]
      exact hstatep.add (hstateslope.mul (measurable_fst.sub hstatex))
    have hfuture : MeasurableSet {pair : ℝ × FiniteSample n |
        pair.1 < (n : ℝ) * (pair.2.targetHeight j : ℝ) -
          pair.2.targetSlope j *
            segmentCurve (terminal pair).x (terminal pair).p
              ((terminal pair).slope lam) pair.1} :=
      measurableSet_lt measurable_fst (hheight.sub (hslope.mul hcurve))
    have hset :
        {pair : ℝ × FiniteSample n |
            j ∉ (terminal pair).seenTarget →
              pair.2.targetPoint j ∈
                targetRawRemainingSetAt n lam (terminal pair) pair.1} =
          {pair : ℝ × FiniteSample n | j ∈ (terminal pair).seenTarget} ∪
            {pair : ℝ × FiniteSample n |
              pair.1 < (n : ℝ) * (pair.2.targetHeight j : ℝ) -
                pair.2.targetSlope j *
                  segmentCurve (terminal pair).x (terminal pair).p
                    ((terminal pair).slope lam) pair.1} := by
      ext pair
      simp only [mem_union, mem_ofPred_eq]
      by_cases hj : j ∈ (terminal pair).seenTarget
      · simp [hj]
      · simp [hj, targetRawRemainingSetAt, targetRawRemainingSet,
          FiniteSample.targetPoint, FiniteSample.targetSlope, mul_comm]
    rw [hset]
    exact hseen.union hfuture
  have hsourceAll : MeasurableSet {pair : ℝ × FiniteSample n |
      ∀ i, i ∉ (terminal pair).seenSource →
        pair.2.sourcePoint i ∈
          sourceRawRemainingSetAt n lam (terminal pair) pair.1} := by
    rw [show {pair : ℝ × FiniteSample n |
        ∀ i, i ∉ (terminal pair).seenSource →
          pair.2.sourcePoint i ∈
            sourceRawRemainingSetAt n lam (terminal pair) pair.1} =
      ⋂ i : Fin n, {pair : ℝ × FiniteSample n |
        i ∉ (terminal pair).seenSource →
          pair.2.sourcePoint i ∈
            sourceRawRemainingSetAt n lam (terminal pair) pair.1} by
        ext pair
        simp]
    exact MeasurableSet.iInter hsource
  have htargetAll : MeasurableSet {pair : ℝ × FiniteSample n |
      ∀ j, j ∉ (terminal pair).seenTarget →
        pair.2.targetPoint j ∈
          targetRawRemainingSetAt n lam (terminal pair) pair.1} := by
    rw [show {pair : ℝ × FiniteSample n |
        ∀ j, j ∉ (terminal pair).seenTarget →
          pair.2.targetPoint j ∈
            targetRawRemainingSetAt n lam (terminal pair) pair.1} =
      ⋂ j : Fin n, {pair : ℝ × FiniteSample n |
        j ∉ (terminal pair).seenTarget →
          pair.2.targetPoint j ∈
            targetRawRemainingSetAt n lam (terminal pair) pair.1} by
        ext pair
        simp]
    exact MeasurableSet.iInter htarget
  have hremaining : MeasurableSet {pair : ℝ × FiniteSample n |
      LiesInStateRemainingAt lam (terminal pair) pair.1 pair.2} := by
    change MeasurableSet
      ({pair : ℝ × FiniteSample n |
          ∀ i, i ∉ (terminal pair).seenSource →
            pair.2.sourcePoint i ∈
              sourceRawRemainingSetAt n lam (terminal pair) pair.1} ∩
        {pair : ℝ × FiniteSample n |
          ∀ j, j ∉ (terminal pair).seenTarget →
            pair.2.targetPoint j ∈
              targetRawRemainingSetAt n lam (terminal pair) pair.1})
    exact hsourceAll.inter htargetAll
  change MeasurableSet
    ({pair : ℝ × FiniteSample n |
        HistoryBranch pair.2 lam x0 p0 sourcePattern targetPattern history} ∩
      ({pair : ℝ × FiniteSample n | (terminal pair).x ≤ pair.1} ∩
        {pair : ℝ × FiniteSample n |
          LiesInStateRemainingAt lam (terminal pair) pair.1 pair.2}))
  exact hbranch.inter (hterminal_le.inter hremaining)

/-- A fixed prescribed strict pre-jump history is jointly measurable in the coordinate and the
sample. -/
theorem measurableSet_historyBeforeCoordinate_joint
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    MeasurableSet {pair : ℝ × FiniteSample n |
      HistoryBeforeCoordinate pair.2 lam x0 p0
        sourcePattern targetPattern history pair.1} := by
  classical
  let terminal : ℝ × FiniteSample n → FeedbackStepState n := fun pair ↦
    pair.2.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hterminal : Measurable terminal := by
    exact (FiniteSample.measurable_scheduledState
      (n := n) lam x0 p0 sourcePattern targetPattern history).comp measurable_snd
  have hsampleState : Measurable fun pair : ℝ × FiniteSample n ↦
      (pair.2, terminal pair) :=
    measurable_snd.prodMk hterminal
  have hbranch : MeasurableSet {pair : ℝ × FiniteSample n |
      HistoryBranch pair.2 lam x0 p0 sourcePattern targetPattern history} :=
    measurable_snd <| measurableSet_historyBranch
      (n := n) lam x0 p0 sourcePattern targetPattern history
  have hterminal_lt : MeasurableSet {pair : ℝ × FiniteSample n |
      (terminal pair).x < pair.1} :=
    measurableSet_lt (FeedbackStepState.measurable_x.comp hterminal) measurable_fst
  have hsource (i : Fin n) :
      MeasurableSet {pair : ℝ × FiniteSample n |
        i ∉ (terminal pair).seenSource →
          pair.1 < (terminal pair).sourceCoordinate pair.2 lam i} := by
    have hseen : MeasurableSet {pair : ℝ × FiniteSample n |
        i ∈ (terminal pair).seenSource} :=
      hsampleState (FiniteSample.measurableSet_mem_seenSource i)
    have hcoord : Measurable fun pair : ℝ × FiniteSample n ↦
        (terminal pair).sourceCoordinate pair.2 lam i :=
      (FiniteSample.measurable_sourceCoordinate lam i).comp hsampleState
    have hlt : MeasurableSet {pair : ℝ × FiniteSample n |
        pair.1 < (terminal pair).sourceCoordinate pair.2 lam i} :=
      measurableSet_lt measurable_fst hcoord
    have hset :
        {pair : ℝ × FiniteSample n |
            i ∉ (terminal pair).seenSource →
              pair.1 < (terminal pair).sourceCoordinate pair.2 lam i} =
          {pair : ℝ × FiniteSample n | i ∈ (terminal pair).seenSource} ∪
            {pair : ℝ × FiniteSample n |
              pair.1 < (terminal pair).sourceCoordinate pair.2 lam i} := by
      ext pair
      by_cases hi : i ∈ (terminal pair).seenSource <;> simp [hi]
    rw [hset]
    exact hseen.union hlt
  have htarget (j : Fin n) :
      MeasurableSet {pair : ℝ × FiniteSample n |
        j ∉ (terminal pair).seenTarget →
          pair.1 < (terminal pair).targetCoordinate pair.2 lam j} := by
    have hseen : MeasurableSet {pair : ℝ × FiniteSample n |
        j ∈ (terminal pair).seenTarget} :=
      hsampleState (FiniteSample.measurableSet_mem_seenTarget j)
    have hcoord : Measurable fun pair : ℝ × FiniteSample n ↦
        (terminal pair).targetCoordinate pair.2 lam j :=
      (FiniteSample.measurable_targetCoordinate lam j).comp hsampleState
    have hlt : MeasurableSet {pair : ℝ × FiniteSample n |
        pair.1 < (terminal pair).targetCoordinate pair.2 lam j} :=
      measurableSet_lt measurable_fst hcoord
    have hset :
        {pair : ℝ × FiniteSample n |
            j ∉ (terminal pair).seenTarget →
              pair.1 < (terminal pair).targetCoordinate pair.2 lam j} =
          {pair : ℝ × FiniteSample n | j ∈ (terminal pair).seenTarget} ∪
            {pair : ℝ × FiniteSample n |
              pair.1 < (terminal pair).targetCoordinate pair.2 lam j} := by
      ext pair
      by_cases hj : j ∈ (terminal pair).seenTarget <;> simp [hj]
    rw [hset]
    exact hseen.union hlt
  have hsourceAll : MeasurableSet {pair : ℝ × FiniteSample n |
      ∀ i, i ∉ (terminal pair).seenSource →
        pair.1 < (terminal pair).sourceCoordinate pair.2 lam i} := by
    rw [show {pair : ℝ × FiniteSample n |
        ∀ i, i ∉ (terminal pair).seenSource →
          pair.1 < (terminal pair).sourceCoordinate pair.2 lam i} =
      ⋂ i : Fin n, {pair : ℝ × FiniteSample n |
        i ∉ (terminal pair).seenSource →
          pair.1 < (terminal pair).sourceCoordinate pair.2 lam i} by
        ext pair
        simp]
    exact MeasurableSet.iInter hsource
  have htargetAll : MeasurableSet {pair : ℝ × FiniteSample n |
      ∀ j, j ∉ (terminal pair).seenTarget →
        pair.1 < (terminal pair).targetCoordinate pair.2 lam j} := by
    rw [show {pair : ℝ × FiniteSample n |
        ∀ j, j ∉ (terminal pair).seenTarget →
          pair.1 < (terminal pair).targetCoordinate pair.2 lam j} =
      ⋂ j : Fin n, {pair : ℝ × FiniteSample n |
        j ∉ (terminal pair).seenTarget →
          pair.1 < (terminal pair).targetCoordinate pair.2 lam j} by
        ext pair
        simp]
    exact MeasurableSet.iInter htarget
  have hbase : MeasurableSet
      ({pair : ℝ × FiniteSample n |
          HistoryBranch pair.2 lam x0 p0 sourcePattern targetPattern history} ∩
        ({pair : ℝ × FiniteSample n | (terminal pair).x < pair.1} ∩
          ({pair : ℝ × FiniteSample n |
              ∀ i, i ∉ (terminal pair).seenSource →
                pair.1 < (terminal pair).sourceCoordinate pair.2 lam i} ∩
            {pair : ℝ × FiniteSample n |
              ∀ j, j ∉ (terminal pair).seenTarget →
                pair.1 < (terminal pair).targetCoordinate pair.2 lam j}))) :=
    hbranch.inter (hterminal_lt.inter (hsourceAll.inter htargetAll))
  have hnoTies : MeasurableSet {pair : ℝ × FiniteSample n |
      pair.2.NoFeedbackTies lam x0 p0} :=
    measurable_snd <| FiniteSample.measurableSet_noFeedbackTies lam x0 p0
  change MeasurableSet
    (({pair : ℝ × FiniteSample n |
        HistoryBranch pair.2 lam x0 p0 sourcePattern targetPattern history} ∩
      ({pair : ℝ × FiniteSample n | (terminal pair).x < pair.1} ∩
        ({pair : ℝ × FiniteSample n |
            ∀ i, i ∉ (terminal pair).seenSource →
              pair.1 < (terminal pair).sourceCoordinate pair.2 lam i} ∩
          {pair : ℝ × FiniteSample n |
            ∀ j, j ∉ (terminal pair).seenTarget →
              pair.1 < (terminal pair).targetCoordinate pair.2 lam j}))) ∩
      {pair : ℝ × FiniteSample n | pair.2.NoFeedbackTies lam x0 p0})
  exact hbase.inter hnoTies

end OTSelector
