import OTSelector.Feedback.ForcedHistory
import OTSelector.Feedback.FeedbackPointLaw
import OTSelector.Feedback.TrueArea

/-!
# Deterministic geometry on a finite forced history

This module packages the purely deterministic branch facts needed by the later conditional-law
argument.  A branch is a finite initial-state match together with the forced-history realization;
the probabilistic law of such a branch is deliberately not part of this file.
-/

open Set

namespace OTSelector

variable {n : ℕ}

namespace FeedbackStepState

variable {n : ℕ}

/-- A forced step depends on a prescribed label only through that label's marked point. -/
theorem forcedLabelStep_eq_of_feedbackLabelPoint_eq
    (sample₁ sample₂ : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (label : FeedbackLabel n)
    (hpoint : feedbackLabelPoint label sample₁ = feedbackLabelPoint label sample₂) :
    state.forcedLabelStep sample₁ lam label =
      state.forcedLabelStep sample₂ lam label := by
  cases label with
  | inl i =>
      have hheight : sample₁.sourceHeight i = sample₂.sourceHeight i :=
        congrArg Prod.fst hpoint
      have hmark : sample₁.sourceMark i = sample₂.sourceMark i :=
        congrArg Prod.snd hpoint
      simp [forcedLabelStep, labelCoordinate, sourceCoordinate, FiniteSample.sourceSlope,
        hheight, hmark]
  | inr j =>
      have hheight : sample₁.targetHeight j = sample₂.targetHeight j :=
        congrArg Prod.fst hpoint
      have hmark : sample₁.targetMark j = sample₂.targetMark j :=
        congrArg Prod.snd hpoint
      simp [forcedLabelStep, labelCoordinate, targetCoordinate, FiniteSample.targetSlope,
        hheight, hmark]

end FeedbackStepState

namespace FiniteSample

variable {n : ℕ}

/-- A scheduled forced history is unchanged when all labels in the history have the same points. -/
theorem scheduledStateFrom_eq_of_history_points_eq
    (sample₁ sample₂ : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (history : List (FeedbackLabel n))
    (hpoints : ∀ label, label ∈ history →
      feedbackLabelPoint label sample₁ = feedbackLabelPoint label sample₂) :
    scheduledStateFrom sample₁ lam state history =
      scheduledStateFrom sample₂ lam state history := by
  induction history generalizing state with
  | nil => rfl
  | cons label history ih =>
      have hpoint : feedbackLabelPoint label sample₁ = feedbackLabelPoint label sample₂ :=
        hpoints label (by simp)
      have hstep := FeedbackStepState.forcedLabelStep_eq_of_feedbackLabelPoint_eq
        sample₁ sample₂ lam state label hpoint
      change scheduledStateFrom sample₁ lam
          (state.forcedLabelStep sample₁ lam label) history =
        scheduledStateFrom sample₂ lam
          (state.forcedLabelStep sample₂ lam label) history
      rw [hstep]
      apply ih
      intro label' hlabel'
      exact hpoints label' (by simp [hlabel'])

/-- The scheduled state from a fixed initial pattern depends on a history only through its points. -/
theorem scheduledState_eq_of_history_points_eq
    (sample₁ sample₂ : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hpoints : ∀ label, label ∈ history →
      feedbackLabelPoint label sample₁ = feedbackLabelPoint label sample₂) :
    scheduledState sample₁ lam x0 p0 sourcePattern targetPattern history =
      scheduledState sample₂ lam x0 p0 sourcePattern targetPattern history := by
  exact scheduledStateFrom_eq_of_history_points_eq sample₁ sample₂ lam
    (forcedInitialState x0 p0 sourcePattern targetPattern) history hpoints

end FiniteSample

/-- A deterministic finite-history branch with prescribed initial seen sets. -/
def HistoryBranch (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) : Prop :=
  sample.initialFeedbackState x0 p0 =
      FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern ∧
    FiniteSample.ForcedHistoryRealizes sample lam
      (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern) history

/-- The scheduled state on a realized branch inherits the ordinary recursion invariant. -/
theorem HistoryBranch.scheduledState_forwardValid
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history) :
    sample.ForwardValid
      (FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history) := by
  have heq := FiniteSample.feedbackState_eq_scheduledState_of_history sample lam x0 p0
    sourcePattern targetPattern history hbranch.1 hbranch.2
  rw [← heq]
  exact sample.feedbackState_forwardValid hlam0 hlamHalf x0 p0 history.length

/-- A source point whose label is not seen lies in the current source remaining region. -/
theorem sourcePoint_mem_sourceRemainingSet_of_forwardValid
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (i : Fin n) (hstate : sample.ForwardValid state)
    (hi : i ∉ state.seenSource) :
    rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
      sourceRemainingSet (n : ℝ)
        (segmentCurve state.x state.p (state.slope lam)) state.x := by
  constructor
  · constructor
    · simp only [rankStripMap, rankCoordinateMap, FiniteSample.sourcePoint]
      change 0 ≤ (n : ℝ) * (sample.sourceHeight i : ℝ) ∧
        (n : ℝ) * (sample.sourceHeight i : ℝ) ≤ (n : ℝ)
      constructor
      · have hn : 0 ≤ (n : ℝ) := by positivity
        have ht0 := (sample.sourceHeight i).property.1
        exact mul_nonneg hn ht0
      · have hn : 0 ≤ (n : ℝ) := by positivity
        have ht1 := (sample.sourceHeight i).property.2
        nlinarith [mul_nonneg hn (sub_nonneg.mpr ht1)]
    · simp only [rankStripMap, FiniteSample.sourcePoint, Set.mem_univ]
  · change ¬ ((n : ℝ) * (sample.sourceHeight i : ℝ) +
      segmentCurve state.x state.p (state.slope lam) state.x *
        (1 - (sample.sourceMark i : ℝ)) ≤ state.x)
    have hfuture := hstate.1 i hi
    have hcurve : segmentCurve state.x state.p (state.slope lam) state.x = state.p := by
      simp [segmentCurve]
    rw [hcurve]
    simpa [FiniteSample.sourceSlope, mul_comm] using not_le_of_gt hfuture

/-- A target point whose label is not seen lies in the current target remaining region. -/
theorem targetPoint_mem_targetRemainingSet_of_forwardValid
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (j : Fin n) (hstate : sample.ForwardValid state)
    (hj : j ∉ state.seenTarget) :
    rankStripMap (n : ℝ) (sample.targetPoint j) ∈
      targetRemainingSet (n : ℝ)
        (segmentCurve state.x state.p (state.slope lam)) state.x := by
  constructor
  · constructor
    · simp only [rankStripMap, rankCoordinateMap, FiniteSample.targetPoint]
      change 0 ≤ (n : ℝ) * (sample.targetHeight j : ℝ) ∧
        (n : ℝ) * (sample.targetHeight j : ℝ) ≤ (n : ℝ)
      constructor
      · have hn : 0 ≤ (n : ℝ) := by positivity
        have ht0 := (sample.targetHeight j).property.1
        exact mul_nonneg hn ht0
      · have hn : 0 ≤ (n : ℝ) := by positivity
        have ht1 := (sample.targetHeight j).property.2
        nlinarith [mul_nonneg hn (sub_nonneg.mpr ht1)]
    · simp only [rankStripMap, FiniteSample.targetPoint, Set.mem_univ]
  · change ¬ ((n : ℝ) * (sample.targetHeight j : ℝ) -
      segmentCurve state.x state.p (state.slope lam) state.x *
        (1 + (sample.targetMark j : ℝ)) ≤ state.x)
    have hfuture := hstate.2 j hj
    have hcurve : segmentCurve state.x state.p (state.slope lam) state.x = state.p := by
      simp [segmentCurve]
    rw [hcurve]
    simpa [FiniteSample.targetSlope, mul_comm] using not_le_of_gt hfuture

/-! ## Branch-specialized forms for later fibre arguments -/

theorem HistoryBranch.sourcePoint_mem_sourceRemainingSet
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (i : Fin n)
    (hi : i ∉
      (FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).seenSource) :
    rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
      sourceRemainingSet (n : ℝ)
        (segmentCurve
          (FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).x
          (FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).p
          ((FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).slope lam))
        (FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).x := by
  exact sourcePoint_mem_sourceRemainingSet_of_forwardValid sample lam _ i
    (HistoryBranch.scheduledState_forwardValid sample hlam0 hlamHalf hbranch) hi

theorem HistoryBranch.targetPoint_mem_targetRemainingSet
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (j : Fin n)
    (hj : j ∉
      (FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).seenTarget) :
    rankStripMap (n : ℝ) (sample.targetPoint j) ∈
      targetRemainingSet (n : ℝ)
        (segmentCurve
          (FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).x
          (FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).p
          ((FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).slope lam))
        (FiniteSample.scheduledState sample lam x0 p0 sourcePattern targetPattern history).x := by
  exact targetPoint_mem_targetRemainingSet_of_forwardValid sample lam _ j
    (HistoryBranch.scheduledState_forwardValid sample hlam0 hlamHalf hbranch) hj

end OTSelector
