import OTSelector.Feedback.FiniteHistoryPartition

/-!
# Uniqueness of no-tie finite history cells

The finite index set is only a useful partition after restricting to the no-feedback-tie
locus.  This file proves that restriction deterministically.  The proof compares two forced
histories from the same actual recursive state; it does not identify histories from terminal
seen sets alone.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

namespace FiniteSample

/-! ## Elementary one-step facts -/

private theorem labelStepRealizes_candidates_nonempty
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    {label : FeedbackLabel n}
    (hlabel : labelStepRealizes sample lam state label) :
    (state.candidates sample lam).Nonempty := by
  cases label with
  | inl i =>
      have hi : i ∈ state.newSource sample lam := by
        rw [hlabel.1]
        simp
      have hi' : i ∈ Finset.univ \ state.seenSource :=
        (Finset.mem_filter.mp hi).1
      refine ⟨state.sourceCoordinate sample lam i, ?_⟩
      rw [FeedbackStepState.candidates]
      simp only [Finset.mem_union]
      left
      exact Finset.mem_image.mpr ⟨i, hi', rfl⟩
  | inr j =>
      have hj : j ∈ state.newTarget sample lam := by
        rw [hlabel.2]
        simp
      have hj' : j ∈ Finset.univ \ state.seenTarget :=
        (Finset.mem_filter.mp hj).1
      refine ⟨state.targetCoordinate sample lam j, ?_⟩
      rw [FeedbackStepState.candidates]
      simp only [Finset.mem_union]
      right
      exact Finset.mem_image.mpr ⟨j, hj', rfl⟩

private theorem labelStepRealizes_labelCoordinate_eq_nextCoordinate
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    {label : FeedbackLabel n}
    (hlabel : labelStepRealizes sample lam state label) :
    state.labelCoordinate sample lam label = state.nextCoordinate sample lam := by
  cases label with
  | inl i =>
      exact (Finset.mem_filter.mp (show i ∈ state.newSource sample lam by
        rw [hlabel.1]
        simp)).2
  | inr j =>
      exact (Finset.mem_filter.mp (show j ∈ state.newTarget sample lam by
        rw [hlabel.2]
        simp)).2

/-! A remaining-at-`x` state cannot have its next candidate at or before `x`. -/

private theorem nextCoordinate_gt_of_liesInStateRemainingAt
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) {x y : ℝ} (hyx : y ≤ x)
    (hremaining : LiesInStateRemainingAt lam state x sample)
    (hcand : (state.candidates sample lam).Nonempty) :
    y < state.nextCoordinate sample lam := by
  have hsource_gt : ∀ i, i ∉ state.seenSource →
      x < state.sourceCoordinate sample lam i := by
    intro i hi
    have hi_mem := hremaining.1 i hi
    have hi_line : x <
        (n : ℝ) * (sample.sourceHeight i : ℝ) + sample.sourceSlope i *
          segmentCurve state.x state.p (state.slope lam) x := by
      simpa [sourceRawRemainingSetAt, sourceRawRemainingSet, FiniteSample.sourcePoint,
        FiniteSample.sourceSlope, FeedbackStepState.slope, mul_comm] using hi_mem
    have ha := sample.sourceSlope_mem i
    have hcross := (x_lt_sourceSegmentCrossing_iff ha.1 ha.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2 hi_line
    simpa only [FeedbackStepState.sourceCoordinate, FeedbackStepState.slope] using hcross
  have htarget_gt : ∀ j, j ∉ state.seenTarget →
      x < state.targetCoordinate sample lam j := by
    intro j hj
    have hj_mem := hremaining.2 j hj
    have hj_line : x <
        (n : ℝ) * (sample.targetHeight j : ℝ) - sample.targetSlope j *
          segmentCurve state.x state.p (state.slope lam) x := by
      simpa [targetRawRemainingSetAt, targetRawRemainingSet, FiniteSample.targetPoint,
        FiniteSample.targetSlope, FeedbackStepState.slope, mul_comm] using hj_mem
    have hb := sample.targetSlope_mem j
    have hcross := (x_lt_targetSegmentCrossing_iff hb.1 hb.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2 hj_line
    simpa only [FeedbackStepState.targetCoordinate, FeedbackStepState.slope] using hcross
  have hnext_mem := state.nextCoordinate_mem_candidates sample lam hcand
  rw [FeedbackStepState.candidates] at hnext_mem
  simp only [Finset.mem_union] at hnext_mem
  rcases hnext_mem with hsource | htarget
  · rw [FeedbackStepState.sourceCandidates] at hsource
    obtain ⟨i, hi, hcoord⟩ := Finset.mem_image.mp hsource
    have hnotseen : i ∉ state.seenSource := (Finset.mem_sdiff.mp hi).2
    have hxnext : x < state.nextCoordinate sample lam := by
      exact hcoord ▸ hsource_gt i hnotseen
    exact hyx.trans_lt hxnext
  · rw [FeedbackStepState.targetCandidates] at htarget
    obtain ⟨j, hj, hcoord⟩ := Finset.mem_image.mp htarget
    have hnotseen : j ∉ state.seenTarget := (Finset.mem_sdiff.mp hj).2
    have hxnext : x < state.nextCoordinate sample lam := by
      exact hcoord ▸ htarget_gt j hnotseen
    exact hyx.trans_lt hxnext

/-! The scheduled forced path is coordinate-monotone on a realized branch. -/

private theorem scheduledStateFrom_x_ge_of_forwardValid
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) (hforward : sample.ForwardValid state)
    (history : List (FeedbackLabel n))
    (hgood : ForcedHistoryRealizes sample lam state history) :
    state.x ≤ (scheduledStateFrom sample lam state history).x := by
  induction history generalizing state with
  | nil => simp [scheduledStateFrom]
  | cons label history ih =>
      have hlabel := hgood.1
      have hcand := labelStepRealizes_candidates_nonempty sample lam state hlabel
      have hnext := sample.nextCoordinate_gt_of_forwardValid hlam0 hlamHalf hforward hcand
      have hcoord := labelStepRealizes_labelCoordinate_eq_nextCoordinate sample lam state hlabel
      have hstepx : state.x < (state.forcedLabelStep sample lam label).x := by
        cases label with
        | inl i =>
            change state.x < state.sourceCoordinate sample lam i
            have hcoord' : state.sourceCoordinate sample lam i = state.nextCoordinate sample lam := by
              simpa using hcoord
            rw [hcoord']
            exact hnext
        | inr j =>
            change state.x < state.targetCoordinate sample lam j
            have hcoord' : state.targetCoordinate sample lam j = state.nextCoordinate sample lam := by
              simpa using hcoord
            rw [hcoord']
            exact hnext
      have hforced : sample.ForwardValid (state.forcedLabelStep sample lam label) := by
        have hstep : state.step sample lam = state.forcedLabelStep sample lam label := by
          cases label with
          | inl i =>
              exact step_eq_forcedLabelStep_of_source_singleton sample lam state i
                hlabel.1 hlabel.2
          | inr j =>
              exact step_eq_forcedLabelStep_of_target_singleton sample lam state j
                hlabel.1 hlabel.2
        rw [← hstep]
        exact sample.step_forwardValid hlam0 hlamHalf state
      have htail := ih (state := state.forcedLabelStep sample lam label)
        hforced hgood.2
      change state.x ≤ (scheduledStateFrom sample lam
        (state.forcedLabelStep sample lam label) history).x
      exact hstepx.le.trans htail

/-! ## A no-tie index cannot carry two different valid labels -/

private theorem feedbackIndex_lt_of_labelStepRealizes
    (sample : FiniteSample n) (lam x0 p0 : ℝ) (m : ℕ)
    (_hm : m ≤ 2 * n) (state : FeedbackStepState n)
    (hstate : sample.feedbackState lam x0 p0 m = state)
    {label : FeedbackLabel n}
    (hlabel : labelStepRealizes sample lam state label) :
    m < 2 * n := by
  have hcand := labelStepRealizes_candidates_nonempty sample lam state hlabel
  by_contra hnot
  have hge : 2 * n ≤ m := Nat.le_of_not_gt hnot
  have hstable : sample.feedbackState lam x0 p0 m =
      sample.feedbackState lam x0 p0 (2 * n) := by
    have h := sample.feedbackState_eq_of_candidates_eq_empty lam x0 p0 (2 * n)
      (sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0) (m - 2 * n)
    simpa [Nat.add_sub_of_le hge] using h
  have hempty : state.candidates sample lam = ∅ := by
    rw [← hstate, hstable]
    exact sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0
  exact hcand.ne_empty hempty

private theorem label_eq_of_noFeedbackTies
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (hties : sample.NoFeedbackTies lam x0 p0)
    (m : ℕ) (hm : m ≤ 2 * n) (state : FeedbackStepState n)
    (hstate : sample.feedbackState lam x0 p0 m = state)
    {label₁ label₂ : FeedbackLabel n}
    (hlabel₁ : labelStepRealizes sample lam state label₁)
    (hlabel₂ : labelStepRealizes sample lam state label₂) :
    label₁ = label₂ := by
  have hm_lt := feedbackIndex_lt_of_labelStepRealizes sample lam x0 p0 m hm state
    hstate hlabel₁
  have hupper := hties m hm_lt
  rw [hstate] at hupper
  cases label₁ with
  | inl i =>
      cases label₂ with
      | inl j =>
          have hi := hlabel₁.1
          have hj := hlabel₂.1
          have hs : ({i} : Finset (Fin n)) = {j} := hi.symm.trans hj
          simpa using hs
      | inr j =>
          have hi : (state.newSource sample lam).card = 1 := by
            rw [hlabel₁.1]
            simp
          have hj : (state.newTarget sample lam).card = 1 := by
            rw [hlabel₂.2]
            simp
          omega
  | inr i =>
      cases label₂ with
      | inl j =>
          have hi : (state.newTarget sample lam).card = 1 := by
            rw [hlabel₁.2]
            simp
          have hj : (state.newSource sample lam).card = 1 := by
            rw [hlabel₂.1]
            simp
          omega
      | inr j =>
          have hi := hlabel₁.2
          have hj := hlabel₂.2
          have ht : ({i} : Finset (Fin n)) = {j} := hi.symm.trans hj
          simpa using ht

/-! ## Uniqueness of a coordinate history -/

private theorem forcedHistory_eq_of_noFeedbackTies_from
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hties : sample.NoFeedbackTies lam x0 p0)
    (m : ℕ) (hm : m ≤ 2 * n) (state : FeedbackStepState n)
    (hstate : sample.feedbackState lam x0 p0 m = state)
    (history₁ history₂ : List (FeedbackLabel n))
    (hgood₁ : ForcedHistoryRealizes sample lam state history₁)
    (hgood₂ : ForcedHistoryRealizes sample lam state history₂)
    (hterminal₁ :
      (scheduledStateFrom sample lam state history₁).x ≤ x ∧
        LiesInStateRemainingAt lam
          (scheduledStateFrom sample lam state history₁) x sample)
    (hterminal₂ :
      (scheduledStateFrom sample lam state history₂).x ≤ x ∧
        LiesInStateRemainingAt lam
          (scheduledStateFrom sample lam state history₂) x sample) :
    history₁ = history₂ := by
  cases history₁ with
  | nil =>
      cases history₂ with
      | nil => rfl
      | cons label₂ tail₂ =>
          have hlabel₂ := hgood₂.1
          have hcand₂ := labelStepRealizes_candidates_nonempty sample lam state hlabel₂
          have hnext := nextCoordinate_gt_of_liesInStateRemainingAt sample hlam0 hlamHalf
            state (le_rfl : x ≤ x) hterminal₁.2 hcand₂
          have hcoord := labelStepRealizes_labelCoordinate_eq_nextCoordinate sample lam state hlabel₂
          have hstepx : x < (state.forcedLabelStep sample lam label₂).x := by
            cases label₂ with
            | inl i =>
                change x < state.sourceCoordinate sample lam i
                have hcoord' : state.sourceCoordinate sample lam i = state.nextCoordinate sample lam := by
                  simpa using hcoord
                rw [hcoord']
                exact hnext
            | inr j =>
                change x < state.targetCoordinate sample lam j
                have hcoord' : state.targetCoordinate sample lam j = state.nextCoordinate sample lam := by
                  simpa using hcoord
                rw [hcoord']
                exact hnext
          have hforward : sample.ForwardValid (state.forcedLabelStep sample lam label₂) := by
            have hstep : state.step sample lam = state.forcedLabelStep sample lam label₂ := by
              cases label₂ with
              | inl i =>
                  exact step_eq_forcedLabelStep_of_source_singleton sample lam state i
                    hlabel₂.1 hlabel₂.2
              | inr j =>
                  exact step_eq_forcedLabelStep_of_target_singleton sample lam state j
                    hlabel₂.1 hlabel₂.2
            rw [← hstep]
            exact sample.step_forwardValid hlam0 hlamHalf state
          have hmono := scheduledStateFrom_x_ge_of_forwardValid sample hlam0 hlamHalf
            (state.forcedLabelStep sample lam label₂) hforward tail₂ hgood₂.2
          have hle : (state.forcedLabelStep sample lam label₂).x ≤ x := by
            have hmono' : (state.forcedLabelStep sample lam label₂).x ≤
                (scheduledStateFrom sample lam
                  (state.forcedLabelStep sample lam label₂) tail₂).x := hmono
            exact hmono'.trans (by simpa [scheduledStateFrom] using hterminal₂.1)
          linarith
  | cons label₁ tail₁ =>
      cases history₂ with
      | nil =>
          have hlabel₁ := hgood₁.1
          have hcand₁ := labelStepRealizes_candidates_nonempty sample lam state hlabel₁
          have hnext := nextCoordinate_gt_of_liesInStateRemainingAt sample hlam0 hlamHalf
            state (le_rfl : x ≤ x) hterminal₂.2 hcand₁
          have hcoord := labelStepRealizes_labelCoordinate_eq_nextCoordinate sample lam state hlabel₁
          have hstepx : x < (state.forcedLabelStep sample lam label₁).x := by
            cases label₁ with
            | inl i =>
                change x < state.sourceCoordinate sample lam i
                have hcoord' : state.sourceCoordinate sample lam i = state.nextCoordinate sample lam := by
                  simpa using hcoord
                rw [hcoord']
                exact hnext
            | inr j =>
                change x < state.targetCoordinate sample lam j
                have hcoord' : state.targetCoordinate sample lam j = state.nextCoordinate sample lam := by
                  simpa using hcoord
                rw [hcoord']
                exact hnext
          have hforward : sample.ForwardValid (state.forcedLabelStep sample lam label₁) := by
            have hstep : state.step sample lam = state.forcedLabelStep sample lam label₁ := by
              cases label₁ with
              | inl i =>
                  exact step_eq_forcedLabelStep_of_source_singleton sample lam state i
                    hlabel₁.1 hlabel₁.2
              | inr j =>
                  exact step_eq_forcedLabelStep_of_target_singleton sample lam state j
                    hlabel₁.1 hlabel₁.2
            rw [← hstep]
            exact sample.step_forwardValid hlam0 hlamHalf state
          have hmono := scheduledStateFrom_x_ge_of_forwardValid sample hlam0 hlamHalf
            (state.forcedLabelStep sample lam label₁) hforward tail₁ hgood₁.2
          have hle : (state.forcedLabelStep sample lam label₁).x ≤ x := by
            have hmono' : (state.forcedLabelStep sample lam label₁).x ≤
                (scheduledStateFrom sample lam
                  (state.forcedLabelStep sample lam label₁) tail₁).x := hmono
            exact hmono'.trans (by simpa [scheduledStateFrom] using hterminal₁.1)
          linarith
      | cons label₂ tail₂ =>
          have hlabel₁ := hgood₁.1
          have hlabel₂ := hgood₂.1
          have hhead : label₁ = label₂ :=
            label_eq_of_noFeedbackTies sample lam x0 p0 hties m hm state hstate
              hlabel₁ hlabel₂
          subst label₂
          have hstep : state.step sample lam = state.forcedLabelStep sample lam label₁ := by
            cases label₁ with
            | inl i =>
                exact step_eq_forcedLabelStep_of_source_singleton sample lam state i
                  hlabel₁.1 hlabel₁.2
            | inr j =>
                exact step_eq_forcedLabelStep_of_target_singleton sample lam state j
                  hlabel₁.1 hlabel₁.2
          have hm_lt := feedbackIndex_lt_of_labelStepRealizes sample lam x0 p0 m hm state
            hstate hlabel₁
          have hstate' : sample.feedbackState lam x0 p0 (m + 1) =
              state.forcedLabelStep sample lam label₁ := by
            rw [feedbackState_succ, hstate, hstep]
          have hm' : m + 1 ≤ 2 * n := by omega
          have hterminal₁' :
              (scheduledStateFrom sample lam
                (state.forcedLabelStep sample lam label₁) tail₁).x ≤ x ∧
                LiesInStateRemainingAt lam
                  (scheduledStateFrom sample lam
                    (state.forcedLabelStep sample lam label₁) tail₁) x sample := by
            simpa [scheduledStateFrom] using hterminal₁
          have hterminal₂' :
              (scheduledStateFrom sample lam
                (state.forcedLabelStep sample lam label₁) tail₂).x ≤ x ∧
                LiesInStateRemainingAt lam
                  (scheduledStateFrom sample lam
                    (state.forcedLabelStep sample lam label₁) tail₂) x sample := by
            simpa [scheduledStateFrom] using hterminal₂
          have htail := forcedHistory_eq_of_noFeedbackTies_from sample hlam0 hlamHalf hties
            (m + 1) hm' (state.forcedLabelStep sample lam label₁) hstate' tail₁ tail₂
            hgood₁.2 hgood₂.2 hterminal₁' hterminal₂'
          simp [htail]

/-! ## Public uniqueness and disjointness statements -/

theorem history_eq_of_noFeedbackTies_of_same_cell
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hties : sample.NoFeedbackTies lam x0 p0)
    (sourcePattern targetPattern : Finset (Fin n))
    (history₁ history₂ : List (FeedbackLabel n))
    (hcell₁ : HistoryAtCoordinate sample lam x0 p0
      sourcePattern targetPattern history₁ x)
    (hcell₂ : HistoryAtCoordinate sample lam x0 p0
      sourcePattern targetPattern history₂ x) :
    history₁ = history₂ := by
  change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history₁ ∧
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history₁).x ≤ x ∧
        LiesInStateRemainingAt lam
          (sample.scheduledState lam x0 p0 sourcePattern targetPattern history₁) x sample at hcell₁
  change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history₂ ∧
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history₂).x ≤ x ∧
        LiesInStateRemainingAt lam
          (sample.scheduledState lam x0 p0 sourcePattern targetPattern history₂) x sample at hcell₂
  have hinit : sample.initialFeedbackState x0 p0 =
      forcedInitialState x0 p0 sourcePattern targetPattern := hcell₁.1.1
  have hstate : sample.feedbackState lam x0 p0 0 =
      forcedInitialState x0 p0 sourcePattern targetPattern := by
    simpa [feedbackState_zero] using hinit
  have hterminal₁ :
      (scheduledStateFrom sample lam
        (forcedInitialState x0 p0 sourcePattern targetPattern) history₁).x ≤ x ∧
        LiesInStateRemainingAt lam
          (scheduledStateFrom sample lam
            (forcedInitialState x0 p0 sourcePattern targetPattern) history₁) x sample := by
    simpa [scheduledState] using hcell₁.2
  have hterminal₂ :
      (scheduledStateFrom sample lam
        (forcedInitialState x0 p0 sourcePattern targetPattern) history₂).x ≤ x ∧
        LiesInStateRemainingAt lam
          (scheduledStateFrom sample lam
            (forcedInitialState x0 p0 sourcePattern targetPattern) history₂) x sample := by
    simpa [scheduledState] using hcell₂.2
  exact forcedHistory_eq_of_noFeedbackTies_from sample hlam0 hlamHalf hties 0
    (by omega) (forcedInitialState x0 p0 sourcePattern targetPattern) hstate
    history₁ history₂ hcell₁.1.2 hcell₂.1.2 hterminal₁ hterminal₂

theorem historyCellIndex_eq_of_mem_of_noFeedbackTies
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hties : sample.NoFeedbackTies lam x0 p0)
    (index₁ index₂ : HistoryCellIndex n)
    (h₁ : sample ∈ historyCell index₁ lam x0 p0 x)
    (h₂ : sample ∈ historyCell index₂ lam x0 p0 x) :
    index₁ = index₂ := by
  rcases index₁ with ⟨source₁, target₁, history₁, hlen₁⟩
  rcases index₂ with ⟨source₂, target₂, history₂, hlen₂⟩
  change HistoryAtCoordinate sample lam x0 p0 source₁ target₁ history₁ x at h₁
  change HistoryAtCoordinate sample lam x0 p0 source₂ target₂ history₂ x at h₂
  have hinit₁ := h₁.1.1
  have hinit₂ := h₂.1.1
  have hforcedEq :
      forcedInitialState x0 p0 source₁ target₁ =
        forcedInitialState x0 p0 source₂ target₂ :=
    hinit₁.symm.trans hinit₂
  have hsourceEq : source₁ = source₂ := by
    have h := congrArg FeedbackStepState.seenSource hforcedEq
    simpa [forcedInitialState] using h
  have htargetEq : target₁ = target₂ := by
    have h := congrArg FeedbackStepState.seenTarget hforcedEq
    simpa [forcedInitialState] using h
  subst source₂
  subst target₂
  have hhistory : history₁ = history₂ :=
    history_eq_of_noFeedbackTies_of_same_cell sample hlam0 hlamHalf hties
      source₁ target₁ history₁ history₂ h₁ h₂
  subst history₂
  rfl

end FiniteSample

end OTSelector
