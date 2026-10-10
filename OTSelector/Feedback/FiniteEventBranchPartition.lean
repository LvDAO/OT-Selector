import OTSelector.Feedback.FiniteEventHistorySum
import OTSelector.Feedback.FiniteHistoryPartition

/-!
# Branch partition at a fixed recursive step

For a no-tie sample, a realized forced history of a fixed length is unique, including its initial
seen patterns.  Consequently the source and target labels introduced at a fixed recursive step
can be written as a finite sum over `HistoryCellIndex`.  The branch indicator is explicit and the
cardinality on a realized branch is read from its scheduled state.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## One-step no-tie uniqueness -/

private theorem label_eq_of_noFeedbackTies_at_state
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    {m : ℕ} (_hm : m ≤ 2 * n) (state : FeedbackStepState n)
    (hstate : feedbackState sample lam x0 p0 m = state)
    {label₁ label₂ : FeedbackLabel n}
    (hlabel₁ : labelStepRealizes sample lam state label₁)
    (hlabel₂ : labelStepRealizes sample lam state label₂) :
    label₁ = label₂ := by
  have hm_lt : m < 2 * n := by
    by_contra hnot
    have hge : 2 * n ≤ m := Nat.le_of_not_gt hnot
    have hstable : feedbackState sample lam x0 p0 m =
        feedbackState sample lam x0 p0 (2 * n) := by
      have h := sample.feedbackState_eq_of_candidates_eq_empty lam x0 p0 (2 * n)
        (sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0) (m - 2 * n)
      simpa [Nat.add_sub_of_le hge] using h
    have hcand : state.candidates sample lam = ∅ := by
      rw [← hstate, hstable]
      exact sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0
    cases label₁ with
    | inl i =>
        have hne : state.newSource sample lam ≠ ∅ := by
          rw [hlabel₁.1]
          simp
        exact hne (sample.newSource_eq_empty_of_candidates_eq_empty lam state hcand)
    | inr j =>
        have hne : state.newTarget sample lam ≠ ∅ := by
          rw [hlabel₁.2]
          simp
        exact hne (sample.newTarget_eq_empty_of_candidates_eq_empty lam state hcand)
  have hupper := hNoTie m hm_lt
  rw [hstate] at hupper
  cases label₁ with
  | inl i =>
      cases label₂ with
      | inl j =>
          have hsingleton : ({i} : Finset (Fin n)) = {j} :=
            hlabel₁.1.symm.trans hlabel₂.1
          simpa using hsingleton
      | inr j =>
          have hsource : (state.newSource sample lam).card = 1 := by
            rw [hlabel₁.1]
            simp
          have htarget : (state.newTarget sample lam).card = 1 := by
            rw [hlabel₂.2]
            simp
          omega
  | inr i =>
      cases label₂ with
      | inl j =>
          have htarget : (state.newTarget sample lam).card = 1 := by
            rw [hlabel₁.2]
            simp
          have hsource : (state.newSource sample lam).card = 1 := by
            rw [hlabel₂.1]
            simp
          omega
      | inr j =>
          have hsingleton : ({i} : Finset (Fin n)) = {j} :=
            hlabel₁.2.symm.trans hlabel₂.2
          simpa using hsingleton

/-! ## Uniqueness of same-length realized forced histories -/

private theorem forced_history_eq_of_noFeedbackTies_from_state_same_length
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    {m : ℕ} (hm : m ≤ 2 * n) (state : FeedbackStepState n)
    (hstate : feedbackState sample lam x0 p0 m = state)
    {history₁ history₂ : List (FeedbackLabel n)}
    (hlen : history₁.length = history₂.length)
    (hgood₁ : ForcedHistoryRealizes sample lam state history₁)
    (hgood₂ : ForcedHistoryRealizes sample lam state history₂) :
    history₁ = history₂ := by
  induction history₁ generalizing history₂ m state with
  | nil =>
      cases history₂ with
      | nil => rfl
      | cons label₂ tail₂ => simp at hlen
  | cons label₁ tail₁ ih =>
      cases history₂ with
      | nil => simp at hlen
      | cons label₂ tail₂ =>
          have hlabel₁ := hgood₁.1
          have hlabel₂ := hgood₂.1
          have hm_lt : m < 2 * n := by
            by_contra hnot
            have hge : 2 * n ≤ m := Nat.le_of_not_gt hnot
            have hstable : feedbackState sample lam x0 p0 m =
                feedbackState sample lam x0 p0 (2 * n) := by
              have h := sample.feedbackState_eq_of_candidates_eq_empty lam x0 p0 (2 * n)
                (sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0) (m - 2 * n)
              simpa [Nat.add_sub_of_le hge] using h
            have hcand : state.candidates sample lam = ∅ := by
              rw [← hstate, hstable]
              exact sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0
            cases label₁ with
            | inl i =>
                have hne : state.newSource sample lam ≠ ∅ := by
                  rw [hlabel₁.1]
                  simp
                exact hne (sample.newSource_eq_empty_of_candidates_eq_empty lam state hcand)
            | inr j =>
                have hne : state.newTarget sample lam ≠ ∅ := by
                  rw [hlabel₁.2]
                  simp
                exact hne (sample.newTarget_eq_empty_of_candidates_eq_empty lam state hcand)
          have hlabel : label₁ = label₂ :=
            label_eq_of_noFeedbackTies_at_state sample lam x0 p0 hNoTie hm state hstate
              hlabel₁ hlabel₂
          subst label₂
          have hstep : state.step sample lam =
              state.forcedLabelStep sample lam label₁ := by
            cases label₁ with
            | inl i =>
                exact step_eq_forcedLabelStep_of_source_singleton sample lam state i
                  hlabel₁.1 hlabel₁.2
            | inr j =>
                exact step_eq_forcedLabelStep_of_target_singleton sample lam state j
                  hlabel₁.1 hlabel₁.2
          have hstate' : feedbackState sample lam x0 p0 (m + 1) =
              state.forcedLabelStep sample lam label₁ := by
            rw [feedbackState_succ, hstate, hstep]
          have htail := ih (history₂ := tail₂) (m := m + 1)
            (state := state.forcedLabelStep sample lam label₁)
            (hm := by omega) (hstate := hstate')
            (hlen := by simpa using hlen) hgood₁.2 hgood₂.2
          simp [htail]

/-! ## Unique `HistoryCellIndex` at a fixed step -/

theorem historyCellIndex_eq_of_noFeedbackTies_of_realized_step
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (m : Fin (2 * n)) (index₁ index₂ : HistoryCellIndex n)
    (h₁ : index₁.history.length = m.val ∧
      HistoryBranch sample lam x0 p0 index₁.sourcePattern index₁.targetPattern index₁.history)
    (h₂ : index₂.history.length = m.val ∧
      HistoryBranch sample lam x0 p0 index₂.sourcePattern index₂.targetPattern index₂.history) :
    index₁ = index₂ := by
  rcases index₁ with ⟨source₁, target₁, history₁, hbound₁⟩
  rcases index₂ with ⟨source₂, target₂, history₂, hbound₂⟩
  change history₁.length = m.val ∧
      HistoryBranch sample lam x0 p0 source₁ target₁ history₁ at h₁
  change history₂.length = m.val ∧
      HistoryBranch sample lam x0 p0 source₂ target₂ history₂ at h₂
  have hinit_eq : forcedInitialState x0 p0 source₁ target₁ =
      forcedInitialState x0 p0 source₂ target₂ :=
    h₁.2.1.symm.trans h₂.2.1
  have hsource_eq : source₁ = source₂ := by
    have hseen := congrArg FeedbackStepState.seenSource hinit_eq
    simpa [forcedInitialState] using hseen
  have htarget_eq : target₁ = target₂ := by
    have hseen := congrArg FeedbackStepState.seenTarget hinit_eq
    simpa [forcedInitialState] using hseen
  subst source₂
  subst target₂
  have hstate0 : feedbackState sample lam x0 p0 0 =
      forcedInitialState x0 p0 source₁ target₁ := by
    simpa [feedbackState_zero] using h₁.2.1
  have hhistory : history₁ = history₂ :=
    forced_history_eq_of_noFeedbackTies_from_state_same_length sample lam x0 p0 hNoTie
      (m := 0) (hm := by omega) (state := forcedInitialState x0 p0 source₁ target₁)
      hstate0 (by simp [h₁.1, h₂.1])
      h₁.2.2 h₂.2.2
  subst history₂
  rfl

private theorem scheduledState_newSource_card_eq_feedbackState_card_of_realized_step
    (sample : FiniteSample n) (lam x0 p0 : ℝ) (m : Fin (2 * n))
    (index : HistoryCellIndex n)
    (hindex : index.history.length = m.val ∧
      HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history) :
    ((sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history).newSource
        sample lam).card =
      ((feedbackState sample lam x0 p0 m.val).newSource sample lam).card := by
  have hstate := sample.feedbackState_eq_scheduledState_of_history
    lam x0 p0 index.sourcePattern index.targetPattern index.history
    hindex.2.1 hindex.2.2
  have hstate' : feedbackState sample lam x0 p0 m.val =
      sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history := by
    simpa [hindex.1] using hstate
  exact congrArg (fun state : FeedbackStepState n =>
    (state.newSource sample lam).card) hstate'.symm

private theorem scheduledState_newTarget_card_eq_feedbackState_card_of_realized_step
    (sample : FiniteSample n) (lam x0 p0 : ℝ) (m : Fin (2 * n))
    (index : HistoryCellIndex n)
    (hindex : index.history.length = m.val ∧
      HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history) :
    ((sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history).newTarget
        sample lam).card =
      ((feedbackState sample lam x0 p0 m.val).newTarget sample lam).card := by
  have hstate := sample.feedbackState_eq_scheduledState_of_history
    lam x0 p0 index.sourcePattern index.targetPattern index.history
    hindex.2.1 hindex.2.2
  have hstate' : feedbackState sample lam x0 p0 m.val =
      sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history := by
    simpa [hindex.1] using hstate
  exact congrArg (fun state : FeedbackStepState n =>
    (state.newTarget sample lam).card) hstate'.symm

/-! ## Source and target cardinality sums -/

theorem feedbackState_newSource_card_eq_sum_historyCellIndex_branch
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n)) :
    ((feedbackState sample lam x0 p0 m.val).newSource sample lam).card =
      ∑ index : HistoryCellIndex n, if
        index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history then
        ((sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history).newSource
          sample lam).card
      else 0 := by
  classical
  by_cases hsource :
      ((feedbackState sample lam x0 p0 m.val).newSource sample lam).Nonempty
  · obtain ⟨i, hi⟩ := hsource
    have hcand := sample.candidates_nonempty_of_mem_newSource lam
      (feedbackState sample lam x0 p0 m.val) i hi
    obtain ⟨history, hlen, hbranch, hstate⟩ :=
      sample.exists_historyBranch_of_noFeedbackTies_of_active lam x0 p0 (m := m.val) m.isLt
        hNoTie hcand
    let index : HistoryCellIndex n :=
      { sourcePattern := sample.initialSeenSource x0 p0
        targetPattern := sample.initialSeenTarget x0 p0
        history := history
        history_length_le := by omega }
    have hindex : index.history.length = m.val ∧
        HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history := by
      exact ⟨by simpa [index] using hlen, by simpa [index] using hbranch⟩
    have hcard := scheduledState_newSource_card_eq_feedbackState_card_of_realized_step
      sample lam x0 p0 m index hindex
    rw [Fintype.sum_eq_single index]
    · simp [hindex, hcard]
    · intro other hne
      have hnot : ¬ (other.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 other.sourcePattern other.targetPattern other.history) := by
        intro hother
        exact hne (historyCellIndex_eq_of_noFeedbackTies_of_realized_step
          sample lam x0 p0 hNoTie m other index hother hindex)
      simp [hnot]
  · have hsource_empty : (feedbackState sample lam x0 p0 m.val).newSource sample lam = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hsource
    rw [hsource_empty, Finset.card_empty]
    symm
    apply Fintype.sum_eq_zero
    intro index
    by_cases hindex : index.history.length = m.val ∧
        HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
    · have hcard := scheduledState_newSource_card_eq_feedbackState_card_of_realized_step
        sample lam x0 p0 m index hindex
      simp [hindex, hcard, hsource_empty]
    · simp [hindex]

theorem feedbackState_newTarget_card_eq_sum_historyCellIndex_branch
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) (m : Fin (2 * n)) :
    ((feedbackState sample lam x0 p0 m.val).newTarget sample lam).card =
      ∑ index : HistoryCellIndex n, if
        index.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history then
        ((sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern index.history).newTarget
          sample lam).card
      else 0 := by
  classical
  by_cases htarget :
      ((feedbackState sample lam x0 p0 m.val).newTarget sample lam).Nonempty
  · obtain ⟨j, hj⟩ := htarget
    have hcand := sample.candidates_nonempty_of_mem_newTarget lam
      (feedbackState sample lam x0 p0 m.val) j hj
    obtain ⟨history, hlen, hbranch, hstate⟩ :=
      sample.exists_historyBranch_of_noFeedbackTies_of_active lam x0 p0 (m := m.val) m.isLt
        hNoTie hcand
    let index : HistoryCellIndex n :=
      { sourcePattern := sample.initialSeenSource x0 p0
        targetPattern := sample.initialSeenTarget x0 p0
        history := history
        history_length_le := by omega }
    have hindex : index.history.length = m.val ∧
        HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history := by
      exact ⟨by simpa [index] using hlen, by simpa [index] using hbranch⟩
    have hcard := scheduledState_newTarget_card_eq_feedbackState_card_of_realized_step
      sample lam x0 p0 m index hindex
    rw [Fintype.sum_eq_single index]
    · simp [hindex, hcard]
    · intro other hne
      have hnot : ¬ (other.history.length = m.val ∧
          HistoryBranch sample lam x0 p0 other.sourcePattern other.targetPattern other.history) := by
        intro hother
        exact hne (historyCellIndex_eq_of_noFeedbackTies_of_realized_step
          sample lam x0 p0 hNoTie m other index hother hindex)
      simp [hnot]
  · have htarget_empty : (feedbackState sample lam x0 p0 m.val).newTarget sample lam = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp htarget
    rw [htarget_empty, Finset.card_empty]
    symm
    apply Fintype.sum_eq_zero
    intro index
    by_cases hindex : index.history.length = m.val ∧
        HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
    · have hcard := scheduledState_newTarget_card_eq_feedbackState_card_of_realized_step
        sample lam x0 p0 m index hindex
      simp [hindex, hcard, htarget_empty]
    · simp [hindex]

end FiniteSample

end OTSelector
