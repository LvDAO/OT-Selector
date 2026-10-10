import Mathlib.Data.Fintype.Card
import OTSelector.Feedback.ForcedHistory

/-!
# Finite length of a forced feedback history

This file records the purely finite combinatorics of a realized forced history.  A realized
label is not already seen, and a forced step inserts exactly that label into the corresponding
seen set.  Consequently a realized history is duplicate-free and has length at most `2 * n`.
No probability or measurability assumption is used here.
-/

namespace OTSelector

namespace FeedbackStepState

variable {n : ℕ}

/-! ## One-step seen-set bookkeeping -/

theorem labelStepRealizes_source_not_mem_seen
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n)
    (hreal : FiniteSample.labelStepRealizes sample lam state (Sum.inl i)) :
    i ∉ state.seenSource := by
  intro hi
  have hnew : i ∈ state.newSource sample lam := by
    rw [hreal.1]
    simp
  exact (Finset.disjoint_left.mp (state.newSource_disjoint_seenSource sample lam)) hnew hi

theorem labelStepRealizes_target_not_mem_seen
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n)
    (hreal : FiniteSample.labelStepRealizes sample lam state (Sum.inr j)) :
    j ∉ state.seenTarget := by
  intro hj
  have hnew : j ∈ state.newTarget sample lam := by
    rw [hreal.2]
    simp
  exact (Finset.disjoint_left.mp (state.newTarget_disjoint_seenTarget sample lam)) hnew hj

theorem forcedLabelStep_source_seenSource_eq_insert
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n) :
    (state.forcedLabelStep sample lam (Sum.inl i)).seenSource =
      insert i state.seenSource :=
  rfl

theorem forcedLabelStep_source_seenTarget_eq
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n) :
    (state.forcedLabelStep sample lam (Sum.inl i)).seenTarget = state.seenTarget :=
  rfl

theorem forcedLabelStep_target_seenSource_eq
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n) :
    (state.forcedLabelStep sample lam (Sum.inr j)).seenSource = state.seenSource :=
  rfl

theorem forcedLabelStep_target_seenTarget_eq_insert
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n) :
    (state.forcedLabelStep sample lam (Sum.inr j)).seenTarget =
      insert j state.seenTarget :=
  rfl

theorem seenSource_subset_forcedLabelStep
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (label : FeedbackLabel n) :
    state.seenSource ⊆ (state.forcedLabelStep sample lam label).seenSource := by
  cases label with
  | inl i =>
      rw [forcedLabelStep_source_seenSource_eq_insert]
      intro k hk
      exact Finset.mem_insert_of_mem hk
  | inr j =>
      rw [forcedLabelStep_target_seenSource_eq]

theorem seenTarget_subset_forcedLabelStep
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (label : FeedbackLabel n) :
    state.seenTarget ⊆ (state.forcedLabelStep sample lam label).seenTarget := by
  cases label with
  | inl i =>
      rw [forcedLabelStep_source_seenTarget_eq]
  | inr j =>
      rw [forcedLabelStep_target_seenTarget_eq_insert]
      intro k hk
      exact Finset.mem_insert_of_mem hk

theorem forcedLabelStep_source_mem_seenSource
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n) :
    i ∈ (state.forcedLabelStep sample lam (Sum.inl i)).seenSource := by
  rw [forcedLabelStep_source_seenSource_eq_insert]
  simp

theorem forcedLabelStep_target_mem_seenTarget
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n) :
    j ∈ (state.forcedLabelStep sample lam (Sum.inr j)).seenTarget := by
  rw [forcedLabelStep_target_seenTarget_eq_insert]
  simp

end FeedbackStepState

namespace FiniteSample

variable {n : ℕ}

/-! ## A realized tail cannot reuse a seen label -/

theorem ForcedHistoryRealizes.source_not_mem_of_seen
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (history : List (FeedbackLabel n)) (i : Fin n) :
    i ∈ state.seenSource →
      sample.ForcedHistoryRealizes lam state history →
        Sum.inl i ∉ history := by
  induction history generalizing state with
  | nil =>
      intro _ _ hmem
      simp at hmem
  | cons label history ih =>
      intro hi hgood hmem
      have hhead : label ≠ Sum.inl i := by
        intro hlabel
        subst label
        exact (state.labelStepRealizes_source_not_mem_seen sample lam i hgood.1) hi
      have hiNext : i ∈
          (state.forcedLabelStep sample lam label).seenSource := by
        exact (state.seenSource_subset_forcedLabelStep sample lam label) hi
      have htail := ih (state := state.forcedLabelStep sample lam label)
        hiNext hgood.2
      have hmemTail : Sum.inl i ∈ history := by
        rcases List.mem_cons.mp hmem with hlabel | htailmem
        · exact False.elim (hhead hlabel.symm)
        · exact htailmem
      exact htail hmemTail

theorem ForcedHistoryRealizes.target_not_mem_of_seen
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (history : List (FeedbackLabel n)) (j : Fin n) :
    j ∈ state.seenTarget →
      sample.ForcedHistoryRealizes lam state history →
        Sum.inr j ∉ history := by
  induction history generalizing state with
  | nil =>
      intro _ _ hmem
      simp at hmem
  | cons label history ih =>
      intro hj hgood hmem
      have hhead : label ≠ Sum.inr j := by
        intro hlabel
        subst label
        exact (state.labelStepRealizes_target_not_mem_seen sample lam j hgood.1) hj
      have hjNext : j ∈
          (state.forcedLabelStep sample lam label).seenTarget := by
        exact (state.seenTarget_subset_forcedLabelStep sample lam label) hj
      have htail := ih (state := state.forcedLabelStep sample lam label)
        hjNext hgood.2
      have hmemTail : Sum.inr j ∈ history := by
        rcases List.mem_cons.mp hmem with hlabel | htailmem
        · exact False.elim (hhead hlabel.symm)
        · exact htailmem
      exact htail hmemTail

/-! ## No duplicates and the cardinality bound -/

theorem ForcedHistoryRealizes.nodup
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (history : List (FeedbackLabel n))
    (hgood : sample.ForcedHistoryRealizes lam state history) :
    history.Nodup := by
  induction history generalizing state with
  | nil =>
      simp
  | cons label history ih =>
      apply List.nodup_cons.mpr
      constructor
      · cases label with
        | inl i =>
            exact ForcedHistoryRealizes.source_not_mem_of_seen sample lam
              (state.forcedLabelStep sample lam (Sum.inl i)) history i
              (state.forcedLabelStep_source_mem_seenSource sample lam i) hgood.2
        | inr j =>
            exact ForcedHistoryRealizes.target_not_mem_of_seen sample lam
              (state.forcedLabelStep sample lam (Sum.inr j)) history j
              (state.forcedLabelStep_target_mem_seenTarget sample lam j) hgood.2
      · exact ih (state := state.forcedLabelStep sample lam label) hgood.2

theorem ForcedHistoryRealizes.length_le_two_mul
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (history : List (FeedbackLabel n))
    (hgood : sample.ForcedHistoryRealizes lam state history) :
    history.length ≤ 2 * n := by
  have hlength : history.length ≤ Fintype.card (FeedbackLabel n) :=
    (ForcedHistoryRealizes.nodup sample lam state history hgood).length_le_card
  simpa [FeedbackLabel, two_mul] using hlength

end FiniteSample

end OTSelector
