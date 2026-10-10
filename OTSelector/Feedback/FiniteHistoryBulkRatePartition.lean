import OTSelector.Feedback.FiniteHistoryTerminalRate

/-!
# Finite strict-history partition of the bulk rates

At a deterministic coordinate strictly to the right of the initial point, exactly one strict
history cell is realized almost surely.  Histories of length below `2 * n` are indexed once by
`Fin (2 * n)`; a realized history of length exactly `2 * n` is omitted from that outer index but
has zero source and target rate.  These facts give the finite rate partitions used in the raw
predictable-rectangle calculation.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

/-- A generic strict-cell partition for a function that vanishes on every realized terminal
history. -/
theorem sum_step_historyBeforeCell_indicator_ae_of_terminal_zero
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 < x) (f : FiniteSample n → ℝ)
    (hterminal : ∀ (index : HistoryCellIndex n) (sample : FiniteSample n),
      sample ∈ historyBeforeCell index lam x0 p0 x →
        ¬index.history.length < 2 * n → f sample = 0) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          (historyBeforeCell index lam x0 p0 x).indicator f sample
        else 0) = f sample := by
  filter_upwards [exists_historyBeforeCellIndex_ae
      (n := n) (p0 := p0) hlam0 hlamHalf hx0x] with sample hcover
  obtain ⟨chosen, hchosen⟩ := hcover
  classical
  by_cases hlength : chosen.history.length < 2 * n
  · let chosenStep : Fin (2 * n) := ⟨chosen.history.length, hlength⟩
    rw [Fintype.sum_eq_single chosenStep]
    · rw [Fintype.sum_eq_single chosen]
      · simp [chosenStep, hchosen]
      · intro other hne
        have hnot : sample ∉ historyBeforeCell other lam x0 p0 x := by
          intro hother
          exact hne (sample.historyBeforeCellIndex_eq_of_mem
            hlam0 hlamHalf other chosen hother hchosen)
        simp [hnot]
    · intro otherStep hne
      apply Fintype.sum_eq_zero
      intro index
      by_cases hindexLength : index.history.length = otherStep.val
      · have hnot : sample ∉ historyBeforeCell index lam x0 p0 x := by
          intro hindex
          have hindexEq := sample.historyBeforeCellIndex_eq_of_mem
            hlam0 hlamHalf index chosen hindex hchosen
          subst index
          apply hne
          apply Fin.ext
          simpa [chosenStep] using hindexLength.symm
        simp [hindexLength, hnot]
      · simp [hindexLength]
  · have hf : f sample = 0 := hterminal chosen sample hchosen hlength
    rw [hf]
    apply Fintype.sum_eq_zero
    intro step
    apply Fintype.sum_eq_zero
    intro index
    by_cases hindexLength : index.history.length = step.val
    · have hnot : sample ∉ historyBeforeCell index lam x0 p0 x := by
        intro hindex
        have hindexEq := sample.historyBeforeCellIndex_eq_of_mem
          hlam0 hlamHalf index chosen hindex hchosen
        subst index
        apply hlength
        rw [hindexLength]
        exact step.isLt
      simp [hindexLength, hnot]
    · simp [hindexLength]

/-- The source safe bulk rate is the finite sum of its strict nonterminal history-cell pieces. -/
theorem sum_step_historyBeforeCell_sourceBulkRate_ae
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (u : ℝ≥0) (hu : 0 < u) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          (historyBeforeCell index lam x0 p0
            (FiniteSample.elapsedFeedbackCoordinate x0 u)).indicator
              (fun sample ↦ safeSourceBulkRate
                hlam0 hlamHalf B x0 p0 u sample) sample
        else 0) = safeSourceBulkRate hlam0 hlamHalf B x0 p0 u sample := by
  have hx0x : x0 < FiniteSample.elapsedFeedbackCoordinate x0 u := by
    simp only [FiniteSample.elapsedFeedbackCoordinate]
    exact lt_add_of_pos_right x0 (by exact_mod_cast hu)
  apply sum_step_historyBeforeCell_indicator_ae_of_terminal_zero
    hlam0 hlamHalf hx0x
  intro index sample hcell hterminal
  exact safeSourceBulkRate_eq_zero_of_historyBeforeCell_not_lt
    index sample hlam0 hlamHalf hx0x hcell hterminal u rfl

/-- The target safe bulk rate is the finite sum of its strict nonterminal history-cell pieces. -/
theorem sum_step_historyBeforeCell_targetBulkRate_ae
    {lam B x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (u : ℝ≥0) (hu : 0 < u) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          (historyBeforeCell index lam x0 p0
            (FiniteSample.elapsedFeedbackCoordinate x0 u)).indicator
              (fun sample ↦ safeTargetBulkRate
                hlam0 hlamHalf B x0 p0 u sample) sample
        else 0) = safeTargetBulkRate hlam0 hlamHalf B x0 p0 u sample := by
  have hx0x : x0 < FiniteSample.elapsedFeedbackCoordinate x0 u := by
    simp only [FiniteSample.elapsedFeedbackCoordinate]
    exact lt_add_of_pos_right x0 (by exact_mod_cast hu)
  apply sum_step_historyBeforeCell_indicator_ae_of_terminal_zero
    hlam0 hlamHalf hx0x
  intro index sample hcell hterminal
  exact safeTargetBulkRate_eq_zero_of_historyBeforeCell_not_lt
    index sample hlam0 hlamHalf hx0x hcell hterminal u rfl

end OTSelector
