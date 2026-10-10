import OTSelector.Feedback.FiniteHistoryCoverage
import Mathlib.Data.Set.Finite.List

/-!
# Finite history-cell index set

The history-coordinate cells used by the deterministic coverage theorem are indexed by two
initial seen patterns and a genuinely bounded feedback-label list.  The index type is finite; no
probability or disjointness assertion is made here.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

/-- A finite coordinate for a prescribed feedback history cell. -/
structure HistoryCellIndex (n : ℕ) where
  sourcePattern : Finset (Fin n)
  targetPattern : Finset (Fin n)
  history : List (FeedbackLabel n)
  history_length_le : history.length ≤ 2 * n

private noncomputable instance boundedHistoryFintype (n : ℕ) :
    Fintype {history : List (FeedbackLabel n) // history.length ≤ 2 * n} :=
  (List.finite_length_le (FeedbackLabel n) (2 * n)).fintype

/-- The coordinate type is finite because both patterns and the bounded history are finite. -/
instance : Finite (HistoryCellIndex n) := by
  let f : HistoryCellIndex n →
      Finset (Fin n) × Finset (Fin n) ×
        {history : List (FeedbackLabel n) // history.length ≤ 2 * n} :=
    fun index ↦ (index.sourcePattern, index.targetPattern,
      ⟨index.history, index.history_length_le⟩)
  exact Finite.of_injective f (by
    intro index₁ index₂ h
    cases index₁ with
    | mk source₁ target₁ history₁ length₁ =>
        cases index₂ with
        | mk source₂ target₂ history₂ length₂ =>
            cases h
            rfl)

/-- A noncomputable enumeration of all finite history-cell coordinates. -/
noncomputable instance historyCellIndexFintype (n : ℕ) : Fintype (HistoryCellIndex n) :=
  Fintype.ofFinite _

/-- The finite set of all history-cell coordinates. -/
noncomputable def allHistoryCellIndices (n : ℕ) : Finset (HistoryCellIndex n) := Finset.univ

@[simp]
theorem mem_allHistoryCellIndices (index : HistoryCellIndex n) :
    index ∈ allHistoryCellIndices n := by
  simp [allHistoryCellIndices]

/-- The measurable sample event represented by one finite history-cell coordinate. -/
def historyCell (index : HistoryCellIndex n) (lam x0 p0 x : ℝ) : Set (FiniteSample n) :=
  {sample |
    HistoryAtCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern index.history x}

theorem measurableSet_historyCell (index : HistoryCellIndex n) (lam x0 p0 x : ℝ) :
    MeasurableSet (historyCell index lam x0 p0 x) := by
  exact measurableSet_historyAtCoordinate lam x0 p0 index.sourcePattern index.targetPattern
    index.history x

/-! ## Coverage -/

namespace FiniteSample

/-- Every no-tie sample belongs to a cell indexed by `HistoryCellIndex n`. -/
theorem exists_historyCellIndex_of_noFeedbackTies
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    ∃ index : HistoryCellIndex n, sample ∈ historyCell index lam x0 p0 x := by
  obtain ⟨history, hcell, hlen⟩ := sample.exists_historyAtCoordinate_of_noFeedbackTies
    hlam0 hlamHalf hx0x hNoTie
  let index : HistoryCellIndex n :=
    { sourcePattern := sample.initialSeenSource x0 p0
      targetPattern := sample.initialSeenTarget x0 p0
      history := history
      history_length_le := hlen }
  exact ⟨index, hcell⟩

/-- Coverage with the explicit finite enumeration of coordinates. -/
theorem exists_mem_allHistoryCellIndices_of_noFeedbackTies
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    ∃ index : HistoryCellIndex n,
      index ∈ allHistoryCellIndices n ∧ sample ∈ historyCell index lam x0 p0 x := by
  obtain ⟨index, hcell⟩ := sample.exists_historyCellIndex_of_noFeedbackTies
    hlam0 hlamHalf hx0x hNoTie
  exact ⟨index, mem_allHistoryCellIndices index, hcell⟩

end FiniteSample

end OTSelector
