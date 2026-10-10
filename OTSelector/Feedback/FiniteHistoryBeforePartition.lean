import OTSelector.Feedback.FeedbackEventTimeNull
import OTSelector.Feedback.FiniteHistoryBefore
import OTSelector.Feedback.FiniteHistoryDisjoint

/-!
# Finite partition by strict pre-event histories

At a deterministic coordinate strictly to the right of the initial point, the no-tie and
frontier-null events leave exactly one strict finite-history cell.  This is the partition used
when the predictable compensator is computed by Fubini over the finitely many forced histories.

The result is an almost-everywhere partition under the canonical finite-sample law.  It does not
assert a compensator or an adaptive independence statement.
-/

open MeasureTheory Set
open scoped BigOperators

namespace OTSelector

variable {n : ℕ}

/-- The strict pre-event cell represented by a finite history index. -/
def historyBeforeCell (index : HistoryCellIndex n) (lam x0 p0 x : ℝ) :
    Set (FiniteSample n) :=
  {sample |
    HistoryBeforeCoordinate sample lam x0 p0 index.sourcePattern index.targetPattern
      index.history x}

theorem measurableSet_historyBeforeCell
    (index : HistoryCellIndex n) (lam x0 p0 x : ℝ) :
    MeasurableSet (historyBeforeCell index lam x0 p0 x) := by
  exact measurableSet_historyBeforeCoordinate lam x0 p0 index.sourcePattern
    index.targetPattern index.history x

namespace FiniteSample

/-- Every no-tie sample with no event at `x` belongs to a strict pre-event history cell. -/
theorem exists_historyBeforeCellIndex
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hNoEvent : sample.NoFeedbackEventAt lam x0 p0 x) :
    ∃ index : HistoryCellIndex n, sample ∈ historyBeforeCell index lam x0 p0 x := by
  obtain ⟨history, hbefore, hlength⟩ :=
    sample.exists_historyBeforeCoordinate_of_noFeedbackTies_of_noFeedbackEventAt
      hlam0 hlamHalf hx0x hNoTie hNoEvent
  let index : HistoryCellIndex n :=
    { sourcePattern := sample.initialSeenSource x0 p0
      targetPattern := sample.initialSeenTarget x0 p0
      history := history
      history_length_le := hlength }
  exact ⟨index, hbefore⟩

/-- Strict pre-event cells have unique indices. -/
theorem historyBeforeCellIndex_eq_of_mem
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (index₁ index₂ : HistoryCellIndex n)
    (h₁ : sample ∈ historyBeforeCell index₁ lam x0 p0 x)
    (h₂ : sample ∈ historyBeforeCell index₂ lam x0 p0 x) :
    index₁ = index₂ := by
  have hties : sample.NoFeedbackTies lam x0 p0 := h₁.2
  apply historyCellIndex_eq_of_mem_of_noFeedbackTies sample hlam0 hlamHalf hties
  · exact historyBeforeCoordinate_imp_historyAtCoordinate sample hlam0 hlamHalf h₁
  · exact historyBeforeCoordinate_imp_historyAtCoordinate sample hlam0 hlamHalf h₂

end FiniteSample

/-- Distinct strict history indices define disjoint cells. -/
theorem disjoint_historyBeforeCell_of_ne
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {index₁ index₂ : HistoryCellIndex n} (hne : index₁ ≠ index₂) :
    Disjoint (historyBeforeCell index₁ lam x0 p0 x)
      (historyBeforeCell index₂ lam x0 p0 x) := by
  rw [Set.disjoint_left]
  intro sample h₁ h₂
  exact hne (sample.historyBeforeCellIndex_eq_of_mem hlam0 hlamHalf index₁ index₂ h₁ h₂)

/-- At a deterministic non-initial coordinate, the strict history cells cover almost every
finite sample. -/
theorem exists_historyBeforeCellIndex_ae
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 < x) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      ∃ index : HistoryCellIndex n, sample ∈ historyBeforeCell index lam x0 p0 x := by
  filter_upwards [FiniteSample.finiteSampleLaw_noFeedbackTies_ae
      (n := n) (x0 := x0) (p0 := p0)
      hlam0 hlamHalf,
    FiniteSample.noFeedbackEventAt_ae (n := n) (p0 := p0) hlam0 hlamHalf hx0x] with
      sample hties hnoEvent
  exact sample.exists_historyBeforeCellIndex hlam0 hlamHalf hx0x hties hnoEvent

/-- At a deterministic non-event coordinate, the strict and right-continuous versions of a
fixed history cell agree almost everywhere. -/
theorem historyBeforeCell_ae_eq_historyCell
    (index : HistoryCellIndex n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x) :
    historyBeforeCell index lam x0 p0 x =ᵐ[
        (finiteSampleLaw n : Measure (FiniteSample n))]
      historyCell index lam x0 p0 x := by
  filter_upwards [FiniteSample.finiteSampleLaw_noFeedbackTies_ae
      (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf,
    FiniteSample.noFeedbackEventAt_ae (n := n) (p0 := p0) hlam0 hlamHalf hx0x] with
      sample hties hnoEvent
  apply propext
  constructor
  · intro hbefore
    exact historyBeforeCoordinate_imp_historyAtCoordinate sample hlam0 hlamHalf hbefore
  · intro hcell
    obtain ⟨strictIndex, hstrict⟩ :=
      sample.exists_historyBeforeCellIndex hlam0 hlamHalf hx0x hties hnoEvent
    have hstrictAt : sample ∈ historyCell strictIndex lam x0 p0 x :=
      historyBeforeCoordinate_imp_historyAtCoordinate sample hlam0 hlamHalf hstrict
    have hEq := sample.historyCellIndex_eq_of_mem_of_noFeedbackTies
      hlam0 hlamHalf hties strictIndex index hstrictAt hcell
    change sample ∈ historyBeforeCell index lam x0 p0 x
    rw [← hEq]
    exact hstrict

/-- The finite sum of strict-cell indicators is one almost everywhere. -/
theorem sum_historyBeforeCell_indicator_one_ae
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 < x) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      (∑ index : HistoryCellIndex n,
        (historyBeforeCell index lam x0 p0 x).indicator (fun _ ↦ (1 : ℝ)) sample) = 1 := by
  filter_upwards [exists_historyBeforeCellIndex_ae
      (n := n) (p0 := p0) hlam0 hlamHalf hx0x] with
      sample hcover
  obtain ⟨index, hindex⟩ := hcover
  classical
  rw [Fintype.sum_eq_single index]
  · simp [hindex]
  · intro other hne
    have hnot : sample ∉ historyBeforeCell other lam x0 p0 x := by
      intro hother
      exact hne (sample.historyBeforeCellIndex_eq_of_mem
        hlam0 hlamHalf other index hother hindex)
    simp [hnot]

end OTSelector
