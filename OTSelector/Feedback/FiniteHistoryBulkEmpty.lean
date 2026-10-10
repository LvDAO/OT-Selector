import OTSelector.Feedback.FiniteHistoryBulkNextEvent

/-!
# Empty clipped bulk sections

The clipped bulk interval is an ordinary half-open interval.  When its right endpoint is below
its left endpoint, the corresponding bulk-thinned next-event section is literally empty.  These
lemmas keep that branch separate from oriented `intervalIntegral` notation: no negative interval
is interpreted as a probability mass.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace OTSelector

variable {n : ℕ}

theorem Ioc_feedbackBranchBulkStart_stop_eq_empty_of_stop_lt_start
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (hstop : feedbackBranchBulkStop B lam state t <
      feedbackBranchBulkStart B lam state s) :
    Ioc (feedbackBranchBulkStart B lam state s)
        (feedbackBranchBulkStop B lam state t) = ∅ := by
  exact Ioc_eq_empty (not_lt.mpr (le_of_lt hstop))

theorem feedbackBulkNextEventSet_eq_empty_of_stop_lt_start
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hstop : feedbackBranchBulkStop B lam state t <
      feedbackBranchBulkStart B lam state s) :
    feedbackBulkNextEventSet B lam state s t S label = ∅ := by
  ext unseen
  constructor
  · intro hunseen
    rcases hunseen with ⟨⟨hrect, hnext⟩, hbulk⟩
    let y := feedbackLabelFixedStateCrossing n lam state label (unseen label)
    have hstate : state.x < y := by
      exact (mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
        state lam label (unseen label) state.x hlam0 hlamHalf).1
        ((mem_feedbackUnseenRectangularSetAt_iff lam state state.x S unseen).1 hrect label)
    have hst : s < y := hnext.1.1
    have hybulk := (feedbackBulkRegion_state_iff_mem_Icc state hB).1 hbulk
    have hstart : feedbackBranchBulkStart B lam state s ≤ y := by
      unfold feedbackBranchBulkStart feedbackBulkNextStart
      exact max_le hstate.le (max_le hst.le hybulk.1)
    have hstop' : y ≤ feedbackBranchBulkStop B lam state t := by
      unfold feedbackBranchBulkStop feedbackBulkNextStop
      exact le_min hnext.1.2 hybulk.2
    exact False.elim ((not_lt_of_ge (hstart.trans hstop')) hstop)
  · intro hunseen
    simp at hunseen

theorem feedbackBulkNextEventSetOfLabel_eq_empty_of_stop_lt_start
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hstop : feedbackBranchBulkStop B lam state t <
      feedbackBranchBulkStart B lam state s) :
    feedbackBulkNextEventSetOfLabel B lam state s t S label = ∅ := by
  classical
  unfold feedbackBulkNextEventSetOfLabel
  split_ifs with hlabel
  · exact feedbackBulkNextEventSet_eq_empty_of_stop_lt_start
      B lam state s t S ⟨label, hlabel⟩ hB hlam0 hlamHalf hstop
  · rfl

theorem feedbackUnseenTupleLaw_real_feedbackBulkNextEventSet_eq_zero_of_stop_lt_start
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hstop : feedbackBranchBulkStop B lam state t <
      feedbackBranchBulkStart B lam state s) :
    (feedbackUnseenTupleLaw S).real
        (feedbackBulkNextEventSet B lam state s t S label) = 0 := by
  rw [feedbackBulkNextEventSet_eq_empty_of_stop_lt_start
    B lam state s t S label hB hlam0 hlamHalf hstop]
  simp

theorem feedbackUnseenTupleLaw_real_feedbackBulkNextEventSetOfLabel_eq_zero_of_stop_lt_start
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hstop : feedbackBranchBulkStop B lam state t <
      feedbackBranchBulkStart B lam state s) :
    (feedbackUnseenTupleLaw S).real
        (feedbackBulkNextEventSetOfLabel B lam state s t S label) = 0 := by
  rw [feedbackBulkNextEventSetOfLabel_eq_empty_of_stop_lt_start
    B lam state s t S label hB hlam0 hlamHalf hstop]
  simp

theorem sum_feedbackUnseenTupleLaw_real_sourceBulkNextEventSetOfLabel_eq_zero_of_stop_lt_start
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n))
    (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hstop : feedbackBranchBulkStop B lam state t <
      feedbackBranchBulkStart B lam state s) :
    ∑ label ∈ feedbackUnseenSourceLabels S,
        (feedbackUnseenTupleLaw S).real
          (feedbackBulkNextEventSetOfLabel B lam state s t S label) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro label hlabel
  exact feedbackUnseenTupleLaw_real_feedbackBulkNextEventSetOfLabel_eq_zero_of_stop_lt_start
    B lam state s t S label hB hlam0 hlamHalf hstop

theorem sum_feedbackUnseenTupleLaw_real_targetBulkNextEventSetOfLabel_eq_zero_of_stop_lt_start
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n))
    (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hstop : feedbackBranchBulkStop B lam state t <
      feedbackBranchBulkStart B lam state s) :
    ∑ label ∈ feedbackUnseenTargetLabels S,
        (feedbackUnseenTupleLaw S).real
          (feedbackBulkNextEventSetOfLabel B lam state s t S label) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro label hlabel
  exact feedbackUnseenTupleLaw_real_feedbackBulkNextEventSetOfLabel_eq_zero_of_stop_lt_start
    B lam state s t S label hB hlam0 hlamHalf hstop

theorem integral_restrict_Ioc_feedbackBranchBulkStart_stop_eq_zero_of_stop_lt_start
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (f : ℝ → ℝ)
    (hstop : feedbackBranchBulkStop B lam state t <
      feedbackBranchBulkStart B lam state s) :
    ∫ y in Ioc (feedbackBranchBulkStart B lam state s)
        (feedbackBranchBulkStop B lam state t), f y ∂volume = 0 := by
  rw [Ioc_feedbackBranchBulkStart_stop_eq_empty_of_stop_lt_start
    B lam state s t hstop]
  simp

end OTSelector
