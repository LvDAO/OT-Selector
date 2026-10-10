import OTSelector.Feedback.FiniteHistoryBulkInterval
import OTSelector.Feedback.FiniteHistoryCrossingAtomless
import OTSelector.Feedback.FiniteHistorySectionConstancy

/-!
# Bulk-restricted next events on a fixed finite-history section

On the strict terminal remaining rectangle, accepting a next crossing in the closed affine bulk
strip and in `(s,t]` is the same, up to a null lower-endpoint fibre, as asking that the crossing
lie in the clipped half-open interval `(branchStart, branchStop]`.  This is the exact endpoint
reduction needed before inserting a raw predictable event and applying the fixed-section flux
identity.
-/

open MeasureTheory Set
open scoped Classical

namespace OTSelector

variable {n : ℕ}

/-- The next unseen label is selected in `(s,t]`, the branch was still alive at its terminal
coordinate, and the selected crossing lies in the affine bulk strip. -/
def feedbackBulkNextEventSet
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S) :
    Set (feedbackUnseenFinset S → MarkedHeight) :=
  feedbackUnseenRectangularSetAt lam state state.x S ∩
    feedbackNextEventSet lam state s t S label ∩
      {unseen |
        let y := feedbackLabelFixedStateCrossing n lam state label (unseen label)
        feedbackBulkRegion n B y
          (segmentCurve state.x state.p (state.slope lam) y)}

/-- Ambient-label wrapper; already-seen labels contribute the empty set. -/
noncomputable def feedbackBulkNextEventSetOfLabel
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n) :
    Set (feedbackUnseenFinset S → MarkedHeight) :=
  if hlabel : label ∈ feedbackUnseenFinset S then
    feedbackBulkNextEventSet B lam state s t S ⟨label, hlabel⟩
  else ∅

theorem measurableSet_feedbackBulkNextEventSet
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet (feedbackBulkNextEventSet B lam state s t S label) := by
  have hcross : Measurable
      (fun unseen : feedbackUnseenFinset S → MarkedHeight ↦
        feedbackLabelFixedStateCrossing n lam state label (unseen label)) :=
    (measurable_feedbackLabelFixedStateCrossing state lam label hlam0 hlamHalf).comp
      (measurable_pi_apply label)
  have hcurve : Measurable
      (fun unseen : feedbackUnseenFinset S → MarkedHeight ↦
        segmentCurve state.x state.p (state.slope lam)
          (feedbackLabelFixedStateCrossing n lam state label (unseen label))) := by
    have haffine : Continuous
        (fun y : ℝ ↦ segmentCurve state.x state.p (state.slope lam) y) := by
      unfold segmentCurve
      fun_prop
    exact haffine.measurable.comp hcross
  exact ((measurableSet_feedbackUnseenRectangularSetAt lam state state.x S).inter
    (measurableSet_feedbackNextEventSet state lam s t S label hlam0 hlamHalf)).inter
      ((feedbackBulkRegion_measurableSet n B).preimage (hcross.prodMk hcurve))

theorem measurableSet_feedbackBulkNextEventSetOfLabel
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    MeasurableSet (feedbackBulkNextEventSetOfLabel B lam state s t S label) := by
  classical
  unfold feedbackBulkNextEventSetOfLabel
  split_ifs with hlabel
  · exact measurableSet_feedbackBulkNextEventSet B lam state s t S
      ⟨label, hlabel⟩ hlam0 hlamHalf
  · exact MeasurableSet.empty

private theorem feedbackNextEventSet_branchBulk_subset
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hab : feedbackBranchBulkStart B lam state s ≤
      feedbackBranchBulkStop B lam state t) :
    feedbackNextEventSet lam state
        (feedbackBranchBulkStart B lam state s)
        (feedbackBranchBulkStop B lam state t) S label ⊆
      feedbackBulkNextEventSet B lam state s t S label := by
  intro unseen hnext
  let a := feedbackBranchBulkStart B lam state s
  let b := feedbackBranchBulkStop B lam state t
  let y := feedbackLabelFixedStateCrossing n lam state label (unseen label)
  have hy : y ∈ Ioc a b := hnext.1
  have hrectA := feedbackNextEventSet_subset_feedbackUnseenRectangularSetAt
    state lam a b S label hlam0 hlamHalf hab hnext
  have hstateA : state.x ≤ a := feedbackBranchBulkStart_ge_state B lam state s
  have hrect : unseen ∈ feedbackUnseenRectangularSetAt lam state state.x S :=
    feedbackUnseenRectangularSetAt_subset lam state state.x a S
      hlam0 hlamHalf hstateA hrectA
  have hst : y ∈ Ioc s t := by
    exact ⟨lt_of_le_of_lt (feedbackBranchBulkStart_ge_s B lam state s) hy.1,
      hy.2.trans (feedbackBranchBulkStop_le_t B lam state t)⟩
  have hbulk : feedbackBulkRegion n B y
      (segmentCurve state.x state.p (state.slope lam) y) := by
    apply (feedbackBulkRegion_state_iff_mem_Icc state hB).2
    exact ⟨(feedbackBranchBulkStart_ge_lower B lam state s).trans hy.1.le,
      hy.2.trans (feedbackBranchBulkStop_le_upper B lam state t)⟩
  exact ⟨⟨hrect, ⟨hst, hnext.2⟩⟩, hbulk⟩

private theorem feedbackBulkNextEventSet_sdiff_branchBulk_subset_singleton
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    feedbackBulkNextEventSet B lam state s t S label \
        feedbackNextEventSet lam state
          (feedbackBranchBulkStart B lam state s)
          (feedbackBranchBulkStop B lam state t) S label ⊆
      {unseen |
        feedbackLabelFixedStateCrossing n lam state label (unseen label) =
          feedbackBulkStateLower B lam state} := by
  intro unseen hunseen
  rcases hunseen with ⟨⟨⟨hrect, hnext⟩, hbulk⟩, hnotClipped⟩
  let y := feedbackLabelFixedStateCrossing n lam state label (unseen label)
  have hyst : y ∈ Ioc s t := hnext.1
  have hybulk := (feedbackBulkRegion_state_iff_mem_Icc state hB).1 hbulk
  have hystate : state.x < y := by
    have hremain :=
      (mem_feedbackUnseenRectangularSetAt_iff lam state state.x S unseen).1 hrect label
    exact (mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
      state lam label (unseen label) state.x hlam0 hlamHalf).1 hremain
  have hyStop : y ≤ feedbackBranchBulkStop B lam state t := by
    exact le_min hyst.2 hybulk.2
  have hnotStart : ¬ feedbackBranchBulkStart B lam state s < y := by
    intro hstart
    exact hnotClipped ⟨⟨hstart, hyStop⟩, hnext.2⟩
  have hyStart : y ≤ feedbackBranchBulkStart B lam state s := le_of_not_gt hnotStart
  have houter : feedbackBranchBulkStart B lam state s = state.x ∨
      feedbackBranchBulkStart B lam state s = feedbackBulkNextStart B lam state s :=
    max_choice state.x (feedbackBulkNextStart B lam state s)
  rcases houter with hstate | hnextStart
  · have : y ≤ state.x := by simpa [hstate] using hyStart
    exact False.elim ((not_le_of_gt hystate) this)
  · have hinner : feedbackBulkNextStart B lam state s = s ∨
        feedbackBulkNextStart B lam state s = feedbackBulkStateLower B lam state :=
      max_choice s (feedbackBulkStateLower B lam state)
    rcases hinner with hs | hlower
    · have : y ≤ s := by simpa [hnextStart, hs] using hyStart
      exact False.elim ((not_le_of_gt hyst.1) this)
    · have hyle : y ≤ feedbackBulkStateLower B lam state := by
        simpa [hnextStart, hlower] using hyStart
      exact le_antisymm hyle hybulk.1

theorem feedbackBulkNextEventSet_ae_eq_branchBulkNextEventSet
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hn : 0 < n) (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hab : feedbackBranchBulkStart B lam state s ≤
      feedbackBranchBulkStop B lam state t) :
    feedbackBulkNextEventSet B lam state s t S label =ᵐ[feedbackUnseenTupleLaw S]
      feedbackNextEventSet lam state
        (feedbackBranchBulkStart B lam state s)
        (feedbackBranchBulkStop B lam state t) S label := by
  apply Filter.EventuallyLE.antisymm
  · apply ae_le_set.mpr
    exact measure_mono_null
      (feedbackBulkNextEventSet_sdiff_branchBulk_subset_singleton
        B lam state s t S label hB hlam0 hlamHalf)
      (feedbackUnseenTupleLaw_fixedStateCrossing_singleton_eq_zero
        state lam S label (feedbackBulkStateLower B lam state)
          hn hlam0 hlamHalf)
  · exact Filter.Eventually.of_forall
      (feedbackNextEventSet_branchBulk_subset
        B lam state s t S label hB hlam0 hlamHalf hab)

theorem feedbackUnseenTupleLaw_real_feedbackBulkNextEventSet_eq
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : feedbackUnseenFinset S)
    (hn : 0 < n) (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hab : feedbackBranchBulkStart B lam state s ≤
      feedbackBranchBulkStop B lam state t) :
    (feedbackUnseenTupleLaw S).real
        (feedbackBulkNextEventSet B lam state s t S label) =
      (feedbackUnseenTupleLaw S).real
        (feedbackNextEventSet lam state
          (feedbackBranchBulkStart B lam state s)
          (feedbackBranchBulkStop B lam state t) S label) := by
  unfold Measure.real
  rw [measure_congr (feedbackBulkNextEventSet_ae_eq_branchBulkNextEventSet
    B lam state s t S label hn hB hlam0 hlamHalf hab)]

theorem feedbackUnseenTupleLaw_real_feedbackBulkNextEventSetOfLabel_eq
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hn : 0 < n) (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hab : feedbackBranchBulkStart B lam state s ≤
      feedbackBranchBulkStop B lam state t) :
    (feedbackUnseenTupleLaw S).real
        (feedbackBulkNextEventSetOfLabel B lam state s t S label) =
      (feedbackUnseenTupleLaw S).real
        (feedbackNextEventSetOfLabel lam state
          (feedbackBranchBulkStart B lam state s)
          (feedbackBranchBulkStop B lam state t) S label) := by
  classical
  unfold feedbackBulkNextEventSetOfLabel feedbackNextEventSetOfLabel
  split_ifs with hlabel
  · exact feedbackUnseenTupleLaw_real_feedbackBulkNextEventSet_eq
      B lam state s t S ⟨label, hlabel⟩ hn hB hlam0 hlamHalf hab
  · rfl

theorem feedbackBulkNextEventSetOfLabel_ae_eq_branchBulkNextEventSetOfLabel
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ)
    (S : Finset (FeedbackLabel n)) (label : FeedbackLabel n)
    (hn : 0 < n) (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hab : feedbackBranchBulkStart B lam state s ≤
      feedbackBranchBulkStop B lam state t) :
    feedbackBulkNextEventSetOfLabel B lam state s t S label
        =ᵐ[feedbackUnseenTupleLaw S]
      feedbackNextEventSetOfLabel lam state
        (feedbackBranchBulkStart B lam state s)
        (feedbackBranchBulkStop B lam state t) S label := by
  classical
  unfold feedbackBulkNextEventSetOfLabel feedbackNextEventSetOfLabel
  split_ifs with hlabel
  · exact feedbackBulkNextEventSet_ae_eq_branchBulkNextEventSet
      B lam state s t S ⟨label, hlabel⟩ hn hB hlam0 hlamHalf hab
  · exact Filter.EventuallyEq.rfl

end OTSelector
