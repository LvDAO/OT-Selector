import OTSelector.Feedback.AffineBulkInterval
import OTSelector.Feedback.FiniteHistorySurvivalFlux

/-!
# Half-open reduction of a fixed affine bulk slab

The paper's bulk strip is closed, whereas counting increments use `(s,t]`.  Their intersection
is the canonical half-open interval obtained by clipping both endpoints, up to at most the lower
bulk endpoint.  This file records the exact inclusions; the next module removes that singleton
using the atomlessness of a fixed crossing coordinate.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

noncomputable def feedbackBulkNextStart
    (B lam : ℝ) (state : FeedbackStepState n) (s : ℝ) : ℝ :=
  max s (feedbackBulkStateLower B lam state)

noncomputable def feedbackBulkNextStop
    (B lam : ℝ) (state : FeedbackStepState n) (t : ℝ) : ℝ :=
  min t (feedbackBulkStateUpper B lam state)

/-- The branch is only alive strictly after its terminal knot. -/
noncomputable def feedbackBranchBulkStart
    (B lam : ℝ) (state : FeedbackStepState n) (s : ℝ) : ℝ :=
  max state.x (feedbackBulkNextStart B lam state s)

noncomputable def feedbackBranchBulkStop
    (B lam : ℝ) (state : FeedbackStepState n) (t : ℝ) : ℝ :=
  feedbackBulkNextStop B lam state t

theorem feedbackBranchBulkStart_ge_state
    (B lam : ℝ) (state : FeedbackStepState n) (s : ℝ) :
    state.x ≤ feedbackBranchBulkStart B lam state s :=
  le_max_left _ _

theorem feedbackBranchBulkStart_ge_s
    (B lam : ℝ) (state : FeedbackStepState n) (s : ℝ) :
    s ≤ feedbackBranchBulkStart B lam state s :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem feedbackBranchBulkStart_ge_lower
    (B lam : ℝ) (state : FeedbackStepState n) (s : ℝ) :
    feedbackBulkStateLower B lam state ≤ feedbackBranchBulkStart B lam state s :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem feedbackBranchBulkStop_le_t
    (B lam : ℝ) (state : FeedbackStepState n) (t : ℝ) :
    feedbackBranchBulkStop B lam state t ≤ t :=
  min_le_left _ _

theorem feedbackBranchBulkStop_le_upper
    (B lam : ℝ) (state : FeedbackStepState n) (t : ℝ) :
    feedbackBranchBulkStop B lam state t ≤ feedbackBulkStateUpper B lam state :=
  min_le_right _ _

theorem feedbackBulkRegion_on_branchBulkInterval
    (B lam : ℝ) (state : FeedbackStepState n) (s t y : ℝ) (hB : 0 < B)
    (hy : y ∈ Icc (feedbackBranchBulkStart B lam state s)
      (feedbackBranchBulkStop B lam state t)) :
    feedbackBulkRegion n B y
      (segmentCurve state.x state.p (state.slope lam) y) := by
  apply (feedbackBulkRegion_state_iff_mem_Icc state hB).2
  exact ⟨(feedbackBranchBulkStart_ge_lower B lam state s).trans hy.1,
    hy.2.trans (feedbackBranchBulkStop_le_upper B lam state t)⟩

theorem feedbackBoundary_bounds_on_branchBulkInterval
    (B lam : ℝ) (state : FeedbackStepState n) (s t y : ℝ) (hB : 0 < B)
    (hy : y ∈ Icc (feedbackBranchBulkStart B lam state s)
      (feedbackBranchBulkStop B lam state t)) :
    (∀ u : UnitMark,
      0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
          targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n := by
  exact feedbackBulkState_boundary_bounds state hB
    ⟨(feedbackBranchBulkStart_ge_lower B lam state s).trans hy.1,
      hy.2.trans (feedbackBranchBulkStop_le_upper B lam state t)⟩

theorem feedbackSourceRemainingRealMassAt_pos_on_branchBulkInterval
    (B lam : ℝ) (state : FeedbackStepState n) (s t y : ℝ)
    (hn : 0 < n) (hB : 0 < B)
    (hy : y ∈ Icc (feedbackBranchBulkStart B lam state s)
      (feedbackBranchBulkStop B lam state t)) :
    0 < feedbackSourceRemainingRealMassAt lam state y := by
  have hbulk := feedbackBulkRegion_on_branchBulkInterval B lam state s t y hB hy
  have harea := sourceUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold feedbackSourceRemainingRealMassAt feedbackSourceRemainingAreaAt
  exact div_pos (lt_of_lt_of_le (by positivity : 0 < 15 * B / 16) harea) hnreal

theorem feedbackTargetRemainingRealMassAt_pos_on_branchBulkInterval
    (B lam : ℝ) (state : FeedbackStepState n) (s t y : ℝ)
    (hn : 0 < n) (hB : 0 < B)
    (hy : y ∈ Icc (feedbackBranchBulkStart B lam state s)
      (feedbackBranchBulkStop B lam state t)) :
    0 < feedbackTargetRemainingRealMassAt lam state y := by
  have hbulk := feedbackBulkRegion_on_branchBulkInterval B lam state s t y hB hy
  have harea := targetUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold feedbackTargetRemainingRealMassAt feedbackTargetRemainingAreaAt
  exact div_pos (lt_of_lt_of_le (by positivity : 0 < 13 * B / 16) harea) hnreal

theorem Ioc_feedbackBulkNext_subset
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ) (hB : 0 < B) :
    Ioc (feedbackBulkNextStart B lam state s)
        (feedbackBulkNextStop B lam state t) ⊆
      {y | feedbackBulkRegion n B y
        (segmentCurve state.x state.p (state.slope lam) y)} ∩ Ioc s t := by
  intro y hy
  have hleft := lt_of_le_of_lt (le_max_left s (feedbackBulkStateLower B lam state)) hy.1
  have hlower := lt_of_le_of_lt
    (le_max_right s (feedbackBulkStateLower B lam state)) hy.1
  have hright := hy.2.trans (min_le_left t (feedbackBulkStateUpper B lam state))
  have hupper := hy.2.trans
    (min_le_right t (feedbackBulkStateUpper B lam state))
  refine ⟨(feedbackBulkRegion_state_iff_mem_Icc state hB).2 ⟨hlower.le, hupper⟩,
    hleft, hright⟩

theorem feedbackBulk_inter_Ioc_sdiff_Ioc_feedbackBulkNext_subset_singleton
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ) (hB : 0 < B) :
    ({y | feedbackBulkRegion n B y
        (segmentCurve state.x state.p (state.slope lam) y)} ∩ Ioc s t) \
        Ioc (feedbackBulkNextStart B lam state s)
          (feedbackBulkNextStop B lam state t) ⊆
      {feedbackBulkStateLower B lam state} := by
  intro y hy
  rcases hy with ⟨⟨hybulk, hyst, hyt⟩, hynext⟩
  have hybounds := (feedbackBulkRegion_state_iff_mem_Icc state hB).1 hybulk
  have hyStop : y ≤ feedbackBulkNextStop B lam state t := by
    exact le_min hyt hybounds.2
  have hnotStart : ¬ feedbackBulkNextStart B lam state s < y := by
    intro hstart
    exact hynext ⟨hstart, hyStop⟩
  have hyStart : y ≤ feedbackBulkNextStart B lam state s := le_of_not_gt hnotStart
  have hlower_le : feedbackBulkStateLower B lam state ≤ y := hybounds.1
  have hmax_cases : feedbackBulkNextStart B lam state s = s ∨
      feedbackBulkNextStart B lam state s = feedbackBulkStateLower B lam state := by
    exact max_choice s (feedbackBulkStateLower B lam state)
  rcases hmax_cases with hstartS | hstartLower
  · have : y ≤ s := by simpa [hstartS] using hyStart
    exact False.elim ((not_le_of_gt hyst) this)
  · have hyLower : y ≤ feedbackBulkStateLower B lam state := by
      simpa [hstartLower] using hyStart
    have : y = feedbackBulkStateLower B lam state := le_antisymm hyLower hlower_le
    simp [this]

theorem feedbackBulk_inter_Ioc_ae_eq_Ioc_feedbackBulkNext
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ) (hB : 0 < B) :
    (({y : ℝ | feedbackBulkRegion n B y
        (segmentCurve state.x state.p (state.slope lam) y)} ∩ Ioc s t) : Set ℝ) =ᵐ[volume]
      Ioc (feedbackBulkNextStart B lam state s)
        (feedbackBulkNextStop B lam state t) := by
  apply Filter.EventuallyLE.antisymm
  · apply ae_le_set.mpr
    exact measure_mono_null
      (feedbackBulk_inter_Ioc_sdiff_Ioc_feedbackBulkNext_subset_singleton
        B lam state s t hB)
      (measure_singleton (feedbackBulkStateLower B lam state))
  · exact Filter.Eventually.of_forall
      (Ioc_feedbackBulkNext_subset B lam state s t hB)

theorem feedbackBulk_inter_Ioc_inter_Ioi_state_ae_eq_Ioc_branchBulk
    (B lam : ℝ) (state : FeedbackStepState n) (s t : ℝ) (hB : 0 < B) :
    ((({y : ℝ | feedbackBulkRegion n B y
        (segmentCurve state.x state.p (state.slope lam) y)} ∩ Ioc s t) ∩
          Ioi state.x) : Set ℝ) =ᵐ[volume]
      Ioc (feedbackBranchBulkStart B lam state s)
        (feedbackBranchBulkStop B lam state t) := by
  have hbase := ae_eq_set_inter
    (feedbackBulk_inter_Ioc_ae_eq_Ioc_feedbackBulkNext B lam state s t hB)
    (ae_eq_refl (Ioi state.x))
  apply hbase.trans
  exact Filter.Eventually.of_forall fun y ↦ by
    apply propext
    change
      (y ∈ Ioc (feedbackBulkNextStart B lam state s)
          (feedbackBulkNextStop B lam state t) ∩ Ioi state.x) ↔
        y ∈ Ioc (feedbackBranchBulkStart B lam state s)
          (feedbackBranchBulkStop B lam state t)
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi, feedbackBranchBulkStart,
      feedbackBranchBulkStop, max_lt_iff]
    tauto

end OTSelector
