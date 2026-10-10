import OTSelector.Feedback.AffineBulkInterval
import OTSelector.Feedback.FiniteHistorySurvivalFlux

/-!
# Positive finite-history factors on a bulk section

On a fixed affine state, a bulk point has all source and target boundaries strictly between zero
and `n`.  The one-point rank-strip mass formula therefore gives positive mass to every remaining
label.  Finite products of these factors give a positive product rectangle, hence a witness for
the unseen section.  This is deterministic fixed-state infrastructure; it introduces no
conditional law, certificate, `sorry`, or axiom.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

/-! ## One-label positivity -/

set_option linter.unusedVariables false in
theorem unitSquareUniform_feedbackLabelRemainingSetAt_real_pos_of_feedbackBulkRegion
    (state : FeedbackStepState n) (B lam a : ℝ)
    (hn : 0 < n) (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : feedbackBulkRegion n B a
      (segmentCurve state.x state.p (state.slope lam) a))
    (label : FeedbackLabel n) :
    0 < (unitSquareUniform : Measure MarkedHeight).real
      (feedbackLabelRemainingSetAt lam state a label) := by
  have haIcc : a ∈ Icc (feedbackBulkStateLower B lam state)
      (feedbackBulkStateUpper B lam state) :=
    (feedbackBulkRegion_state_iff_mem_Icc state hB).1 hbulk
  have hbounds := feedbackBulkState_boundary_bounds state hB haIcc
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hsourceArea : 0 < sourceUnclippedRemainingMass n
      (segmentCurve state.x state.p (state.slope lam) a) a := by
    have hlower : 0 < 15 * B / 16 := by positivity
    exact lt_of_lt_of_le hlower
      (sourceUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk)
  have htargetArea : 0 < targetUnclippedRemainingMass n
      (segmentCurve state.x state.p (state.slope lam) a) a := by
    have hlower : 0 < 13 * B / 16 := by positivity
    exact lt_of_lt_of_le hlower
      (targetUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk)
  have hsourceMass : 0 < feedbackSourceRemainingRealMassAt lam state a := by
    dsimp [feedbackSourceRemainingRealMassAt, feedbackSourceRemainingAreaAt]
    exact div_pos hsourceArea hnreal
  have htargetMass : 0 < feedbackTargetRemainingRealMassAt lam state a := by
    dsimp [feedbackTargetRemainingRealMassAt, feedbackTargetRemainingAreaAt]
    exact div_pos htargetArea hnreal
  cases label with
  | inl i =>
      have hmass := feedbackLabelRemainingRealMassAt_eq_unitSquareUniform_real
        hn lam state a (Sum.inl i) ⟨hbounds.1, hbounds.2⟩
      rw [← hmass]
      simpa [feedbackLabelRemainingRealMassAt] using hsourceMass
  | inr j =>
      have hmass := feedbackLabelRemainingRealMassAt_eq_unitSquareUniform_real
        hn lam state a (Sum.inr j) ⟨hbounds.1, hbounds.2⟩
      rw [← hmass]
      simpa [feedbackLabelRemainingRealMassAt] using htargetMass

theorem unitSquareUniform_feedbackLabelRemainingSetAt_pos_of_feedbackBulkRegion
    (state : FeedbackStepState n) (B lam a : ℝ)
    (hn : 0 < n) (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : feedbackBulkRegion n B a
      (segmentCurve state.x state.p (state.slope lam) a))
    (label : FeedbackLabel n) :
    0 < (unitSquareUniform : Measure MarkedHeight)
      (feedbackLabelRemainingSetAt lam state a label) := by
  have hreal := unitSquareUniform_feedbackLabelRemainingSetAt_real_pos_of_feedbackBulkRegion
    state B lam a hn hB hlam0 hlamHalf hbulk label
  have hreal_ne :
      (unitSquareUniform : Measure MarkedHeight).real
        (feedbackLabelRemainingSetAt lam state a label) ≠ 0 := ne_of_gt hreal
  have hmeasure_ne :
      (unitSquareUniform : Measure MarkedHeight)
        (feedbackLabelRemainingSetAt lam state a label) ≠ 0 :=
    (measureReal_ne_zero_iff).1 hreal_ne
  exact pos_iff_ne_zero.mpr hmeasure_ne

/-! ## Positive unseen product rectangle -/

theorem feedbackUnseenRectangularSetAt_productReal_pos_of_feedbackBulkRegion
    (state : FeedbackStepState n) (B lam a : ℝ)
    (S : Finset (FeedbackLabel n))
    (hn : 0 < n) (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : feedbackBulkRegion n B a
      (segmentCurve state.x state.p (state.slope lam) a)) :
    0 < (feedbackUnseenTupleLaw S).real
      (feedbackUnseenRectangularSetAt lam state a S) := by
  have haIcc : a ∈ Icc (feedbackBulkStateLower B lam state)
      (feedbackBulkStateUpper B lam state) :=
    (feedbackBulkRegion_state_iff_mem_Icc state hB).1 hbulk
  have hbounds := feedbackBulkState_boundary_bounds state hB haIcc
  have hbulkAll : ∀ label ∈ feedbackUnseenFinset S,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) a) a u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) a) a u ≤ n) ∧
      ∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) a) a v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) a) a v ≤ n := by
    intro label _
    exact ⟨hbounds.1, hbounds.2⟩
  have hprod : 0 < feedbackUnseenSurvivalMassAt lam state a S := by
    simp only [feedbackUnseenSurvivalMassAt]
    apply Finset.prod_pos
    intro label hlabel
    rw [feedbackLabelRemainingRealMassAt_eq_unitSquareUniform_real
      hn lam state a label ⟨hbounds.1, hbounds.2⟩]
    exact unitSquareUniform_feedbackLabelRemainingSetAt_real_pos_of_feedbackBulkRegion
      state B lam a hn hB hlam0 hlamHalf hbulk label
  rw [← feedbackUnseenSurvivalMassAt_eq_feedbackUnseenTupleLaw_real
    hn lam state a S hbulkAll]
  exact hprod

theorem feedbackUnseenRectangularSetAt_nonempty_of_feedbackBulkRegion
    (state : FeedbackStepState n) (B lam a : ℝ)
    (S : Finset (FeedbackLabel n))
    (hn : 0 < n) (hB : 0 < B) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbulk : feedbackBulkRegion n B a
      (segmentCurve state.x state.p (state.slope lam) a)) :
    (feedbackUnseenRectangularSetAt lam state a S).Nonempty := by
  apply nonempty_of_measureReal_ne_zero
    (μ := feedbackUnseenTupleLaw S)
  exact ne_of_gt (feedbackUnseenRectangularSetAt_productReal_pos_of_feedbackBulkRegion
    state B lam a S hn hB hlam0 hlamHalf hbulk)

end OTSelector
