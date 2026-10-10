import OTSelector.Feedback.FeedbackHazard
import OTSelector.Feedback.FiniteHistoryAt

/-!
# One-point remaining masses along a finite feedback history

The point law is the pullback of the rank-strip law under the deterministic rank map.  This file
records the resulting one-point masses for the strict raw remaining regions, and then specializes
them to affine continuations of a feedback state.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## Pulling rank-strip complement masses back to one marked point -/

theorem unitSquareUniform_sourceRawRemainingSet
    {n : ℕ} {p x : ℝ} (hn : 0 < n)
    (hsection0 : ∀ u : UnitMark, 0 ≤ sourceBoundary p x u)
    (hsectionN : ∀ u : UnitMark, sourceBoundary p x u ≤ n) :
    (unitSquareUniform : Measure MarkedHeight).real (sourceRawRemainingSet n p x) =
      sourceUnclippedRemainingMass n p x / n := by
  have hpre : rankStripMap (n : ℝ) ⁻¹' RelativeVC.sourceCutComplementSet p x =
      sourceRawRemainingSet n p x := by
    ext z
    simp [rankStripMap, rankCoordinateMap, RelativeVC.sourceCutComplementSet,
      sourceRawRemainingSet]
  calc
    (unitSquareUniform : Measure MarkedHeight).real (sourceRawRemainingSet n p x) =
        (rankStripLaw n : Measure (ℝ × UnitMark)).real
          (RelativeVC.sourceCutComplementSet p x) := by
      change ENNReal.toReal
          ((unitSquareUniform : Measure MarkedHeight) (sourceRawRemainingSet n p x)) =
        ENNReal.toReal
          ((Measure.map (rankStripMap (n : ℝ))
            (unitUniform.prod unitUniform : Measure MarkedHeight))
            (RelativeVC.sourceCutComplementSet p x))
      rw [Measure.map_apply (measurable_rankStripMap (n : ℝ))
        (RelativeVC.measurableSet_sourceCutComplementSet p x), hpre]
      rfl
    _ = sourceUnclippedRemainingMass n p x / n :=
      rankStripLaw_real_sourceCutComplement hn hsection0 hsectionN

theorem unitSquareUniform_targetRawRemainingSet
    {n : ℕ} {p x : ℝ} (hn : 0 < n)
    (hsection0 : ∀ v : UnitMark, 0 ≤ targetBoundary p x v)
    (hsectionN : ∀ v : UnitMark, targetBoundary p x v ≤ n) :
    (unitSquareUniform : Measure MarkedHeight).real (targetRawRemainingSet n p x) =
      targetUnclippedRemainingMass n p x / n := by
  have hpre : rankStripMap (n : ℝ) ⁻¹' RelativeVC.targetCutComplementSet p x =
      targetRawRemainingSet n p x := by
    ext z
    simp [rankStripMap, rankCoordinateMap, RelativeVC.targetCutComplementSet,
      targetRawRemainingSet]
  calc
    (unitSquareUniform : Measure MarkedHeight).real (targetRawRemainingSet n p x) =
        (rankStripLaw n : Measure (ℝ × UnitMark)).real
          (RelativeVC.targetCutComplementSet p x) := by
      change ENNReal.toReal
          ((unitSquareUniform : Measure MarkedHeight) (targetRawRemainingSet n p x)) =
        ENNReal.toReal
          ((Measure.map (rankStripMap (n : ℝ))
            (unitUniform.prod unitUniform : Measure MarkedHeight))
            (RelativeVC.targetCutComplementSet p x))
      rw [Measure.map_apply (measurable_rankStripMap (n : ℝ))
        (RelativeVC.measurableSet_targetCutComplementSet p x), hpre]
      rfl
    _ = targetUnclippedRemainingMass n p x / n :=
      rankStripLaw_real_targetCutComplement hn hsection0 hsectionN

/-! ## Timed affine continuations -/

theorem unitSquareUniform_sourceRawRemainingSetAt_mass
    (state : FeedbackStepState n) (lam x : ℝ) (hn : 0 < n)
    (hsection0 : ∀ u : UnitMark,
      0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) x) x u)
    (hsectionN : ∀ u : UnitMark,
      sourceBoundary (segmentCurve state.x state.p (state.slope lam) x) x u ≤ n) :
    (unitSquareUniform : Measure MarkedHeight).real
        (sourceRawRemainingSetAt n lam state x) =
      sourceUnclippedRemainingMass n
        (segmentCurve state.x state.p (state.slope lam) x) x / n := by
  exact unitSquareUniform_sourceRawRemainingSet hn hsection0 hsectionN

theorem unitSquareUniform_targetRawRemainingSetAt_mass
    (state : FeedbackStepState n) (lam x : ℝ) (hn : 0 < n)
    (hsection0 : ∀ u : UnitMark,
      0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) x) x u)
    (hsectionN : ∀ u : UnitMark,
      targetBoundary (segmentCurve state.x state.p (state.slope lam) x) x u ≤ n) :
    (unitSquareUniform : Measure MarkedHeight).real
        (targetRawRemainingSetAt n lam state x) =
      targetUnclippedRemainingMass n
        (segmentCurve state.x state.p (state.slope lam) x) x / n := by
  exact unitSquareUniform_targetRawRemainingSet hn hsection0 hsectionN

theorem unitSquareUniform_sourceRawRemainingSetAt_mass_sub
    (state : FeedbackStepState n) (lam s t : ℝ) (hn : 0 < n) (hst : s ≤ t)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ u : UnitMark,
        0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u) ∧
      (∀ u : UnitMark,
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n)) :
    (unitSquareUniform : Measure MarkedHeight).real
        (sourceRawRemainingSetAt n lam state s) -
        (unitSquareUniform : Measure MarkedHeight).real
          (sourceRawRemainingSetAt n lam state t) =
      (t - s) * (1 - state.slope lam / 2) / n := by
  have hs := unitSquareUniform_sourceRawRemainingSetAt_mass state lam s hn
    (hbulk s ⟨le_rfl, hst⟩).1 (hbulk s ⟨le_rfl, hst⟩).2
  have ht := unitSquareUniform_sourceRawRemainingSetAt_mass state lam t hn
    (hbulk t ⟨hst, le_rfl⟩).1 (hbulk t ⟨hst, le_rfl⟩).2
  rw [hs, ht]
  have hsub := sourceUnclippedRemainingMass_segment_sub n state.x state.p
    (state.slope lam) s t
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
  nlinarith [hsub]

theorem unitSquareUniform_targetRawRemainingSetAt_mass_sub
    (state : FeedbackStepState n) (lam s t : ℝ) (hn : 0 < n) (hst : s ≤ t)
    (hbulk : ∀ y ∈ Icc s t,
      (∀ v : UnitMark,
        0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v) ∧
      (∀ v : UnitMark,
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n)) :
    (unitSquareUniform : Measure MarkedHeight).real
        (targetRawRemainingSetAt n lam state s) -
        (unitSquareUniform : Measure MarkedHeight).real
          (targetRawRemainingSetAt n lam state t) =
      (t - s) * (1 + 3 * state.slope lam / 2) / n := by
  have hs := unitSquareUniform_targetRawRemainingSetAt_mass state lam s hn
    (hbulk s ⟨le_rfl, hst⟩).1 (hbulk s ⟨le_rfl, hst⟩).2
  have ht := unitSquareUniform_targetRawRemainingSetAt_mass state lam t hn
    (hbulk t ⟨hst, le_rfl⟩).1 (hbulk t ⟨hst, le_rfl⟩).2
  rw [hs, ht]
  have hsub := targetUnclippedRemainingMass_segment_sub n state.x state.p
    (state.slope lam) s t
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
  nlinarith [hsub]

end OTSelector
