import OTSelector.Feedback.CutMass
import OTSelector.Feedback.FeedbackRecursion

/-!
# Deterministic bulk swept-area formulas for one feedback segment

For a fixed affine continuation whose vertical sections stay inside the rank strip, the unswept
source and target areas are affine functions of the coordinate.  Their losses per unit coordinate
are exactly the marked factors and total factors in `(1.13)--(1.15)`.

The definitions below are deliberately named `unclipped`: outside the bulk they are algebraic
extensions, not physical areas or hazards.  `TrueArea.lean` supplies the globally valid clipped
quantities and proves agreement under section bounds.  Conditional product laws and compensator
martingales belong to the subsequent probability layer.
-/

open MeasureTheory

namespace OTSelector

/-- Algebraic source remaining-area formula, valid as an area when sections lie in the strip. -/
noncomputable def sourceUnclippedRemainingMass (width p x : ℝ) : ℝ :=
  width - x + p / 2

/-- Algebraic target remaining-area formula, valid as an area when sections lie in the strip. -/
noncomputable def targetUnclippedRemainingMass (width p x : ℝ) : ℝ :=
  width - x - 3 * p / 2

/-- Source boundary height at mark `u`. -/
def sourceBoundary (p x u : ℝ) : ℝ :=
  x - p * (1 - u)

/-- Target boundary height at mark `v`. -/
def targetBoundary (p x v : ℝ) : ℝ :=
  x + p * (1 + v)

/-- Advancing an affine segment sweeps a source mark slice at the source marked rate. -/
theorem sourceBoundary_segment_sub
    (x0 p0 q x y u : ℝ) :
    sourceBoundary (segmentCurve x0 p0 q y) y u -
        sourceBoundary (segmentCurve x0 p0 q x) x u =
      (y - x) * sourceMarkedFactor q u := by
  simp only [sourceBoundary, segmentCurve, sourceMarkedFactor]
  ring

/-- Advancing an affine segment sweeps a target mark slice at the target marked rate. -/
theorem targetBoundary_segment_sub
    (x0 p0 q x y v : ℝ) :
    targetBoundary (segmentCurve x0 p0 q y) y v -
        targetBoundary (segmentCurve x0 p0 q x) x v =
      (y - x) * targetMarkedFactor q v := by
  simp only [targetBoundary, segmentCurve, targetMarkedFactor]
  ring

/-- Change of the source unclipped area formula along an affine segment. -/
theorem sourceUnclippedRemainingMass_segment_sub
    (width x0 p0 q x y : ℝ) :
    sourceUnclippedRemainingMass width (segmentCurve x0 p0 q x) x -
        sourceUnclippedRemainingMass width (segmentCurve x0 p0 q y) y =
      (y - x) * (1 - q / 2) := by
  simp only [sourceUnclippedRemainingMass, segmentCurve]
  ring

/-- Change of the target unclipped area formula along an affine segment. -/
theorem targetUnclippedRemainingMass_segment_sub
    (width x0 p0 q x y : ℝ) :
    targetUnclippedRemainingMass width (segmentCurve x0 p0 q x) x -
        targetUnclippedRemainingMass width (segmentCurve x0 p0 q y) y =
      (y - x) * (1 + 3 * q / 2) := by
  simp only [targetUnclippedRemainingMass, segmentCurve]
  ring

/-- The source marked factor integrates to the source total factor on the unit mark law. -/
theorem integral_sourceMarkedFactor (q : ℝ) :
    ∫ u : UnitMark, sourceMarkedFactor q u ∂(unitUniform : Measure UnitMark) =
      1 - q / 2 := by
  have h := RelativeVC.integral_unitUniform_affine (1 - q) q
  convert h using 1
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u ↦ by
      simp only [sourceMarkedFactor]
      ring
  · ring

/-- The target marked factor integrates to the target total factor on the unit mark law. -/
theorem integral_targetMarkedFactor (q : ℝ) :
    ∫ v : UnitMark, targetMarkedFactor q v ∂(unitUniform : Measure UnitMark) =
      1 + 3 * q / 2 := by
  have h := RelativeVC.integral_unitUniform_affine (1 + q) q
  convert h using 1
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v ↦ by
      simp only [targetMarkedFactor]
      ring
  · ring

namespace FeedbackStepState

variable {n : ℕ}

/-- Bulk source-density formula.  It has a probabilistic meaning only under the bulk invariant. -/
noncomputable def sourceUnclippedResidualDensity (state : FeedbackStepState n) : ℝ :=
  ((n - state.seenSource.card : ℕ) : ℝ) /
    sourceUnclippedRemainingMass n state.p state.x

/-- Bulk target-density formula.  It has a probabilistic meaning only under the bulk invariant. -/
noncomputable def targetUnclippedResidualDensity (state : FeedbackStepState n) : ℝ :=
  ((n - state.seenTarget.card : ℕ) : ℝ) /
    targetUnclippedRemainingMass n state.p state.x

/-- Bulk source-rate formula.  No intensity claim is made for an arbitrary recursion state. -/
noncomputable def sourceUnclippedStateRate (lam : ℝ) (state : FeedbackStepState n) : ℝ :=
  sourceTotalRate state.sourceUnclippedResidualDensity (state.slope lam)

/-- Bulk target-rate formula.  No intensity claim is made for an arbitrary recursion state. -/
noncomputable def targetUnclippedStateRate (lam : ℝ) (state : FeedbackStepState n) : ℝ :=
  targetTotalRate state.targetUnclippedResidualDensity (state.slope lam)

theorem sourceUnclippedStateRate_eq (lam : ℝ) (state : FeedbackStepState n) :
    state.sourceUnclippedStateRate lam =
      ((n - state.seenSource.card : ℕ) : ℝ) /
          sourceUnclippedRemainingMass n state.p state.x *
        (1 - state.slope lam / 2) := by
  rfl

theorem targetUnclippedStateRate_eq (lam : ℝ) (state : FeedbackStepState n) :
    state.targetUnclippedStateRate lam =
      ((n - state.seenTarget.card : ℕ) : ℝ) /
          targetUnclippedRemainingMass n state.p state.x *
        (1 + 3 * state.slope lam / 2) := by
  rfl

end FeedbackStepState

variable {n : ℕ}

/-- Exact source population complement mass in rank coordinates. -/
theorem rankStripLaw_source_complement_mass
    {p x : ℝ} (hn : 0 < n)
    (hsection0 : ∀ u : UnitMark, 0 ≤ sourceBoundary p x u)
    (hsectionN : ∀ u : UnitMark, sourceBoundary p x u ≤ n) :
    (n : ℝ) * (1 - (rankStripLaw n : Measure (ℝ × UnitMark)).real
        (RelativeVC.errorSet (RelativeVC.sourceCutEval (p, x))
          RelativeVC.falseCutTarget)) =
      sourceUnclippedRemainingMass n p x := by
  have hmass := RelativeVC.rankStripLaw_real_sourceCut
    (width := (n : ℝ)) (p := p) (x := x) (by exact_mod_cast hn)
    (by simpa only [sourceBoundary] using hsection0)
    (by simpa only [sourceBoundary] using hsectionN)
  rw [hmass]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [sourceUnclippedRemainingMass]
  field_simp
  ring

/-- Exact target population complement mass in rank coordinates. -/
theorem rankStripLaw_target_complement_mass
    {p x : ℝ} (hn : 0 < n)
    (hsection0 : ∀ v : UnitMark, 0 ≤ targetBoundary p x v)
    (hsectionN : ∀ v : UnitMark, targetBoundary p x v ≤ n) :
    (n : ℝ) * (1 - (rankStripLaw n : Measure (ℝ × UnitMark)).real
        (RelativeVC.errorSet (RelativeVC.targetCutEval (p, x))
          RelativeVC.falseCutTarget)) =
      targetUnclippedRemainingMass n p x := by
  have hmass := RelativeVC.rankStripLaw_real_targetCut
    (width := (n : ℝ)) (p := p) (x := x) (by exact_mod_cast hn)
    (by simpa only [targetBoundary] using hsection0)
    (by simpa only [targetBoundary] using hsectionN)
  rw [hmass]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [targetUnclippedRemainingMass]
  field_simp
  ring

/-- Source unswept probability mass, expressed as rank area divided by strip width. -/
theorem rankStripLaw_real_sourceCutComplement
    {p x : ℝ} (hn : 0 < n)
    (hsection0 : ∀ u : UnitMark, 0 ≤ sourceBoundary p x u)
    (hsectionN : ∀ u : UnitMark, sourceBoundary p x u ≤ n) :
    (rankStripLaw n : Measure (ℝ × UnitMark)).real
        (RelativeVC.sourceCutComplementSet p x) =
      sourceUnclippedRemainingMass n p x / n := by
  have hmeas : MeasurableSet
      (RelativeVC.errorSet (RelativeVC.sourceCutEval (p, x))
        RelativeVC.falseCutTarget) :=
    RelativeVC.measurableSet_errorSet
      (RelativeVC.measurable_sourceCutClass _ ⟨p, x, rfl⟩)
      RelativeVC.measurable_falseCutTarget
  rw [RelativeVC.sourceCutComplementSet_eq_errorSet_compl,
    probReal_compl_eq_one_sub hmeas]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (eq_div_iff hnreal).2
  simpa only [mul_comm] using
    rankStripLaw_source_complement_mass hn hsection0 hsectionN

/-- Target unswept probability mass, expressed as rank area divided by strip width. -/
theorem rankStripLaw_real_targetCutComplement
    {p x : ℝ} (hn : 0 < n)
    (hsection0 : ∀ v : UnitMark, 0 ≤ targetBoundary p x v)
    (hsectionN : ∀ v : UnitMark, targetBoundary p x v ≤ n) :
    (rankStripLaw n : Measure (ℝ × UnitMark)).real
        (RelativeVC.targetCutComplementSet p x) =
      targetUnclippedRemainingMass n p x / n := by
  have hmeas : MeasurableSet
      (RelativeVC.errorSet (RelativeVC.targetCutEval (p, x))
        RelativeVC.falseCutTarget) :=
    RelativeVC.measurableSet_errorSet
      (RelativeVC.measurable_targetCutClass _ ⟨p, x, rfl⟩)
      RelativeVC.measurable_falseCutTarget
  rw [RelativeVC.targetCutComplementSet_eq_errorSet_compl,
    probReal_compl_eq_one_sub hmeas]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (eq_div_iff hnreal).2
  simpa only [mul_comm] using
    rankStripLaw_target_complement_mass hn hsection0 hsectionN

end OTSelector
