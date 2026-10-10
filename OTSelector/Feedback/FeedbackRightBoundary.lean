import OTSelector.Feedback.AdaptiveDeferredDecision
import OTSelector.Feedback.FeedbackRegularityStopping
import OTSelector.Feedback.EndpointTail
import OTSelector.Probability.CountingProcess.FiniteEventCountTop

/-!
# Actual data at the right feedback boundary

This file isolates the data available when the recursive feedback exploration reaches a
deterministic elapsed horizon.  It also defines the future event times obtained by freezing the
height at that boundary.  The deferred-decision theorem is exposed in its mathematically valid
form: a product law on every realized finite-history section, with the continuously valued seen
tuple retained as the outer parameter.

No regular conditional law with respect to the whole revealed filtration is asserted here.  Such
a statement additionally requires a theorem identifying the finite-history sections as a
generating class for the revealed-snapshot sigma algebra.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Boundary state measurable in the revealed filtration -/

/-- Safe height at the deterministic right boundary `x0 + T`. -/
noncomputable def rightBoundaryHeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 T sample

/-- Safe post-jump number of source labels remaining at the right boundary. -/
noncomputable def rightBoundarySourceRemaining
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeSourceRemainingAt hlam0 hlamHalf x0 p0 T sample

/-- Safe post-jump number of target labels remaining at the right boundary. -/
noncomputable def rightBoundaryTargetRemaining
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeTargetRemainingAt hlam0 hlamHalf x0 p0 T sample

/-- Safe integer current at the right boundary, cast to the real count scale. -/
noncomputable def rightBoundaryCurrent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  (safeCurrentAt hlam0 hlamHalf x0 p0 T sample : ℝ)

theorem rightBoundaryHeight_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) :
    StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      (rightBoundaryHeight hlam0 hlamHalf x0 p0 T) := by
  change StronglyMeasurable[
    usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
    (fun sample : FiniteSample n ↦
      safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 T sample)
  exact safeFeedbackHeightAtElapsed_stronglyAdapted
    (n := n) hlam0 hlamHalf x0 p0 T

theorem rightBoundarySourceRemaining_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) :
    StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      (rightBoundarySourceRemaining hlam0 hlamHalf x0 p0 T) := by
  have hpre := (safeSourceRemainingBefore_predictable
    (n := n) hlam0 hlamHalf x0 p0).stronglyAdapted T
  have hN := safeSourceCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf x0 p0
  have hbefore : IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦
        (CountingProcess.countBefore
          (safeSourceCount hlam0 hlamHalf x0 p0) t sample : ℝ)) :=
    CountingProcess.stronglyMeasurable_countBefore hN.stronglyAdapted hN.monotone
  have hcount := safeSourceCount_stronglyAdapted
    (n := n) hlam0 hlamHalf x0 p0 T
  have hsum := hpre.add (hbefore.stronglyAdapted T)
  have hinit : StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      (fun sample : FiniteSample n ↦ safeInitialSourceRemainingReal lam x0 p0 sample) := by
    convert hsum using 1
    funext sample
    simp [safeSourceRemainingBefore]
  change StronglyMeasurable[
    usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
    (fun sample : FiniteSample n ↦
      safeInitialSourceRemainingReal lam x0 p0 sample -
        (safeSourceCount hlam0 hlamHalf x0 p0 T sample : ℝ))
  exact hinit.sub hcount

theorem rightBoundaryTargetRemaining_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) :
    StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      (rightBoundaryTargetRemaining hlam0 hlamHalf x0 p0 T) := by
  have hpre := (safeTargetRemainingBefore_predictable
    (n := n) hlam0 hlamHalf x0 p0).stronglyAdapted T
  have hN := safeTargetCount_isSimpleCountingProcess
    (n := n) hlam0 hlamHalf x0 p0
  have hbefore : IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦
        (CountingProcess.countBefore
          (safeTargetCount hlam0 hlamHalf x0 p0) t sample : ℝ)) :=
    CountingProcess.stronglyMeasurable_countBefore hN.stronglyAdapted hN.monotone
  have hcount := safeTargetCount_stronglyAdapted
    (n := n) hlam0 hlamHalf x0 p0 T
  have hsum := hpre.add (hbefore.stronglyAdapted T)
  have hinit : StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      (fun sample : FiniteSample n ↦ safeInitialTargetRemainingReal lam x0 p0 sample) := by
    convert hsum using 1
    funext sample
    simp [safeTargetRemainingBefore]
  change StronglyMeasurable[
    usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
    (fun sample : FiniteSample n ↦
      safeInitialTargetRemainingReal lam x0 p0 sample -
        (safeTargetCount hlam0 hlamHalf x0 p0 T sample : ℝ))
  exact hinit.sub hcount

theorem rightBoundaryCurrent_stronglyMeasurable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) :
    StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      (rightBoundaryCurrent hlam0 hlamHalf x0 p0 T) := by
  have hK0 : StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      (fun sample : FiniteSample n ↦ (safeK0 lam x0 p0 sample : ℝ)) :=
    (safeK0_stronglyMeasurable_usual_zero
      (n := n) hlam0 hlamHalf x0 p0).mono
        ((usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).mono
          (show (0 : ℝ≥0) ≤ T from bot_le))
  have hsource := safeSourceCount_stronglyAdapted
    (n := n) hlam0 hlamHalf x0 p0 T
  have htarget := safeTargetCount_stronglyAdapted
    (n := n) hlam0 hlamHalf x0 p0 T
  have hsum := (hK0.add hsource).sub htarget
  convert hsum using 1
  funext sample
  rw [rightBoundaryCurrent, safeCurrentAt_eq_K0_add_counts]
  norm_num

/-! ## Frozen-height future events -/

/-- Labels strictly in the source complement at the frozen boundary. -/
noncomputable def rightSourceInitialPattern
    (q : FiniteSample n → ℝ) (xR : ℝ) (sample : FiniteSample n) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ xR < sample.sourcePhase i (q sample)

/-- Labels strictly in the target complement at the frozen boundary. -/
noncomputable def rightTargetInitialPattern
    (q : FiniteSample n → ℝ) (xR : ℝ) (sample : FiniteSample n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ xR < sample.targetPhase j (q sample)

/-- Elapsed crossing time of a source label after freezing the height at `q`.  Labels outside the
strict boundary complement are sent to `top`. -/
noncomputable def rightSourceEventTime
    (q : FiniteSample n → ℝ) (xR : ℝ) (i : Fin n) :
    FiniteSample n → WithTop ℝ≥0 := fun sample ↦
  if xR < sample.sourcePhase i (q sample) then
    ((Real.toNNReal (sample.sourcePhase i (q sample) - xR) : ℝ≥0) : WithTop ℝ≥0)
  else ⊤

/-- Target analogue of `rightSourceEventTime`. -/
noncomputable def rightTargetEventTime
    (q : FiniteSample n → ℝ) (xR : ℝ) (j : Fin n) :
    FiniteSample n → WithTop ℝ≥0 := fun sample ↦
  if xR < sample.targetPhase j (q sample) then
    ((Real.toNNReal (sample.targetPhase j (q sample) - xR) : ℝ≥0) : WithTop ℝ≥0)
  else ⊤

/-- Number of future source crossings attained by elapsed time `t`. -/
noncomputable def rightSourceCount
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) : FiniteSample n → ℕ :=
  CountingProcess.finiteEventCountTop (fun i : Fin n ↦ rightSourceEventTime q xR i) t

/-- Number of future target crossings attained by elapsed time `t`. -/
noncomputable def rightTargetCount
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) : FiniteSample n → ℕ :=
  CountingProcess.finiteEventCountTop (fun j : Fin n ↦ rightTargetEventTime q xR j) t

private theorem measurable_sourcePhase_comp
    {q : FiniteSample n → ℝ} (hq : Measurable q) (i : Fin n) :
    Measurable fun sample : FiniteSample n ↦ sample.sourcePhase i (q sample) := by
  simp only [sourcePhase, sourceSlope]
  exact (measurable_const.mul
    ((FiniteSample.measurable_sourceHeight i).subtype_coe)).add
      (((measurable_const.sub
        ((FiniteSample.measurable_sourceMark i).subtype_coe))).mul hq)

private theorem measurable_targetPhase_comp
    {q : FiniteSample n → ℝ} (hq : Measurable q) (j : Fin n) :
    Measurable fun sample : FiniteSample n ↦ sample.targetPhase j (q sample) := by
  simp only [targetPhase, targetSlope]
  exact (measurable_const.mul
    ((FiniteSample.measurable_targetHeight j).subtype_coe)).sub
      (((measurable_const.add
        ((FiniteSample.measurable_targetMark j).subtype_coe))).mul hq)

theorem measurable_rightSourceInitialPattern
    {q : FiniteSample n → ℝ} (hq : Measurable q) (xR : ℝ) :
    Measurable (rightSourceInitialPattern q xR) := by
  apply measurable_finset_of_mem
  intro i
  simpa [rightSourceInitialPattern] using
    (measurableSet_lt measurable_const (measurable_sourcePhase_comp hq i))

theorem measurable_rightTargetInitialPattern
    {q : FiniteSample n → ℝ} (hq : Measurable q) (xR : ℝ) :
    Measurable (rightTargetInitialPattern q xR) := by
  apply measurable_finset_of_mem
  intro j
  simpa [rightTargetInitialPattern] using
    (measurableSet_lt measurable_const (measurable_targetPhase_comp hq j))

theorem measurable_rightSourceEventTime
    {q : FiniteSample n → ℝ} (hq : Measurable q) (xR : ℝ) (i : Fin n) :
    Measurable (rightSourceEventTime q xR i) := by
  let phase : FiniteSample n → ℝ := fun sample ↦ sample.sourcePhase i (q sample)
  have hphase : Measurable phase := measurable_sourcePhase_comp hq i
  have hset : MeasurableSet {sample : FiniteSample n | xR < phase sample} :=
    measurableSet_lt measurable_const hphase
  have hbranch : Measurable fun sample : FiniteSample n ↦
      ((Real.toNNReal (phase sample - xR) : ℝ≥0) : WithTop ℝ≥0) :=
    Measurable.withTop_coe (measurable_real_toNNReal.comp (hphase.sub measurable_const))
  unfold rightSourceEventTime
  exact Measurable.ite hset hbranch measurable_const

theorem measurable_rightTargetEventTime
    {q : FiniteSample n → ℝ} (hq : Measurable q) (xR : ℝ) (j : Fin n) :
    Measurable (rightTargetEventTime q xR j) := by
  let phase : FiniteSample n → ℝ := fun sample ↦ sample.targetPhase j (q sample)
  have hphase : Measurable phase := measurable_targetPhase_comp hq j
  have hset : MeasurableSet {sample : FiniteSample n | xR < phase sample} :=
    measurableSet_lt measurable_const hphase
  have hbranch : Measurable fun sample : FiniteSample n ↦
      ((Real.toNNReal (phase sample - xR) : ℝ≥0) : WithTop ℝ≥0) :=
    Measurable.withTop_coe (measurable_real_toNNReal.comp (hphase.sub measurable_const))
  unfold rightTargetEventTime
  exact Measurable.ite hset hbranch measurable_const

theorem measurable_rightSourceCount
    {q : FiniteSample n → ℝ} (hq : Measurable q) (xR : ℝ) (t : ℝ≥0) :
    Measurable (rightSourceCount q xR t) := by
  unfold rightSourceCount CountingProcess.finiteEventCountTop
  apply measurable_finset_card.comp
  apply measurable_finset_of_mem
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact measurableSet_le (measurable_rightSourceEventTime hq xR i) measurable_const

theorem measurable_rightTargetCount
    {q : FiniteSample n → ℝ} (hq : Measurable q) (xR : ℝ) (t : ℝ≥0) :
    Measurable (rightTargetCount q xR t) := by
  unfold rightTargetCount CountingProcess.finiteEventCountTop
  apply measurable_finset_card.comp
  apply measurable_finset_of_mem
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact measurableSet_le (measurable_rightTargetEventTime hq xR j) measurable_const

@[simp] theorem rightSourceCount_zero
    (q : FiniteSample n → ℝ) (xR : ℝ) (sample : FiniteSample n) :
    rightSourceCount q xR 0 sample = 0 := by
  apply CountingProcess.finiteEventCountTop_zero
  intro i
  simp only [rightSourceEventTime]
  split_ifs with h
  · exact Or.inr (WithTop.coe_pos.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr h)))
  · exact Or.inl rfl

@[simp] theorem rightTargetCount_zero
    (q : FiniteSample n → ℝ) (xR : ℝ) (sample : FiniteSample n) :
    rightTargetCount q xR 0 sample = 0 := by
  apply CountingProcess.finiteEventCountTop_zero
  intro j
  simp only [rightTargetEventTime]
  split_ifs with h
  · exact Or.inr (WithTop.coe_pos.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr h)))
  · exact Or.inl rfl

/-! ## The valid deferred-decision statement at a right boundary -/

/-- On every realized deterministic-coordinate history section, the labels not yet exposed at
the boundary have the product of their one-label laws conditioned to their strict complements.
This is the exact reusable content of the deferred-decision argument before the separate
section-to-filtration monotone-class step. -/
theorem rightBoundary_unseenTupleLaw_cond_historySection_eq_pi
    (reference : FiniteSample n) {lam x0 p0 xR : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history xR) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    (feedbackUnseenTupleLaw S)[|
        {unseen | HistoryAtCoordinate
          (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
          lam x0 p0 sourcePattern targetPattern history xR}] =
      Measure.pi fun label : feedbackUnseenFinset S ↦
        (unitSquareUniform : Measure MarkedHeight)[|
          feedbackLabelRemainingSetAt lam terminal xR
            (label : FeedbackLabel n)] := by
  exact feedbackUnseenTupleLaw_cond_historySection_eq_pi
    reference hlam0 hlamHalf href

end FiniteSample

end OTSelector
