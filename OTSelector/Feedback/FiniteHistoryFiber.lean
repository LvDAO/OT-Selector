import OTSelector.Feedback.FiniteHistoryGeometry
import OTSelector.Feedback.ForcedHistoryLength
import OTSelector.Feedback.RecursiveIntersectionBridge
import OTSelector.Feedback.SelectionStability
import OTSelector.Basic.UnitUniformOpenPos

/-!
# Fibres of a finite feedback history

This module gives the deterministic fibre used by the adaptive deferred-decision argument.  The
revealed coordinates are represented by equality on the labels seen in the terminal scheduled
state.  Every other labelled point is required to lie in the corresponding terminal remaining
region.  No conditional law or filtration statement is bundled into this definition.
-/

open Set

namespace OTSelector

variable {n : ℕ}

/-! ## Raw one-point remaining regions -/

/-- Source remaining region in the unscaled iid marked-point coordinates. -/
def sourceRawRemainingSet (n : ℕ) (p x : ℝ) : Set MarkedHeight :=
  {z | x < (n : ℝ) * (z.1 : ℝ) + p * (1 - (z.2 : ℝ))}

/-- Target remaining region in the unscaled iid marked-point coordinates. -/
def targetRawRemainingSet (n : ℕ) (p x : ℝ) : Set MarkedHeight :=
  {z | x < (n : ℝ) * (z.1 : ℝ) - p * (1 + (z.2 : ℝ))}

theorem isOpen_sourceRawRemainingSet (n : ℕ) (p x : ℝ) :
    IsOpen (sourceRawRemainingSet n p x) := by
  have hheight : Continuous fun z : MarkedHeight ↦ (n : ℝ) * (z.1 : ℝ) :=
    continuous_const.mul (continuous_subtype_val.comp continuous_fst)
  have hmark : Continuous fun z : MarkedHeight ↦ p * (1 - (z.2 : ℝ)) :=
    continuous_const.mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
  exact isOpen_lt continuous_const (hheight.add hmark)

theorem isOpen_targetRawRemainingSet (n : ℕ) (p x : ℝ) :
    IsOpen (targetRawRemainingSet n p x) := by
  have hheight : Continuous fun z : MarkedHeight ↦ (n : ℝ) * (z.1 : ℝ) :=
    continuous_const.mul (continuous_subtype_val.comp continuous_fst)
  have hmark : Continuous fun z : MarkedHeight ↦ p * (1 + (z.2 : ℝ)) :=
    continuous_const.mul
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))
  exact isOpen_lt continuous_const (hheight.sub hmark)

theorem mem_sourceRawRemainingSet_iff (sample : FiniteSample n)
    (state : FeedbackStepState n) (lam : ℝ) (i : Fin n) :
    sample.sourcePoint i ∈ sourceRawRemainingSet n state.p state.x ↔
      rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
        sourceRemainingSet (n : ℝ)
          (segmentCurve state.x state.p (state.slope lam)) state.x := by
  have hstrip : 0 ≤ (n : ℝ) * (sample.sourceHeight i : ℝ) ∧
      (n : ℝ) * (sample.sourceHeight i : ℝ) ≤ (n : ℝ) := by
    constructor
    · exact mul_nonneg (Nat.cast_nonneg n) (sample.sourceHeight i).property.1
    · nlinarith [mul_nonneg (Nat.cast_nonneg n)
        (sub_nonneg.mpr (sample.sourceHeight i).property.2)]
  simp [sourceRawRemainingSet, sourceRemainingSet, sourceSwept, rankStripMap,
    rankCoordinateMap, FiniteSample.sourcePoint, segmentCurve, hstrip, mul_comm]

theorem mem_targetRawRemainingSet_iff (sample : FiniteSample n)
    (state : FeedbackStepState n) (lam : ℝ) (j : Fin n) :
    sample.targetPoint j ∈ targetRawRemainingSet n state.p state.x ↔
      rankStripMap (n : ℝ) (sample.targetPoint j) ∈
        targetRemainingSet (n : ℝ)
          (segmentCurve state.x state.p (state.slope lam)) state.x := by
  have hstrip : 0 ≤ (n : ℝ) * (sample.targetHeight j : ℝ) ∧
      (n : ℝ) * (sample.targetHeight j : ℝ) ≤ (n : ℝ) := by
    constructor
    · exact mul_nonneg (Nat.cast_nonneg n) (sample.targetHeight j).property.1
    · nlinarith [mul_nonneg (Nat.cast_nonneg n)
        (sub_nonneg.mpr (sample.targetHeight j).property.2)]
  simp [targetRawRemainingSet, targetRemainingSet, targetSwept, rankStripMap,
    rankCoordinateMap, FiniteSample.targetPoint, segmentCurve, hstrip, mul_comm]
  constructor <;> intro h <;> linarith

/-- A witnessed source remaining region has strictly positive one-point product mass. -/
theorem unitSquareUniform_sourceRawRemainingSet_pos
    {n : ℕ} {p x : ℝ} {z : MarkedHeight}
    (hz : z ∈ sourceRawRemainingSet n p x) :
    0 < (unitSquareUniform : MeasureTheory.Measure MarkedHeight)
      (sourceRawRemainingSet n p x) := by
  let _ := unitSquareUniform_isOpenPosMeasure
  exact (isOpen_sourceRawRemainingSet n p x).measure_pos _ ⟨z, hz⟩

/-- A witnessed target remaining region has strictly positive one-point product mass. -/
theorem unitSquareUniform_targetRawRemainingSet_pos
    {n : ℕ} {p x : ℝ} {z : MarkedHeight}
    (hz : z ∈ targetRawRemainingSet n p x) :
    0 < (unitSquareUniform : MeasureTheory.Measure MarkedHeight)
      (targetRawRemainingSet n p x) := by
  let _ := unitSquareUniform_isOpenPosMeasure
  exact (isOpen_targetRawRemainingSet n p x).measure_pos _ ⟨z, hz⟩

/-! ## The deterministic fibre -/

/-- Two samples agree on every labelled point recorded in a feedback state. -/
def AgreesOnStateSeen (state : FeedbackStepState n)
    (reference sample : FiniteSample n) : Prop :=
  (∀ i, i ∈ state.seenSource →
      reference.sourcePoint i = sample.sourcePoint i) ∧
    ∀ j, j ∈ state.seenTarget →
      reference.targetPoint j = sample.targetPoint j

/-- All labels not recorded in a state lie in its source or target remaining region. -/
def LiesInStateRemaining (lam : ℝ) (state : FeedbackStepState n)
    (sample : FiniteSample n) : Prop :=
  (∀ i, i ∉ state.seenSource →
      rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
        sourceRemainingSet (n : ℝ)
          (segmentCurve state.x state.p (state.slope lam)) state.x) ∧
    ∀ j, j ∉ state.seenTarget →
      rankStripMap (n : ℝ) (sample.targetPoint j) ∈
        targetRemainingSet (n : ℝ)
          (segmentCurve state.x state.p (state.slope lam)) state.x

/-- An actually unseen source label witnesses positive mass of the source remaining region. -/
theorem LiesInStateRemaining.source_mass_pos
    {lam : ℝ} {state : FeedbackStepState n} {sample : FiniteSample n}
    (hremaining : LiesInStateRemaining lam state sample)
    {i : Fin n} (hi : i ∉ state.seenSource) :
    0 < (unitSquareUniform : MeasureTheory.Measure MarkedHeight)
      (sourceRawRemainingSet n state.p state.x) := by
  apply unitSquareUniform_sourceRawRemainingSet_pos
  exact (mem_sourceRawRemainingSet_iff sample state lam i).2 (hremaining.1 i hi)

/-- An actually unseen target label witnesses positive mass of the target remaining region. -/
theorem LiesInStateRemaining.target_mass_pos
    {lam : ℝ} {state : FeedbackStepState n} {sample : FiniteSample n}
    (hremaining : LiesInStateRemaining lam state sample)
    {j : Fin n} (hj : j ∉ state.seenTarget) :
    0 < (unitSquareUniform : MeasureTheory.Measure MarkedHeight)
      (targetRawRemainingSet n state.p state.x) := by
  apply unitSquareUniform_targetRawRemainingSet_pos
  exact (mem_targetRawRemainingSet_iff sample state lam j).2 (hremaining.2 j hj)

/-- The deterministic fibre over the terminal state of a fixed labelled history. -/
def FiniteHistoryFibre (reference sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) : Prop :=
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  AgreesOnStateSeen terminal reference sample ∧
    LiesInStateRemaining lam terminal sample

/-! ## Phase inequalities along a spacelike graph -/

namespace FeedbackGraph

variable {lam : ℝ} (graph : FeedbackGraph lam)

/-- Positivity of a source phase at a later coordinate propagates to every earlier coordinate. -/
theorem sourcePhase_gt_of_le (sample : FiniteSample n) (i : Fin n)
    {x y : ℝ} (hxy : x ≤ y)
    (hy : y < sample.sourcePhase i (graph.curve y)) :
    x < sample.sourcePhase i (graph.curve x) := by
  have hmono := graph.strictMono_sourceTransform (sample.sourceSlope_mem i)
  have htransform :
      x - sample.sourceSlope i * graph.curve x ≤
        y - sample.sourceSlope i * graph.curve y :=
    hmono.monotone hxy
  simp only [FiniteSample.sourcePhase] at hy ⊢
  linarith

/-- Positivity of a target phase at a later coordinate propagates to every earlier coordinate. -/
theorem targetPhase_gt_of_le (sample : FiniteSample n) (j : Fin n)
    {x y : ℝ} (hxy : x ≤ y)
    (hy : y < sample.targetPhase j (graph.curve y)) :
    x < sample.targetPhase j (graph.curve x) := by
  have hmono := graph.strictMono_targetTransform (sample.targetSlope_mem j)
  have htransform :
      x + sample.targetSlope j * graph.curve x ≤
        y + sample.targetSlope j * graph.curve y :=
    hmono.monotone hxy
  simp only [FiniteSample.targetPhase] at hy ⊢
  linarith

end FeedbackGraph

/-! ## Membership and agreement bridges -/

theorem sourcePhase_gt_of_mem_sourceRemainingSet
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n)
    (hi : rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
      sourceRemainingSet (n : ℝ)
        (segmentCurve state.x state.p (state.slope lam)) state.x) :
    state.x < sample.sourcePhase i state.p := by
  rcases hi with ⟨_, hi⟩
  simp only [sourceSwept, mem_compl_iff, mem_ofPred_eq] at hi
  have hcurve : segmentCurve state.x state.p (state.slope lam) state.x = state.p := by
    simp [segmentCurve]
  rw [hcurve] at hi
  simpa [FiniteSample.sourcePhase, FiniteSample.sourcePoint, rankCoordinateMap,
    FiniteSample.sourceSlope, mul_comm] using lt_of_not_ge hi

theorem targetPhase_gt_of_mem_targetRemainingSet
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n)
    (hj : rankStripMap (n : ℝ) (sample.targetPoint j) ∈
      targetRemainingSet (n : ℝ)
        (segmentCurve state.x state.p (state.slope lam)) state.x) :
    state.x < sample.targetPhase j state.p := by
  rcases hj with ⟨_, hj⟩
  simp only [targetSwept, mem_compl_iff, mem_ofPred_eq] at hj
  have hcurve : segmentCurve state.x state.p (state.slope lam) state.x = state.p := by
    simp [segmentCurve]
  rw [hcurve] at hj
  simpa [FiniteSample.targetPhase, FiniteSample.targetPoint, rankCoordinateMap,
    FiniteSample.targetSlope, mul_comm] using lt_of_not_ge hj

namespace FeedbackStepState

/-- A label coordinate depends on the sample only through that label's marked point. -/
theorem labelCoordinate_eq_of_feedbackLabelPoint_eq
    (reference sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (label : FeedbackLabel n)
    (hpoint : feedbackLabelPoint label reference = feedbackLabelPoint label sample) :
    state.labelCoordinate reference lam label = state.labelCoordinate sample lam label := by
  cases label with
  | inl i =>
      have hheight : reference.sourceHeight i = sample.sourceHeight i :=
        congrArg Prod.fst hpoint
      have hmark : reference.sourceMark i = sample.sourceMark i :=
        congrArg Prod.snd hpoint
      simp [labelCoordinate, sourceCoordinate, FiniteSample.sourceSlope, hheight, hmark]
  | inr j =>
      have hheight : reference.targetHeight j = sample.targetHeight j :=
        congrArg Prod.fst hpoint
      have hmark : reference.targetMark j = sample.targetMark j :=
        congrArg Prod.snd hpoint
      simp [labelCoordinate, targetCoordinate, FiniteSample.targetSlope, hheight, hmark]

end FeedbackStepState

namespace FiniteSample

/-- Every bounded recursive state lies on the globally glued feedback graph. -/
theorem feedbackGraph_curve_eq_state_of_feedbackState_eq
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m ≤ 2 * n) (state : FeedbackStepState n)
    (hstate : sample.feedbackState lam x0 p0 m = state) :
    (sample.feedbackGraph hlam0 hlamHalf x0 p0).curve state.x = state.p := by
  have hcurve := sample.feedbackCurve_eq_feedbackKnotValue_at_knot
    hlam0 hlamHalf x0 p0 hm
  change sample.feedbackCurve lam x0 p0
      (sample.feedbackState lam x0 p0 m).x =
    (sample.feedbackState lam x0 p0 m).p at hcurve
  rw [hstate] at hcurve
  exact hcurve

end FiniteSample

private theorem historyPoints_eq_of_agreesOn_terminal
    (reference sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hagrees : AgreesOnStateSeen
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
      reference sample) :
    ∀ label, label ∈ history →
      feedbackLabelPoint label reference = feedbackLabelPoint label sample := by
  intro label hlabel
  cases label with
  | inl i =>
      exact hagrees.1 i
        (FiniteSample.scheduledState_mem_seenSource_of_mem_history reference lam x0 p0
          sourcePattern targetPattern history i hlabel)
  | inr j =>
      exact hagrees.2 j
        (FiniteSample.scheduledState_mem_seenTarget_of_mem_history reference lam x0 p0
          sourcePattern targetPattern history j hlabel)

/-- With fixed revealed points, two realizations of the same branch have the same terminal state. -/
theorem scheduledState_eq_of_agreesOn_terminal
    (reference sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hagrees : AgreesOnStateSeen
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
      reference sample) :
    reference.scheduledState lam x0 p0 sourcePattern targetPattern history =
      sample.scheduledState lam x0 p0 sourcePattern targetPattern history := by
  exact FiniteSample.scheduledState_eq_of_history_points_eq reference sample lam x0 p0
    sourcePattern targetPattern history
    (historyPoints_eq_of_agreesOn_terminal reference sample lam x0 p0
      sourcePattern targetPattern history hagrees)

/-! ## Recovering the initial branch from a fibre -/

/-- Fibre membership forces the candidate sample to have the same prescribed initial pattern. -/
theorem initialFeedbackState_eq_forcedInitialState_of_mem_fibre
    (reference sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (hfibre : FiniteHistoryFibre reference sample lam x0 p0
      sourcePattern targetPattern history) :
    sample.initialFeedbackState x0 p0 =
      FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern := by
  let terminal :=
    reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  let graph := reference.feedbackGraph hlam0 hlamHalf x0 p0
  have hlen : history.length ≤ 2 * n :=
    href.2.length_le_two_mul reference lam
  have hterminalActual :
      reference.feedbackState lam x0 p0 history.length = terminal := by
    exact FiniteSample.feedbackState_eq_scheduledState_of_history reference lam x0 p0
      sourcePattern targetPattern history href.1 href.2
  have hcurveTerminal : graph.curve terminal.x = terminal.p := by
    have hcurve := reference.feedbackCurve_eq_feedbackKnotValue_at_knot
      hlam0 hlamHalf x0 p0 hlen
    change reference.feedbackCurve lam x0 p0
        (reference.feedbackState lam x0 p0 history.length).x =
      (reference.feedbackState lam x0 p0 history.length).p at hcurve
    rw [hterminalActual] at hcurve
    simpa [graph] using hcurve
  have hcurveInitial : graph.curve x0 = p0 := by
    simpa [graph] using reference.feedbackCurve_at_x0 hlam0 hlamHalf x0 p0
  have hx0terminal : x0 ≤ terminal.x := by
    have hx := reference.feedbackState_x_mono hlam0 hlamHalf x0 p0
      (Nat.zero_le history.length)
    change (reference.feedbackState lam x0 p0 0).x ≤
      (reference.feedbackState lam x0 p0 history.length).x at hx
    rw [FiniteSample.feedbackState_zero, href.1, hterminalActual] at hx
    simpa [FiniteSample.forcedInitialState] using hx
  have hsourcePattern : reference.initialSeenSource x0 p0 = sourcePattern := by
    exact congrArg FeedbackStepState.seenSource href.1
  have htargetPattern : reference.initialSeenTarget x0 p0 = targetPattern := by
    exact congrArg FeedbackStepState.seenTarget href.1
  change AgreesOnStateSeen terminal reference sample ∧
    LiesInStateRemaining lam terminal sample at hfibre
  have hsource : sample.initialSeenSource x0 p0 = sourcePattern := by
    classical
    ext i
    by_cases hi : i ∈ terminal.seenSource
    · have hpoint := hfibre.1.1 i hi
      have hheight : reference.sourceHeight i = sample.sourceHeight i :=
        congrArg Prod.fst hpoint
      have hmark : reference.sourceMark i = sample.sourceMark i :=
        congrArg Prod.snd hpoint
      have hslope : reference.sourceSlope i = sample.sourceSlope i := by
        simp [FiniteSample.sourceSlope, hmark]
      simp only [FiniteSample.initialSeenSource, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [← hheight, ← hslope]
      have hmem : i ∈ reference.initialSeenSource x0 p0 ↔ i ∈ sourcePattern := by
        rw [hsourcePattern]
      simpa only [FiniteSample.initialSeenSource, Finset.mem_filter,
        Finset.mem_univ, true_and] using hmem
    · have hipattern : i ∉ sourcePattern := by
        intro hipattern
        apply hi
        dsimp [terminal]
        rw [FiniteSample.scheduledState_seenSource]
        exact Finset.mem_union_left _ hipattern
      have hremaining := hfibre.2.1 i hi
      have hphaseTerminal :=
        sourcePhase_gt_of_mem_sourceRemainingSet sample lam terminal i hremaining
      have hphaseGraph :
          terminal.x < sample.sourcePhase i (graph.curve terminal.x) := by
        rw [hcurveTerminal]
        exact hphaseTerminal
      have hphaseInitial :=
        graph.sourcePhase_gt_of_le sample i hx0terminal hphaseGraph
      rw [hcurveInitial] at hphaseInitial
      have hinitial : i ∉ sample.initialSeenSource x0 p0 := by
        simp only [FiniteSample.initialSeenSource, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact not_le_of_gt hphaseInitial
      simp [hinitial, hipattern]
  have htarget : sample.initialSeenTarget x0 p0 = targetPattern := by
    classical
    ext j
    by_cases hj : j ∈ terminal.seenTarget
    · have hpoint := hfibre.1.2 j hj
      have hheight : reference.targetHeight j = sample.targetHeight j :=
        congrArg Prod.fst hpoint
      have hmark : reference.targetMark j = sample.targetMark j :=
        congrArg Prod.snd hpoint
      have hslope : reference.targetSlope j = sample.targetSlope j := by
        simp [FiniteSample.targetSlope, hmark]
      simp only [FiniteSample.initialSeenTarget, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [← hheight, ← hslope]
      have hmem : j ∈ reference.initialSeenTarget x0 p0 ↔ j ∈ targetPattern := by
        rw [htargetPattern]
      simpa only [FiniteSample.initialSeenTarget, Finset.mem_filter,
        Finset.mem_univ, true_and] using hmem
    · have hjpattern : j ∉ targetPattern := by
        intro hjpattern
        apply hj
        dsimp [terminal]
        rw [FiniteSample.scheduledState_seenTarget]
        exact Finset.mem_union_left _ hjpattern
      have hremaining := hfibre.2.2 j hj
      have hphaseTerminal :=
        targetPhase_gt_of_mem_targetRemainingSet sample lam terminal j hremaining
      have hphaseGraph :
          terminal.x < sample.targetPhase j (graph.curve terminal.x) := by
        rw [hcurveTerminal]
        exact hphaseTerminal
      have hphaseInitial :=
        graph.targetPhase_gt_of_le sample j hx0terminal hphaseGraph
      rw [hcurveInitial] at hphaseInitial
      have hinitial : j ∉ sample.initialSeenTarget x0 p0 := by
        simp only [FiniteSample.initialSeenTarget, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact not_le_of_gt hphaseInitial
      simp [hinitial, hjpattern]
  simp [FiniteSample.initialFeedbackState, FiniteSample.initialFeedbackCurrent,
    FiniteSample.forcedInitialState, hsource, htarget]

/-! ## The forward half of the fibre identity -/

/-- A branch with the same revealed coordinates as a reference branch lies in its history fibre. -/
theorem finiteHistoryFibre_of_historyBranch_of_agrees
    (reference sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hsample : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history)
    (hagrees : AgreesOnStateSeen
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
      reference sample) :
    FiniteHistoryFibre reference sample lam x0 p0 sourcePattern targetPattern history := by
  let referenceTerminal :=
    reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  let sampleTerminal :=
    sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hterminal : referenceTerminal = sampleTerminal := by
    exact scheduledState_eq_of_agreesOn_terminal reference sample lam x0 p0
      sourcePattern targetPattern history hagrees
  refine ⟨hagrees, ?_⟩
  constructor
  · intro i hi
    have hi' : i ∉ sampleTerminal.seenSource := by
      rw [← hterminal]
      exact hi
    have hmem := HistoryBranch.sourcePoint_mem_sourceRemainingSet sample
      hlam0 hlamHalf hsample i hi'
    simpa [referenceTerminal, sampleTerminal, hterminal] using hmem
  · intro j hj
    have hj' : j ∉ sampleTerminal.seenTarget := by
      rw [← hterminal]
      exact hj
    have hmem := HistoryBranch.targetPoint_mem_targetRemainingSet sample
      hlam0 hlamHalf hsample j hj'
    simpa [referenceTerminal, sampleTerminal, hterminal] using hmem

/-- Every realized branch belongs to the fibre over its own revealed coordinates. -/
theorem HistoryBranch.mem_finiteHistoryFibre
    (sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history) :
    FiniteHistoryFibre sample sample lam x0 p0 sourcePattern targetPattern history := by
  apply finiteHistoryFibre_of_historyBranch_of_agrees sample sample hlam0 hlamHalf hbranch
  exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-! ## The reverse half of the fibre identity -/

private theorem sourceCoordinate_gt_of_terminal_remaining
    (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)
    (state next terminal : FeedbackStepState n) (i : Fin n)
    (hnextTerminal : next.x ≤ terminal.x)
    (hcurveNext : graph.curve next.x = next.p)
    (hcurveTerminal : graph.curve terminal.x = terminal.p)
    (hsegmentNext :
      segmentCurve state.x state.p (state.slope lam) next.x = next.p)
    (hi : rankStripMap (n : ℝ) (sample.sourcePoint i) ∈
      sourceRemainingSet (n : ℝ)
        (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x) :
    next.x < state.sourceCoordinate sample lam i := by
  have hterminal := sourcePhase_gt_of_mem_sourceRemainingSet sample lam terminal i hi
  have hterminalGraph :
      terminal.x < sample.sourcePhase i (graph.curve terminal.x) := by
    rw [hcurveTerminal]
    exact hterminal
  have hnextGraph := graph.sourcePhase_gt_of_le sample i hnextTerminal hterminalGraph
  have hnextPhase : next.x < sample.sourcePhase i next.p := by
    rw [← hcurveNext]
    exact hnextGraph
  have hsegmentPhase :
      next.x < (n : ℝ) * (sample.sourceHeight i : ℝ) +
        sample.sourceSlope i *
          segmentCurve state.x state.p (state.slope lam) next.x := by
    simpa [FiniteSample.sourcePhase, hsegmentNext] using hnextPhase
  have ha := sample.sourceSlope_mem i
  have hcross := (x_lt_sourceSegmentCrossing_iff ha.1 ha.2
    (abs_feedbackSlope_le (k := (state.current : ℝ)) graph.lam_nonneg)
    graph.lam_nonneg graph.lam_lt_half).2 hsegmentPhase
  simpa [FeedbackStepState.sourceCoordinate, FeedbackStepState.slope] using hcross

private theorem targetCoordinate_gt_of_terminal_remaining
    (sample : FiniteSample n) {lam : ℝ} (graph : FeedbackGraph lam)
    (state next terminal : FeedbackStepState n) (j : Fin n)
    (hnextTerminal : next.x ≤ terminal.x)
    (hcurveNext : graph.curve next.x = next.p)
    (hcurveTerminal : graph.curve terminal.x = terminal.p)
    (hsegmentNext :
      segmentCurve state.x state.p (state.slope lam) next.x = next.p)
    (hj : rankStripMap (n : ℝ) (sample.targetPoint j) ∈
      targetRemainingSet (n : ℝ)
        (segmentCurve terminal.x terminal.p (terminal.slope lam)) terminal.x) :
    next.x < state.targetCoordinate sample lam j := by
  have hterminal := targetPhase_gt_of_mem_targetRemainingSet sample lam terminal j hj
  have hterminalGraph :
      terminal.x < sample.targetPhase j (graph.curve terminal.x) := by
    rw [hcurveTerminal]
    exact hterminal
  have hnextGraph := graph.targetPhase_gt_of_le sample j hnextTerminal hterminalGraph
  have hnextPhase : next.x < sample.targetPhase j next.p := by
    rw [← hcurveNext]
    exact hnextGraph
  have hsegmentPhase :
      next.x < (n : ℝ) * (sample.targetHeight j : ℝ) -
        sample.targetSlope j *
          segmentCurve state.x state.p (state.slope lam) next.x := by
    simpa [FiniteSample.targetPhase, hsegmentNext] using hnextPhase
  have hb := sample.targetSlope_mem j
  have hcross := (x_lt_targetSegmentCrossing_iff hb.1 hb.2
    (abs_feedbackSlope_le (k := (state.current : ℝ)) graph.lam_nonneg)
    graph.lam_nonneg graph.lam_lt_half).2 hsegmentPhase
  simpa [FeedbackStepState.targetCoordinate, FeedbackStepState.slope] using hcross

private theorem forcedHistoryRealizes_transfer_aux
    (reference sample : FiniteSample n) {lam x0 p0 : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (terminal : FeedbackStepState n) (total : ℕ)
    (hlen : total ≤ 2 * n)
    (hterminalActual :
      reference.feedbackState lam x0 p0 total = terminal)
    (hagrees : AgreesOnStateSeen terminal reference sample)
    (hremaining : LiesInStateRemaining lam terminal sample)
    {m : ℕ} {state : FeedbackStepState n}
    (remaining : List (FeedbackLabel n))
    (htotal : m + remaining.length = total)
    (hstate : reference.feedbackState lam x0 p0 m = state)
    (hreal : reference.ForcedHistoryRealizes lam state remaining)
    (hterminalTail :
      terminal = reference.scheduledStateFrom lam state remaining) :
    sample.ForcedHistoryRealizes lam state remaining := by
  induction remaining generalizing m state with
  | nil => trivial
  | cons label tail ih =>
      let next := state.forcedLabelStep reference lam label
      let graph := reference.feedbackGraph hlam0 hlamHalf x0 p0
      have hbase : reference.labelStepRealizes lam state label := hreal.1
      have htail : reference.ForcedHistoryRealizes lam next tail := by
        simpa [next] using hreal.2
      have hstepEq : state.step reference lam = next := by
        cases label with
        | inl i =>
            exact FiniteSample.step_eq_forcedLabelStep_of_source_singleton
              reference lam state i hbase.1 hbase.2
        | inr j =>
            exact FiniteSample.step_eq_forcedLabelStep_of_target_singleton
              reference lam state j hbase.1 hbase.2
      have hnextActual :
          reference.feedbackState lam x0 p0 (m + 1) = next := by
        rw [FiniteSample.feedbackState_succ, hstate, hstepEq]
      have hmnext : m + 1 ≤ total := by
        simp only [List.length_cons] at htotal
        omega
      have hmnextBound : m + 1 ≤ 2 * n := hmnext.trans hlen
      have hnextTerminal : next.x ≤ terminal.x := by
        have hmono := reference.feedbackState_x_mono hlam0 hlamHalf x0 p0 hmnext
        change (reference.feedbackState lam x0 p0 (m + 1)).x ≤
          (reference.feedbackState lam x0 p0 total).x at hmono
        rw [hnextActual, hterminalActual] at hmono
        exact hmono
      have hcurveNext : graph.curve next.x = next.p := by
        simpa [graph] using
          reference.feedbackGraph_curve_eq_state_of_feedbackState_eq
            hlam0 hlamHalf x0 p0 hmnextBound next hnextActual
      have hcurveTerminal : graph.curve terminal.x = terminal.p := by
        simpa [graph] using
          reference.feedbackGraph_curve_eq_state_of_feedbackState_eq
            hlam0 hlamHalf x0 p0 hlen terminal hterminalActual
      have hterminalNext :
          terminal = reference.scheduledStateFrom lam next tail := by
        simpa [FiniteSample.scheduledStateFrom, next] using hterminalTail
      have hsegmentNext :
          segmentCurve state.x state.p (state.slope lam) next.x = next.p := by
        cases label <;> rfl
      have hselectedPoint :
          feedbackLabelPoint label reference = feedbackLabelPoint label sample := by
        cases label with
        | inl i =>
            apply hagrees.1 i
            rw [hterminalNext, FiniteSample.scheduledStateFrom_seenSource]
            exact Finset.mem_union_left _ (by simp [next])
        | inr j =>
            apply hagrees.2 j
            rw [hterminalNext, FiniteSample.scheduledStateFrom_seenTarget]
            exact Finset.mem_union_left _ (by simp [next])
      have hselectedCoordinate :=
        FeedbackStepState.labelCoordinate_eq_of_feedbackLabelPoint_eq
          reference sample lam state label hselectedPoint
      have hsampleStep : sample.labelStepRealizes lam state label := by
        cases label with
        | inl i =>
            have hselectedSample :
                state.sourceCoordinate sample lam i = next.x := by
              simpa [next, FeedbackStepState.labelCoordinate,
                FeedbackStepState.forcedLabelStep] using hselectedCoordinate.symm
            apply FeedbackStepState.labelStepRealizes_of_source_unique_min
            · have hiNew : i ∈ state.newSource reference lam := by
                rw [hbase.1]
                simp
              exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hiNew).1).2
            · intro k hk hki
              by_cases hkTerminal : k ∈ terminal.seenSource
              · have hpoint := hagrees.1 k hkTerminal
                have hcoord :=
                  FeedbackStepState.labelCoordinate_eq_of_feedbackLabelPoint_eq
                    reference sample lam state (Sum.inl k) hpoint
                have hrefLt :=
                  FeedbackStepState.labelStepRealizes_source_lt_source_of_ne
                    reference lam state i k hbase hk hki
                calc
                  state.sourceCoordinate sample lam i =
                      state.sourceCoordinate reference lam i := by
                    simpa [FeedbackStepState.labelCoordinate] using
                      hselectedCoordinate.symm
                  _ < state.sourceCoordinate reference lam k := hrefLt
                  _ = state.sourceCoordinate sample lam k := by
                    simpa [FeedbackStepState.labelCoordinate] using hcoord
              · have hfuture := sourceCoordinate_gt_of_terminal_remaining
                  sample graph state next terminal k hnextTerminal hcurveNext
                  hcurveTerminal hsegmentNext (hremaining.1 k hkTerminal)
                simpa [FeedbackStepState.labelCoordinate] using
                  hselectedSample.trans_lt hfuture
            · intro j hj
              by_cases hjTerminal : j ∈ terminal.seenTarget
              · have hpoint := hagrees.2 j hjTerminal
                have hcoord :=
                  FeedbackStepState.labelCoordinate_eq_of_feedbackLabelPoint_eq
                    reference sample lam state (Sum.inr j) hpoint
                have hrefLt :=
                  FeedbackStepState.labelStepRealizes_source_lt_target
                    reference lam state i hbase j hj
                calc
                  state.sourceCoordinate sample lam i =
                      state.sourceCoordinate reference lam i := by
                    simpa [FeedbackStepState.labelCoordinate] using
                      hselectedCoordinate.symm
                  _ < state.targetCoordinate reference lam j := hrefLt
                  _ = state.targetCoordinate sample lam j := by
                    simpa [FeedbackStepState.labelCoordinate] using hcoord
              · have hfuture := targetCoordinate_gt_of_terminal_remaining
                  sample graph state next terminal j hnextTerminal hcurveNext
                  hcurveTerminal hsegmentNext (hremaining.2 j hjTerminal)
                simpa [FeedbackStepState.labelCoordinate] using
                  hselectedSample.trans_lt hfuture
        | inr j =>
            have hselectedSample :
                state.targetCoordinate sample lam j = next.x := by
              simpa [next, FeedbackStepState.labelCoordinate,
                FeedbackStepState.forcedLabelStep] using hselectedCoordinate.symm
            apply FeedbackStepState.labelStepRealizes_of_target_unique_min
            · have hjNew : j ∈ state.newTarget reference lam := by
                rw [hbase.2]
                simp
              exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hjNew).1).2
            · intro k hk
              by_cases hkTerminal : k ∈ terminal.seenSource
              · have hpoint := hagrees.1 k hkTerminal
                have hcoord :=
                  FeedbackStepState.labelCoordinate_eq_of_feedbackLabelPoint_eq
                    reference sample lam state (Sum.inl k) hpoint
                have hrefLt :=
                  FeedbackStepState.labelStepRealizes_target_lt_source
                    reference lam state j k hbase hk
                calc
                  state.targetCoordinate sample lam j =
                      state.targetCoordinate reference lam j := by
                    simpa [FeedbackStepState.labelCoordinate] using
                      hselectedCoordinate.symm
                  _ < state.sourceCoordinate reference lam k := hrefLt
                  _ = state.sourceCoordinate sample lam k := by
                    simpa [FeedbackStepState.labelCoordinate] using hcoord
              · have hfuture := sourceCoordinate_gt_of_terminal_remaining
                  sample graph state next terminal k hnextTerminal hcurveNext
                  hcurveTerminal hsegmentNext (hremaining.1 k hkTerminal)
                simpa [FeedbackStepState.labelCoordinate] using
                  hselectedSample.trans_lt hfuture
            · intro l hl hlj
              by_cases hlTerminal : l ∈ terminal.seenTarget
              · have hpoint := hagrees.2 l hlTerminal
                have hcoord :=
                  FeedbackStepState.labelCoordinate_eq_of_feedbackLabelPoint_eq
                    reference sample lam state (Sum.inr l) hpoint
                have hrefLt :=
                  FeedbackStepState.labelStepRealizes_target_lt_target_of_ne
                    reference lam state j l hbase hl hlj
                calc
                  state.targetCoordinate sample lam j =
                      state.targetCoordinate reference lam j := by
                    simpa [FeedbackStepState.labelCoordinate] using
                      hselectedCoordinate.symm
                  _ < state.targetCoordinate reference lam l := hrefLt
                  _ = state.targetCoordinate sample lam l := by
                    simpa [FeedbackStepState.labelCoordinate] using hcoord
              · have hfuture := targetCoordinate_gt_of_terminal_remaining
                  sample graph state next terminal l hnextTerminal hcurveNext
                  hcurveTerminal hsegmentNext (hremaining.2 l hlTerminal)
                simpa [FeedbackStepState.labelCoordinate] using
                  hselectedSample.trans_lt hfuture
      refine ⟨hsampleStep, ?_⟩
      have htailSample := ih (m := m + 1) (state := next)
        (by
          simp only [List.length_cons] at htotal
          omega)
        hnextActual htail hterminalNext
      have hnextEq := FeedbackStepState.forcedLabelStep_eq_of_feedbackLabelPoint_eq
        reference sample lam state label hselectedPoint
      simpa [next, hnextEq] using htailSample

/-- Membership in a reference branch fibre forces the candidate sample to realize that branch. -/
theorem historyBranch_of_mem_finiteHistoryFibre
    (reference sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (hfibre : FiniteHistoryFibre reference sample lam x0 p0
      sourcePattern targetPattern history) :
    HistoryBranch sample lam x0 p0 sourcePattern targetPattern history := by
  let terminal :=
    reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hlen : history.length ≤ 2 * n :=
    href.2.length_le_two_mul reference lam
  have hinit := initialFeedbackState_eq_forcedInitialState_of_mem_fibre
    reference sample hlam0 hlamHalf href hfibre
  have hterminalActual :
      reference.feedbackState lam x0 p0 history.length = terminal := by
    exact FiniteSample.feedbackState_eq_scheduledState_of_history reference lam x0 p0
      sourcePattern targetPattern history href.1 href.2
  change AgreesOnStateSeen terminal reference sample ∧
    LiesInStateRemaining lam terminal sample at hfibre
  refine ⟨hinit, ?_⟩
  apply forcedHistoryRealizes_transfer_aux reference sample hlam0 hlamHalf
    terminal history.length hlen hterminalActual hfibre.1 hfibre.2
    (m := 0)
    (state := FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern)
    history
  · simp
  · simpa using href.1
  · exact href.2
  · rfl

/-- Exact deterministic fibre identity for a fixed realized reference history. -/
theorem historyBranch_and_agrees_iff_mem_finiteHistoryFibre
    (reference sample : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history) :
    (HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      AgreesOnStateSeen
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
        reference sample) ↔
      FiniteHistoryFibre reference sample lam x0 p0
        sourcePattern targetPattern history := by
  constructor
  · rintro ⟨hsample, hagrees⟩
    exact finiteHistoryFibre_of_historyBranch_of_agrees
      reference sample hlam0 hlamHalf hsample hagrees
  · intro hfibre
    refine ⟨historyBranch_of_mem_finiteHistoryFibre
      reference sample hlam0 hlamHalf href hfibre, ?_⟩
    exact hfibre.1

end OTSelector
