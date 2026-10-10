import OTSelector.Feedback.FiniteHistoryAt
import OTSelector.Feedback.FiniteHistoryProductSection
import OTSelector.Probability.IndependentRandomRegion
import OTSelector.Probability.PiConditioning

/-!
# Deterministic-coordinate integration for adaptive feedback histories

For a fixed initial pattern, labelled history, and deterministic observation coordinate, the
finite sample is transported through the measurable seen/unseen equivalence.  Its law becomes the
product of the seen-tuple and unseen-tuple laws, so Fubini applies to the actual history cell.

This file does not condition on an exact continuous seen tuple as if it were a positive-measure
atom.  The revealed tuple remains the outer integration variable.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## Product-coordinate history cells -/

/-- The law of the tuple indexed by a fixed set of feedback labels. -/
noncomputable def feedbackTupleLaw (S : Finset (FeedbackLabel n)) :
    Measure (S → MarkedHeight) :=
  Measure.pi fun _ : S ↦ (unitSquareUniform : Measure MarkedHeight)

/-- The law of the tuple indexed by the complement of a fixed label set. -/
noncomputable def feedbackUnseenTupleLaw (S : Finset (FeedbackLabel n)) :
    Measure (feedbackUnseenFinset S → MarkedHeight) :=
  Measure.pi fun _ : feedbackUnseenFinset S ↦
    (unitSquareUniform : Measure MarkedHeight)

@[fun_prop]
theorem measurable_finiteSampleSeenUnseenMerge (S : Finset (FeedbackLabel n)) :
    Measurable fun parts :
        (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) ↦
      finiteSampleSeenUnseenMerge S parts.1 parts.2 := by
  change Measurable ((finiteSampleSeenUnseenMeasurableEquiv S).symm)
  exact (finiteSampleSeenUnseenMeasurableEquiv S).symm.measurable

@[simp]
theorem finiteSampleSeenUnseenMerge_split
    (S : Finset (FeedbackLabel n)) (sample : FiniteSample n) :
    finiteSampleSeenUnseenMerge S
      (feedbackSeenTuple S sample) (feedbackUnseenTuple S sample) = sample := by
  change (finiteSampleSeenUnseenMeasurableEquiv S).symm
    (finiteSampleSeenUnseenMeasurableEquiv S sample) = sample
  exact (finiteSampleSeenUnseenMeasurableEquiv S).symm_apply_apply sample

/-- A deterministic-coordinate history cell written in seen/unseen product coordinates. -/
def historyAtCoordinateProductSet
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (x : ℝ) :
    Set
      ((feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight) ×
        (feedbackUnseenFinset
          (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)) :=
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  {parts | HistoryAtCoordinate
    (finiteSampleSeenUnseenMerge S parts.1 parts.2)
    lam x0 p0 sourcePattern targetPattern history x}

theorem measurableSet_historyAtCoordinateProductSet
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (x : ℝ) :
    MeasurableSet
      (historyAtCoordinateProductSet lam x0 p0 sourcePattern targetPattern history x) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  have hmerge := measurable_finiteSampleSeenUnseenMerge (n := n) S
  have hcell := measurableSet_historyAtCoordinate (n := n)
    lam x0 p0 sourcePattern targetPattern history x
  simpa [historyAtCoordinateProductSet, S] using hmerge hcell

theorem mem_historyAtCoordinateProductSet_iff
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (x : ℝ)
    (parts :
      (feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight) ×
        (feedbackUnseenFinset
          (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)) :
    parts ∈ historyAtCoordinateProductSet lam x0 p0
        sourcePattern targetPattern history x ↔
      HistoryAtCoordinate
        (finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history) parts.1 parts.2)
        lam x0 p0 sourcePattern targetPattern history x := by
  rfl

/-! ## Exact Fubini transport -/

/-- The actual finite-sample history-cell integral equals the iterated seen/unseen product
integral.  The integrand may depend jointly on both tuples. -/
theorem integral_historyAtCoordinate_eq_iterated
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (x : ℝ)
    {F :
      (feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight) ×
        (feedbackUnseenFinset
          (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight) → ℝ}
    (hF : Integrable F
      ((feedbackTupleLaw
        (feedbackTerminalLabelSet sourcePattern targetPattern history)).prod
        (feedbackUnseenTupleLaw
          (feedbackTerminalLabelSet sourcePattern targetPattern history)))) :
    (∫ sample,
        {sample : FiniteSample n |
          HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x}.indicator
          (fun sample ↦ F
            (feedbackSeenTuple
              (feedbackTerminalLabelSet sourcePattern targetPattern history) sample,
             feedbackUnseenTuple
              (feedbackTerminalLabelSet sourcePattern targetPattern history) sample)) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
      ∫ seen, ∫ unseen,
        (historyAtCoordinateProductSet lam x0 p0
          sourcePattern targetPattern history x).indicator F (seen, unseen)
          ∂(feedbackUnseenTupleLaw
            (feedbackTerminalLabelSet sourcePattern targetPattern history))
        ∂(feedbackTupleLaw
          (feedbackTerminalLabelSet sourcePattern targetPattern history)) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let C := historyAtCoordinateProductSet lam x0 p0 sourcePattern targetPattern history x
  have hC : MeasurableSet C := by
    simpa [C] using measurableSet_historyAtCoordinateProductSet (n := n)
      lam x0 p0 sourcePattern targetPattern history x
  have hF' : Integrable F
      ((Measure.map (feedbackSeenTuple S)
        (finiteSampleLaw n : Measure (FiniteSample n))).prod
        (Measure.map (feedbackUnseenTuple S)
          (finiteSampleLaw n : Measure (FiniteSample n)))) := by
    rw [finiteSampleLaw_map_feedbackSeenTuple (n := n) S,
      finiteSampleLaw_map_feedbackUnseenTuple (n := n) S]
    simpa [feedbackTupleLaw, feedbackUnseenTupleLaw, S] using hF
  have htransport := Probability.integral_indepFun_randomRegion_eq_iterated
    (measurable_feedbackSeenTuple S) (measurable_feedbackUnseenTuple S)
    (feedbackSeenTuple_indepFun_feedbackUnseenTuple (n := n) S)
    hC hF'
  rw [finiteSampleLaw_map_feedbackSeenTuple (n := n) S,
    finiteSampleLaw_map_feedbackUnseenTuple (n := n) S] at htransport
  change
    (∫ sample,
      C.indicator F
        (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)
      ∂(finiteSampleLaw n : Measure (FiniteSample n))) = _ at htransport
  rw [show feedbackTupleLaw S =
      Measure.pi (fun _ : S ↦ (unitSquareUniform : Measure MarkedHeight)) from rfl,
    show feedbackUnseenTupleLaw S =
      Measure.pi (fun _ : feedbackUnseenFinset S ↦
        (unitSquareUniform : Measure MarkedHeight)) from rfl]
  rw [← htransport]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun sample ↦ by
    by_cases hcell :
        HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x
    · have hpair :
          (feedbackSeenTuple S sample, feedbackUnseenTuple S sample) ∈ C := by
        change HistoryAtCoordinate
          (finiteSampleSeenUnseenMerge S
            (feedbackSeenTuple S sample) (feedbackUnseenTuple S sample))
          lam x0 p0 sourcePattern targetPattern history x
        simpa using hcell
      have hmem : sample ∈ {sample : FiniteSample n |
          HistoryAtCoordinate sample lam x0 p0
            sourcePattern targetPattern history x} := hcell
      rw [Set.indicator_of_mem hmem]
      change _ = C.indicator F
        (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)
      rw [Set.indicator_of_mem hpair]
    · have hpair :
          (feedbackSeenTuple S sample, feedbackUnseenTuple S sample) ∉ C := by
        intro hp
        apply hcell
        change HistoryAtCoordinate
          (finiteSampleSeenUnseenMerge S
            (feedbackSeenTuple S sample) (feedbackUnseenTuple S sample))
          lam x0 p0 sourcePattern targetPattern history x at hp
        simpa using hp
      have hmem : sample ∉ {sample : FiniteSample n |
          HistoryAtCoordinate sample lam x0 p0
            sourcePattern targetPattern history x} := hcell
      rw [Set.indicator_of_notMem hmem]
      change (0 : ℝ) = C.indicator F
        (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)
      rw [Set.indicator_of_notMem hpair]

/-! ## Conditional unseen law inside a realized timed history section -/

/-- Fixing the continuously valued seen tuple of a realized timed history leaves the unseen
coordinates distributed as the product of the corresponding one-point laws conditioned to stay
in their strict remaining regions.  This is a section theorem; it does not condition the original
sample law on a zero-mass exact seen tuple. -/
theorem feedbackUnseenTupleLaw_cond_historySection_eq_pi
    (reference : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history x) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    (feedbackUnseenTupleLaw S)[|
        {unseen | HistoryAtCoordinate
          (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
          lam x0 p0 sourcePattern targetPattern history x}] =
      Measure.pi fun label : feedbackUnseenFinset S ↦
        (unitSquareUniform : Measure MarkedHeight)[|
          feedbackLabelRemainingSetAt lam terminal x
            (label : FeedbackLabel n)] := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  let remaining : feedbackUnseenFinset S → Set MarkedHeight := fun label ↦
    feedbackLabelRemainingSetAt lam terminal x (label : FeedbackLabel n)
  have hremaining : ∀ label, MeasurableSet (remaining label) := by
    intro label
    exact measurableSet_feedbackLabelRemainingSetAt lam terminal x
      (label : FeedbackLabel n)
  have hpositive : ∀ label,
      (unitSquareUniform : Measure MarkedHeight) (remaining label) ≠ 0 := by
    intro label
    exact ne_of_gt
      (unitSquareUniform_feedbackUnseenRectangularSetAt_factor_pos
        reference hlam0 hlamHalf href label)
  have hsection :
      {unseen | HistoryAtCoordinate
        (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
        lam x0 p0 sourcePattern targetPattern history x} =
        Set.univ.pi remaining := by
    ext unseen
    simpa [S, terminal, remaining, feedbackUnseenRectangularSetAt] using
      (historyAtCoordinate_finiteSampleSeenUnseenMerge_iff
        reference hlam0 hlamHalf href (feedbackSeenTuple S reference) unseen rfl)
  have hcond := Probability.map_eval_cond_univ_pi_eq_pi_map
    (unitSquareUniform : Measure MarkedHeight) remaining hremaining hpositive
  dsimp only
  rw [hsection]
  simpa [feedbackUnseenTupleLaw, remaining] using hcond

end OTSelector
