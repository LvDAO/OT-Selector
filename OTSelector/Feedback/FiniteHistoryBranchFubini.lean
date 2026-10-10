import OTSelector.Feedback.AdaptiveDeferredDecision

/-!
# Fubini transport for a fixed finite-history branch

This module transports the measurable event of a prescribed `HistoryBranch` through the
finite-sample seen/unseen measurable equivalence.  The continuously valued seen tuple remains the
outer integration variable; no conditional law on an exact tuple is introduced.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## Product-coordinate branch cells -/

/-- A fixed finite-history branch written in seen/unseen product coordinates. -/
def historyBranchProductSet
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    Set
      ((feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight) ×
        (feedbackUnseenFinset
          (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)) :=
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  {parts | HistoryBranch
    (finiteSampleSeenUnseenMerge S parts.1 parts.2)
    lam x0 p0 sourcePattern targetPattern history}

theorem measurableSet_historyBranchProductSet
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    MeasurableSet
      (historyBranchProductSet lam x0 p0 sourcePattern targetPattern history) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  have hmerge := measurable_finiteSampleSeenUnseenMerge (n := n) S
  have hbranch := measurableSet_historyBranch (n := n) lam x0 p0
    sourcePattern targetPattern history
  simpa [historyBranchProductSet, S] using hmerge hbranch

theorem mem_historyBranchProductSet_iff
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (parts :
      (feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight) ×
        (feedbackUnseenFinset
          (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)) :
    parts ∈ historyBranchProductSet lam x0 p0 sourcePattern targetPattern history ↔
      HistoryBranch
        (finiteSampleSeenUnseenMerge
          (feedbackTerminalLabelSet sourcePattern targetPattern history)
          parts.1 parts.2)
        lam x0 p0 sourcePattern targetPattern history := by
  rfl

/-! ## Exact Fubini transport -/

/-- The finite-sample integral over a fixed branch equals the iterated seen/unseen product
integral.  The integrand may depend jointly on both tuples. -/
theorem integral_historyBranch_eq_iterated
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
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
          HistoryBranch sample lam x0 p0 sourcePattern targetPattern history}.indicator
          (fun sample ↦ F
            (feedbackSeenTuple
              (feedbackTerminalLabelSet sourcePattern targetPattern history) sample,
             feedbackUnseenTuple
              (feedbackTerminalLabelSet sourcePattern targetPattern history) sample)) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n))) =
      ∫ seen, ∫ unseen,
        (historyBranchProductSet lam x0 p0
          sourcePattern targetPattern history).indicator F (seen, unseen)
          ∂(feedbackUnseenTupleLaw
            (feedbackTerminalLabelSet sourcePattern targetPattern history))
        ∂(feedbackTupleLaw
          (feedbackTerminalLabelSet sourcePattern targetPattern history)) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let C := historyBranchProductSet lam x0 p0 sourcePattern targetPattern history
  have hC : MeasurableSet C := by
    simpa [C] using measurableSet_historyBranchProductSet (n := n)
      lam x0 p0 sourcePattern targetPattern history
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
    by_cases hbranch :
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history
    · have hpair :
          (feedbackSeenTuple S sample, feedbackUnseenTuple S sample) ∈ C := by
        change HistoryBranch
          (finiteSampleSeenUnseenMerge S
            (feedbackSeenTuple S sample) (feedbackUnseenTuple S sample))
          lam x0 p0 sourcePattern targetPattern history
        simpa [finiteSampleSeenUnseenMerge_split] using hbranch
      have hmem : sample ∈ {sample : FiniteSample n |
          HistoryBranch sample lam x0 p0 sourcePattern targetPattern history} := hbranch
      rw [Set.indicator_of_mem hmem]
      change _ = C.indicator F
        (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)
      rw [Set.indicator_of_mem hpair]
    · have hpair :
          (feedbackSeenTuple S sample, feedbackUnseenTuple S sample) ∉ C := by
        intro hp
        apply hbranch
        change HistoryBranch
          (finiteSampleSeenUnseenMerge S
            (feedbackSeenTuple S sample) (feedbackUnseenTuple S sample))
          lam x0 p0 sourcePattern targetPattern history at hp
        simpa [finiteSampleSeenUnseenMerge_split] using hp
      have hmem : sample ∉ {sample : FiniteSample n |
          HistoryBranch sample lam x0 p0 sourcePattern targetPattern history} := hbranch
      rw [Set.indicator_of_notMem hmem]
      change (0 : ℝ) = C.indicator F
        (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)
      rw [Set.indicator_of_notMem hpair]

/-! ## Fixed seen sections -/

/-- On a realized branch, fixing the seen tuple gives exactly the product of strict terminal
remaining regions for the unseen labels. -/
theorem historyBranchProductSet_section_eq_feedbackUnseenRectangularSet
    (reference : FiniteSample n) {lam x0 p0 : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen :
      feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference) :
    {unseen |
      (seen, unseen) ∈ historyBranchProductSet lam x0 p0 sourcePattern targetPattern history} =
      feedbackUnseenRectangularSet
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
        (feedbackTerminalLabelSet sourcePattern targetPattern history) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  ext unseen
  change HistoryBranch
      (finiteSampleSeenUnseenMerge S seen unseen)
      lam x0 p0 sourcePattern targetPattern history ↔
    unseen ∈ feedbackUnseenRectangularSet terminal S
  rw [historyBranch_finiteSampleSeenUnseenMerge_iff
    reference hlam0 hlamHalf href seen unseen hseen]
  simpa [terminal, S] using
    (mem_feedbackUnseenRectangularSet_iff terminal S unseen).symm

end OTSelector
