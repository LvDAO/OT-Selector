import OTSelector.Feedback.FiniteHistoryProductSection

/-!
# Canonical representatives for fixed seen tuples

For a fixed terminal label set, the seen coordinates determine the scheduled state.  This file
chooses one harmless constant value for every unseen coordinate, packages the resulting sample as
a measurable representative of the seen section, and records the state identity needed when an
arbitrary unseen tuple is used instead.

No conditional-law or certificate interface is introduced here.
-/

open MeasureTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## A canonical legal unseen value -/

/-- The endpoint `0` as a legal mark in the closed unit interval. -/
def feedbackCanonicalUnitMark : UnitMark :=
  ⟨0, by constructor <;> norm_num⟩

/-- A fixed legal marked point used for all coordinates outside a seen label set. -/
def feedbackCanonicalMarkedHeight : MarkedHeight :=
  (feedbackCanonicalUnitMark, feedbackCanonicalUnitMark)

/-- The constant unseen tuple used to select a representative of a seen section. -/
def feedbackCanonicalUnseenTuple (S : Finset (FeedbackLabel n)) :
    feedbackUnseenFinset S → MarkedHeight :=
  fun _ ↦ feedbackCanonicalMarkedHeight

/-! ## The representative and its measurable dependence on the seen tuple -/

/-- The finite sample obtained by merging `seen` with the canonical unseen tuple. -/
noncomputable def feedbackSeenRepresentative (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight) : FiniteSample n :=
  finiteSampleSeenUnseenMerge S seen (feedbackCanonicalUnseenTuple S)

@[simp]
theorem feedbackSeenTuple_feedbackSeenRepresentative
    (S : Finset (FeedbackLabel n)) (seen : S → MarkedHeight) :
    feedbackSeenTuple S (feedbackSeenRepresentative S seen) = seen := by
  exact feedbackSeenTuple_finiteSampleSeenUnseenMerge S seen
    (feedbackCanonicalUnseenTuple S)

@[fun_prop]
theorem measurable_feedbackSeenRepresentative
    (S : Finset (FeedbackLabel n)) :
    Measurable (feedbackSeenRepresentative S) := by
  have hmerge : Measurable (fun parts :
      (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) ↦
        finiteSampleSeenUnseenMerge S parts.1 parts.2) := by
    change Measurable ((finiteSampleSeenUnseenMeasurableEquiv S).symm)
    exact (finiteSampleSeenUnseenMeasurableEquiv S).symm.measurable
  have hparts : Measurable (fun seen : S → MarkedHeight ↦
      (seen, feedbackCanonicalUnseenTuple S)) :=
    measurable_id.prodMk measurable_const
  change Measurable (fun seen : S → MarkedHeight ↦
    finiteSampleSeenUnseenMerge S seen (feedbackCanonicalUnseenTuple S))
  exact hmerge.comp hparts

/-! ## The scheduled state as a function of the seen tuple -/

/-- Scheduled terminal state represented using only the seen tuple. -/
noncomputable def feedbackScheduledStateOfSeen
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight) :
    FeedbackStepState n :=
  (feedbackSeenRepresentative
      (feedbackTerminalLabelSet sourcePattern targetPattern history) seen).scheduledState
    lam x0 p0 sourcePattern targetPattern history

@[fun_prop]
theorem measurable_feedbackScheduledStateOfSeen
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    Measurable (feedbackScheduledStateOfSeen (n := n) lam x0 p0
      sourcePattern targetPattern history) := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  have hstate : Measurable (fun sample : FiniteSample n ↦
      sample.scheduledState lam x0 p0 sourcePattern targetPattern history) :=
    FiniteSample.measurable_scheduledState lam x0 p0 sourcePattern targetPattern history
  change Measurable (fun seen : S → MarkedHeight ↦
    (feedbackSeenRepresentative S seen).scheduledState
      lam x0 p0 sourcePattern targetPattern history)
  exact hstate.comp (measurable_feedbackSeenRepresentative (n := n) S)

/-! ## Independence of the representative choice -/

/-- Every unseen merge with the same seen tuple has the representative's scheduled state. -/
theorem scheduledState_eq_feedbackScheduledStateOfSeen_of_finiteSampleSeenUnseenMerge
    (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hS : S = feedbackTerminalLabelSet sourcePattern targetPattern history) :
    (finiteSampleSeenUnseenMerge S seen unseen).scheduledState
        lam x0 p0 sourcePattern targetPattern history =
      feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history
        (by simpa [hS] using seen) := by
  subst S
  let S' := feedbackTerminalLabelSet sourcePattern targetPattern history
  have htuple :
      feedbackSeenTuple S'
          (finiteSampleSeenUnseenMerge S' seen unseen) =
        feedbackSeenTuple S' (feedbackSeenRepresentative S' seen) := by
    rw [feedbackSeenTuple_finiteSampleSeenUnseenMerge,
      feedbackSeenTuple_feedbackSeenRepresentative]
  exact scheduledState_eq_of_feedbackSeenTuple_eq
    (finiteSampleSeenUnseenMerge S' seen unseen)
    (feedbackSeenRepresentative S' seen)
    lam x0 p0 sourcePattern targetPattern history htuple

end OTSelector
