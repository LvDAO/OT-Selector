import Mathlib.Probability.Independence.Basic
import OTSelector.Feedback.FeedbackPointLaw

/-!
# Finite-sample laws after a label split

For a finite set of feedback labels, this file packages the corresponding marked points as a
single random tuple.  The tuple law and the independence of the seen and unseen tuples are
transported from the already established independent family of labelled points.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

variable {n : ℕ}

/-- The complement of a label set among all feedback labels. -/
def feedbackUnseenFinset (S : Finset (FeedbackLabel n)) : Finset (FeedbackLabel n) :=
  Finset.univ \ S

/-- The tuple of marked points indexed by a finite label set. -/
def feedbackLabelTuple (S : Finset (FeedbackLabel n))
    (sample : FiniteSample n) : S → MarkedHeight :=
  fun label ↦ feedbackLabelPoint (label : FeedbackLabel n) sample

/-- The tuple of the labels declared seen. -/
abbrev feedbackSeenTuple (S : Finset (FeedbackLabel n)) :
    FiniteSample n → S → MarkedHeight :=
  feedbackLabelTuple S

/-- The tuple of the labels not in `S`. -/
abbrev feedbackUnseenTuple (S : Finset (FeedbackLabel n)) :
    FiniteSample n → feedbackUnseenFinset S → MarkedHeight :=
  feedbackLabelTuple (feedbackUnseenFinset S)

@[fun_prop]
theorem measurable_feedbackLabelTuple (S : Finset (FeedbackLabel n)) :
    Measurable (feedbackLabelTuple S : FiniteSample n → S → MarkedHeight) := by
  exact measurable_pi_lambda _ fun label ↦
    measurable_feedbackLabelPoint (label : FeedbackLabel n)

@[fun_prop]
theorem measurable_feedbackSeenTuple (S : Finset (FeedbackLabel n)) :
    Measurable (feedbackSeenTuple S : FiniteSample n → S → MarkedHeight) :=
  measurable_feedbackLabelTuple S

@[fun_prop]
theorem measurable_feedbackUnseenTuple (S : Finset (FeedbackLabel n)) :
    Measurable (feedbackUnseenTuple S :
      FiniteSample n → feedbackUnseenFinset S → MarkedHeight) :=
  measurable_feedbackLabelTuple (feedbackUnseenFinset S)

private theorem feedbackLabelTuple_iIndep (S : Finset (FeedbackLabel n)) :
    iIndepFun (fun label : S ↦
      fun sample : FiniteSample n ↦ feedbackLabelPoint (label : FeedbackLabel n) sample)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  exact (finiteSampleLaw_feedbackLabel_iIndep (n := n)).precomp
    (g := fun label : S ↦ (label : FeedbackLabel n)) (by
      intro label₁ label₂ h
      exact Subtype.ext h)

/-- Exact product law of the tuple indexed by any finite label set. -/
theorem finiteSampleLaw_map_feedbackLabelTuple (S : Finset (FeedbackLabel n)) :
    Measure.map (feedbackLabelTuple S) (finiteSampleLaw n : Measure (FiniteSample n)) =
      Measure.pi fun _ : S ↦ (unitSquareUniform : Measure MarkedHeight) := by
  have hmap := (feedbackLabelTuple_iIndep (n := n) S).map_fun_eq_pi_map
    (fun label : S ↦
      (measurable_feedbackLabelPoint (label : FeedbackLabel n)).aemeasurable)
  have hmap' :
      Measure.map (feedbackLabelTuple S) (finiteSampleLaw n : Measure (FiniteSample n)) =
        Measure.pi fun label : S ↦
          Measure.map (feedbackLabelPoint (label : FeedbackLabel n))
            (finiteSampleLaw n : Measure (FiniteSample n)) := by
    change Measure.map
        (fun sample : FiniteSample n ↦
          fun label : S ↦ feedbackLabelPoint (label : FeedbackLabel n) sample)
        (finiteSampleLaw n : Measure (FiniteSample n)) = _
    exact hmap
  rw [hmap']
  congr 1
  funext label
  exact congrArg ProbabilityMeasure.toMeasure
    (finiteSampleLaw_map_feedbackLabelPoint (n := n) (label : FeedbackLabel n))

theorem finiteSampleLaw_map_feedbackSeenTuple (S : Finset (FeedbackLabel n)) :
    Measure.map (feedbackSeenTuple S) (finiteSampleLaw n : Measure (FiniteSample n)) =
      Measure.pi fun _ : S ↦ (unitSquareUniform : Measure MarkedHeight) :=
  finiteSampleLaw_map_feedbackLabelTuple S

theorem finiteSampleLaw_map_feedbackUnseenTuple (S : Finset (FeedbackLabel n)) :
    Measure.map (feedbackUnseenTuple S) (finiteSampleLaw n : Measure (FiniteSample n)) =
      Measure.pi fun _ : feedbackUnseenFinset S ↦
        (unitSquareUniform : Measure MarkedHeight) :=
  finiteSampleLaw_map_feedbackLabelTuple (feedbackUnseenFinset S)

/-- The seen and unseen marked-point tuples are independent. -/
theorem feedbackSeenTuple_indepFun_feedbackUnseenTuple (S : Finset (FeedbackLabel n)) :
    IndepFun (feedbackSeenTuple S) (feedbackUnseenTuple S)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  exact (finiteSampleLaw_feedbackLabel_iIndep (n := n)).finsets_comp'
    (S := S) (S' := feedbackUnseenFinset S) Finset.disjoint_sdiff
    (fun label ↦ measurable_feedbackLabelPoint label)
    measurable_id measurable_id

/-- Joint law of the seen and unseen tuples is the product of their exact marginal laws. -/
theorem finiteSampleLaw_map_feedbackSeenUnseenTuple (S : Finset (FeedbackLabel n)) :
    Measure.map (fun sample : FiniteSample n ↦
      (feedbackSeenTuple S sample, feedbackUnseenTuple S sample))
      (finiteSampleLaw n : Measure (FiniteSample n)) =
      (Measure.pi fun _ : S ↦ (unitSquareUniform : Measure MarkedHeight)).prod
        (Measure.pi fun _ : feedbackUnseenFinset S ↦
          (unitSquareUniform : Measure MarkedHeight)) := by
  have hpair := (feedbackSeenTuple_indepFun_feedbackUnseenTuple (n := n) S).map_prod_eq_prod_map_map
    (measurable_feedbackSeenTuple S).aemeasurable
    (measurable_feedbackUnseenTuple S).aemeasurable
  rw [finiteSampleLaw_map_feedbackSeenTuple (n := n) S,
    finiteSampleLaw_map_feedbackUnseenTuple (n := n) S] at hpair
  exact hpair

end OTSelector
