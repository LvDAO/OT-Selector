import Mathlib.Probability.Independence.Basic
import OTSelector.Basic.FiniteSamplePointLaw
import OTSelector.Feedback.ForcedHistory

/-!
# Point laws indexed by feedback labels

`FeedbackLabel n` is the source/target sum used by the feedback recursion.  This file transfers the
point law proved for the two-colour index `Fin 2 × Fin n` to that sum without reproving independence.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

variable {n : ℕ}

/-- The explicit index map from feedback labels to the two-colour point array. -/
def feedbackLabelToPointLabel : FeedbackLabel n → PointLabel n
  | Sum.inl i => (0, i)
  | Sum.inr j => (1, j)

theorem feedbackLabelToPointLabel_injective :
    Function.Injective (feedbackLabelToPointLabel : FeedbackLabel n → PointLabel n) := by
  intro a b h
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          have hij : i = j := congrArg Prod.snd h
          cases hij
          rfl
      | inr j =>
          have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst h
          simp at h01
  | inr i =>
      cases b with
      | inl j =>
          have h10 : (1 : Fin 2) = 0 := congrArg Prod.fst h
          simp at h10
      | inr j =>
          have hij : i = j := congrArg Prod.snd h
          cases hij
          rfl

/-- The marked point carried by a feedback label. -/
def feedbackLabelPoint (label : FeedbackLabel n) (sample : FiniteSample n) : MarkedHeight :=
  match label with
  | Sum.inl i => FiniteSample.sourcePoint sample i
  | Sum.inr j => FiniteSample.targetPoint sample j

@[simp] theorem feedbackLabelPoint_inl (i : Fin n) (sample : FiniteSample n) :
    feedbackLabelPoint (Sum.inl i) sample = FiniteSample.sourcePoint sample i :=
  rfl

@[simp] theorem feedbackLabelPoint_inr (j : Fin n) (sample : FiniteSample n) :
    feedbackLabelPoint (Sum.inr j) sample = FiniteSample.targetPoint sample j :=
  rfl

@[fun_prop]
theorem measurable_feedbackLabelPoint (label : FeedbackLabel n) :
    Measurable (feedbackLabelPoint label : FiniteSample n → MarkedHeight) := by
  cases label with
  | inl i =>
      exact (FiniteSample.measurable_sourceHeight i).prodMk
        (FiniteSample.measurable_sourceMark i)
  | inr j =>
      exact (FiniteSample.measurable_targetHeight j).prodMk
        (FiniteSample.measurable_targetMark j)

private theorem feedbackLabelPoint_eq_pointLabelCoordinate
    (label : FeedbackLabel n) :
    (feedbackLabelPoint label : FiniteSample n → MarkedHeight) =
      pointLabelCoordinate (feedbackLabelToPointLabel label) := by
  cases label <;> rfl

theorem finiteSampleLaw_map_feedbackLabelPoint (label : FeedbackLabel n) :
    (finiteSampleLaw n).map (measurable_feedbackLabelPoint label).aemeasurable =
      unitSquareUniform := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (feedbackLabelPoint label)
      (finiteSampleLaw n : Measure (FiniteSample n)) =
    (unitSquareUniform : Measure MarkedHeight)
  rw [feedbackLabelPoint_eq_pointLabelCoordinate label]
  exact congrArg ProbabilityMeasure.toMeasure
    (finiteSampleLaw_map_pointLabel (n := n) (feedbackLabelToPointLabel label))

theorem finiteSampleLaw_feedbackLabel_iIndep :
    iIndepFun (fun label : FeedbackLabel n ↦
      fun sample : FiniteSample n ↦ feedbackLabelPoint label sample)
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
  have h := (finiteSampleLaw_pointLabels_iIndep (n := n)).precomp
    (feedbackLabelToPointLabel_injective (n := n))
  simpa only [feedbackLabelPoint_eq_pointLabelCoordinate] using h

end OTSelector
