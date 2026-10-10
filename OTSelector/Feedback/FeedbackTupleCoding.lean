import OTSelector.Feedback.FiniteSampleSplitLaw

/-!
# Measurable codings for feedback point tuples

This file records the deterministic coordinate codings used by the adaptive deferred-decision
argument.  A finite sample is identified with its complete array of marked feedback points.  A
complete array is then split into its coordinates on a finite set of labels and on its complement.
All maps are explicit and both directions are proved measurable; no null-set witness interface is
introduced.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

variable {n : ℕ}

/-! ## The complete feedback point array -/

/-- The complete marked-point array indexed by feedback labels. -/
abbrev FeedbackPointArray (n : ℕ) := FeedbackLabel n → MarkedHeight

/-- The complete feedback point array attached to a finite sample. -/
def feedbackPointArray (sample : FiniteSample n) : FeedbackPointArray n :=
  fun label ↦ feedbackLabelPoint label sample

@[simp] theorem feedbackPointArray_apply (sample : FiniteSample n)
    (label : FeedbackLabel n) :
    feedbackPointArray sample label = feedbackLabelPoint label sample :=
  rfl

/-- Recover the four scalar coordinate arrays from a complete feedback point array. -/
def feedbackPointArrayToSample (points : FeedbackPointArray n) : FiniteSample n where
  sourceMark := fun i ↦ (points (Sum.inl i)).2
  sourceHeight := fun i ↦ (points (Sum.inl i)).1
  targetMark := fun j ↦ (points (Sum.inr j)).2
  targetHeight := fun j ↦ (points (Sum.inr j)).1

@[simp] theorem feedbackPointArrayToSample_sourcePoint
    (points : FeedbackPointArray n) (i : Fin n) :
    (feedbackPointArrayToSample points).sourcePoint i = points (Sum.inl i) := by
  rfl

@[simp] theorem feedbackPointArrayToSample_targetPoint
    (points : FeedbackPointArray n) (j : Fin n) :
    (feedbackPointArrayToSample points).targetPoint j = points (Sum.inr j) := by
  rfl

@[simp] theorem feedbackPointArrayToSample_sourceMark
    (points : FeedbackPointArray n) (i : Fin n) :
    (feedbackPointArrayToSample points).sourceMark i = (points (Sum.inl i)).2 :=
  rfl

@[simp] theorem feedbackPointArrayToSample_sourceHeight
    (points : FeedbackPointArray n) (i : Fin n) :
    (feedbackPointArrayToSample points).sourceHeight i = (points (Sum.inl i)).1 :=
  rfl

@[simp] theorem feedbackPointArrayToSample_targetMark
    (points : FeedbackPointArray n) (j : Fin n) :
    (feedbackPointArrayToSample points).targetMark j = (points (Sum.inr j)).2 :=
  rfl

@[simp] theorem feedbackPointArrayToSample_targetHeight
    (points : FeedbackPointArray n) (j : Fin n) :
    (feedbackPointArrayToSample points).targetHeight j = (points (Sum.inr j)).1 :=
  rfl

@[simp] theorem feedbackPointArrayToSample_feedbackPointArray
    (points : FeedbackPointArray n) :
    feedbackPointArray (feedbackPointArrayToSample points) = points := by
  funext label
  cases label with
  | inl i => rfl
  | inr j => rfl

@[simp] theorem feedbackPointArray_feedbackPointArrayToSample
    (sample : FiniteSample n) :
    feedbackPointArrayToSample (feedbackPointArray sample) = sample := by
  cases sample
  simp [feedbackPointArray, feedbackPointArrayToSample, feedbackLabelPoint,
    FiniteSample.sourcePoint, FiniteSample.targetPoint]

/-- The explicit equivalence between a finite sample and its complete feedback point array. -/
def feedbackPointArrayEquiv (n : ℕ) :
    FiniteSample n ≃ FeedbackPointArray n where
  toFun := feedbackPointArray
  invFun := feedbackPointArrayToSample
  left_inv := feedbackPointArray_feedbackPointArrayToSample
  right_inv := feedbackPointArrayToSample_feedbackPointArray

@[fun_prop]
theorem measurable_feedbackPointArray :
    Measurable (feedbackPointArray : FiniteSample n → FeedbackPointArray n) := by
  exact measurable_pi_lambda _ fun label ↦ by
    simpa [feedbackPointArray] using measurable_feedbackLabelPoint label

@[fun_prop]
theorem measurable_feedbackPointArrayToSample :
    Measurable (feedbackPointArrayToSample : FeedbackPointArray n → FiniteSample n) := by
  have harrays : Measurable (fun points : FeedbackPointArray n ↦
      FiniteSample.toFourArrays (feedbackPointArrayToSample points)) := by
    refine measurable_pi_lambda _ fun c ↦ ?_
    refine measurable_pi_lambda _ fun i ↦ ?_
    fin_cases c
    · change Measurable (fun points : FeedbackPointArray n ↦
          (points (Sum.inl i)).2)
      have heval : Measurable (fun points : FeedbackPointArray n ↦
          points (Sum.inl i)) := measurable_pi_apply (Sum.inl i)
      exact measurable_snd.comp heval
    · change Measurable (fun points : FeedbackPointArray n ↦
          (points (Sum.inl i)).1)
      have heval : Measurable (fun points : FeedbackPointArray n ↦
          points (Sum.inl i)) := measurable_pi_apply (Sum.inl i)
      exact measurable_fst.comp heval
    · change Measurable (fun points : FeedbackPointArray n ↦
          (points (Sum.inr i)).2)
      have heval : Measurable (fun points : FeedbackPointArray n ↦
          points (Sum.inr i)) := measurable_pi_apply (Sum.inr i)
      exact measurable_snd.comp heval
    · change Measurable (fun points : FeedbackPointArray n ↦
          (points (Sum.inr i)).1)
      have heval : Measurable (fun points : FeedbackPointArray n ↦
          points (Sum.inr i)) := measurable_pi_apply (Sum.inr i)
      exact measurable_fst.comp heval
  have hrecover :
      (fun points : FeedbackPointArray n ↦
        FiniteSample.ofFourArrays (FiniteSample.toFourArrays
          (feedbackPointArrayToSample points))) = feedbackPointArrayToSample := by
    funext points
    exact FiniteSample.ofFourArrays_toFourArrays _
  rw [← hrecover]
  exact FiniteSample.measurable_ofFourArrays.comp harrays

/-- The complete feedback-array coding as a measurable equivalence. -/
noncomputable def feedbackPointArrayMeasurableEquiv (n : ℕ) :
    FiniteSample n ≃ᵐ FeedbackPointArray n where
  toEquiv := feedbackPointArrayEquiv n
  measurable_toFun := measurable_feedbackPointArray
  measurable_invFun := measurable_feedbackPointArrayToSample

@[simp] theorem feedbackPointArrayMeasurableEquiv_apply
    (sample : FiniteSample n) :
    feedbackPointArrayMeasurableEquiv n sample = feedbackPointArray sample :=
  rfl

@[simp] theorem feedbackPointArrayMeasurableEquiv_symm_apply
    (points : FeedbackPointArray n) :
    (feedbackPointArrayMeasurableEquiv n).symm points = feedbackPointArrayToSample points :=
  rfl

/-! ## Splitting and merging a complete feedback array -/

/-- Restrict a complete feedback array to the seen and unseen label domains. -/
def feedbackArraySplit (S : Finset (FeedbackLabel n))
    (points : FeedbackPointArray n) :
    (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) :=
  (fun label ↦ points (label : FeedbackLabel n),
    fun label ↦ points (label : FeedbackLabel n))

/-- Merge a seen tuple and an unseen tuple into a complete feedback array. -/
def feedbackArrayMerge (S : Finset (FeedbackLabel n))
    (parts : (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight)) :
    FeedbackPointArray n :=
  fun label ↦ if h : label ∈ S then parts.1 ⟨label, h⟩ else
    parts.2 ⟨label, by simp [feedbackUnseenFinset, h]⟩

@[simp] theorem feedbackArraySplit_fst (S : Finset (FeedbackLabel n))
    (points : FeedbackPointArray n) (label : S) :
    (feedbackArraySplit S points).1 label = points (label : FeedbackLabel n) :=
  rfl

@[simp] theorem feedbackArraySplit_snd (S : Finset (FeedbackLabel n))
    (points : FeedbackPointArray n) (label : feedbackUnseenFinset S) :
    (feedbackArraySplit S points).2 label = points (label : FeedbackLabel n) :=
  rfl

@[simp] theorem feedbackArrayMerge_apply_mem (S : Finset (FeedbackLabel n))
    (parts : (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight))
    (label : FeedbackLabel n) (h : label ∈ S) :
    feedbackArrayMerge S parts label = parts.1 ⟨label, h⟩ := by
  simp [feedbackArrayMerge, h]

@[simp] theorem feedbackArrayMerge_apply_not_mem (S : Finset (FeedbackLabel n))
    (parts : (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight))
    (label : FeedbackLabel n) (h : label ∉ S) :
    feedbackArrayMerge S parts label =
      parts.2 ⟨label, by simp [feedbackUnseenFinset, h]⟩ := by
  simp [feedbackArrayMerge, h]

@[simp] theorem feedbackArrayMerge_split (S : Finset (FeedbackLabel n))
    (points : FeedbackPointArray n) :
    feedbackArrayMerge S (feedbackArraySplit S points) = points := by
  funext label
  by_cases h : label ∈ S
  · rw [feedbackArrayMerge_apply_mem S _ label h]
    rfl
  · rw [feedbackArrayMerge_apply_not_mem S _ label h]
    rfl

@[simp] theorem feedbackArraySplit_merge (S : Finset (FeedbackLabel n))
    (parts : (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight)) :
    feedbackArraySplit S (feedbackArrayMerge S parts) = parts := by
  apply Prod.ext
  · funext label
    rw [feedbackArraySplit_fst]
    exact feedbackArrayMerge_apply_mem S parts (label : FeedbackLabel n) label.property
  · funext label
    rw [feedbackArraySplit_snd]
    exact feedbackArrayMerge_apply_not_mem S parts (label : FeedbackLabel n)
      (by simpa [feedbackUnseenFinset] using label.property)

/-- The measurable split/merge equivalence for a fixed seen label set. -/
def feedbackArraySplitEquiv (S : Finset (FeedbackLabel n)) :
    FeedbackPointArray n ≃
      (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) where
  toFun := feedbackArraySplit S
  invFun := feedbackArrayMerge S
  left_inv := feedbackArrayMerge_split S
  right_inv := feedbackArraySplit_merge S

@[fun_prop]
theorem measurable_feedbackArraySplit (S : Finset (FeedbackLabel n)) :
    Measurable (feedbackArraySplit S : FeedbackPointArray n →
      (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight)) := by
  have hseen : Measurable (fun points : FeedbackPointArray n ↦
      fun label : S ↦ points (label : FeedbackLabel n)) :=
    measurable_pi_lambda _ fun label ↦ measurable_pi_apply (label : FeedbackLabel n)
  have hunseen : Measurable (fun points : FeedbackPointArray n ↦
      fun label : feedbackUnseenFinset S ↦ points (label : FeedbackLabel n)) :=
    measurable_pi_lambda _ fun label ↦ measurable_pi_apply (label : FeedbackLabel n)
  exact hseen.prodMk hunseen

@[fun_prop]
theorem measurable_feedbackArrayMerge (S : Finset (FeedbackLabel n)) :
    Measurable (feedbackArrayMerge S :
      ((S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight)) →
        FeedbackPointArray n) := by
  refine measurable_pi_lambda _ fun label ↦ ?_
  by_cases h : label ∈ S
  · let seenLabel : S := ⟨label, h⟩
    have hseen : Measurable (fun parts :
        (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) ↦
        parts.1 seenLabel) :=
      (measurable_pi_apply seenLabel).comp measurable_fst
    simpa [feedbackArrayMerge, h, seenLabel] using hseen
  · let unseenLabel : feedbackUnseenFinset S :=
      ⟨label, by simp [feedbackUnseenFinset, h]⟩
    have hunseen : Measurable (fun parts :
        (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) ↦
        parts.2 unseenLabel) :=
      (measurable_pi_apply unseenLabel).comp measurable_snd
    simpa [feedbackArrayMerge, h, unseenLabel] using hunseen

noncomputable def feedbackArraySplitMeasurableEquiv
    (S : Finset (FeedbackLabel n)) :
    FeedbackPointArray n ≃ᵐ
      (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) where
  toEquiv := feedbackArraySplitEquiv S
  measurable_toFun := measurable_feedbackArraySplit S
  measurable_invFun := measurable_feedbackArrayMerge S

@[simp] theorem feedbackArraySplitMeasurableEquiv_apply
    (S : Finset (FeedbackLabel n)) (points : FeedbackPointArray n) :
    feedbackArraySplitMeasurableEquiv S points = feedbackArraySplit S points :=
  rfl

@[simp] theorem feedbackArraySplitMeasurableEquiv_symm_apply
    (S : Finset (FeedbackLabel n))
    (parts : (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight)) :
    (feedbackArraySplitMeasurableEquiv S).symm parts = feedbackArrayMerge S parts :=
  rfl

/-! ## The combined finite-sample seen/unseen coding -/

noncomputable def finiteSampleSeenUnseenMeasurableEquiv
    (S : Finset (FeedbackLabel n)) :
    FiniteSample n ≃ᵐ
      (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) :=
  (feedbackPointArrayMeasurableEquiv n).trans
    (feedbackArraySplitMeasurableEquiv S)

def finiteSampleSeenUnseenEquiv (S : Finset (FeedbackLabel n)) :
    FiniteSample n ≃
      (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight) :=
  feedbackPointArrayEquiv n |>.trans (feedbackArraySplitEquiv S)

@[simp] theorem finiteSampleSeenUnseenMeasurableEquiv_apply
    (S : Finset (FeedbackLabel n)) (sample : FiniteSample n) :
    finiteSampleSeenUnseenMeasurableEquiv S sample =
      (feedbackSeenTuple S sample, feedbackUnseenTuple S sample) := by
  change feedbackArraySplit S (feedbackPointArray sample) = _
  rfl

@[simp] theorem finiteSampleSeenUnseenEquiv_apply
    (S : Finset (FeedbackLabel n)) (sample : FiniteSample n) :
    finiteSampleSeenUnseenEquiv S sample =
      (feedbackSeenTuple S sample, feedbackUnseenTuple S sample) := by
  change feedbackArraySplit S (feedbackPointArray sample) = _
  rfl

@[simp] theorem finiteSampleSeenUnseenMeasurableEquiv_symm_apply
    (S : Finset (FeedbackLabel n))
    (parts : (S → MarkedHeight) × (feedbackUnseenFinset S → MarkedHeight)) :
    (finiteSampleSeenUnseenMeasurableEquiv S).symm parts =
      feedbackPointArrayToSample (feedbackArrayMerge S parts) := by
  rfl

end OTSelector
