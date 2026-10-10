import OTSelector.Feedback.Graph
import OTSelector.Feedback.FeedbackSegment
import OTSelector.Feedback.CrossingRates

/-!
# One deterministic feedback step

This file records the finite bookkeeping performed on one affine segment.  The state is only
computational data: it contains the current coordinate, graph value, signed crossing count, and
the labels already used.  No probabilistic or future-event assertion is part of this interface.
-/

namespace OTSelector

/-- Computational state at one point of an event-driven feedback construction. -/
structure FeedbackStepState (n : ℕ) where
  x : ℝ
  p : ℝ
  current : ℤ
  seenSource : Finset (Fin n)
  seenTarget : Finset (Fin n)

namespace FeedbackStepState

variable {n : ℕ}

/-- The current affine slope, using the signed current crossing count. -/
noncomputable def slope (lam : ℝ) (state : FeedbackStepState n) : ℝ :=
  feedbackSlope lam (state.current : ℝ)

/-- The source crossing coordinate attached to one not-yet-seen source label. -/
noncomputable def sourceCoordinate (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (i : Fin n) : ℝ :=
  sourceSegmentCrossing state.x state.p (state.slope lam)
    ((n : ℝ) * (sample.sourceHeight i : ℝ)) (sample.sourceSlope i)

/-- The target crossing coordinate attached to one not-yet-seen target label. -/
noncomputable def targetCoordinate (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (j : Fin n) : ℝ :=
  targetSegmentCrossing state.x state.p (state.slope lam)
    ((n : ℝ) * (sample.targetHeight j : ℝ)) (sample.targetSlope j)

/-- Source coordinates whose labels have not yet been used. -/
noncomputable def sourceCandidates (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : Finset ℝ := by
  classical
  exact (Finset.univ \ state.seenSource).image (state.sourceCoordinate sample lam)

/-- Target coordinates whose labels have not yet been used. -/
noncomputable def targetCandidates (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : Finset ℝ := by
  classical
  exact (Finset.univ \ state.seenTarget).image (state.targetCoordinate sample lam)

/-- All candidate coordinates on the current affine segment. -/
noncomputable def candidates (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : Finset ℝ :=
  state.sourceCandidates sample lam ∪ state.targetCandidates sample lam

private theorem sourceCandidates_eq_empty_iff (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    state.sourceCandidates sample lam = ∅ ↔ state.seenSource = Finset.univ := by
  classical
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    have hi' : i ∈ Finset.univ \ state.seenSource := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hi
    have hz : state.sourceCoordinate sample lam i ∈
        state.sourceCandidates sample lam := by
      exact Finset.mem_image.mpr ⟨i, hi', rfl⟩
    rw [h] at hz
    simp at hz
  · intro h
    simp [sourceCandidates, h]

private theorem targetCandidates_eq_empty_iff (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    state.targetCandidates sample lam = ∅ ↔ state.seenTarget = Finset.univ := by
  classical
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hj
    have hj' : j ∈ Finset.univ \ state.seenTarget := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hj
    have hz : state.targetCoordinate sample lam j ∈
        state.targetCandidates sample lam := by
      exact Finset.mem_image.mpr ⟨j, hj', rfl⟩
    rw [h] at hz
    simp at hz
  · intro h
    simp [targetCandidates, h]

/-- There are no candidate coordinates exactly when every label has already been used. -/
theorem candidates_eq_empty_iff (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    state.candidates sample lam = ∅ ↔
      state.seenSource = Finset.univ ∧ state.seenTarget = Finset.univ := by
  classical
  change (state.sourceCandidates sample lam ∪ state.targetCandidates sample lam = ∅) ↔ _
  rw [Finset.union_eq_empty]
  rw [sourceCandidates_eq_empty_iff, targetCandidates_eq_empty_iff]

/-- The next coordinate is the current coordinate if no candidate remains, and otherwise the
minimum candidate coordinate. -/
noncomputable def nextCoordinate (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : ℝ :=
  if h : (state.candidates sample lam).Nonempty then
    (state.candidates sample lam).min' h
  else state.x

theorem nextCoordinate_mem_candidates (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (h : (state.candidates sample lam).Nonempty) :
    state.nextCoordinate sample lam ∈ state.candidates sample lam := by
  simp only [nextCoordinate, dite_eq_left h]
  exact Finset.min'_mem _ h

/-- Source labels whose segment crossing coordinate equals the selected coordinate. -/
noncomputable def newSource (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : Finset (Fin n) := by
  classical
  exact (Finset.univ \ state.seenSource).filter fun i ↦
    state.sourceCoordinate sample lam i = state.nextCoordinate sample lam

/- Target labels whose segment crossing coordinate equals the selected coordinate. -/
noncomputable def newTarget (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : Finset (Fin n) := by
  classical
  exact (Finset.univ \ state.seenTarget).filter fun j ↦
    state.targetCoordinate sample lam j = state.nextCoordinate sample lam

private theorem mem_sourceCandidates_iff (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (z : ℝ) :
    z ∈ state.sourceCandidates sample lam ↔
      ∃ i ∈ Finset.univ \ state.seenSource, state.sourceCoordinate sample lam i = z := by
  classical
  simp [sourceCandidates]

private theorem mem_targetCandidates_iff (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (z : ℝ) :
    z ∈ state.targetCandidates sample lam ↔
      ∃ j ∈ Finset.univ \ state.seenTarget, state.targetCoordinate sample lam j = z := by
  classical
  simp [targetCandidates]

theorem new_family_nonempty (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (h : (state.candidates sample lam).Nonempty) :
    (state.newSource sample lam).Nonempty ∨ (state.newTarget sample lam).Nonempty := by
  classical
  have hcoord := state.nextCoordinate_mem_candidates sample lam h
  simp only [candidates, Finset.mem_union] at hcoord
  rcases hcoord with hsource | htarget
  · obtain ⟨i, hi, hzi⟩ := (state.mem_sourceCandidates_iff sample lam _).mp hsource
    left
    refine ⟨i, ?_⟩
    exact Finset.mem_filter.mpr ⟨hi, hzi⟩
  · obtain ⟨j, hj, hzj⟩ := (state.mem_targetCandidates_iff sample lam _).mp htarget
    right
    refine ⟨j, ?_⟩
    exact Finset.mem_filter.mpr ⟨hj, hzj⟩

theorem newSource_disjoint_seenSource (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    Disjoint (state.newSource sample lam) state.seenSource := by
  classical
  rw [Finset.disjoint_left]
  intro i hiNew hiSeen
  have hiFilter : i ∈ (Finset.univ \ state.seenSource).filter (fun i ↦
      state.sourceCoordinate sample lam i = state.nextCoordinate sample lam) := by
    simpa only [newSource] using hiNew
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hiFilter).1).2 hiSeen

theorem newTarget_disjoint_seenTarget (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    Disjoint (state.newTarget sample lam) state.seenTarget := by
  classical
  rw [Finset.disjoint_left]
  intro j hjNew hjSeen
  have hjFilter : j ∈ (Finset.univ \ state.seenTarget).filter (fun j ↦
      state.targetCoordinate sample lam j = state.nextCoordinate sample lam) := by
    simpa only [newTarget] using hjNew
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hjFilter).1).2 hjSeen

/- The state after processing the selected coordinate. -/
noncomputable def step (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : FeedbackStepState n :=
  { x := state.nextCoordinate sample lam
    p := segmentCurve state.x state.p (state.slope lam) (state.nextCoordinate sample lam)
    current := state.current + (state.newSource sample lam).card -
      (state.newTarget sample lam).card
    seenSource := state.seenSource ∪ state.newSource sample lam
    seenTarget := state.seenTarget ∪ state.newTarget sample lam }

theorem seenSource_subset_step (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    state.seenSource ⊆ (state.step sample lam).seenSource := by
  exact Finset.subset_union_left

theorem seenTarget_subset_step (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    state.seenTarget ⊆ (state.step sample lam).seenTarget := by
  exact Finset.subset_union_left

theorem step_seenSource_subset_univ (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    (state.step sample lam).seenSource ⊆ Finset.univ := by
  intro i hi
  exact Finset.mem_univ i

theorem step_seenTarget_subset_univ (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    (state.step sample lam).seenTarget ⊆ Finset.univ := by
  intro j hj
  exact Finset.mem_univ j

theorem step_seen_card_sum_lt (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (h : (state.candidates sample lam).Nonempty) :
    state.seenSource.card + state.seenTarget.card <
      (state.step sample lam).seenSource.card +
        (state.step sample lam).seenTarget.card := by
  classical
  rcases state.new_family_nonempty sample lam h with hsource | htarget
  · have hsource_card : 0 < (state.newSource sample lam).card :=
      Finset.card_pos.mpr hsource
    have hsource_disjoint :
        Disjoint state.seenSource (state.newSource sample lam) :=
      (state.newSource_disjoint_seenSource sample lam).symm
    have hsource_strict : state.seenSource.card <
        (state.seenSource ∪ state.newSource sample lam).card := by
      rw [Finset.card_union_of_disjoint hsource_disjoint]
      exact Nat.lt_add_of_pos_right hsource_card
    have htarget_mono : state.seenTarget.card ≤
        (state.seenTarget ∪ state.newTarget sample lam).card := by
      exact Finset.card_le_card Finset.subset_union_left
    change state.seenSource.card + state.seenTarget.card <
      (state.seenSource ∪ state.newSource sample lam).card +
        (state.seenTarget ∪ state.newTarget sample lam).card
    exact Nat.add_lt_add_of_lt_of_le hsource_strict htarget_mono
  · have htarget_card : 0 < (state.newTarget sample lam).card :=
      Finset.card_pos.mpr htarget
    have htarget_disjoint :
        Disjoint state.seenTarget (state.newTarget sample lam) :=
      (state.newTarget_disjoint_seenTarget sample lam).symm
    have htarget_strict : state.seenTarget.card <
        (state.seenTarget ∪ state.newTarget sample lam).card := by
      rw [Finset.card_union_of_disjoint htarget_disjoint]
      exact Nat.lt_add_of_pos_right htarget_card
    have hsource_mono : state.seenSource.card ≤
        (state.seenSource ∪ state.newSource sample lam).card := by
      exact Finset.card_le_card Finset.subset_union_left
    change state.seenSource.card + state.seenTarget.card <
      (state.seenSource ∪ state.newSource sample lam).card +
        (state.seenTarget ∪ state.newTarget sample lam).card
    exact Nat.add_lt_add_of_le_of_lt hsource_mono htarget_strict

theorem step_eq_of_candidates_eq_empty (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (h : state.candidates sample lam = ∅) :
    state.step sample lam = state := by
  classical
  have hnot : ¬(state.candidates sample lam).Nonempty := by
    intro hc
    obtain ⟨z, hz⟩ := hc
    rw [h] at hz
    simp at hz
  have hseen := (state.candidates_eq_empty_iff sample lam).mp h
  have hnext : state.nextCoordinate sample lam = state.x := by
    simp [nextCoordinate, hnot]
  have hsource : state.newSource sample lam = ∅ := by
    simp [newSource, hseen.1]
  have htarget : state.newTarget sample lam = ∅ := by
    simp [newTarget, hseen.2]
  simp [step, hnext, hsource, htarget, segmentCurve]

@[simp] theorem step_current (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) :
    (state.step sample lam).current =
      state.current + (state.newSource sample lam).card -
        (state.newTarget sample lam).card :=
  rfl

end FeedbackStepState

end OTSelector
