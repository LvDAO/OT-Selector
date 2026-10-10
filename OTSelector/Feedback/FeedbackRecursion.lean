import OTSelector.Feedback.FeedbackStep
import OTSelector.Feedback.RateBounds

/-!
# Finite event-driven feedback recursion

The recursion starts by marking every trajectory already below the initial point.  Each later step
uses the affine continuation with slope `lam * sign(current)` and processes every label at the
least remaining crossing coordinate.  This file first establishes the deterministic recursion;
measurability and the product-law intensity computation belong to the subsequent probability
layer.
-/

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-- Source labels already swept at the initial graph point. -/
noncomputable def initialSeenSource (x0 p0 : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i =>
    (n : ℝ) * (sample.sourceHeight i : ℝ) + sample.sourceSlope i * p0 ≤ x0

/-- Target labels already swept at the initial graph point. -/
noncomputable def initialSeenTarget (x0 p0 : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j =>
    (n : ℝ) * (sample.targetHeight j : ℝ) - sample.targetSlope j * p0 ≤ x0

/-- Signed source-minus-target count at the initial graph point. -/
noncomputable def initialFeedbackCurrent (x0 p0 : ℝ) : ℤ :=
  (sample.initialSeenSource x0 p0).card - (sample.initialSeenTarget x0 p0).card

/-- Initial computational state for the forward event recursion. -/
noncomputable def initialFeedbackState (x0 p0 : ℝ) : FeedbackStepState n :=
  { x := x0
    p := p0
    current := sample.initialFeedbackCurrent x0 p0
    seenSource := sample.initialSeenSource x0 p0
    seenTarget := sample.initialSeenTarget x0 p0 }

/-- Every unseen source line lies strictly above the initial graph point. -/
theorem initial_unseenSource_above (x0 p0 : ℝ) {i : Fin n}
    (hi : i ∉ (sample.initialFeedbackState x0 p0).seenSource) :
    x0 < (n : ℝ) * (sample.sourceHeight i : ℝ) + sample.sourceSlope i * p0 := by
  classical
  simp only [initialFeedbackState, initialSeenSource, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi
  exact lt_of_not_ge hi

/-- Every unseen target line lies strictly above the initial graph point. -/
theorem initial_unseenTarget_above (x0 p0 : ℝ) {j : Fin n}
    (hj : j ∉ (sample.initialFeedbackState x0 p0).seenTarget) :
    x0 < (n : ℝ) * (sample.targetHeight j : ℝ) - sample.targetSlope j * p0 := by
  classical
  simp only [initialFeedbackState, initialSeenTarget, Finset.mem_filter,
    Finset.mem_univ, true_and] at hj
  exact lt_of_not_ge hj

/-- Every not-yet-seen line is strictly above the current graph point. -/
def ForwardValid (state : FeedbackStepState n) : Prop :=
  (∀ i, i ∉ state.seenSource →
      state.x < (n : ℝ) * (sample.sourceHeight i : ℝ) +
        sample.sourceSlope i * state.p) ∧
    ∀ j, j ∉ state.seenTarget →
      state.x < (n : ℝ) * (sample.targetHeight j : ℝ) -
        sample.targetSlope j * state.p

theorem initialFeedbackState_forwardValid (x0 p0 : ℝ) :
    sample.ForwardValid (sample.initialFeedbackState x0 p0) := by
  constructor
  · intro i hi
    exact sample.initial_unseenSource_above x0 p0 hi
  · intro j hj
    exact sample.initial_unseenTarget_above x0 p0 hj

/-- Every current candidate lies strictly after a valid state coordinate. -/
theorem candidate_gt_of_forwardValid
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {state : FeedbackStepState n} (hstate : sample.ForwardValid state)
    {z : ℝ} (hz : z ∈ state.candidates sample lam) :
    state.x < z := by
  classical
  rw [FeedbackStepState.candidates, Finset.mem_union] at hz
  rcases hz with hz | hz
  · rw [FeedbackStepState.sourceCandidates] at hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have hiSeen : i ∉ state.seenSource := (Finset.mem_sdiff.mp hi).2
    have ha := sample.sourceSlope_mem i
    apply (x0_lt_sourceSegmentCrossing_iff ha.1 ha.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2
    exact hstate.1 i hiSeen
  · rw [FeedbackStepState.targetCandidates] at hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    have hjSeen : j ∉ state.seenTarget := (Finset.mem_sdiff.mp hj).2
    have hb := sample.targetSlope_mem j
    apply (x0_lt_targetSegmentCrossing_iff hb.1 hb.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2
    exact hstate.2 j hjSeen

/-- A nonempty valid state advances to a strictly larger coordinate. -/
theorem nextCoordinate_gt_of_forwardValid
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {state : FeedbackStepState n} (hstate : sample.ForwardValid state)
    (hcand : (state.candidates sample lam).Nonempty) :
    state.x < state.nextCoordinate sample lam :=
  sample.candidate_gt_of_forwardValid hlam0 hlamHalf hstate
    (state.nextCoordinate_mem_candidates sample lam hcand)

/-- One affine event step preserves the future-line invariant. -/
theorem step_forwardValid
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) :
    sample.ForwardValid (state.step sample lam) := by
  classical
  constructor
  · intro i hi
    have hiUnion : i ∉ state.seenSource ∪ state.newSource sample lam := hi
    have hiSeen : i ∉ state.seenSource := by
      exact fun hmem => hiUnion (Finset.mem_union_left _ hmem)
    have hiNew : i ∉ state.newSource sample lam := by
      exact fun hmem => hiUnion (Finset.mem_union_right _ hmem)
    have hiDiff : i ∈ Finset.univ \ state.seenSource :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiSeen⟩
    have hiCandidate : state.sourceCoordinate sample lam i ∈
        state.candidates sample lam := by
      rw [FeedbackStepState.candidates, Finset.mem_union]
      left
      exact Finset.mem_image.mpr ⟨i, hiDiff, rfl⟩
    have hcand : (state.candidates sample lam).Nonempty := ⟨_, hiCandidate⟩
    have hnextLe : state.nextCoordinate sample lam ≤
        state.sourceCoordinate sample lam i := by
      rw [FeedbackStepState.nextCoordinate, dite_eq_left hcand]
      exact Finset.min'_le _ _ hiCandidate
    have hne : state.sourceCoordinate sample lam i ≠
        state.nextCoordinate sample lam := by
      intro heq
      apply hiNew
      exact Finset.mem_filter.mpr ⟨hiDiff, heq⟩
    have hnextLt : state.nextCoordinate sample lam <
        state.sourceCoordinate sample lam i := lt_of_le_of_ne hnextLe (Ne.symm hne)
    have ha := sample.sourceSlope_mem i
    have hphase := (x_lt_sourceSegmentCrossing_iff ha.1 ha.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).1 hnextLt
    simpa only [FeedbackStepState.step, FeedbackStepState.sourceCoordinate,
      FeedbackStepState.slope] using hphase
  · intro j hj
    have hjUnion : j ∉ state.seenTarget ∪ state.newTarget sample lam := hj
    have hjSeen : j ∉ state.seenTarget := by
      exact fun hmem => hjUnion (Finset.mem_union_left _ hmem)
    have hjNew : j ∉ state.newTarget sample lam := by
      exact fun hmem => hjUnion (Finset.mem_union_right _ hmem)
    have hjDiff : j ∈ Finset.univ \ state.seenTarget :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjSeen⟩
    have hjCandidate : state.targetCoordinate sample lam j ∈
        state.candidates sample lam := by
      rw [FeedbackStepState.candidates, Finset.mem_union]
      right
      exact Finset.mem_image.mpr ⟨j, hjDiff, rfl⟩
    have hcand : (state.candidates sample lam).Nonempty := ⟨_, hjCandidate⟩
    have hnextLe : state.nextCoordinate sample lam ≤
        state.targetCoordinate sample lam j := by
      rw [FeedbackStepState.nextCoordinate, dite_eq_left hcand]
      exact Finset.min'_le _ _ hjCandidate
    have hne : state.targetCoordinate sample lam j ≠
        state.nextCoordinate sample lam := by
      intro heq
      apply hjNew
      exact Finset.mem_filter.mpr ⟨hjDiff, heq⟩
    have hnextLt : state.nextCoordinate sample lam <
        state.targetCoordinate sample lam j := lt_of_le_of_ne hnextLe (Ne.symm hne)
    have hb := sample.targetSlope_mem j
    have hphase := (x_lt_targetSegmentCrossing_iff hb.1 hb.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).1 hnextLt
    simpa only [FeedbackStepState.step, FeedbackStepState.targetCoordinate,
      FeedbackStepState.slope] using hphase

/-- The state after `m` affine event steps. -/
noncomputable def feedbackState (lam x0 p0 : ℝ) : ℕ → FeedbackStepState n
  | 0 => sample.initialFeedbackState x0 p0
  | m + 1 => (feedbackState lam x0 p0 m).step sample lam

@[simp]
theorem feedbackState_zero (lam x0 p0 : ℝ) :
    feedbackState sample lam x0 p0 0 = sample.initialFeedbackState x0 p0 :=
  rfl

@[simp]
theorem feedbackState_succ (lam x0 p0 : ℝ) (m : ℕ) :
    feedbackState sample lam x0 p0 (m + 1) =
      (feedbackState sample lam x0 p0 m).step sample lam :=
  rfl

/-- Every state produced by the finite recursion satisfies the future-line invariant. -/
theorem feedbackState_forwardValid
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (m : ℕ) :
    sample.ForwardValid (feedbackState sample lam x0 p0 m) := by
  cases m with
  | zero => exact sample.initialFeedbackState_forwardValid x0 p0
  | succ m =>
      rw [feedbackState_succ]
      exact sample.step_forwardValid hlam0 hlamHalf _

/-- Whenever candidates remain, the recursion strictly advances its coordinate. -/
theorem feedbackState_x_strictMono_step
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (m : ℕ)
    (hcand : ((feedbackState sample lam x0 p0 m).candidates sample lam).Nonempty) :
    (feedbackState sample lam x0 p0 m).x <
      (feedbackState sample lam x0 p0 (m + 1)).x := by
  rw [feedbackState_succ]
  exact sample.nextCoordinate_gt_of_forwardValid hlam0 hlamHalf
    (sample.feedbackState_forwardValid hlam0 hlamHalf x0 p0 m) hcand

/-- At most `2n` distinct labels can be recorded in any recursion state. -/
theorem feedbackState_seen_card_sum_le (lam x0 p0 : ℝ) (m : ℕ) :
    (feedbackState sample lam x0 p0 m).seenSource.card +
        (feedbackState sample lam x0 p0 m).seenTarget.card ≤ 2 * n := by
  have hs : (feedbackState sample lam x0 p0 m).seenSource.card ≤ n := by
    simpa using (feedbackState sample lam x0 p0 m).seenSource.card_le_univ
  have ht : (feedbackState sample lam x0 p0 m).seenTarget.card ≤ n := by
    simpa using (feedbackState sample lam x0 p0 m).seenTarget.card_le_univ
  have hsum := Nat.add_le_add hs ht
  omega

/-- A state with a remaining candidate has recorded strictly fewer than all `2n` labels. -/
theorem seen_card_sum_lt_of_candidates_nonempty
    (lam : ℝ) (state : FeedbackStepState n)
    (hcand : (state.candidates sample lam).Nonempty) :
    state.seenSource.card + state.seenTarget.card < 2 * n := by
  classical
  have hnotAll : ¬(state.seenSource = Finset.univ ∧ state.seenTarget = Finset.univ) := by
    intro hall
    exact hcand.ne_empty ((state.candidates_eq_empty_iff sample lam).2 hall)
  rcases not_and_or.mp hnotAll with hsource | htarget
  · have hs : state.seenSource.card < n := by
      simpa using (Finset.card_lt_iff_ne_univ state.seenSource).2 hsource
    have ht : state.seenTarget.card ≤ n := by
      simpa using state.seenTarget.card_le_univ
    omega
  · have hs : state.seenSource.card ≤ n := by
      simpa using state.seenSource.card_le_univ
    have ht : state.seenTarget.card < n := by
      simpa using (Finset.card_lt_iff_ne_univ state.seenTarget).2 htarget
    omega

/-- After `m` recursive steps, either the construction has stopped or it has recorded at least
`m` more labels than were present initially.  Simultaneous crossings only improve this bound. -/
private theorem feedbackState_done_or_seen_growth
    (lam x0 p0 : ℝ) (m : ℕ) :
    (feedbackState sample lam x0 p0 m).candidates sample lam = ∅ ∨
      (sample.initialFeedbackState x0 p0).seenSource.card +
          (sample.initialFeedbackState x0 p0).seenTarget.card + m ≤
        (feedbackState sample lam x0 p0 m).seenSource.card +
          (feedbackState sample lam x0 p0 m).seenTarget.card := by
  induction m with
  | zero =>
      by_cases hdone :
          (feedbackState sample lam x0 p0 0).candidates sample lam = ∅
      · exact Or.inl hdone
      · right
        simp
  | succ m ih =>
      rw [feedbackState_succ]
      rcases ih with hdone | hgrowth
      · left
        rw [(feedbackState sample lam x0 p0 m).step_eq_of_candidates_eq_empty
          sample lam hdone]
        exact hdone
      · by_cases hdone :
          (feedbackState sample lam x0 p0 m).candidates sample lam = ∅
        · left
          rw [(feedbackState sample lam x0 p0 m).step_eq_of_candidates_eq_empty
            sample lam hdone]
          exact hdone
        · right
          have hcand :
              ((feedbackState sample lam x0 p0 m).candidates sample lam).Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr hdone
          have hstep := (feedbackState sample lam x0 p0 m).step_seen_card_sum_lt
            sample lam hcand
          omega

/-- The event-driven recursion has no remaining label after at most `2n` steps. -/
theorem feedbackState_candidates_eq_empty_two_mul
    (lam x0 p0 : ℝ) :
    (feedbackState sample lam x0 p0 (2 * n)).candidates sample lam = ∅ := by
  rcases sample.feedbackState_done_or_seen_growth lam x0 p0 (2 * n) with hdone | hgrowth
  · exact hdone
  · by_contra hdone
    have hcand :
        ((feedbackState sample lam x0 p0 (2 * n)).candidates sample lam).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hdone
    have hlt := sample.seen_card_sum_lt_of_candidates_nonempty lam _ hcand
    omega

/-- Once no candidate remains, the next recursive state is unchanged. -/
theorem feedbackState_succ_eq_of_candidates_eq_empty
    (lam x0 p0 : ℝ) (m : ℕ)
    (hdone : (feedbackState sample lam x0 p0 m).candidates sample lam = ∅) :
    feedbackState sample lam x0 p0 (m + 1) = feedbackState sample lam x0 p0 m := by
  rw [feedbackState_succ]
  exact (feedbackState sample lam x0 p0 m).step_eq_of_candidates_eq_empty
    sample lam hdone

/-- The recursive state is constant after the deterministic horizon `2n`. -/
theorem feedbackState_stable_after_two_mul
    (lam x0 p0 : ℝ) (r : ℕ) :
    feedbackState sample lam x0 p0 (2 * n + r) =
      feedbackState sample lam x0 p0 (2 * n) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hdone :
          (feedbackState sample lam x0 p0 (2 * n + r)).candidates sample lam = ∅ := by
        rw [ih]
        exact sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0
      rw [Nat.add_succ, sample.feedbackState_succ_eq_of_candidates_eq_empty lam x0 p0 _ hdone]
      exact ih

end FiniteSample

end OTSelector
