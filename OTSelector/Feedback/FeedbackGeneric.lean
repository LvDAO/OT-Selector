import OTSelector.Feedback.FeedbackRecursion

/-!
# Generic deterministic consequences of the feedback recursion

This file records the ordinary geometric no-tie condition and the elementary consequences that
are used before introducing any probability law.  The condition is a proposition about the finite
sample and the deterministic event recursion; it carries no auxiliary data.
-/

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-- No two colours or labels are processed at the same event before the finite horizon. -/
def NoFeedbackTies (lam x0 p0 : ℝ) : Prop :=
  ∀ m < 2 * n,
    ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 m).newTarget sample lam).card ≤ 1

/-- A nonempty candidate set produces at least one new label at its selected coordinate. -/
theorem new_label_count_pos_of_candidates_nonempty
    (lam : ℝ) (state : FeedbackStepState n)
    (hcand : (state.candidates sample lam).Nonempty) :
    0 < (state.newSource sample lam).card + (state.newTarget sample lam).card := by
  rcases state.new_family_nonempty sample lam hcand with hsource | htarget
  · have hcard : 0 < (state.newSource sample lam).card := Finset.card_pos.mpr hsource
    omega
  · have hcard : 0 < (state.newTarget sample lam).card := Finset.card_pos.mpr htarget
    omega

/-- Under `NoFeedbackTies`, a nonempty candidate step processes exactly one label. -/
theorem new_label_count_eq_one_of_noFeedbackTies
    {lam x0 p0 : ℝ} (hties : sample.NoFeedbackTies lam x0 p0)
    {m : ℕ} (hm : m < 2 * n)
    (hcand : ((feedbackState sample lam x0 p0 m).candidates sample lam).Nonempty) :
    ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 m).newTarget sample lam).card = 1 := by
  have hupper := hties m hm
  have hlower := sample.new_label_count_pos_of_candidates_nonempty lam _ hcand
  omega

/-- Under `NoFeedbackTies`, a nonempty step has exactly one active colour. -/
theorem new_label_single_color_of_noFeedbackTies
    {lam x0 p0 : ℝ} (hties : sample.NoFeedbackTies lam x0 p0)
    {m : ℕ} (hm : m < 2 * n)
    (hcand : ((feedbackState sample lam x0 p0 m).candidates sample lam).Nonempty) :
    (((feedbackState sample lam x0 p0 m).newSource sample lam).card = 1 ∧
      ((feedbackState sample lam x0 p0 m).newTarget sample lam).card = 0) ∨
    (((feedbackState sample lam x0 p0 m).newSource sample lam).card = 0 ∧
      ((feedbackState sample lam x0 p0 m).newTarget sample lam).card = 1) := by
  have hone := sample.new_label_count_eq_one_of_noFeedbackTies hties hm hcand
  by_cases hsource :
      ((feedbackState sample lam x0 p0 m).newSource sample lam).card = 0
  · right
    constructor
    · exact hsource
    · omega
  · left
    constructor
    · omega
    · omega

/-- A source event changes the recursive current by `+1` under `NoFeedbackTies`. -/
theorem feedbackState_current_step_add_one_of_noFeedbackTies
    {lam x0 p0 : ℝ} (hties : sample.NoFeedbackTies lam x0 p0)
    {m : ℕ} (hm : m < 2 * n)
    (hcand : ((feedbackState sample lam x0 p0 m).candidates sample lam).Nonempty)
    (hsource : ((feedbackState sample lam x0 p0 m).newSource sample lam).Nonempty) :
    (feedbackState sample lam x0 p0 (m + 1)).current =
      (feedbackState sample lam x0 p0 m).current + 1 := by
  have hsingle := sample.new_label_single_color_of_noFeedbackTies hties hm hcand
  have hsource_card :
      ((feedbackState sample lam x0 p0 m).newSource sample lam).card = 1 := by
    rcases hsingle with hsource_only | htarget_only
    · exact hsource_only.1
    · have hpos : 0 < ((feedbackState sample lam x0 p0 m).newSource sample lam).card :=
        Finset.card_pos.mpr hsource
      omega
  have htarget_card :
      ((feedbackState sample lam x0 p0 m).newTarget sample lam).card = 0 := by
    rcases hsingle with hsource_only | htarget_only
    · exact hsource_only.2
    · omega
  rw [feedbackState_succ, FeedbackStepState.step_current]
  simp [hsource_card, htarget_card]

/-- A target event changes the recursive current by `-1` under `NoFeedbackTies`. -/
theorem feedbackState_current_step_sub_one_of_noFeedbackTies
    {lam x0 p0 : ℝ} (hties : sample.NoFeedbackTies lam x0 p0)
    {m : ℕ} (hm : m < 2 * n)
    (hcand : ((feedbackState sample lam x0 p0 m).candidates sample lam).Nonempty)
    (htarget : ((feedbackState sample lam x0 p0 m).newTarget sample lam).Nonempty) :
    (feedbackState sample lam x0 p0 (m + 1)).current =
      (feedbackState sample lam x0 p0 m).current - 1 := by
  have hsingle := sample.new_label_single_color_of_noFeedbackTies hties hm hcand
  have htarget_card :
      ((feedbackState sample lam x0 p0 m).newTarget sample lam).card = 1 := by
    rcases hsingle with hsource_only | htarget_only
    · have hpos : 0 < ((feedbackState sample lam x0 p0 m).newTarget sample lam).card :=
        Finset.card_pos.mpr htarget
      omega
    · exact htarget_only.2
  have hsource_card :
      ((feedbackState sample lam x0 p0 m).newSource sample lam).card = 0 := by
    rcases hsingle with hsource_only | htarget_only
    · omega
    · exact htarget_only.1
  rw [feedbackState_succ, FeedbackStepState.step_current]
  simp [hsource_card, htarget_card]

/-- Every nonempty no-tie step changes the recursive current by one unit in one direction. -/
theorem feedbackState_current_step_add_or_sub_one_of_noFeedbackTies
    {lam x0 p0 : ℝ} (hties : sample.NoFeedbackTies lam x0 p0)
    {m : ℕ} (hm : m < 2 * n)
    (hcand : ((feedbackState sample lam x0 p0 m).candidates sample lam).Nonempty) :
    (feedbackState sample lam x0 p0 (m + 1)).current =
        (feedbackState sample lam x0 p0 m).current + 1 ∨
      (feedbackState sample lam x0 p0 (m + 1)).current =
        (feedbackState sample lam x0 p0 m).current - 1 := by
  rcases sample.new_label_single_color_of_noFeedbackTies hties hm hcand with hsource | htarget
  · left
    apply sample.feedbackState_current_step_add_one_of_noFeedbackTies hties hm hcand
    exact Finset.card_pos.mp (by omega :
      0 < ((feedbackState sample lam x0 p0 m).newSource sample lam).card)
  · right
    apply sample.feedbackState_current_step_sub_one_of_noFeedbackTies hties hm hcand
    exact Finset.card_pos.mp (by omega :
      0 < ((feedbackState sample lam x0 p0 m).newTarget sample lam).card)

end FiniteSample

end OTSelector
