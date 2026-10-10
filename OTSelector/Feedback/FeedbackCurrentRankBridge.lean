import OTSelector.Feedback.FeedbackRegularitySurvival
import OTSelector.Feedback.FiniteEventBulkSurvival

/-!
# Actual feedback current and rank-discrepancy bridges

The recursive feedback state, the finite counting paths, and the final graph-intersection counts
encode the same post-jump current.  This file records the corresponding pointwise equalities.  The
bulk-thinned equality is deliberately restricted to strict survival before the first bulk exit.
-/

open scoped NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Strict-left counts through the closed bulk endpoint -/

/-- Through the closed bulk endpoint, thinning preserves the strict-left count of every finite
event family.  The endpoint itself need not satisfy strict bulk survival: every label counted on
the left occurs at a strictly earlier coordinate, where the existing acceptance theorem applies.
-/
theorem countBefore_finiteEventCountThinned_safeFeedbackBulkMask_eq_of_le_exit
    {m : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (xi : Fin m → FiniteSample n → WithTop ℝ≥0)
    (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.countBefore
        (CountingProcess.finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0) xi) t sample =
      CountingProcess.countBefore
        (CountingProcess.finiteEventCountTop xi) t sample := by
  classical
  change CountingProcess.countBefore
      (fun s sample' ↦ CountingProcess.finiteEventCountTop
        (fun i ↦ CountingProcess.thinnedEventTime
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0) (xi i)) s sample') t sample =
    CountingProcess.countBefore
      (fun s sample' ↦ CountingProcess.finiteEventCountTop xi s sample') t sample
  rw [CountingProcess.countBefore_finiteEventCountTop_eq_card_filter_lt,
    CountingProcess.countBefore_finiteEventCountTop_eq_card_filter_lt]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    have hacc : CountingProcess.eventAccepted
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0) (xi i) sample :=
      ((CountingProcess.thinnedEventTime_le_iff sample t).mp hi.le).1
    simpa only [CountingProcess.thinnedEventTime_of_accepted hacc] using hi
  · intro hi
    have hne : xi i sample ≠ ⊤ := by
      intro htop
      rw [htop] at hi
      exact (not_lt_of_ge le_top) hi
    let u : ℝ≥0 := (xi i sample).untop hne
    have hueq : (u : WithTop ℝ≥0) = xi i sample := WithTop.coe_untop _ _
    have huexit : (u : WithTop ℝ≥0) <
        safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample := by
      rw [hueq]
      exact hi.trans_le ht
    have hacc :=
      eventAccepted_safeFeedbackBulkMask_of_le_of_lt_safeFeedbackBulkExitTime
        (n := n) hlam0 hlamHalf B x0 p0 u sample (xi i)
        (by rw [hueq]) huexit
    simpa only [CountingProcess.thinnedEventTime_of_accepted hacc] using hi

/-- Through the closed bulk endpoint, the strict-left bulk source count equals the full strict-left
source count. -/
theorem countBefore_safeSourceBulkCount_eq_safeSourceCount_of_le_exit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.countBefore
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0) t sample =
      CountingProcess.countBefore
        (safeSourceCount hlam0 hlamHalf x0 p0) t sample := by
  exact countBefore_finiteEventCountThinned_safeFeedbackBulkMask_eq_of_le_exit
    (n := n) hlam0 hlamHalf B x0 p0
    (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample ht

/-- Through the closed bulk endpoint, the strict-left bulk target count equals the full strict-left
target count. -/
theorem countBefore_safeTargetBulkCount_eq_safeTargetCount_of_le_exit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.countBefore
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample =
      CountingProcess.countBefore
        (safeTargetCount hlam0 hlamHalf x0 p0) t sample := by
  exact countBefore_finiteEventCountThinned_safeFeedbackBulkMask_eq_of_le_exit
    (n := n) hlam0 hlamHalf B x0 p0
    (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample ht

/-- Through the closed bulk endpoint, the bulk strict-left current is the full safe pre-current.
-/
theorem leftCurrentOfSafeBulkCounts_eq_safePreCurrentAt_of_le_exit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.leftCurrentOfCounts (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample =
      safePreCurrentAt hlam0 hlamHalf x0 p0 t sample := by
  unfold safePreCurrentAt CountingProcess.leftCurrentOfCounts
  rw [countBefore_safeSourceBulkCount_eq_safeSourceCount_of_le_exit
      (n := n) hlam0 hlamHalf B x0 p0 t sample ht,
    countBefore_safeTargetBulkCount_eq_safeTargetCount_of_le_exit
      (n := n) hlam0 hlamHalf B x0 p0 t sample ht]

/-- On the no-tie event, the actual post-jump feedback current is exactly the rank discrepancy of
the final feedback graph at the current elapsed coordinate. -/
theorem safeCurrentAt_cast_eq_feedbackRankDiscrepancy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    (safeCurrentAt hlam0 hlamHalf x0 p0 t sample : ℝ) =
      RelativeVC.feedbackRankDiscrepancy
        (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t) := by
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t
  have hcurrent : state.current =
      (state.seenSource.card : ℤ) - state.seenTarget.card := by
    change (feedbackState sample lam x0 p0
      (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val).current = _
    exact sample.feedbackState_current_eq_card_sub lam x0 p0 _
  have hsource := feedbackStateAtElapsed_seenSource_card_eq_sourceIntersectionCount
    sample hlam0 hlamHalf x0 p0 t
  have htarget := feedbackStateAtElapsed_seenTarget_card_eq_targetIntersectionCount
    sample hlam0 hlamHalf x0 p0 t
  have hheight := sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
    hlam0 hlamHalf x0 p0 t hNoTie
  have hintersection := sample.intersectionCurrent_eq_feedbackRankDiscrepancy
    (sample.feedbackGraph hlam0 hlamHalf x0 p0) (elapsedFeedbackCoordinate x0 t)
  rw [safeCurrentAt, ite_eq_left hNoTie]
  change (state.current : ℝ) = _
  rw [hcurrent, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    hsource, htarget, hheight]
  exact hintersection

/-- Before the first bulk exit, the post-jump current of the bulk-thinned counts equals the full
safe post-jump current. -/
theorem currentOfSafeBulkCounts_eq_safeCurrentAt_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.currentOfCounts (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample =
      safeCurrentAt hlam0 hlamHalf x0 p0 t sample := by
  rw [CountingProcess.currentOfCounts,
    safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B x0 p0 t sample ht,
    safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B x0 p0 t sample ht]
  exact (safeCurrentAt_eq_K0_add_counts hlam0 hlamHalf x0 p0 t sample).symm

/-- Strict bulk survival identifies the actual bulk post-current with the final-graph rank
discrepancy, without a one-jump error. -/
theorem currentOfSafeBulkCounts_cast_eq_feedbackRankDiscrepancy_of_lt_exit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    (CountingProcess.currentOfCounts (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample : ℝ) =
      RelativeVC.feedbackRankDiscrepancy
        (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t) := by
  rw [currentOfSafeBulkCounts_eq_safeCurrentAt_of_lt_safeFeedbackBulkExitTime
    hlam0 hlamHalf B x0 p0 t sample ht]
  exact safeCurrentAt_cast_eq_feedbackRankDiscrepancy
    hlam0 hlamHalf x0 p0 t sample hNoTie

/-- Through the closed bulk endpoint, the final-graph rank discrepancy differs from the bulk
strict-left current by at most the single jump that can occur at the endpoint. -/
theorem abs_feedbackRankDiscrepancy_sub_leftCurrentOfSafeBulkCounts_le_one_of_le_exit
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (ht : (t : WithTop ℝ≥0) ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    |RelativeVC.feedbackRankDiscrepancy
        (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t) -
      (CountingProcess.leftCurrentOfCounts (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample : ℝ)| ≤ 1 := by
  rw [← safeCurrentAt_cast_eq_feedbackRankDiscrepancy
      hlam0 hlamHalf x0 p0 t sample hNoTie,
    leftCurrentOfSafeBulkCounts_eq_safePreCurrentAt_of_le_exit
      hlam0 hlamHalf B x0 p0 t sample ht,
    safeCurrentAt_eq_currentOfCounts]
  exact CountingProcess.abs_currentOfCounts_sub_leftCurrentOfCounts_le_one
    (safeSourceCount_isSimpleCountingProcess hlam0 hlamHalf x0 p0)
    (safeTargetCount_isSimpleCountingProcess hlam0 hlamHalf x0 p0)
    (safeCounts_noSimultaneousJumpsOn hlam0 hlamHalf x0 p0 t)

end FiniteSample

end OTSelector
