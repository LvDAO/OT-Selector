import OTSelector.Feedback.FeedbackCurrentRankBridge
import OTSelector.Feedback.FeedbackEventTimeNull
import OTSelector.Feedback.FeedbackA1Stopping
import OTSelector.Feedback.FeedbackA1StoppedDrift

/-!
# Closed A1 endpoint bridge

At a deterministic positive elapsed coordinate, actual feedback knots are absent almost surely.
Consequently the post-current and strict-left current coincide there.  On the right-closed A1
survival event this identifies the terminal bulk current exactly with the final-graph rank
discrepancy.  The endpoint event itself remains `T ≤ τ`; singleton nullity is used only to choose
the a.e. representative of the terminal current.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace OTSelector

namespace FiniteSample

open CountingProcess

variable {n : ℕ}

private theorem safeK0_mem_Icc_endpoint
    (lam x0 p0 : ℝ) (sample : FiniteSample n) :
    -(n : ℤ) ≤ safeK0 lam x0 p0 sample ∧ safeK0 lam x0 p0 sample ≤ (n : ℤ) := by
  classical
  have hsource : (sample.initialSeenSource x0 p0).card ≤ n := by
    simpa using Finset.card_le_card
      (Finset.subset_univ (sample.initialSeenSource x0 p0))
  have htarget : (sample.initialSeenTarget x0 p0).card ≤ n := by
    simpa using Finset.card_le_card
      (Finset.subset_univ (sample.initialSeenTarget x0 p0))
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · simp only [safeK0, hgood, ite_true, initialFeedbackCurrent]
    constructor <;> omega
  · simp [safeK0, hgood]

/-- The post-current of the two actual bulk counts is still strictly inside the standard A1
cutoff.  This closes the terminal unclipping step without an additional cutoff hypothesis. -/
theorem currentOfSafeBulkCounts_strictInterior_post
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    -(feedbackA1CurrentCutoff n : ℤ) <
        currentOfCounts (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
          (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample ∧
      currentOfCounts (safeK0 lam x0 p0)
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
          (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample <
        (feedbackA1CurrentCutoff n : ℤ) := by
  have hsource : safeSourceBulkCount hlam0 hlamHalf B x0 p0 t sample ≤ n := by
    simpa only [safeSourceBulkCount] using
      finiteEventCountThinned_le
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample
  have htarget : safeTargetBulkCount hlam0 hlamHalf B x0 p0 t sample ≤ n := by
    simpa only [safeTargetBulkCount] using
      finiteEventCountThinned_le
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample
  have hK0 := safeK0_mem_Icc_endpoint (n := n) lam x0 p0 sample
  simp only [currentOfCounts, feedbackA1CurrentCutoff]
  constructor <;> omega

private theorem finiteEventCountTop_eq_countBefore_of_no_event
    {Ω : Type*} {m : ℕ} (xi : Fin m → Ω → WithTop ℝ≥0)
    (T : ℝ≥0) (omega : Ω)
    (hne : ∀ i, xi i omega ≠ (T : WithTop ℝ≥0)) :
    finiteEventCountTop xi T omega =
      countBefore (fun s omega' ↦ finiteEventCountTop xi s omega') T omega := by
  classical
  change (Finset.univ.filter
      (fun i : Fin m ↦ xi i omega ≤ (T : WithTop ℝ≥0))).card = _
  rw [countBefore_finiteEventCountTop_eq_card_filter_lt]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hi ↦ lt_of_le_of_ne hi (hne i), fun hi ↦ hi.le⟩

private theorem finiteEventCountThinned_eq_countBefore_of_no_event
    {Ω : Type*} {m : ℕ} (G : ℝ≥0 → Ω → ℝ)
    (xi : Fin m → Ω → WithTop ℝ≥0) (T : ℝ≥0) (omega : Ω)
    (hne : ∀ i, xi i omega ≠ (T : WithTop ℝ≥0)) :
    finiteEventCountThinned G xi T omega =
      countBefore (finiteEventCountThinned G xi) T omega := by
  unfold finiteEventCountThinned
  apply finiteEventCountTop_eq_countBefore_of_no_event
  intro i
  by_cases hacc : eventAccepted G (xi i) omega
  · rw [thinnedEventTime_of_accepted hacc]
    exact hne i
  · rw [thinnedEventTime_of_not_accepted hacc]
    exact WithTop.top_ne_coe

private theorem sourceEventTime_ne_of_noFeedbackEventAt
    (sample : FiniteSample n) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0)
    (hNoEvent : sample.NoFeedbackEventAt lam x0 p0
      (elapsedFeedbackCoordinate x0 T)) (i : Fin n) :
    sourceEventTime hlam0 hlamHalf x0 p0 i sample ≠ (T : WithTop ℝ≥0) := by
  intro heq
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · simp only [sourceEventTime, hgood, ↓reduceIte] at heq
    by_cases hS : (sample.sourceEventSet lam x0 p0 i).Nonempty
    · rw [sourceEventTimeRaw, dite_eq_left hS] at heq
      let m := (sample.sourceEventSet lam x0 p0 i).min' hS
      have hnn : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) = T :=
        WithTop.coe_eq_coe.mp heq
      have hreal := congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) hnn
      apply hNoEvent (m.val + 1) (by omega) (by omega)
      simp only [coe_elapsedFeedbackKnot] at hreal
      unfold elapsedFeedbackCoordinate
      linarith
    · rw [sourceEventTimeRaw, dite_eq_right hS] at heq
      exact WithTop.coe_ne_top heq.symm
  · have htop : sourceEventTime hlam0 hlamHalf x0 p0 i sample = ⊤ := by
      simp [sourceEventTime, hgood]
    rw [htop] at heq
    exact WithTop.coe_ne_top heq.symm

private theorem targetEventTime_ne_of_noFeedbackEventAt
    (sample : FiniteSample n) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0)
    (hNoEvent : sample.NoFeedbackEventAt lam x0 p0
      (elapsedFeedbackCoordinate x0 T)) (j : Fin n) :
    targetEventTime hlam0 hlamHalf x0 p0 j sample ≠ (T : WithTop ℝ≥0) := by
  intro heq
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · simp only [targetEventTime, hgood, ↓reduceIte] at heq
    by_cases hS : (sample.targetEventSet lam x0 p0 j).Nonempty
    · rw [targetEventTimeRaw, dite_eq_left hS] at heq
      let m := (sample.targetEventSet lam x0 p0 j).min' hS
      have hnn : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) = T :=
        WithTop.coe_eq_coe.mp heq
      have hreal := congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) hnn
      apply hNoEvent (m.val + 1) (by omega) (by omega)
      simp only [coe_elapsedFeedbackKnot] at hreal
      unfold elapsedFeedbackCoordinate
      linarith
    · rw [targetEventTimeRaw, dite_eq_right hS] at heq
      exact WithTop.coe_ne_top heq.symm
  · have htop : targetEventTime hlam0 hlamHalf x0 p0 j sample = ⊤ := by
      simp [targetEventTime, hgood]
    rw [htop] at heq
    exact WithTop.coe_ne_top heq.symm

/-- Almost surely, closed A1 survival at the deterministic terminal coordinate identifies the
actual bulk post-current with the final-graph rank discrepancy.  In particular, the conclusion
uses `T ≤ τA1`, not a strict endpoint event. -/
theorem currentOfSafeBulkCounts_cast_eq_feedbackRankDiscrepancy_ae_on_closed_A1_endpoint
    {lam eta B : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      (T : WithTop ℝ≥0) ≤
          safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample →
        (currentOfCounts (safeK0 lam B 0)
            (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
            (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) T sample : ℝ) =
          RelativeVC.feedbackRankDiscrepancy
            (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
            (safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 T sample)
            (elapsedFeedbackCoordinate B T) := by
  have hBx : B < elapsedFeedbackCoordinate B T := by
    unfold elapsedFeedbackCoordinate
    exact lt_add_of_pos_right B (by exact_mod_cast hT)
  filter_upwards [finiteSampleLaw_noFeedbackTies_ae
      (n := n) (x0 := B) (p0 := 0) hlam0 hlamHalf,
    noFeedbackEventAt_ae (n := n) (p0 := 0) hlam0 hlamHalf hBx] with
      sample hNoTie hNoEvent
  intro hAlive
  have hBulk : (T : WithTop ℝ≥0) ≤
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    hAlive.trans (min_le_left _ _)
  have hSourceNe : ∀ i : Fin n,
      sourceEventTime hlam0 hlamHalf B 0 i sample ≠ (T : WithTop ℝ≥0) :=
    fun i ↦ sourceEventTime_ne_of_noFeedbackEventAt
      sample hlam0 hlamHalf B 0 T hNoEvent i
  have hTargetNe : ∀ j : Fin n,
      targetEventTime hlam0 hlamHalf B 0 j sample ≠ (T : WithTop ℝ≥0) :=
    fun j ↦ targetEventTime_ne_of_noFeedbackEventAt
      sample hlam0 hlamHalf B 0 T hNoEvent j
  have hSourceFull : safeSourceCount hlam0 hlamHalf B 0 T sample =
      countBefore (safeSourceCount (n := n) hlam0 hlamHalf B 0) T sample := by
    unfold safeSourceCount
    exact finiteEventCountTop_eq_countBefore_of_no_event
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf B 0 i) T sample hSourceNe
  have hTargetFull : safeTargetCount hlam0 hlamHalf B 0 T sample =
      countBefore (safeTargetCount (n := n) hlam0 hlamHalf B 0) T sample := by
    unfold safeTargetCount
    exact finiteEventCountTop_eq_countBefore_of_no_event
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf B 0 j) T sample hTargetNe
  have hSourceBulk : safeSourceBulkCount hlam0 hlamHalf B B 0 T sample =
      countBefore (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0) T sample := by
    unfold safeSourceBulkCount
    exact finiteEventCountThinned_eq_countBefore_of_no_event
      (safeFeedbackBulkMask hlam0 hlamHalf B B 0)
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf B 0 i) T sample hSourceNe
  have hTargetBulk : safeTargetBulkCount hlam0 hlamHalf B B 0 T sample =
      countBefore (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) T sample := by
    unfold safeTargetBulkCount
    exact finiteEventCountThinned_eq_countBefore_of_no_event
      (safeFeedbackBulkMask hlam0 hlamHalf B B 0)
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf B 0 j) T sample hTargetNe
  have hBulkPostLeft :
      currentOfCounts (safeK0 lam B 0)
          (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
          (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) T sample =
        leftCurrentOfCounts (safeK0 lam B 0)
          (safeSourceBulkCount (n := n) hlam0 hlamHalf B B 0)
          (safeTargetBulkCount (n := n) hlam0 hlamHalf B B 0) T sample := by
    unfold currentOfCounts leftCurrentOfCounts
    rw [hSourceBulk, hTargetBulk]
  have hPrePost : safePreCurrentAt hlam0 hlamHalf B 0 T sample =
      safeCurrentAt hlam0 hlamHalf B 0 T sample := by
    unfold safePreCurrentAt leftCurrentOfCounts
    rw [← hSourceFull, ← hTargetFull]
    exact (safeCurrentAt_eq_K0_add_counts hlam0 hlamHalf B 0 T sample).symm
  rw [hBulkPostLeft,
    leftCurrentOfSafeBulkCounts_eq_safePreCurrentAt_of_le_exit
      hlam0 hlamHalf B B 0 T sample hBulk,
    hPrePost]
  exact safeCurrentAt_cast_eq_feedbackRankDiscrepancy
    hlam0 hlamHalf B 0 T sample hNoTie

end FiniteSample

end OTSelector
