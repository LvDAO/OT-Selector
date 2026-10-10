import OTSelector.Feedback.FeedbackBulkStopping
import OTSelector.Feedback.FiniteEventBulkCount

/-!
# Finite bulk counts before the first exit

Strict survival before the first feedback bulk exit forces every event already attained by the
survival horizon to be accepted by the predictable bulk mask.  Consequently the bulk-thinned
source and target counts, their strict left counts, and the resulting left current agree with the
corresponding unthinned objects before that exit.
-/

open MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Acceptance and retained event times -/

/-- Any finite event attained by a strict survival horizon is accepted by the bulk mask. -/
theorem eventAccepted_safeFeedbackBulkMask_of_le_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (xi : FiniteSample n → WithTop ℝ≥0)
    (hxi : xi sample ≤ (t : WithTop ℝ≥0))
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.eventAccepted
      (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0) xi sample := by
  have hne : xi sample ≠ ⊤ := by
    intro htop
    rw [htop] at hxi
    exact WithTop.not_top_le_coe t hxi
  let u : ℝ≥0 := (xi sample).untop hne
  have hueq : (u : WithTop ℝ≥0) = xi sample := WithTop.coe_untop _ _
  have huexit : (u : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample :=
    (hueq.trans_le hxi).trans_lt ht
  have hbulk := feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime
    (n := n) hlam0 hlamHalf B x0 p0 u sample huexit
  refine ⟨hne, ?_⟩
  unfold stoppedValue
  rw [WithTop.untopA_eq_untop hne]
  change safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 u sample ≠ 0
  simp [safeFeedbackBulkMask, hbulk]

/-- A source event attained by a strict survival horizon is accepted by the bulk mask. -/
theorem eventAccepted_safeFeedbackBulkMask_source_of_le_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) (i : Fin n)
    (hi : sourceEventTime hlam0 hlamHalf x0 p0 i sample ≤ (t : WithTop ℝ≥0))
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.eventAccepted
      (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (sourceEventTime hlam0 hlamHalf x0 p0 i) sample := by
  exact eventAccepted_safeFeedbackBulkMask_of_le_of_lt_safeFeedbackBulkExitTime
    (n := n) hlam0 hlamHalf B x0 p0 t sample
    (sourceEventTime hlam0 hlamHalf x0 p0 i) hi ht

/-- A target event attained by a strict survival horizon is accepted by the bulk mask. -/
theorem eventAccepted_safeFeedbackBulkMask_target_of_le_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) (j : Fin n)
    (hj : targetEventTime hlam0 hlamHalf x0 p0 j sample ≤ (t : WithTop ℝ≥0))
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.eventAccepted
      (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (targetEventTime hlam0 hlamHalf x0 p0 j) sample := by
  exact eventAccepted_safeFeedbackBulkMask_of_le_of_lt_safeFeedbackBulkExitTime
    (n := n) hlam0 hlamHalf B x0 p0 t sample
    (targetEventTime hlam0 hlamHalf x0 p0 j) hj ht

/-- An attained source event retains its original time before the first bulk exit. -/
theorem safeSourceBulkEventTime_eq_sourceEventTime_of_le_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) (i : Fin n)
    (hi : sourceEventTime hlam0 hlamHalf x0 p0 i sample ≤ (t : WithTop ℝ≥0))
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    safeSourceBulkEventTime hlam0 hlamHalf B x0 p0 i sample =
      sourceEventTime hlam0 hlamHalf x0 p0 i sample := by
  simpa only [safeSourceBulkEventTime] using
    CountingProcess.thinnedEventTime_of_accepted
      (eventAccepted_safeFeedbackBulkMask_source_of_le_of_lt_safeFeedbackBulkExitTime
        (n := n) hlam0 hlamHalf B x0 p0 t sample i hi ht)

/-- An attained target event retains its original time before the first bulk exit. -/
theorem safeTargetBulkEventTime_eq_targetEventTime_of_le_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) (j : Fin n)
    (hj : targetEventTime hlam0 hlamHalf x0 p0 j sample ≤ (t : WithTop ℝ≥0))
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    safeTargetBulkEventTime hlam0 hlamHalf B x0 p0 j sample =
      targetEventTime hlam0 hlamHalf x0 p0 j sample := by
  simpa only [safeTargetBulkEventTime] using
    CountingProcess.thinnedEventTime_of_accepted
      (eventAccepted_safeFeedbackBulkMask_target_of_le_of_lt_safeFeedbackBulkExitTime
        (n := n) hlam0 hlamHalf B x0 p0 t sample j hj ht)

/-! ## Cumulative and strict-left count bridges -/

/-- Before the first bulk exit, thinning does not change any finite-family count. -/
theorem finiteEventCountThinned_safeFeedbackBulkMask_eq_finiteEventCountTop_of_lt_exit
    {m : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (xi : Fin m → FiniteSample n → WithTop ℝ≥0)
    (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0) xi t sample =
      CountingProcess.finiteEventCountTop xi t sample := by
  classical
  rw [CountingProcess.finiteEventCountThinned_eq_card_filter]
  unfold CountingProcess.finiteEventCountTop
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.left
  · intro hi
    exact ⟨hi, eventAccepted_safeFeedbackBulkMask_of_le_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B x0 p0 t sample (xi i) hi ht⟩

/-- The bulk source count equals the full source count before the first bulk exit. -/
theorem safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    safeSourceBulkCount hlam0 hlamHalf B x0 p0 t sample =
      safeSourceCount hlam0 hlamHalf x0 p0 t sample := by
  simpa only [safeSourceBulkCount, safeSourceCount] using
    (finiteEventCountThinned_safeFeedbackBulkMask_eq_finiteEventCountTop_of_lt_exit
      (n := n) hlam0 hlamHalf B x0 p0
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample ht)

/-- The bulk target count equals the full target count before the first bulk exit. -/
theorem safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    safeTargetBulkCount hlam0 hlamHalf B x0 p0 t sample =
      safeTargetCount hlam0 hlamHalf x0 p0 t sample := by
  simpa only [safeTargetBulkCount, safeTargetCount] using
    (finiteEventCountThinned_safeFeedbackBulkMask_eq_finiteEventCountTop_of_lt_exit
      (n := n) hlam0 hlamHalf B x0 p0
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample ht)

/-- Before the first bulk exit, thinning preserves the strict-left count of any finite family. -/
theorem countBefore_finiteEventCountThinned_safeFeedbackBulkMask_eq_of_lt_exit
    {m : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (xi : Fin m → FiniteSample n → WithTop ℝ≥0)
    (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.countBefore
        (CountingProcess.finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0) xi) t sample =
      CountingProcess.countBefore (CountingProcess.finiteEventCountTop xi) t sample := by
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
    have hacc := eventAccepted_safeFeedbackBulkMask_of_le_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B x0 p0 t sample (xi i) hi.le ht
    simpa only [CountingProcess.thinnedEventTime_of_accepted hacc] using hi

/-- The strict-left bulk source count equals the full source count before the first exit. -/
theorem countBefore_safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.countBefore
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0) t sample =
      CountingProcess.countBefore (safeSourceCount hlam0 hlamHalf x0 p0) t sample := by
  change CountingProcess.countBefore
      (CountingProcess.finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i)) t sample =
    CountingProcess.countBefore
      (CountingProcess.finiteEventCountTop
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i)) t sample
  exact countBefore_finiteEventCountThinned_safeFeedbackBulkMask_eq_of_lt_exit
    (n := n) hlam0 hlamHalf B x0 p0
    (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample ht

/-- The strict-left bulk target count equals the full target count before the first exit. -/
theorem countBefore_safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.countBefore
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample =
      CountingProcess.countBefore (safeTargetCount hlam0 hlamHalf x0 p0) t sample := by
  change CountingProcess.countBefore
      (CountingProcess.finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j)) t sample =
    CountingProcess.countBefore
      (CountingProcess.finiteEventCountTop
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j)) t sample
  exact countBefore_finiteEventCountThinned_safeFeedbackBulkMask_eq_of_lt_exit
    (n := n) hlam0 hlamHalf B x0 p0
    (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample ht

/-- All strict-left bulk and full counts agree at every time before a survival horizon. -/
theorem safeBulkCounts_countBefore_eq_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    ∀ u : ℝ≥0, u < t →
      CountingProcess.countBefore
          (safeSourceBulkCount hlam0 hlamHalf B x0 p0) u sample =
        CountingProcess.countBefore (safeSourceCount hlam0 hlamHalf x0 p0) u sample ∧
      CountingProcess.countBefore
          (safeTargetBulkCount hlam0 hlamHalf B x0 p0) u sample =
        CountingProcess.countBefore (safeTargetCount hlam0 hlamHalf x0 p0) u sample := by
  intro u hut
  have huexit : (u : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample :=
    (WithTop.coe_lt_coe.mpr hut).trans ht
  exact ⟨
    countBefore_safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B x0 p0 u sample huexit,
    countBefore_safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B x0 p0 u sample huexit⟩

/-! ## Left-current bridge -/

/-- The left current built from bulk counts is the safe pre-current before the first bulk exit. -/
theorem leftCurrentOfSafeBulkCounts_eq_safePreCurrentAt_of_lt_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample) :
    CountingProcess.leftCurrentOfCounts (safeK0 lam x0 p0)
        (safeSourceBulkCount hlam0 hlamHalf B x0 p0)
        (safeTargetBulkCount hlam0 hlamHalf B x0 p0) t sample =
      safePreCurrentAt hlam0 hlamHalf x0 p0 t sample := by
  unfold safePreCurrentAt CountingProcess.leftCurrentOfCounts
  rw [countBefore_safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B x0 p0 t sample ht,
    countBefore_safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime
      (n := n) hlam0 hlamHalf B x0 p0 t sample ht]

end FiniteSample

end OTSelector
