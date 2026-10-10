import OTSelector.Feedback.FeedbackGraphFrozenOccupation
import OTSelector.Feedback.FeedbackI3SegmentedIntensity

/-!
# A genuine short bulk window supplies the crossing-prefix geometry

The window ends strictly before the freezing time.  This avoids any convention about an event
at the stopping boundary and uses only the already proved strict-stop lower-occupation bound.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal ProbabilityTheory

namespace OTSelector.FiniteSample
open CountingProcess
variable {n : ℕ}

private theorem cut_count_increment_le_window (v : Fin n → ℝ) (x y R W : ℝ)
    (hx : R - W ≤ x) (hy : y ≤ R) :
    ((Finset.univ.filter fun i ↦ v i ≤ y).card : ℝ) -
      (Finset.univ.filter fun i ↦ v i ≤ x).card ≤
        (Finset.univ.filter fun i ↦ R - W ≤ v i ∧ v i ≤ R).card := by
  have hpoint (i : Fin n) : (if v i ≤ y then (1 : ℝ) else 0) -
      (if v i ≤ x then (1 : ℝ) else 0) ≤
        if R - W ≤ v i ∧ v i ≤ R then (1 : ℝ) else 0 := by
    by_cases hiy : v i ≤ y
    · by_cases hix : v i ≤ x
      · simp only [ite_eq_left hiy, ite_eq_left hix, sub_self]
        split_ifs <;> norm_num
      · have hiw : R - W ≤ v i ∧ v i ≤ R := ⟨hx.trans (le_of_not_ge hix), hiy.trans hy⟩
        simp [hiy, hix, hiw]
    · simp only [ite_eq_right hiy, zero_sub]
      split_ifs <;> norm_num
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpoint i)
  simpa only [Finset.sum_sub_distrib, Finset.sum_boole] using hsum

theorem sourceFullCount_eq_stoppedGraphCut_of_survival
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T u : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) (hu : u ≤ T) :
    sourceFullCount hlam0 hlamHalf B u sample = sample.graphSourceCutCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (u : ℝ)) := by
  rw [sample.stoppedContinuationFeedbackGraph_eq_horizon hlam0 hlamHalf eta B T hstop]
  change sourceFullCount hlam0 hlamHalf B u sample =
    sample.sourceIntersectionCount (sample.horizonFeedbackGraph hlam0 hlamHalf B T) _
  rw [sourceFullCount_eq_sourceIntersectionCount_at_B_add hlam0 hlamHalf B u sample hNoTie,
    sample.sourceIntersectionCount_eq_filter_phase, sample.sourceIntersectionCount_eq_filter_phase,
    sample.horizonFeedbackGraph_curve_eq_feedbackCurve_of_le_right hlam0 hlamHalf B T
      (show B + (u : ℝ) ≤ B + (T : ℝ) from add_le_add le_rfl (show (u : ℝ) ≤ T from hu))]
  rfl

theorem targetFullCount_eq_stoppedGraphCut_of_survival
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T u : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) (hu : u ≤ T) :
    targetFullCount hlam0 hlamHalf B u sample = sample.graphTargetCutCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (u : ℝ)) := by
  rw [sample.stoppedContinuationFeedbackGraph_eq_horizon hlam0 hlamHalf eta B T hstop]
  change targetFullCount hlam0 hlamHalf B u sample =
    sample.targetIntersectionCount (sample.horizonFeedbackGraph hlam0 hlamHalf B T) _
  rw [targetFullCount_eq_targetIntersectionCount_at_B_add hlam0 hlamHalf B u sample hNoTie,
    sample.targetIntersectionCount_eq_filter_phase, sample.targetIntersectionCount_eq_filter_phase,
    sample.horizonFeedbackGraph_curve_eq_feedbackCurve_of_le_right hlam0 hlamHalf B T
      (show B + (u : ℝ) ≤ B + (T : ℝ) from add_le_add le_rfl (show (u : ℝ) ≤ T from hu))]
  rfl

/-- The two exceptional lower-occupation events for a deterministic short bulk window. -/
def bulkBackwardWindowBadEvent {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T s r : ℝ≥0) : Set (FiniteSample n) :=
  stoppedLowerOccupationEvent (safeSourceBulkCount hlam0 hlamHalf B B 0) (fun _ ↦ s)
      (safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T)
      (lowerOccupationCountRate ((1 : ℝ) / 2)) r ∪
    stoppedLowerOccupationEvent (safeTargetBulkCount hlam0 hlamHalf B B 0) (fun _ ↦ s)
      (safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T)
      (lowerOccupationCountRate ((1 : ℝ) / 2)) r

theorem measurableSet_bulkBackwardWindowBadEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta : ℝ) {B : ℝ} (hB : 0 < B) (T s r : ℝ≥0) :
    MeasurableSet (bulkBackwardWindowBadEvent (n := n) hlam0 hlamHalf eta B T s r) := by
  have hs := isStoppingTime_const
    (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0) s
  have hA1 := safeFeedbackA1StopTime_isStoppingTime (n := n) hlam0 hlamHalf hB eta B 0 T
  exact (measurableSet_stoppedLowerOccupationEvent_bounded
    (safeSourceBulkCount_isSimpleCountingProcess hlam0 hlamHalf B B 0)
    hs (fun _ ↦ le_rfl) hA1).union
      (measurableSet_stoppedLowerOccupationEvent_bounded
        (safeTargetBulkCount_isSimpleCountingProcess hlam0 hlamHalf B B 0)
        hs (fun _ ↦ le_rfl) hA1)

/-- The actual finite-sample probability cost is exponentially small in the short duration. -/
theorem measureReal_bulkBackwardWindowBadEvent_le
    {lam eta B : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    (hn : 0 < n) (hB : 0 < B) (heta0 : 0 ≤ eta)
    (hetaSmall : eta * (2 + lam) ≤ lam) (T s r : ℝ≥0) (hr : 0 < r) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real (bulkBackwardWindowBadEvent hlam0.le (by linarith) eta B T s r) ≤
      2 * Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (r : ℝ)) := by
  let hlamHalf : lam < 1 / 2 := by linarith
  have hs := isStoppingTime_const
    (usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0) s
  have hA1 := safeFeedbackA1StopTime_isStoppingTime (n := n) hlam0.le hlamHalf hB eta B 0 T
  have hsource := safeSourceBulkCount_condExp_lowerOccupation_through_A1
    (x0 := B) (p0 := 0) hlam0 hlam hn hB heta0 hetaSmall T hr hs (fun _ ↦ le_rfl)
  have htarget := safeTargetBulkCount_condExp_lowerOccupation_through_A1
    (x0 := B) (p0 := 0) hlam0 hlam hn hB heta0 hetaSmall T hr hs (fun _ ↦ le_rfl)
  have hsourceP := measureReal_le_of_condExp_indicator_le_const hs.measurableSpace_le
    (measurableSet_stoppedLowerOccupationEvent_bounded
      (safeSourceBulkCount_isSimpleCountingProcess hlam0.le hlamHalf B B 0)
      hs (fun _ ↦ le_rfl) hA1) hsource
  have htargetP := measureReal_le_of_condExp_indicator_le_const hs.measurableSpace_le
    (measurableSet_stoppedLowerOccupationEvent_bounded
      (safeTargetBulkCount_isSimpleCountingProcess hlam0.le hlamHalf B B 0)
      hs (fun _ ↦ le_rfl) hA1) htarget
  unfold bulkBackwardWindowBadEvent
  exact (measureReal_union_le _ _).trans (by linarith only [hsourceP, htargetP])

/-- A thinned source increment strictly before freezing is contained in the physical backward
window of the actual stopped graph. -/
theorem sourceBulkIncrement_le_stoppedGraphBackwardWindow
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T s r : ℝ≥0) (W : ℝ) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) (hend : s + r < T) (hstart : (T : ℝ) - W ≤ s) :
    (safeSourceBulkCount hlam0 hlamHalf B B 0 (s + r) sample : ℝ) -
      safeSourceBulkCount hlam0 hlamHalf B B 0 s sample ≤
        (sample.graphSourceBackwardWindowCount
          (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ)) W : ℝ) := by
  have hsT : s ≤ T := (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ r from bot_le)).trans hend.le
  have hA1Bulk : (T : WithTop ℝ≥0) ≤ safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
    rw [← hstop]
    exact min_le_left _ _
  have hendExit : ((s + r : ℝ≥0) : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    (WithTop.coe_lt_coe.mpr hend).trans_le hA1Bulk
  have hsExit : (s : WithTop ℝ≥0) < safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    (WithTop.coe_le_coe.mpr (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ r from bot_le))).trans_lt hendExit
  have hdiff : (safeSourceBulkCount hlam0 hlamHalf B B 0 (s + r) sample : ℝ) -
      safeSourceBulkCount hlam0 hlamHalf B B 0 s sample =
        (sample.graphSourceCutCount
          (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + ((s + r : ℝ≥0) : ℝ)) : ℝ) -
        sample.graphSourceCutCount
          (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (s : ℝ)) := by
    rw [← sourceFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T (s + r)
        sample hNoTie hstop hend.le,
      ← sourceFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T s
        sample hNoTie hstop hsT,
      safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime
        hlam0 hlamHalf B B 0 (s + r) sample hendExit,
      safeSourceBulkCount_eq_safeSourceCount_of_lt_safeFeedbackBulkExitTime
        hlam0 hlamHalf B B 0 s sample hsExit,
      sourceFullCount_eq_initial_card_add_safeSourceCount,
      sourceFullCount_eq_initial_card_add_safeSourceCount]
    push_cast
    ring
  rw [hdiff]
  exact cut_count_increment_le_window _ _ _ _ _ (by linarith) (add_le_add le_rfl (show ((s + r : ℝ≥0) : ℝ) ≤ T from hend.le))

/-- Target counterpart of the same physical-window containment. -/
theorem targetBulkIncrement_le_stoppedGraphBackwardWindow
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T s r : ℝ≥0) (W : ℝ) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) (hend : s + r < T) (hstart : (T : ℝ) - W ≤ s) :
    (safeTargetBulkCount hlam0 hlamHalf B B 0 (s + r) sample : ℝ) -
      safeTargetBulkCount hlam0 hlamHalf B B 0 s sample ≤
        (sample.graphTargetBackwardWindowCount
          (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ)) W : ℝ) := by
  have hsT : s ≤ T := (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ r from bot_le)).trans hend.le
  have hA1Bulk : (T : WithTop ℝ≥0) ≤ safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
    rw [← hstop]
    exact min_le_left _ _
  have hendExit : ((s + r : ℝ≥0) : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    (WithTop.coe_lt_coe.mpr hend).trans_le hA1Bulk
  have hsExit : (s : WithTop ℝ≥0) < safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample :=
    (WithTop.coe_le_coe.mpr (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ r from bot_le))).trans_lt hendExit
  have hdiff : (safeTargetBulkCount hlam0 hlamHalf B B 0 (s + r) sample : ℝ) -
      safeTargetBulkCount hlam0 hlamHalf B B 0 s sample =
        (sample.graphTargetCutCount
          (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + ((s + r : ℝ≥0) : ℝ)) : ℝ) -
        sample.graphTargetCutCount
          (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (s : ℝ)) := by
    rw [← targetFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T (s + r)
        sample hNoTie hstop hend.le,
      ← targetFullCount_eq_stoppedGraphCut_of_survival hlam0 hlamHalf eta B T s
        sample hNoTie hstop hsT,
      safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime
        hlam0 hlamHalf B B 0 (s + r) sample hendExit,
      safeTargetBulkCount_eq_safeTargetCount_of_lt_safeFeedbackBulkExitTime
        hlam0 hlamHalf B B 0 s sample hsExit,
      targetFullCount_eq_initial_card_add_safeTargetCount,
      targetFullCount_eq_initial_card_add_safeTargetCount]
    push_cast
    ring
  rw [hdiff]
  exact cut_count_increment_le_window _ _ _ _ _ (by linarith) (add_le_add le_rfl (show ((s + r : ℝ≥0) : ℝ) ≤ T from hend.le))

/-- Outside two genuine exponentially unlikely count events, a bounded current supplies both
backward-window hypotheses for the crossing-prefix energy bound. -/
theorem stoppedGraph_backwardWindows_of_not_bulkBackwardWindowBadEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T s r : ℝ≥0) (W : ℝ) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) (hend : s + r < T) (hstart : (T : ℝ) - W ≤ s)
    (hcurrent : |sample.graphRankCurrent
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ))| ≤
        lowerOccupationCountRate ((1 : ℝ) / 2) * (r : ℝ))
    (hgood : sample ∉ bulkBackwardWindowBadEvent hlam0 hlamHalf eta B T s r) :
    sample.graphCrossingRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ)) ≤
      sample.graphSourceBackwardWindowCount
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ)) W ∧
    sample.graphCrossingRankCount
      (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ)) ≤
      sample.graphTargetBackwardWindowCount
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) (B + (T : ℝ)) W := by
  have hsurv : ((s + r : ℝ≥0) : WithTop ℝ≥0) ≤
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample := by
    rw [hstop]
    exact WithTop.coe_le_coe.mpr hend.le
  have hs : lowerOccupationCountRate ((1 : ℝ) / 2) * (r : ℝ) <
      (safeSourceBulkCount hlam0 hlamHalf B B 0 (s + r) sample : ℝ) -
        safeSourceBulkCount hlam0 hlamHalf B B 0 s sample :=
    lt_of_not_ge fun h ↦ hgood (Or.inl ⟨h, hsurv⟩)
  have ht : lowerOccupationCountRate ((1 : ℝ) / 2) * (r : ℝ) <
      (safeTargetBulkCount hlam0 hlamHalf B B 0 (s + r) sample : ℝ) -
        safeTargetBulkCount hlam0 hlamHalf B B 0 s sample :=
    lt_of_not_ge fun h ↦ hgood (Or.inr ⟨h, hsurv⟩)
  constructor
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [sample.graphCrossingRankCount_cast_eq_abs_current]
    exact (hcurrent.trans hs.le).trans (sourceBulkIncrement_le_stoppedGraphBackwardWindow
      hlam0 hlamHalf eta B T s r W sample hNoTie hstop hend hstart)
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [sample.graphCrossingRankCount_cast_eq_abs_current]
    exact (hcurrent.trans ht.le).trans (targetBulkIncrement_le_stoppedGraphBackwardWindow
      hlam0 hlamHalf eta B T s r W sample hNoTie hstop hend hstart)

end OTSelector.FiniteSample
