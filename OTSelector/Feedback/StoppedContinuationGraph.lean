import OTSelector.Feedback.FeedbackA2StoppedAssembly
import OTSelector.Feedback.HorizonGraph

/-!
# Unconditioned stopped continuation of the feedback graph

For every sample, the recursive curve is followed until the actual A1 stop, already capped by the
deterministic horizon, and is then frozen.  This differs both from the full recursion and from the
deterministic-horizon graph.  On the public stopped A2 good event the stop equals the horizon, so
the stopped graph agrees with `horizonFeedbackGraph`.
-/

open MeasureTheory Set
open scoped NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)


private theorem safeFeedbackA1StopTime_ne_top
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) :
    safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample ≠ ⊤ := by
  apply ne_top_of_le_ne_top WithTop.coe_ne_top
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The finite elapsed value of the A1 stop, which is capped by `T` by construction. -/
noncomputable def safeFeedbackA1StopElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) : ℝ≥0 :=
  (safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample).untop
    (sample.safeFeedbackA1StopTime_ne_top hlam0 hlamHalf eta B T)

theorem coe_safeFeedbackA1StopElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) :
    (sample.safeFeedbackA1StopElapsed hlam0 hlamHalf eta B T : WithTop ℝ≥0) =
      safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample := by
  exact WithTop.coe_untop _ _

theorem safeFeedbackA1StopElapsed_le_horizon
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) :
    sample.safeFeedbackA1StopElapsed hlam0 hlamHalf eta B T ≤ T := by
  apply WithTop.coe_le_coe.mp
  rw [sample.coe_safeFeedbackA1StopElapsed hlam0 hlamHalf eta B T]
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The full recursive graph frozen at the actual A1 stop capped by `T`. -/
noncomputable def stoppedContinuationFeedbackGraph
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) : FeedbackGraph lam :=
  sample.horizonFeedbackGraph hlam0 hlamHalf B
    (sample.safeFeedbackA1StopElapsed hlam0 hlamHalf eta B T)

/-- If the actual A1 stop reaches `T`, the stopped and deterministic-horizon graphs agree. -/
theorem stoppedContinuationFeedbackGraph_eq_horizon
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) :
    sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T =
      sample.horizonFeedbackGraph hlam0 hlamHalf B T := by
  have hElapsed : sample.safeFeedbackA1StopElapsed hlam0 hlamHalf eta B T = T := by
    apply WithTop.coe_eq_coe.mp
    rw [sample.coe_safeFeedbackA1StopElapsed hlam0 hlamHalf eta B T, hstop]
  exact congrArg (sample.horizonFeedbackGraph hlam0 hlamHalf B) hElapsed

/-- If the first bulk exit has a finite elapsed value strictly before the deterministic horizon,
then the safe height is exactly on the shear boundary there.  The spatial coordinate cannot cause
the exit on this window, so continuity forces the remaining closed constraint to be tight. -/
theorem abs_safeFeedbackHeightAtElapsed_eq_eighth_of_bulkExit_eq_of_lt_horizon
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) {T u : ℝ≥0}
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hExitEq : safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample =
      (u : WithTop ℝ≥0))
    (huT : u < T) :
    |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 u sample| = B / 8 := by
  let height : ℝ≥0 → ℝ := fun s ↦
    safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 s sample
  have hcont : Continuous height :=
    safeFeedbackHeightAtElapsed_continuous hlam0 hlamHalf B 0 sample
  have hzero : height 0 = 0 := by
    change safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 0 sample = 0
    by_cases hNoTie : sample.NoFeedbackTies lam B 0
    · rw [sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
        hlam0 hlamHalf B 0 0 hNoTie]
      simpa using sample.feedbackCurve_at_x0 hlam0 hlamHalf B 0
    · simp [safeFeedbackHeightAtElapsed, hNoTie]
  have hupper : |height u| ≤ B / 8 := by
    by_cases hu0 : u = 0
    · subst u
      rw [hzero, abs_zero]
      exact div_nonneg hB.le (by norm_num)
    · let closedRange : Set ℝ≥0 := {s | |height s| ≤ B / 8}
      have hclosed : IsClosed closedRange := by
        exact isClosed_le hcont.abs continuous_const
      have hsubset : Iio u ⊆ closedRange := by
        intro s hs
        have hsExit : (s : WithTop ℝ≥0) <
            safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample := by
          rw [hExitEq]
          exact_mod_cast hs
        exact (feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime
          (n := n) hlam0 hlamHalf B B 0 s sample hsExit).2.2
      have hnonempty : (Iio u : Set ℝ≥0).Nonempty := by
        refine ⟨0, ?_⟩
        exact pos_iff_ne_zero.mpr hu0
      have huClosure : u ∈ closure (Iio u : Set ℝ≥0) := by
        rw [closure_Iio' hnonempty]
        exact mem_Iic.mpr le_rfl
      exact closure_minimal hsubset hclosed huClosure
  apply le_antisymm hupper
  by_contra hnot
  have hstrict : |height u| < B / 8 := lt_of_not_ge hnot
  have huTR : (u : ℝ) < (T : ℝ) := by exact_mod_cast huT
  let margin : ℝ := B / 8 - |height u|
  have hmargin : 0 < margin := sub_pos.mpr hstrict
  obtain ⟨delta, hdelta, hmap⟩ :=
    Metric.continuousAt_iff.mp hcont.abs.continuousAt margin hmargin
  let stepR : ℝ := min (delta / 2) (((T : ℝ) - (u : ℝ)) / 2)
  have hstepR : 0 < stepR := by
    exact lt_min (half_pos hdelta) (half_pos (sub_pos.mpr huTR))
  let step : ℝ≥0 := ⟨stepR, hstepR.le⟩
  let v : ℝ≥0 := u + step
  have huv : u < v := by
    apply NNReal.coe_lt_coe.mp
    change (u : ℝ) < (u : ℝ) + stepR
    linarith
  have hvT : v < T := by
    apply NNReal.coe_lt_coe.mp
    change (u : ℝ) + stepR < (T : ℝ)
    have hstepHalf : stepR ≤ ((T : ℝ) - (u : ℝ)) / 2 := min_le_right _ _
    linarith
  have hExitV : safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample <
      (v : WithTop ℝ≥0) := by
    rw [hExitEq]
    exact_mod_cast huv
  rw [safeFeedbackBulkExitTime, MeasureTheory.hittingAfter_lt_iff] at hExitV
  obtain ⟨j, hj, hjBad⟩ := hExitV
  have hExitLeJ : safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample ≤
      (j : WithTop ℝ≥0) := by
    unfold safeFeedbackBulkExitTime
    exact MeasureTheory.hittingAfter_le_of_mem bot_le hjBad
  have huj : u ≤ j := by
    rw [hExitEq] at hExitLeJ
    exact_mod_cast hExitLeJ
  have hjv : j < v := hj.2
  have hjT : j < T := hjv.trans hvT
  have hjDist : dist j u < delta := by
    have hsub : 0 ≤ (j : ℝ) - (u : ℝ) := sub_nonneg.mpr (by exact_mod_cast huj)
    rw [NNReal.dist_eq, abs_of_nonneg hsub]
    have hjvR : (j : ℝ) < (v : ℝ) := by exact_mod_cast hjv
    have hvR : (v : ℝ) = (u : ℝ) + stepR := by rfl
    rw [hvR] at hjvR
    have hstepDelta : stepR ≤ delta / 2 := min_le_left _ _
    linarith
  have hheightDist : dist |height j| |height u| < margin := hmap hjDist
  have hjHeight : |height j| < B / 8 := by
    rw [Real.dist_eq] at hheightDist
    have hdiff : |height j| - |height u| < margin :=
      (le_abs_self (|height j| - |height u|)).trans_lt hheightDist
    dsimp only [margin] at hdiff
    linarith
  change ¬feedbackBulkRegion n B
      (elapsedFeedbackCoordinate B j) (height j) at hjBad
  apply hjBad
  refine ⟨?_, ?_, hjHeight.le⟩
  · simp [elapsedFeedbackCoordinate]
  · have hjTR : (j : ℝ) < (T : ℝ) := by exact_mod_cast hjT
    simp only [elapsedFeedbackCoordinate]
    linarith

/-- A finite bulk exit before the horizon supplies its elapsed coordinate and the exact shear
boundary value there. -/
theorem exists_bulkExit_elapsed_height_eq_eighth_of_lt_horizon
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) {T : ℝ≥0}
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hExit : safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample <
      (T : WithTop ℝ≥0)) :
    ∃ u : ℝ≥0, u < T ∧
      safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample =
        (u : WithTop ℝ≥0) ∧
      |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 u sample| = B / 8 := by
  have hne : safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample ≠ ⊤ :=
    ne_top_of_lt hExit
  let u : ℝ≥0 :=
    (safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample).untop hne
  have hExitEq : safeFeedbackBulkExitTime hlam0 hlamHalf B B 0 sample =
      (u : WithTop ℝ≥0) := by
    exact (WithTop.coe_untop _ hne).symm
  have huT : u < T := by
    apply WithTop.coe_lt_coe.mp
    rw [← hExitEq]
    exact hExit
  exact ⟨u, huT, hExitEq,
    sample.abs_safeFeedbackHeightAtElapsed_eq_eighth_of_bulkExit_eq_of_lt_horizon
      hlam0 hlamHalf hB hRight hExitEq huT⟩

/-- The public stopped A2 good event excludes a bulk exit before the deterministic horizon. -/
theorem feedbackA2StoppedGoodEvent.horizon_le_safeFeedbackBulkExitTime
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n) (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num))
        eta amplitude globalQ endpointQ B T R) :
    (T : WithTop ℝ≥0) ≤ safeFeedbackBulkExitTime
      hlam0.le (hlam.trans (by norm_num)) B B 0 sample := by
  by_contra hnot
  have hExit := lt_of_not_ge hnot
  obtain ⟨u, huT, _, hheight⟩ :=
    sample.exists_bulkExit_elapsed_height_eq_eighth_of_lt_horizon
      hlam0.le (hlam.trans (by norm_num)) hB hRight hExit
  have hstrict := feedbackA2StoppedGoodEvent.abs_safeFeedbackHeightAtElapsed_lt
    hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood huT
  exact (ne_of_lt hstrict) hheight

/-- On the public stopped A2 good event, the capped A1 stop reaches the deterministic horizon. -/
theorem feedbackA2StoppedGoodEvent.safeFeedbackA1StopTime_eq_horizon
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n) (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num))
        eta amplitude globalQ endpointQ B T R) :
    safeFeedbackA1StopTime
        hlam0.le (hlam.trans (by norm_num)) eta B B 0 T sample =
      (T : WithTop ℝ≥0) := by
  have hA1 : sample ∈ feedbackA1GoodEvent n lam B 0 := by
    by_contra hbad
    apply hgood
    exact Or.inr (Or.inr (Or.inl hbad))
  have hbulk := feedbackA2StoppedGoodEvent.horizon_le_safeFeedbackBulkExitTime
    sample hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood
  rw [safeFeedbackA1StopTime_eq_min_bulkExit_horizon_of_good
    hn hlam0.le (hlam.trans (by norm_num)) heta hB B 0 T sample hA1 hsqrt hlinear]
  exact min_eq_right hbulk

/-- On the public stopped A2 good event, the unconditioned stopped graph agrees with the
deterministic-horizon graph. -/
theorem feedbackA2StoppedGoodEvent.stoppedContinuationFeedbackGraph_eq_horizon
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 8)
    {eta amplitude globalQ endpointQ B : ℝ} {T : ℝ≥0} {R : ℕ}
    (hn : 4 ≤ n) (hB : 0 < B) (hBn : B ≤ n) (heta : 0 ≤ eta)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * B / 16))
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < B / 4)
    (hgood : sample ∈ feedbackA2StoppedGoodEvent
      hlam0.le (hlam.trans (by norm_num))
        eta amplitude globalQ endpointQ B T R) :
    sample.stoppedContinuationFeedbackGraph
        hlam0.le (hlam.trans (by norm_num)) eta B T =
      sample.horizonFeedbackGraph
        hlam0.le (hlam.trans (by norm_num)) B T := by
  apply sample.stoppedContinuationFeedbackGraph_eq_horizon
  exact feedbackA2StoppedGoodEvent.safeFeedbackA1StopTime_eq_horizon
    sample hlam0 hlam hn hB hBn heta hRight hsqrt hlinear hthreshold hgood

end FiniteSample

end OTSelector
