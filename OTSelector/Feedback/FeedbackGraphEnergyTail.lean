import OTSelector.Feedback.FeedbackGraphEnergyEvents
import OTSelector.Feedback.FeedbackRightIntervalCountsEnergy
import OTSelector.Feedback.FeedbackLeftRateSurvival

/-!
# Actual finite-sample graph-energy tail

A finite union of the proved bulk, boundary, interval, and energy events controls the actual
stopped comparison graph.  All probability bounds use the original finite-sample law.  This
module keeps the finite numerical conditions explicit; asymptotic parameter choices are separate.
-/

open MeasureTheory Set
open scoped BigOperators NNReal Classical

namespace OTSelector.FiniteSample

open CountingProcess

attribute [local irreducible] rightBoundaryFrozenCurrent rightBoundaryFrozenEnergy
  feedbackPreRightEnergy

variable {n : ℕ}

/-- Explicit finite-`n` energy tail for the actual stopped comparison graph. -/
theorem measureReal_stoppedGraphComparisonEnergy_tail_le
    {lam eta amplitude globalQ endpointQ Kpre Kright L a W : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 8) (hn : 4 ≤ n) (hamp : 0 < amplitude)
    (B T s r : ℝ≥0) (R : ℕ)
    (hB : (B : ℝ) = amplitude * Real.sqrt n) (hB1 : 1 ≤ (B : ℝ))
    (hBquarter : 4 * (B : ℝ) ≤ n)
    (hboundary : (B : ℝ) + T = (n : ℝ) - B) (hT : 0 < T)
    (heta0 : 0 ≤ eta) (hetaSmall : eta * (2 + lam) ≤ lam)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤ eta ^ 2 * (13 * (B : ℝ) / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤ eta * (13 * (B : ℝ) / 16))
    (hthreshold : 2 * (globalQ + 32) * Real.sqrt n + (2 * (R : ℝ) + 2) < (B : ℝ) / 4)
    (hL : 0 ≤ L) (ha : 0 < a) (hW : 0 ≤ W) (hr : 0 < r)
    (hKpre : 0 < Kpre) (hKright : 0 < Kright)
    (herr : 60 * Real.log n + 1 / 4 ≤ Real.sqrt B)
    (hgeometry : (B : ℝ) + T ≤ (n : ℝ) - (8 * (L * Real.sqrt B) + 1) -
      8 * (a * Real.sqrt B + (60 * Real.log n + 1 / 4)))
    (hend : s + r < T) (hstart : (T : ℝ) - W ≤ s)
    (hbacklog : L ≤ lowerOccupationCountRate ((1 : ℝ) / 2) * (r : ℝ)) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {sample | feedbackGraphEnergyLinearConstant amplitude Kpre Kright L a W * n <
        sample.graphComparisonEnergy
          (sample.stoppedContinuationFeedbackGraph hlam0.le (by linarith) eta B T)} ≤
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2StoppedBadEvent hlam0.le (by linarith) eta amplitude globalQ endpointQ B T R) +
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample | ¬rightBoundaryMomentGood lam ((B : ℝ) + T) B L
          (sample.revealedSnapshotAtElapsed hlam0.le (by linarith) B 0 T)} +
      4 * Real.exp (-(B : ℝ) / 8) + 16 / (n : ℝ) ^ 3 +
      2 * Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (r : ℝ)) +
      feedbackPreRightEnergyLinearConstant lam amplitude / Kpre +
      3 * (4 + (17 * L) ^ 2) / Kright + (4 + (17 * L) ^ 2) / a ^ 2 := by
  have hlamHalf : lam < 1 / 2 := hlam.trans (by norm_num)
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let G : Set (FiniteSample n) := {sample | rightBoundaryMomentGood lam ((B : ℝ) + T) B L
    (sample.revealedSnapshotAtElapsed hlam0.le hlamHalf B 0 T)}
  let H : ℝ := (n : ℝ) - (8 * (L * Real.sqrt B) + 1)
  let A2 := feedbackA2StoppedBadEvent (n := n) hlam0.le hlamHalf eta amplitude globalQ endpointQ B T R
  let leftBad : Set (FiniteSample n) := {sample | leftRateExitTime n B sample ≠ (B : WithTop ℝ≥0)}
  let gridBad : Set (FiniteSample n) := G ∩ {sample | ¬rightBoundaryIntervalGridGood n lam
    ((B : ℝ) + T) (1 / 8) (60 * Real.log n) (fun _ ↦ H)
    (sample.revealedSnapshotAtElapsed hlam0.le hlamHalf B 0 T) sample}
  let bulkBad := bulkBackwardWindowBadEvent (n := n) hlam0.le hlamHalf eta B T s r
  let preBad : Set (FiniteSample n) := {sample | Kpre * n ≤
    feedbackPreRightEnergy hlam0.le hlamHalf eta B T sample}
  let rightBad : Set (FiniteSample n) := G ∩ {sample | Kright * (B : ℝ) ^ 2 ≤
    rightBoundaryFrozenEnergy lam ((B : ℝ) + T) ((n : ℝ) + 2 * B)
      (sample.revealedSnapshotAtElapsed hlam0.le hlamHalf B 0 T) sample}
  let currentBad : Set (FiniteSample n) := G ∩ {sample | a * Real.sqrt B ≤
    |rightBoundaryFrozenCurrent lam ((B : ℝ) + T) H
      (sample.revealedSnapshotAtElapsed hlam0.le hlamHalf B 0 T) sample|}
  let bad : Fin 9 → Set (FiniteSample n) :=
    ![A2, Gᶜ, (leftHeightGenericEvent n)ᶜ, leftBad, gridBad, bulkBad, preBad, rightBad, currentBad]
  have hn0 : 0 < n := by omega
  have hBpos : 0 < (B : ℝ) := lt_of_lt_of_le zero_lt_one hB1
  have hBn : (B : ℝ) ≤ (n : ℝ) / 2 := by linarith
  have herr0 : 0 ≤ 60 * Real.log (n : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  have hRH : (B : ℝ) + T ≤ H := by
    dsimp [H]
    have : 0 ≤ 8 * (a * Real.sqrt B + (60 * Real.log n + 1 / 4)) := by positivity
    linarith
  have hsubset : {sample | feedbackGraphEnergyLinearConstant amplitude Kpre Kright L a W * n <
      sample.graphComparisonEnergy (sample.stoppedContinuationFeedbackGraph hlam0.le hlamHalf eta B T)} ⊆
      ⋃ i, bad i := by
    intro sample henergy
    by_contra hout
    have hnot (i : Fin 9) : sample ∉ bad i := fun hi ↦ hout (mem_iUnion.mpr ⟨i, hi⟩)
    have hA2 : sample ∈ feedbackA2StoppedGoodEvent hlam0.le hlamHalf eta amplitude globalQ endpointQ B T R := hnot 0
    have hmoment : sample ∈ G := by
      have hh := hnot 1
      change ¬ sample ∉ G at hh
      exact not_not.mp hh
    have hgeneric : sample ∈ leftHeightGenericEvent n := by
      have hg := hnot 2
      change sample ∉ (leftHeightGenericEvent n)ᶜ at hg
      exact not_not.mp hg
    have hA1 : sample ∈ feedbackA1GoodEvent n lam B 0 := by
      by_contra hbad
      exact hA2 (Or.inr (Or.inr (Or.inl hbad)))
    have hNoTie := feedbackA1GoodEvent.noFeedbackTies hA1
    have hstop := feedbackA2StoppedGoodEvent.safeFeedbackA1StopTime_eq_horizon sample
      hlam0 hlam hn hBpos (by linarith : (B : ℝ) ≤ n) heta0 hboundary.le
      hsqrt hlinear hthreshold hA2
    have hleft : leftRateExitTime n B sample = (B : WithTop ℝ≥0) := by
      have hh := hnot 3
      change ¬leftRateExitTime n B sample ≠ (B : WithTop ℝ≥0) at hh
      exact not_not.mp hh
    have hgrid : rightBoundaryIntervalGridGood n lam ((B : ℝ) + T) (1 / 8)
        (60 * Real.log n) (fun _ ↦ H)
        (sample.revealedSnapshotAtElapsed hlam0.le hlamHalf B 0 T) sample := by
      by_contra hh
      exact hnot 4 ⟨hmoment, hh⟩
    have hbulk : sample ∉ bulkBad := hnot 5
    have hpre : feedbackPreRightEnergy hlam0.le hlamHalf eta B T sample ≤ Kpre * n := by
      have hh := hnot 6
      change ¬ Kpre * n ≤ feedbackPreRightEnergy hlam0.le hlamHalf eta B T sample at hh
      exact (lt_of_not_ge hh).le
    have hright : rightBoundaryFrozenEnergy lam ((B : ℝ) + T) ((n : ℝ) + 2 * B)
        (sample.revealedSnapshotAtElapsed hlam0.le hlamHalf B 0 T) sample ≤ Kright * (B : ℝ) ^ 2 := by
      apply le_of_lt
      apply lt_of_not_ge
      intro hh
      exact hnot 7 ⟨hmoment, hh⟩
    have hcurrent : |rightBoundaryFrozenCurrent lam ((B : ℝ) + T) H
        (sample.revealedSnapshotAtElapsed hlam0.le hlamHalf B 0 T) sample| ≤ a * Real.sqrt B := by
      apply le_of_lt
      apply lt_of_not_ge
      intro hh
      exact hnot 8 ⟨hmoment, hh⟩
    have hle := sample.stoppedGraphComparisonEnergy_le_linear_of_actual_events
      hlam0.le hlamHalf hn0 eta B T s r hB hB1 hL ha.le hW herr0 herr hNoTie hgeneric hleft hstop
      hgeometry hend hstart hbacklog hbulk hmoment hgrid hcurrent hpre hright
    exact (not_lt_of_ge hle) henergy
  have hG : MeasurableSet[usualRevealedFiltration (n := n) hlam0.le hlamHalf B 0 T] G :=
    measurableSet_actual_rightBoundaryMomentGood hlam0.le hlamHalf B 0 T B L
  have hgeneric : μ.real (leftHeightGenericEvent n)ᶜ = 0 := by
    simp only [Measure.real, μ, measure_leftHeightGenericEvent_compl_eq_zero, ENNReal.toReal_zero]
  have hleft := measureReal_leftRateExitTime_ne_boundary_le hn0 (by exact_mod_cast hBpos) hBquarter
  have hgrid : μ.real gridBad ≤ 16 / (n : ℝ) ^ 3 := by
    simpa only [μ, gridBad, G, H, mul_assoc] using
      measureReal_actual_intervalGridFailure_on_moment_le (by omega : 1 < n) hlam0.le hlamHalf
        B 0 T hT hboundary hBpos hBn hL
  have hbulk := measureReal_bulkBackwardWindowBadEvent_le hlam0 hlam hn0 hBpos heta0 hetaSmall T s r hr
  have hpre := measureReal_feedbackPreRightEnergy_tail_le hlam0 hlam hn0 hamp hB hBquarter
    heta0 hetaSmall T (by linarith : (T : ℝ) ≤ n) hKpre
  have hright : μ.real rightBad ≤ 3 * (4 + (17 * L) ^ 2) / Kright := by
    have hh := measureReal_actual_frozenEnergy_tail_inter_le hn0 hlam0.le hlamHalf B 0 T hT
      hboundary hB1 hBn hL (by linarith : (B : ℝ) + T ≤ (n : ℝ) + 2 * B)
      (by linarith : (n : ℝ) + 2 * B - ((B : ℝ) + T) ≤ 3 * B)
      (mul_pos hKright (sq_pos_of_pos hBpos)) G hG (fun _ h ↦ h)
    calc
      μ.real rightBad ≤ 3 * (4 + (17 * L) ^ 2) * (B : ℝ) ^ 2 / (Kright * (B : ℝ) ^ 2) := hh
      _ = _ := by field_simp
  have hcurrent : μ.real currentBad ≤ (4 + (17 * L) ^ 2) / a ^ 2 := by
    have hh := measureReal_actual_frozenCurrent_tail_inter_le hn0 hlam0.le hlamHalf B 0 T hT
      hboundary hB1 hBn hL hRH (mul_pos ha (Real.sqrt_pos.mpr hBpos)) G hG (fun _ h ↦ h)
    calc
      μ.real currentBad ≤ (4 + (17 * L) ^ 2) * (B : ℝ) / (a * Real.sqrt B) ^ 2 := hh
      _ = _ := by
        have hroot : Real.sqrt (B : ℝ) ^ 2 = (B : ℝ) := Real.sq_sqrt B.2
        simp only [mul_pow]
        field_simp
        nlinarith only [hroot]
  let bound : Fin 9 → ℝ := ![μ.real A2, μ.real Gᶜ, 0,
    4 * Real.exp (-(B : ℝ) / 8), 16 / (n : ℝ) ^ 3,
    2 * Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (r : ℝ)),
    feedbackPreRightEnergyLinearConstant lam amplitude / Kpre,
    3 * (4 + (17 * L) ^ 2) / Kright, (4 + (17 * L) ^ 2) / a ^ 2]
  have hpoint : ∀ i, μ.real (bad i) ≤ bound i := by
    intro i
    fin_cases i
    · exact le_rfl
    · exact le_rfl
    · exact hgeneric.le
    · exact hleft
    · exact hgrid
    · exact hbulk
    · exact hpre
    · exact hright
    · exact hcurrent
  have hsum := (measureReal_mono (μ := μ) hsubset).trans
    ((measureReal_iUnion_fintype_le (μ := μ) bad).trans (Finset.sum_le_sum (fun i _ ↦ hpoint i)))
  have hboundSum : (∑ i, bound i) = μ.real A2 + μ.real Gᶜ +
      4 * Real.exp (-(B : ℝ) / 8) + 16 / (n : ℝ) ^ 3 +
      2 * Real.exp (-lowerOccupationDecayRate ((1 : ℝ) / 2) * (r : ℝ)) +
      feedbackPreRightEnergyLinearConstant lam amplitude / Kpre +
      3 * (4 + (17 * L) ^ 2) / Kright + (4 + (17 * L) ^ 2) / a ^ 2 := by
    simp only [bound, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      add_zero]
    ring
  rw [hboundSum] at hsum
  exact hsum

end OTSelector.FiniteSample
