import OTSelector.Feedback.RankEnergyOccupation
import OTSelector.Feedback.FeedbackRightBoundaryMoment
import OTSelector.Feedback.FeedbackRightTailRelativeVC

/-!
# Physical graph occupation equals the actual frozen-current occupation

This identifies the current in the deterministic rank-energy bound with the current whose
conditional second moment is already proved under the finite-sample law.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector.FiniteSample
variable {n : ℕ} (sample : FiniteSample n)

private theorem cut_count_add_right_count (v : Fin n → ℝ) (x : ℝ) :
    ((Finset.univ.filter fun i ↦ v i ≤ x).card : ℝ) +
      (∑ i : Fin n, if x < v i then (1 : ℝ) else 0) = n := by
  rw [Finset.sum_boole]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i ↦ v i ≤ x)
  simp only [not_le, Finset.card_univ, Fintype.card_fin] at h
  exact_mod_cast h

/-- Complementary source and target counts express graph current using frozen physical
phases at every coordinate where the graph has the specified height. -/
theorem graphRankCurrent_eq_phase_remaining_difference {lam : ℝ}
    (graph : FeedbackGraph lam) (x q : ℝ) (hcurve : graph.curve x = q) :
    sample.graphRankCurrent graph x =
      (∑ j : Fin n, if x < sample.targetPhase j q then (1 : ℝ) else 0) -
        ∑ i : Fin n, if x < sample.sourcePhase i q then (1 : ℝ) else 0 := by
  have hs := cut_count_add_right_count (sample.sourceIntersection graph) x
  have ht := cut_count_add_right_count (sample.targetIntersection graph) x
  have hsource (i : Fin n) : x < sample.sourceIntersection graph i ↔
      x < sample.sourcePhase i q := by
    rw [← not_le, sample.sourceIntersection_le_iff, hcurve, not_le]
  have htarget (j : Fin n) : x < sample.targetIntersection graph j ↔
      x < sample.targetPhase j q := by
    rw [← not_le, sample.targetIntersection_le_iff, hcurve, not_le]
  simp_rw [hsource] at hs
  simp_rw [htarget] at ht
  unfold graphRankCurrent graphSourceCutCount graphTargetCutCount
  linarith

/-- On the actual no-tie boundary, the constant-tail graph current is exactly the frozen
snapshot current at every physical coordinate after the boundary. -/
theorem graphRankCurrent_eq_actualFrozenCurrent_of_constant_tail
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (graph : FeedbackGraph lam)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hconstant : ∀ x : ℝ, x0 + (T : ℝ) ≤ x → graph.curve x =
      actualRightTailFrozenHeight hlam0 hlamHalf x0 p0 T sample)
    (x : ℝ) (hx : x0 + (T : ℝ) ≤ x) :
    sample.graphRankCurrent graph x =
      rightBoundaryFrozenCurrent lam (x0 + (T : ℝ)) x
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample := by
  let t : ℝ≥0 := ⟨x - (x0 + (T : ℝ)), sub_nonneg.mpr hx⟩
  have hxt : x0 + (T : ℝ) + (t : ℝ) = x := by
    change x0 + (T : ℝ) + (x - (x0 + (T : ℝ))) = x
    ring
  have hs := rightTailFrozenSourceCount_actual_eq_rightSourceRemainingAt
    hlam0 hlamHalf x0 p0 T t sample hNoTie
  have ht := rightTailFrozenTargetCount_actual_eq_rightTargetRemainingAt
    hlam0 hlamHalf x0 p0 T t sample hNoTie
  rw [rightSourceRemainingAt_eq_strict_count, hxt] at hs
  rw [rightTargetRemainingAt_eq_strict_count, hxt] at ht
  rw [sample.graphRankCurrent_eq_phase_remaining_difference graph x _ (hconstant x hx)]
  exact congrArg₂ (fun u v : ℝ ↦ u - v) ht.symm hs.symm

/-- The actual stopped graph inherits the frozen continuation on bulk survival. -/
theorem stoppedGraph_curve_eq_actualFrozenHeight_of_survival
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) (x : ℝ) (hx : B + (T : ℝ) ≤ x) :
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve x =
      actualRightTailFrozenHeight hlam0 hlamHalf B 0 T sample := by
  rw [sample.stoppedContinuationFeedbackGraph_eq_horizon hlam0 hlamHalf eta B T hstop,
    sample.horizonFeedbackGraph_curve_eq_right hlam0 hlamHalf B T hx]
  unfold actualRightTailFrozenHeight
  rw [rightBoundaryFrozenHeight_revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T sample hNoTie]
  exact (safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
    hlam0 hlamHalf B 0 T sample hNoTie).symm

/-- The deterministic right-energy integral is exactly the random variable appearing in the
proved conditional frozen-current moment bound. -/
theorem stoppedGraph_rightOccupation_eq_actualFrozenEnergy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) (H : ℝ) (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) :
    (∫ x in Icc (B + (T : ℝ)) H,
      sample.graphRankCurrent
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) x ^ 2) =
      rightBoundaryFrozenEnergy lam (B + (T : ℝ)) H
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T) sample := by
  rw [integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [sample.graphRankCurrent_eq_actualFrozenCurrent_of_constant_tail
    hlam0 hlamHalf B 0 T _ hNoTie
    (sample.stoppedGraph_curve_eq_actualFrozenHeight_of_survival
      hlam0 hlamHalf eta B T hNoTie hstop) x hx.1.le]

/-- Enlarging the physical interval lets the actual graph bound use the fixed endpoint in the
available conditional frozen-energy theorem. -/
theorem stoppedGraph_rightOccupation_le_actualFrozenEnergy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (eta B : ℝ) (T : ℝ≥0) {H X : ℝ} (hHX : H ≤ X)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) :
    (∫ x in Icc (B + (T : ℝ)) H,
      sample.graphRankCurrent
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T) x ^ 2) ≤
      rightBoundaryFrozenEnergy lam (B + (T : ℝ)) X
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf B 0 T) sample := by
  rw [← sample.stoppedGraph_rightOccupation_eq_actualFrozenEnergy
    hlam0 hlamHalf eta B T X hNoTie hstop]
  exact setIntegral_mono_set
    (sample.integrableOn_sq_graphRankCurrent _ _ _) (ae_of_all _ fun _ ↦ sq_nonneg _)
    (ae_of_all _ fun _ hx ↦ ⟨hx.1, hx.2.trans hHX⟩)

end OTSelector.FiniteSample
