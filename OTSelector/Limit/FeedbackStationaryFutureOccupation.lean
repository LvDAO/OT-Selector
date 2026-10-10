import OTSelector.Limit.FeedbackOccupationBalance
import OTSelector.Limit.FeedbackMarkedRestart
import OTSelector.Limit.FeedbackStationaryFutureReadout

/-!
# The complete future under occupation of an actual return cell

The first-return gate is measurable in the finite jump history. Conditional on a visited
current, the whole restarted marked path has the actual trajectory law. Integrating within
each holding segment therefore identifies the complete residual future, including all later
return cells, rather than only the next waiting time.
-/

open MeasureTheory ProbabilityTheory Preorder Set Filter
open scoped ENNReal

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- Before the first return, the actual finite past selects the entire genuine restarted path
law, with no assumption about regeneration or future independence. -/
theorem lintegral_feedbackMarkedTrajectory_beforeReturn_restart {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (n : ℕ) (k : ℤ)
    {f : FeedbackCellPath → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ w, if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k
      then f (feedbackMarkedRestart n w) else 0
      ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      feedbackMarkedTrajectory lam hlam0 hlam 0
        {w | n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k} *
        ∫⁻ z, f z ∂feedbackMarkedTrajectory lam hlam0 hlam k := by
  let A : Set ((i : Finset.Iic n) → FeedbackMarkedStep) :=
    {x | feedbackBeforeReturnHistory n x ∧ (x ⟨n, by simp⟩).2.2 = k}
  have hA : MeasurableSet A := (measurableSet_feedbackBeforeReturnHistory n).inter
    (measurableSet_eq_fun ((measurable_pi_apply _).snd.snd) measurable_const)
  have hae : ∀ᵐ (w : FeedbackCellPath) ∂feedbackMarkedTrajectory lam hlam0 hlam 0,
      (frestrictLe n w ∈ A) ↔ n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k := by
    filter_upwards [feedbackMarkedFirstReturnIndex_pos hlam0 hlam] with w hw
    exact and_congr_left (fun _ ↦ feedbackBeforeReturnHistory_iff n hw)
  have hprod : Measurable (fun p : ((i : Finset.Iic n) → FeedbackMarkedStep) × FeedbackCellPath ↦
      if p.1 ∈ A then f p.2 else 0) :=
    (hf.comp measurable_snd).ite (hA.preimage measurable_fst) measurable_const
  calc
    _ = ∫⁻ w, if frestrictLe n w ∈ A then f (feedbackMarkedRestart n w) else 0
        ∂feedbackMarkedTrajectory lam hlam0 hlam 0 := by
      apply lintegral_congr_ae
      filter_upwards [hae] with w hw
      simp only [hw]
    _ = ∫⁻ p, if p.1 ∈ A then f p.2 else 0
        ∂(feedbackMarkedTrajectory lam hlam0 hlam 0).map
          (fun w ↦ (frestrictLe n w, feedbackMarkedRestart n w)) := by
      rw [lintegral_map hprod ((measurable_frestrictLe n).prodMk
        (measurable_feedbackMarkedRestart n))]
    _ = ∫⁻ x, ∫⁻ z, if x ∈ A then f z else 0
        ∂feedbackMarkedRestartKernel lam hlam0 hlam n x
        ∂(feedbackMarkedTrajectory lam hlam0 hlam 0).map (frestrictLe n) := by
      rw [feedbackMarkedTrajectory_history_restart, Measure.lintegral_compProd hprod]
    _ = ∫⁻ x, A.indicator (fun _ ↦ ∫⁻ z, f z
        ∂feedbackMarkedTrajectory lam hlam0 hlam k) x
        ∂(feedbackMarkedTrajectory lam hlam0 hlam 0).map (frestrictLe n) := by
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        simp only [hx, ↓reduceIte]
        change (∫⁻ z, f z ∂feedbackMarkedTrajectory lam hlam0 hlam
          (x ⟨n, by simp⟩).2.2) = _
        rw [hx.2]
      · simp only [hx, ↓reduceIte, lintegral_zero, Set.indicator_of_notMem hx]
    _ = _ := by
      rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ,
        Measure.map_apply (measurable_frestrictLe n) hA, mul_comm]
      congr 1
      apply measure_congr
      exact hae.mono fun w hw ↦ propext hw

private theorem measurable_feedbackFirstHoldingReward {f : FeedbackCellPath → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fun w : FeedbackCellPath ↦
      ∫⁻ a in Ico 0 (w 1).1, f (feedbackMarkedResidual w a)) := by
  have hS : MeasurableSet {p : FeedbackCellPath × ℝ | 0 ≤ p.2 ∧ p.2 < (p.1 1).1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop))
  have hm := ((hf.comp measurable_feedbackMarkedResidual).indicator hS).lintegral_prod_right'
    (ν := (volume : Measure ℝ))
  convert hm using 1
  funext w
  exact (lintegral_indicator measurableSet_Ico _).symm

/-- Occupation of a specified pre-return holding segment sees the entire actual trajectory
from its current, with the inverse-rate factor forced by the exponential holding law. -/
theorem lintegral_feedbackMarkedTrajectory_holding_future {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (n : ℕ) (k : ℤ)
    {f : FeedbackCellPath → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ w, if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k then
      ∫⁻ a in Ico 0 (w (n + 1)).1,
        f (feedbackMarkedResidual (feedbackMarkedRestart n w) a) else 0
      ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      feedbackMarkedTrajectory lam hlam0 hlam 0
        {w | n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k} *
        ((ENNReal.ofReal (totalJumpRate lam k))⁻¹ *
          ∫⁻ z, f z ∂feedbackMarkedTrajectory lam hlam0 hlam k) := by
  have h := lintegral_feedbackMarkedTrajectory_beforeReturn_restart hlam0 hlam n k
    (measurable_feedbackFirstHoldingReward hf)
  simp only [feedbackMarkedRestart_succ, Nat.add_zero] at h
  rw [lintegral_feedbackMarkedResidual _ hlam0 hlam k hf] at h
  exact h

/-- The literal return-cell roof, restricted to current `k`, carries the full future trajectory
law from `k`, with mass equal to the true occupation of that state. -/
theorem lintegral_feedbackCellFuture_state {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) {f : FeedbackCellPath → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength w),
      if feedbackCellCurrent w t = k then f (feedbackCellFuture w t) else 0
      ∂volume ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      (∫⁻ w, feedbackCellStateOccupation w k ∂feedbackMarkedTrajectory lam hlam0 hlam 0) *
        ∫⁻ z, f z ∂feedbackMarkedTrajectory lam hlam0 hlam k := by
  have hgate (n : ℕ) : MeasurableSet {w : FeedbackCellPath |
      n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k} := by measurability
  have hreward (n : ℕ) : Measurable (fun w : FeedbackCellPath ↦
      ∫⁻ a in Ico 0 (w (n + 1)).1,
        f (feedbackMarkedResidual (feedbackMarkedRestart n w) a)) := by
    have h := (measurable_feedbackFirstHoldingReward hf).comp (measurable_feedbackMarkedRestart n)
    simpa only [Function.comp_def, feedbackMarkedRestart_succ, Nat.add_zero] using h
  calc
    _ = ∫⁻ w, ∑' n : ℕ, if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k then
        ∫⁻ a in Ico 0 (w (n + 1)).1,
          f (feedbackMarkedResidual (feedbackMarkedRestart n w) a) else 0
          ∂feedbackMarkedTrajectory lam hlam0 hlam 0 := by
      apply lintegral_congr_ae
      filter_upwards [feedbackMarkedTrajectory_waits_positive hlam0 hlam 0,
        feedbackMarkedFirstReturnIndex_pos hlam0 hlam,
        feedbackMarkedTrajectory_initial hlam0 hlam 0] with w hw ht hz
      exact lintegral_feedbackCellFuture_eq_holding_sum w k hw ht
        (congrArg (fun z : FeedbackMarkedStep ↦ z.2.2) hz) hf
    _ = _ := by
      rw [lintegral_tsum (fun n ↦ ((hreward n).ite (hgate n) measurable_const).aemeasurable)]
      simp_rw [lintegral_feedbackMarkedTrajectory_holding_future hlam0 hlam _ k hf]
      rw [ENNReal.tsum_mul_right, ← lintegral_feedbackCellStateVisits,
        lintegral_feedbackCellStateOccupation_eq_visits hlam0 hlam k,
        ENNReal.ofReal_inv_of_pos (totalJumpRate_pos hlam0 hlam k), mul_assoc]

/-- Normalizing the actual return-cell roof identifies its complete future conditional on the
root current. The current weight is the proved explicit invariant mass. -/
theorem lintegral_feedbackCellFuture_state_normalized {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) {f : FeedbackCellPath → ℝ≥0∞} (hf : Measurable f) :
    (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ *
      (∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength w),
        if feedbackCellCurrent w t = k then f (feedbackCellFuture w t) else 0
        ∂volume ∂feedbackMarkedTrajectory lam hlam0 hlam 0) =
      ENNReal.ofReal (invariantMass lam k) *
        ∫⁻ z, f z ∂feedbackMarkedTrajectory lam hlam0 hlam k := by
  rw [lintegral_feedbackCellFuture_state hlam0 hlam k hf, ← mul_assoc,
    ← feedbackStationaryCurrentLaw_singleton_eq_occupation hlam0 hlam k,
    feedbackStationaryCurrentLaw_singleton hlam0 hlam k]

end OTSelector.Limit
