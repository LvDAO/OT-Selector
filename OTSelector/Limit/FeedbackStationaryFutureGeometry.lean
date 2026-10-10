import OTSelector.Limit.FeedbackStationaryFutureRoof

/-!
# Actual environment current and physical clocks of the complete future

On the actual return roof, the rerooted environment current agrees with the current read from
the positively concatenated path. The complete future retains the original jump clocks shifted
by the observation time.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Limit

open PointProcess

/-- The first-return current is unchanged by concatenating later cells. -/
theorem feedbackConcatCellPaths_first_cell_current (ω : ℕ → FeedbackCellPath)
    (hτ : 0 < feedbackMarkedFirstReturnIndex (ω 0)) (hstart : (ω 0 0).2.2 = 0)
    (t : ℝ) : feedbackCellCurrent (feedbackConcatCellPaths ω) t =
      feedbackCellCurrent (ω 0) t := by
  have hcoord (n : ℕ) (hn : n ≤ feedbackMarkedFirstReturnIndex (ω 0)) :
      (feedbackConcatCellPaths ω n).2.2 = (ω 0 n).2.2 := by
    cases n with
    | zero => exact hstart.symm
    | succ n => rw [feedbackConcatCellPaths_first_cell_coordinate ω n (by omega)]
  unfold feedbackCellCurrent
  rw [feedbackConcatCellPaths_first_return ω hτ]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [feedbackConcatCellPaths_first_cell_clock ω (i + 1) (by omega)]
  unfold feedbackCellJump
  rw [hcoord (i + 1) (by omega), hcoord i (by omega)]

/-- At almost every actual stationary roof point, the observable environment root current is
exactly the current read at the same cut from the complete positive trajectory. -/
theorem feedbackReturnRoofLaw_rootCurrent_eq_concatPositive (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ p ∂feedbackReturnRoofLaw lam hlam0 hlam,
      (FeedbackEnvironment.reroot p.2 (feedbackConcatenatedEnvironment lam p.1)).path.rootCurrent =
        feedbackCellCurrent (feedbackConcatPositiveCellPaths p.1) p.2 := by
  unfold feedbackReturnRoofLaw
  apply Measure.ae_smul_measure
  have hroof : MeasurableSet {p : FeedbackCellSequence × ℝ |
      0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd
        (measurable_feedbackCellLength.comp ((measurable_pi_apply 0).comp measurable_fst)))
  have hbase := Measure.quasiMeasurePreserving_fst (μ := feedbackCellBase lam hlam0 hlam)
    (ν := (volume : Measure ℝ)) |>.ae (feedbackCellBase_identification_good hlam0 hlam)
  change ∀ᵐ p ∂((feedbackCellBase lam hlam0 hlam).prod volume).restrict
    {p : FeedbackCellSequence × ℝ | 0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)}, _
  filter_upwards [ae_restrict_of_ae hbase, ae_restrict_mem hroof] with p hp ht
  change FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam p.1).currentIncrement
    (feedbackConcatenatedEnvironment lam p.1).path p.2 = _
  rw [currentAt_feedbackConcatenatedEnvironment lam hp.1 hp.2.1 hp.2.2.2]
  have hi : feedbackCellIndex p.1 p.2 = 0 := by
    apply (feedbackCellIndex_eq_iff hp.1.1 p.2 0).mpr
    have hr : feedbackCellRoot p.1 1 = feedbackCellLength (p.1 0) := by
      simpa only [zero_add, feedbackCellRoot_zero] using feedbackCellRoot_add_one p.1 0
    simpa only [feedbackCellRoot_zero, zero_add, hr] using ht
  rw [feedbackConcatenatedCurrent, hi, feedbackCellRoot_zero, sub_zero]
  exact (feedbackConcatCellPaths_first_cell_current (fun j : ℕ ↦ p.1 (j : ℤ))
    (hp.1.2 0).2 (hp.2.2.1 0) p.2).symm

/-- The first remaining wait ends at the original next clock, shifted to the observation origin. -/
theorem feedbackCellFuture_one (w : FeedbackCellPath) (t : ℝ) :
    feedbackCellFuture w t 1 =
      (feedbackCellClock w (feedbackCellHoldingIndex w t + 1) - t,
        (w (feedbackCellHoldingIndex w t + 1)).2) := by
  simp only [feedbackCellFuture, feedbackMarkedResidual_one, feedbackMarkedRestart_succ,
    Nat.add_zero, feedbackCellClock_succ]
  congr 1
  ring

/-- Every jump after the first remaining jump retains its original marked step. -/
theorem feedbackCellFuture_add_two (w : FeedbackCellPath) (t : ℝ) (m : ℕ) :
    feedbackCellFuture w t (m + 2) = w (feedbackCellHoldingIndex w t + m + 2) := by
  simp [feedbackCellFuture, feedbackMarkedRestart, Nat.add_assoc]

/-- Every positive future jump clock is the corresponding original physical clock minus the
observation time. The algebraic identity requires no stochastic or regularity assumptions. -/
theorem feedbackCellFuture_clock (w : FeedbackCellPath) (t : ℝ) (m : ℕ) :
    feedbackCellClock (feedbackCellFuture w t) (m + 1) =
      feedbackCellClock w (feedbackCellHoldingIndex w t + m + 1) - t := by
  induction m with
  | zero => simp [feedbackCellClock_succ, feedbackCellFuture_one]
  | succ m ih =>
      rw [feedbackCellClock_succ, ih, feedbackCellFuture_add_two]
      rw [show feedbackCellHoldingIndex w t + (m + 1) + 1 =
        (feedbackCellHoldingIndex w t + m + 1) + 1 by omega,
        feedbackCellClock_succ w (feedbackCellHoldingIndex w t + m + 1)]
      simp only [Nat.add_assoc]
      ring

end OTSelector.Limit
