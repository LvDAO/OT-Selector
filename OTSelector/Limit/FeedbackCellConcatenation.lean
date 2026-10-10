import OTSelector.Limit.FeedbackCellRoots
import OTSelector.Limit.FeedbackCellGeometry
import OTSelector.PointProcess.FiniteMatchingSceneMeasurable
import OTSelector.PointProcess.FeedbackEnvironment
import OTSelector.PointProcess.FeedbackCellConfiguration
import OTSelector.Probability.RenewalErgodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Actual concatenation of marked first-return cells

The finite current of a cell is read directly from its actual marked path and first-return index.
Arrival points include the terminal return jump, so that each cell owns its right endpoint.
The graph height is the integral of the feedback velocity of the concatenated current.
-/

open MeasureTheory Set Filter Function
open scoped BigOperators Interval ENNReal

set_option maxHeartbeats 600000

namespace OTSelector.Limit

/-- The post-arrival integer increment of an actual marked jump. -/
def feedbackCellJump (w : FeedbackCellPath) (i : ℕ) : ℤ :=
  (w (i + 1)).2.2 - (w i).2.2

theorem measurable_feedbackCellJump (i : ℕ) : Measurable (fun w ↦ feedbackCellJump w i) := by
  unfold feedbackCellJump
  fun_prop

/-- The right-continuous current inside a first-return cell, read from its finitely many jumps.
For zero-start returning paths it is zero before the first jump and after the terminal jump. -/
noncomputable def feedbackCellCurrent (w : FeedbackCellPath) (u : ℝ) : ℤ :=
  ∑ i ∈ Finset.range (feedbackMarkedFirstReturnIndex w),
    if feedbackCellClock w (i + 1) ≤ u then feedbackCellJump w i else 0

private theorem measurable_feedbackCellCurrent_partial :
    Measurable (fun p : (FeedbackCellPath × ℝ) × ℕ ↦
      ∑ i ∈ Finset.range p.2,
        if feedbackCellClock p.1.1 (i + 1) ≤ p.1.2 then feedbackCellJump p.1.1 i else 0) := by
  apply measurable_from_prod_countable_left
  intro n
  dsimp only
  apply Finset.measurable_sum
  intro i hi
  exact ((measurable_feedbackCellJump i).comp measurable_fst).ite
    (measurableSet_le ((measurable_feedbackCellClock (i + 1)).comp measurable_fst)
      measurable_snd) measurable_const

theorem measurable_feedbackCellCurrent :
    Measurable (fun p : FeedbackCellPath × ℝ ↦ feedbackCellCurrent p.1 p.2) := by
  unfold feedbackCellCurrent
  exact measurable_feedbackCellCurrent_partial.comp
    (f := fun p : FeedbackCellPath × ℝ ↦ (p, feedbackMarkedFirstReturnIndex p.1))
    (measurable_id.prodMk (measurable_feedbackMarkedFirstReturnIndex.comp measurable_fst))

/-- Summing all actual current increments recovers the current difference at the cell endpoints. -/
theorem feedbackCellJump_sum (w : FeedbackCellPath) (n : ℕ) :
    (∑ i ∈ Finset.range n, feedbackCellJump w i) = (w n).2.2 - (w 0).2.2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, feedbackCellJump]; ring

/-- The cell current agrees with the actual discrete current between two consecutive clocks. -/
theorem feedbackCellCurrent_eq_of_clock_bounds (w : FeedbackCellPath) (n : ℕ) (u : ℝ)
    (hn : n ≤ feedbackMarkedFirstReturnIndex w) (hstart : (w 0).2.2 = 0)
    (hclock : StrictMono (feedbackCellClock w))
    (hlo : feedbackCellClock w n ≤ u)
    (hhi : u < feedbackCellClock w (n + 1)) :
    feedbackCellCurrent w u = (w n).2.2 := by
  have hsplit (i : ℕ) : feedbackCellClock w (i + 1) ≤ u ↔ i < n := by
    constructor
    · intro h
      by_contra hni
      have hh := hclock.monotone (Nat.add_le_add_right (Nat.le_of_not_gt hni) 1)
      linarith
    · intro h
      exact (hclock.monotone (Nat.succ_le_iff.mpr h)).trans hlo
  simp_rw [feedbackCellCurrent, hsplit]
  have hs : (∑ i ∈ Finset.range (feedbackMarkedFirstReturnIndex w),
      if i < n then feedbackCellJump w i else 0) = ∑ i ∈ Finset.range n, feedbackCellJump w i := by
    calc
      _ = ∑ i ∈ Finset.range n, if i < n then feedbackCellJump w i else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono hn)
        intro i hi hin
        simp only [Finset.mem_range] at hin
        simp only [hin, ↓reduceIte]
      _ = _ := Finset.sum_congr rfl fun i hi ↦ ite_eq_left (Finset.mem_range.mp hi)
  rw [hs, feedbackCellJump_sum, hstart, sub_zero]

/-- After the terminal clock every jump has occurred, giving the true terminal current. -/
theorem feedbackCellCurrent_eq_terminal (w : FeedbackCellPath) (u : ℝ)
    (hstart : (w 0).2.2 = 0) (hclock : Monotone (feedbackCellClock w))
    (hu : feedbackCellClock w (feedbackMarkedFirstReturnIndex w) ≤ u) :
    feedbackCellCurrent w u = (w (feedbackMarkedFirstReturnIndex w)).2.2 := by
  unfold feedbackCellCurrent
  have heq (i : ℕ) (hi : i ∈ Finset.range (feedbackMarkedFirstReturnIndex w)) :
      feedbackCellClock w (i + 1) ≤ u :=
    (hclock (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi))).trans hu
  rw [Finset.sum_congr rfl (fun i hi ↦ ite_eq_left (heq i hi)),
    feedbackCellJump_sum, hstart, sub_zero]

/-- The actual two-sided current, selecting the physical first-return cell containing the point. -/
noncomputable def feedbackConcatenatedCurrent (w : FeedbackCellSequence) (x : ℝ) : ℤ :=
  let j := feedbackCellIndex w x
  feedbackCellCurrent (w j) (x - feedbackCellRoot w j)

private theorem measurable_feedbackCellPath_eval :
    Measurable (fun p : FeedbackCellSequence × ℤ ↦ p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro j
  exact measurable_pi_apply j

private theorem measurable_feedbackCellRoot_joint :
    Measurable (fun p : FeedbackCellSequence × ℤ ↦ feedbackCellRoot p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro j
  exact measurable_feedbackCellRoot j

theorem measurable_feedbackConcatenatedCurrent :
    Measurable (fun p : FeedbackCellSequence × ℝ ↦ feedbackConcatenatedCurrent p.1 p.2) := by
  unfold feedbackConcatenatedCurrent
  exact measurable_feedbackCellCurrent.comp
    (f := fun p : FeedbackCellSequence × ℝ ↦
      (p.1 (feedbackCellIndex p.1 p.2), p.2 - feedbackCellRoot p.1 (feedbackCellIndex p.1 p.2)))
    ((measurable_feedbackCellPath_eval.comp
      (measurable_fst.prodMk measurable_feedbackCellIndex)).prodMk
    (measurable_snd.sub (measurable_feedbackCellRoot_joint.comp
      (f := fun p : FeedbackCellSequence × ℝ ↦ (p.1, feedbackCellIndex p.1 p.2))
      (measurable_fst.prodMk measurable_feedbackCellIndex))))

/-- Integer cell shifts correspond to the actual spatial movement between their roots. -/
theorem feedbackConcatenatedCurrent_shift {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (k : ℤ) (x : ℝ) :
    feedbackConcatenatedCurrent (IIDShift.shift k w) x =
      feedbackConcatenatedCurrent w (x + feedbackCellRoot w k) := by
  have hi := feedbackCellIndex_shift hw k (x + feedbackCellRoot w k)
  simp only [add_sub_cancel_right] at hi
  simp only [feedbackConcatenatedCurrent, hi, feedbackCellRoot_shift, IIDShift.shift,
    sub_add_cancel]
  congr 1
  ring

private theorem abs_currentSign_le_one (k : ℤ) : |currentSign k| ≤ 1 := by
  cases k with
  | ofNat n => cases n <;> norm_num [currentSign]
  | negSucc n => norm_num [currentSign]

/-- Feedback velocity of the actual concatenated current. -/
noncomputable def feedbackConcatenatedVelocity (lam : ℝ) (w : FeedbackCellSequence) (x : ℝ) : ℝ :=
  lam * currentSign (feedbackConcatenatedCurrent w x)

theorem measurable_feedbackConcatenatedVelocity (lam : ℝ) :
    Measurable (fun p : FeedbackCellSequence × ℝ ↦ feedbackConcatenatedVelocity lam p.1 p.2) :=
  measurable_const.mul ((measurable_of_countable currentSign).comp
    measurable_feedbackConcatenatedCurrent)

theorem norm_feedbackConcatenatedVelocity_le (lam : ℝ) (w : FeedbackCellSequence) (x : ℝ) :
    ‖feedbackConcatenatedVelocity lam w x‖ ≤ |lam| := by
  simpa only [feedbackConcatenatedVelocity, Real.norm_eq_abs, abs_mul, mul_one] using
    mul_le_mul_of_nonneg_left (abs_currentSign_le_one (feedbackConcatenatedCurrent w x))
      (abs_nonneg lam)

private theorem intervalIntegrable_feedbackConcatenatedVelocity (lam : ℝ)
    (w : FeedbackCellSequence) (a b : ℝ) :
    IntervalIntegrable (feedbackConcatenatedVelocity lam w) volume a b := by
  rw [intervalIntegrable_iff]
  let : IsFiniteMeasure (volume.restrict (Ι a b)) := ⟨by simp [Real.volume_uIoc]⟩
  apply Integrable.of_bound
    ((measurable_feedbackConcatenatedVelocity lam).comp measurable_prodMk_left).aestronglyMeasurable
    |lam|
  exact ae_of_all _ (norm_feedbackConcatenatedVelocity_le lam w)

/-- The graph is the actual integral of the feedback velocity and is normalized at the origin. -/
noncomputable def feedbackConcatenatedHeight (lam : ℝ) (w : FeedbackCellSequence) (x : ℝ) : ℝ :=
  ∫ t in 0..x, feedbackConcatenatedVelocity lam w t

/-- The concatenated graph retains the deterministic slope bound across every cell boundary. -/
theorem lipschitzWith_feedbackConcatenatedHeight (lam : ℝ) (w : FeedbackCellSequence) :
    LipschitzWith (Real.toNNReal |lam|) (feedbackConcatenatedHeight lam w) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hi := intervalIntegrable_feedbackConcatenatedVelocity lam w
  have heq : feedbackConcatenatedHeight lam w x - feedbackConcatenatedHeight lam w y =
      ∫ t in y..x, feedbackConcatenatedVelocity lam w t :=
    intervalIntegral.integral_interval_sub_left (hi 0 x) (hi 0 y)
  rw [Real.dist_eq, heq, Real.coe_toNNReal _ (abs_nonneg lam), Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ ↦ norm_feedbackConcatenatedVelocity_le lam w t)

theorem measurable_feedbackConcatenatedHeight (lam x : ℝ) :
    Measurable (fun w ↦ feedbackConcatenatedHeight lam w x) := by
  exact (((measurable_feedbackConcatenatedVelocity lam).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc 0 x))).sub
    ((measurable_feedbackConcatenatedVelocity lam).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc x 0)))).measurable

/-- The continuous normalized graph-height carrier of the actual concatenated cells. -/
noncomputable def feedbackConcatenatedGraphHeight (lam : ℝ) (w : FeedbackCellSequence) :
    PointProcess.GraphHeight where
  toContinuousMap := ⟨feedbackConcatenatedHeight lam w,
    (lipschitzWith_feedbackConcatenatedHeight lam w).continuous⟩
  map_zero' := by simp [feedbackConcatenatedHeight]

theorem measurable_feedbackConcatenatedGraphHeight (lam : ℝ) :
    Measurable (feedbackConcatenatedGraphHeight lam) :=
  PointProcess.GraphHeight.measurable_of_eval (measurable_feedbackConcatenatedHeight lam)

/-- Concatenating after an integer cell shift exactly reroots the actual feedback graph. -/
theorem feedbackConcatenatedGraphHeight_shift (lam : ℝ) {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (k : ℤ) :
    feedbackConcatenatedGraphHeight lam (IIDShift.shift k w) =
      (feedbackConcatenatedGraphHeight lam w).reroot (feedbackCellRoot w k) := by
  ext x
  change (∫ t in 0..x, feedbackConcatenatedVelocity lam (IIDShift.shift k w) t) =
    feedbackConcatenatedHeight lam w (x + feedbackCellRoot w k) -
      feedbackConcatenatedHeight lam w (feedbackCellRoot w k)
  have heq : feedbackConcatenatedVelocity lam (IIDShift.shift k w) =
      fun t ↦ feedbackConcatenatedVelocity lam w (t + feedbackCellRoot w k) := by
    funext t
    simp only [feedbackConcatenatedVelocity, feedbackConcatenatedCurrent_shift hw]
  rw [heq, intervalIntegral.integral_comp_add_right, zero_add]
  exact (intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_feedbackConcatenatedVelocity lam w 0 (x + feedbackCellRoot w k))
    (intervalIntegrable_feedbackConcatenatedVelocity lam w 0 (feedbackCellRoot w k))).symm

/-- Strictly positive actual holding times leave current zero at the beginning of the cell. -/
theorem feedbackCellCurrent_zero (w : FeedbackCellPath)
    (hw : ∀ i, 0 < (w (i + 1)).1) : feedbackCellCurrent w 0 = 0 := by
  unfold feedbackCellCurrent
  apply Finset.sum_eq_zero
  intro i hi
  have ht : 0 < feedbackCellClock w (i + 1) := by
    simpa only [feedbackCellClock_zero] using
      feedbackCellClock_strictMono w hw (Nat.zero_lt_succ i)
  exact ite_eq_right (not_le_of_gt ht)

/-- The current at the distinguished return root is really zero. -/
theorem feedbackConcatenatedCurrent_zero {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (hw0 : ∀ i, 0 < (w 0 (i + 1)).1) :
    feedbackConcatenatedCurrent w 0 = 0 := by
  have hi : feedbackCellIndex w 0 = 0 := by
    apply (feedbackCellIndex_eq_iff hw 0 0).mpr
    constructor
    · simp only [feedbackCellRoot_zero, le_refl]
    · rw [feedbackCellRoot_add_one, feedbackCellRoot_zero, zero_add]
      exact hw.1 0
  simp only [feedbackConcatenatedCurrent, hi, feedbackCellRoot_zero, sub_zero,
    feedbackCellCurrent_zero _ hw0]

/-- The actual normalized feedback path at a return root, which has current zero. -/
noncomputable def feedbackConcatenatedPath (lam : ℝ) (w : FeedbackCellSequence) :
    PointProcess.FeedbackPath := ⟨feedbackConcatenatedGraphHeight lam w, 0⟩

theorem measurable_feedbackConcatenatedPath (lam : ℝ) :
    Measurable (feedbackConcatenatedPath lam) := by
  have hemb : MeasurableEmbedding PointProcess.FeedbackPath.coordinates :=
    PointProcess.FeedbackPath.isEmbedding_coordinates.continuous.measurable.measurableEmbedding
      PointProcess.FeedbackPath.equivCoordinates.injective
  apply hemb.measurable_comp_iff.mp
  exact (measurable_feedbackConcatenatedGraphHeight lam).prodMk measurable_const

/-- The root-current field equals the actual concatenated current on genuine cell paths. -/
theorem feedbackConcatenatedPath_rootCurrent (lam : ℝ) {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (hw0 : ∀ i, 0 < (w 0 (i + 1)).1) :
    (feedbackConcatenatedPath lam w).rootCurrent = feedbackConcatenatedCurrent w 0 :=
  (feedbackConcatenatedCurrent_zero hw hw0).symm

/-- The actual two-sided marked environment consists of the two event configurations and
of the integral graph of their feedback current, rooted at a return with current zero. -/
noncomputable def feedbackConcatenatedEnvironment (lam : ℝ) (w : FeedbackCellSequence) :
    PointProcess.FeedbackEnvironment :=
  ⟨PointProcess.feedbackConcatenatedSource w, PointProcess.feedbackConcatenatedTarget w,
    feedbackConcatenatedPath lam w⟩

theorem measurable_feedbackConcatenatedEnvironment (lam : ℝ) :
    Measurable (feedbackConcatenatedEnvironment lam) :=
  PointProcess.FeedbackEnvironment.measurable_mk
    PointProcess.measurable_feedbackConcatenatedSource
    PointProcess.measurable_feedbackConcatenatedTarget
    (measurable_feedbackConcatenatedGraphHeight lam) measurable_const

/-- The genuine iid cell law obeys one-cell covariance, including the integer root current.
The zero current update is proved by counting the actual balanced return-cell events. -/
theorem feedbackConcatenatedEnvironment_onecell {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam,
      feedbackConcatenatedEnvironment lam (IIDShift.shift 1 w) =
        feedbackCellLength (w 0) +ᵥ feedbackConcatenatedEnvironment lam w := by
  filter_upwards [feedbackCellBase_roots_good hlam0 hlam,
    PointProcess.feedbackCellBase_orientedCount_onecell_zero hlam0 hlam] with w hw hc
  have hr : feedbackCellRoot w 1 = feedbackCellLength (w 0) := by
    simpa only [feedbackCellRoot_zero, zero_add] using feedbackCellRoot_add_one w 0
  apply PointProcess.FeedbackEnvironment.ext
  · change PointProcess.feedbackConcatenatedSource (IIDShift.shift 1 w) =
      PointProcess.LocalConfiguration.reroot (feedbackCellLength (w 0))
        (PointProcess.feedbackConcatenatedSource w)
    simpa only [hr] using PointProcess.feedbackConcatenatedSource_shift w 1
  · change PointProcess.feedbackConcatenatedTarget (IIDShift.shift 1 w) =
      PointProcess.LocalConfiguration.reroot (feedbackCellLength (w 0))
        (PointProcess.feedbackConcatenatedTarget w)
    simpa only [hr] using PointProcess.feedbackConcatenatedTarget_shift w 1
  · apply PointProcess.FeedbackPath.ext
    · change feedbackConcatenatedGraphHeight lam (IIDShift.shift 1 w) =
        (feedbackConcatenatedGraphHeight lam w).reroot (feedbackCellLength (w 0))
      simpa only [hr] using feedbackConcatenatedGraphHeight_shift lam hw 1
    · change (0 : ℤ) = 0 +
        (PointProcess.LocalConfiguration.orientedCount
          (PointProcess.feedbackConcatenatedSource w) 0 (feedbackCellLength (w 0)) -
        PointProcess.LocalConfiguration.orientedCount
          (PointProcess.feedbackConcatenatedTarget w) 0 (feedbackCellLength (w 0)))
      simp only [hc, add_zero]

/-- The explicit spatial occupation law of the actual iid marked return cells. Its roof is the
physical first-return clock, and its observable is the actual two-color feedback environment. -/
noncomputable def feedbackStationaryEnvironmentLaw (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) : Measure PointProcess.FeedbackEnvironment :=
  renewalStationaryLaw (feedbackCellBase lam hlam0 hlam)
    (fun w ↦ feedbackCellLength (w 0)) (fun p ↦ p.1 +ᵥ p.2)
    (feedbackConcatenatedEnvironment lam)

instance feedbackStationaryEnvironmentLaw_isProbability {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    IsProbabilityMeasure (feedbackStationaryEnvironmentLaw lam hlam0 hlam) :=
  isProbabilityMeasure_renewalStationaryLaw (feedbackCellBase lam hlam0 hlam)
    (measurable_feedbackCellLength.comp (measurable_pi_apply 0))
    (integrable_feedbackCellBase_length hlam0 hlam 0)
    ((feedbackCellBase_lengths_positive hlam0 hlam).mono fun _ hw ↦ hw 0)
    PointProcess.FeedbackEnvironment.measurable_uncurry_reroot
    (measurable_feedbackConcatenatedEnvironment lam)

/-- Every real rerooting preserves the actual normalized occupation law. -/
theorem measurePreserving_feedbackStationaryEnvironmentLaw {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (t : ℝ) :
    MeasurePreserving (fun e : PointProcess.FeedbackEnvironment ↦ t +ᵥ e)
      (feedbackStationaryEnvironmentLaw lam hlam0 hlam)
      (feedbackStationaryEnvironmentLaw lam hlam0 hlam) :=
  measurePreserving_renewalStationaryLaw (feedbackCellBase lam hlam0 hlam)
    (measurable_feedbackCellLength.comp (measurable_pi_apply 0))
    (integrable_feedbackCellBase_length hlam0 hlam 0)
    ((feedbackCellBase_lengths_positive hlam0 hlam).mono fun _ hw ↦ hw 0)
    (IIDShift.measurePreserving_shift (feedbackMarkedTrajectory lam hlam0 hlam 0) 1)
    PointProcess.FeedbackEnvironment.measurable_uncurry_reroot
    (measurable_feedbackConcatenatedEnvironment lam)
    (fun a b e ↦ (add_vadd a b e).symm)
    (feedbackConcatenatedEnvironment_onecell hlam0 hlam) t

/-- The whole real translation action is ergodic under this actual feedback environment law. -/
theorem ergodicVAdd_feedbackStationaryEnvironmentLaw {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ErgodicVAdd ℝ PointProcess.FeedbackEnvironment
      (feedbackStationaryEnvironmentLaw lam hlam0 hlam) :=
  ergodicVAdd_renewalStationaryLaw (feedbackCellBase lam hlam0 hlam)
    (measurable_feedbackCellLength.comp (measurable_pi_apply 0))
    (integrable_feedbackCellBase_length hlam0 hlam 0)
    ((feedbackCellBase_lengths_positive hlam0 hlam).mono fun _ hw ↦ hw 0)
    (IIDShift.ergodic_shift_one (feedbackMarkedTrajectory lam hlam0 hlam 0))
    PointProcess.FeedbackEnvironment.measurable_uncurry_reroot
    (measurable_feedbackConcatenatedEnvironment lam)
    (feedbackConcatenatedEnvironment_onecell hlam0 hlam)

/-- The actual occupation formula has the true mean first-return length as its denominator. -/
theorem integral_feedbackStationaryEnvironmentLaw {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {f : PointProcess.FeedbackEnvironment → ℝ}
    (hf : Measurable f) {C : ℝ} (hbound : ∀ e, ‖f e‖ ≤ C) :
    (∫ e, f e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam) =
      (feedbackCellMean lam hlam0 hlam)⁻¹ *
        ∫ w, (∫ u in 0..feedbackCellLength (w 0),
          f (u +ᵥ feedbackConcatenatedEnvironment lam w)) ∂feedbackCellBase lam hlam0 hlam := by
  have h := integral_renewalStationaryLaw (feedbackCellBase lam hlam0 hlam)
      (measurable_feedbackCellLength.comp (measurable_pi_apply 0))
      (integrable_feedbackCellBase_length hlam0 hlam 0)
      (ae_of_all _ fun w ↦ feedbackCellLength_nonneg (w 0))
      PointProcess.FeedbackEnvironment.measurable_uncurry_reroot
      (measurable_feedbackConcatenatedEnvironment lam) hf hbound
  simp only [Function.comp_def, integral_feedbackCellBase_length] at h
  exact h

end OTSelector.Limit
