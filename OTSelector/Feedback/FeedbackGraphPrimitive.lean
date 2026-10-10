import OTSelector.Feedback.StoppedContinuationGraph
import OTSelector.Limit.FeedbackInvariant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The actual finite feedback graph is the primitive of its current

At every nonnegative elapsed time, the selected post-jump state gives the right derivative of
the original recursive curve.  The right-derivative version of the fundamental theorem of
calculus therefore identifies graph increments, including intervals containing event times.
The stopped-graph result uses the actual event that the stop reaches the deterministic horizon.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal Topology

namespace OTSelector

/-- The finite and infinite feedback conventions use exactly the same sign. -/
private theorem feedbackSlope_intCast_primitive (lam : ℝ) (k : ℤ) :
    feedbackSlope lam (k : ℝ) = lam * Limit.currentSign k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => simp [feedbackSlope, Limit.currentSign]
    | succ n =>
      have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      simp [feedbackSlope, Limit.currentSign, Nat.cast_add, Nat.cast_one, hp]
  | negSucc n =>
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [feedbackSlope, Limit.currentSign, Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    rw [ite_eq_right (by linarith), ite_eq_left (by linarith)]
    ring

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-- The actual post-jump current is measurable as a function of elapsed time. -/
theorem measurable_safeCurrentAt_time
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) :
    Measurable (fun t : ℝ≥0 ↦ safeCurrentAt hlam0 hlamHalf x0 p0 t sample) := by
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · simp only [safeCurrentAt, hgood, ↓reduceIte]
    have hset : Measurable (sample.elapsedIndexSet hlam0 hlamHalf x0 p0) := by
      apply measurable_finset_of_mem
      intro m
      simp only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact measurableSet_le measurable_const measurable_id
    have hindex : Measurable (sample.elapsedIndex hlam0 hlamHalf x0 p0) :=
      (measurable_of_countable (maxFinsetIndex (⟨0, by omega⟩ : Fin (2 * n + 1)))).comp hset
    exact (measurable_of_countable (fun m : Fin (2 * n + 1) ↦
      (sample.feedbackState lam x0 p0 m.val).current)).comp hindex
  · simpa only [safeCurrentAt, hgood, ↓reduceIte] using
      (measurable_const : Measurable (fun _ : ℝ≥0 ↦ (0 : ℤ)))

/-- The feedback velocity is integrable on every finite real interval. -/
theorem intervalIntegrable_safeFeedbackVelocity
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 a b : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦
      lam * Limit.currentSign (safeCurrentAt hlam0 hlamHalf x0 p0 u.toNNReal sample))
      volume a b := by
  have hm : Measurable (fun u : ℝ ↦
      lam * Limit.currentSign (safeCurrentAt hlam0 hlamHalf x0 p0 u.toNNReal sample)) :=
    measurable_const.mul ((measurable_of_countable Limit.currentSign).comp
      ((sample.measurable_safeCurrentAt_time hlam0 hlamHalf x0 p0).comp
        measurable_real_toNNReal))
  let : IsFiniteMeasure (volume.restrict (uIoc a b)) := ⟨by simp [Real.volume_uIoc]⟩
  rw [intervalIntegrable_iff]
  apply Integrable.of_bound hm.aestronglyMeasurable lam
  exact ae_of_all _ fun u ↦ by
    rw [Real.norm_eq_abs, ← feedbackSlope_intCast_primitive]
    exact abs_feedbackSlope_le hlam0

/-- The original graph has the actual post-jump feedback velocity as its right derivative.
This holds at event times as well as between events. -/
theorem hasDerivWithinAt_feedbackCurve_elapsed_right
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivWithinAt (fun v ↦ sample.feedbackCurve lam x0 p0 (x0 + v))
      (lam * Limit.currentSign (safeCurrentAt hlam0 hlamHalf x0 p0 u.toNNReal sample))
      (Ioi u) u := by
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 u.toNNReal
  have hmem := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 u.toNNReal
  have hleftNN : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 I.val ≤ u.toNNReal := by
    simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  have hleft : sample.feedbackKnot lam x0 p0 I.val ≤ x0 + u := by
    have h := NNReal.coe_le_coe.mpr hleftNN
    simpa only [coe_elapsedFeedbackKnot, Real.coe_toNNReal _ hu, sub_le_iff_le_add,
      add_comm] using h
  rw [← feedbackSlope_intCast_primitive]
  simp only [safeCurrentAt, hNoTie, ↓reduceIte]
  change HasDerivWithinAt (fun v ↦ sample.feedbackCurve lam x0 p0 (x0 + v))
    ((sample.feedbackState lam x0 p0 I.val).slope lam) (Ioi u) u
  by_cases hm : I.val < 2 * n
  · have hright : x0 + u < sample.feedbackKnot lam x0 p0 (I.val + 1) := by
      simpa only [Real.coe_toNNReal _ hu] using
        sample.elapsedIndex_next_knot_gt_of_val_lt hlam0 hlamHalf x0 p0 u.toNNReal hm
    let f : ℝ → ℝ := fun v ↦ segmentCurve (sample.feedbackKnot lam x0 p0 I.val)
      (sample.feedbackKnotValue lam x0 p0 I.val)
      ((sample.feedbackState lam x0 p0 I.val).slope lam) (x0 + v)
    have hd : HasDerivAt f ((sample.feedbackState lam x0 p0 I.val).slope lam) u := by
      convert ((((hasDerivAt_id u).const_add x0).sub_const
          (sample.feedbackKnot lam x0 p0 I.val)).const_mul
          ((sample.feedbackState lam x0 p0 I.val).slope lam)).const_add
          (sample.feedbackKnotValue lam x0 p0 I.val) using 1
      · rfl
      · rfl
      · rfl
      · simp only [mul_one]
    apply hd.hasDerivWithinAt.congr_of_eventuallyEq
    · have hnear : ∀ᶠ v in 𝓝 u, x0 + v <
          sample.feedbackKnot lam x0 p0 (I.val + 1) :=
        (isOpen_lt (continuous_const.add continuous_id) continuous_const).mem_nhds
          (show sample.feedbackKnot lam x0 p0 (I.val + 1) > x0 + u from hright)
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with v hv hvu
      exact sample.feedbackCurve_eq_segment_on_closed_interval hlam0 hlamHalf x0 p0 hm
        (hleft.trans (add_le_add le_rfl (le_of_lt hvu))) hv.le
    · exact sample.feedbackCurve_eq_segment_on_closed_interval hlam0 hlamHalf x0 p0 hm
        hleft hright.le
  · have hI : I.val = 2 * n := by have := I.isLt; omega
    rw [hI, sample.feedbackState_terminal_slope]
    have hterminal : sample.feedbackKnot lam x0 p0 (2 * n) ≤ x0 + u := by
      simpa only [hI] using hleft
    apply (hasDerivWithinAt_const u (Ioi u)
      (sample.feedbackKnotValue lam x0 p0 (2 * n))).congr
    · intro v hv
      exact sample.feedbackCurve_eq_terminal_value_of_ge_terminal_knot hlam0 hlamHalf x0 p0
        (hterminal.trans (add_le_add le_rfl hv.le))
    · exact sample.feedbackCurve_eq_terminal_value_of_ge_terminal_knot hlam0 hlamHalf x0 p0
        hterminal

/-- Every increment of the original finite feedback graph is the integral of the actual
post-jump current's feedback velocity. -/
theorem feedbackCurve_sub_eq_integral_safeCurrentAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    sample.feedbackCurve lam x0 p0 (x0 + t) - sample.feedbackCurve lam x0 p0 (x0 + s) =
      ∫ u in s..t, lam * Limit.currentSign
        (safeCurrentAt hlam0 hlamHalf x0 p0 u.toNNReal sample) := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hst
  · exact ((sample.feedbackCurve_continuous hlam0 hlamHalf x0 p0).comp
      (continuous_const.add continuous_id)).continuousOn
  · intro u hu
    exact sample.hasDerivWithinAt_feedbackCurve_elapsed_right hlam0 hlamHalf x0 p0 hNoTie
      (hs.trans hu.1.le)
  · exact sample.intervalIntegrable_safeFeedbackVelocity hlam0 hlamHalf x0 p0 s t

/-- On the actual survival event, the stopped graph satisfies the feedback primitive identity
through the closed deterministic bulk horizon. -/
theorem stoppedContinuationFeedbackGraph_curve_sub_eq_integral_safeCurrentAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (eta B : ℝ) (T : ℝ≥0)
    (hstop : safeFeedbackA1StopTime hlam0 hlamHalf eta B B 0 T sample =
      (T : WithTop ℝ≥0)) (hNoTie : sample.NoFeedbackTies lam B 0)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve (B + t) -
        (sample.stoppedContinuationFeedbackGraph hlam0 hlamHalf eta B T).curve (B + s) =
      ∫ u in s..t, lam * Limit.currentSign
        (safeCurrentAt hlam0 hlamHalf B 0 u.toNNReal sample) := by
  rw [sample.stoppedContinuationFeedbackGraph_eq_horizon hlam0 hlamHalf eta B T hstop,
    sample.horizonFeedbackGraph_curve_eq_of_mem hlam0 hlamHalf B T
      (show B + t ∈ Icc B (B + (T : ℝ)) from
        ⟨le_add_of_nonneg_right (hs.trans hst), add_le_add le_rfl ht⟩),
    sample.horizonFeedbackGraph_curve_eq_of_mem hlam0 hlamHalf B T
      (show B + s ∈ Icc B (B + (T : ℝ)) from
        ⟨le_add_of_nonneg_right hs, add_le_add le_rfl (hst.trans ht)⟩)]
  exact sample.feedbackCurve_sub_eq_integral_safeCurrentAt hlam0 hlamHalf B 0 hNoTie hs hst

end FiniteSample
end OTSelector
