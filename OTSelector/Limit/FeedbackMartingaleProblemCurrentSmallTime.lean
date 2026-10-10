import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentUniqueness

/-!
# A quadratic bound on events after the first event

The original constant-mark martingales give the expected count at every bounded stopping
coordinate. Stopping at the first event therefore controls all additional events by a quadratic
function of the observation duration. This is the small-time error used in stationary generator
balance; it is proved for the actual environment counts.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit

open PointProcess CountingProcess

/-- The constant mark test recovers the actual birth or death rate. -/
theorem feedbackEnvironmentMarkRate_one {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (b : Bool) (k : ℤ) :
    feedbackEnvironmentMarkRate lam b (fun _ ↦ 1) k =
      if b then birthRate lam k else deathRate lam k := by
  cases b
  · change deathRate lam k * targetFeedbackMarkMean (lam * currentSign k) (fun _ ↦ 1) = _
    rw [← integral_targetMarkRateMeasure_eq_markMean hlam0 hlam]
    simp only [Bool.false_eq_true, ite_false, integral_const, smul_eq_mul, mul_one,
      Measure.real, targetMarkRateMeasure_univ hlam0 hlam,
      ENNReal.toReal_ofReal (deathRate_pos hlam0 hlam k).le]
  · change birthRate lam k * sourceFeedbackMarkMean (lam * currentSign k) (fun _ ↦ 1) = _
    rw [← integral_sourceMarkRateMeasure_eq_markMean hlam0 hlam]
    simp only [ite_true, integral_const, smul_eq_mul, mul_one, Measure.real,
      sourceMarkRateMeasure_univ hlam0 hlam,
      ENNReal.toReal_ofReal (birthRate_pos hlam0 hlam k).le]

/-- The actual integrated total event rate. -/
noncomputable def feedbackEnvironmentEventDrift (lam : ℝ) (e : FeedbackEnvironment) (t : ℝ) : ℝ :=
  ∫ s in 0..t, totalJumpRate lam (feedbackEnvironmentCurrent e s)

/-- The original two-color constant-mark compensators sum to total count minus total rate. -/
theorem feedbackEnvironment_compensator_sum_one {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (e : FeedbackEnvironment) (t : ℝ≥0) :
    feedbackEnvironmentMarkedCompensator lam true (fun _ ↦ 1) t e +
        feedbackEnvironmentMarkedCompensator lam false (fun _ ↦ 1) t e =
      (feedbackEnvironmentEventCount e t : ℝ) - feedbackEnvironmentEventDrift lam e t := by
  unfold feedbackEnvironmentMarkedCompensator feedbackEnvironmentEventCount
    feedbackEnvironmentEventDrift
  rw [LocalConfiguration.firstEventTestCount_one, LocalConfiguration.firstEventTestCount_one]
  have hs := intervalIntegrable_feedbackEnvironmentMarkRate lam true (fun _ ↦ 1) e 0 t
  have ht := intervalIntegrable_feedbackEnvironmentMarkRate lam false (fun _ ↦ 1) e 0 t
  rw [show (fun s ↦ totalJumpRate lam (feedbackEnvironmentCurrent e s)) =
      (fun s ↦ feedbackEnvironmentMarkRate lam true (fun _ ↦ 1) (feedbackEnvironmentCurrent e s) +
        feedbackEnvironmentMarkRate lam false (fun _ ↦ 1) (feedbackEnvironmentCurrent e s)) by
    funext s; simp only [feedbackEnvironmentMarkRate_one hlam0 hlam, ite_true,
      Bool.false_eq_true, ite_false]; rfl,
    intervalIntegral.integral_add hs ht]
  simp only [feedbackEnvironmentTwoColor, ite_true, Bool.false_eq_true, ite_false, Int.cast_add]
  ring

theorem intervalIntegrable_feedbackEnvironmentEventRate {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (e : FeedbackEnvironment) (a b : ℝ) :
    IntervalIntegrable (fun s ↦ totalJumpRate lam (feedbackEnvironmentCurrent e s)) volume a b := by
  convert (intervalIntegrable_feedbackEnvironmentMarkRate lam true (fun _ ↦ 1) e a b).add
    (intervalIntegrable_feedbackEnvironmentMarkRate lam false (fun _ ↦ 1) e a b) using 1
  funext s
  simp only [feedbackEnvironmentMarkRate_one hlam0 hlam, ite_true, Bool.false_eq_true, ite_false]
  rfl

theorem feedbackEnvironmentEventDrift_sub_le {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (e : FeedbackEnvironment) {a b : ℝ} (hab : a ≤ b) :
    feedbackEnvironmentEventDrift lam e b - feedbackEnvironmentEventDrift lam e a ≤
      3 * (b - a) := by
  have hi := intervalIntegrable_feedbackEnvironmentEventRate hlam0 hlam e
  have heq : feedbackEnvironmentEventDrift lam e b - feedbackEnvironmentEventDrift lam e a =
      ∫ s in a..b, totalJumpRate lam (feedbackEnvironmentCurrent e s) := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)
    change (∫ s in 0..b, totalJumpRate lam (feedbackEnvironmentCurrent e s)) -
      (∫ s in 0..a, totalJumpRate lam (feedbackEnvironmentCurrent e s)) = _
    linarith
  rw [heq]
  calc
    _ ≤ ∫ _s in a..b, (3 : ℝ) := intervalIntegral.integral_mono_on hab (hi a b)
      intervalIntegrable_const (fun s _ ↦ ((totalJumpRate_bounds hlam0 _).2).trans (by linarith))
    _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring

theorem feedbackEnvironmentEventDrift_le {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (e : FeedbackEnvironment) (t : ℝ≥0) :
    feedbackEnvironmentEventDrift lam e t ≤ 3 * (t : ℝ) := by
  simpa [feedbackEnvironmentEventDrift] using
    feedbackEnvironmentEventDrift_sub_le hlam0 hlam e t.property

private theorem eventCount_nonneg (e : FeedbackEnvironment) (t : ℝ≥0) :
    0 ≤ feedbackEnvironmentEventCount e t :=
  add_nonneg (LocalConfiguration.spatialCount_nonneg _ _ _)
    (LocalConfiguration.spatialCount_nonneg _ _ _)

theorem feedbackEnvironmentEventCount_mono (e : FeedbackEnvironment) {s t : ℝ≥0} (hst : s ≤ t) :
    feedbackEnvironmentEventCount e s ≤ feedbackEnvironmentEventCount e t := by
  have hs := LocalConfiguration.spatialCount_add e.source s.property
    (show (s : ℝ) ≤ t from hst)
  have ht := LocalConfiguration.spatialCount_add e.target s.property
    (show (s : ℝ) ≤ t from hst)
  unfold feedbackEnvironmentEventCount
  rw [hs, ht]
  exact add_le_add
    (le_add_of_nonneg_right (LocalConfiguration.spatialCount_nonneg e.source s t))
    (le_add_of_nonneg_right (LocalConfiguration.spatialCount_nonneg e.target s t))

section Martingale

variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
  (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
  (htest : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0),
    Measurable[ℱ t] (fun ω ↦ LocalConfiguration.firstEventTestCount
      (feedbackEnvironmentTwoColor (e ω)) b ψ t))
  (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
    Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)

include he hM in
theorem integrable_feedbackEnvironmentEventCount (t : ℝ≥0) :
    Integrable (fun ω ↦ (feedbackEnvironmentEventCount (e ω) t : ℝ)) μ := by
  have hi := (integrable_feedbackEnvironment_spatialCount_of_martingale μ ℱ e he lam true
    (hM true (BoundedContinuousFunction.const UnitMark 1)) t).add
    (integrable_feedbackEnvironment_spatialCount_of_martingale μ ℱ e he lam false
      (hM false (BoundedContinuousFunction.const UnitMark 1)) t)
  convert hi using 1 <;> try rfl
  funext ω
  simp [feedbackEnvironmentEventCount, feedbackEnvironmentTwoColor]

include he htest hM in
theorem integrable_feedbackEnvironmentEventCount_stopping
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω ↦ (feedbackEnvironmentEventCount (e ω) (σ ω) : ℝ)) μ := by
  have hN : StronglyAdapted ℱ (fun t ω ↦ (feedbackEnvironmentEventCount (e ω) t : ℝ)) :=
    fun t ↦ ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
      (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest t)).stronglyMeasurable
  apply integrable_stopping_eval_of_rightContinuous hN hσ hσT
    (Eventually.of_forall fun ω t ↦ continuousWithinAt_feedbackEnvironmentEventCount (e ω) t)
    (integrable_feedbackEnvironmentEventCount μ ℱ e he hM T)
  exact Eventually.of_forall fun ω s hs ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast eventCount_nonneg (e ω) s)]
    exact_mod_cast feedbackEnvironmentEventCount_mono (e ω) hs

include he hlam0 hlam htest hM in
/-- The original marked MP gives the expected total count at any bounded stopping coordinate. -/
theorem integral_feedbackEnvironmentEventCount_stopping
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω ↦ feedbackEnvironmentEventDrift lam (e ω) (σ ω)) μ ∧
    (∫ ω, (feedbackEnvironmentEventCount (e ω) (σ ω) : ℝ) ∂μ) =
      ∫ ω, feedbackEnvironmentEventDrift lam (e ω) (σ ω) ∂μ := by
  have hstop (b : Bool) :
      Integrable (fun ω ↦ feedbackEnvironmentMarkedCompensator lam b (fun _ ↦ 1) (σ ω) (e ω)) μ ∧
      (∫ ω, feedbackEnvironmentMarkedCompensator lam b (fun _ ↦ 1) (σ ω) (e ω) ∂μ) = 0 := by
    obtain ⟨D, hD, hb⟩ := exists_integrable_bound_feedbackEnvironmentMarkedCompensator μ ℱ e he
      lam hM b (BoundedContinuousFunction.const UnitMark 1) T
    have hright : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt
        (fun s ↦ feedbackEnvironmentMarkedCompensator lam b (fun _ ↦ 1) s (e ω)) (Ici t) t :=
      Eventually.of_forall fun ω t ↦
        continuousWithinAt_feedbackEnvironmentMarkedCompensator lam b (fun _ ↦ 1) (e ω) t
    refine ⟨integrable_stopping_eval_of_rightContinuous
      (hM b (BoundedContinuousFunction.const UnitMark 1)).stronglyAdapted hσ hσT hright hD
      (hb.mono fun _ hh s hs ↦ hh s (hs.trans (by simp))), ?_⟩
    have hh := integral_martingale_stopping_of_integrable_bound
      (hM b (BoundedContinuousFunction.const UnitMark 1)) hσ hσT hright hD hb
    have hz : (fun ω ↦ feedbackEnvironmentMarkedCompensator lam b
        (BoundedContinuousFunction.const UnitMark 1) 0 (e ω)) = fun _ ↦ 0 := by
      funext ω
      exact feedbackEnvironmentMarkedCompensator_zero lam b _ (e ω)
    rw [hz, integral_zero] at hh
    exact hh
  have hcount := integrable_feedbackEnvironmentEventCount_stopping μ ℱ e he htest hM hσ hσT
  have hsum : Integrable (fun ω ↦
      feedbackEnvironmentMarkedCompensator lam true (fun _ ↦ 1) (σ ω) (e ω) +
        feedbackEnvironmentMarkedCompensator lam false (fun _ ↦ 1) (σ ω) (e ω)) μ :=
    (hstop true).1.add (hstop false).1
  have hid : (fun ω ↦ feedbackEnvironmentEventDrift lam (e ω) (σ ω)) =
      fun ω ↦ (feedbackEnvironmentEventCount (e ω) (σ ω) : ℝ) -
        (feedbackEnvironmentMarkedCompensator lam true (fun _ ↦ 1) (σ ω) (e ω) +
          feedbackEnvironmentMarkedCompensator lam false (fun _ ↦ 1) (σ ω) (e ω)) := by
    funext ω
    rw [feedbackEnvironment_compensator_sum_one hlam0 hlam]
    ring
  rw [hid]
  refine ⟨hcount.sub hsum, ?_⟩
  rw [integral_sub hcount hsum, integral_add (hstop true).1 (hstop false).1,
    (hstop true).2, (hstop false).2]
  ring

include he hlam0 hlam htest hM in
theorem integral_feedbackEnvironmentEventCount_le (t : ℝ≥0) :
    (∫ ω, (feedbackEnvironmentEventCount (e ω) t : ℝ) ∂μ) ≤ 3 * (t : ℝ) := by
  have hh := integral_feedbackEnvironmentEventCount_stopping μ ℱ e he hlam0 hlam htest hM
    (isStoppingTime_const ℱ t) (T := t) (fun _ ↦ le_rfl)
  rw [hh.2]
  calc
    _ ≤ ∫ _ω, 3 * (t : ℝ) ∂μ := integral_mono hh.1 (integrable_const _)
      (fun ω ↦ feedbackEnvironmentEventDrift_le hlam0 hlam (e ω) t)
    _ = _ := by simp

include he hlam0 hlam htest hM in
/-- Expected events occurring strictly after the first actual event are quadratic in the
observation length. No factorial-moment or collision estimate is a premise. -/
theorem integral_feedbackEnvironment_extraCount_after_first_le (t : ℝ≥0) :
    (∫ ω, ((feedbackEnvironmentEventCount (e ω) t : ℝ) -
      (feedbackEnvironmentEventCount (e ω)
        (cappedStoppingValue t (fun ω ↦ feedbackEnvironmentFirstTime (e ω)) ω) : ℝ)) ∂μ) ≤
      9 * (t : ℝ) ^ 2 := by
  let σ := cappedStoppingValue t (fun ω ↦ feedbackEnvironmentFirstTime (e ω))
  have hτ := feedbackEnvironmentFirstTime_isStoppingTime e ℱ
    (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest)
  have hσ := cappedStoppingValue_isStoppingTime ℱ hτ t
  have hσt := cappedStoppingValue_le t (fun ω ↦ feedbackEnvironmentFirstTime (e ω))
  have hcap := integral_feedbackEnvironmentEventCount_stopping μ ℱ e he hlam0 hlam htest hM hσ hσt
  have htime := integral_feedbackEnvironmentEventCount_stopping μ ℱ e he hlam0 hlam htest hM
    (isStoppingTime_const ℱ t) (T := t) (fun _ ↦ le_rfl)
  let I : Ω → ℝ := fun ω ↦ if feedbackEnvironmentFirstTime (e ω) ≤ (t : ℝ≥0∞) then 1 else 0
  have hI : Integrable I μ := by
    have hh : Integrable ({ω | feedbackEnvironmentFirstTime (e ω) ≤ (t : ℝ≥0∞)}.indicator
        (fun _ ↦ (1 : ℝ))) μ := (integrable_const (1 : ℝ)).indicator
      (hτ.measurableSpace_le _ (hτ.measurableSet_le' t))
    apply hh.congr
    filter_upwards with ω
    by_cases h : feedbackEnvironmentFirstTime (e ω) ≤ (t : ℝ≥0∞) <;> simp [I, h]
  have hIle (ω : Ω) : I ω ≤ (feedbackEnvironmentEventCount (e ω) t : ℝ) := by
    dsimp [I]
    split_ifs with h
    · change LocalConfiguration.firstPositiveTime (feedbackEnvironmentTwoColor (e ω)) ≤
        (t : ℝ≥0∞) at h
      have hfirstle : LocalConfiguration.firstPositiveTime (feedbackEnvironmentTwoColor (e ω)) ≤
          ENNReal.ofReal (t : ℝ) := by
        rw [ENNReal.ofReal_coe_nnreal]
        exact h
      have hc := (LocalConfiguration.firstPositiveTime_le_iff
        (feedbackEnvironmentTwoColor (e ω)) (t := (t : ℝ)) t.property).mp hfirstle
      exact_mod_cast hc
    · exact_mod_cast eventCount_nonneg (e ω) t
  have hEI : (∫ ω, I ω ∂μ) ≤ 3 * (t : ℝ) :=
    (integral_mono hI (integrable_feedbackEnvironmentEventCount μ ℱ e he hM t) hIle).trans
      (integral_feedbackEnvironmentEventCount_le μ ℱ e he hlam0 hlam htest hM t)
  have hDrift (ω : Ω) :
      feedbackEnvironmentEventDrift lam (e ω) t - feedbackEnvironmentEventDrift lam (e ω) (σ ω) ≤
        (3 * (t : ℝ)) * I ω := by
    by_cases h : feedbackEnvironmentFirstTime (e ω) ≤ (t : ℝ≥0∞)
    · have hh := feedbackEnvironmentEventDrift_sub_le hlam0 hlam (e ω)
        (show (σ ω : ℝ) ≤ t from hσt ω)
      simp only [I, h, ite_true, mul_one]
      exact hh.trans (by nlinarith [NNReal.coe_nonneg (σ ω)])
    · have heq : σ ω = t := by
        apply ENNReal.coe_injective
        have hc := coe_cappedStoppingValue t (fun ω ↦ feedbackEnvironmentFirstTime (e ω)) ω
        change (σ ω : ℝ≥0∞) = min (feedbackEnvironmentFirstTime (e ω)) (t : ℝ≥0∞) at hc
        rw [hc, min_eq_right (le_of_not_ge h)]
      simp only [heq, sub_self, I, h, ite_false, mul_zero, le_refl]
  rw [integral_sub (integrable_feedbackEnvironmentEventCount μ ℱ e he hM t)
    (integrable_feedbackEnvironmentEventCount_stopping μ ℱ e he htest hM hσ hσt),
    htime.2, hcap.2, ← integral_sub htime.1 hcap.1]
  calc
    _ ≤ ∫ ω, (3 * (t : ℝ)) * I ω ∂μ := integral_mono (htime.1.sub hcap.1)
      (hI.const_mul _) hDrift
    _ = (3 * (t : ℝ)) * ∫ ω, I ω ∂μ := integral_const_mul _ _
    _ ≤ 9 * (t : ℝ) ^ 2 := by nlinarith [t.property]

end Martingale
end OTSelector.Limit
