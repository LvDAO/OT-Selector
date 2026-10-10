import OTSelector.Limit.FeedbackMartingaleProblemCurrentSmallTime

/-!
# A one-jump approximation for actual current indicators

A bounded current indicator can differ from its first-jump approximation only when an
additional actual event has occurred. The quadratic extra-count estimate therefore controls
the expectation error without assuming a Markov property or a second-moment estimate.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit

open PointProcess CountingProcess

/-- Indicator of one integer current value. -/
def feedbackCurrentIndicator (k j : ℤ) : ℝ := if j = k then 1 else 0

theorem norm_feedbackCurrentIndicator_le (k j : ℤ) : ‖feedbackCurrentIndicator k j‖ ≤ 1 := by
  unfold feedbackCurrentIndicator
  split_ifs <;> norm_num

/-- The current at a nonnegative cut uses precisely the two actual forward counts. -/
theorem feedbackEnvironmentCurrent_nnreal (e : FeedbackEnvironment) (t : ℝ≥0) :
    feedbackEnvironmentCurrent e t = e.path.rootCurrent +
      LocalConfiguration.spatialCount e.source 0 t - LocalConfiguration.spatialCount e.target 0 t := by
  have hs : LocalConfiguration.spatialCount e.source (t : ℝ) 0 = 0 :=
    LocalConfiguration.spatialCount_eq_zero_of_le _ t.property
  have ht : LocalConfiguration.spatialCount e.target (t : ℝ) 0 = 0 :=
    LocalConfiguration.spatialCount_eq_zero_of_le _ t.property
  change e.path.rootCurrent +
    ((LocalConfiguration.spatialCount e.source 0 (t : ℝ) - LocalConfiguration.spatialCount e.source (t : ℝ) 0) -
      (LocalConfiguration.spatialCount e.target 0 (t : ℝ) - LocalConfiguration.spatialCount e.target (t : ℝ) 0)) = _
  rw [hs, ht]
  ring

/-- No increase of total event count means no change in the actual current. -/
theorem feedbackEnvironmentCurrent_eq_of_eventCount_eq (e : FeedbackEnvironment)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hcount : feedbackEnvironmentEventCount e t = feedbackEnvironmentEventCount e s) :
    feedbackEnvironmentCurrent e t = feedbackEnvironmentCurrent e s := by
  have hs := LocalConfiguration.spatialCount_add e.source s.property
    (show (s : ℝ) ≤ t from hst)
  have ht := LocalConfiguration.spatialCount_add e.target s.property
    (show (s : ℝ) ≤ t from hst)
  have hsn := LocalConfiguration.spatialCount_nonneg e.source s t
  have htn := LocalConfiguration.spatialCount_nonneg e.target s t
  have halg (A B C D E F : ℤ) (h₁ : A = B + C) (h₂ : D = E + F)
      (h₃ : A + D = B + E) (h₄ : 0 ≤ C) (h₅ : 0 ≤ F) : A - D = B - E := by omega
  have hh := halg _ _ _ _ _ _ hs ht hcount hsn htn
  rw [feedbackEnvironmentCurrent_nnreal, feedbackEnvironmentCurrent_nnreal]
  calc
    _ = e.path.rootCurrent + (LocalConfiguration.spatialCount e.source 0 t -
        LocalConfiguration.spatialCount e.target 0 t) := by ring
    _ = e.path.rootCurrent + (LocalConfiguration.spatialCount e.source 0 s -
        LocalConfiguration.spatialCount e.target 0 s) := congrArg (e.path.rootCurrent + ·) hh
    _ = _ := by ring

/-- A current indicator changes by at most the number of intervening actual events. -/
theorem norm_feedbackCurrentIndicator_sub_le_eventCount (e : FeedbackEnvironment)
    (k : ℤ) {s t : ℝ≥0} (hst : s ≤ t) :
    ‖feedbackCurrentIndicator k (feedbackEnvironmentCurrent e t) -
      feedbackCurrentIndicator k (feedbackEnvironmentCurrent e s)‖ ≤
        (feedbackEnvironmentEventCount e t : ℝ) - (feedbackEnvironmentEventCount e s : ℝ) := by
  have hmono := feedbackEnvironmentEventCount_mono e hst
  by_cases heq : feedbackEnvironmentEventCount e t = feedbackEnvironmentEventCount e s
  · rw [feedbackEnvironmentCurrent_eq_of_eventCount_eq e hst heq, sub_self, norm_zero,
      heq, sub_self]
  · have hgap : (1 : ℝ) ≤ (feedbackEnvironmentEventCount e t : ℝ) -
        (feedbackEnvironmentEventCount e s : ℝ) := by
      have hh : (1 : ℤ) ≤ feedbackEnvironmentEventCount e t - feedbackEnvironmentEventCount e s := by omega
      exact_mod_cast hh
    apply le_trans _ hgap
    unfold feedbackCurrentIndicator
    split_ifs <;> norm_num

/-- Current indicator after retaining only the first actual event before the given cut. -/
noncomputable def feedbackFirstCurrentIndicator (k : ℤ) (t : ℝ≥0) (e : FeedbackEnvironment) : ℝ :=
  if feedbackEnvironmentFirstTime e ≤ (t : ℝ≥0∞) then
    feedbackCurrentIndicator k (feedbackEnvironmentFirstJump e).2 else
    feedbackCurrentIndicator k e.path.rootCurrent

/-- Stopping the actual current at its first event gives precisely the one-jump readout. -/
theorem feedbackCurrentIndicator_capped_first (e : FeedbackEnvironment)
    (hsimple : LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor e))
    (k : ℤ) (t : ℝ≥0) :
    feedbackCurrentIndicator k (feedbackEnvironmentCurrent e
      (cappedStoppingValue t (fun _ : Unit ↦ feedbackEnvironmentFirstTime e) ())) =
        feedbackFirstCurrentIndicator k t e := by
  let σ := cappedStoppingValue t (fun _ : Unit ↦ feedbackEnvironmentFirstTime e) ()
  have hc := coe_cappedStoppingValue t (fun _ : Unit ↦ feedbackEnvironmentFirstTime e) ()
  change (σ : ℝ≥0∞) = min (feedbackEnvironmentFirstTime e) (t : ℝ≥0∞) at hc
  by_cases ht : feedbackEnvironmentFirstTime e ≤ (t : ℝ≥0∞)
  · have hfinite := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
    have heq : (σ : ℝ) = (feedbackEnvironmentFirstTime e).toReal := by
      have hh := congrArg ENNReal.toReal (hc.trans (min_eq_left ht))
      simpa only [ENNReal.coe_toReal] using hh
    change feedbackCurrentIndicator k (feedbackEnvironmentCurrent e (σ : ℝ)) = _
    rw [heq, feedbackEnvironmentCurrent_firstTime e hsimple hfinite]
    simp only [feedbackFirstCurrentIndicator, ht, ite_true]
  · have heq : σ = t := ENNReal.coe_injective (hc.trans (min_eq_right (le_of_not_ge ht)))
    change feedbackCurrentIndicator k (feedbackEnvironmentCurrent e (σ : ℝ)) = _
    rw [heq]
    have hbefore : ENNReal.ofReal (t : ℝ) < feedbackEnvironmentFirstTime e := by
      rw [ENNReal.ofReal_coe_nnreal]
      exact lt_of_not_ge ht
    have hh := feedbackEnvironmentCurrent_before_first e (x := (t : ℝ)) t.property hbefore
    rw [hh]
    simp only [feedbackFirstCurrentIndicator, ht, ite_false]

theorem measurable_feedbackFirstCurrentIndicator (k : ℤ) (t : ℝ≥0) :
    Measurable (feedbackFirstCurrentIndicator k t) :=
  ((measurable_of_countable (feedbackCurrentIndicator k)).comp
    measurable_feedbackEnvironmentFirstJump.snd).ite
      (measurableSet_le measurable_feedbackEnvironmentFirstTime measurable_const)
      ((measurable_of_countable (feedbackCurrentIndicator k)).comp
        FeedbackEnvironment.measurable_rootCurrent)

theorem integrable_feedbackCurrentIndicator (μ : Measure FeedbackEnvironment)
    [IsFiniteMeasure μ] (k : ℤ) (t : ℝ) :
    Integrable (fun e ↦ feedbackCurrentIndicator k (feedbackEnvironmentCurrent e t)) μ := by
  have hm : Measurable (fun e ↦ feedbackCurrentIndicator k (feedbackEnvironmentCurrent e t)) :=
    (measurable_of_countable (feedbackCurrentIndicator k)).comp
      (measurable_feedbackEnvironmentCurrent.comp
        (f := fun e : FeedbackEnvironment ↦ (t, e)) (measurable_const.prodMk measurable_id))
  exact Integrable.of_bound hm.aestronglyMeasurable 1
    (Eventually.of_forall fun e ↦ norm_feedbackCurrentIndicator_le _ _)

/-- The expectation error of the one-jump indicator approximation is genuinely quadratic. -/
theorem norm_integral_feedbackCurrentIndicator_sub_first_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (htest : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0),
      Measurable[ℱ t] (fun ω ↦ LocalConfiguration.firstEventTestCount
        (feedbackEnvironmentTwoColor (e ω)) b ψ t))
    (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
    (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
      Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
    (k : ℤ) (t : ℝ≥0) :
    ‖∫ ω, (feedbackCurrentIndicator k (feedbackEnvironmentCurrent (e ω) t) -
      feedbackFirstCurrentIndicator k t (e ω)) ∂μ‖ ≤ 9 * (t : ℝ) ^ 2 := by
  let σ := cappedStoppingValue t (fun ω ↦ feedbackEnvironmentFirstTime (e ω))
  have hτ := feedbackEnvironmentFirstTime_isStoppingTime e ℱ
    (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest)
  have hσ := cappedStoppingValue_isStoppingTime ℱ hτ t
  have hσt := cappedStoppingValue_le t (fun ω ↦ feedbackEnvironmentFirstTime (e ω))
  have hi : Integrable (fun ω ↦ (feedbackEnvironmentEventCount (e ω) t : ℝ) -
      (feedbackEnvironmentEventCount (e ω) (σ ω) : ℝ)) μ :=
    (integrable_feedbackEnvironmentEventCount μ ℱ e he hM t).sub
      (integrable_feedbackEnvironmentEventCount_stopping μ ℱ e he htest hM hσ hσt)
  have hb : ∀ᵐ ω ∂μ,
      ‖feedbackCurrentIndicator k (feedbackEnvironmentCurrent (e ω) t) -
        feedbackFirstCurrentIndicator k t (e ω)‖ ≤
      (feedbackEnvironmentEventCount (e ω) t : ℝ) -
        (feedbackEnvironmentEventCount (e ω) (σ ω) : ℝ) := by
    filter_upwards [hsimple] with ω hω
    rw [← feedbackCurrentIndicator_capped_first (e ω) hω k t]
    exact norm_feedbackCurrentIndicator_sub_le_eventCount (e ω) k (hσt ω)
  exact (norm_integral_le_of_norm_le hi hb).trans
    (integral_feedbackEnvironment_extraCount_after_first_le μ ℱ e he hlam0 hlam htest hM t)

end OTSelector.Limit
