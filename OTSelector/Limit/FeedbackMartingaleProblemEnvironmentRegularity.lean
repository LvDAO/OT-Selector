import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentFirstJump
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Regularity forced by the actual marked-count martingale problem

The feedback mark rate has only three values, one for each sign of the current. Its bounded
measurable drift therefore has a continuous primitive. Right continuity of actual marked
counts gives right continuity of the compensator. The constant-one counting martingale supplies
an integrable unweighted count, which controls every bounded mark test on a finite horizon.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BoundedContinuousFunction Topology

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.Limit

open PointProcess

/-- A deterministic bound for the three possible values of the actual color mark rate. -/
noncomputable def feedbackEnvironmentMarkRateBound
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) : ℝ :=
  ‖feedbackEnvironmentMarkRate lam b ψ (-1)‖ +
    ‖feedbackEnvironmentMarkRate lam b ψ 0‖ +
      ‖feedbackEnvironmentMarkRate lam b ψ 1‖

theorem feedbackEnvironmentMarkRateBound_nonneg (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) :
    0 ≤ feedbackEnvironmentMarkRateBound lam b ψ := by
  unfold feedbackEnvironmentMarkRateBound
  positivity

theorem norm_feedbackEnvironmentMarkRate_le (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ)
    (j : ℤ) : ‖feedbackEnvironmentMarkRate lam b ψ j‖ ≤
      feedbackEnvironmentMarkRateBound lam b ψ := by
  have hn := norm_nonneg (feedbackEnvironmentMarkRate lam b ψ (-1))
  have hz := norm_nonneg (feedbackEnvironmentMarkRate lam b ψ 0)
  have hp := norm_nonneg (feedbackEnvironmentMarkRate lam b ψ 1)
  unfold feedbackEnvironmentMarkRateBound
  cases j with
  | ofNat n =>
    cases n with
    | zero =>
      change ‖feedbackEnvironmentMarkRate lam b ψ 0‖ ≤ _
      linarith
    | succ n =>
      change ‖feedbackEnvironmentMarkRate lam b ψ 1‖ ≤ _
      linarith
  | negSucc n =>
    change ‖feedbackEnvironmentMarkRate lam b ψ (-1)‖ ≤ _
    linarith

theorem measurable_feedbackEnvironmentMarkRate_current
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) :
    Measurable (fun p : ℝ × FeedbackEnvironment ↦
      feedbackEnvironmentMarkRate lam b ψ (feedbackEnvironmentCurrent p.2 p.1)) :=
  (measurable_of_countable (feedbackEnvironmentMarkRate lam b ψ)).comp
    measurable_feedbackEnvironmentCurrent

/-- No regularity of the mark test is needed for local time integrability: after integrating
over its mark law, the resulting state rate has only three real values. -/
theorem intervalIntegrable_feedbackEnvironmentMarkRate
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) (e : FeedbackEnvironment) (a d : ℝ) :
    IntervalIntegrable (fun s ↦ feedbackEnvironmentMarkRate lam b ψ
      (feedbackEnvironmentCurrent e s)) volume a d := by
  have hi : Measurable (fun s : ℝ ↦ (s, e)) := measurable_id.prodMk measurable_const
  have hm := (measurable_feedbackEnvironmentMarkRate_current lam b ψ).comp hi
  apply (intervalIntegrable_const (c := feedbackEnvironmentMarkRateBound lam b ψ)).mono_fun'
    hm.aestronglyMeasurable
  exact Eventually.of_forall fun s ↦ norm_feedbackEnvironmentMarkRate_le lam b ψ _

theorem continuous_integral_feedbackEnvironmentMarkRate_current
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) (e : FeedbackEnvironment) :
    Continuous (fun t : ℝ ↦ ∫ s in 0..t,
      feedbackEnvironmentMarkRate lam b ψ (feedbackEnvironmentCurrent e s)) :=
  intervalIntegral.continuous_primitive
    (intervalIntegrable_feedbackEnvironmentMarkRate lam b ψ e) 0

/-- Right continuity of the original compensator follows from the actual count and drift. -/
theorem continuousWithinAt_feedbackEnvironmentMarkedCompensator
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) (e : FeedbackEnvironment) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ feedbackEnvironmentMarkedCompensator lam b ψ s e)
      (Ici t) t := by
  exact (LocalConfiguration.continuousWithinAt_firstEventTestCount_nnreal
    (feedbackEnvironmentTwoColor e) b ψ t).sub
      (((continuous_integral_feedbackEnvironmentMarkRate_current lam b ψ e).comp
        continuous_subtype_val).continuousWithinAt)

/-- Fixed-horizon drift is measurable as a function of the actual environment. -/
theorem measurable_integral_feedbackEnvironmentMarkRate_current
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) (t : ℝ) :
    Measurable (fun e : FeedbackEnvironment ↦ ∫ s in 0..t,
      feedbackEnvironmentMarkRate lam b ψ (feedbackEnvironmentCurrent e s)) := by
  have hm := (measurable_feedbackEnvironmentMarkRate_current lam b ψ).comp measurable_swap
  exact ((hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 t))).sub
    (hm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc t 0)))).measurable

theorem norm_integral_feedbackEnvironmentMarkRate_current_le
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) (e : FeedbackEnvironment) (t : ℝ) :
    ‖∫ s in 0..t, feedbackEnvironmentMarkRate lam b ψ (feedbackEnvironmentCurrent e s)‖ ≤
      feedbackEnvironmentMarkRateBound lam b ψ * |t| := by
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t)
    (fun s _ ↦ norm_feedbackEnvironmentMarkRate_le lam b ψ (feedbackEnvironmentCurrent e s))

theorem integrable_integral_feedbackEnvironmentMarkRate_current
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (e : Ω → FeedbackEnvironment) (he : Measurable e)
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) (t : ℝ) :
    Integrable (fun ω ↦ ∫ s in 0..t,
      feedbackEnvironmentMarkRate lam b ψ (feedbackEnvironmentCurrent (e ω) s)) μ := by
  apply (integrable_const (feedbackEnvironmentMarkRateBound lam b ψ * |t|)).mono'
    ((measurable_integral_feedbackEnvironmentMarkRate_current lam b ψ t).comp
      he).aestronglyMeasurable
  exact Eventually.of_forall fun ω ↦
    norm_integral_feedbackEnvironmentMarkRate_current_le lam b ψ (e ω) t

/-- The original constant-one compensator implies integrability of the actual unweighted
count. The drift is integrable because its rate takes only three values. -/
theorem integrable_feedbackEnvironment_spatialCount_of_martingale
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) (lam : ℝ) (b : Bool)
    (hM : Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b
      (fun _ ↦ 1) t (e ω)) ℱ μ) (t : ℝ≥0) :
    Integrable (fun ω ↦ (LocalConfiguration.spatialCount
      (feedbackEnvironmentTwoColor (e ω) b) 0 t : ℝ)) μ := by
  have hi := (hM.integrable t).add
    (integrable_integral_feedbackEnvironmentMarkRate_current μ e he lam b (fun _ ↦ 1) t)
  apply hi.congr
  filter_upwards with ω
  change feedbackEnvironmentMarkedCompensator lam b (fun _ ↦ 1) t (e ω) +
    (∫ s in 0..(t : ℝ), feedbackEnvironmentMarkRate lam b (fun _ ↦ 1)
      (feedbackEnvironmentCurrent (e ω) s)) = _
  rw [feedbackEnvironmentMarkedCompensator, sub_add_cancel,
    LocalConfiguration.firstEventTestCount_one]

/-- A single original constant-one martingale supplies an integrable envelope for every
bounded continuous mark test of that color on a finite horizon. -/
theorem exists_integrable_bound_feedbackEnvironmentMarkedCompensator_of_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) (lam : ℝ) (b : Bool)
    (hM : Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b
      (fun _ ↦ 1) t (e ω)) ℱ μ)
    (ψ : UnitMark →ᵇ ℝ) (T : ℝ≥0) :
    ∃ D : Ω → ℝ, Integrable D μ ∧ ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 →
      ‖feedbackEnvironmentMarkedCompensator lam b ψ s (e ω)‖ ≤ D ω := by
  let D : Ω → ℝ := fun ω ↦ ‖ψ‖ * (LocalConfiguration.spatialCount
      (feedbackEnvironmentTwoColor (e ω) b) 0 (T + 1) : ℝ) +
    feedbackEnvironmentMarkRateBound lam b ψ * ((T + 1 : ℝ≥0) : ℝ)
  refine ⟨D, ?_, Eventually.of_forall fun ω s hs ↦ ?_⟩
  · exact ((integrable_feedbackEnvironment_spatialCount_of_martingale μ ℱ e he lam b hM
      (T + 1)).const_mul ‖ψ‖).add (integrable_const _)
  · have hst : (s : ℝ) ≤ ((T + 1 : ℝ≥0) : ℝ) := by exact_mod_cast hs
    have hcount := LocalConfiguration.norm_firstEventTestCount_le
      (feedbackEnvironmentTwoColor (e ω)) b ψ hst
    have hdrift := norm_integral_feedbackEnvironmentMarkRate_current_le lam b ψ (e ω) s
    simp only [NNReal.abs_eq] at hdrift
    exact (norm_sub_le _ _).trans ((add_le_add hcount hdrift).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hst
        (feedbackEnvironmentMarkRateBound_nonneg lam b ψ))))

/-- The actual marked-count martingale problem entails the local integrable-envelope premise. -/
theorem exists_integrable_bound_feedbackEnvironmentMarkedCompensator
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) (lam : ℝ)
    (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
      Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
    (b : Bool) (ψ : UnitMark →ᵇ ℝ) (T : ℝ≥0) :
    ∃ D : Ω → ℝ, Integrable D μ ∧ ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 →
      ‖feedbackEnvironmentMarkedCompensator lam b ψ s (e ω)‖ ≤ D ω :=
  exists_integrable_bound_feedbackEnvironmentMarkedCompensator_of_one μ ℱ e he lam b
    (hM b (BoundedContinuousFunction.const UnitMark 1)) ψ T

/-- The original actual marked-count martingale problem determines the first marked holding
law on every initial history event with fixed current. Right continuity and local integrable
envelopes are consequences of the actual configurations and the constant-one martingales. -/
theorem feedbackEnvironment_firstJumpLaw_cond_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
    (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
      Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) (hA0 : μ A ≠ 0)
    (k : ℤ) (hk : ∀ ω ∈ A, (e ω).path.rootCurrent = k) :
    attainedFirstJumpLaw μ[|A] (fun ω ↦ feedbackEnvironmentFirstTime (e ω))
      (fun ω ↦ feedbackEnvironmentFirstJump (e ω)) =
      (expMeasure (totalJumpRate lam k)).prod (feedbackMarkedJumpKernel lam k) :=
  feedbackEnvironment_firstJumpLaw_cond_eq_of_marked_martingale μ ℱ e he hlam0 hlam
    hcount hsimple hM
    (fun b ψ ↦ Eventually.of_forall fun ω t ↦
      continuousWithinAt_feedbackEnvironmentMarkedCompensator lam b ψ (e ω) t)
    (fun b ψ T ↦ exists_integrable_bound_feedbackEnvironmentMarkedCompensator
      μ ℱ e he lam hM b ψ T)
    hA hA0 k hk

end OTSelector.Limit
