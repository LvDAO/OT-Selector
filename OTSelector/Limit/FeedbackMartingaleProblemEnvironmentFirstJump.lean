import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentReadout
import OTSelector.Limit.FeedbackMartingaleProblemCountingReadout

/-!
# The actual environment's first-jump law from its marked-count martingales

The processes in the hypotheses count the real source and target configurations and integrate
the actual feedback rates. First-event geometry and the frozen pre-jump current supply the
stopped readout. Conditioning on any initial history event with fixed root current identifies
the first waiting time, geometric mark, and resulting current.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.Limit

open PointProcess
attribute [local instance] Classical.propDecidable

/-- The actual color rate applied to a geometric-mark test in current `j`. -/
noncomputable def feedbackEnvironmentMarkRate
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) (j : ℤ) : ℝ :=
  if b then birthRate lam j * sourceFeedbackMarkMean (lam * currentSign j) ψ
  else deathRate lam j * targetFeedbackMarkMean (lam * currentSign j) ψ

/-- The original marked-count compensator, read directly from the two actual configurations. -/
noncomputable def feedbackEnvironmentMarkedCompensator
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) (t : ℝ≥0)
    (e : FeedbackEnvironment) : ℝ :=
  LocalConfiguration.firstEventTestCount (feedbackEnvironmentTwoColor e) b ψ t -
    ∫ s in 0..(t : ℝ), feedbackEnvironmentMarkRate lam b ψ
      (feedbackEnvironmentCurrent e s)

/-- A test of the next mark and current, restricted to one possible jump color. -/
def feedbackNextCurrentTest (k : ℤ) (ψ : (UnitMark × ℤ) →ᵇ ℝ) (b : Bool) :
    UnitMark →ᵇ ℝ :=
  ψ.compContinuous ⟨fun u ↦ (u, if b then k + 1 else k - 1),
    continuous_id.prodMk continuous_const⟩

/-- Summing the two original continuous-test compensators tests the next marked current. -/
noncomputable def feedbackEnvironmentJumpCompensator
    (lam : ℝ) (k : ℤ) (ψ : (UnitMark × ℤ) →ᵇ ℝ)
    (t : ℝ≥0) (e : FeedbackEnvironment) : ℝ :=
  feedbackEnvironmentMarkedCompensator lam true (feedbackNextCurrentTest k ψ true) t e +
    feedbackEnvironmentMarkedCompensator lam false (feedbackNextCurrentTest k ψ false) t e

/-- The raw two-color marked-count compensator stopped at the actual first event is precisely
its first-jump compensator. No distributional identity is assumed here. -/
theorem feedbackEnvironmentJumpCompensator_stopped
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (e : FeedbackEnvironment) (hsimple : LocalConfiguration.IsTimeSimple
      (feedbackEnvironmentTwoColor e)) (k : ℤ) (hk : e.path.rootCurrent = k)
    (ψ : (UnitMark × ℤ) →ᵇ ℝ) (t : ℝ≥0) :
    feedbackEnvironmentJumpCompensator lam k ψ
      (CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ feedbackEnvironmentFirstTime e) ()) e =
    firstJumpTestCompensator (totalJumpRate lam k) (feedbackMarkedJumpKernel lam k)
      feedbackEnvironmentFirstTime feedbackEnvironmentFirstJump ψ t e := by
  have hcount (b : Bool) := LocalConfiguration.firstEventTestCount_capped
    (feedbackEnvironmentTwoColor e) hsimple b (feedbackNextCurrentTest k ψ b) t
  have hint (b : Bool) := integral_feedbackEnvironmentCurrent_capped_first e
    (feedbackEnvironmentMarkRate lam b (feedbackNextCurrentTest k ψ b)) t
  let L : ℝ := ∫ s in 0..(t : ℝ),
    if ENNReal.ofReal s < feedbackEnvironmentFirstTime e then 1 else 0
  have hL (d : ∀ s : ℝ, Decidable (ENNReal.ofReal s < feedbackEnvironmentFirstTime e)) :
      (∫ s in 0..(t : ℝ), @ite ℝ (ENNReal.ofReal s < feedbackEnvironmentFirstTime e)
        (d s) 1 0) = L := by
    unfold L
    apply intervalIntegral.integral_congr
    intro s _
    by_cases h : ENNReal.ofReal s < feedbackEnvironmentFirstTime e <;> simp [h]
  unfold feedbackEnvironmentJumpCompensator feedbackEnvironmentMarkedCompensator
  erw [hcount true, hcount false, hint true, hint false]
  simp only [feedbackEnvironmentMarkRate, feedbackNextCurrentTest,
    BoundedContinuousFunction.compContinuous_apply, BoundedContinuousFunction.coe_compContinuous,
    ContinuousMap.coe_mk, Function.comp_def, Bool.false_eq_true, ↓reduceIte]
  unfold firstJumpTestCompensator
  have hLOrder := hL (fun s ↦ @LinearOrder.toDecidableLT ℝ≥0∞ inferInstance
    (ENNReal.ofReal s) (feedbackEnvironmentFirstTime e))
  rw [hLOrder]
  change
    ((if feedbackEnvironmentFirstTime e ≤ ENNReal.ofReal (t : ℝ) ∧
          (feedbackEnvironmentFirstEvent e).1 = true
      then ψ ((feedbackEnvironmentFirstEvent e).2.2, k + 1) else 0) -
        (birthRate lam e.path.rootCurrent * sourceFeedbackMarkMean
          (lam * currentSign e.path.rootCurrent) (fun u ↦ ψ (u, k + 1))) * L) +
    ((if feedbackEnvironmentFirstTime e ≤ ENNReal.ofReal (t : ℝ) ∧
          (feedbackEnvironmentFirstEvent e).1 = false
      then ψ ((feedbackEnvironmentFirstEvent e).2.2, k - 1) else 0) -
        (deathRate lam e.path.rootCurrent * targetFeedbackMarkMean
          (lam * currentSign e.path.rootCurrent) (fun u ↦ ψ (u, k - 1))) * L) =
    (if feedbackEnvironmentFirstTime e ≤ ENNReal.ofReal (t : ℝ)
      then ψ (feedbackEnvironmentFirstJump e) else 0) -
        (totalJumpRate lam k * ∫ z, ψ z ∂feedbackMarkedJumpKernel lam k) * L
  rw [hk, totalJumpRate_mul_integral_feedbackMarkedJumpKernel hlam0 hlam k ψ]
  by_cases ht : feedbackEnvironmentFirstTime e ≤ ENNReal.ofReal (t : ℝ)
  · cases hb : (feedbackEnvironmentFirstEvent e).1 <;>
      simp only [ht, true_and, Bool.false_eq_true, Bool.true_eq_false,
        ↓reduceIte, feedbackEnvironmentFirstJump, hk, hb] <;>
      simp only [sub_eq_add_neg] <;> ring
  · simp only [ht, false_and, ↓reduceIte]
    ring

@[simp]
theorem feedbackEnvironmentMarkedCompensator_zero
    (lam : ℝ) (b : Bool) (ψ : UnitMark → ℝ) (e : FeedbackEnvironment) :
    feedbackEnvironmentMarkedCompensator lam b ψ 0 e = 0 := by
  simp [feedbackEnvironmentMarkedCompensator,
    LocalConfiguration.firstEventTestCount_zero]

/-- An actual bare-environment marked martingale problem determines its first jump even after
conditioning on an arbitrary initially revealed event. Simplicity is a path support condition;
the first-jump law itself is derived from the original counting martingales. -/
theorem feedbackEnvironment_firstJumpLaw_cond_eq_of_marked_martingale
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
    (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
      Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
    (hRight : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ), ∀ᵐ ω ∂μ, ∀ t,
      ContinuousWithinAt (fun s ↦ feedbackEnvironmentMarkedCompensator lam b ψ s (e ω))
        (Ici t) t)
    (hEnvelope : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) T, ∃ D : Ω → ℝ,
      Integrable D μ ∧ ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 →
        ‖feedbackEnvironmentMarkedCompensator lam b ψ s (e ω)‖ ≤ D ω)
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) (hA0 : μ A ≠ 0)
    (k : ℤ) (hk : ∀ ω ∈ A, (e ω).path.rootCurrent = k) :
    attainedFirstJumpLaw μ[|A] (fun ω ↦ feedbackEnvironmentFirstTime (e ω))
      (fun ω ↦ feedbackEnvironmentFirstJump (e ω)) =
      (expMeasure (totalJumpRate lam k)).prod (feedbackMarkedJumpKernel lam k) := by
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  apply attainedFirstJumpLaw_cond_eq_of_local_stopped_test_readout μ ℱ
    (measurable_feedbackEnvironmentFirstTime.comp he)
    (measurable_feedbackEnvironmentFirstJump.comp he)
    (feedbackEnvironmentFirstTime_isStoppingTime e ℱ hcount)
    (feedbackMarkedJumpKernel lam k) (totalJumpRate_pos hlam0 hlam k)
    (fun ψ t ω ↦ feedbackEnvironmentJumpCompensator lam k ψ t (e ω))
  · intro ψ
    exact (hM true (feedbackNextCurrentTest k ψ true)).add
      (hM false (feedbackNextCurrentTest k ψ false))
  · intro ψ
    exact Eventually.of_forall fun ω ↦ by simp [feedbackEnvironmentJumpCompensator]
  · intro ψ
    filter_upwards [hRight true (feedbackNextCurrentTest k ψ true),
      hRight false (feedbackNextCurrentTest k ψ false)] with ω hs ht
    intro t
    exact (hs t).add (ht t)
  · intro ψ T
    obtain ⟨Ds, hDs, hbs⟩ := hEnvelope true (feedbackNextCurrentTest k ψ true) T
    obtain ⟨Dt, hDt, hbt⟩ := hEnvelope false (feedbackNextCurrentTest k ψ false) T
    refine ⟨fun ω ↦ Ds ω + Dt ω, hDs.add hDt, ?_⟩
    filter_upwards [hbs, hbt] with ω hs ht
    intro s hst
    exact (norm_add_le _ _).trans (add_le_add (hs s hst) (ht s hst))
  · exact hA
  · exact hA0
  · intro ψ t
    filter_upwards [ae_restrict_of_ae hsimple,
      ae_restrict_mem (ℱ.le 0 _ hA)] with ω hs hω
    exact feedbackEnvironmentJumpCompensator_stopped hlam0 hlam (e ω) hs k (hk ω hω) ψ t

end OTSelector.Limit
