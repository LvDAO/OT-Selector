import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentRestartReadout
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentNextStopping

/-!
# The actual conditional marked jump law after a bounded observed cut

Optional sampling is applied to increments of the original marked-count martingales. Actual
rerooting supplies their stopped readout, while revealed counts supply the next-event stopping
time. Thus the restart kernel is proved on every stopped-history event, rather than assumed as
a strong Markov property.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.Limit

open PointProcess

/-- After any bounded observed stopping coordinate, conditioning on any event in its revealed
history with fixed current gives the actual marked holding kernel. In particular the next
waiting time is finite almost surely on that event. -/
theorem feedbackEnvironment_nextJumpLaw_cond_eq_of_bounded_stopping
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
    (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
      Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0))
    {S : ℝ≥0} (hσS : ∀ ω, σ ω ≤ S)
    {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) (hA0 : μ A ≠ 0)
    (k : ℤ) (hk : ∀ᵐ ω ∂μ.restrict A, feedbackEnvironmentCurrent (e ω) (σ ω) = k) :
    attainedFirstJumpLaw μ[|A]
      (fun ω ↦ feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot (σ ω) (e ω)))
      (fun ω ↦ feedbackEnvironmentFirstJump (FeedbackEnvironment.reroot (σ ω) (e ω))) =
        feedbackMarkedHoldingKernel lam k ∧
      ∀ᵐ ω ∂μ[|A],
        feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot (σ ω) (e ω)) ≠ ∞ := by
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  let := feedbackMarkedHoldingKernel_isMarkov hlam0 hlam
  let := cond_isProbabilityMeasure (μ := μ) hA0
  have hσm : Measurable (fun ω ↦ (σ ω : ℝ≥0∞)) := hσ.measurable'
  have hσreal : Measurable (fun ω ↦ (σ ω : ℝ)) := by
    simpa using hσm.ennreal_toReal
  have hreroot : Measurable (fun ω ↦ FeedbackEnvironment.reroot (σ ω) (e ω)) :=
    FeedbackEnvironment.measurable_uncurry_reroot.comp
      (f := fun ω ↦ ((σ ω : ℝ), e ω)) (hσreal.prodMk he)
  have hτ := measurable_feedbackEnvironmentFirstTime.comp hreroot
  have hJ := measurable_feedbackEnvironmentFirstJump.comp hreroot
  have heq : attainedFirstJumpLaw μ[|A]
      (fun ω ↦ feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot (σ ω) (e ω)))
      (fun ω ↦ feedbackEnvironmentFirstJump (FeedbackEnvironment.reroot (σ ω) (e ω))) =
        feedbackMarkedHoldingKernel lam k := by
    apply attainedFirstJumpLaw_cond_eq_of_stopping_pair_readout μ ℱ hτ hJ
      (feedbackMarkedJumpKernel lam k) (totalJumpRate_pos hlam0 hlam k) hσ
      (fun t ω ↦ feedbackEnvironmentNextCappedTime (e ω) (σ ω) t)
      (fun t ↦ feedbackEnvironmentNextCappedTime_isStoppingTime e ℱ hcount hσ t)
      (fun t ω ↦ le_feedbackEnvironmentNextCappedTime (e ω) (σ ω) t)
      (fun t ↦ ⟨S + t, fun ω ↦ (feedbackEnvironmentNextCappedTime_le (e ω) (σ ω) t).trans
        (add_le_add (hσS ω) le_rfl)⟩)
      (fun ψ t ω ↦ feedbackEnvironmentJumpCompensator lam k ψ t (e ω))
    · intro ψ
      exact (hM true (feedbackNextCurrentTest k ψ true)).add
        (hM false (feedbackNextCurrentTest k ψ false))
    · intro ψ
      exact Eventually.of_forall fun ω t ↦
        (continuousWithinAt_feedbackEnvironmentMarkedCompensator lam true
          (feedbackNextCurrentTest k ψ true) (e ω) t).add
        (continuousWithinAt_feedbackEnvironmentMarkedCompensator lam false
          (feedbackNextCurrentTest k ψ false) (e ω) t)
    · intro ψ T
      obtain ⟨Ds, hDs, hbs⟩ := exists_integrable_bound_feedbackEnvironmentMarkedCompensator
        μ ℱ e he lam hM true (feedbackNextCurrentTest k ψ true) T
      obtain ⟨Dt, hDt, hbt⟩ := exists_integrable_bound_feedbackEnvironmentMarkedCompensator
        μ ℱ e he lam hM false (feedbackNextCurrentTest k ψ false) T
      refine ⟨fun ω ↦ Ds ω + Dt ω, hDs.add hDt, ?_⟩
      filter_upwards [hbs, hbt] with ω hs ht
      intro s hst
      exact (norm_add_le _ _).trans (add_le_add (hs s hst) (ht s hst))
    · exact hA
    · exact hA0
    · intro ψ t
      filter_upwards [ae_restrict_of_ae hsimple, hk] with ω hs hω
      exact feedbackEnvironmentJumpCompensator_stopped_after hlam0 hlam (e ω) hs
        (σ ω) t k hω ψ
  exact ⟨heq, (ae_finite_and_map_eq_of_attainedFirstJumpLaw_eq
    μ[|A] hτ hJ (feedbackMarkedHoldingKernel lam k) heq).1⟩

end OTSelector.Limit
