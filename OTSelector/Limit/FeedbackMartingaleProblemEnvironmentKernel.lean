import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentLocalization
import OTSelector.Limit.FeedbackMartingaleProblemHistoryKernel

/-!
# The actual transition kernel conditional on an observed stopped history

Every measurable observation of the stopped past has a next-jump conditional law depending
only on its present current. The proof uses the original marked-count martingale equations,
optional sampling, localization and a countable partition over current values.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 400000

namespace OTSelector.Limit

open PointProcess

/-- The actual next marked jump has the feedback holding kernel given any observation of
the stopped history that determines the present current. No conditional Markov assertion or
finiteness of the next event is assumed. -/
theorem feedbackEnvironment_nextJump_jointLaw
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
    (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
      Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
    {σ : Ω → ℝ≥0∞} (hσ : IsStoppingTime ℱ σ) (hfinite : ∀ᵐ ω ∂μ, σ ω ≠ ∞)
    {X : Ω → H} (hX : Measurable[hσ.measurableSpace] X)
    (current : H → ℤ) (hc : Measurable current)
    (hcurrent : ∀ᵐ ω ∂μ, feedbackEnvironmentCurrent (e ω) (σ ω).toReal = current (X ω)) :
    μ.map (fun ω ↦ (X ω,
      ((feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot (σ ω).toReal (e ω))).toReal,
        feedbackEnvironmentFirstJump (FeedbackEnvironment.reroot (σ ω).toReal (e ω))))) =
      μ.map X ⊗ₘ (feedbackMarkedHoldingKernel lam).comap current hc ∧
    ∀ᵐ ω ∂μ,
      feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot (σ ω).toReal (e ω)) ≠ ∞ := by
  let := feedbackMarkedHoldingKernel_isMarkov hlam0 hlam
  have hXm : Measurable X := hX.mono hσ.measurableSpace_le le_rfl
  let τ := fun ω ↦ feedbackEnvironmentFirstTime
    (FeedbackEnvironment.reroot (σ ω).toReal (e ω))
  let J := fun ω ↦ feedbackEnvironmentFirstJump
    (FeedbackEnvironment.reroot (σ ω).toReal (e ω))
  have hr : Measurable (fun ω ↦ FeedbackEnvironment.reroot (σ ω).toReal (e ω)) :=
    FeedbackEnvironment.measurable_uncurry_reroot.comp
      (f := fun ω ↦ ((σ ω).toReal, e ω)) (hσ.measurable'.ennreal_toReal.prodMk he)
  have hτ : Measurable τ := measurable_feedbackEnvironmentFirstTime.comp hr
  have hJ : Measurable J := measurable_feedbackEnvironmentFirstJump.comp hr
  have hlocal (A : Set H) (hA : MeasurableSet A) (k : ℤ)
      (hk : ∀ x ∈ A, current x = k) (hA0 : μ (X ⁻¹' A) ≠ 0) :
      (μ[|X ⁻¹' A]).map (fun ω ↦ ((τ ω).toReal, J ω)) = feedbackMarkedHoldingKernel lam k ∧
      ∀ᵐ ω ∂μ[|X ⁻¹' A], τ ω ≠ ∞ := by
    apply feedbackEnvironment_nextJumpLaw_cond_eq_of_stopping μ ℱ e he hlam0 hlam
      hcount hsimple hM hσ (hX hA) hA0 (ae_restrict_of_ae hfinite) k
    filter_upwards [ae_restrict_of_ae hcurrent, ae_restrict_mem (hXm hA)] with ω hω hmem
    exact hω.trans (hk (X ω) hmem)
  refine ⟨map_history_next_eq_compProd_of_cond_laws μ hXm
    (hτ.ennreal_toReal.prodMk hJ) current hc (feedbackMarkedHoldingKernel lam)
      (fun A hA k hk hA0 ↦ (hlocal A hA k hk hA0).1), ?_⟩
  let Ak : ℤ → Set H := fun k ↦ current ⁻¹' {k}
  have hAk (k : ℤ) : MeasurableSet (Ak k) := hc (measurableSet_singleton k)
  have hall (k : ℤ) : ∀ᵐ ω ∂μ.restrict (X ⁻¹' Ak k), τ ω ≠ ∞ := by
    by_cases hz : μ (X ⁻¹' Ak k) = 0
    · simp [Measure.restrict_eq_zero.mpr hz]
    · exact (Measure.ae_ennreal_smul_measure_iff
        (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))).mp
        (hlocal (Ak k) (hAk k) k (fun _ hx ↦ hx) hz).2
  have hu : (⋃ k, X ⁻¹' Ak k) = univ := by
    ext ω
    simp [Ak]
  have hh := (ae_restrict_iUnion_iff (fun k ↦ X ⁻¹' Ak k) _).mpr hall
  simpa only [hu, Measure.restrict_univ] using hh

end OTSelector.Limit
