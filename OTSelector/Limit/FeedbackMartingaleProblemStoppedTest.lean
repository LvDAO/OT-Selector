import OTSelector.Limit.FeedbackMartingaleProblemFirstTest
import OTSelector.Limit.FeedbackMartingaleProblemConditioning
import OTSelector.Feedback.FeedbackI3ConditionalGap

/-!
# First-jump laws from stopping the original marked-count martingales

Only the original continuous-test martingales are assumed. Their bounded stopped readout is
the first-jump test compensator, a pathwise identity supplied by first-event geometry. Initial
history events are conditioned using actual normalized restrictions.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BoundedContinuousFunction

namespace OTSelector.Limit

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [TopologicalSpace E] [HasOuterApproxClosed E] [BorelSpace E]

/-- The occupation time before the first jump is exactly the existing capped stopping value. -/
theorem integral_firstJump_survival_eq_cappedStoppingValue (a : ℝ≥0∞) (t : ℝ≥0) :
    (∫ s in 0..(t : ℝ), if ENNReal.ofReal s < a then (1 : ℝ) else 0) =
      (CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ a) () : ℝ) := by
  by_cases ha : a = ∞
  · have hc : CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ a) () = t := by
      apply ENNReal.coe_injective
      have he := CountingProcess.coe_cappedStoppingValue t (fun _ : Unit ↦ a) ()
      change (CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ a) () : ℝ≥0∞) =
        min a (t : ℝ≥0∞) at he
      exact he.trans (by simp [ha])
    rw [hc]
    simp [ha]
  lift a to ℝ≥0 using ha with a
  have hcap : (CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ (a : ℝ≥0∞)) () : ℝ) =
      min (a : ℝ) t := by
    have hc : CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ (a : ℝ≥0∞)) () =
        min a t := by
      apply ENNReal.coe_injective
      have he := CountingProcess.coe_cappedStoppingValue t (fun _ : Unit ↦ (a : ℝ≥0∞)) ()
      change (CountingProcess.cappedStoppingValue t (fun _ : Unit ↦ (a : ℝ≥0∞)) () : ℝ≥0∞) =
        min (a : ℝ≥0∞) t at he
      exact he.trans (ENNReal.coe_min a t).symm
    rw [hc]
    exact NNReal.coe_min _ _
  rw [hcap]
  calc
    _ = ∫ s in 0..(t : ℝ), {s : ℝ | s ≤ min (a : ℝ) t}.indicator (fun _ ↦ (1 : ℝ)) s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Iio_ae_eq_Iic (μ := (volume : Measure ℝ)) (a := (a : ℝ))] with s hs
      intro hst
      have hst' : 0 < s ∧ s ≤ (t : ℝ) := by simpa only [uIoc_of_le (show (0 : ℝ) ≤ t from t.property), mem_Ioc] using hst
      have he : ENNReal.ofReal s < (a : ℝ≥0∞) ↔ s ≤ min (a : ℝ) t := by
        rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hst'.1.le]
        have hs' : s < (a : ℝ) ↔ s ≤ (a : ℝ) := by exact Iff.of_eq hs
        rw [hs', le_min_iff]
        exact iff_self_and.mpr (fun _ ↦ hst'.2)
      simp [Set.indicator_apply, he]
    _ = min (a : ℝ) t := by
      have hcut := intervalIntegral.integral_indicator (μ := (volume : Measure ℝ))
        (f := fun _ : ℝ ↦ (1 : ℝ))
        (show min (a : ℝ) t ∈ Icc 0 (t : ℝ) from
          ⟨le_min a.property t.property, min_le_right _ _⟩)
      simpa using hcut

/-- A stopped readout need only hold on the initial history event being conditioned upon.
This permits the root current to be fixed by that event. -/
theorem attainedFirstJumpLaw_cond_eq_of_local_stopped_test_readout
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {τ : Ω → ℝ≥0∞} {J : Ω → E} (hτ : Measurable τ) (hJ : Measurable J)
    (hstop : IsStoppingTime ℱ τ)
    (π : Measure E) [IsProbabilityMeasure π] {r : ℝ} (hr : 0 < r)
    (M : (E →ᵇ ℝ) → ℝ≥0 → Ω → ℝ)
    (hM : ∀ ψ, Martingale (M ψ) ℱ μ)
    (hzero : ∀ ψ, M ψ 0 =ᵐ[μ] 0)
    (hRight : ∀ ψ, ∀ᵐ ω ∂μ, ∀ t,
      ContinuousWithinAt (fun s ↦ M ψ s ω) (Ici t) t)
    (hEnvelope : ∀ ψ T, ∃ D : Ω → ℝ, Integrable D μ ∧
      ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M ψ s ω‖ ≤ D ω)
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) (hA0 : μ A ≠ 0)
    (hreadout : ∀ ψ t, (fun ω ↦ M ψ (CountingProcess.cappedStoppingValue t τ ω) ω)
      =ᵐ[μ.restrict A] firstJumpTestCompensator r π τ J ψ t) :
    attainedFirstJumpLaw μ[|A] τ J = (expMeasure r).prod π := by
  let := cond_isProbabilityMeasure (μ := μ) hA0
  apply attainedFirstJumpLaw_eq_of_continuous_zero_mean μ[|A] hτ hJ π hr
  intro ψ t
  obtain ⟨D, hD, hbound⟩ := hEnvelope ψ t
  have hi := integral_cond_martingale_stopping_initial (hM ψ) hA
    (CountingProcess.cappedStoppingValue_isStoppingTime ℱ hstop t)
    (CountingProcess.cappedStoppingValue_le t τ) (hRight ψ) hD hbound
  have hread : (fun ω ↦ M ψ (CountingProcess.cappedStoppingValue t τ ω) ω)
      =ᵐ[μ[|A]] firstJumpTestCompensator r π τ J ψ t :=
    Measure.ae_smul_measure (hreadout ψ t) _
  have hz : M ψ 0 =ᵐ[μ[|A]] 0 :=
    Measure.ae_smul_measure (ae_restrict_of_ae (hzero ψ)) _
  rw [integral_congr_ae hread, integral_congr_ae hz] at hi
  simpa using hi

/-- Stopping the original marked-count martingales and conditioning on an initial history event
identifies the attained first waiting time and mark. The readout premise is an almost-everywhere
path identity, not a martingale or a distributional identification of the first jump. -/
theorem attainedFirstJumpLaw_cond_eq_of_stopped_test_readout
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {τ : Ω → ℝ≥0∞} {J : Ω → E} (hτ : Measurable τ) (hJ : Measurable J)
    (hstop : IsStoppingTime ℱ τ)
    (π : Measure E) [IsProbabilityMeasure π] {r : ℝ} (hr : 0 < r)
    (M : (E →ᵇ ℝ) → ℝ≥0 → Ω → ℝ)
    (hM : ∀ ψ, Martingale (M ψ) ℱ μ)
    (hzero : ∀ ψ, M ψ 0 =ᵐ[μ] 0)
    (hRight : ∀ ψ, ∀ᵐ ω ∂μ, ∀ t,
      ContinuousWithinAt (fun s ↦ M ψ s ω) (Ici t) t)
    (hEnvelope : ∀ ψ T, ∃ D : Ω → ℝ, Integrable D μ ∧
      ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M ψ s ω‖ ≤ D ω)
    (hreadout : ∀ ψ t, (fun ω ↦ M ψ (CountingProcess.cappedStoppingValue t τ ω) ω)
      =ᵐ[μ] firstJumpTestCompensator r π τ J ψ t)
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) (hA0 : μ A ≠ 0) :
    attainedFirstJumpLaw μ[|A] τ J = (expMeasure r).prod π := by
  apply attainedFirstJumpLaw_cond_eq_of_local_stopped_test_readout μ ℱ hτ hJ hstop π hr
    M hM hzero hRight hEnvelope hA hA0
  intro ψ t
  exact ae_restrict_of_ae (hreadout ψ t)

end OTSelector.Limit
