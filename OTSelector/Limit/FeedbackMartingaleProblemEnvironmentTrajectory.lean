import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentKernel
import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentHistory
import OTSelector.Limit.FeedbackStationaryFutureHistory

/-!
# The actual chronological trajectory determined by the spatial martingale problem

At each reached event, its observed finite history is tested in the original marked-count
martingales. The resulting conditional holding kernel proves that the next event is reached.
Induction therefore gives all chronological transitions and determines the whole path law.
-/

open MeasureTheory ProbabilityTheory Set Filter Preorder
open scoped NNReal ENNReal BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit

open PointProcess

/-- Stopped-history measurability, together with the actual spatial marked martingale problem,
identifies every chronological transition and proves that every finite event index is reached.
The measurable history versions are allowed to agree only almost everywhere, so no completion
of the original filtration is implicit. -/
theorem feedbackEnvironment_futurePath_joint_steps
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
    (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
      Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
    (hobs : ∀ n, (∀ᵐ ω ∂μ, feedbackEnvironmentEventTime (e ω) n ≠ ∞) →
      ∃ X : Ω → ((i : Finset.Iic n) → FeedbackMarkedStep),
        Measurable[(feedbackEnvironmentEventTime_isStoppingTime e ℱ hcount n).measurableSpace] X ∧
        X =ᵐ[μ] (fun ω ↦ frestrictLe n (feedbackEnvironmentFuturePath (e ω)))) :
    (∀ n, ∀ᵐ ω ∂μ, feedbackEnvironmentEventTime (e ω) n ≠ ∞) ∧
    ∀ n, μ.map (fun ω ↦ (frestrictLe n (feedbackEnvironmentFuturePath (e ω)),
        feedbackEnvironmentFuturePath (e ω) (n + 1))) =
      μ.map (fun ω ↦ frestrictLe n (feedbackEnvironmentFuturePath (e ω))) ⊗ₘ
        feedbackMarkedHistoryKernel lam n := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  have hnext (n : ℕ) (hn : ∀ᵐ ω ∂μ, feedbackEnvironmentEventTime (e ω) n ≠ ∞) :
      (∀ᵐ ω ∂μ, feedbackEnvironmentEventTime (e ω) (n + 1) ≠ ∞) ∧
      μ.map (fun ω ↦ (frestrictLe n (feedbackEnvironmentFuturePath (e ω)),
        feedbackEnvironmentFuturePath (e ω) (n + 1))) =
      μ.map (fun ω ↦ frestrictLe n (feedbackEnvironmentFuturePath (e ω))) ⊗ₘ
        feedbackMarkedHistoryKernel lam n := by
    obtain ⟨X, hX, hXe⟩ := hobs n hn
    let current := fun x : (i : Finset.Iic n) → FeedbackMarkedStep ↦
      (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.2
    have hc : Measurable current := by fun_prop
    have hk : ∀ᵐ ω ∂μ, feedbackEnvironmentCurrent (e ω)
        (feedbackEnvironmentEventTime (e ω) n).toReal = current (X ω) := by
      filter_upwards [hsimple, hn, hXe] with ω hs hf hx
      rw [hx]
      exact (feedbackEnvironmentFuturePath_current (e ω) hs n hf).symm
    have hh := feedbackEnvironment_nextJump_jointLaw μ ℱ e he hlam0 hlam
      hcount hsimple hM (feedbackEnvironmentEventTime_isStoppingTime e ℱ hcount n)
      hn hX current hc hk
    refine ⟨?_, ?_⟩
    · filter_upwards [hn, hh.2] with ω hf hwait
      rw [feedbackEnvironmentEventTime_succ_eq_add (e ω) n hf]
      exact ENNReal.add_ne_top.mpr ⟨hf, hwait⟩
    · have hpair : (fun ω ↦ (X ω,
          ((feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent (e ω) n)).toReal,
            feedbackEnvironmentFirstJump (feedbackEnvironmentAfterEvent (e ω) n)))) =ᵐ[μ]
          (fun ω ↦ (frestrictLe n (feedbackEnvironmentFuturePath (e ω)),
            feedbackEnvironmentFuturePath (e ω) (n + 1))) := by
        filter_upwards [hXe, hn] with ω hx hf
        rw [hx, feedbackEnvironmentFuturePath_succ (e ω) n hf]
      calc
        _ = μ.map (fun ω ↦ (X ω,
            ((feedbackEnvironmentFirstTime (feedbackEnvironmentAfterEvent (e ω) n)).toReal,
              feedbackEnvironmentFirstJump (feedbackEnvironmentAfterEvent (e ω) n)))) :=
          (Measure.map_congr hpair).symm
        _ = μ.map X ⊗ₘ feedbackMarkedHistoryKernel lam n := hh.1
        _ = _ := by rw [Measure.map_congr hXe]
  have hfinite (n : ℕ) : ∀ᵐ ω ∂μ, feedbackEnvironmentEventTime (e ω) n ≠ ∞ := by
    induction n with
    | zero => exact Eventually.of_forall fun _ ↦ by simp
    | succ n ih => exact (hnext n ih).1
  exact ⟨hfinite, fun n ↦ (hnext n (hfinite n)).2⟩

/-- The original marked-count martingale problem determines the complete actual future path
from its initial current distribution. -/
theorem feedbackEnvironment_futurePath_law
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
    (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
      Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
    (hobs : ∀ n, (∀ᵐ ω ∂μ, feedbackEnvironmentEventTime (e ω) n ≠ ∞) →
      ∃ X : Ω → ((i : Finset.Iic n) → FeedbackMarkedStep),
        Measurable[(feedbackEnvironmentEventTime_isStoppingTime e ℱ hcount n).measurableSpace] X ∧
        X =ᵐ[μ] (fun ω ↦ frestrictLe n (feedbackEnvironmentFuturePath (e ω)))) :
    μ.map (fun ω ↦ feedbackEnvironmentFuturePath (e ω)) =
      @Kernel.trajMeasure (fun _ ↦ FeedbackMarkedStep) (fun _ ↦ inferInstance)
        ((μ.map (fun ω ↦ (e ω).path.rootCurrent)).map feedbackMarkedVirtual)
        (feedbackMarkedHistoryKernel lam) (feedbackMarkedHistoryKernel_isMarkov hlam0 hlam) := by
  let := feedbackMarkedHistoryKernel_isMarkov hlam0 hlam
  have hr : Measurable (fun ω ↦ (e ω).path.rootCurrent) :=
    FeedbackEnvironment.measurable_rootCurrent.comp he
  have hv := measurable_of_countable feedbackMarkedVirtual
  have : IsProbabilityMeasure (μ.map (fun ω ↦ (e ω).path.rootCurrent)) :=
    Measure.isProbabilityMeasure_map hr.aemeasurable
  have : IsProbabilityMeasure
      ((μ.map (fun ω ↦ (e ω).path.rootCurrent)).map feedbackMarkedVirtual) :=
    Measure.isProbabilityMeasure_map hv.aemeasurable
  apply map_path_eq_trajMeasure_of_joint_history μ
    (measurable_feedbackEnvironmentFuturePath.comp he)
    ((μ.map (fun ω ↦ (e ω).path.rootCurrent)).map feedbackMarkedVirtual)
    (feedbackMarkedHistoryKernel lam)
  · rw [Measure.map_map hv hr]
    rfl
  · exact (feedbackEnvironment_futurePath_joint_steps μ ℱ e he hlam0 hlam
      hcount hsimple hM hobs).2

end OTSelector.Limit
