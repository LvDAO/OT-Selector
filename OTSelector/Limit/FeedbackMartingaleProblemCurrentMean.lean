import OTSelector.Limit.FeedbackMartingaleProblemCurrentKernel

/-!
# The first-jump current response under the original marked martingale problem

The first holding kernel is identified by optional sampling of the actual marked compensators.
Its integral gives the exact expected first-jump approximation, for arbitrary initial current law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 600000

namespace OTSelector.Limit
open PointProcess

section OriginalMartingaleProblem
variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
  (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
  (hroot : Measurable[ℱ 0] (fun ω ↦ (e ω).path.rootCurrent))
  (htest : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ) (t : ℝ≥0),
    Measurable[ℱ t] (fun ω ↦ LocalConfiguration.firstEventTestCount
      (feedbackEnvironmentTwoColor (e ω)) b ψ t))
  (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
  (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
    Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)

include he hlam0 hlam hroot htest hsimple hM in
/-- The actual initial current and first marked holding step have their genuine joint law. -/
theorem feedbackEnvironment_firstJump_jointLaw :
    μ.map (fun ω ↦ ((e ω).path.rootCurrent,
      ((feedbackEnvironmentFirstTime (e ω)).toReal, feedbackEnvironmentFirstJump (e ω)))) =
      (μ.map (fun ω ↦ (e ω).path.rootCurrent)) ⊗ₘ feedbackMarkedHoldingKernel lam ∧
    ∀ᵐ ω ∂μ, feedbackEnvironmentFirstTime (e ω) ≠ ∞ := by
  have hσ : IsStoppingTime ℱ (fun _ : Ω ↦ ((0 : ℝ≥0) : WithTop ℝ≥0)) := isStoppingTime_const ℱ 0
  have hX : Measurable[hσ.measurableSpace] (fun ω ↦ (e ω).path.rootCurrent) := by
    rw [IsStoppingTime.measurableSpace_const]
    exact hroot
  have hh := feedbackEnvironment_nextJump_jointLaw μ ℱ e he hlam0 hlam
    (feedbackEnvironmentEventCount_adapted_of_tests e ℱ htest) hsimple hM
    (σ := fun _ : Ω ↦ (0 : ℝ≥0∞)) hσ
    (Eventually.of_forall fun _ ↦ ENNReal.zero_ne_top) hX id measurable_id
    (Eventually.of_forall fun ω ↦ by simp [feedbackEnvironmentCurrent, FeedbackEnvironment.currentIncrement, LocalConfiguration.orientedCount])
  simpa only [ENNReal.toReal_zero, FeedbackEnvironment.reroot_zero, Kernel.comap_id] using hh

include he hlam0 hlam hroot htest hsimple hM in
/-- Exact first-jump expectation, with the initial current law left arbitrary. -/
theorem integral_feedbackFirstCurrentIndicator_sub_initial (k : ℤ) (t : ℝ≥0) :
    (∫ ω, (feedbackFirstCurrentIndicator k t (e ω) -
      feedbackCurrentIndicator k (e ω).path.rootCurrent) ∂μ) =
    ∫ j, ((1 - Real.exp (-totalJumpRate lam j * (t : ℝ))) / totalJumpRate lam j) *
      feedbackCurrentIndicatorGenerator lam k j ∂(μ.map (fun ω ↦ (e ω).path.rootCurrent)) := by
  let ρ := μ.map (fun ω ↦ (e ω).path.rootCurrent)
  let f : ℤ × FeedbackMarkedStep → ℝ := fun p ↦
    if p.2.1 ≤ (t : ℝ) then feedbackCurrentIndicator k p.2.2.2 -
      feedbackCurrentIndicator k p.1 else 0
  have hf : Measurable f :=
    (((measurable_of_countable (feedbackCurrentIndicator k)).comp measurable_snd.snd.snd).sub
      ((measurable_of_countable (feedbackCurrentIndicator k)).comp measurable_fst)).ite
      (measurableSet_le measurable_snd.fst measurable_const) measurable_const
  let := feedbackMarkedHoldingKernel_isMarkov hlam0 hlam
  have hρ : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map
    (FeedbackEnvironment.measurable_rootCurrent.comp he).aemeasurable
  have hfint : Integrable f (ρ ⊗ₘ feedbackMarkedHoldingKernel lam) :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall fun p ↦ by
      dsimp [f]
      split_ifs
      · exact norm_feedbackCurrentIndicator_sub_le_one _ _ _
      · simp)
  obtain ⟨hlaw, hfinite⟩ := feedbackEnvironment_firstJump_jointLaw μ ℱ e he hlam0 hlam
    hroot htest hsimple hM
  have hread : Measurable (fun ω ↦ ((e ω).path.rootCurrent,
      ((feedbackEnvironmentFirstTime (e ω)).toReal, feedbackEnvironmentFirstJump (e ω)))) :=
    (FeedbackEnvironment.measurable_rootCurrent.comp he).prodMk
      ((measurable_feedbackEnvironmentFirstTime.comp he).ennreal_toReal.prodMk
        (measurable_feedbackEnvironmentFirstJump.comp he))
  calc
    _ = ∫ ω, f ((e ω).path.rootCurrent,
        ((feedbackEnvironmentFirstTime (e ω)).toReal, feedbackEnvironmentFirstJump (e ω))) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hfinite] with ω hω
      have hc : (feedbackEnvironmentFirstTime (e ω)).toReal ≤ (t : ℝ) ↔
          feedbackEnvironmentFirstTime (e ω) ≤ (t : ℝ≥0∞) := by
        rw [← ENNReal.coe_toReal t]
        exact ENNReal.toReal_le_toReal hω ENNReal.coe_ne_top
      dsimp [f, feedbackFirstCurrentIndicator]
      by_cases hh : feedbackEnvironmentFirstTime (e ω) ≤ (t : ℝ≥0∞)
      · simp only [hh, hc.mpr hh, ite_true]
      · simp only [hh, not_congr hc |>.mpr hh, ite_false, sub_self]
    _ = ∫ p, f p ∂(μ.map (fun ω ↦ ((e ω).path.rootCurrent,
        ((feedbackEnvironmentFirstTime (e ω)).toReal, feedbackEnvironmentFirstJump (e ω))))) :=
      (integral_map hread.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ p, f p ∂(ρ ⊗ₘ feedbackMarkedHoldingKernel lam) := by rw [hlaw]
    _ = ∫ j, ∫ z, f (j, z) ∂feedbackMarkedHoldingKernel lam j ∂ρ :=
      Measure.integral_compProd hfint
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun j ↦
        integral_feedbackMarkedHoldingKernel_currentIndicator hlam0 hlam k j t t.property

end OriginalMartingaleProblem
end OTSelector.Limit
