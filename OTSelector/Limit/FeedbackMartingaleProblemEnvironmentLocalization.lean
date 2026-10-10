import OTSelector.Limit.FeedbackMartingaleProblemEnvironmentRestart
import OTSelector.Limit.FeedbackMartingaleProblemLocalization

/-!
# The actual jump kernel after an arbitrary finite stopping coordinate

The stopped-history event is exhausted by its intersections with `{σ ≤ n}`. On each piece
optional sampling applies at the bounded cut `σ ∧ n`; continuity from below then identifies
the same next-jump law on the original history event.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BoundedContinuousFunction

set_option synthInstance.maxSize 2048
set_option maxHeartbeats 800000

namespace OTSelector.Limit

open PointProcess CountingProcess

private theorem cappedStoppingValue_toReal_eq_of_le {Ω : Type*}
    (σ : Ω → ℝ≥0∞) (T : ℝ≥0) (ω : Ω) (h : σ ω ≤ (T : ℝ≥0∞)) :
    (cappedStoppingValue T σ ω : ℝ) = (σ ω).toReal := by
  have hc : (cappedStoppingValue T σ ω : ℝ≥0∞) = σ ω :=
    (coe_cappedStoppingValue T σ ω).trans (min_eq_left h)
  exact_mod_cast congrArg ENNReal.toReal hc

/-- The original marked-count martingale problem determines the next actual marked jump
on every observed history event at which the stopping coordinate is finite and its current
is fixed. Finiteness of the next wait is a conclusion. -/
theorem feedbackEnvironment_nextJumpLaw_cond_eq_of_stopping
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : Ω → FeedbackEnvironment)
    (he : Measurable e) {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (hcount : ∀ t : ℝ≥0, Measurable[ℱ t] (fun ω ↦
      LocalConfiguration.spatialCount (e ω).source 0 t +
        LocalConfiguration.spatialCount (e ω).target 0 t))
    (hsimple : ∀ᵐ ω ∂μ, LocalConfiguration.IsTimeSimple (feedbackEnvironmentTwoColor (e ω)))
    (hM : ∀ (b : Bool) (ψ : UnitMark →ᵇ ℝ),
      Martingale (fun t ω ↦ feedbackEnvironmentMarkedCompensator lam b ψ t (e ω)) ℱ μ)
    {σ : Ω → ℝ≥0∞} (hσ : IsStoppingTime ℱ σ)
    {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) (hA0 : μ A ≠ 0)
    (hfinite : ∀ᵐ ω ∂μ.restrict A, σ ω ≠ ∞)
    (k : ℤ) (hk : ∀ᵐ ω ∂μ.restrict A,
      feedbackEnvironmentCurrent (e ω) (σ ω).toReal = k) :
    (μ[|A]).map (fun ω ↦
      ((feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot (σ ω).toReal (e ω))).toReal,
        feedbackEnvironmentFirstJump (FeedbackEnvironment.reroot (σ ω).toReal (e ω)))) =
      feedbackMarkedHoldingKernel lam k ∧
    ∀ᵐ ω ∂μ[|A],
      feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot (σ ω).toReal (e ω)) ≠ ∞ := by
  let := feedbackMarkedHoldingKernel_isMarkov hlam0 hlam
  let τ := fun ω ↦ feedbackEnvironmentFirstTime
    (FeedbackEnvironment.reroot (σ ω).toReal (e ω))
  let J := fun ω ↦ feedbackEnvironmentFirstJump
    (FeedbackEnvironment.reroot (σ ω).toReal (e ω))
  have hreroot : Measurable (fun ω ↦ FeedbackEnvironment.reroot (σ ω).toReal (e ω)) :=
    FeedbackEnvironment.measurable_uncurry_reroot.comp
      (f := fun ω ↦ ((σ ω).toReal, e ω)) (hσ.measurable'.ennreal_toReal.prodMk he)
  have hτ : Measurable τ := measurable_feedbackEnvironmentFirstTime.comp hreroot
  have hJ : Measurable J := measurable_feedbackEnvironmentFirstJump.comp hreroot
  have hAm : MeasurableSet A := hσ.measurableSpace_le A hA
  let An : ℕ → Set Ω := fun n ↦ A ∩ {ω | σ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)}
  have hAn (n : ℕ) : MeasurableSet (An n) :=
    hAm.inter (ℱ.le (n : ℝ≥0) _ (hσ (n : ℝ≥0)))
  have hmono : Monotone An := by
    intro n m hnm ω hω
    change ω ∈ A ∧ σ ω ≤ ((n : ℝ≥0) : ℝ≥0∞) at hω
    change ω ∈ A ∧ σ ω ≤ ((m : ℝ≥0) : ℝ≥0∞)
    exact ⟨hω.1, hω.2.trans (by exact_mod_cast hnm)⟩
  have hcover : A =ᵐ[μ] ⋃ n, An n := by
    filter_upwards [(ae_restrict_iff' hAm).mp hfinite] with ω hω
    apply propext
    constructor
    · intro hωA
      obtain ⟨n, hn⟩ := exists_nat_gt (σ ω).toReal
      refine mem_iUnion.mpr ⟨n, hωA, ?_⟩
      change σ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)
      rw [← ENNReal.ofReal_toReal (hω hωA)]
      simpa using ENNReal.ofReal_le_ofReal hn.le
    · intro hωU
      obtain ⟨n, hn⟩ := mem_iUnion.mp hωU
      exact hn.1
  have hpiece (n : ℕ) (hn : μ (An n) ≠ 0) :
      (μ[|An n]).map (fun ω ↦ ((τ ω).toReal, J ω)) = feedbackMarkedHoldingKernel lam k ∧
      ∀ᵐ ω ∂μ[|An n], τ ω ≠ ∞ := by
    let σn := cappedStoppingValue (n : ℝ≥0) σ
    have hσn := cappedStoppingValue_isStoppingTime ℱ hσ (n : ℝ≥0)
    have hAnStop : MeasurableSet[hσn.measurableSpace] (An n) := by
      have hstop := hσ.measurableSet_inter_le (isStoppingTime_const ℱ (n : ℝ≥0)) A hA
      rw [IsStoppingTime.measurableSet] at hstop ⊢
      refine ⟨hstop.1, fun i ↦ ?_⟩
      convert hstop.2 i using 1
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      have hc : (cappedStoppingValue (n : ℝ≥0) σ ω : WithTop ℝ≥0) =
          min (σ ω) ((n : ℝ≥0) : WithTop ℝ≥0) :=
        coe_cappedStoppingValue (n : ℝ≥0) σ ω
      erw [hc]
      rfl
    have hcut (ω : Ω) (hω : ω ∈ An n) : (σn ω : ℝ) = (σ ω).toReal :=
      cappedStoppingValue_toReal_eq_of_le σ n ω hω.2
    have hkernel := feedbackEnvironment_nextJumpLaw_cond_eq_of_bounded_stopping
      μ ℱ e he hlam0 hlam hcount hsimple hM hσn
      (fun ω ↦ cappedStoppingValue_le (n : ℝ≥0) σ ω) hAnStop hn k
      (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hk,
          ae_restrict_mem (hAn n)] with ω hω hmem
        rw [hcut ω hmem]
        exact hω)
    let := cond_isProbabilityMeasure (μ := μ) hn
    have hσnm : Measurable (fun ω ↦ (σn ω : ℝ)) := by
      simpa using hσn.measurable'.ennreal_toReal
    have hrn := FeedbackEnvironment.measurable_uncurry_reroot.comp
      (f := fun ω ↦ ((σn ω : ℝ), e ω)) (hσnm.prodMk he)
    have hfull := ae_finite_and_map_eq_of_attainedFirstJumpLaw_eq μ[|An n]
      (measurable_feedbackEnvironmentFirstTime.comp hrn)
      (measurable_feedbackEnvironmentFirstJump.comp hrn)
      (feedbackMarkedHoldingKernel lam k) hkernel.1
    have hread : (fun ω ↦
        ((feedbackEnvironmentFirstTime (FeedbackEnvironment.reroot (σn ω) (e ω))).toReal,
          feedbackEnvironmentFirstJump (FeedbackEnvironment.reroot (σn ω) (e ω))))
        =ᵐ[μ[|An n]] (fun ω ↦ ((τ ω).toReal, J ω)) := by
      filter_upwards [ae_cond_mem (hAn n)] with ω hω
      simp only [τ, J, hcut ω hω]
    refine ⟨(Measure.map_congr hread).symm.trans hfull.2, ?_⟩
    filter_upwards [hfull.1, ae_cond_mem (hAn n)] with ω hf hω
    simpa only [Function.comp_apply, τ, hcut ω hω] using hf
  refine ⟨map_cond_eq_of_monotone_localization μ (hτ.ennreal_toReal.prodMk hJ)
    (feedbackMarkedHoldingKernel lam k) hAm hA0 An hAn hmono hcover
      (fun n hn ↦ (hpiece n hn).1), ?_⟩
  have hrestrict : ∀ᵐ ω ∂μ.restrict (⋃ n, An n), τ ω ≠ ∞ := by
    apply (ae_restrict_iUnion_iff _ _).mpr
    intro n
    by_cases hn : μ (An n) = 0
    · simp [Measure.restrict_eq_zero.mpr hn]
    · exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))).mp (hpiece n hn).2
  have hrestrictA : ∀ᵐ ω ∂μ.restrict A, τ ω ≠ ∞ := by
    rw [Measure.restrict_congr_set hcover]
    exact hrestrict
  exact Measure.ae_smul_measure hrestrictA _

end OTSelector.Limit
