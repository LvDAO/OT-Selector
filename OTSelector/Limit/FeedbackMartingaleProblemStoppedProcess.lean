import OTSelector.Limit.FeedbackMartingaleProblemStoppingPair
import OTSelector.Feedback.FeedbackI3ConditionalGap
import OTSelector.Probability.CountingProcess.RectangleExtension

/-!
# Stopping a right-continuous continuous-time martingale

Right grids give the genuine stopped-process adaptedness. The two-stopping-time expectation
theorem then gives its martingale equations, using a local integrable envelope.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace OTSelector.Limit

open CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}

private theorem stronglyMeasurable_finite_stop_le
    (hM : StronglyAdapted ℱ M) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0))
    (hfinite : (range σ).Finite) {T : ℝ≥0} (hle : ∀ ω, σ ω ≤ T) :
    StronglyMeasurable[ℱ T] (fun ω ↦ M (σ ω) ω) := by
  classical
  let S := hfinite.toFinset
  have hsum : StronglyMeasurable[ℱ T]
      (∑ s ∈ S, {ω | σ ω = s}.indicator (M s)) := by
    apply Finset.stronglyMeasurable_sum
    intro s hs
    have hsmem : s ∈ range σ := hfinite.mem_toFinset.mp hs
    obtain ⟨ω, rfl⟩ := hsmem
    have he : MeasurableSet[ℱ (σ ω)] {v | σ v = σ ω} := by
      convert hσ.measurableSet_eq (σ ω) using 1
      ext v
      exact WithTop.coe_eq_coe.symm
    exact ((hM (σ ω)).mono (ℱ.mono (hle ω))).indicator (ℱ.mono (hle ω) _ he)
  have heq : (∑ s ∈ S, {ω | σ ω = s}.indicator (M s)) = fun ω ↦ M (σ ω) ω := by
    funext ω
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single_of_mem (σ ω) (by simp [S])]
    · simp
    · intro s _ hs
      simp [Ne.symm hs]
  rw [← heq]
  exact hsum

/-- Right-continuous adapted real paths remain adapted when stopped at an arbitrary stopping
time. The proof uses finite right grids clipped at the current observation time. -/
theorem stronglyAdapted_cappedStoppingValue_of_rightContinuous
    (hM : StronglyAdapted ℱ M) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (hRight : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t) :
    StronglyAdapted ℱ (fun t ω ↦ M (cappedStoppingValue t τ ω) ω) := by
  intro t
  let c := cappedStoppingValue t τ
  have hc := cappedStoppingValue_isStoppingTime ℱ hτ t
  let cgrid : ℕ → Ω → ℝ≥0 := fun n ω ↦ min (rightGrid (n + 1) (c ω)) t
  have hgstop (n : ℕ) : IsStoppingTime ℱ fun ω ↦ (cgrid n ω : WithTop ℝ≥0) := by
    simpa only [cgrid, WithTop.coe_min] using
      (IsStoppingTime.rightGridApprox hc (n + 1) (by omega)).min_const t
  have hgfinite (n : ℕ) : (range (cgrid n)).Finite := by
    have h := (finiteRange_rightGrid_of_le (n + 1) (by omega)
      (cappedStoppingValue_le t τ)).image (fun u : ℝ≥0 ↦ min u t)
    exact h.subset (by rintro _ ⟨ω, rfl⟩; exact ⟨_, ⟨ω, rfl⟩, rfl⟩)
  apply stronglyMeasurable_of_tendsto atTop
    (fun n ↦ stronglyMeasurable_finite_stop_le hM (hgstop n) (hgfinite n)
      (fun _ ↦ min_le_right _ _))
  apply tendsto_pi_nhds.mpr
  intro ω
  apply (hRight ω (c ω)).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
  · have h := (tendsto_rightGrid_succ (c ω)).min (tendsto_const_nhds (x := t))
    have hct : c ω ≤ t := cappedStoppingValue_le t τ ω
    simpa only [min_eq_left hct] using h
  · exact le_min (le_rightGrid (n + 1) (c ω) (by omega)) (cappedStoppingValue_le t τ ω)

/-- An arbitrary stopping time preserves the martingale property for right-continuous real
paths with an integrable envelope on every finite horizon. -/
theorem martingale_cappedStoppingValue_of_rightContinuous
    {μ : Measure Ω} [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (hRight : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    (hEnvelope : ∀ T : ℝ≥0, ∃ D : Ω → ℝ, Integrable D μ ∧
      ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M s ω‖ ≤ D ω) :
    Martingale (fun t ω ↦ M (cappedStoppingValue t τ ω) ω) ℱ μ := by
  have hadapt := stronglyAdapted_cappedStoppingValue_of_rightContinuous
    hM.stronglyAdapted hτ hRight
  have hint (t : ℝ≥0) : Integrable (fun ω ↦ M (cappedStoppingValue t τ ω) ω) μ := by
    obtain ⟨D, hD, hb⟩ := hEnvelope t
    apply hD.mono' ((hadapt t).mono (ℱ.le t)).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    exact hω _ ((cappedStoppingValue_le t τ ω).trans (by simp))
  apply martingale_of_all_setIntegral_eq_of_isFiniteMeasure hadapt hint
  intro s t hst A hA
  let ρ : Ω → ℝ≥0 := fun ω ↦ max (cappedStoppingValue t τ ω) s
  have hρ : IsStoppingTime ℱ fun ω ↦ (ρ ω : WithTop ℝ≥0) := by
    simpa only [ρ, WithTop.coe_max] using
      (cappedStoppingValue_isStoppingTime ℱ hτ t).max_const s
  have hA' : MeasurableSet[(isStoppingTime_const ℱ s).measurableSpace] A := by
    rw [IsStoppingTime.measurableSpace_const]
    exact hA
  obtain ⟨D, hD, hb⟩ := hEnvelope t
  have he := setIntegral_martingale_stopping_pair_of_integrable_bound hM
    (isStoppingTime_const ℱ s) hρ (fun ω ↦ le_max_right _ _)
    (fun ω ↦ max_le (cappedStoppingValue_le t τ ω) hst)
    (Eventually.of_forall hRight) hD hb hA'
  have hpath (ω : Ω) : M (ρ ω) ω =
      M (cappedStoppingValue t τ ω) ω + M s ω - M (cappedStoppingValue s τ ω) ω := by
    by_cases h : τ ω ≤ (s : WithTop ℝ≥0)
    · have hct : (cappedStoppingValue t τ ω : WithTop ℝ≥0) = τ ω := by
        rw [coe_cappedStoppingValue, min_eq_left (h.trans (by exact_mod_cast hst))]
      have hcs : (cappedStoppingValue s τ ω : WithTop ℝ≥0) = τ ω := by
        rw [coe_cappedStoppingValue, min_eq_left h]
      have heq : cappedStoppingValue s τ ω = cappedStoppingValue t τ ω :=
        WithTop.coe_injective (hcs.trans hct.symm)
      have hle : cappedStoppingValue t τ ω ≤ s := by exact_mod_cast hct ▸ h
      simp only [ρ, max_eq_right hle, heq]
      ring
    · have hle : (s : WithTop ℝ≥0) ≤ τ ω := le_of_not_ge h
      have hcs : cappedStoppingValue s τ ω = s := by
        apply WithTop.coe_injective
        rw [coe_cappedStoppingValue, min_eq_right hle]
      have hct : s ≤ cappedStoppingValue t τ ω := by
        apply WithTop.coe_le_coe.mp
        rw [coe_cappedStoppingValue]
        exact le_min hle (by exact_mod_cast hst)
      simp only [ρ, max_eq_left hct, hcs, add_sub_cancel_right]
  simp_rw [hpath] at he
  have hadd : Integrable (fun ω ↦ M (cappedStoppingValue t τ ω) ω + M s ω)
      (μ.restrict A) := (hint t).integrableOn.add (hM.integrable s).integrableOn
  rw [integral_sub hadd (hint s).integrableOn,
    integral_add (hint t).integrableOn (hM.integrable s).integrableOn] at he
  linarith

omit [MeasurableSpace Ω] in
/-- Mathlib's stopped process agrees exactly with the existing finite capped stopping value. -/
theorem stoppedProcess_eq_cappedStoppingValue (M : ℝ≥0 → Ω → ℝ)
    (τ : Ω → WithTop ℝ≥0) :
    stoppedProcess M τ = fun t ω ↦ M (cappedStoppingValue t τ ω) ω := by
  funext t ω
  unfold stoppedProcess
  apply congrArg (fun s ↦ M s ω)
  have hne : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne, WithTop.untop_eq_iff hne,
    coe_cappedStoppingValue, min_comm]

/-- Right-continuous real martingales with local integrable envelopes remain martingales under
arbitrary continuous-time stopping, in mathlib's `stoppedProcess` notation. -/
theorem martingale_stoppedProcess_of_rightContinuous
    {μ : Measure Ω} [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (hRight : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    (hEnvelope : ∀ T : ℝ≥0, ∃ D : Ω → ℝ, Integrable D μ ∧
      ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M s ω‖ ≤ D ω) :
    Martingale (stoppedProcess M τ) ℱ μ := by
  rw [stoppedProcess_eq_cappedStoppingValue]
  exact martingale_cappedStoppingValue_of_rightContinuous hM hτ hRight hEnvelope

/-- Deterministic local bounds suffice for stopping a right-continuous real martingale. -/
theorem martingale_stoppedProcess_of_rightContinuous_bounded
    {μ : Measure Ω} [IsFiniteMeasure μ] (hM : Martingale M ℱ μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (hRight : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    (hBound : ∀ T : ℝ≥0, ∃ C : ℝ, ∀ ω s, s ≤ T → ‖M s ω‖ ≤ C) :
    Martingale (stoppedProcess M τ) ℱ μ := by
  apply martingale_stoppedProcess_of_rightContinuous hM hτ hRight
  intro T
  obtain ⟨C, hC⟩ := hBound (T + 1)
  exact ⟨fun _ ↦ C, integrable_const C, Eventually.of_forall hC⟩

end OTSelector.Limit
