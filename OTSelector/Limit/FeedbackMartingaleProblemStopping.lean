import OTSelector.Probability.CountingProcess.RightGridStopping
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded continuous-time optional sampling by finite right grids

Right continuity and a deterministic bound allow finite-grid optional sampling to pass to an
arbitrary bounded stopping coordinate. This supplies the stopping step in the feedback
first-jump martingale problem without a countable-range assumption.
-/

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace OTSelector.Limit

/-- Bounded optional stopping in continuous time, obtained from finite right grids.
The integrable envelope and right continuity only need to hold outside one null set. -/
theorem integral_martingale_stopping_of_integrable_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℝ≥0))
    (hτT : ∀ ω, τ ω ≤ T)
    (hRight : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    {D : Ω → ℝ} (hD : Integrable D μ)
    (hBound : ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M s ω‖ ≤ D ω) :
    ∫ ω, M (τ ω) ω ∂μ = ∫ ω, M 0 ω ∂μ := by
  let τn : ℕ → Ω → ℝ≥0 := fun n ω ↦ CountingProcess.rightGrid (n + 1) (τ ω)
  have hstop (n : ℕ) : IsStoppingTime ℱ fun ω ↦ (τn n ω : WithTop ℝ≥0) :=
    CountingProcess.IsStoppingTime.rightGridApprox hτ (n + 1) (by omega)
  have hrange (n : ℕ) : (range (τn n)).Finite :=
    CountingProcess.finiteRange_rightGrid_of_le (n + 1) (by omega) hτT
  have hle (n : ℕ) (ω : Ω) : τn n ω ≤ T + 1 := by
    have hi : (((n + 1 : ℕ) : ℝ≥0)⁻¹) ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact (CountingProcess.rightGrid_lt_add_inv (n + 1) (τ ω) (by omega)).le.trans
      (add_le_add (hτT ω) hi)
  have hmean (n : ℕ) : ∫ ω, M (τn n ω) ω ∂μ = ∫ ω, M 0 ω ∂μ := by
    have hle' (ω : Ω) : (τn n ω : WithTop ℝ≥0) ≤ (T + 1 : ℝ≥0) := by
      exact_mod_cast hle n ω
    have hrange' : (range fun ω ↦ (τn n ω : WithTop ℝ≥0)).Countable := by
      exact (hrange n).countable.image (fun t : ℝ≥0 ↦ (t : WithTop ℝ≥0)) |>.mono
        (by rintro _ ⟨ω, rfl⟩; exact ⟨τn n ω, ⟨ω, rfl⟩, rfl⟩)
    have host := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hstop n) hle' hrange'
    calc
      ∫ ω, M (τn n ω) ω ∂μ = ∫ ω, μ[M (T + 1) | (hstop n).measurableSpace] ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [host] with ω hω
        exact hω
      _ = ∫ ω, M (T + 1) ω ∂μ := integral_condExp (hstop n).measurableSpace_le
      _ = ∫ ω, M 0 ω ∂μ := by
        simpa using (hM.setIntegral_eq (show (0 : ℝ≥0) ≤ T + 1 by positivity)
          (s := univ) MeasurableSet.univ).symm
  have hlim : Tendsto (fun n ↦ ∫ ω, M (τn n ω) ω ∂μ) atTop
      (𝓝 (∫ ω, M (τ ω) ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence D
    · intro n
      exact (CountingProcess.stronglyMeasurable_eval_finiteRange hM.stronglyAdapted
        (hstop n) (hrange n)).aestronglyMeasurable
    · exact hD
    · intro n
      filter_upwards [hBound] with ω hω
      exact hω (τn n ω) (hle n ω)
    · filter_upwards [hRight] with ω hω
      apply (hω (τ ω)).tendsto.comp
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨CountingProcess.tendsto_rightGrid_succ (τ ω),
        Filter.Eventually.of_forall fun n ↦
          CountingProcess.le_rightGrid (n + 1) (τ ω) (by omega)⟩
  simp_rw [hmean] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- The constant-envelope special case of bounded continuous-time optional stopping. -/
theorem integral_martingale_boundedStopping
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℝ≥0))
    (hτT : ∀ ω, τ ω ≤ T)
    (hRight : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    {C : ℝ} (hBound : ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M s ω‖ ≤ C) :
    ∫ ω, M (τ ω) ω ∂μ = ∫ ω, M 0 ω ∂μ :=
  integral_martingale_stopping_of_integrable_bound hM hτ hτT hRight
    (integrable_const C) hBound

end OTSelector.Limit
