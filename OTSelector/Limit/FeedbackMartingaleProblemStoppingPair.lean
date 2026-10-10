import OTSelector.Limit.FeedbackMartingaleProblemStopping

/-!
# Optional sampling on a history event between bounded continuous stopping times

Finite right grids preserve measurability of the event at the earlier stopping time. Both
stopped set integrals equal the same deterministic terminal set integral; an integrable envelope
then passes this equality to the original stopping coordinates.
-/

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace OTSelector.Limit

/-- Bounded continuous-time optional sampling on an event measurable at the earlier stopping
coordinate. Right continuity and the integrable envelope may hold outside one null set. -/
theorem setIntegral_martingale_stopping_pair_of_integrable_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) {σ ρ : Ω → ℝ≥0} {T : ℝ≥0}
    (hσ : IsStoppingTime ℱ fun ω ↦ (σ ω : WithTop ℝ≥0))
    (hρ : IsStoppingTime ℱ fun ω ↦ (ρ ω : WithTop ℝ≥0))
    (hσρ : ∀ ω, σ ω ≤ ρ ω) (hρT : ∀ ω, ρ ω ≤ T)
    (hRight : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    {D : Ω → ℝ} (hD : Integrable D μ)
    (hBound : ∀ᵐ ω ∂μ, ∀ s, s ≤ T + 1 → ‖M s ω‖ ≤ D ω)
    {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    ∫ ω in A, M (ρ ω) ω ∂μ = ∫ ω in A, M (σ ω) ω ∂μ := by
  have hend {τ : Ω → ℝ≥0}
      (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℝ≥0))
      (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T) :
      ∫ ω in A, M (τ ω) ω ∂μ = ∫ ω in A, M (T + 1) ω ∂μ := by
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
    have hmean (n : ℕ) : ∫ ω in A, M (τn n ω) ω ∂μ = ∫ ω in A, M (T + 1) ω ∂μ := by
      have hle' (ω : Ω) : (τn n ω : WithTop ℝ≥0) ≤ (T + 1 : ℝ≥0) := by
        exact_mod_cast hle n ω
      have hrange' : (range fun ω ↦ (τn n ω : WithTop ℝ≥0)).Countable := by
        exact (hrange n).countable.image (fun t : ℝ≥0 ↦ (t : WithTop ℝ≥0)) |>.mono
          (by rintro _ ⟨ω, rfl⟩; exact ⟨τn n ω, ⟨ω, rfl⟩, rfl⟩)
      have hA' : MeasurableSet[(hstop n).measurableSpace] A := by
        apply hσ.measurableSpace_mono (hstop n) (s := A) ?_ hA
        intro ω
        change (σ ω : WithTop ℝ≥0) ≤
          (CountingProcess.rightGrid (n + 1) (τ ω) : WithTop ℝ≥0)
        exact_mod_cast (hστ ω).trans
          (CountingProcess.le_rightGrid (n + 1) (τ ω) (by omega))
      have host := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
        (hstop n) hle' hrange'
      calc
        ∫ ω in A, M (τn n ω) ω ∂μ =
            ∫ ω in A, μ[M (T + 1) | (hstop n).measurableSpace] ω ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae host] with ω hω
          exact hω
        _ = ∫ ω in A, M (T + 1) ω ∂μ :=
          setIntegral_condExp (hstop n).measurableSpace_le (hM.integrable _) hA'
    have hlim : Tendsto (fun n ↦ ∫ ω in A, M (τn n ω) ω ∂μ) atTop
        (𝓝 (∫ ω in A, M (τ ω) ω ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence D
      · intro n
        exact (CountingProcess.stronglyMeasurable_eval_finiteRange hM.stronglyAdapted
          (hstop n) (hrange n)).aestronglyMeasurable
      · exact hD.integrableOn
      · intro n
        filter_upwards [ae_restrict_of_ae hBound] with ω hω
        exact hω (τn n ω) (hle n ω)
      · filter_upwards [ae_restrict_of_ae hRight] with ω hω
        apply (hω (τ ω)).tendsto.comp
        apply tendsto_nhdsWithin_iff.mpr
        exact ⟨CountingProcess.tendsto_rightGrid_succ (τ ω),
          Filter.Eventually.of_forall fun n ↦
            CountingProcess.le_rightGrid (n + 1) (τ ω) (by omega)⟩
    simp_rw [hmean] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  exact (hend hρ hσρ hρT).trans (hend hσ (fun _ ↦ le_rfl)
    (fun ω ↦ (hσρ ω).trans (hρT ω))).symm

end OTSelector.Limit
