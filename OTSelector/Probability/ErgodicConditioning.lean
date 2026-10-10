import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Extreme

/-!
# Conditioning a stationary extension of an ergodic environment

An invariant finite measure absolutely continuous with respect to an ergodic environment is a
scalar multiple of that environment.  This file proves the additive-action version, so spatial
ergodicity does not have to be replaced by the stronger ergodicity of one fixed translation.
Pushing an invariant event of an extension to the environment then preserves its normalized law.
-/

open Filter Function MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace OTSelector.Probability

variable {G X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- A finite invariant measure dominated by an ergodic probability law is its mass times that law.
Invariance is required for the entire additive action, not for a distinguished time-one map. -/
theorem eq_mass_smul_of_ergodicVAdd [VAdd G X] [MeasurableConstVAdd G X]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    [ErgodicVAdd G X ν]
    (hinv : ∀ g : G, MeasurePreserving (g +ᵥ ·) μ μ) (hac : μ ≪ ν) :
    μ = μ univ • ν := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, μ.rnDeriv ν =ᵐ[ν] fun _ ↦ c := by
    apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
    intro U hU
    apply eventuallyConst_set.mp
    apply ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := G)
      ((measurable_rnDeriv μ ν) hU)
    intro g
    filter_upwards [(hinv g).rnDeriv_comp_aeEq (measurePreserving_vadd g ν)] with x hx
    exact congrArg (fun y ↦ y ∈ U) hx
  have hμ : μ = c • ν := by
    ext s hs
    calc
      μ s = ∫⁻ x in s, μ.rnDeriv ν x ∂ν := (setLIntegral_rnDeriv hac s).symm
      _ = ∫⁻ _x in s, c ∂ν := lintegral_congr_ae (ae_restrict_of_ae hc)
      _ = (c • ν) s := by simp
  have hmass : μ univ = c := by
    simpa using congrArg (fun ρ : Measure X ↦ ρ univ) hμ
  simpa only [hmass] using hμ

/-- Restricting a stationary extension to an invariant event changes its environmental
marginal only by the probability of that event. -/
theorem map_restrict_invariant_event [VAdd G X] [MeasurableConstVAdd G X]
    [VAdd G Ω] [MeasurableConstVAdd G Ω]
    {μ : Measure Ω} {ν : Measure X} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    [ErgodicVAdd G X ν] {env : Ω → X}
    (henv : MeasurePreserving env μ ν)
    (hinv : ∀ g : G, MeasurePreserving (g +ᵥ ·) μ μ)
    (hcomm : ∀ g : G, Semiconj env (g +ᵥ ·) (g +ᵥ ·))
    {B : Set Ω} (hB : MeasurableSet B)
    (hBinv : ∀ g : G, (g +ᵥ ·) ⁻¹' B =ᵐ[μ] B) :
    (μ.restrict B).map env = μ B • ν := by
  have hrest (g : G) : MeasurePreserving (g +ᵥ ·) (μ.restrict B) (μ.restrict B) := by
    have h := (hinv g).restrict_preimage hB
    rwa [Measure.restrict_congr_set (hBinv g)] at h
  have hmapinv (g : G) : MeasurePreserving (g +ᵥ ·)
      ((μ.restrict B).map env) ((μ.restrict B).map env) :=
    (henv.measurable.measurePreserving (μ.restrict B)).of_semiconj
      (hrest g) (hcomm g) (measurable_const_vadd g)
  have hac : (μ.restrict B).map env ≪ ν := by
    rw [← henv.map_eq]
    exact (absolutelyContinuous_of_le restrict_le_self).map henv.measurable
  have h := eq_mass_smul_of_ergodicVAdd hmapinv hac
  simpa [Measure.map_apply henv.measurable, Measure.restrict_apply, hB] using h

/-- Conditioning on a positive-probability invariant event preserves an ergodic environment. -/
theorem map_cond_invariant_event [VAdd G X] [MeasurableConstVAdd G X]
    [VAdd G Ω] [MeasurableConstVAdd G Ω]
    {μ : Measure Ω} {ν : Measure X} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    [ErgodicVAdd G X ν] {env : Ω → X}
    (henv : MeasurePreserving env μ ν)
    (hinv : ∀ g : G, MeasurePreserving (g +ᵥ ·) μ μ)
    (hcomm : ∀ g : G, Semiconj env (g +ᵥ ·) (g +ᵥ ·))
    {B : Set Ω} (hB : MeasurableSet B)
    (hBinv : ∀ g : G, (g +ᵥ ·) ⁻¹' B =ᵐ[μ] B) (hpos : μ B ≠ 0) :
    (ProbabilityTheory.cond μ B).map env = ν := by
  rw [ProbabilityTheory.cond, Measure.map_smul,
    map_restrict_invariant_event henv hinv hcomm hB hBinv, smul_smul,
    ENNReal.inv_mul_cancel hpos (measure_ne_top μ B), one_smul]

end OTSelector.Probability
