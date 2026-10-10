import OTSelector.Limit.FeedbackMartingaleProblemRestartTest

/-!
# Removing deterministic bounds from conditional jump-law identities

A conditional readout law valid on an increasing family of measurable localization events
extends to their almost-everywhere union. This is ordinary continuity from below of measures;
no limiting Markov or conditional-distribution assertion is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace OTSelector.Limit

/-- A common conditional readout law passes from increasing localization events to their
almost-everywhere union. Zero-probability localization events require no conditional identity. -/
theorem map_cond_eq_of_monotone_localization
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → E} (hf : Measurable f)
    (ν : Measure E) {A : Set Ω} (hA : MeasurableSet A) (hA0 : μ A ≠ 0)
    (Aseq : ℕ → Set Ω) (hAseq : ∀ n, MeasurableSet (Aseq n))
    (hmono : Monotone Aseq) (hcover : A =ᵐ[μ] ⋃ n, Aseq n)
    (hlaw : ∀ n, μ (Aseq n) ≠ 0 → (μ[|Aseq n]).map f = ν) :
    (μ[|A]).map f = ν := by
  apply Measure.ext
  intro B hB
  have hpiece (n : ℕ) : μ (Aseq n ∩ f ⁻¹' B) = μ (Aseq n) * ν B := by
    by_cases hz : μ (Aseq n) = 0
    · have hi : μ (Aseq n ∩ f ⁻¹' B) = 0 := measure_mono_null inter_subset_left hz
      simp [hz, hi]
    · have h := congrArg (fun m : Measure E ↦ m B) (hlaw n hz)
      rw [Measure.map_apply hf hB, cond_apply (hAseq n)] at h
      calc
        _ = μ (Aseq n) * ((μ (Aseq n))⁻¹ * μ (Aseq n ∩ f ⁻¹' B)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hz (measure_ne_top _ _), one_mul]
        _ = μ (Aseq n) * ν B := by rw [h]
  have hmonointer : Monotone (fun n ↦ Aseq n ∩ f ⁻¹' B) :=
    fun _ _ h ↦ inter_subset_inter_left _ (hmono h)
  have hmass : μ (A ∩ f ⁻¹' B) = μ A * ν B := by
    calc
      _ = μ ((⋃ n, Aseq n) ∩ f ⁻¹' B) :=
        measure_congr (hcover.inter EventuallyEq.rfl)
      _ = μ (⋃ n, Aseq n ∩ f ⁻¹' B) := by rw [iUnion_inter]
      _ = ⨆ n, μ (Aseq n ∩ f ⁻¹' B) := hmonointer.measure_iUnion
      _ = ⨆ n, μ (Aseq n) * ν B := by simp_rw [hpiece]
      _ = (⨆ n, μ (Aseq n)) * ν B := (ENNReal.iSup_mul _ _).symm
      _ = μ (⋃ n, Aseq n) * ν B := by rw [hmono.measure_iUnion]
      _ = μ A * ν B := by rw [measure_congr hcover]
  rw [Measure.map_apply hf hB, cond_apply hA, hmass, ← mul_assoc,
    ENNReal.inv_mul_cancel hA0 (measure_ne_top _ _), one_mul]

end OTSelector.Limit
