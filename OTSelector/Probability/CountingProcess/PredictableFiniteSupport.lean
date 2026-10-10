import OTSelector.Probability.CountingProcess.StoppingMasks
import OTSelector.Probability.CountingProcess.OccupationBound

/-!
# Integrability of bounded predictable processes with finite time support

This file isolates the product-integrability argument used by finite-horizon counting rates.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace OTSelector.CountingProcess

private theorem timeMeasure_singleton_zero :
    timeMeasure ({0} : Set NNReal) = 0 := by
  rw [timeMeasure, Measure.map_apply measurable_real_toNNReal
    (measurableSet_singleton (0 : NNReal))]
  have hpre : Real.toNNReal ⁻¹' ({0} : Set NNReal) = Iic (0 : ℝ) := by
    ext x
    simp [Real.toNNReal_eq_zero]
  rw [hpre, Measure.restrict_apply measurableSet_Iic]
  have hint : Iic (0 : ℝ) ∩ Ici (0 : ℝ) = ({0} : Set ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_singleton_iff]
    exact ⟨fun h ↦ le_antisymm h.1 h.2, fun h ↦ ⟨h.le, h.ge⟩⟩
  rw [hint, Real.volume_singleton]

private theorem timeMeasure_Iic_lt_top (T : NNReal) :
    timeMeasure (Iic T) < ∞ := by
  have hsub : Iic T ⊆ Ioc (0 : NNReal) T ∪ ({0} : Set NNReal) := by
    intro t ht
    by_cases ht0 : t = 0
    · exact Or.inr ht0
    · exact Or.inl ⟨lt_of_le_of_ne bot_le (Ne.symm ht0), ht⟩
  calc
    timeMeasure (Iic T) ≤ timeMeasure (Ioc (0 : NNReal) T ∪ ({0} : Set NNReal)) :=
      measure_mono hsub
    _ ≤ timeMeasure (Ioc (0 : NNReal) T) + timeMeasure ({0} : Set NNReal) :=
      measure_union_le _ _
    _ = timeMeasure (Ioc (0 : NNReal) T) := by
      rw [timeMeasure_singleton_zero, add_zero]
    _ < ∞ := timeMeasure_Ioc_lt_top 0 T

private theorem timeSpace_Iic_lt_top
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (T : NNReal) :
    (timeMeasure.prod mu) (Iic T ×ˢ (univ : Set Omega)) < ∞ := by
  let _ : SFinite timeMeasure := by
    unfold timeMeasure
    infer_instance
  have hS : MeasurableSet (Iic T ×ˢ (univ : Set Omega)) :=
    measurableSet_Iic.prod MeasurableSet.univ
  rw [Measure.prod_apply_symm hS]
  have hsec : ∀ omega : Omega,
      timeMeasure ((fun x : NNReal ↦ (x, omega)) ⁻¹'
        (Iic T ×ˢ (univ : Set Omega))) = timeMeasure (Iic T) := by
    intro omega
    congr 1
    ext x
    simp
  simp_rw [hsec, lintegral_const]
  rw [IsProbabilityMeasure.measure_univ]
  simpa using timeMeasure_Iic_lt_top T

/-- A nonnegative predictable process that is uniformly bounded and vanishes after a
deterministic finite time is integrable under the time-sample product law. -/
theorem integrable_uncurry_of_predictable_bounded_finite_support
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    {f : NNReal → Omega → ℝ}
    (hpred : IsStronglyPredictable F f)
    (hnonneg : ∀ t omega, 0 ≤ f t omega)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t omega, f t omega ≤ C)
    (T : NNReal)
    (hsupport : ∀ t omega, f t omega ≠ 0 → t ≤ T) :
    Integrable (Function.uncurry f) (timeMeasure.prod mu) := by
  let nu : Measure (NNReal × Omega) := timeMeasure.prod mu
  let S : Set (NNReal × Omega) := Iic T ×ˢ (univ : Set Omega)
  have hS : MeasurableSet S := measurableSet_Iic.prod MeasurableSet.univ
  have hSfinite : nu S < ∞ := by
    simpa [nu, S] using timeSpace_Iic_lt_top mu T
  have hdomOn : IntegrableOn (fun _ : NNReal × Omega ↦ C) S nu :=
    integrableOn_const hSfinite.ne
  have hdom : Integrable (S.indicator (fun _ : NNReal × Omega ↦ C)) nu :=
    hdomOn.integrable_indicator hS
  have hambient : StronglyMeasurable[Prod.instMeasurableSpace]
      (Function.uncurry f) := hpred.mono (predictable_le_ambient F)
  refine Integrable.mono' hdom hambient.aestronglyMeasurable ?_
  filter_upwards [] with z
  change ‖f z.1 z.2‖ ≤ S.indicator (fun _ : NNReal × Omega ↦ C) z
  by_cases hf : f z.1 z.2 = 0
  · by_cases hzS : z ∈ S
    · simp [hf, Set.indicator_of_mem hzS, hC]
    · simp [hf, Set.indicator, hzS]
  · have hzS : z ∈ S := ⟨hsupport z.1 z.2 hf, Set.mem_univ _⟩
    rw [Set.indicator_of_mem hzS]
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg z.1 z.2)] using
      hbound z.1 z.2

end OTSelector.CountingProcess
