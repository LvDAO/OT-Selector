import OTSelector.Feedback.FeedbackBulkMask
import OTSelector.Probability.CountingProcess.OccupationBound

/-!
# Global product integrability of the safe bulk rates

The safe bulk rates are uniformly bounded by `feedbackBulkRateCap`.  The mask also
forces their time support into a deterministic finite interval: if the rate is
nonzero, then the elapsed coordinate is at most `n - B`, hence the time is at
most `max 0 (n - B - x0)`.  This file records the resulting ordinary product
integrability statement.  It makes no compensator assertion.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace OTSelector

set_option linter.style.haveILetI false

open CountingProcess
open FiniteSample

/-! ## Finite time-measure bookkeeping -/

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
    constructor
    · intro h
      exact le_antisymm h.1 h.2
    · intro h
      exact ⟨h.le, h.ge⟩
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
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : NNReal) :
    (timeMeasure.prod μ) (Iic T ×ˢ (univ : Set Ω)) < ∞ := by
  letI : SFinite timeMeasure := by
    unfold timeMeasure
    infer_instance
  have hT := timeMeasure_Iic_lt_top T
  have hS : MeasurableSet (Iic T ×ˢ (univ : Set Ω)) :=
    measurableSet_Iic.prod MeasurableSet.univ
  rw [Measure.prod_apply_symm hS]
  have hsec : ∀ y : Ω,
      timeMeasure ((fun x : NNReal => (x, y)) ⁻¹'
        (Iic T ×ˢ (univ : Set Ω))) = timeMeasure (Iic T) := by
    intro y
    congr 1
    ext x
    simp
  simp_rw [hsec, lintegral_const]
  rw [IsProbabilityMeasure.measure_univ]
  simpa using hT

/-! ## A reusable bounded finite-support bridge -/

private theorem integrable_of_predictable_bounded_finite_support
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    {f : NNReal → Ω → ℝ}
    (hpred : IsStronglyPredictable F f)
    (hnonneg : ∀ t ω, 0 ≤ f t ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t ω, f t ω ≤ C)
    (Tnn : NNReal)
    (hsupport : ∀ t ω, f t ω ≠ 0 → t ≤ Tnn) :
    Integrable (Function.uncurry f) (timeMeasure.prod μ) := by
  let ν : Measure (NNReal × Ω) := timeMeasure.prod μ
  let S : Set (NNReal × Ω) := Iic Tnn ×ˢ (univ : Set Ω)
  letI : SFinite timeMeasure := by
    unfold timeMeasure
    infer_instance
  have hS : MeasurableSet S := by
    exact measurableSet_Iic.prod MeasurableSet.univ
  have hSfinite : ν S < ∞ := by
    simpa [ν, S] using timeSpace_Iic_lt_top μ Tnn
  have hdomOn : IntegrableOn (fun _ : NNReal × Ω => C) S ν := by
    exact integrableOn_const hSfinite.ne
  have hdom : Integrable (S.indicator (fun _ : NNReal × Ω => C)) ν :=
    hdomOn.integrable_indicator hS
  have hambient : StronglyMeasurable[Prod.instMeasurableSpace]
      (Function.uncurry f) :=
    hpred.mono (predictable_le_ambient F)
  refine Integrable.mono' hdom hambient.aestronglyMeasurable ?_
  filter_upwards [] with z
  change ‖f z.1 z.2‖ ≤ S.indicator (fun _ : NNReal × Ω => C) z
  by_cases hf : f z.1 z.2 = 0
  · by_cases hzS : z ∈ S
    · simp [hf, Set.indicator_of_mem hzS, hC]
    · simp [hf, Set.indicator, hzS]
  · have htime : z.1 ∈ Iic Tnn := hsupport z.1 z.2 hf
    have hzS : z ∈ S := by
      exact ⟨htime, Set.mem_univ _⟩
    rw [Set.indicator_of_mem hzS]
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg z.1 z.2)] using
      hbound z.1 z.2

/-! ## Safe source and target rates -/

private theorem safe_elapsed_le_terminal_of_mask_ne_zero
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : NNReal) (sample : FiniteSample n)
    (hmask : safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample ≠ 0) :
    (t : ℝ) ≤ (n : ℝ) - B - x0 := by
  have hbulk : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) := by
    by_contra h
    apply hmask
    simp [safeFeedbackBulkMask, h]
  rcases hbulk with ⟨_, hupper, _⟩
  dsimp [elapsedFeedbackCoordinate] at hupper
  linarith

private noncomputable def safeRateTerminalTime
    (n : ℕ) (B x0 : ℝ) : NNReal :=
  max 0 (Real.toNNReal ((n : ℝ) - B - x0))

private theorem safeRateTerminalTime_coe
    (n : ℕ) (B x0 : ℝ) :
    (safeRateTerminalTime n B x0 : ℝ) =
      max 0 ((n : ℝ) - B - x0) := by
  simp [safeRateTerminalTime, Real.coe_toNNReal', max_comm]

private theorem safe_rate_le_terminal_time_of_mask_ne_zero
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : NNReal) (sample : FiniteSample n)
    (hmask : safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample ≠ 0) :
    t ≤ safeRateTerminalTime n B x0 := by
  have hupper := safe_elapsed_le_terminal_of_mask_ne_zero
    hlam0 hlamHalf B x0 p0 t sample hmask
  have hmax : (t : ℝ) ≤ max 0 ((n : ℝ) - B - x0) :=
    le_max_of_le_right hupper
  apply NNReal.coe_le_coe.mp
  simpa [safeRateTerminalTime_coe] using hmax

theorem safeSourceBulkRate_product_integrable
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    Integrable
      (Function.uncurry (safeSourceBulkRate hlam0 hlamHalf B x0 p0))
      (timeMeasure.prod (finiteSampleLaw n : Measure (FiniteSample n))) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  let T := safeRateTerminalTime n B x0
  apply integrable_of_predictable_bounded_finite_support
    (μ := (finiteSampleLaw n : Measure (FiniteSample n))) F
    (safeSourceBulkRate_predictable hlam0 hlamHalf B x0 p0)
    (fun t sample ↦ safeSourceBulkRate_nonneg hlam0 hlamHalf B x0 p0 t sample)
    (feedbackBulkRateCap_nonneg n B)
    (fun t sample ↦ safeSourceBulkRate_le_cap hlam0 hlamHalf B x0 p0 t sample)
    T
  intro t sample hf
  have hmask : safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample ≠ 0 := by
    intro hz
    apply hf
    simp [safeSourceBulkRate, hz]
  exact safe_rate_le_terminal_time_of_mask_ne_zero
    hlam0 hlamHalf B x0 p0 t sample hmask

theorem safeTargetBulkRate_product_integrable
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    Integrable
      (Function.uncurry (safeTargetBulkRate hlam0 hlamHalf B x0 p0))
      (timeMeasure.prod (finiteSampleLaw n : Measure (FiniteSample n))) := by
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  let T := safeRateTerminalTime n B x0
  apply integrable_of_predictable_bounded_finite_support
    (μ := (finiteSampleLaw n : Measure (FiniteSample n))) F
    (safeTargetBulkRate_predictable hlam0 hlamHalf B x0 p0)
    (fun t sample ↦ safeTargetBulkRate_nonneg hlam0 hlamHalf B x0 p0 t sample)
    (feedbackBulkRateCap_nonneg n B)
    (fun t sample ↦ safeTargetBulkRate_le_cap hlam0 hlamHalf B x0 p0 t sample)
    T
  intro t sample hf
  have hmask : safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample ≠ 0 := by
    intro hz
    apply hf
    simp [safeTargetBulkRate, hz]
  exact safe_rate_le_terminal_time_of_mask_ne_zero
    hlam0 hlamHalf B x0 p0 t sample hmask

end OTSelector
