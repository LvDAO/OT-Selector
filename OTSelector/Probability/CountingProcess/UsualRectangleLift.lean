import OTSelector.Probability.AmbientNullReduction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lifting set-integral identities to the usual augmentation

The right-continuous augmentation only gives an original-filtration representative of an
event at times strictly larger than its left endpoint.  This file records the small analytic
argument which removes that gap.  A right `L¹` condition on the process lets the representative
time decrease to the left endpoint, while the raw set-integral identity is used at every
strictly later representative time.

The hypothesis is intentionally a direct `L¹` convergence statement, rather than a packaged
martingale or certificate interface.  It is exactly the form needed by the rectangle argument:
for every sequence approaching `s` from the right, the `L¹` distance to `M s` tends to zero.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## A concrete right-approaching sequence -/

/-- A simple sequence approaching `s` from the right.  It is not tied to a terminal time; for
any `t > s` it is eventually below `t`. -/
noncomputable def rightApproach (s : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  s + ((n + 1 : ℕ) : ℝ≥0)⁻¹

theorem rightApproach_gt (s : ℝ≥0) (n : ℕ) : s < rightApproach s n := by
  exact lt_add_of_pos_right s (by positivity)

theorem rightApproach_tendsto (s : ℝ≥0) :
    Tendsto (rightApproach s) atTop (𝓝 s) := by
  have h_inv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0)⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hsum :
      Tendsto (fun n : ℕ ↦ s + ((n + 1 : ℕ) : ℝ≥0)⁻¹) atTop (𝓝 s) := by
    simpa using h_inv.const_add s
  apply Tendsto.congr' ?_ hsum
  filter_upwards [] with n
  simp [rightApproach]

/-! ## The raw-to-usual rectangle lift -/

/-
The `hRightL1` argument below is a sequence form of right `L¹` continuity.  It is convenient
for callers because it avoids choosing a normed-function-space representative: the only
quantity exposed is the integral of the pointwise norm difference.
-/

theorem setIntegral_eq_of_usualAugmentation_of_rightL1
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ)
    (hIntegrable : ∀ u : ℝ≥0, Integrable (M u) μ)
    (hRaw : ∀ {r t : ℝ≥0}, r ≤ t → ∀ A : Set Ω, MeasurableSet[ℱ r] A →
      (∫ ω in A, M t ω ∂μ) = ∫ ω in A, M r ω ∂μ)
    (hRightL1 : ∀ s : ℝ≥0, ∀ {r : ℕ → ℝ≥0},
      Tendsto r atTop (𝓝 s) →
      (∀ᶠ n in atTop, s < r n) →
      Tendsto (fun n ↦ ∫⁻ ω, ‖M (r n) ω - M s ω‖ₑ ∂μ) atTop (𝓝 0))
    {s t : ℝ≥0} (hst : s ≤ t) {B : Set Ω}
    (hB : MeasurableSet[usualAugmentation ℱ μ s] B) :
    (∫ ω in B, M t ω ∂μ) = ∫ ω in B, M s ω ∂μ := by
  rcases eq_or_lt_of_le hst with rfl | hst
  · rfl
  let r : ℕ → ℝ≥0 := rightApproach s
  have hr_tendsto : Tendsto r atTop (𝓝 s) := by
    exact rightApproach_tendsto s
  have hr_right : ∀ᶠ n in atTop, s < r n := by
    exact Filter.Eventually.of_forall (fun n ↦ rightApproach_gt s n)
  have hL1 :
      Tendsto (fun n ↦ ∫⁻ ω, ‖M (r n) ω - M s ω‖ₑ ∂μ) atTop (𝓝 0) :=
    hRightL1 s hr_tendsto hr_right
  have hsetIntegralL1 :
      Tendsto (fun n ↦ ∫ ω in B, M (r n) ω ∂μ) atTop
        (𝓝 (∫ ω in B, M s ω ∂μ)) := by
    exact tendsto_setIntegral_of_L1 (μ := μ) (f := M s) (F := fun n ↦ M (r n))
      (hIntegrable s).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun n ↦ hIntegrable (r n))) hL1 B
  have hr_le_t : ∀ᶠ n in atTop, r n ≤ t := by
    have hmem : ∀ᶠ n in atTop, r n ∈ Iio t :=
      hr_tendsto.eventually (Iio_mem_nhds hst)
    filter_upwards [hmem] with n hn
    exact hn.le
  have hEq : ∀ n : ℕ, s < r n → r n ≤ t →
      (∫ ω in B, M t ω ∂μ) = ∫ ω in B, M (r n) ω ∂μ := by
    intro n hsn hnt
    obtain ⟨A, hA, hAe⟩ :=
      exists_original_measurableSet_ae_eq_of_usualAugmentation_nnreal
        ℱ μ hB (r n) hsn
    calc
      (∫ ω in B, M t ω ∂μ) = ∫ ω in A, M t ω ∂μ :=
        setIntegral_congr_set hAe
      _ = ∫ ω in A, M (r n) ω ∂μ := hRaw hnt A hA
      _ = ∫ ω in B, M (r n) ω ∂μ :=
        (setIntegral_congr_set hAe).symm
  have hEqEventually : ∀ᶠ n in atTop,
      (∫ ω in B, M t ω ∂μ) = ∫ ω in B, M (r n) ω ∂μ := by
    filter_upwards [hr_right, hr_le_t] with n hsn hnt
    exact hEq n hsn hnt
  have hConst :
      Tendsto (fun _ : ℕ ↦ ∫ ω in B, M t ω ∂μ) atTop
        (𝓝 (∫ ω in B, M s ω ∂μ)) :=
    Tendsto.congr' (Filter.EventuallyEq.symm hEqEventually) hsetIntegralL1
  exact tendsto_nhds_unique tendsto_const_nhds hConst

/-! ## The raw-to-usual inequality lift -/

/-- A raw-filtration set-integral upper bound extends to the usual augmentation. -/
theorem setIntegral_le_of_usualAugmentation_of_rightL1
    {μ : Measure Ω}
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (Y : Ω → ℝ)
    (g : ℝ≥0 → Ω → ℝ)
    (hgIntegrable : ∀ u : ℝ≥0, Integrable (g u) μ)
    (hRaw : ∀ {r : ℝ≥0}, ∀ A : Set Ω, MeasurableSet[ℱ r] A →
      (∫ ω in A, Y ω ∂μ) ≤ ∫ ω in A, g r ω ∂μ)
    (hRightL1 : ∀ s : ℝ≥0, ∀ {r : ℕ → ℝ≥0},
      Tendsto r atTop (𝓝 s) →
      (∀ᶠ n in atTop, s < r n) →
      Tendsto (fun n ↦ ∫⁻ ω, ‖g (r n) ω - g s ω‖ₑ ∂μ) atTop (𝓝 0))
    {s : ℝ≥0} {B : Set Ω}
    (hB : MeasurableSet[usualAugmentation ℱ μ s] B) :
    (∫ ω in B, Y ω ∂μ) ≤ ∫ ω in B, g s ω ∂μ := by
  let r : ℕ → ℝ≥0 := rightApproach s
  have hr_tendsto : Tendsto r atTop (𝓝 s) := by
    exact rightApproach_tendsto s
  have hr_right : ∀ᶠ n in atTop, s < r n := by
    exact Filter.Eventually.of_forall (fun n ↦ rightApproach_gt s n)
  have hL1 :
      Tendsto (fun n ↦ ∫⁻ ω, ‖g (r n) ω - g s ω‖ₑ ∂μ) atTop (𝓝 0) :=
    hRightL1 s hr_tendsto hr_right
  have hsetIntegralL1 :
      Tendsto (fun n ↦ ∫ ω in B, g (r n) ω ∂μ) atTop
        (𝓝 (∫ ω in B, g s ω ∂μ)) := by
    exact tendsto_setIntegral_of_L1 (μ := μ) (f := g s) (F := fun n ↦ g (r n))
      (hgIntegrable s).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun n ↦ hgIntegrable (r n))) hL1 B
  have hEq : ∀ n : ℕ, s < r n →
      (∫ ω in B, Y ω ∂μ) ≤ ∫ ω in B, g (r n) ω ∂μ := by
    intro n hsn
    obtain ⟨A, hA, hAe⟩ :=
      exists_original_measurableSet_ae_eq_of_usualAugmentation_nnreal
        ℱ μ hB (r n) hsn
    calc
      (∫ ω in B, Y ω ∂μ) = ∫ ω in A, Y ω ∂μ := setIntegral_congr_set hAe
      _ ≤ ∫ ω in A, g (r n) ω ∂μ := hRaw A hA
      _ = ∫ ω in B, g (r n) ω ∂μ := (setIntegral_congr_set hAe).symm
  have hEqEventually : ∀ᶠ n in atTop,
      (∫ ω in B, Y ω ∂μ) ≤ ∫ ω in B, g (r n) ω ∂μ := by
    filter_upwards [hr_right] with n hsn
    exact hEq n hsn
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hsetIntegralL1 hEqEventually

end OTSelector.CountingProcess
