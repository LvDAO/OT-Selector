import OTSelector.Probability.CountingProcess.UsualRectangleLift
import OTSelector.Probability.CountingProcess.RectangleExtension
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Bounded raw martingales under the usual augmentation

A uniformly bounded right-continuous process has right `L¹` continuity by dominated
convergence. Thus its raw-filtration increment identities pass to the usual augmentation.
This applies to centered finite marked-event sums without duplicating the counting-process lift.
-/

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded, right-continuous process has right `L¹` continuity under a finite measure. -/
theorem bounded_rightContinuous_rightL1 (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : ℝ≥0 → Ω → ℝ) (hM : ∀ t, AEStronglyMeasurable (M t) μ)
    {C : ℝ} (hbound : ∀ t ω, ‖M t ω‖ ≤ C)
    (hrc : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    (s : ℝ≥0) {r : ℕ → ℝ≥0} (hr : Tendsto r atTop (𝓝 s))
    (hright : ∀ᶠ n in atTop, s < r n) :
    Tendsto (fun n ↦ ∫⁻ ω, ‖M (r n) ω - M s ω‖ₑ ∂μ) atTop (𝓝 0) := by
  have hwithin : Tendsto r atTop (𝓝[Ici s] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr, hright.mono fun _ hn ↦ hn.le⟩
  have hmeas : ∀ᶠ n in atTop,
      AEMeasurable (fun ω ↦ ‖M (r n) ω - M s ω‖ₑ) μ :=
    Eventually.of_forall fun n ↦ ((hM (r n)).sub (hM s)).enorm
  have hdom : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
      ‖M (r n) ω - M s ω‖ₑ ≤ ENNReal.ofReal (2 * C) := by
    apply Eventually.of_forall
    intro n
    filter_upwards with ω
    have hnorm : ‖M (r n) ω - M s ω‖ ≤ 2 * C := by
      calc
        _ ≤ ‖M (r n) ω‖ + ‖M s ω‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hbound _ _) (hbound _ _)
        _ = 2 * C := (two_mul C).symm
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm
  have hfinite : (∫⁻ _ : Ω, ENNReal.ofReal (2 * C) ∂μ) ≠ ∞ :=
    (lintegral_const_lt_top (μ := μ) ENNReal.ofReal_ne_top).ne
  have hlim : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ ‖M (r n) ω - M s ω‖ₑ) atTop (𝓝 0) := by
    filter_upwards with ω
    have hzero : Tendsto (fun n ↦ M (r n) ω - M s ω) atTop (𝓝 0) := by
      simpa using ((hrc ω s).tendsto.comp hwithin).sub_const (M s ω)
    simpa only [Function.comp_def, enorm_zero] using
      (continuous_enorm.tendsto (0 : ℝ)).comp hzero
  simpa only [lintegral_zero] using tendsto_lintegral_filter_of_dominated_convergence'
    (μ := μ) (l := atTop) (F := fun n ω ↦ ‖M (r n) ω - M s ω‖ₑ)
    (f := fun _ ↦ (0 : ℝ≥0∞)) (fun _ ↦ ENNReal.ofReal (2 * C))
    hmeas hdom hfinite hlim

/-- Raw increment identities suffice for a bounded right-continuous, usually adapted process. -/
theorem martingale_usualAugmentation_of_bounded_raw
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → ℝ)
    (hadapted : StronglyAdapted (usualAugmentation F μ) M)
    {C : ℝ} (hbound : ∀ t ω, ‖M t ω‖ ≤ C)
    (hrc : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    (hraw : ∀ s t, s ≤ t → ∀ B : Set Ω, MeasurableSet[F s] B →
      (∫ ω in B, M t ω - M s ω ∂μ) = 0) :
    Martingale M (usualAugmentation F μ) μ := by
  have hmeas (t) : AEStronglyMeasurable (M t) μ :=
    ((hadapted t).mono ((usualAugmentation F μ).le t)).aestronglyMeasurable
  have hint (t) : Integrable (M t) μ :=
    Integrable.of_bound (hmeas t) C (Eventually.of_forall (hbound t))
  apply CountingProcess.martingale_of_all_setIntegral_eq_of_isFiniteMeasure hadapted hint
  intro s t hst B hB
  apply CountingProcess.setIntegral_eq_of_usualAugmentation_of_rightL1 F M hint
    ?_ (fun s _ hr hrgt ↦ bounded_rightContinuous_rightL1 μ M hmeas hbound hrc s hr hrgt)
    hst hB
  intro r u hru A hA
  have h := hraw r u hru A hA
  rw [integral_sub (hint u).integrableOn (hint r).integrableOn] at h
  exact sub_eq_zero.mp h

end OTSelector.Probability
