import OTSelector.Feedback.FeedbackRightIntervalCountsMoment

/-!
# Frozen energy on the actual boundary localization

The same boundary event used for interval density and terminal current controls the integrated
right-tail current energy.  Its conditional expectation and Markov estimate use the original
finite-sample law and full bulk boundary sigma field.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical

namespace OTSelector.FiniteSample

variable {n : ℕ}

/-- Actual frozen energy has conditional mean of order `B²` on the moment localization. -/
theorem condExp_actual_frozenEnergy_le
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT : 0 < T) {xEnd B L : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 1 ≤ B) (hBn : B ≤ (n : ℝ) / 2) (hL : 0 ≤ L)
    (hxEnd : x0 + (T : ℝ) ≤ xEnd) (hlength : xEnd - (x0 + (T : ℝ)) ≤ 3 * B)
    (G : Set (FiniteSample n)) (hG : MeasurableSet G)
    (hgood : ∀ sample ∈ G, rightBoundaryMomentGood lam (x0 + T) B L
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
      (fun sample ↦ rightBoundaryFrozenEnergy lam (x0 + T) xEnd
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample) |
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
        (finiteSampleLaw n : Measure (FiniteSample n)).restrict G]
      fun _ ↦ 3 * (4 + (17 * L) ^ 2) * B ^ 2 := by
  have hcond := condExp_rightBoundaryFrozenEnergy_le_on_component hn hlam0 hlamHalf
    x0 p0 T hT xEnd B (1 / 2) 2 L 8 G hG hB (by norm_num) (by norm_num) hL (by norm_num)
    hxEnd hlength
    (fun sample hsample ↦ by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using (hgood sample hsample).1)
    (fun sample hsample ↦ by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using (hgood sample hsample).2.1)
    (fun sample hsample ↦ (hgood sample hsample).2.2.1)
    (fun sample hsample ↦ (hgood sample hsample).2.2.2.1)
    (fun sample hsample y hy ↦ rightBoundaryHistoryProbability_difference_le hn lam
      (x0 + T) y B _ hboundary (lt_of_lt_of_le zero_lt_one hB) hBn
      (hgood sample hsample).2.2.2.2 hy.1.le)
  filter_upwards [hcond] with sample hs
  convert hs using 1
  ring

/-- The restricted expectation is controlled without changing the underlying sample law. -/
theorem setIntegral_actual_frozenEnergy_le
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT : 0 < T) {xEnd B L : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 1 ≤ B) (hBn : B ≤ (n : ℝ) / 2) (hL : 0 ≤ L)
    (hxEnd : x0 + (T : ℝ) ≤ xEnd) (hlength : xEnd - (x0 + (T : ℝ)) ≤ 3 * B)
    (G : Set (FiniteSample n))
    (hG : MeasurableSet[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] G)
    (hgood : ∀ sample ∈ G, rightBoundaryMomentGood lam (x0 + T) B L
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) :
    (∫ sample in G, rightBoundaryFrozenEnergy lam (x0 + T) xEnd
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n))) ≤ 3 * (4 + (17 * L) ^ 2) * B ^ 2 := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let E : FiniteSample n → ℝ := fun sample ↦ rightBoundaryFrozenEnergy lam (x0 + T) xEnd
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample
  have hE : StronglyMeasurable E :=
    stronglyMeasurable_frozenEnergy_comp lam (x0 + T) xEnd _ _
      (measurable_revealedSnapshotAtElapsed (n := n) hlam0 hlamHalf x0 p0 T) measurable_id
  have hint : Integrable E μ := Integrable.of_bound hE.aestronglyMeasurable
    ((xEnd - (x0 + (T : ℝ))) * (3 * n) ^ 2)
    (Filter.Eventually.of_forall fun sample ↦ norm_rightBoundaryFrozenEnergy_le lam hxEnd _ sample)
  have hcond := condExp_actual_frozenEnergy_le hn hlam0 hlamHalf x0 p0 T hT hboundary
    hB hBn hL hxEnd hlength G
    ((usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le T G hG) hgood
  have hce : Integrable (μ[E | usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]) μ :=
    integrable_condExp
  have hmono := integral_mono_ae hce.integrableOn (integrable_const _) hcond
  rw [setIntegral_condExp ((usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le T) hint hG,
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hmono
  exact hmono.trans (by
    simpa using mul_le_mul_of_nonneg_right (measureReal_le_one (μ := μ) (s := G))
      (by positivity : 0 ≤ 3 * (4 + (17 * L) ^ 2) * B ^ 2))

/-- Markov's inequality for the actual frozen energy on a bulk-measurable localization. -/
theorem measureReal_actual_frozenEnergy_tail_inter_le
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT : 0 < T) {xEnd B L a : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 1 ≤ B) (hBn : B ≤ (n : ℝ) / 2) (hL : 0 ≤ L)
    (hxEnd : x0 + (T : ℝ) ≤ xEnd) (hlength : xEnd - (x0 + (T : ℝ)) ≤ 3 * B)
    (ha : 0 < a) (G : Set (FiniteSample n))
    (hG : MeasurableSet[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] G)
    (hgood : ∀ sample ∈ G, rightBoundaryMomentGood lam (x0 + T) B L
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      (G ∩ {sample | a ≤ rightBoundaryFrozenEnergy lam (x0 + T) xEnd
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample}) ≤
      3 * (4 + (17 * L) ^ 2) * B ^ 2 / a := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let E : FiniteSample n → ℝ := fun sample ↦ rightBoundaryFrozenEnergy lam (x0 + T) xEnd
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample
  have hE : StronglyMeasurable E :=
    stronglyMeasurable_frozenEnergy_comp lam (x0 + T) xEnd _ _
      (measurable_revealedSnapshotAtElapsed (n := n) hlam0 hlamHalf x0 p0 T) measurable_id
  have hint : Integrable E μ := Integrable.of_bound hE.aestronglyMeasurable
    ((xEnd - (x0 + (T : ℝ))) * (3 * n) ^ 2)
    (Filter.Eventually.of_forall fun sample ↦ norm_rightBoundaryFrozenEnergy_le lam hxEnd _ sample)
  have hnonneg : ∀ sample, 0 ≤ E sample := fun sample ↦ integral_nonneg (fun _ ↦ sq_nonneg _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ.restrict G)
    (Filter.Eventually.of_forall hnonneg) hint.integrableOn a
  rw [measureReal_restrict_apply (measurableSet_le measurable_const hE.measurable), inter_comm] at hmarkov
  have hmean := setIntegral_actual_frozenEnergy_le hn hlam0 hlamHalf x0 p0 T hT hboundary
    hB hBn hL hxEnd hlength G hG hgood
  exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hmarkov.trans hmean)

end OTSelector.FiniteSample
