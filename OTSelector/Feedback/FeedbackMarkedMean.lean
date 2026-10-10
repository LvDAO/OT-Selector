import OTSelector.Feedback.FeedbackMarkedNextEvent
import OTSelector.Feedback.FeedbackPredictableRate

/-!
# Regularity of the actual conditional mark averages

The weighted mark integrals are affine in the current slope. Their normalized means are
measurable everywhere, continuous on the admissible slope interval, and preserve a mark-test
bound. Composing with the actual left feedback slope gives bounded predictable transforms.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

private theorem mark_integrable {f : UnitMark → ℝ} (hf : Continuous f) :
    Integrable f (unitUniform : Measure UnitMark) := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact
    (μ := (unitUniform : Measure UnitMark)) (K := (univ : Set UnitMark)) isCompact_univ

private theorem integral_mark_affine (q : ℝ) (ψ b : UnitMark → ℝ)
    (hψ : Continuous ψ) (hb : Continuous b) :
    (∫ u, ψ u * (1 + q * b u) ∂(unitUniform : Measure UnitMark)) =
      (∫ u, ψ u ∂(unitUniform : Measure UnitMark)) +
        q * ∫ u, ψ u * b u ∂(unitUniform : Measure UnitMark) := by
  simp_rw [show ∀ u, ψ u * (1 + q * b u) = ψ u + q * (ψ u * b u) by intro u; ring]
  have hi : Integrable (fun u ↦ q * (ψ u * b u)) (unitUniform : Measure UnitMark) :=
    (mark_integrable (hψ.mul hb)).const_mul q
  rw [integral_add (mark_integrable hψ) hi,
    integral_const_mul]

theorem sourceFeedbackMarkMean_eq (q : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    sourceFeedbackMarkMean q ψ =
      ((∫ u, ψ u ∂(unitUniform : Measure UnitMark)) +
        q * ∫ u, ψ u * ((u : ℝ) - 1) ∂(unitUniform : Measure UnitMark)) / (1 - q / 2) := by
  unfold sourceFeedbackMarkMean
  congr 1
  convert integral_mark_affine q ψ (fun u ↦ (u : ℝ) - 1) hψ (by fun_prop) using 1
  apply integral_congr_ae
  filter_upwards with u
  simp only [sourceMarkedFactor]
  ring

theorem targetFeedbackMarkMean_eq (q : ℝ) (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    targetFeedbackMarkMean q ψ =
      ((∫ u, ψ u ∂(unitUniform : Measure UnitMark)) +
        q * ∫ u, ψ u * (1 + (u : ℝ)) ∂(unitUniform : Measure UnitMark)) / (1 + 3 * q / 2) := by
  unfold targetFeedbackMarkMean targetMarkedFactor
  rw [integral_mark_affine q ψ _ hψ (by fun_prop)]

theorem measurable_sourceFeedbackMarkMean (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    Measurable (fun q ↦ sourceFeedbackMarkMean q ψ) := by
  simp_rw [sourceFeedbackMarkMean_eq _ ψ hψ]
  fun_prop

theorem measurable_targetFeedbackMarkMean (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    Measurable (fun q ↦ targetFeedbackMarkMean q ψ) := by
  simp_rw [targetFeedbackMarkMean_eq _ ψ hψ]
  fun_prop

theorem continuousOn_sourceFeedbackMarkMean (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    ContinuousOn (fun q ↦ sourceFeedbackMarkMean q ψ) (Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  simp_rw [sourceFeedbackMarkMean_eq _ ψ hψ]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro q hq
  linarith [hq.2]

theorem continuousOn_targetFeedbackMarkMean (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    ContinuousOn (fun q ↦ targetFeedbackMarkMean q ψ) (Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  simp_rw [targetFeedbackMarkMean_eq _ ψ hψ]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro q hq
  linarith [hq.1]

private theorem norm_normalized_mark_integral_le (ψ F : UnitMark → ℝ)
    (hψ : Continuous ψ) (hF : Continuous F) (hF0 : ∀ u, 0 ≤ F u)
    {C : ℝ} (hbound : ∀ u, ‖ψ u‖ ≤ C)
    (hden : 0 < ∫ u, F u ∂(unitUniform : Measure UnitMark)) :
    ‖(∫ u, ψ u * F u ∂(unitUniform : Measure UnitMark)) /
      (∫ u, F u ∂(unitUniform : Measure UnitMark))‖ ≤ C := by
  rw [norm_div, Real.norm_of_nonneg hden.le, div_le_iff₀ hden]
  calc
    _ ≤ ∫ u, ‖ψ u * F u‖ ∂(unitUniform : Measure UnitMark) := norm_integral_le_integral_norm _
    _ ≤ ∫ u, C * F u ∂(unitUniform : Measure UnitMark) := by
      apply integral_mono (mark_integrable (hψ.mul hF)).norm
        ((mark_integrable hF).const_mul C)
      intro u
      change ‖ψ u * F u‖ ≤ C * F u
      rw [norm_mul, Real.norm_eq_abs (F u), abs_of_nonneg (hF0 u)]
      exact mul_le_mul_of_nonneg_right (hbound u) (hF0 u)
    _ = _ := integral_const_mul _ _

theorem norm_sourceFeedbackMarkMean_le {lam q C : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : lam < 1 / 2) (hq : |q| ≤ lam) (ψ : UnitMark → ℝ) (hψ : Continuous ψ)
    (hbound : ∀ u, ‖ψ u‖ ≤ C) : ‖sourceFeedbackMarkMean q ψ‖ ≤ C := by
  have hq1 : q ≤ lam := (le_abs_self q).trans hq
  have hpos (u : UnitMark) : 0 ≤ sourceMarkedFactor q u := by
    have hp := mul_le_mul_of_nonneg_right hq1 (sub_nonneg.mpr u.property.2)
    have hp' := mul_le_mul_of_nonneg_left
      (show 1 - (u : ℝ) ≤ 1 by linarith [u.property.1]) hlam0
    dsimp [sourceMarkedFactor]
    nlinarith
  have h := norm_normalized_mark_integral_le ψ (fun u ↦ sourceMarkedFactor q u)
    hψ (by unfold sourceMarkedFactor; fun_prop) hpos hbound
    (by rw [integral_sourceMarkedFactor]; linarith)
  simpa only [sourceFeedbackMarkMean, integral_sourceMarkedFactor] using h

theorem norm_targetFeedbackMarkMean_le {lam q C : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : lam < 1 / 2) (hq : |q| ≤ lam) (ψ : UnitMark → ℝ) (hψ : Continuous ψ)
    (hbound : ∀ u, ‖ψ u‖ ≤ C) : ‖targetFeedbackMarkMean q ψ‖ ≤ C := by
  have hq1 : -lam ≤ q := neg_le_of_abs_le hq
  have hpos (u : UnitMark) : 0 ≤ targetMarkedFactor q u := by
    have hp := mul_le_mul_of_nonneg_right hq1
      (show 0 ≤ 1 + (u : ℝ) by linarith [u.property.1])
    have hp' := mul_le_mul_of_nonneg_left
      (show 1 + (u : ℝ) ≤ 2 by linarith [u.property.2]) hlam0
    dsimp [targetMarkedFactor]
    nlinarith
  have h := norm_normalized_mark_integral_le ψ (fun u ↦ targetMarkedFactor q u)
    hψ (by unfold targetMarkedFactor; fun_prop) hpos hbound
    (by rw [integral_targetMarkedFactor]; linarith)
  simpa only [targetFeedbackMarkMean, integral_targetMarkedFactor] using h

theorem measurable_feedbackLabelMarkMean {n : ℕ} (ψ : UnitMark → ℝ)
    (hψ : Continuous ψ) (label : FeedbackLabel n) :
    Measurable (fun q ↦ feedbackLabelMarkMean q ψ label) := by
  cases label with
  | inl i => exact measurable_sourceFeedbackMarkMean ψ hψ
  | inr i => exact measurable_targetFeedbackMarkMean ψ hψ

theorem norm_feedbackLabelMarkMean_le {n : ℕ} {lam q C : ℝ}
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 2) (hq : |q| ≤ lam)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) (hbound : ∀ u, ‖ψ u‖ ≤ C)
    (label : FeedbackLabel n) : ‖feedbackLabelMarkMean q ψ label‖ ≤ C := by
  cases label with
  | inl i => exact norm_sourceFeedbackMarkMean_le hlam0 hlam hq ψ hψ hbound
  | inr i => exact norm_targetFeedbackMarkMean_le hlam0 hlam hq ψ hψ hbound

namespace FiniteSample

theorem sourceFeedbackMarkMean_safePreFeedbackSlope_predictable {n : ℕ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    IsStronglyPredictable (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ sourceFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample) ψ) :=
  ((measurable_sourceFeedbackMarkMean ψ hψ).comp
    (safePreFeedbackSlope_predictable (n := n) hlam0 hlamHalf x0 p0).measurable).stronglyMeasurable

theorem targetFeedbackMarkMean_safePreFeedbackSlope_predictable {n : ℕ} {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ)
    (ψ : UnitMark → ℝ) (hψ : Continuous ψ) :
    IsStronglyPredictable (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ targetFeedbackMarkMean (safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample) ψ) :=
  ((measurable_targetFeedbackMarkMean ψ hψ).comp
    (safePreFeedbackSlope_predictable (n := n) hlam0 hlamHalf x0 p0).measurable).stronglyMeasurable

end FiniteSample

end OTSelector
