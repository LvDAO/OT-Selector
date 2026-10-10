import OTSelector.Limit.FeedbackMarkedFirstHold
import OTSelector.Limit.FeedbackCellTrajectory
import OTSelector.Probability.ExponentialPalm

/-!
# Occupation of the first hold preserves the entire marked future law

At any initial current, replacing the first wait by its remaining duration and integrating the
observation age over that wait multiplies the complete path law by the inverse jump rate.
All later waiting times, marks, and currents are retained in this identity.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OTSelector.Limit

/-- Advance inside the first hold, retaining the virtual initial state and all later jumps. -/
def feedbackMarkedResidual (w : FeedbackCellPath) (a : ℝ) (n : ℕ) : FeedbackMarkedStep :=
  if n = 1 then ((w 1).1 - a, (w 1).2) else w n

@[fun_prop]
theorem measurable_feedbackMarkedResidual :
    Measurable (fun p : FeedbackCellPath × ℝ ↦ feedbackMarkedResidual p.1 p.2) := by
  apply measurable_pi_lambda
  intro n
  by_cases h : n = 1 <;> simp only [feedbackMarkedResidual, h, ↓reduceIte] <;> fun_prop

@[simp] theorem feedbackMarkedResidual_zero (w : FeedbackCellPath) (a : ℝ) :
    feedbackMarkedResidual w a 0 = w 0 := rfl

@[simp] theorem feedbackMarkedResidual_one (w : FeedbackCellPath) (a : ℝ) :
    feedbackMarkedResidual w a 1 = ((w 1).1 - a, (w 1).2) := by
  simp [feedbackMarkedResidual]

@[simp] theorem feedbackMarkedResidual_add_two (w : FeedbackCellPath) (a : ℝ) (n : ℕ) :
    feedbackMarkedResidual w a (n + 2) = w (n + 2) := by
  simp [feedbackMarkedResidual]

private def firstHoldAssemble (k : ℤ) (p : ℝ × (UnitMark × ℤ) × FeedbackCellPath) :
    FeedbackCellPath
  | 0 => feedbackMarkedVirtual k
  | 1 => (p.1, p.2.1)
  | n + 2 => p.2.2 (n + 1)

@[fun_prop] private theorem measurable_firstHoldAssemble (k : ℤ) :
    Measurable (firstHoldAssemble k) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n => cases n <;> dsimp [firstHoldAssemble] <;> fun_prop

private theorem firstHoldAssemble_extract (k : ℤ) (w : FeedbackCellPath)
    (h : w 0 = feedbackMarkedVirtual k) :
    firstHoldAssemble k ((w 1).1, (w 1).2, feedbackMarkedRestart 1 w) = w := by
  funext n
  cases n with
  | zero => exact h.symm
  | succ n => cases n with
    | zero => rfl
    | succ n => simp [firstHoldAssemble, feedbackMarkedRestart, Nat.add_comm]

private theorem feedbackMarkedResidual_assemble (k : ℤ)
    (p : ℝ × (UnitMark × ℤ) × FeedbackCellPath) (a : ℝ) :
    feedbackMarkedResidual (firstHoldAssemble k p) a =
      firstHoldAssemble k (p.1 - a, p.2) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => cases n <;> simp [firstHoldAssemble, feedbackMarkedResidual]

private theorem lintegral_exponential_residual {r : ℝ} (hr : 0 < r)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, ∫⁻ a in Ico 0 t, g (t - a) ∂volume ∂expMeasure r =
      (ENNReal.ofReal r)⁻¹ * ∫⁻ u, g u ∂expMeasure r := by
  let := isProbabilityMeasure_expMeasure hr
  have hmap : (exponentialOccupationMeasure r).map (fun p ↦ p.1 - p.2) =
      (ENNReal.ofReal r)⁻¹ • expMeasure r := by
    have h := congrArg (fun μ : Measure (ℝ × ℝ) ↦ μ.map Prod.snd)
      (exponentialOccupationMeasure_map_age_residual hr)
    rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_smul] at h
    simpa [Function.comp_def] using h
  have hS : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  calc
    _ = ∫⁻ p, g (p.1 - p.2) ∂exponentialOccupationMeasure r := by
      rw [exponentialOccupationMeasure, ← lintegral_indicator hS,
        lintegral_prod _ (by
          exact (show Measurable (fun p : ℝ × ℝ ↦
            {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ q.1}.indicator
              (fun q ↦ g (q.1 - q.2)) p) from
            (show Measurable (fun p : ℝ × ℝ ↦ g (p.1 - p.2)) by fun_prop).indicator hS).aemeasurable)]
      apply lintegral_congr
      intro t
      rw [restrict_Ico_eq_restrict_Icc, ← lintegral_indicator measurableSet_Icc]
      rfl
    _ = (ENNReal.ofReal r)⁻¹ * ∫⁻ u, g u ∂expMeasure r := by
      rw [← lintegral_map hg (by fun_prop), hmap, lintegral_smul_measure, smul_eq_mul]

private theorem measurable_firstHoldOccupation (k : ℤ) {f : FeedbackCellPath → ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (fun p : ℝ × (UnitMark × ℤ) × FeedbackCellPath ↦
      ∫⁻ a in Ico 0 p.1, f (firstHoldAssemble k (p.1 - a, p.2)) ∂volume) := by
  simp_rw [← lintegral_indicator measurableSet_Ico]
  have hS : MeasurableSet {q : (ℝ × (UnitMark × ℤ) × FeedbackCellPath) × ℝ |
      q.2 ∈ Ico 0 q.1.1} := by
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst.fst)
  have hm := (hf.comp ((measurable_firstHoldAssemble k).comp
    (show Measurable (fun q : (ℝ × (UnitMark × ℤ) × FeedbackCellPath) × ℝ ↦
      (q.1.1 - q.2, q.1.2)) by fun_prop))).indicator hS
  exact hm.lintegral_prod_right'

/-- First-hold occupation leaves the complete marked future unchanged, apart from the
inverse-rate mass. This includes every future wait, jump mark, and visited current. -/
theorem lintegral_feedbackMarkedResidual (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) {f : FeedbackCellPath → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ w, ∫⁻ a in Ico 0 (w 1).1, f (feedbackMarkedResidual w a) ∂volume
        ∂feedbackMarkedTrajectory lam hlam0 hlam k =
      (ENNReal.ofReal (totalJumpRate lam k))⁻¹ *
        ∫⁻ w, f w ∂feedbackMarkedTrajectory lam hlam0 hlam k := by
  let := feedbackMarkedJumpKernel_isMarkov hlam0 hlam
  let := isProbabilityMeasure_expMeasure (totalJumpRate_pos hlam0 hlam k)
  let ν := feedbackMarkedJumpKernel lam k ⊗ₘ feedbackMarkedAfterJumpKernel lam hlam0 hlam
  let μ := feedbackMarkedTrajectory lam hlam0 hlam k
  have hzero : ∀ᵐ w ∂μ, w 0 = feedbackMarkedVirtual k := by
    have h : ∀ᵐ z ∂Measure.dirac (feedbackMarkedVirtual k), z = feedbackMarkedVirtual k := by simp
    rw [← feedbackMarkedTrajectory_map_zero lam hlam0 hlam k] at h
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h
  have hμ : ((expMeasure (totalJumpRate lam k)).prod ν).map (firstHoldAssemble k) = μ := by
    rw [← feedbackMarkedTrajectory_first_wait_product lam hlam0 hlam k,
      Measure.map_map (measurable_firstHoldAssemble k) (by fun_prop)]
    calc
      _ = μ.map id := Measure.map_congr (hzero.mono fun w hw ↦ firstHoldAssemble_extract k w hw)
      _ = μ := Measure.map_id
  have hocc := measurable_firstHoldOccupation k hf
  have hprod : Measurable (fun p : ℝ × (UnitMark × ℤ) × FeedbackCellPath ↦
      f (firstHoldAssemble k p)) := hf.comp (measurable_firstHoldAssemble k)
  have hres : Measurable (fun w : FeedbackCellPath ↦
      ∫⁻ a in Ico 0 (w 1).1, f (feedbackMarkedResidual w a) ∂volume) := by
    simp_rw [← lintegral_indicator measurableSet_Ico]
    have hS : MeasurableSet {p : FeedbackCellPath × ℝ | p.2 ∈ Ico 0 (p.1 1).1} := by
      exact (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd ((measurable_pi_apply 1).comp measurable_fst).fst)
    exact ((hf.comp measurable_feedbackMarkedResidual).indicator hS).lintegral_prod_right'
  change (∫⁻ w, ∫⁻ a in Ico 0 (w 1).1, f (feedbackMarkedResidual w a) ∂volume ∂μ) =
    (ENNReal.ofReal (totalJumpRate lam k))⁻¹ * ∫⁻ w, f w ∂μ
  rw [← hμ, lintegral_map hres (measurable_firstHoldAssemble k),
    lintegral_map hf (measurable_firstHoldAssemble k)]
  simp_rw [feedbackMarkedResidual_assemble]
  change (∫⁻ p, ∫⁻ a in Ico 0 p.1,
    f (firstHoldAssemble k (p.1 - a, p.2)) ∂volume
      ∂(expMeasure (totalJumpRate lam k)).prod ν) = _
  rw [lintegral_prod _ hocc.aemeasurable,
    lintegral_lintegral_swap hocc.aemeasurable]
  calc
    _ = ∫⁻ p, (ENNReal.ofReal (totalJumpRate lam k))⁻¹ *
        ∫⁻ t, f (firstHoldAssemble k (t, p)) ∂expMeasure (totalJumpRate lam k) ∂ν := by
      apply lintegral_congr
      intro p
      exact lintegral_exponential_residual (totalJumpRate_pos hlam0 hlam k)
        (hprod.comp (measurable_id.prodMk measurable_const))
    _ = (ENNReal.ofReal (totalJumpRate lam k))⁻¹ *
        ∫⁻ p, f (firstHoldAssemble k p) ∂(expMeasure (totalJumpRate lam k)).prod ν := by
      rw [lintegral_const_mul _ (hprod.lintegral_prod_left'),
        ← lintegral_prod_symm _ hprod.aemeasurable]

end OTSelector.Limit
