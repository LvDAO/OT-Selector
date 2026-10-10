import OTSelector.Limit.FeedbackMarkedTrajectory
import OTSelector.Limit.FeedbackRegenerationReturnLength
import Mathlib.Probability.Independence.InfinitePi

/-!
# Actual return-cell lengths and the independent cell base

Each cell reads the first positive return segment of an actual marked trajectory from zero.
The roof is the physical return time, including its initial zero hold. Its positive finite mean
is derived from the proved trajectory moments, rather than assumed as a renewal input.
-/

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal BigOperators Topology

namespace OTSelector.Limit

/-- The full marked path used to read one first-return cell. -/
abbrev FeedbackCellPath := ℕ → FeedbackMarkedStep

/-- Physical duration of the first return cell; the exceptional infinite-duration branch is null. -/
noncomputable def feedbackCellLength (w : FeedbackCellPath) : ℝ :=
  (feedbackReturnLength (feedbackMarkedTrajectoryProjection w)).toReal

@[fun_prop]
theorem measurable_feedbackCellLength : Measurable feedbackCellLength :=
  (measurable_feedbackReturnLength.comp measurable_feedbackMarkedTrajectoryProjection).ennreal_toReal

theorem feedbackCellLength_nonneg (w : FeedbackCellPath) : 0 ≤ feedbackCellLength w :=
  ENNReal.toReal_nonneg

theorem feedbackMarkedTrajectory_waits_positive {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (k : ℤ) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam k, ∀ i, 0 < (w (i + 1)).1 := by
  have h := feedbackHoldingJumpTrajectory_waits_positive hlam0 hlam k
  rw [← feedbackMarkedTrajectory_map hlam0 hlam k] at h
  exact ae_of_ae_map measurable_feedbackMarkedTrajectoryProjection.aemeasurable h

theorem feedbackCellLength_positive {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam 0, 0 < feedbackCellLength w := by
  have hfin := feedbackReturnLength_finite hlam0 hlam
  rw [← feedbackMarkedTrajectory_map hlam0 hlam 0] at hfin
  have hfin' := ae_of_ae_map measurable_feedbackMarkedTrajectoryProjection.aemeasurable hfin
  filter_upwards [hfin', feedbackMarkedTrajectory_waits_positive hlam0 hlam 0] with w hf hw
  apply ENNReal.toReal_pos_iff.mpr
  refine ⟨?_, hf⟩
  exact (ENNReal.ofReal_pos.mpr (hw 0)).trans_le
    (le_self_add : ENNReal.ofReal (w 1).1 ≤
      feedbackReturnLength (feedbackMarkedTrajectoryProjection w))

/-- All integer cell-length moments remain finite after passing to the actual marked law. -/
theorem feedbackCellLength_lintegral_moments {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (p : ℕ) :
    (∫⁻ w, feedbackReturnLength (feedbackMarkedTrajectoryProjection w) ^ p
      ∂feedbackMarkedTrajectory lam hlam0 hlam 0) < ∞ := by
  have h := feedbackReturnLength_moments hlam0 hlam p
  rw [← feedbackMarkedTrajectory_map hlam0 hlam 0,
    lintegral_map (measurable_feedbackReturnLength.pow_const p)
      measurable_feedbackMarkedTrajectoryProjection] at h
  exact h

/-- The real cell roof is integrable under the actual marked first-return construction. -/
theorem integrable_feedbackCellLength {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    Integrable feedbackCellLength (feedbackMarkedTrajectory lam hlam0 hlam 0) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_feedbackReturnLength.comp measurable_feedbackMarkedTrajectoryProjection).aemeasurable
  simpa only [pow_one, Function.comp_def] using
    (feedbackCellLength_lintegral_moments hlam0 hlam 1).ne

/-- Mean physical length of an actual return cell, used to normalize spatial occupation. -/
noncomputable def feedbackCellMean (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) : ℝ :=
  ∫ w, feedbackCellLength w ∂feedbackMarkedTrajectory lam hlam0 hlam 0

theorem feedbackCellMean_pos {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    0 < feedbackCellMean lam hlam0 hlam := by
  apply (integral_pos_iff_support_of_nonneg feedbackCellLength_nonneg
    (integrable_feedbackCellLength hlam0 hlam)).mpr
  have hs : ∀ᵐ w ∂feedbackMarkedTrajectory lam hlam0 hlam 0,
      w ∈ Function.support feedbackCellLength :=
    (feedbackCellLength_positive hlam0 hlam).mono (fun _ hw ↦ hw.ne')
  have heq : Function.support feedbackCellLength =ᵐ[feedbackMarkedTrajectory lam hlam0 hlam 0]
      Set.univ := hs.mono (fun w hw ↦ propext
        ⟨fun _ ↦ Set.mem_univ w, fun _ ↦ hw⟩)
  rw [measure_congr heq, measure_univ]
  exact zero_lt_one

/-- Independent actual path coordinates; only the first-return segment of each coordinate is used. -/
abbrev FeedbackCellSequence := ℤ → FeedbackCellPath

noncomputable def feedbackCellBase (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    Measure FeedbackCellSequence :=
  Measure.infinitePi (fun _ : ℤ ↦ feedbackMarkedTrajectory lam hlam0 hlam 0)

instance feedbackCellBase_isProbability {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    IsProbabilityMeasure (feedbackCellBase lam hlam0 hlam) := by
  unfold feedbackCellBase
  infer_instance

theorem feedbackCellBase_eval_measurePreserving {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (j : ℤ) :
    MeasurePreserving (fun w : FeedbackCellSequence ↦ w j)
      (feedbackCellBase lam hlam0 hlam) (feedbackMarkedTrajectory lam hlam0 hlam 0) :=
  measurePreserving_eval_infinitePi _ j

theorem feedbackCellBase_lengths_positive {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ j : ℤ, 0 < feedbackCellLength (w j) := by
  rw [ae_all_iff]
  intro j
  have h := feedbackCellLength_positive hlam0 hlam
  rw [← (feedbackCellBase_eval_measurePreserving hlam0 hlam j).map_eq] at h
  exact ae_of_ae_map (measurable_pi_apply j).aemeasurable h

theorem feedbackCellBase_lengths_iIndep {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    iIndepFun (fun j (w : FeedbackCellSequence) ↦ feedbackCellLength (w j))
      (feedbackCellBase lam hlam0 hlam) :=
  iIndepFun_infinitePi (X := fun _ ↦ feedbackCellLength)
    (fun _ ↦ measurable_feedbackCellLength)

theorem integrable_feedbackCellBase_length {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (j : ℤ) :
    Integrable (fun w : FeedbackCellSequence ↦ feedbackCellLength (w j))
      (feedbackCellBase lam hlam0 hlam) :=
  (feedbackCellBase_eval_measurePreserving hlam0 hlam j).integrable_comp_of_integrable
    (integrable_feedbackCellLength hlam0 hlam)

theorem integral_feedbackCellBase_length {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (j : ℤ) :
    (∫ w : FeedbackCellSequence, feedbackCellLength (w j) ∂feedbackCellBase lam hlam0 hlam) =
      feedbackCellMean lam hlam0 hlam := by
  rw [feedbackCellMean, ← (feedbackCellBase_eval_measurePreserving hlam0 hlam j).map_eq,
    integral_map (measurable_pi_apply j).aemeasurable
      measurable_feedbackCellLength.aestronglyMeasurable]

end OTSelector.Limit
