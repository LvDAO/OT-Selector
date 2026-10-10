import OTSelector.Limit.FeedbackStationaryFutureReadout
import OTSelector.PointProcess.FeedbackReturnPalm

/-!
# The actual cell roof as an occupation measure on complete future paths

Concatenating the positive cells preserves the distinguished return roof almost everywhere and
has the original marked trajectory law. Thus the actual iid cell suspension pushes forward to
the first-return occupation measure of that complete trajectory.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OTSelector.Limit

open PointProcess

/-- Positive concatenation preserves the roof length under the actual iid cell base. -/
theorem feedbackConcatPositiveCellPaths_length_ae (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ ω ∂feedbackCellBase lam hlam0 hlam,
      feedbackCellLength (feedbackConcatPositiveCellPaths ω) = feedbackCellLength (ω 0) := by
  filter_upwards [feedbackCellBase_configuration_good hlam0 hlam] with ω hω
  exact feedbackConcatPositiveCellPaths_length ω (fun j ↦ (hω.2 j).1) (hω.2 0).2

/-- The unnormalized actual cell suspension is the first-return occupation of the original
complete marked trajectory after positive concatenation. -/
theorem feedbackOccupationRoof_map_concatPositive (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (renewalRoofMeasure (feedbackCellBase lam hlam0 hlam)
      (fun ω ↦ feedbackCellLength (ω 0))).map
        (fun p ↦ (feedbackConcatPositiveCellPaths p.1, p.2)) =
      ((feedbackMarkedTrajectory lam hlam0 hlam 0).prod volume).restrict
        {p : FeedbackCellPath × ℝ | 0 ≤ p.2 ∧ p.2 < feedbackCellLength p.1} := by
  let c : FeedbackCellSequence × ℝ → FeedbackCellPath × ℝ :=
    fun p ↦ (feedbackConcatPositiveCellPaths p.1, p.2)
  have hc : Measurable c := measurable_feedbackConcatPositiveCellPaths.prodMap measurable_id
  have hprod : ((feedbackCellBase lam hlam0 hlam).prod volume).map c =
      (feedbackMarkedTrajectory lam hlam0 hlam 0).prod volume := by
    change ((feedbackCellBase lam hlam0 hlam).prod volume).map
      (Prod.map feedbackConcatPositiveCellPaths id) = _
    rw [← Measure.map_prod_map _ _ measurable_feedbackConcatPositiveCellPaths measurable_id,
      feedbackConcatPositiveCellPaths_map, Measure.map_id]
  have hS : MeasurableSet {p : FeedbackCellPath × ℝ |
      0 ≤ p.2 ∧ p.2 < feedbackCellLength p.1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_feedbackCellLength.comp measurable_fst))
  have hroof : {p : FeedbackCellSequence × ℝ |
      0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)} =ᵐ[
        (feedbackCellBase lam hlam0 hlam).prod volume]
      c ⁻¹' {p : FeedbackCellPath × ℝ | 0 ≤ p.2 ∧ p.2 < feedbackCellLength p.1} := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (feedbackConcatPositiveCellPaths_length_ae lam hlam0 hlam)] with p hp
    change (0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)) =
      (0 ≤ p.2 ∧ p.2 < feedbackCellLength (feedbackConcatPositiveCellPaths p.1))
    rw [hp]
  change (((feedbackCellBase lam hlam0 hlam).prod volume).restrict _).map c = _
  rw [Measure.restrict_congr_set hroof, ← Measure.restrict_map hc hS, hprod]

/-- The actual normalized return roof pushes forward to normalized first-return occupation
of the original complete marked trajectory. -/
theorem feedbackReturnRoofLaw_map_concatPositive (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    (feedbackReturnRoofLaw lam hlam0 hlam).map
      (fun p ↦ (feedbackConcatPositiveCellPaths p.1, p.2)) =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ •
        ((feedbackMarkedTrajectory lam hlam0 hlam 0).prod volume).restrict
          {p : FeedbackCellPath × ℝ | 0 ≤ p.2 ∧ p.2 < feedbackCellLength p.1} := by
  rw [feedbackReturnRoofLaw, Measure.map_smul, feedbackOccupationRoof_map_concatPositive]

/-- Nonnegative observations of the entire future and the location in its first return cell
can be integrated directly against the original trajectory law. -/
theorem lintegral_feedbackReturnRoofLaw_concatPositive (lam : ℝ) (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) {F : FeedbackCellPath × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F (feedbackConcatPositiveCellPaths p.1, p.2)
        ∂feedbackReturnRoofLaw lam hlam0 hlam =
      (ENNReal.ofReal (feedbackCellMean lam hlam0 hlam))⁻¹ *
        ∫⁻ w, ∫⁻ t in Ico 0 (feedbackCellLength w), F (w, t) ∂volume
          ∂feedbackMarkedTrajectory lam hlam0 hlam 0 := by
  have hc : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      (feedbackConcatPositiveCellPaths p.1, p.2)) :=
    measurable_feedbackConcatPositiveCellPaths.prodMap measurable_id
  have hS : MeasurableSet {p : FeedbackCellPath × ℝ |
      0 ≤ p.2 ∧ p.2 < feedbackCellLength p.1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_feedbackCellLength.comp measurable_fst))
  rw [← lintegral_map hF hc, feedbackReturnRoofLaw_map_concatPositive,
    lintegral_smul_measure, smul_eq_mul, ← lintegral_indicator hS,
    lintegral_prod _ (hF.indicator hS).aemeasurable]
  congr 1
  apply lintegral_congr
  intro w
  rw [← lintegral_indicator (measurableSet_Ico (a := (0 : ℝ))
    (b := feedbackCellLength w))]
  rfl

end OTSelector.Limit
