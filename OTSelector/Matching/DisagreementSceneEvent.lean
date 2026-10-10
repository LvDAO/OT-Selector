import OTSelector.Matching.FeedbackSceneJoiningFlow
import OTSelector.Matching.DisagreementSceneReroot
import OTSelector.Limit.FeedbackMarkIntensity

/-!
# The actual disagreement event and fixed non-event cuts
-/

open Set Function MeasureTheory
open scoped Classical ENNReal

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

/-- Every fixed spatial location has zero actual source and target counting mass. -/
theorem ae_feedbackStationary_zero_count_at {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) (x : ℝ) :
    ∀ᵐ e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam,
      LocalConfiguration.countingMeasure e.source ({x} ×ˢ univ) = 0 ∧
      LocalConfiguration.countingMeasure e.target ({x} ×ˢ univ) = 0 := by
  have hA : MeasurableSet ({x} ×ˢ (univ : Set UnitMark)) :=
    (measurableSet_singleton x).prod MeasurableSet.univ
  have hsrc : Measurable (fun e : FeedbackEnvironment ↦ LocalConfiguration.countingMeasure e.source) :=
    LocalConfiguration.measurable_countingMeasure.comp FeedbackEnvironment.measurable_source
  have htgt : Measurable (fun e : FeedbackEnvironment ↦ LocalConfiguration.countingMeasure e.target) :=
    LocalConfiguration.measurable_countingMeasure.comp FeedbackEnvironment.measurable_target
  have hs : (∫⁻ e, LocalConfiguration.countingMeasure e.source ({x} ×ˢ univ)
      ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam) = 0 := by
    rw [← Measure.bind_apply hA hsrc.aemeasurable, feedbackStationary_source_intensity hlam0 hlam,
      Measure.prod_prod, measure_singleton, zero_mul]
  have ht : (∫⁻ e, LocalConfiguration.countingMeasure e.target ({x} ×ˢ univ)
      ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam) = 0 := by
    rw [← Measure.bind_apply hA htgt.aemeasurable, feedbackStationary_target_intensity hlam0 hlam,
      Measure.prod_prod, measure_singleton, zero_mul]
  exact ((lintegral_eq_zero_iff' ((Measure.measurable_coe hA).comp hsrc).aemeasurable).mp hs).and
    ((lintegral_eq_zero_iff' ((Measure.measurable_coe hA).comp htgt).aemeasurable).mp ht)

/-- A zero spatial-slice count excludes every actual marked atom at that location. -/
theorem atom_coordinate_ne_of_zero_count (config : LocalConfiguration matchingPointBase)
    (x : ℝ) (hzero : LocalConfiguration.countingMeasure config ({x} ×ˢ univ) = 0)
    (z : MatchingPoint) (hz : LocalConfiguration.multiplicity config z ≠ 0) : z.1 ≠ x := by
  intro heq
  have hsub : ({z} : Set MatchingPoint) ⊆ {x} ×ˢ univ := by
    intro y hy
    rcases mem_singleton_iff.mp hy with rfl
    exact ⟨heq, mem_univ _⟩
  have hc : LocalConfiguration.countingMeasure config {z} = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq hzero) zero_le
  apply hz
  simpa only [LocalConfiguration.countingMeasure_singleton, Nat.cast_eq_zero] using hc

end OTSelector.Matching
