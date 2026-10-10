import OTSelector.Matching.DisagreementFeedbackCovariance
import OTSelector.Limit.FeedbackMarkIntensity

/-!
# Actual feedback intensity excludes one-sided disagreement orbits

The source-count bound is derived from the true stationary roof law. Actual scene
edge covariance and measurable raw labels then instantiate the proved mass transport.
The carrier may be the full-measure good subtype of the actual scene/roof joining.
-/

open Function Set MeasureTheory
open scoped Classical ENNReal

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

/-- Active raw labels have finite intensity under any lift with the actual roof marginal. -/
theorem lintegral_feedback_active_source_count_lt_top {Ω : Type*} [MeasurableSpace Ω]
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam < 1 / 2)
    (μ : Measure Ω) (p : Ω → FeedbackCellSequence × ℝ) (hp : Measurable p)
    (hroof : μ.map p = feedbackStationaryRoofLaw lam hlam0 hlam) :
    (∫⁻ ω, ∑' i : ℤ × ℕ,
      if feedbackCellEventActive (p ω).1 1 i ∧
        (feedbackRootedEventPoint (p ω) i).1 ∈ Icc (-1) 1 then (1 : ℝ≥0∞) else 0 ∂μ) < ∞ := by
  let A : Set MatchingPoint := Icc (-1) 1 ×ˢ univ
  have hA : MeasurableSet A := measurableSet_Icc.prod MeasurableSet.univ
  let F : FeedbackEnvironment → ℝ≥0∞ := fun e ↦ LocalConfiguration.countingMeasure e.source A
  have hF : Measurable F := (Measure.measurable_coe hA).comp
    (LocalConfiguration.measurable_countingMeasure.comp FeedbackEnvironment.measurable_source)
  have henv : μ.map (fun ω ↦ feedbackRoofEnvironment lam (p ω)) =
      feedbackStationaryEnvironmentLaw lam hlam0 hlam := by
    rw [← feedbackStationaryRoofLaw_environment_map lam hlam0 hlam, ← hroof,
      Measure.map_map (measurable_feedbackRoofEnvironment lam) hp]
    rfl
  calc
    _ = ∫⁻ ω, F (feedbackRoofEnvironment lam (p ω)) ∂μ := by
      apply lintegral_congr
      intro ω
      dsimp only [F, A, feedbackRoofEnvironment, FeedbackEnvironment.reroot,
        feedbackConcatenatedEnvironment, feedbackConcatenatedSource]
      refine Eq.trans ?_ (feedbackRootedEventPoint_count (p ω) 1 (Icc (-1) 1) measurableSet_Icc).symm
      apply tsum_congr
      intro i
      split_ifs <;> rfl
    _ = ∫⁻ e, F e ∂feedbackStationaryEnvironmentLaw lam hlam0 hlam := by
      rw [← henv]
      exact (lintegral_map hF ((measurable_feedbackRoofEnvironment lam).comp hp)).symm
    _ = ((volume : Measure ℝ).prod (volume : Measure UnitMark)) A := by
      rw [← feedbackStationary_source_intensity hlam0 hlam]
      exact (Measure.bind_apply hA (LocalConfiguration.measurable_countingMeasure.comp
        FeedbackEnvironment.measurable_source).aemeasurable).symm
    _ < ∞ := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_lt_top measure_Icc_lt_top (measure_lt_top _ _)

section ScenePair

variable {Ω : Type*} [MeasurableSpace Ω]
    (p : Ω → FeedbackCellSequence × ℝ) (scene₁ scene₂ : Ω → MatchingScene)
    (hp₁ : ∀ ω, (scene₁ ω).IsSimplePerfectMatching)
    (hp₂ : ∀ ω, (scene₂ ω).IsSimplePerfectMatching)
    (hs₁ : ∀ ω, (scene₁ ω).source =
      LocalConfiguration.reroot (p ω).2 (feedbackConcatenatedSource (p ω).1))
    (ht₁ : ∀ ω, (scene₁ ω).target =
      LocalConfiguration.reroot (p ω).2 (feedbackConcatenatedTarget (p ω).1))
    (hs₂ : ∀ ω, (scene₂ ω).source =
      LocalConfiguration.reroot (p ω).2 (feedbackConcatenatedSource (p ω).1))
    (ht₂ : ∀ ω, (scene₂ ω).target =
      LocalConfiguration.reroot (p ω).2 (feedbackConcatenatedTarget (p ω).1))
    (hp : Measurable p) (hscene₁ : Measurable scene₁) (hscene₂ : Measurable scene₂)

include hp hscene₁ hscene₂

/-- The true stationary roof and simultaneous scene rerooting exclude both one-sided
infinite orbit types. No source-intensity or orbit-exclusion conclusion is an input. -/
theorem ae_feedbackSceneRawPartner_no_oneSidedOrbit {lam : ℝ}
    (hlam0 : 0 < lam) (hlam : lam < 1 / 2) (μ : Measure Ω)
    (hroof : μ.map p = feedbackStationaryRoofLaw lam hlam0 hlam)
    (shift : ℝ → Ω → Ω) (hshift : ∀ a, MeasurePreserving (shift a) μ μ)
    (hflow : ∀ a, ∀ᵐ ω ∂μ,
      p (shift a ω) = feedbackRoofFlow (-a) (p ω) ∧
      scene₁ (shift a ω) = (scene₁ ω).reroot (-a) ∧
      scene₂ (shift a ω) = (scene₂ ω).reroot (-a)) :
    ∀ᵐ ω ∂μ, ∀ i,
      ¬ LowerAnchoredOrbit
        (feedbackSceneRawPartner (p ω) (scene₁ ω) (scene₂ ω)
          (hp₁ ω) (hp₂ ω) (hs₁ ω) (ht₁ ω) (hs₂ ω) (ht₂ ω))
        (fun j ↦ (feedbackRootedEventPoint (p ω) j).1) i ∧
      ¬ LowerAnchoredOrbit
        (feedbackSceneRawPartner (p ω) (scene₁ ω) (scene₂ ω)
          (hp₁ ω) (hp₂ ω) (hs₁ ω) (ht₁ ω) (hs₂ ω) (ht₂ ω))
        (fun j ↦ -(feedbackRootedEventPoint (p ω) j).1) i := by
  let R := fun ω ↦ feedbackSceneRawPartner (p ω) (scene₁ ω) (scene₂ ω)
    (hp₁ ω) (hp₂ ω) (hs₁ ω) (ht₁ ω) (hs₂ ω) (ht₂ ω)
  let x := fun ω j ↦ (feedbackRootedEventPoint (p ω) j).1
  have hm : ∀ i n, Measurable (fun ω ↦ partnerOrbitPositions (R ω) (x ω) i n) :=
    measurable_feedbackSceneRawPartner_orbit p scene₁ scene₂ hp₁ hp₂ hs₁ ht₁ hs₂ ht₂
      hp hscene₁ hscene₂
  apply ae_not_oneSidedAnchoredOrbit_active R x hm
    (fun ω i ↦ feedbackCellEventActive (p ω).1 1 i) μ shift hshift
  · exact ae_of_all μ fun ω i hi ↦ feedbackRawPartnerPermutation_inactive _ _ _ i hi
  · intro a
    filter_upwards [hflow a] with ω hω
    rcases hω with ⟨hr, h₁, h₂⟩
    refine ⟨feedbackRoofLabelShift (-a) (p ω), ?_, ?_⟩
    · intro i
      rw [hr]
      exact feedbackRoofLabelShift_active (-a) (p ω) 1 i
    · intro i _ n
      have hp₁' : ((scene₁ ω).reroot (-a)).IsSimplePerfectMatching := h₁ ▸ hp₁ (shift a ω)
      have hp₂' : ((scene₂ ω).reroot (-a)).IsSimplePerfectMatching := h₂ ▸ hp₂ (shift a ω)
      have hs₁' : ((scene₁ ω).reroot (-a)).source =
          LocalConfiguration.reroot (feedbackRoofFlow (-a) (p ω)).2
            (feedbackConcatenatedSource (feedbackRoofFlow (-a) (p ω)).1) := by
        simpa only [hr, h₁] using hs₁ (shift a ω)
      have ht₁' : ((scene₁ ω).reroot (-a)).target =
          LocalConfiguration.reroot (feedbackRoofFlow (-a) (p ω)).2
            (feedbackConcatenatedTarget (feedbackRoofFlow (-a) (p ω)).1) := by
        simpa only [hr, h₁] using ht₁ (shift a ω)
      have hs₂' : ((scene₂ ω).reroot (-a)).source =
          LocalConfiguration.reroot (feedbackRoofFlow (-a) (p ω)).2
            (feedbackConcatenatedSource (feedbackRoofFlow (-a) (p ω)).1) := by
        simpa only [hr, h₂] using hs₂ (shift a ω)
      have ht₂' : ((scene₂ ω).reroot (-a)).target =
          LocalConfiguration.reroot (feedbackRoofFlow (-a) (p ω)).2
            (feedbackConcatenatedTarget (feedbackRoofFlow (-a) (p ω)).1) := by
        simpa only [hr, h₂] using ht₂ (shift a ω)
      simpa only [R, x, hr, h₁, h₂, neg_neg] using
        feedbackSceneRawPartner_orbit_roofFlow (-a) (p ω) (scene₁ ω) (scene₂ ω)
          (hp₁ ω) (hp₂ ω) hp₁' hp₂' (hs₁ ω) (ht₁ ω) (hs₂ ω) (ht₂ ω)
          hs₁' ht₁' hs₂' ht₂' i n
  · exact lintegral_feedback_active_source_count_lt_top hlam0 hlam μ p hp hroof

end ScenePair

end OTSelector.Matching
