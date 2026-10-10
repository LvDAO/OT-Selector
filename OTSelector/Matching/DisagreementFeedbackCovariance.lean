import OTSelector.Matching.DisagreementFeedbackLabels
import OTSelector.Limit.FeedbackRoofFlow

/-!
# Covariance of the actual raw disagreement permutation

The actual roof flow reindexes `(j,n)` as `(j-k,n)`, where `k` is its new containing
cell. This preserves active labels, translates their marked locations, and forces
conjugacy of the scene partner permutation by the actual edge relation.
-/

open Function Set MeasureTheory
open scoped Classical ENNReal

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

/-- The exact raw event-label reindexing induced by the actual roof flow. -/
noncomputable def feedbackRoofLabelShift (a : ℝ) (p : FeedbackCellSequence × ℝ) :
    Equiv.Perm (ℤ × ℕ) :=
  Equiv.prodCongr (Equiv.addRight (-feedbackCellIndex p.1 (p.2 + a))) (Equiv.refl ℕ)

@[simp]
theorem feedbackRoofLabelShift_apply (a : ℝ) (p : FeedbackCellSequence × ℝ) (i : ℤ × ℕ) :
    feedbackRoofLabelShift a p i = (i.1 + -feedbackCellIndex p.1 (p.2 + a), i.2) := rfl

theorem feedbackRoofLabelShift_active (a : ℝ) (p : FeedbackCellSequence × ℝ)
    (d : ℤ) (i : ℤ × ℕ) :
    feedbackCellEventActive (feedbackRoofFlow a p).1 d (feedbackRoofLabelShift a p i) ↔
      feedbackCellEventActive p.1 d i := by
  change feedbackCellEventActive (IIDShift.shift (feedbackCellIndex p.1 (p.2 + a)) p.1)
    d (i.1 + -feedbackCellIndex p.1 (p.2 + a), i.2) ↔ _
  rw [feedbackCellEventActive_shift]
  simp only [neg_add_cancel_right, Prod.eta]

theorem feedbackRoofLabelShift_point (a : ℝ) (p : FeedbackCellSequence × ℝ)
    (i : ℤ × ℕ) :
    feedbackRootedEventPoint (feedbackRoofFlow a p) (feedbackRoofLabelShift a p i) =
      ((feedbackRootedEventPoint p i).1 - a, (feedbackRootedEventPoint p i).2) := by
  unfold feedbackRootedEventPoint
  rw [feedbackRoofLabelShift_apply]
  change Configuration.pointTranslation (-(p.2 + a - feedbackCellRoot p.1
    (feedbackCellIndex p.1 (p.2 + a))))
    (feedbackCellEventPoint (IIDShift.shift (feedbackCellIndex p.1 (p.2 + a)) p.1)
      (i.1 + -feedbackCellIndex p.1 (p.2 + a), i.2)) = _
  rw [feedbackCellEventPoint_shift]
  simp only [neg_add_cancel_right, Prod.eta, Configuration.pointTranslation_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

section Scenes

variable (a : ℝ) (p : FeedbackCellSequence × ℝ) (scene₁ scene₂ : MatchingScene)
    (hp₁ : scene₁.IsSimplePerfectMatching) (hp₂ : scene₂.IsSimplePerfectMatching)
    (hp₁' : (scene₁.reroot a).IsSimplePerfectMatching)
    (hp₂' : (scene₂.reroot a).IsSimplePerfectMatching)
    (hs₁ : scene₁.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht₁ : scene₁.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (hs₂ : scene₂.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht₂ : scene₂.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (hs₁' : (scene₁.reroot a).source = LocalConfiguration.reroot (feedbackRoofFlow a p).2
      (feedbackConcatenatedSource (feedbackRoofFlow a p).1))
    (ht₁' : (scene₁.reroot a).target = LocalConfiguration.reroot (feedbackRoofFlow a p).2
      (feedbackConcatenatedTarget (feedbackRoofFlow a p).1))
    (hs₂' : (scene₂.reroot a).source = LocalConfiguration.reroot (feedbackRoofFlow a p).2
      (feedbackConcatenatedSource (feedbackRoofFlow a p).1))
    (ht₂' : (scene₂.reroot a).target = LocalConfiguration.reroot (feedbackRoofFlow a p).2
      (feedbackConcatenatedTarget (feedbackRoofFlow a p).1))

/-- One partner step is covariant because both actual edges reroot together. -/
theorem feedbackSceneRawPartner_roofFlow (i : ℤ × ℕ) :
    feedbackSceneRawPartner (feedbackRoofFlow a p) (scene₁.reroot a) (scene₂.reroot a)
      hp₁' hp₂' hs₁' ht₁' hs₂' ht₂' (feedbackRoofLabelShift a p i) =
        feedbackRoofLabelShift a p
          (feedbackSceneRawPartner p scene₁ scene₂ hp₁ hp₂ hs₁ ht₁ hs₂ ht₂ i) := by
  let j := feedbackSceneRawPartner p scene₁ scene₂ hp₁ hp₂ hs₁ ht₁ hs₂ ht₂ i
  have hold := (feedbackSceneRawPartner_eq_iff p scene₁ scene₂ hp₁ hp₂ hs₁ ht₁ hs₂ ht₂ i j).mp rfl
  apply (feedbackSceneRawPartner_eq_iff (feedbackRoofFlow a p) (scene₁.reroot a)
    (scene₂.reroot a) hp₁' hp₂' hs₁' ht₁' hs₂' ht₂' _ _).mpr
  rcases hold with ⟨hi, hij⟩ | ⟨hi, hj, k, hk, he₁, he₂⟩
  · exact Or.inl ⟨(feedbackRoofLabelShift_active a p 1 i).not.mpr hi,
      congrArg (feedbackRoofLabelShift a p) hij⟩
  · refine Or.inr ⟨(feedbackRoofLabelShift_active a p 1 i).mpr hi,
      (feedbackRoofLabelShift_active a p 1 j).mpr hj, feedbackRoofLabelShift a p k,
      (feedbackRoofLabelShift_active a p (-1) k).mpr hk, ?_, ?_⟩
    · rw [feedbackRoofLabelShift_point, feedbackRoofLabelShift_point,
        MatchingScene.edge_multiplicity_reroot]
      exact he₁
    · rw [feedbackRoofLabelShift_point, feedbackRoofLabelShift_point,
        MatchingScene.edge_multiplicity_reroot]
      exact he₂

/-- Every integer-orbit position obeys the actual spatial translation law. -/
theorem feedbackSceneRawPartner_orbit_roofFlow (i : ℤ × ℕ) (n : ℤ) :
    partnerOrbitPositions
      (feedbackSceneRawPartner (feedbackRoofFlow a p) (scene₁.reroot a) (scene₂.reroot a)
        hp₁' hp₂' hs₁' ht₁' hs₂' ht₂')
      (fun j ↦ (feedbackRootedEventPoint (feedbackRoofFlow a p) j).1)
      (feedbackRoofLabelShift a p i) n =
        -a + partnerOrbitPositions
          (feedbackSceneRawPartner p scene₁ scene₂ hp₁ hp₂ hs₁ ht₁ hs₂ ht₂)
          (fun j ↦ (feedbackRootedEventPoint p j).1) i n := by
  apply partnerOrbitPositions_covariant _ _ _ _ (feedbackRoofLabelShift a p) (-a)
  · intro j
    rw [feedbackRoofLabelShift_point]
    dsimp
    ring
  · exact feedbackSceneRawPartner_roofFlow a p scene₁ scene₂ hp₁ hp₂ hp₁' hp₂'
      hs₁ ht₁ hs₂ ht₂ hs₁' ht₁' hs₂' ht₂'

end Scenes

/-- Fixed inactive labels do not change any genuine integer iterate. -/
theorem feedbackRawPartnerPermutation_zpow_active (w : FeedbackCellSequence)
    (σ₁ σ₂ : FeedbackEventLabel w 1 ≃ FeedbackEventLabel w (-1))
    (i : FeedbackEventLabel w 1) (n : ℤ) :
    (feedbackRawPartnerPermutation w σ₁ σ₂ ^ n) i =
      (((feedbackLabelMatching w σ₁).partnerPermutation (feedbackLabelMatching w σ₂) ^ n) i).val := by
  let q := (feedbackLabelMatching w σ₁).partnerPermutation (feedbackLabelMatching w σ₂)
  change ((Equiv.Perm.subtypeCongrHom (feedbackCellEventActive w 1) (q, 1)) ^ n) i = _
  rw [← map_zpow]
  simp [Equiv.Perm.subtypeCongrHom_apply, Equiv.Perm.subtypeCongr.left_apply_subtype, q]

end OTSelector.Matching
