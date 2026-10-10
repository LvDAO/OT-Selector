import OTSelector.Matching.FeedbackConditionalEnergyGap
import OTSelector.Matching.DisagreementPermutation
import OTSelector.PointProcess.MatchingScenePerfect

/-!
# Actual scene matchings read on regenerative event labels

The equivalences below use the singleton masses of the actual concatenated counting measures.
Every partner is read from the scene's edge configuration and then transported to its unique
retained cell label.
-/

open MeasureTheory Set Function
open scoped BigOperators ENNReal Classical

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000

/-- An actual atom of the rerooted concatenation is exactly one retained labelled event. -/
theorem feedbackRerootedPoints_atom_iff (w : FeedbackCellSequence) (u : ℝ)
    (direction : ℤ) (x : MatchingPoint) :
    LocalConfiguration.multiplicity
        (LocalConfiguration.reroot u (feedbackConcatenatedPoints direction w)) x ≠ 0 ↔
      ∃ i : FeedbackEventLabel w direction,
        Configuration.pointTranslation (-u) (feedbackCellEventPoint w i) = x := by
  have hcast : LocalConfiguration.multiplicity
      (LocalConfiguration.reroot u (feedbackConcatenatedPoints direction w)) x ≠ 0 ↔
      (LocalConfiguration.multiplicity
      (LocalConfiguration.reroot u (feedbackConcatenatedPoints direction w)) x : ℝ≥0∞) ≠ 0 := by
    simp
  rw [hcast, ← LocalConfiguration.countingMeasure_singleton,
    LocalConfiguration.countingMeasure_reroot,
    Measure.map_apply (Configuration.pointTranslation (-u)).measurable (measurableSet_singleton x)]
  have hpre : Configuration.pointTranslation (-u) ⁻¹' {x} =
      {(Configuration.pointTranslation (-u)).symm x} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff]
    exact (Configuration.pointTranslation (-u)).toEquiv.eq_symm_apply.symm
  rw [hpre, feedbackConcatenatedPoints_atom_iff]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨⟨i, hi⟩, hx ▸ (Configuration.pointTranslation (-u)).apply_symm_apply x⟩
  · rintro ⟨i, hx⟩
    exact ⟨i, i.property,
      (Configuration.pointTranslation (-u)).toEquiv.eq_symm_apply.mpr hx⟩

/-- The concrete bijection from retained cell events to actual atoms of an equal configuration. -/
noncomputable def feedbackEventAtomEquiv (w : FeedbackCellSequence) (u : ℝ) (direction : ℤ)
    (config : LocalConfiguration matchingPointBase)
    (hconfig : config = LocalConfiguration.reroot u (feedbackConcatenatedPoints direction w)) :
    FeedbackEventLabel w direction ≃ {x : MatchingPoint // LocalConfiguration.multiplicity config x ≠ 0} :=
  Equiv.ofBijective (fun i ↦ ⟨Configuration.pointTranslation (-u) (feedbackCellEventPoint w i), by
    rw [hconfig]
    exact (feedbackRerootedPoints_atom_iff w u direction _).mpr ⟨i, rfl⟩⟩) (by
    constructor
    · intro i j hij
      apply Subtype.ext
      have hpoint := (Configuration.pointTranslation (-u)).injective (congrArg Subtype.val hij)
      exact feedbackCellEventPoint_fst_injective i.property.1 i.property.2.1 j.property.2.1
        (congrArg Prod.fst hpoint)
    · intro x
      have hx := x.property
      simp only [hconfig] at hx
      obtain ⟨i, hi⟩ := (feedbackRerootedPoints_atom_iff w u direction x).mp hx
      exact ⟨i, Subtype.ext hi⟩)

@[simp]
theorem feedbackEventAtomEquiv_apply_val (w : FeedbackCellSequence) (u : ℝ) (direction : ℤ)
    (config : LocalConfiguration matchingPointBase)
    (hconfig : config = LocalConfiguration.reroot u (feedbackConcatenatedPoints direction w))
    (i : FeedbackEventLabel w direction) :
    (feedbackEventAtomEquiv w u direction config hconfig i).val =
      Configuration.pointTranslation (-u) (feedbackCellEventPoint w i) := rfl

noncomputable abbrev feedbackSceneSourceEquiv (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1)) :
    FeedbackEventLabel p.1 1 ≃ MatchingScene.SourceAtom scene :=
  feedbackEventAtomEquiv p.1 p.2 1 scene.source hs

noncomputable abbrev feedbackSceneTargetEquiv (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene)
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1)) :
    FeedbackEventLabel p.1 (-1) ≃ MatchingScene.TargetAtom scene :=
  feedbackEventAtomEquiv p.1 p.2 (-1) scene.target ht

/-- Read the actual scene edge relation on its unique source and target event labels. -/
noncomputable def feedbackSceneAssignment (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hperfect : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1)) :
    FeedbackEventLabel p.1 1 ≃ FeedbackEventLabel p.1 (-1) :=
  (feedbackSceneSourceEquiv p scene hs).trans
    ((MatchingScene.atomAssignment hperfect).trans (feedbackSceneTargetEquiv p scene ht).symm)

/-- Transport commutes with the concrete partner relation. -/
theorem feedbackSceneAssignment_partner (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hperfect : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (i : FeedbackEventLabel p.1 1) :
    feedbackSceneTargetEquiv p scene ht (feedbackSceneAssignment p scene hperfect hs ht i) =
      MatchingScene.atomAssignment hperfect (feedbackSceneSourceEquiv p scene hs i) := by
  simp only [feedbackSceneAssignment, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- Every transported pair remains an actual edge of the original scene. -/
theorem feedbackSceneAssignment_edge (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hperfect : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (i : FeedbackEventLabel p.1 1) :
    LocalConfiguration.multiplicity scene.edges
      (Configuration.pointTranslation (-p.2) (feedbackCellEventPoint p.1 i),
        Configuration.pointTranslation (-p.2)
          (feedbackCellEventPoint p.1 (feedbackSceneAssignment p scene hperfect hs ht i))) ≠ 0 := by
  have he := MatchingScene.atomAssignment_edge hperfect (feedbackSceneSourceEquiv p scene hs i)
  rw [← feedbackSceneAssignment_partner p scene hperfect hs ht i] at he
  exact he

/-- Source coordinates differ by exactly the original spatial root. -/
theorem feedbackSceneSourceEquiv_coordinate (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (i : FeedbackEventLabel p.1 1) :
    (feedbackSceneSourceEquiv p scene hs i).val.1 = (feedbackCellEventPoint p.1 i).1 - p.2 := by
  change (feedbackCellEventPoint p.1 i).1 + -p.2 = _
  ring

/-- Partner coordinates are preserved by the same root translation. -/
theorem feedbackSceneAssignment_coordinate (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hperfect : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (i : FeedbackEventLabel p.1 1) :
    (MatchingScene.atomAssignment hperfect (feedbackSceneSourceEquiv p scene hs i)).val.1 =
      (feedbackCellEventPoint p.1 (feedbackSceneAssignment p scene hperfect hs ht i)).1 - p.2 := by
  rw [← feedbackSceneAssignment_partner p scene hperfect hs ht i]
  change (feedbackCellEventPoint p.1 (feedbackSceneAssignment p scene hperfect hs ht i)).1 +
    -p.2 = (feedbackCellEventPoint p.1 (feedbackSceneAssignment p scene hperfect hs ht i)).1 - p.2
  ring

/-- Actual crossing current is unchanged by relabelling and shifts with the spatial root. -/
theorem feedbackSceneAssignment_current (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hperfect : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1)) (x : ℝ) :
    (feedbackLabelMatching p.1 (feedbackSceneAssignment p scene hperfect hs ht)).current x =
      (MatchingScene.spatialMatching hperfect).current (x - p.2) := by
  unfold SpatialMatching.current
  rw [← (feedbackSceneSourceEquiv p scene hs).tsum_eq]
  apply tsum_congr
  intro i
  change crossingSign (feedbackCellEventPoint p.1 i).1
      (feedbackCellEventPoint p.1 (feedbackSceneAssignment p scene hperfect hs ht i)).1 x =
    crossingSign (feedbackSceneSourceEquiv p scene hs i).val.1
      (MatchingScene.atomAssignment hperfect (feedbackSceneSourceEquiv p scene hs i)).val.1 (x - p.2)
  rw [feedbackSceneSourceEquiv_coordinate,
    feedbackSceneAssignment_coordinate p scene hperfect hs ht i]
  simp only [crossingSign, sub_le_sub_iff_right]

/-- The full unsigned energy sum has the same exact relabelling identity. -/
theorem feedbackSceneAssignment_crossingEnergy (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hperfect : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1)) (x : ℝ) :
    (feedbackLabelMatching p.1 (feedbackSceneAssignment p scene hperfect hs ht)).crossingEnergy x =
      (MatchingScene.spatialMatching hperfect).crossingEnergy (x - p.2) := by
  unfold SpatialMatching.crossingEnergy
  rw [← (feedbackSceneSourceEquiv p scene hs).tsum_eq]
  apply tsum_congr
  intro i
  change |(crossingSign (feedbackCellEventPoint p.1 i).1
      (feedbackCellEventPoint p.1 (feedbackSceneAssignment p scene hperfect hs ht i)).1 x : ℝ)| *
      (1 + |(feedbackCellEventPoint p.1 (feedbackSceneAssignment p scene hperfect hs ht i)).1 -
        (feedbackCellEventPoint p.1 i).1|) =
    |(crossingSign (feedbackSceneSourceEquiv p scene hs i).val.1
      (MatchingScene.atomAssignment hperfect (feedbackSceneSourceEquiv p scene hs i)).val.1
      (x - p.2) : ℝ)| *
      (1 + |(MatchingScene.atomAssignment hperfect (feedbackSceneSourceEquiv p scene hs i)).val.1 -
        (feedbackSceneSourceEquiv p scene hs i).val.1|)
  rw [feedbackSceneSourceEquiv_coordinate,
    feedbackSceneAssignment_coordinate p scene hperfect hs ht i]
  simp only [crossingSign, sub_le_sub_iff_right, sub_sub_sub_cancel_right]

/-- Finite crossing families transport directly along the actual atom equivalence. -/
theorem feedbackSceneAssignment_finite_crossings (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hperfect : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (hfinite : ∀ x, {i : MatchingScene.SourceAtom scene |
      Crosses x i.val.1 (MatchingScene.atomAssignment hperfect i).val.1}.Finite) (x : ℝ) :
    {i : FeedbackEventLabel p.1 1 | Crosses x (feedbackCellEventPoint p.1 i).1
      (feedbackCellEventPoint p.1 (feedbackSceneAssignment p scene hperfect hs ht i)).1}.Finite := by
  have hf := (hfinite (x - p.2)).preimage (feedbackSceneSourceEquiv p scene hs).injective.injOn
  apply hf.subset
  intro i hi
  change Crosses (x - p.2) (feedbackSceneSourceEquiv p scene hs i).val.1
    (MatchingScene.atomAssignment hperfect (feedbackSceneSourceEquiv p scene hs i)).val.1
  rw [feedbackSceneSourceEquiv_coordinate,
    feedbackSceneAssignment_coordinate p scene hperfect hs ht i]
  simpa only [mem_ofPred_eq, Crosses, sub_lt_sub_iff_right] using hi

/-- Quadratic feedback costs commute with the actual atom correspondence. -/
theorem feedbackSceneAssignment_cost {lam : ℝ} (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (hg : ∀ x, scene.path.graphHeight x =
      feedbackConcatenatedGraphHeight lam p.1 (x + p.2) - feedbackConcatenatedGraphHeight lam p.1 p.2)
    (i : FeedbackEventLabel p.1 1) (j : FeedbackEventLabel p.1 (-1)) :
    markedQuadraticCost scene.path.graphHeight (feedbackSceneSourceEquiv p scene hs i).val
      (feedbackSceneTargetEquiv p scene ht j).val = feedbackLabelCost lam p.1 i j := by
  have hD : (1 - ((feedbackCellEventPoint p.1 i).2 : ℝ)) +
      (1 + ((feedbackCellEventPoint p.1 j).2 : ℝ)) ≠ 0 := by
    linarith [(feedbackCellEventPoint p.1 i).2.property.2,
      (feedbackCellEventPoint p.1 j).2.property.1]
  have hcost := quadraticCost_reroot (g := (feedbackConcatenatedGraphHeight lam p.1 : ℝ → ℝ))
    (feedbackConcatenatedGraphHeight lam p.1).continuous
    p.2 (feedbackCellEventPoint p.1 i).1 (feedbackCellEventPoint p.1 j).1
    (1 - ((feedbackCellEventPoint p.1 i).2 : ℝ))
    (1 + ((feedbackCellEventPoint p.1 j).2 : ℝ)) hD
  change quadraticCost scene.path.graphHeight
    ((feedbackCellEventPoint p.1 i).1 + -p.2) ((feedbackCellEventPoint p.1 j).1 + -p.2)
    (1 - ((feedbackCellEventPoint p.1 i).2 : ℝ))
    (1 + ((feedbackCellEventPoint p.1 j).2 : ℝ)) =
    quadraticCost (feedbackConcatenatedGraphHeight lam p.1)
      (feedbackCellEventPoint p.1 i).1 (feedbackCellEventPoint p.1 j).1
      (1 - ((feedbackCellEventPoint p.1 i).2 : ℝ))
      (1 + ((feedbackCellEventPoint p.1 j).2 : ℝ))
  rw [show (scene.path.graphHeight : ℝ → ℝ) =
    (fun x ↦ feedbackConcatenatedGraphHeight lam p.1 (x + p.2) -
      feedbackConcatenatedGraphHeight lam p.1 p.2) from funext hg]
  simpa only [sub_eq_add_neg] using hcost

/-- Finite local optimality is transported using mathlib's finite-set image equivalence. -/
theorem feedbackSceneAssignment_locally_minimizing {lam : ℝ} (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hperfect : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (hg : ∀ x, scene.path.graphHeight x =
      feedbackConcatenatedGraphHeight lam p.1 (x + p.2) - feedbackConcatenatedGraphHeight lam p.1 p.2)
    (hmin : (MatchingScene.spatialMatching hperfect).IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost scene.path.graphHeight i.val j.val)) :
    (feedbackLabelMatching p.1 (feedbackSceneAssignment p scene hperfect hs ht)).IsLocallyMinimizing
      (feedbackLabelCost lam p.1) := by
  intro rows tau
  let e := feedbackSceneSourceEquiv p scene hs
  let er := Finset.equivMap e.toEmbedding rows
  let tau' := er.permCongr tau
  have h := hmin (rows.map e.toEmbedding) tau'
  change (∑ i : rows.map e.toEmbedding, markedQuadraticCost scene.path.graphHeight i.val.val
      (MatchingScene.atomAssignment hperfect i.val).val) ≤
    ∑ i : rows.map e.toEmbedding, markedQuadraticCost scene.path.graphHeight i.val.val
      (MatchingScene.atomAssignment hperfect (tau' i).val).val at h
  rw [← er.sum_comp (fun j ↦ markedQuadraticCost scene.path.graphHeight j.val.val
      (MatchingScene.atomAssignment hperfect j.val).val),
    ← er.sum_comp (fun j ↦ markedQuadraticCost scene.path.graphHeight j.val.val
      (MatchingScene.atomAssignment hperfect (tau' j).val).val)] at h
  have htau (i : rows) : tau' (er i) = er (tau i) := by
    simp only [tau', Equiv.permCongr_apply, Equiv.symm_apply_apply]
  have hc (i j : rows) : markedQuadraticCost scene.path.graphHeight (er i).val.val
      (MatchingScene.atomAssignment hperfect (er j).val).val =
      feedbackLabelCost lam p.1 i (feedbackSceneAssignment p scene hperfect hs ht j) := by
    change markedQuadraticCost scene.path.graphHeight (e i).val
      (MatchingScene.atomAssignment hperfect (e j)).val = _
    rw [← feedbackSceneAssignment_partner p scene hperfect hs ht j]
    exact feedbackSceneAssignment_cost p scene hs ht hg i _
  simpa only [htau, hc, feedbackLabelMatching] using h

/-- The physical window energy of the retained labels is exactly the scene's rooted window
energy. In particular any scene-law moment bound transports without changing its constant. -/
theorem feedbackSceneAssignment_windowEnergy (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hperfect : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1)) (h L : ℝ) :
    feedbackWindowEnergy p (feedbackSceneAssignment p scene hperfect hs ht) h L =
      ∫ x in Icc (h / 2 - L / 2) (h / 2 + L / 2),
        (MatchingScene.spatialMatching hperfect).crossingEnergy x := by
  unfold feedbackWindowEnergy
  simp_rw [feedbackSceneAssignment_crossingEnergy p scene hperfect hs ht]
  rw [← integral_indicator (s := feedbackEnergyInterval p h L) measurableSet_Icc,
    ← integral_indicator measurableSet_Icc]
  calc
    _ = ∫ x : ℝ, (Icc (h / 2 - L / 2) (h / 2 + L / 2)).indicator
        (MatchingScene.spatialMatching hperfect).crossingEnergy (x + -p.2) := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      have hi : x ∈ feedbackEnergyInterval p h L ↔
          x + -p.2 ∈ Icc (h / 2 - L / 2) (h / 2 + L / 2) := by
        change (_ ≤ x ∧ x ≤ _) ↔ (_ ≤ x + -p.2 ∧ x + -p.2 ≤ _)
        constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
      simp only [Set.indicator_apply, hi, sub_eq_add_neg]
    _ = _ := integral_add_right_eq_self _ (-p.2)

/-- The physical energy observable, with zero assigned off the perfect-matching support. -/
noncomputable def feedbackSceneWindowEnergy (scene : MatchingScene) (h L : ℝ) : ℝ :=
  if hp : scene.IsSimplePerfectMatching then
    ∫ x in Icc (h / 2 - L / 2) (h / 2 + L / 2),
      (MatchingScene.spatialMatching hp).crossingEnergy x
  else 0

@[simp]
theorem feedbackSceneWindowEnergy_of_perfect (scene : MatchingScene)
    (hp : scene.IsSimplePerfectMatching) (h L : ℝ) :
    feedbackSceneWindowEnergy scene h L =
      ∫ x in Icc (h / 2 - L / 2) (h / 2 + L / 2),
        (MatchingScene.spatialMatching hp).crossingEnergy x := by
  simp only [feedbackSceneWindowEnergy, dite_eq_left hp]

/-- Matching current, finite crossings, and local minimality transfer from the actual scene
under exact equality of its feedback environment with the observed roof environment. -/
theorem feedbackSceneAssignment_admissible {lam : ℝ} (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hp : scene.IsSimplePerfectMatching)
    (he : (⟨scene.source, scene.target, scene.path⟩ : FeedbackEnvironment) = feedbackRoofEnvironment lam p)
    (hfinite : ∀ x, {i : MatchingScene.SourceAtom scene |
      Crosses x i.val.1 (MatchingScene.atomAssignment hp i).val.1}.Finite)
    (hflux : ∀ x, (MatchingScene.spatialMatching hp).current x = scene.currentAt x)
    (hmin : (MatchingScene.spatialMatching hp).IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost scene.path.graphHeight i.val j.val))
    (hw : ∀ x, FeedbackPath.currentAt (feedbackConcatenatedEnvironment lam p.1).currentIncrement
      (feedbackConcatenatedEnvironment lam p.1).path x = feedbackConcatenatedCurrent p.1 x) :
    FeedbackMatchingAdmissible p
      (feedbackSceneAssignment p scene hp (congrArg FeedbackEnvironment.source he)
        (congrArg FeedbackEnvironment.target he)) lam := by
  have hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1) :=
    congrArg FeedbackEnvironment.source he
  have ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1) :=
    congrArg FeedbackEnvironment.target he
  change FeedbackMatchingAdmissible p (feedbackSceneAssignment p scene hp hs ht) lam
  refine ⟨feedbackSceneAssignment_finite_crossings p scene hp hs ht hfinite, ?_, ?_⟩
  · intro cut hz
    rw [feedbackSceneAssignment_current p scene hp hs ht cut, hflux]
    have hcur := congrArg (fun e : FeedbackEnvironment ↦
      FeedbackPath.currentAt e.currentIncrement e.path (cut - p.2)) he
    change scene.currentAt (cut - p.2) = _ at hcur
    rw [hcur]
    change FeedbackPath.currentAt
      (FeedbackEnvironment.reroot p.2 (feedbackConcatenatedEnvironment lam p.1)).currentIncrement
      (FeedbackEnvironment.reroot p.2 (feedbackConcatenatedEnvironment lam p.1)).path
      (cut - p.2) = 0
    rw [currentAt_feedbackEnvironment_reroot, sub_add_cancel, hw, hz.1]
  · apply feedbackSceneAssignment_locally_minimizing p scene hp hs ht _ hmin
    intro x
    exact congrArg (fun e : FeedbackEnvironment ↦ e.path.graphHeight x) he

/-- The partner permutation acts on all raw labels by fixing every inactive source label. -/
noncomputable def feedbackRawPartnerPermutation (w : FeedbackCellSequence)
    (σ₁ σ₂ : FeedbackEventLabel w 1 ≃ FeedbackEventLabel w (-1)) : Equiv.Perm (ℤ × ℕ) :=
  ((feedbackLabelMatching w σ₁).partnerPermutation (feedbackLabelMatching w σ₂)).subtypeCongr
    (Equiv.refl _)

@[simp]
theorem feedbackRawPartnerPermutation_active (w : FeedbackCellSequence)
    (σ₁ σ₂ : FeedbackEventLabel w 1 ≃ FeedbackEventLabel w (-1))
    (i : FeedbackEventLabel w 1) :
    feedbackRawPartnerPermutation w σ₁ σ₂ i =
      ((feedbackLabelMatching w σ₁).partnerPermutation (feedbackLabelMatching w σ₂) i).val := by
  exact Equiv.Perm.subtypeCongr.left_apply_subtype _ _ i

@[simp]
theorem feedbackRawPartnerPermutation_inactive (w : FeedbackCellSequence)
    (σ₁ σ₂ : FeedbackEventLabel w 1 ≃ FeedbackEventLabel w (-1))
    (i : ℤ × ℕ) (hi : ¬feedbackCellEventActive w 1 i) :
    feedbackRawPartnerPermutation w σ₁ σ₂ i = i := by
  exact Equiv.Perm.subtypeCongr.right_apply _ _ hi

end OTSelector.Matching
