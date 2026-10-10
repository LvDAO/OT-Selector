import OTSelector.Matching.DisagreementFeedbackCovariance
import OTSelector.Matching.DisagreementUniqueness
import OTSelector.Matching.FeedbackSceneJoiningEnergy
import OTSelector.Matching.DisagreementSceneEvent

/-!
# Actual common-cut uniqueness on a good scene pair
-/

open Function Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 4096

/-- Local minimality in the exact rooted marked cost transports to the genuine labels. -/
theorem feedbackSceneAssignment_locally_minimizing_actual (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hp : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (hmin : (MatchingScene.spatialMatching hp).IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost scene.path.graphHeight i.val j.val)) :
    (feedbackLabelMatching p.1 (feedbackSceneAssignment p scene hp hs ht)).IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost scene.path.graphHeight
        (feedbackRootedEventPoint p i) (feedbackRootedEventPoint p j)) := by
  intro rows tau
  let e := feedbackSceneSourceEquiv p scene hs
  let er := Finset.equivMap e.toEmbedding rows
  let tau' := er.permCongr tau
  have h := hmin (rows.map e.toEmbedding) tau'
  change (∑ i : rows.map e.toEmbedding, markedQuadraticCost scene.path.graphHeight i.val.val
      (MatchingScene.atomAssignment hp i.val).val) ≤
    ∑ i : rows.map e.toEmbedding, markedQuadraticCost scene.path.graphHeight i.val.val
      (MatchingScene.atomAssignment hp (tau' i).val).val at h
  rw [← er.sum_comp (fun j ↦ markedQuadraticCost scene.path.graphHeight j.val.val
      (MatchingScene.atomAssignment hp j.val).val),
    ← er.sum_comp (fun j ↦ markedQuadraticCost scene.path.graphHeight j.val.val
      (MatchingScene.atomAssignment hp (tau' j).val).val)] at h
  have htau (i : rows) : tau' (er i) = er (tau i) := by
    simp only [tau', Equiv.permCongr_apply, Equiv.symm_apply_apply]
  have hc (i j : rows) : markedQuadraticCost scene.path.graphHeight (er i).val.val
      (MatchingScene.atomAssignment hp (er j).val).val =
      markedQuadraticCost scene.path.graphHeight (feedbackRootedEventPoint p i)
        (feedbackRootedEventPoint p (feedbackSceneAssignment p scene hp hs ht j)) := by
    change markedQuadraticCost scene.path.graphHeight (e i).val
      (MatchingScene.atomAssignment hp (e j)).val = _
    rw [← feedbackSceneAssignment_partner p scene hp hs ht j]
    rfl
  simpa only [htau, hc, feedbackLabelMatching] using h

private theorem lowerAnchoredOrbit_of_positions_translate {S T : Type*}
    {p : Equiv.Perm S} {q : Equiv.Perm T} {source : S → ℝ} {target : T → ℝ}
    {i : S} {j : T} (a : ℝ)
    (heq : ∀ n, partnerOrbitPositions p source i n = a + partnerOrbitPositions q target j n)
    (h : LowerAnchoredOrbit q target j) : LowerAnchoredOrbit p source i := by
  refine ⟨fun m n hmn ↦ h.1 (by rw [heq, heq] at hmn; linarith), ?_⟩
  obtain ⟨b, hb⟩ := h.2
  refine ⟨a + b, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [heq]
  linarith [hb ⟨n, rfl⟩]

/-- Orbit exclusion for raw rooted labels also excludes unrooted genuine label orbits. -/
theorem feedbackLabelMatching_no_anchor_of_raw (p : FeedbackCellSequence × ℝ)
    (σ₁ σ₂ : FeedbackEventLabel p.1 1 ≃ FeedbackEventLabel p.1 (-1))
    (hraw : ∀ i, ¬ LowerAnchoredOrbit (feedbackRawPartnerPermutation p.1 σ₁ σ₂)
      (fun j ↦ (feedbackRootedEventPoint p j).1) i ∧
      ¬ LowerAnchoredOrbit (feedbackRawPartnerPermutation p.1 σ₁ σ₂)
      (fun j ↦ -(feedbackRootedEventPoint p j).1) i) :
    ∀ i, ¬ LowerAnchoredOrbit
      ((feedbackLabelMatching p.1 σ₁).partnerPermutation (feedbackLabelMatching p.1 σ₂))
      (feedbackLabelMatching p.1 σ₁).source i ∧
      ¬ LowerAnchoredOrbit
      ((feedbackLabelMatching p.1 σ₁).partnerPermutation (feedbackLabelMatching p.1 σ₂))
      (fun j ↦ -(feedbackLabelMatching p.1 σ₁).source j) i := by
  intro i
  constructor
  · intro hi
    apply (hraw i).1
    apply lowerAnchoredOrbit_of_positions_translate (-p.2) (h := hi)
    intro n
    unfold partnerOrbitPositions
    rw [feedbackRawPartnerPermutation_zpow_active]
    change (feedbackCellEventPoint p.1 _).1 + -p.2 = -p.2 + (feedbackCellEventPoint p.1 _).1
    ring
  · intro hi
    apply (hraw i).2
    apply lowerAnchoredOrbit_of_positions_translate p.2 (h := hi)
    intro n
    unfold partnerOrbitPositions
    rw [feedbackRawPartnerPermutation_zpow_active]
    change -((feedbackCellEventPoint p.1 _).1 + -p.2) = p.2 + -(feedbackCellEventPoint p.1 _).1
    ring

/-- Equal actual assignments determine the entire two simple edge configurations. -/
theorem feedbackScene_edges_eq_of_assignment_eq (p : FeedbackCellSequence × ℝ)
    (scene₁ scene₂ : MatchingScene) (hp₁ : scene₁.IsSimplePerfectMatching)
    (hp₂ : scene₂.IsSimplePerfectMatching)
    (hs₁ : scene₁.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht₁ : scene₁.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (hs₂ : scene₂.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht₂ : scene₂.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (heq : feedbackSceneAssignment p scene₁ hp₁ hs₁ ht₁ =
      feedbackSceneAssignment p scene₂ hp₂ hs₂ ht₂) : scene₁.edges = scene₂.edges := by
  have himp (c d : MatchingScene) (hc : c.IsSimplePerfectMatching) (hd : d.IsSimplePerfectMatching)
      (hcs : c.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
      (hct : c.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
      (hds : d.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
      (hdt : d.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
      (h : feedbackSceneAssignment p c hc hcs hct = feedbackSceneAssignment p d hd hds hdt)
      (z : MatchingPoint × MatchingPoint) (hz : LocalConfiguration.multiplicity c.edges z ≠ 0) :
      LocalConfiguration.multiplicity d.edges z ≠ 0 := by
    obtain ⟨hs, ht⟩ := hc.endpoints z hz
    obtain ⟨i, hi⟩ := (feedbackSceneSourceEquiv p c hcs).surjective ⟨z.1, hs⟩
    obtain ⟨j, hj⟩ := (feedbackSceneTargetEquiv p c hct).surjective ⟨z.2, ht⟩
    have hip : feedbackRootedEventPoint p i = z.1 := congrArg Subtype.val hi
    have hjp : feedbackRootedEventPoint p j = z.2 := congrArg Subtype.val hj
    have hassign : feedbackSceneAssignment p c hc hcs hct i = j :=
      (feedbackSceneAssignment_eq_iff_edge p c hc hcs hct i j).mpr (by simpa [hip, hjp] using hz)
    rw [h] at hassign
    simpa only [hip, hjp, Prod.eta] using
      (feedbackSceneAssignment_eq_iff_edge p d hd hds hdt i j).mp hassign
  apply LocalConfiguration.toLocallyFinsupp_injective
  ext z
  have hi : LocalConfiguration.multiplicity scene₁.edges z ≠ 0 ↔
      LocalConfiguration.multiplicity scene₂.edges z ≠ 0 :=
    ⟨himp scene₁ scene₂ hp₁ hp₂ hs₁ ht₁ hs₂ ht₂ heq z,
      himp scene₂ scene₁ hp₂ hp₁ hs₂ ht₂ hs₁ ht₁ heq.symm z⟩
  have h₁ := hp₁.simple_edges z
  have h₂ := hp₂.simple_edges z
  change LocalConfiguration.multiplicity scene₁.edges z = LocalConfiguration.multiplicity scene₂.edges z
  omega

/-- Under the established no-tie and orbit-exclusion conclusions, an actual common non-event
cut forces equality of the two complete scene edge configurations. -/
theorem feedbackScene_edges_eq_of_commonEmptyCut {lam : ℝ} (q : FeedbackSceneRoofPoint)
    (hgood : ∀ k : Fin 2, (feedbackSceneRoofScene q k).IsSimplePerfectMatching ∧
      feedbackSceneEnvironment (feedbackSceneRoofScene q k) = feedbackRoofEnvironment lam q.2.1)
    (hcandidate : ∀ k : Fin 2, FeedbackSceneEnergyCandidate lam (feedbackSceneRoofScene q k))
    (hnotie : FeedbackNoFiniteTies (feedbackRoofEnvironment lam q.2.1))
    (hraw : ∀ i, ¬ LowerAnchoredOrbit
      (feedbackSceneRawPartner q.2.1 q.2.2.1 q.2.2.2 (hgood 0).1 (hgood 1).1
        (congrArg FeedbackEnvironment.source (hgood 0).2)
        (congrArg FeedbackEnvironment.target (hgood 0).2)
        (congrArg FeedbackEnvironment.source (hgood 1).2)
        (congrArg FeedbackEnvironment.target (hgood 1).2))
      (fun j ↦ (feedbackRootedEventPoint q.2.1 j).1) i ∧
      ¬ LowerAnchoredOrbit
      (feedbackSceneRawPartner q.2.1 q.2.2.1 q.2.2.2 (hgood 0).1 (hgood 1).1
        (congrArg FeedbackEnvironment.source (hgood 0).2)
        (congrArg FeedbackEnvironment.target (hgood 0).2)
        (congrArg FeedbackEnvironment.source (hgood 1).2)
        (congrArg FeedbackEnvironment.target (hgood 1).2))
      (fun j ↦ -(feedbackRootedEventPoint q.2.1 j).1) i)
    (x : ℝ)
    (hnon : LocalConfiguration.countingMeasure (feedbackRoofEnvironment lam q.2.1).source
        ({x} ×ˢ univ) = 0 ∧
      LocalConfiguration.countingMeasure (feedbackRoofEnvironment lam q.2.1).target
        ({x} ×ˢ univ) = 0)
    (hcut : feedbackSceneCommonEmptyCut q x) : q.2.2.1.edges = q.2.2.2.edges := by
  let p := q.2.1
  let scene := feedbackSceneRoofScene q
  let hp : ∀ k : Fin 2, (scene k).IsSimplePerfectMatching := fun k ↦ (hgood k).1
  let hs : ∀ k : Fin 2, (scene k).source =
      LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1) :=
    fun k ↦ congrArg FeedbackEnvironment.source (hgood k).2
  let ht : ∀ k : Fin 2, (scene k).target =
      LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1) :=
    fun k ↦ congrArg FeedbackEnvironment.target (hgood k).2
  let σ := fun k ↦ feedbackSceneAssignment p (scene k) (hp k) (hs k) (ht k)
  let M := fun k ↦ feedbackLabelMatching p.1 (σ k)
  have hmin (k : Fin 2) : (M k).IsLocallyMinimizing (fun i j ↦
      markedQuadraticCost (feedbackRoofEnvironment lam p).path.graphHeight
        (feedbackRootedEventPoint p i) (feedbackRootedEventPoint p j)) := by
    have h := feedbackSceneAssignment_locally_minimizing_actual p (scene k) (hp k)
      (hs k) (ht k) (hcandidate k).locally_minimizing
    have hg := congrArg (fun e : FeedbackEnvironment ↦ e.path.graphHeight) (hgood k).2
    change (scene k).path.graphHeight = (feedbackRoofEnvironment lam p).path.graphHeight at hg
    rw [hg] at h
    exact h
  have hsa (i : FeedbackEventLabel p.1 1) :
      LocalConfiguration.multiplicity (feedbackRoofEnvironment lam p).source
        (feedbackRootedEventPoint p i) ≠ 0 := by
    change LocalConfiguration.multiplicity
      (LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
        (feedbackRootedEventPoint p i) ≠ 0
    rw [← hs 0]
    exact (feedbackSceneSourceEquiv p (scene 0) (hs 0) i).property
  have hta (i : FeedbackEventLabel p.1 (-1)) :
      LocalConfiguration.multiplicity (feedbackRoofEnvironment lam p).target
        (feedbackRootedEventPoint p i) ≠ 0 := by
    change LocalConfiguration.multiplicity
      (LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
        (feedbackRootedEventPoint p i) ≠ 0
    rw [← ht 0]
    exact (feedbackSceneTargetEquiv p (scene 0) (ht 0) i).property
  have hpointinj : Injective (M 0).source := by
    intro i j hij
    exact Subtype.ext (feedbackCellEventPoint_fst_injective i.property.1 i.property.2.1
      j.property.2.1 hij)
  have hsrcinj : Injective (fun i : FeedbackEventLabel p.1 1 ↦ feedbackRootedEventPoint p i) := by
    intro i j hij
    exact (feedbackSceneSourceEquiv p (scene 0) (hs 0)).injective (Subtype.ext hij)
  have htgtinj : Injective (fun i : FeedbackEventLabel p.1 (-1) ↦ feedbackRootedEventPoint p i) := by
    intro i j hij
    exact (feedbackSceneTargetEquiv p (scene 0) (ht 0)).injective (Subtype.ext hij)
  have hcross (k : Fin 2) (c : ℝ) :
      {i | Crosses c ((M k).source i) ((M k).target ((M k).assignment i))}.Finite :=
    feedbackSceneAssignment_finite_crossings p (scene k) (hp k) (hs k) (ht k)
      (hcandidate k).finite_crossings c
  have hnonS (i : FeedbackEventLabel p.1 1) : (M 0).source i ≠ p.2 + x := by
    have h := atom_coordinate_ne_of_zero_count _ x hnon.1 _ (hsa i)
    change (feedbackCellEventPoint p.1 i).1 + -p.2 ≠ x at h
    change (feedbackCellEventPoint p.1 i).1 ≠ p.2 + x
    exact fun heq ↦ h (by linarith)
  have hnonT (i : FeedbackEventLabel p.1 (-1)) : (M 0).target i ≠ p.2 + x := by
    have h := atom_coordinate_ne_of_zero_count _ x hnon.2 _ (hta i)
    change (feedbackCellEventPoint p.1 i).1 + -p.2 ≠ x at h
    change (feedbackCellEventPoint p.1 i).1 ≠ p.2 + x
    exact fun heq ↦ h (by linarith)
  have hempty (k : Fin 2) (i : FeedbackEventLabel p.1 1) :
      ¬ Crosses (p.2 + x) ((M k).source i) ((M k).target ((M k).assignment i)) := by
    intro hi
    change Crosses (p.2 + x) (feedbackCellEventPoint p.1 i).1
      (feedbackCellEventPoint p.1 (σ k i)).1 at hi
    apply hcut k (hp k) (feedbackSceneSourceEquiv p (scene k) (hs k) i)
    rw [feedbackSceneSourceEquiv_coordinate, feedbackSceneAssignment_coordinate p (scene k)
      (hp k) (hs k) (ht k)]
    rcases hi with hi | hi
    · exact Or.inl ⟨by linarith [hi.1], by linarith [hi.2]⟩
    · exact Or.inr ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have heq := SpatialMatching.assignment_eq_of_no_ties_of_common_empty_cut (M 0) (M 1) hnotie
    (fun i ↦ feedbackRootedEventPoint p i) (fun j ↦ feedbackRootedEventPoint p j)
    hsrcinj htgtinj (fun i ↦ by simpa using hsa i) (fun j ↦ by simpa using hta j)
    (hmin 0) (hmin 1) rfl rfl hpointinj (feedbackLabelMatching_locallyFinite _ _)
    (feedbackLabelMatching_locallyFinite _ _) (fun c _ ↦ hcross 0 c) (fun c _ ↦ hcross 1 c)
    (feedbackLabelMatching_no_anchor_of_raw p (σ 0) (σ 1) hraw)
    (p.2 + x) hnonS hnonT (hempty 0) (hempty 1)
  exact feedbackScene_edges_eq_of_assignment_eq p (scene 0) (scene 1) (hp 0) (hp 1)
    (hs 0) (ht 0) (hs 1) (ht 1) heq

end OTSelector.Matching
