import OTSelector.Matching.DisagreementSceneReroot
import OTSelector.Matching.FeedbackSceneMatching

/-!
# Measurable disagreement on actual regenerative event labels

The raw partner permutation is read from the two scene edge relations. Inactive
labels are fixed. Measurability follows from countably many actual edge tests,
without assuming that the selected partner functions are measurable.
-/

open Function Set MeasureTheory
open scoped Classical ENNReal

namespace OTSelector.Matching
open OTSelector.Limit OTSelector.PointProcess

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

/-- A retained event's marked location relative to the actual observation origin. -/
noncomputable def feedbackRootedEventPoint (p : FeedbackCellSequence × ℝ) (i : ℤ × ℕ) :
    MatchingPoint := Configuration.pointTranslation (-p.2) (feedbackCellEventPoint p.1 i)

@[fun_prop]
theorem measurable_feedbackRootedEventPoint (i : ℤ × ℕ) :
    Measurable (fun p ↦ feedbackRootedEventPoint p i) := by
  change Measurable (fun p : FeedbackCellSequence × ℝ ↦
    ((feedbackCellEventPoint p.1 i).1 + -p.2, (feedbackCellEventPoint p.1 i).2))
  exact (((measurable_feedbackCellEventPoint i).comp measurable_fst).fst.add
    measurable_snd.neg).prodMk (((measurable_feedbackCellEventPoint i).comp measurable_fst).snd)

/-- The actual labelled assignment is completely determined by actual scene edge atoms. -/
theorem feedbackSceneAssignment_eq_iff_edge (p : FeedbackCellSequence × ℝ)
    (scene : MatchingScene) (hp : scene.IsSimplePerfectMatching)
    (hs : scene.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht : scene.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (i : FeedbackEventLabel p.1 1) (j : FeedbackEventLabel p.1 (-1)) :
    feedbackSceneAssignment p scene hp hs ht i = j ↔
      LocalConfiguration.multiplicity scene.edges
        (feedbackRootedEventPoint p i, feedbackRootedEventPoint p j) ≠ 0 := by
  rw [← (feedbackSceneTargetEquiv p scene ht).injective.eq_iff,
    feedbackSceneAssignment_partner]
  exact MatchingScene.atomAssignment_eq_iff_edge hp _ _

/-- A raw permutation fiber uses a common actual target, or a fixed inactive label. -/
theorem feedbackRawPartnerPermutation_eq_iff (w : FeedbackCellSequence)
    (σ₁ σ₂ : FeedbackEventLabel w 1 ≃ FeedbackEventLabel w (-1)) (i j : ℤ × ℕ) :
    feedbackRawPartnerPermutation w σ₁ σ₂ i = j ↔
      (¬feedbackCellEventActive w 1 i ∧ i = j) ∨
      ∃ (hi : feedbackCellEventActive w 1 i) (hj : feedbackCellEventActive w 1 j),
        σ₁ ⟨i, hi⟩ = σ₂ ⟨j, hj⟩ := by
  by_cases hi : feedbackCellEventActive w 1 i
  · have hr := feedbackRawPartnerPermutation_active w σ₁ σ₂ ⟨i, hi⟩
    change feedbackRawPartnerPermutation w σ₁ σ₂ i = (σ₂.symm (σ₁ ⟨i, hi⟩)).val at hr
    rw [hr]
    constructor
    · intro heq
      have hj : feedbackCellEventActive w 1 j := heq ▸ (σ₂.symm (σ₁ ⟨i, hi⟩)).property
      refine Or.inr ⟨hi, hj, ?_⟩
      exact (σ₂.apply_symm_apply (σ₁ ⟨i, hi⟩)).symm.trans
        (congrArg σ₂ (Subtype.ext heq))
    · rintro (⟨hni, _⟩ | ⟨_, hj, heq⟩)
      · exact False.elim (hni hi)
      · exact congrArg Subtype.val ((congrArg σ₂.symm heq).trans (σ₂.symm_apply_apply _))
  · rw [feedbackRawPartnerPermutation_inactive w σ₁ σ₂ i hi]
    constructor
    · exact fun hij ↦ Or.inl ⟨hi, hij⟩
    · rintro (⟨_, hij⟩ | ⟨hi', _, _⟩)
      · exact hij
      · exact False.elim (hi hi')

/-- The active raw-label count is exactly the actual rooted configuration count. -/
theorem feedbackRootedEventPoint_count (p : FeedbackCellSequence × ℝ) (d : ℤ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    LocalConfiguration.countingMeasure
      (LocalConfiguration.reroot p.2 (feedbackConcatenatedPoints d p.1)) (A ×ˢ univ) =
      ∑' i : ℤ × ℕ, if feedbackCellEventActive p.1 d i ∧
        (feedbackRootedEventPoint p i).1 ∈ A then (1 : ℝ≥0∞) else 0 := by
  have hm := (Configuration.pointTranslation (-p.2) (M := UnitMark)).measurable
  rw [LocalConfiguration.countingMeasure_reroot, countingMeasure_feedbackConcatenatedPoints,
    Measure.map_sum hm.aemeasurable, Measure.sum_apply _ (hA.prod MeasurableSet.univ)]
  apply tsum_congr
  intro i
  by_cases hi : feedbackCellEventActive p.1 d i
  · simp only [hi, ite_true, true_and, Measure.map_dirac' hm, Measure.dirac_apply' _
      (hA.prod MeasurableSet.univ), Set.indicator_apply, Pi.one_apply, mem_prod, mem_univ,
      and_true, feedbackRootedEventPoint]
  · simp only [hi, ite_false, false_and, Measure.map_zero, Measure.coe_zero, Pi.zero_apply]

section ScenePair

variable (p : FeedbackCellSequence × ℝ) (scene₁ scene₂ : MatchingScene)
    (hp₁ : scene₁.IsSimplePerfectMatching) (hp₂ : scene₂.IsSimplePerfectMatching)
    (hs₁ : scene₁.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht₁ : scene₁.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))
    (hs₂ : scene₂.source = LocalConfiguration.reroot p.2 (feedbackConcatenatedSource p.1))
    (ht₂ : scene₂.target = LocalConfiguration.reroot p.2 (feedbackConcatenatedTarget p.1))

/-- The disagreement permutation of the two actual scenes, extended by identity off their sources. -/
noncomputable def feedbackSceneRawPartner : Equiv.Perm (ℤ × ℕ) :=
  feedbackRawPartnerPermutation p.1 (feedbackSceneAssignment p scene₁ hp₁ hs₁ ht₁)
    (feedbackSceneAssignment p scene₂ hp₂ hs₂ ht₂)

/-- A countable, measurable edge-relation description of every raw permutation fiber. -/
theorem feedbackSceneRawPartner_eq_iff (i j : ℤ × ℕ) :
    feedbackSceneRawPartner p scene₁ scene₂ hp₁ hp₂ hs₁ ht₁ hs₂ ht₂ i = j ↔
      (¬feedbackCellEventActive p.1 1 i ∧ i = j) ∨
      (feedbackCellEventActive p.1 1 i ∧ feedbackCellEventActive p.1 1 j ∧
        ∃ k : ℤ × ℕ, feedbackCellEventActive p.1 (-1) k ∧
          LocalConfiguration.multiplicity scene₁.edges
            (feedbackRootedEventPoint p i, feedbackRootedEventPoint p k) ≠ 0 ∧
          LocalConfiguration.multiplicity scene₂.edges
            (feedbackRootedEventPoint p j, feedbackRootedEventPoint p k) ≠ 0) := by
  rw [feedbackSceneRawPartner, feedbackRawPartnerPermutation_eq_iff]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨hi, hj, heq⟩
    let k := feedbackSceneAssignment p scene₁ hp₁ hs₁ ht₁ ⟨i, hi⟩
    refine ⟨hi, hj, k.val, k.property, ?_, ?_⟩
    · exact (feedbackSceneAssignment_eq_iff_edge p scene₁ hp₁ hs₁ ht₁ ⟨i, hi⟩ k).mp rfl
    · exact (feedbackSceneAssignment_eq_iff_edge p scene₂ hp₂ hs₂ ht₂ ⟨j, hj⟩ k).mp heq.symm
  · rintro ⟨hi, hj, k, hk, he₁, he₂⟩
    exact ⟨hi, hj,
      ((feedbackSceneAssignment_eq_iff_edge p scene₁ hp₁ hs₁ ht₁ ⟨i, hi⟩ ⟨k, hk⟩).mpr he₁).trans
        ((feedbackSceneAssignment_eq_iff_edge p scene₂ hp₂ hs₂ ht₂ ⟨j, hj⟩ ⟨k, hk⟩).mpr he₂).symm⟩

end ScenePair

/-- Integer iterates of a measurable countable permutation family are measurable. -/
theorem measurable_perm_zpow_apply {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (p : Ω → Equiv.Perm S) (hp : ∀ i, Measurable (fun ω ↦ p ω i)) (i : S) (n : ℤ) :
    Measurable (fun ω ↦ (p ω ^ n) i) := by
  have hsymm (i : S) : Measurable (fun ω ↦ (p ω).symm i) := by
    apply measurable_to_countable'
    intro j
    convert measurableSet_eq_fun measurable_const (hp j) using 1
    ext ω
    exact (p ω).symm_apply_eq
  have hpow (q : Ω → Equiv.Perm S) (hq : ∀ i, Measurable (fun ω ↦ q ω i))
      (m : ℕ) : Measurable (fun ω ↦ (q ω ^ m) i) := by
    induction m with
    | zero => simpa only [pow_zero, Equiv.Perm.one_apply] using
        (measurable_const : Measurable (fun _ : Ω ↦ i))
    | succ m ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      have hqjoint : Measurable (fun z : Ω × S ↦ q z.1 z.2) :=
        measurable_from_prod_countable_left hq
      exact hqjoint.comp (measurable_id.prodMk ih)
  cases n with
  | ofNat n => exact hpow p hp n
  | negSucc n =>
      simpa only [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def] using
        hpow (fun ω ↦ (p ω).symm) hsymm (n + 1)

section Measurability

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

/-- Measurability of the actual selected partner is proved from edge atoms, on any good support. -/
theorem measurable_feedbackSceneRawPartner (i : ℤ × ℕ) :
    Measurable (fun ω ↦ feedbackSceneRawPartner (p ω) (scene₁ ω) (scene₂ ω)
      (hp₁ ω) (hp₂ ω) (hs₁ ω) (ht₁ ω) (hs₂ ω) (ht₂ ω) i) := by
  apply measurable_to_countable'
  intro j
  have ha (d : ℤ) (k : ℤ × ℕ) : MeasurableSet {ω | feedbackCellEventActive (p ω).1 d k} :=
    (measurableSet_feedbackCellEventActive d k).preimage hp.fst
  have he (scene : Ω → MatchingScene) (hscene : Measurable scene) (k l : ℤ × ℕ) :
      MeasurableSet {ω | LocalConfiguration.multiplicity (scene ω).edges
        (feedbackRootedEventPoint (p ω) k, feedbackRootedEventPoint (p ω) l) ≠ 0} :=
    MatchingScene.measurableSet_edgeAtom_param hscene
      ((measurable_feedbackRootedEventPoint k).comp hp)
      ((measurable_feedbackRootedEventPoint l).comp hp)
  have hk : MeasurableSet {ω | ∃ k : ℤ × ℕ, feedbackCellEventActive (p ω).1 (-1) k ∧
      LocalConfiguration.multiplicity (scene₁ ω).edges
        (feedbackRootedEventPoint (p ω) i, feedbackRootedEventPoint (p ω) k) ≠ 0 ∧
      LocalConfiguration.multiplicity (scene₂ ω).edges
        (feedbackRootedEventPoint (p ω) j, feedbackRootedEventPoint (p ω) k) ≠ 0} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k ↦
      (ha (-1) k).inter ((he scene₁ hscene₁ i k).inter (he scene₂ hscene₂ j k))
  have hconst : MeasurableSet {ω : Ω | i = j} := by
    by_cases hij : i = j <;> simp [hij]
  convert ((ha 1 i).compl.inter hconst).union ((ha 1 i).inter ((ha 1 j).inter hk)) using 1
  ext ω
  exact feedbackSceneRawPartner_eq_iff (p ω) (scene₁ ω) (scene₂ ω)
    (hp₁ ω) (hp₂ ω) (hs₁ ω) (ht₁ ω) (hs₂ ω) (ht₂ ω) i j

/-- Every actual integer-orbit position is measurable, including negative iterates. -/
theorem measurable_feedbackSceneRawPartner_orbit (i : ℤ × ℕ) (n : ℤ) :
    Measurable (fun ω ↦ partnerOrbitPositions
      (feedbackSceneRawPartner (p ω) (scene₁ ω) (scene₂ ω)
        (hp₁ ω) (hp₂ ω) (hs₁ ω) (ht₁ ω) (hs₂ ω) (ht₂ ω))
      (fun j ↦ (feedbackRootedEventPoint (p ω) j).1) i n) := by
  have hpoint : Measurable (fun z : Ω × (ℤ × ℕ) ↦
      (feedbackRootedEventPoint (p z.1) z.2).1) :=
    measurable_from_prod_countable_left fun j ↦
      ((measurable_feedbackRootedEventPoint j).comp hp).fst
  exact hpoint.comp (measurable_id.prodMk
    (measurable_perm_zpow_apply _
      (measurable_feedbackSceneRawPartner p scene₁ scene₂ hp₁ hp₂ hs₁ ht₁ hs₂ ht₂
        hp hscene₁ hscene₂) i n))

end Measurability

end OTSelector.Matching
