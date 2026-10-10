import OTSelector.PointProcess.MatchingSceneTransportCrossing

/-!
# All-cut recovery of the actual matching current

The difference of crossing currents at two cuts is the source-minus-target count in their
half-open interval. Root-current recovery therefore propagates to every real cut, including
cuts through actual endpoints.
-/

open MeasureTheory Set Function Filter Topology
open scoped BigOperators Classical ENNReal

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess.LocalConfiguration

/-- The contribution of one spatial point to the signed count between two cuts. -/
noncomputable def cutIncrement (a b s : ℝ) : ℤ :=
  (if s ≤ b then 1 else 0) - (if s ≤ a then 1 else 0)

theorem cutIncrement_eq_indicator (a b s : ℝ) :
    (cutIncrement a b s : ℝ) =
      (Ioc a b).indicator (fun _ ↦ (1 : ℝ)) s -
        (Ioc b a).indicator (fun _ ↦ (1 : ℝ)) s := by
  by_cases ha : s ≤ a <;> by_cases hb : s ≤ b <;>
    simp [cutIncrement, mem_Ioc, ha, hb, not_lt.mpr, lt_of_not_ge]

theorem cutIncrement_eq_zero_of_not_mem (a b s : ℝ)
    (hs : s ∉ Icc (min a b) (max a b)) : cutIncrement a b s = 0 := by
  by_cases ha : s ≤ a <;> by_cases hb : s ≤ b
  · simp [cutIncrement, ha, hb]
  · exfalso
    exact hs ⟨(min_le_right _ _).trans (not_le.mp hb).le, ha.trans (le_max_left _ _)⟩
  · exfalso
    exact hs ⟨(min_le_left _ _).trans (not_le.mp ha).le, hb.trans (le_max_right _ _)⟩
  · simp [cutIncrement, ha, hb]

theorem finite_cutIncrement_support (config : LocalConfiguration matchingPointBase) (a b : ℝ) :
    (Function.support (fun x : {x // multiplicity config x ≠ 0} ↦
      cutIncrement a b x.val.1)).Finite := by
  have hK : IsCompact (Icc (min a b) (max a b) ×ˢ (univ : Set UnitMark)) :=
    isCompact_Icc.prod isCompact_univ
  have hfin := (locallyFiniteSupport_multiplicity config).finite_inter_support_of_isCompact hK
  apply (hfin.preimage (Subtype.val_injective.injOn)).subset
  intro x hx
  refine ⟨⟨?_, mem_univ _⟩, x.property⟩
  by_contra hn
  exact hx (cutIncrement_eq_zero_of_not_mem a b x.val.1 hn)

/-- Signed interval counts of a simple configuration are exactly its actual atom sum. -/
theorem orientedCount_eq_tsum_atoms (config : LocalConfiguration matchingPointBase)
    (hsimple : ∀ x, multiplicity config x ≤ 1) (a b : ℝ) :
    orientedCount config a b = ∑' x : {x // multiplicity config x ≠ 0},
      cutIncrement a b x.val.1 := by
  let f : MatchingPoint → ℝ := fun x ↦ (cutIncrement a b x.1 : ℝ)
  let g (a b : ℝ) : MatchingPoint → ℝ := (spatialIoc a b).indicator (fun _ ↦ 1)
  have hg (a b : ℝ) : Integrable (g a b) (countingMeasure config) :=
    (integrable_indicator_iff (measurableSet_spatialIoc a b)).mpr
      (integrableOn_const (countingMeasure_lt_top_of_isBounded config (isBounded_spatialIoc a b)).ne)
  have hfg : f = fun x ↦ g a b x - g b a x := by
    funext x
    exact cutIncrement_eq_indicator a b x.1
  have hf : Integrable f (countingMeasure config) := by rw [hfg]; exact (hg a b).sub (hg b a)
  have hi : (∫ x, f x ∂countingMeasure config) = (orientedCount config a b : ℝ) := by
    rw [hfg, integral_sub (hg a b) (hg b a)]
    simp only [g, integral_indicator_const _ (measurableSet_spatialIoc _ _), smul_eq_mul,
      mul_one, orientedCount, Int.cast_sub, spatialCount_cast]
  rw [integral_eq_tsum_atoms config hf] at hi
  have hm (x : {x // multiplicity config x ≠ 0}) : multiplicity config x.val = 1 :=
    Nat.le_antisymm (hsimple _) (Nat.one_le_iff_ne_zero.mpr x.property)
  simp_rw [hm, Nat.cast_one, one_mul] at hi
  have hfin := finite_cutIncrement_support config a b
  have hout (x : {x // multiplicity config x ≠ 0}) (hx : x ∉ hfin.toFinset) :
      cutIncrement a b x.val.1 = 0 := by
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hx
  have houtReal (x : {x // multiplicity config x ≠ 0}) (hx : x ∉ hfin.toFinset) :
      f x.val = 0 := by
    change (cutIncrement a b x.val.1 : ℝ) = 0
    rw [hout x hx, Int.cast_zero]
  rw [tsum_eq_sum (s := hfin.toFinset) houtReal] at hi
  apply (Int.cast_injective (α := ℝ))
  rw [tsum_eq_sum (s := hfin.toFinset) hout, Int.cast_sum]
  exact hi.symm

end OTSelector.PointProcess.LocalConfiguration

namespace OTSelector.PointProcess.MatchingScene

private theorem crossingSign_eq_zero_add_increments (s t x : ℝ) :
    crossingSign s t x = crossingSign s t 0 +
      LocalConfiguration.cutIncrement 0 x s - LocalConfiguration.cutIncrement 0 x t := by
  unfold crossingSign LocalConfiguration.cutIncrement
  ring

/-- Finitely many root crossings and local endpoint finiteness imply finitely many crossings
at every cut, including event cuts with the original half-open convention. -/
theorem finite_crossingSupport_all_of_zero {scene : MatchingScene}
    (hp : IsSimplePerfectMatching scene)
    (hzero : (Function.support (fun i : SourceAtom scene ↦
      crossingSign i.val.1 (atomAssignment hp i).val.1 0)).Finite) (x : ℝ) :
    (Function.support (fun i : SourceAtom scene ↦
      crossingSign i.val.1 (atomAssignment hp i).val.1 x)).Finite := by
  have hs := LocalConfiguration.finite_cutIncrement_support scene.source 0 x
  have ht := LocalConfiguration.finite_cutIncrement_support scene.target 0 x
  have htt : (Function.support (fun i : SourceAtom scene ↦
      LocalConfiguration.cutIncrement 0 x (atomAssignment hp i).val.1)).Finite :=
    ht.preimage (atomAssignment hp).injective.injOn
  apply ((hzero.union hs).union htt).subset
  intro i hi
  by_contra hn
  have hh : crossingSign i.val.1 (atomAssignment hp i).val.1 0 = 0 ∧
      LocalConfiguration.cutIncrement 0 x i.val.1 = 0 ∧
      LocalConfiguration.cutIncrement 0 x (atomAssignment hp i).val.1 = 0 := by
    simpa only [Set.mem_union, not_or, Function.mem_support, not_not, and_assoc] using hn
  exact hi (by
    change crossingSign i.val.1 (atomAssignment hp i).val.1 x = 0
    rw [crossingSign_eq_zero_add_increments, hh.1, hh.2.1, hh.2.2]
    ring)

/-- The actual infinite matching current satisfies the same count increment as the environment.
All sums involved have finite support, proved from the single root crossing bound. -/
theorem current_eq_root_add_currentIncrement {scene : MatchingScene}
    (hp : IsSimplePerfectMatching scene)
    (hsource : ∀ p, LocalConfiguration.multiplicity scene.source p ≤ 1)
    (htarget : ∀ p, LocalConfiguration.multiplicity scene.target p ≤ 1)
    (hzero : (Function.support (fun i : SourceAtom scene ↦
      crossingSign i.val.1 (atomAssignment hp i).val.1 0)).Finite) (x : ℝ) :
    (spatialMatching hp).current x = (spatialMatching hp).current 0 + scene.currentIncrement 0 x := by
  have hs := LocalConfiguration.finite_cutIncrement_support scene.source 0 x
  have ht := LocalConfiguration.finite_cutIncrement_support scene.target 0 x
  have htt : (Function.support (fun i : SourceAtom scene ↦
      LocalConfiguration.cutIncrement 0 x (atomAssignment hp i).val.1)).Finite :=
    ht.preimage (atomAssignment hp).injective.injOn
  have hi₀ : Summable (fun i : SourceAtom scene ↦
      crossingSign i.val.1 (atomAssignment hp i).val.1 0) := summable_of_hasFiniteSupport hzero
  have hiS : Summable (fun i : SourceAtom scene ↦
      LocalConfiguration.cutIncrement 0 x i.val.1) := summable_of_hasFiniteSupport hs
  have hiT : Summable (fun i : SourceAtom scene ↦
      LocalConfiguration.cutIncrement 0 x (atomAssignment hp i).val.1) := summable_of_hasFiniteSupport htt
  change (∑' i : SourceAtom scene, crossingSign i.val.1 (atomAssignment hp i).val.1 x) = _
  have heq : (fun i : SourceAtom scene ↦ crossingSign i.val.1 (atomAssignment hp i).val.1 x) =
      (fun i ↦ crossingSign i.val.1 (atomAssignment hp i).val.1 0 +
        LocalConfiguration.cutIncrement 0 x i.val.1 -
        LocalConfiguration.cutIncrement 0 x (atomAssignment hp i).val.1) := by
    funext i
    exact crossingSign_eq_zero_add_increments _ _ _
  rw [heq, (hi₀.add hiS).tsum_sub hiT, hi₀.tsum_add hiS]
  rw [(atomAssignment hp).tsum_eq (fun i ↦ LocalConfiguration.cutIncrement 0 x i.val.1)]
  rw [← LocalConfiguration.orientedCount_eq_tsum_atoms scene.source hsource,
    ← LocalConfiguration.orientedCount_eq_tsum_atoms scene.target htarget]
  change (spatialMatching hp).current 0 + LocalConfiguration.orientedCount scene.source 0 x -
    LocalConfiguration.orientedCount scene.target 0 x = _
  unfold currentIncrement
  ring

/-- Root-current recovery identifies the matching current at every real cut. -/
theorem current_eq_currentAt_of_zero {scene : MatchingScene}
    (hp : IsSimplePerfectMatching scene)
    (hsource : ∀ p, LocalConfiguration.multiplicity scene.source p ≤ 1)
    (htarget : ∀ p, LocalConfiguration.multiplicity scene.target p ≤ 1)
    (hzero : (Function.support (fun i : SourceAtom scene ↦
      crossingSign i.val.1 (atomAssignment hp i).val.1 0)).Finite)
    (hcurrent : (spatialMatching hp).current 0 = scene.path.rootCurrent) :
    ∀ x : ℝ, (spatialMatching hp).current x = scene.currentAt x := by
  intro x
  rw [current_eq_root_add_currentIncrement hp hsource htarget hzero x, hcurrent]
  rfl

/-- Every strict crossing family is finite after the proved root crossing recovery. -/
theorem finite_crosses_all_of_zero {scene : MatchingScene}
    (hp : IsSimplePerfectMatching scene)
    (hzero : (Function.support (fun i : SourceAtom scene ↦
      crossingSign i.val.1 (atomAssignment hp i).val.1 0)).Finite) :
    ∀ x : ℝ, {i : SourceAtom scene | OTSelector.Matching.Crosses x
      ((spatialMatching hp).source i) ((spatialMatching hp).target ((spatialMatching hp).assignment i))}.Finite := by
  intro x
  apply (finite_crossingSupport_all_of_zero hp hzero x).subset
  intro i hi
  change crossingSign i.val.1 (atomAssignment hp i).val.1 x ≠ 0
  rcases hi with hi | hi
  · simp only [spatialMatching] at hi
    simp [crossingSign, hi.1.le, not_le.mpr hi.2]
  · simp only [spatialMatching] at hi
    simp [crossingSign, hi.1.le, not_le.mpr hi.2]

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.PointProcess.MatchingScene

/-- A true fixed-energy weak scene limit has zero relative matching flux at every spatial cut.
The only environment inputs are endpoint simplicity and absence of an endpoint at the root. -/
theorem ae_current_eq_currentAt_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν)) {C ρ : ℝ}
    (henergy : ∀ᶠ k in atTop, (∑ i,
      ((sample k).targetIntersection (graph k) (assignment k i) -
        (sample k).sourceIntersection (graph k) i) ^ 2) ≤ C * (b k - a k))
    (hcount : ∀ᶠ k in atTop, (N k : ℝ) ≤ ρ * (b k - a k))
    (hzero : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      (∀ x : SourceAtom scene, x.val.1 ≠ 0) ∧ (∀ y : TargetAtom scene, y.val.1 ≠ 0))
    (hsimple : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      (∀ p, LocalConfiguration.multiplicity scene.source p ≤ 1) ∧
      (∀ p, LocalConfiguration.multiplicity scene.target p ≤ 1)) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), ∀ hp : IsSimplePerfectMatching scene,
      (∀ x : ℝ, (spatialMatching hp).current x = scene.currentAt x) ∧
      (∀ x : ℝ, {i : SourceAtom scene | OTSelector.Matching.Crosses x
        ((spatialMatching hp).source i)
        ((spatialMatching hp).target ((spatialMatching hp).assignment i))}.Finite) := by
  have hroot := ae_current_zero_of_rootedMatchingSceneLaw_tendsto
    sample graph assignment a b hab hlaw hμ henergy hcount hzero
  filter_upwards [hroot, hsimple] with scene hr hs hp
  exact ⟨current_eq_currentAt_of_zero hp hs.1 hs.2 (hr hp).1 (hr hp).2,
    finite_crosses_all_of_zero hp (hr hp).1⟩

end OTSelector.PointProcess.MatchingScene
