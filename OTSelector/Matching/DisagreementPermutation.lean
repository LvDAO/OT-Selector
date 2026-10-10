import OTSelector.Matching.OneStepBootstrap
import OTSelector.Matching.FeedbackNoFiniteTies
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!+# The partner permutation of two locally minimizing matchings

The permutation sends each source to the source having the same target in the
second matching. Restricting it to a finite invariant set gives actual finite
replacement permutations. Local optimality in both directions forces a cost tie.
-/

open Function Set
open scoped BigOperators Classical

namespace OTSelector.Matching

open OTSelector.Limit OTSelector.PointProcess

/-- The actual no-tie property is independent of the chosen finite label type. -/
theorem FeedbackNoFiniteTies.fintype {e : FeedbackEnvironment} (h : FeedbackNoFiniteTies e)
    {J : Type*} [Fintype J] (s t : J → MatchingPoint) (tau : Equiv.Perm J)
    (hs : Injective s) (ht : Injective t)
    (hsa : ∀ i, LocalConfiguration.countingMeasure e.source {s i} ≠ 0)
    (hta : ∀ i, LocalConfiguration.countingMeasure e.target {t i} ≠ 0)
    (htau : tau ≠ Equiv.refl _) :
    (∑ i, markedQuadraticCost e.path.graphHeight (s i) (t i)) ≠
      ∑ i, markedQuadraticCost e.path.graphHeight (s i) (t (tau i)) := by
  let f := Fintype.equivFin J
  let tau' := f.symm.trans (tau.trans f)
  have htau' : tau' ≠ Equiv.refl _ := by
    intro heq
    apply htau
    ext i
    apply f.injective
    have hi := congrArg (fun p : Equiv.Perm (Fin (Fintype.card J)) ↦ p (f i)) heq
    simpa only [tau', Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.refl_apply] using hi
  have hn := h (Fintype.card J) (s ∘ f.symm) (t ∘ f.symm) tau'
    (hs.comp f.symm.injective) (ht.comp f.symm.injective) (fun i ↦ hsa _) (fun i ↦ hta _) htau'
  intro heq
  apply hn
  simp only [Function.comp_apply, tau', Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [f.symm.sum_comp (fun j ↦ markedQuadraticCost e.path.graphHeight (s j) (t j)),
    f.symm.sum_comp (fun j ↦ markedQuadraticCost e.path.graphHeight (s j) (t (tau j)))]
  exact heq

namespace SpatialMatching

variable {S T : Type*}

/-- Follow the first matching to its target and the second matching back to a source. -/
def partnerPermutation (M₁ M₂ : SpatialMatching S T) : Equiv.Perm S :=
  M₁.assignment.trans M₂.assignment.symm

@[simp]
theorem assignment_partnerPermutation (M₁ M₂ : SpatialMatching S T) (i : S) :
    M₂.assignment (M₁.partnerPermutation M₂ i) = M₁.assignment i :=
  M₂.assignment.apply_symm_apply _

@[simp]
theorem assignment_partnerPermutation_symm (M₁ M₂ : SpatialMatching S T) (i : S) :
    M₁.assignment ((M₁.partnerPermutation M₂).symm i) = M₂.assignment i :=
  M₁.assignment.apply_symm_apply _

theorem partnerPermutation_fixed_iff (M₁ M₂ : SpatialMatching S T) (i : S) :
    M₁.partnerPermutation M₂ i = i ↔ M₁.assignment i = M₂.assignment i := by
  constructor
  · intro h
    rw [← assignment_partnerPermutation M₁ M₂ i, h]
  · intro h
    exact M₂.assignment.injective (by simpa using h)

/-- The concrete finite replacement obtained by restricting the partner permutation. -/
def partnerRestriction (M₁ M₂ : SpatialMatching S T) (rows : Finset S)
    (hrows : ∀ i, M₁.partnerPermutation M₂ i ∈ rows ↔ i ∈ rows) : Equiv.Perm rows :=
  (M₁.partnerPermutation M₂).subtypePerm hrows

@[simp]
theorem partnerRestriction_assignment (M₁ M₂ : SpatialMatching S T) (rows : Finset S)
    (hrows : ∀ i, M₁.partnerPermutation M₂ i ∈ rows ↔ i ∈ rows) (i : rows) :
    M₂.assignment (M₁.partnerRestriction M₂ rows hrows i) = M₁.assignment i :=
  assignment_partnerPermutation M₁ M₂ i

@[simp]
theorem partnerRestriction_symm_assignment (M₁ M₂ : SpatialMatching S T) (rows : Finset S)
    (hrows : ∀ i, M₁.partnerPermutation M₂ i ∈ rows ↔ i ∈ rows) (i : rows) :
    M₁.assignment ((M₁.partnerRestriction M₂ rows hrows).symm i) = M₂.assignment i :=
  assignment_partnerPermutation_symm M₁ M₂ i

/-- Two local minimizers have equal cost on every finite invariant disagreement set. -/
theorem finite_invariant_cost_eq (M₁ M₂ : SpatialMatching S T) {cost : S → T → ℝ}
    (hmin₁ : M₁.IsLocallyMinimizing cost) (hmin₂ : M₂.IsLocallyMinimizing cost)
    (rows : Finset S)
    (hrows : ∀ i, M₁.partnerPermutation M₂ i ∈ rows ↔ i ∈ rows) :
    (∑ i : rows, cost i (M₁.assignment i)) = ∑ i : rows, cost i (M₂.assignment i) := by
  apply le_antisymm
  · simpa only [partnerRestriction_symm_assignment] using
      hmin₁ rows (M₁.partnerRestriction M₂ rows hrows).symm
  · simpa only [partnerRestriction_assignment] using
      hmin₂ rows (M₁.partnerRestriction M₂ rows hrows)

/-- A finite partner orbit supplies its invariant finite replacement set. -/
theorem finite_partnerOrbit_cost_eq (M₁ M₂ : SpatialMatching S T) {cost : S → T → ℝ}
    (hmin₁ : M₁.IsLocallyMinimizing cost) (hmin₂ : M₂.IsLocallyMinimizing cost)
    (i : S) (hfinite : {j | (M₁.partnerPermutation M₂).SameCycle i j}.Finite) :
    (∑ j : hfinite.toFinset, cost j (M₁.assignment j)) =
      ∑ j : hfinite.toFinset, cost j (M₂.assignment j) := by
  apply finite_invariant_cost_eq M₁ M₂ hmin₁ hmin₂
  intro j
  simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
    (Equiv.Perm.sameCycle_apply_right (f := M₁.partnerPermutation M₂) (x := i) (y := j))

/-- In an actual no-tie environment, every finite partner orbit is a common edge. -/
theorem finite_partnerOrbit_fixed_of_no_ties
    (M₁ M₂ : SpatialMatching S T) {e : FeedbackEnvironment} (hnotie : FeedbackNoFiniteTies e)
    (source : S → MatchingPoint) (target : T → MatchingPoint)
    (hsource : Injective source) (htarget : Injective target)
    (hsa : ∀ i, LocalConfiguration.countingMeasure e.source {source i} ≠ 0)
    (hta : ∀ i, LocalConfiguration.countingMeasure e.target {target i} ≠ 0)
    (hmin₁ : M₁.IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost e.path.graphHeight (source i) (target j)))
    (hmin₂ : M₂.IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost e.path.graphHeight (source i) (target j)))
    (i : S) (hfinite : {j | (M₁.partnerPermutation M₂).SameCycle i j}.Finite) :
    M₁.assignment i = M₂.assignment i := by
  let rows := hfinite.toFinset
  have hrows : ∀ j, M₁.partnerPermutation M₂ j ∈ rows ↔ j ∈ rows := by
    intro j
    simpa only [rows, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
      (Equiv.Perm.sameCycle_apply_right (f := M₁.partnerPermutation M₂) (x := i) (y := j))
  let tau := M₁.partnerRestriction M₂ rows hrows
  by_contra hi
  have htau : tau ≠ Equiv.refl _ := by
    intro heq
    have himem : i ∈ rows := hfinite.mem_toFinset.mpr (Equiv.Perm.SameCycle.rfl)
    have heqi := congrArg (fun p : Equiv.Perm rows ↦ (p ⟨i, himem⟩).val) heq
    exact hi ((partnerPermutation_fixed_iff M₁ M₂ i).mp heqi)
  have hn := hnotie.fintype (fun j : rows ↦ source j)
    (fun j : rows ↦ target (M₂.assignment j)) tau
    (hsource.comp Subtype.val_injective)
    (htarget.comp (M₂.assignment.injective.comp Subtype.val_injective))
    (fun j ↦ hsa _) (fun j ↦ hta _) htau
  apply hn
  simpa only [tau, partnerRestriction_assignment] using
    (finite_invariant_cost_eq M₁ M₂ hmin₁ hmin₂ rows hrows).symm

/-- Every differing edge lies on an infinite two-sided partner orbit. -/
theorem infinite_partnerOrbit_of_no_ties
    (M₁ M₂ : SpatialMatching S T) {e : FeedbackEnvironment} (hnotie : FeedbackNoFiniteTies e)
    (source : S → MatchingPoint) (target : T → MatchingPoint)
    (hsource : Injective source) (htarget : Injective target)
    (hsa : ∀ i, LocalConfiguration.countingMeasure e.source {source i} ≠ 0)
    (hta : ∀ i, LocalConfiguration.countingMeasure e.target {target i} ≠ 0)
    (hmin₁ : M₁.IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost e.path.graphHeight (source i) (target j)))
    (hmin₂ : M₂.IsLocallyMinimizing
      (fun i j ↦ markedQuadraticCost e.path.graphHeight (source i) (target j)))
    {i : S} (hi : M₁.assignment i ≠ M₂.assignment i) :
    {j | (M₁.partnerPermutation M₂).SameCycle i j}.Infinite := by
  intro hfinite
  exact hi (finite_partnerOrbit_fixed_of_no_ties M₁ M₂ hnotie source target
    hsource htarget hsa hta hmin₁ hmin₂ i hfinite)

end SpatialMatching

end OTSelector.Matching
