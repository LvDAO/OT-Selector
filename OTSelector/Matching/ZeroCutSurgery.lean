import OTSelector.PointProcess.MatchingLocalLimit
import Mathlib.Logic.Equiv.Sum

/-!
# Finite zero-current cut surgery

A balanced finite family of edges crossing a cut is repaired by an actual permutation
of its target labels. Extending this permutation gives a perfect matching and fixes
every unselected row. The cost estimate uses the genuine quadratic feedback gauge.
-/

open Function Set
open scoped BigOperators Classical

namespace OTSelector.Matching

/-- A spatial perfect matching is a bijection of source and target labels. -/
structure SpatialMatching (S T : Type*) where
  source : S → ℝ
  target : T → ℝ
  assignment : S ≃ T

namespace SpatialMatching

variable {S T J : Type*} [Fintype J]

/-- Reassign the targets of finitely many rows, preserving the full bijection. -/
noncomputable def rematch (M : SpatialMatching S T) (selected : J ↪ S)
    (tau : Equiv.Perm J) : SpatialMatching S T where
  source := M.source
  target := M.target
  assignment := (tau.viaFintypeEmbedding selected).trans M.assignment

@[simp]
theorem rematch_selected (M : SpatialMatching S T) (selected : J ↪ S)
    (tau : Equiv.Perm J) (j : J) :
    (M.rematch selected tau).assignment (selected j) =
      M.assignment (selected (tau j)) := by
  simp [rematch]

theorem rematch_unselected (M : SpatialMatching S T) (selected : J ↪ S)
    (tau : Equiv.Perm J) {i : S} (hi : i ∉ range selected) :
    (M.rematch selected tau).assignment i = M.assignment i := by
  simp only [rematch, Equiv.trans_apply,
    tau.viaFintypeEmbedding_apply_notMem_range selected hi]

end SpatialMatching

/-- Strict crossing is sufficient because the surgery cut is not an event coordinate. -/
def Crosses (cut source target : ℝ) : Prop :=
  (source < cut ∧ cut < target) ∨ (target < cut ∧ cut < source)

namespace SpatialMatching

variable {S T : Type*}

/-- Local finiteness is imposed on endpoint labels, so multiplicities are counted. -/
def LocallyFinite (M : SpatialMatching S T) : Prop :=
  (∀ a b, {i | M.source i ∈ Icc a b}.Finite) ∧
    ∀ a b, {j | M.target j ∈ Icc a b}.Finite

/-- The finite modification consists precisely of old edges meeting the open cut interval. -/
def edgesMeeting (M : SpatialMatching S T) (left right : ℝ) : Set S :=
  {i | (M.source i < right ∨ M.target (M.assignment i) < right) ∧
    (left < M.source i ∨ left < M.target (M.assignment i))}

/-- Local endpoint finiteness and finite crossings at the two boundary cuts make the
entire selected edge family finite. No moment bound on the matching is used. -/
theorem finite_edgesMeeting (M : SpatialMatching S T) (hloc : M.LocallyFinite)
    (left right : ℝ)
    (hleft : {i | Crosses left (M.source i) (M.target (M.assignment i))}.Finite)
    (hright : {i | Crosses right (M.source i) (M.target (M.assignment i))}.Finite) :
    (M.edgesMeeting left right).Finite := by
  apply (((hloc.1 left right).union hleft).union hright).subset
  intro i hi
  change (M.source i < right ∨ M.target (M.assignment i) < right) ∧
    (left < M.source i ∨ left < M.target (M.assignment i)) at hi
  by_cases hl : M.source i < left
  · apply Or.inl ∘ Or.inr
    apply Or.inl
    refine ⟨hl, ?_⟩
    rcases hi.2 with hs | ht
    · linarith
    · exact ht
  · by_cases hr : right < M.source i
    · apply Or.inr
      apply Or.inr
      refine ⟨?_, hr⟩
      rcases hi.1 with hs | ht
      · linarith
      · exact ht
    · exact Or.inl (Or.inl ⟨not_lt.mp hl, not_lt.mp hr⟩)

end SpatialMatching

/-- A permutation exchanging the two sides of a finite partition. -/
noncomputable def exchangeSides {J : Type*} (p : J → Prop)
    (e : {j // p j} ≃ {j // ¬p j}) : Equiv.Perm J :=
  (Equiv.sumCompl p).symm.trans
    ((Equiv.sumCongr e e.symm).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl p)))

theorem exchangeSides_side {J : Type*} (p : J → Prop)
    (e : {j // p j} ≃ {j // ¬p j}) (j : J) :
    p (exchangeSides p e j) ↔ ¬p j := by
  by_cases hj : p j
  · simp [exchangeSides, Equiv.sumCompl_symm_apply_of_pos hj, hj,
      (e ⟨j, hj⟩).property]
  · simp [exchangeSides, Equiv.sumCompl_symm_apply_of_neg hj, hj,
      (e.symm ⟨j, hj⟩).property]

/-- Vanishing oriented current gives the equal cardinalities used in the repair. -/
theorem card_sides_eq_of_zero_current {J : Type*} [Fintype J] (p : J → Prop)
    (hzero : (∑ j, if p j then (1 : ℤ) else -1) = 0) :
    Fintype.card {j // p j} = Fintype.card {j // ¬p j} := by
  have hsum : (∑ j, if p j then (1 : ℤ) else -1) =
      Fintype.card {j // p j} - (Fintype.card {j // ¬p j} : ℤ) := by
    rw [Finset.sum_ite]
    simp [Fintype.card_subtype, sub_eq_add_neg]
  rw [hsum] at hzero
  exact_mod_cast sub_eq_zero.mp hzero

private theorem endpoint_distance_le {x s t : ℝ} (h : Crosses x s t) :
    |s - x| ≤ |t - s| ∧ |t - x| ≤ |t - s| := by
  rcases h with h | h
  · rw [abs_of_nonpos (by linarith : s - x ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ t - x),
      abs_of_nonneg (by linarith : 0 ≤ t - s)]
    constructor <;> linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ s - x),
      abs_of_nonpos (by linarith : t - x ≤ 0),
      abs_of_nonpos (by linarith : t - s ≤ 0)]
    constructor <;> linarith

/-- Every balanced finite crossing family admits a target permutation whose new edges
lie entirely on their source side and have length at most twice the old total length. -/
theorem exists_zero_cut_repair {J : Type*} [Fintype J]
    (source target : J → ℝ) (cut theta : ℝ)
    (hcross : ∀ j, Crosses cut (source j) (target j))
    (hzero : (∑ j, if source j < cut then (1 : ℤ) else -1) = 0)
    (hlength : ∑ j, |target j - source j| ≤ theta) :
    ∃ tau : Equiv.Perm J,
      (∀ j, (source j < cut ∧ target (tau j) < cut) ∨
        (cut < source j ∧ cut < target (tau j))) ∧
      ∀ j, |target (tau j) - source j| ≤ 2 * theta := by
  let p : J → Prop := fun j ↦ source j < cut
  let e := Fintype.equivOfCardEq (card_sides_eq_of_zero_current p hzero)
  let tau := exchangeSides p e
  have hside (j : J) := exchangeSides_side p e j
  have hend (j : J) : |source j - cut| ≤ theta ∧ |target j - cut| ≤ theta := by
    have hi : |target j - source j| ≤ theta :=
      (Finset.single_le_sum (fun k _ ↦ abs_nonneg (target k - source k))
        (Finset.mem_univ j)).trans hlength
    exact ⟨(endpoint_distance_le (hcross j)).1.trans hi,
      (endpoint_distance_le (hcross j)).2.trans hi⟩
  refine ⟨tau, ?_, ?_⟩
  · intro j
    rcases hcross j with hj | hj
    · have hn : ¬source (tau j) < cut := by
        intro ht
        exact (hside j).1 ht hj.1
      rcases hcross (tau j) with ht | ht
      · exact (hn ht.1).elim
      · exact Or.inl ⟨hj.1, ht.1⟩
    · have ht : source (tau j) < cut := (hside j).2 (by dsimp [p]; linarith)
      rcases hcross (tau j) with hk | hk
      · exact Or.inr ⟨hj.2, hk.2⟩
      · linarith
  · intro j
    calc
      |target (tau j) - source j| ≤
          |target (tau j) - cut| + |cut - source j| := abs_sub_le _ _ _
      _ ≤ theta + theta := add_le_add (hend (tau j)).2 (by
        simpa only [abs_sub_comm] using (hend j).1)
      _ = 2 * theta := by ring

/-- The repair cost is cubic in the common crossing-count/length bound. The inputs
are pointwise coercivity and the actual crossing data, not a repair inequality. -/
theorem exists_zero_cut_repair_cost {J : Type*} [Fintype J]
    (source target : J → ℝ) (cost : J → J → ℝ) (cut theta C : ℝ)
    (hC : 0 ≤ C) (htheta : 0 ≤ theta)
    (hcross : ∀ j, Crosses cut (source j) (target j))
    (hzero : (∑ j, if source j < cut then (1 : ℤ) else -1) = 0)
    (hcount : (Fintype.card J : ℝ) ≤ theta)
    (hlength : ∑ j, |target j - source j| ≤ theta)
    (hcost : ∀ i j, cost i j ≤ C * (target j - source i) ^ 2) :
    ∃ tau : Equiv.Perm J,
      (∀ j, (source j < cut ∧ target (tau j) < cut) ∨
        (cut < source j ∧ cut < target (tau j))) ∧
      (∀ j, |target (tau j) - source j| ≤ 2 * theta) ∧
      (∑ j, cost j (tau j)) ≤ 4 * C * theta ^ 3 := by
  obtain ⟨tau, hs, hd⟩ := exists_zero_cut_repair source target cut theta hcross hzero hlength
  refine ⟨tau, hs, hd, ?_⟩
  calc
    _ ≤ ∑ _j : J, C * (2 * theta) ^ 2 := Finset.sum_le_sum fun j _ ↦ by
      apply (hcost j (tau j)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      nlinarith [sq_abs (target (tau j) - source j), hd j,
        abs_nonneg (target (tau j) - source j)]
    _ = (Fintype.card J : ℝ) * (C * (2 * theta) ^ 2) := by simp
    _ ≤ theta * (C * (2 * theta) ^ 2) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hC (sq_nonneg _))
    _ = 4 * C * theta ^ 3 := by ring

/-- The feedback gauge has the same coercivity constants in either endpoint order. -/
theorem quadraticCost_bounds {lam xi eta a b : ℝ} {g : ℝ → ℝ}
    (hg : Continuous g) (hLip : ScalarLipschitz lam g)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (1 : ℝ) 2) :
    quadraticLowerConstant' lam * (eta - xi) ^ 2 ≤ quadraticCost g xi eta a b ∧
      quadraticCost g xi eta a b ≤ quadraticUpperConstant lam * (eta - xi) ^ 2 := by
  rcases lt_trichotomy xi eta with h | h | h
  · exact ⟨quadraticGauge_lower_bound h hg hLip hlam0 hlam ha hb,
      quadraticGauge_upper_bound h hg hLip hlam0 hlam ha hb⟩
  · subst eta
    have hD : a + b ≠ 0 := by linarith [ha.1, hb.1]
    have hq : fourPointQuotient g xi xi a b = g xi := by
      unfold fourPointQuotient fourPointGap fourPointSourceValue fourPointTargetValue
        fourPointDenominator
      field_simp
      ring
    have hz : quadraticCost g xi xi a b = 0 := by
      simp [quadraticCost, gaugedFourPointCost, hq, fourPointDenominator,
        fourPointSourceValue, fourPointTargetValue]
      ring
    simp [hz]
  · have horder : -xi < -eta := by linarith
    have hlo := quadraticGauge_lower_bound horder (reflectedGraph_continuous hg)
      (reflectedGraph_lipschitz hLip) hlam0 hlam ha hb
    have hup := quadraticGauge_upper_bound horder (reflectedGraph_continuous hg)
      (reflectedGraph_lipschitz hLip) hlam0 hlam ha hb
    rw [quadraticCost_reflected] at hlo hup
    have heq : (-eta - -xi) ^ 2 = (eta - xi) ^ 2 := by ring
    simpa only [heq] using And.intro hlo hup

/-- Zero-cut surgery for the actual quadratic cost and the full physical mark intervals.
No positive lower bound on an individual source mark is needed. -/
theorem exists_marked_zero_cut_repair {J : Type*} [Fintype J]
    (source target : J → PointProcess.MatchingPoint) (cut theta : ℝ)
    {lam : ℝ} {g : ℝ → ℝ} (hg : Continuous g) (hLip : ScalarLipschitz lam g)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8) (htheta : 0 ≤ theta)
    (hcross : ∀ j, Crosses cut (source j).1 (target j).1)
    (hzero : (∑ j, if (source j).1 < cut then (1 : ℤ) else -1) = 0)
    (hcount : (Fintype.card J : ℝ) ≤ theta)
    (hlength : ∑ j, |(target j).1 - (source j).1| ≤ theta) :
    ∃ tau : Equiv.Perm J,
      (∀ j, ((source j).1 < cut ∧ (target (tau j)).1 < cut) ∨
        (cut < (source j).1 ∧ cut < (target (tau j)).1)) ∧
      (∀ j, |(target (tau j)).1 - (source j).1| ≤ 2 * theta) ∧
      (∑ j, PointProcess.markedQuadraticCost g (source j) (target (tau j))) ≤
        4 * quadraticUpperConstant lam * theta ^ 3 := by
  apply exists_zero_cut_repair_cost (fun j ↦ (source j).1) (fun j ↦ (target j).1)
    (fun i j ↦ PointProcess.markedQuadraticCost g (source i) (target j)) cut theta
    (quadraticUpperConstant lam) (by unfold quadraticUpperConstant; positivity)
    htheta hcross hzero hcount hlength
  intro i j
  apply (quadraticCost_bounds hg hLip hlam0 hlam _ _).2
  · constructor <;> linarith [(source i).2.property.1, (source i).2.property.2]
  · constructor <;> linarith [(target j).2.property.1, (target j).2.property.2]

/-- The finite repair produces an actual perfect matching on the original, possibly
infinite, label sets and fixes every row not selected for surgery. -/
theorem SpatialMatching.exists_zero_cut_rematch {S T J : Type*} [Fintype J]
    (M : SpatialMatching S T) (selected : J ↪ S) (cost : S → T → ℝ)
    {cut theta C : ℝ} (hC : 0 ≤ C) (htheta : 0 ≤ theta)
    (hcross : ∀ j, Crosses cut (M.source (selected j))
      (M.target (M.assignment (selected j))))
    (hzero : (∑ j, if M.source (selected j) < cut then (1 : ℤ) else -1) = 0)
    (hcount : (Fintype.card J : ℝ) ≤ theta)
    (hlength : (∑ j, |M.target (M.assignment (selected j)) - M.source (selected j)|) ≤ theta)
    (hcost : ∀ i j, cost i j ≤ C * (M.target j - M.source i) ^ 2) :
    ∃ repaired : SpatialMatching S T,
      repaired.source = M.source ∧ repaired.target = M.target ∧
      (∀ i ∉ range selected, repaired.assignment i = M.assignment i) ∧
      (∀ j, ¬Crosses cut (repaired.source (selected j))
        (repaired.target (repaired.assignment (selected j)))) ∧
      (∑ j, cost (selected j) (repaired.assignment (selected j))) ≤ 4 * C * theta ^ 3 := by
  obtain ⟨tau, hside, _, hbound⟩ := exists_zero_cut_repair_cost
    (fun j ↦ M.source (selected j)) (fun j ↦ M.target (M.assignment (selected j)))
    (fun i j ↦ cost (selected i) (M.assignment (selected j))) cut theta C hC htheta
    hcross hzero hcount hlength (fun i j ↦ hcost (selected i) (M.assignment (selected j)))
  refine ⟨M.rematch selected tau, rfl, rfl, ?_, ?_, ?_⟩
  · intro i hi
    exact M.rematch_unselected selected tau hi
  · intro j
    simp only [SpatialMatching.rematch_selected]
    change ¬Crosses cut (M.source (selected j)) (M.target (M.assignment (selected (tau j))))
    rcases hside j with h | h <;> rintro (hc | hc) <;> linarith
  · simpa only [SpatialMatching.rematch_selected] using hbound

theorem markedQuadraticCost_bounds {lam : ℝ} {g : ℝ → ℝ}
    (hg : Continuous g) (hLip : ScalarLipschitz lam g)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1 / 8)
    (source target : PointProcess.MatchingPoint) :
    quadraticLowerConstant' lam * (target.1 - source.1) ^ 2 ≤
        PointProcess.markedQuadraticCost g source target ∧
      PointProcess.markedQuadraticCost g source target ≤
        quadraticUpperConstant lam * (target.1 - source.1) ^ 2 := by
  apply quadraticCost_bounds hg hLip hlam0 hlam
  · constructor <;> linarith [source.2.property.1, source.2.property.2]
  · constructor <;> linarith [target.2.property.1, target.2.property.2]

end OTSelector.Matching
