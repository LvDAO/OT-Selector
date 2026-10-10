import OTSelector.Matching.DisagreementPermutation
import Mathlib.Dynamics.PeriodicPts.Defs

/-!+# Spatial ends of an actual partner orbit

Infinite partner orbits have no repeated labels. Local endpoint finiteness and
finite matching crossings then force each one-sided trajectory to escape toward
one of the two spatial infinities.
-/

open Function Set Filter
open scoped BigOperators Classical

namespace OTSelector.Matching

/-- A positive action period makes the entire integer orbit finite. -/
theorem finite_sameCycle_of_period_pos {S : Type*} (p : Equiv.Perm S) (i : S)
    (hp : 0 < MulAction.period p i) : {j | p.SameCycle i j}.Finite := by
  let f : Fin (MulAction.period p i) → S := fun n ↦ (p ^ (n.val : ℤ)) i
  apply (Set.finite_range f).subset
  rintro j ⟨n, rfl⟩
  have hmod0 : 0 ≤ n % (MulAction.period p i : ℤ) := Int.emod_nonneg _ (by omega)
  have hmodlt : n % (MulAction.period p i : ℤ) < MulAction.period p i :=
    Int.emod_lt_of_pos _ (by exact_mod_cast hp)
  refine ⟨⟨(n % (MulAction.period p i : ℤ)).toNat, by omega⟩, ?_⟩
  change (p ^ (((n % (MulAction.period p i : ℤ)).toNat : ℕ) : ℤ)) i = (p ^ n) i
  rw [Int.toNat_of_nonneg hmod0]
  exact MulAction.zpow_mod_period_smul (g := p) (a := i) n

/-- An infinite orbit is genuinely a bi-infinite sequence of distinct source labels. -/
theorem zpow_apply_injective_of_infinite_sameCycle {S : Type*} (p : Equiv.Perm S) (i : S)
    (hinfinite : {j | p.SameCycle i j}.Infinite) : Injective (fun n : ℤ ↦ (p ^ n) i) := by
  have hp : MulAction.period p i = 0 := by
    by_contra h
    exact hinfinite (finite_sameCycle_of_period_pos p i (Nat.pos_of_ne_zero h))
  intro m n hmn
  have hz : (p ^ (-n + m)) i = i := by
    have h := congrArg (fun j ↦ (p ^ (-n)) j) hmn
    simpa only [← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel,
      zpow_zero, Equiv.Perm.one_apply] using h
  have hd := (MulAction.zpow_smul_eq_iff_period_dvd (g := p) (a := i)).mp hz
  rw [hp] at hd
  norm_num at hd
  omega

/-- A Boolean predicate with only finitely many consecutive changes eventually stabilizes. -/
theorem eventually_predicate_constant {P : ℕ → Prop}
    (hfinite : {n | ¬ (P n ↔ P (n + 1))}.Finite) :
    (∀ᶠ n in atTop, P n) ∨ ∀ᶠ n in atTop, ¬ P n := by
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  have hstable : ∀ n, P (N + 1) ↔ P (N + 1 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : P (N + 1 + n) ↔ P (N + 1 + n + 1) := by
        by_contra h
        have := hN h
        omega
      change P (N + 1) ↔ P (N + 1 + (n + 1))
      rw [← Nat.add_assoc]
      exact ih.trans hn
  by_cases hP : P (N + 1)
  · left
    filter_upwards [eventually_ge_atTop (N + 1)] with n hn
    simpa only [Nat.add_sub_of_le hn] using (hstable (n - (N + 1))).mp hP
  · right
    filter_upwards [eventually_ge_atTop (N + 1)] with n hn
    simpa only [Nat.add_sub_of_le hn] using (hstable (n - (N + 1))).not.mp hP

/-- Finite visits to bounded windows and finitely many crossings of one cut force an end. -/
theorem tendsto_infinity_of_finite_visits {x : ℕ → ℝ}
    (hvisit : ∀ a b, {n | x n ∈ Icc a b}.Finite)
    (hcross : {n | ¬ (x n < 0 ↔ x (n + 1) < 0)}.Finite) :
    Tendsto x atTop atTop ∨ Tendsto x atTop atBot := by
  rcases eventually_predicate_constant hcross with hneg | hpos
  · right
    apply tendsto_atBot.mpr
    intro b
    obtain ⟨N, hN⟩ := (hvisit b 0).bddAbove
    filter_upwards [hneg, eventually_gt_atTop N] with n hn hlarge
    by_contra h
    exact (not_le_of_gt hlarge) (hN ⟨(not_le.mp h).le, hn.le⟩)
  · left
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨N, hN⟩ := (hvisit 0 b).bddAbove
    filter_upwards [hpos, eventually_gt_atTop N] with n hn hlarge
    by_contra h
    exact (not_le_of_gt hlarge) (hN ⟨not_lt.mp hn, (not_le.mp h).le⟩)

/-- Two ends tending to the right bound the full integer orbit from below. -/
theorem partner_orbit_bddBelow_of_two_right_ends {S : Type*}
    (p : Equiv.Perm S) (source : S → ℝ) (i : S)
    (hf : Tendsto (fun n : ℕ ↦ source ((p ^ n) i)) atTop atTop)
    (hb : Tendsto (fun n : ℕ ↦ source ((p.symm ^ n) i)) atTop atTop) :
    BddBelow (range (fun n : ℤ ↦ source ((p ^ n) i))) := by
  obtain ⟨a, ha⟩ := bddBelow_range_of_tendsto_atTop_atTop hf
  obtain ⟨b, hb⟩ := bddBelow_range_of_tendsto_atTop_atTop hb
  refine ⟨min a b, ?_⟩
  rintro x ⟨n, rfl⟩
  cases n with
  | ofNat n => exact min_le_left a b |>.trans (ha ⟨n, by simp⟩)
  | negSucc n =>
    apply (min_le_right a b).trans
    dsimp only
    rw [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def]
    exact hb ⟨n + 1, rfl⟩

/-- Two ends tending to the left bound the full integer orbit from above. -/
theorem partner_orbit_bddAbove_of_two_left_ends {S : Type*}
    (p : Equiv.Perm S) (source : S → ℝ) (i : S)
    (hf : Tendsto (fun n : ℕ ↦ source ((p ^ n) i)) atTop atBot)
    (hb : Tendsto (fun n : ℕ ↦ source ((p.symm ^ n) i)) atTop atBot) :
    BddAbove (range (fun n : ℤ ↦ source ((p ^ n) i))) := by
  obtain ⟨a, ha⟩ := bddAbove_range_of_tendsto_atTop_atBot hf
  obtain ⟨b, hb⟩ := bddAbove_range_of_tendsto_atTop_atBot hb
  refine ⟨max a b, ?_⟩
  rintro x ⟨n, rfl⟩
  cases n with
  | ofNat n => exact (ha ⟨n, by simp⟩).trans (le_max_left a b)
  | negSucc n =>
    apply le_trans _ (le_max_right a b)
    dsimp only
    rw [zpow_negSucc, ← inv_pow, Equiv.Perm.inv_def]
    exact hb ⟨n + 1, rfl⟩

private theorem connected_pair_meets_window (a b c : ℝ) (h : ¬ (a < 0 ↔ c < 0)) :
    ((a < 1 ∨ b < 1) ∧ (-1 < a ∨ -1 < b)) ∨
      ((c < 1 ∨ b < 1) ∧ (-1 < c ∨ -1 < b)) := by
  by_cases ha : a < 0
  · have hc : 0 ≤ c := not_lt.mp (fun hc ↦ h ⟨fun _ ↦ hc, fun _ ↦ ha⟩)
    by_cases hb : b < 1
    · exact Or.inr ⟨Or.inr hb, Or.inl (by linarith)⟩
    · exact Or.inl ⟨Or.inl (by linarith), Or.inr (by linarith)⟩
  · have hc : c < 0 := by
      by_contra hc
      exact h ⟨fun h ↦ (ha h).elim, fun h ↦ (hc h).elim⟩
    by_cases hb : b < 1
    · exact Or.inl ⟨Or.inr hb, Or.inl (by linarith)⟩
    · exact Or.inr ⟨Or.inl (by linarith), Or.inr (by linarith)⟩

namespace SpatialMatching

variable {S T : Type*}

/-- Actual consecutive disagreement vertices share a target of the two matchings. -/
theorem partner_step_meets_window (M₁ M₂ : SpatialMatching S T)
    (hs : M₁.source = M₂.source) (ht : M₁.target = M₂.target) (i : S)
    (h : ¬ (M₁.source i < 0 ↔ M₁.source (M₁.partnerPermutation M₂ i) < 0)) :
    i ∈ M₁.edgesMeeting (-1) 1 ∨
      M₁.partnerPermutation M₂ i ∈ M₂.edgesMeeting (-1) 1 := by
  have hh := connected_pair_meets_window (M₁.source i) (M₁.target (M₁.assignment i))
    (M₁.source (M₁.partnerPermutation M₂ i)) h
  simpa only [edgesMeeting, Set.mem_ofPred_eq, hs, ht, assignment_partnerPermutation] using hh

/-- Every injective forward partner trajectory has a spatial end. Only the original
endpoint local finiteness and the four boundary crossing families are required. -/
theorem partner_forward_tendsto_infinity (M₁ M₂ : SpatialMatching S T)
    (hs : M₁.source = M₂.source) (ht : M₁.target = M₂.target)
    (hloc₁ : M₁.LocallyFinite) (hloc₂ : M₂.LocallyFinite)
    (hcross₁ : ∀ c ∈ ({-1, 1} : Set ℝ),
      {i | Crosses c (M₁.source i) (M₁.target (M₁.assignment i))}.Finite)
    (hcross₂ : ∀ c ∈ ({-1, 1} : Set ℝ),
      {i | Crosses c (M₂.source i) (M₂.target (M₂.assignment i))}.Finite)
    (i : S) (hi : {j | (M₁.partnerPermutation M₂).SameCycle i j}.Infinite) :
    Tendsto (fun n : ℕ ↦ M₁.source ((M₁.partnerPermutation M₂ ^ n) i)) atTop atTop ∨
      Tendsto (fun n : ℕ ↦ M₁.source ((M₁.partnerPermutation M₂ ^ n) i)) atTop atBot := by
  let p := M₁.partnerPermutation M₂
  have hinj : Injective (fun n : ℕ ↦ (p ^ n) i) := by
    intro m n h
    have hh := zpow_apply_injective_of_infinite_sameCycle p i hi
      (show (p ^ (m : ℤ)) i = (p ^ (n : ℤ)) i by simpa using h)
    exact_mod_cast hh
  have hE₁ := M₁.finite_edgesMeeting hloc₁ (-1) 1 (hcross₁ _ (by simp)) (hcross₁ _ (by simp))
  have hE₂ := M₂.finite_edgesMeeting hloc₂ (-1) 1 (hcross₂ _ (by simp)) (hcross₂ _ (by simp))
  apply tendsto_infinity_of_finite_visits
  · intro a b
    change ((fun n : ℕ ↦ (p ^ n) i) ⁻¹' {j : S | M₁.source j ∈ Icc a b}).Finite
    exact Set.Finite.preimage hinj.injOn (hloc₁.1 a b)
  · have hnextinj : Injective (fun n : ℕ ↦ p ((p ^ n) i)) := p.injective.comp hinj
    apply ((Set.Finite.preimage hinj.injOn hE₁).union
      (Set.Finite.preimage hnextinj.injOn hE₂)).subset
    intro n hn
    have hstep : (p ^ (n + 1)) i = p ((p ^ n) i) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    change ¬ (M₁.source ((p ^ n) i) < 0 ↔ M₁.source ((p ^ (n + 1)) i) < 0) at hn
    rw [hstep] at hn
    exact partner_step_meets_window M₁ M₂ hs ht ((p ^ n) i) hn

/-- Reversing the two matchings gives the other spatial end of the same actual orbit. -/
theorem partner_backward_tendsto_infinity (M₁ M₂ : SpatialMatching S T)
    (hs : M₁.source = M₂.source) (ht : M₁.target = M₂.target)
    (hloc₁ : M₁.LocallyFinite) (hloc₂ : M₂.LocallyFinite)
    (hcross₁ : ∀ c ∈ ({-1, 1} : Set ℝ),
      {i | Crosses c (M₁.source i) (M₁.target (M₁.assignment i))}.Finite)
    (hcross₂ : ∀ c ∈ ({-1, 1} : Set ℝ),
      {i | Crosses c (M₂.source i) (M₂.target (M₂.assignment i))}.Finite)
    (i : S) (hi : {j | (M₁.partnerPermutation M₂).SameCycle i j}.Infinite) :
    Tendsto (fun n : ℕ ↦ M₁.source (((M₁.partnerPermutation M₂).symm ^ n) i)) atTop atTop ∨
      Tendsto (fun n : ℕ ↦ M₁.source (((M₁.partnerPermutation M₂).symm ^ n) i)) atTop atBot := by
  have hinv : {j | (M₂.partnerPermutation M₁).SameCycle i j}.Infinite := by
    simpa only [show M₂.partnerPermutation M₁ = (M₁.partnerPermutation M₂)⁻¹ from rfl,
      Equiv.Perm.sameCycle_inv] using hi
  simpa only [← hs, show M₂.partnerPermutation M₁ = (M₁.partnerPermutation M₂).symm from rfl] using
    partner_forward_tendsto_infinity M₂ M₁ hs.symm ht.symm hloc₂ hloc₁ hcross₂ hcross₁ i hinv

private theorem same_side_of_not_crosses {cut x y : ℝ}
    (hx : x ≠ cut) (hy : y ≠ cut) (h : ¬ Crosses cut x y) : x < cut ↔ y < cut := by
  constructor
  · intro hxc
    by_contra hyc
    exact h (Or.inl ⟨hxc, lt_of_le_of_ne (not_lt.mp hyc) hy.symm⟩)
  · intro hyc
    by_contra hxc
    exact h (Or.inr ⟨hyc, lt_of_le_of_ne (not_lt.mp hxc) hx.symm⟩)

/-- A common non-event empty cut preserves the spatial side at each actual partner step. -/
theorem partner_same_side_of_empty_cut (M₁ M₂ : SpatialMatching S T)
    (hs : M₁.source = M₂.source) (ht : M₁.target = M₂.target) (cut : ℝ)
    (hsne : ∀ i, M₁.source i ≠ cut) (htne : ∀ j, M₁.target j ≠ cut)
    (hcut₁ : ∀ i, ¬ Crosses cut (M₁.source i) (M₁.target (M₁.assignment i)))
    (hcut₂ : ∀ i, ¬ Crosses cut (M₂.source i) (M₂.target (M₂.assignment i)))
    (i : S) : M₁.source i < cut ↔ M₁.source (M₁.partnerPermutation M₂ i) < cut := by
  have h₁ := same_side_of_not_crosses (hsne i) (htne (M₁.assignment i)) (hcut₁ i)
  have h₂ := same_side_of_not_crosses
    (show M₂.source (M₁.partnerPermutation M₂ i) ≠ cut by rw [← hs]; exact hsne _)
    (show M₂.target (M₂.assignment (M₁.partnerPermutation M₂ i)) ≠ cut by
      rw [← ht]; exact htne _) (hcut₂ (M₁.partnerPermutation M₂ i))
  rw [← hs, ← ht, assignment_partnerPermutation] at h₂
  exact h₁.trans h₂.symm

/-- A common empty cut confines the whole forward partner orbit to one side. -/
theorem partner_forward_same_side_of_empty_cut (M₁ M₂ : SpatialMatching S T)
    (hs : M₁.source = M₂.source) (ht : M₁.target = M₂.target) (cut : ℝ)
    (hsne : ∀ i, M₁.source i ≠ cut) (htne : ∀ j, M₁.target j ≠ cut)
    (hcut₁ : ∀ i, ¬ Crosses cut (M₁.source i) (M₁.target (M₁.assignment i)))
    (hcut₂ : ∀ i, ¬ Crosses cut (M₂.source i) (M₂.target (M₂.assignment i)))
    (i : S) (n : ℕ) :
    M₁.source i < cut ↔ M₁.source ((M₁.partnerPermutation M₂ ^ n) i) < cut := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (partner_same_side_of_empty_cut M₁ M₂ hs ht cut hsne htne hcut₁ hcut₂ _)

/-- A common non-event empty cut cannot coexist with an orbit whose two ends have
opposite signs. The end alternatives themselves are supplied by finite crossings. -/
theorem not_opposite_ends_of_empty_cut (M₁ M₂ : SpatialMatching S T)
    (hs : M₁.source = M₂.source) (ht : M₁.target = M₂.target) (cut : ℝ)
    (hsne : ∀ i, M₁.source i ≠ cut) (htne : ∀ j, M₁.target j ≠ cut)
    (hcut₁ : ∀ i, ¬ Crosses cut (M₁.source i) (M₁.target (M₁.assignment i)))
    (hcut₂ : ∀ i, ¬ Crosses cut (M₂.source i) (M₂.target (M₂.assignment i))) (i : S) :
    ¬ ((Tendsto (fun n : ℕ ↦ M₁.source ((M₁.partnerPermutation M₂ ^ n) i)) atTop atTop ∧
        Tendsto (fun n : ℕ ↦ M₁.source (((M₁.partnerPermutation M₂).symm ^ n) i)) atTop atBot) ∨
      (Tendsto (fun n : ℕ ↦ M₁.source ((M₁.partnerPermutation M₂ ^ n) i)) atTop atBot ∧
        Tendsto (fun n : ℕ ↦ M₁.source (((M₁.partnerPermutation M₂).symm ^ n) i)) atTop atTop)) := by
  have hf := partner_forward_same_side_of_empty_cut M₁ M₂ hs ht cut hsne htne hcut₁ hcut₂ i
  have hb : ∀ n : ℕ, M₁.source i < cut ↔
      M₁.source (((M₁.partnerPermutation M₂).symm ^ n) i) < cut := by
    intro n
    simpa only [← hs, show M₂.partnerPermutation M₁ = (M₁.partnerPermutation M₂).symm from rfl]
      using partner_forward_same_side_of_empty_cut M₂ M₁ hs.symm ht.symm cut
        (fun j ↦ by rw [← hs]; exact hsne j)
        (fun j ↦ by rw [← ht]; exact htne j) hcut₂ hcut₁ i n
  have htop {x : ℕ → ℝ} (hside : ∀ n, M₁.source i < cut ↔ x n < cut)
      (h : Tendsto x atTop atTop) : ¬ M₁.source i < cut := by
    intro hi
    obtain ⟨n, hn⟩ := (h.eventually (eventually_ge_atTop cut)).exists
    exact (not_lt_of_ge hn) ((hside n).mp hi)
  have hbot {x : ℕ → ℝ} (hside : ∀ n, M₁.source i < cut ↔ x n < cut)
      (h : Tendsto x atTop atBot) : M₁.source i < cut := by
    obtain ⟨n, hn⟩ := (h.eventually (eventually_lt_atBot cut)).exists
    exact (hside n).mpr hn
  rintro (⟨hft, hbb⟩ | ⟨hfb, hbt⟩)
  · exact htop hf hft (hbot hb hbb)
  · exact htop hb hbt (hbot hf hfb)

end SpatialMatching

end OTSelector.Matching
