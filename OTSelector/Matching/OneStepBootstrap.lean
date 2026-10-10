import OTSelector.Matching.ZeroCutSurgery
import OTSelector.PointProcess.FiniteMatchingTail

/-!
# Two-cut finite rematching and the deterministic energy estimate

The three spatial regions are matched separately. The interior matching is the
environmental comparison matching; the exterior matchings are constructed from
the equal cardinalities forced by zero crossing current.
-/

open Function Set MeasureTheory
open scoped BigOperators Classical

namespace OTSelector.Matching

/-- The left exterior, open interior, and right exterior of two non-event cuts. -/
noncomputable def cutRegion (left right x : ℝ) : Fin 3 :=
  if x < left then 0 else if x < right then 1 else 2

theorem cutRegion_eq_zero {left right x : ℝ} :
    cutRegion left right x = 0 ↔ x < left := by
  by_cases hx : x < left <;> by_cases hr : x < right <;> simp [cutRegion, hx, hr]

theorem cutRegion_eq_one {left right x : ℝ} :
    cutRegion left right x = 1 ↔ ¬x < left ∧ x < right := by
  by_cases hx : x < left <;> simp [cutRegion, hx]

theorem cutRegion_eq_two {left right x : ℝ} (hlr : left < right) :
    cutRegion left right x = 2 ↔ ¬x < right := by
  by_cases hx : x < left
  · have hr : x < right := hx.trans hlr
    simp [cutRegion, hx, hr]
  · simp [cutRegion, hx]

/-- Glue genuine bijections of corresponding fibers into a full bijection. -/
noncomputable def glueRegions {J K A : Type*} (sourceRegion : J → A)
    (targetRegion : K → A)
    (e : ∀ a, {j // sourceRegion j = a} ≃ {k // targetRegion k = a}) : J ≃ K :=
  (Equiv.sigmaFiberEquiv sourceRegion).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv targetRegion))

theorem glueRegions_apply {J K A : Type*} (sourceRegion : J → A)
    (targetRegion : K → A)
    (e : ∀ a, {j // sourceRegion j = a} ≃ {k // targetRegion k = a})
    (a : A) (j : {j // sourceRegion j = a}) :
    glueRegions sourceRegion targetRegion e j = (e a j).val := by
  rcases j with ⟨j, rfl⟩
  rfl

theorem glueRegions_region {J K A : Type*} (sourceRegion : J → A)
    (targetRegion : K → A)
    (e : ∀ a, {j // sourceRegion j = a} ≃ {k // targetRegion k = a}) (j : J) :
    targetRegion (glueRegions sourceRegion targetRegion e j) = sourceRegion j :=
  (e (sourceRegion j) ⟨j, rfl⟩).property

/-- Current written as the difference of source and target left-occupancies. -/
noncomputable def finiteCurrent {J : Type*} [Fintype J]
    (source target : J → ℝ) (cut : ℝ) : ℤ :=
  ∑ j, ((if source j < cut then (1 : ℤ) else 0) -
    (if target j < cut then 1 else 0))

theorem card_left_eq_of_finiteCurrent_eq_zero {J : Type*} [Fintype J]
    (source target : J → ℝ) (cut : ℝ) (hzero : finiteCurrent source target cut = 0) :
    Fintype.card {j // source j < cut} = Fintype.card {j // target j < cut} := by
  unfold finiteCurrent at hzero
  rw [Finset.sum_sub_distrib] at hzero
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    mul_one] at hzero
  simpa only [Fintype.card_subtype] using Int.ofNat_inj.mp (sub_eq_zero.mp hzero)

/-- The three actual endpoint populations have equal sizes at zero-current cuts. -/
theorem card_cutRegion_eq {J : Type*} [Fintype J]
    (source target : J → ℝ) {left right : ℝ} (hlr : left < right)
    (hleft : finiteCurrent source target left = 0)
    (hright : finiteCurrent source target right = 0) (k : Fin 3) :
    Fintype.card {j // cutRegion left right (source j) = k} =
      Fintype.card {j // cutRegion left right (target j) = k} := by
  have h0 := card_left_eq_of_finiteCurrent_eq_zero source target left hleft
  have h2 : Fintype.card {j // ¬source j < right} =
      Fintype.card {j // ¬target j < right} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl,
      card_left_eq_of_finiteCurrent_eq_zero source target right hright]
  have hs : Fintype.card J =
      Fintype.card {j // cutRegion left right (source j) = 0} +
      Fintype.card {j // cutRegion left right (source j) = 1} +
      Fintype.card {j // cutRegion left right (source j) = 2} := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun j ↦
      cutRegion left right (source j))), Fintype.card_sigma, Fin.sum_univ_three]
  have ht : Fintype.card J =
      Fintype.card {j // cutRegion left right (target j) = 0} +
      Fintype.card {j // cutRegion left right (target j) = 1} +
      Fintype.card {j // cutRegion left right (target j) = 2} := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun j ↦
      cutRegion left right (target j))), Fintype.card_sigma, Fin.sum_univ_three]
  simp only [cutRegion_eq_zero, cutRegion_eq_two hlr] at hs ht
  fin_cases k
  · change Fintype.card {j // cutRegion left right (source j) = 0} =
      Fintype.card {j // cutRegion left right (target j) = 0}
    simpa only [cutRegion_eq_zero] using h0
  · change Fintype.card {j // cutRegion left right (source j) = 1} =
      Fintype.card {j // cutRegion left right (target j) = 1}
    omega
  · change Fintype.card {j // cutRegion left right (source j) = 2} =
      Fintype.card {j // cutRegion left right (target j) = 2}
    simpa only [cutRegion_eq_two hlr] using h2

/-- Crossing endpoints are within the total crossing length of their cut. -/
theorem crossing_endpoint_distance {J : Type*} [Fintype J]
    (source target : J → ℝ) (cut theta : ℝ)
    (hlength : (∑ j : {j // Crosses cut (source j) (target j)},
      |target j - source j|) ≤ theta) {j : J} (hj : Crosses cut (source j) (target j)) :
    |source j - cut| ≤ theta ∧ |target j - cut| ≤ theta := by
  have hb : |target j - source j| ≤ theta :=
    (Finset.single_le_sum (fun (k : {j // Crosses cut (source j) (target j)}) _ ↦
      abs_nonneg (target k - source k))
      (Finset.mem_univ (⟨j, hj⟩ : {j // Crosses cut (source j) (target j)}))).trans hlength
  rcases hj with h | h
  · rw [abs_of_nonpos (by linarith : source j - cut ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ target j - cut)]
    rw [abs_of_nonneg (by linarith : 0 ≤ target j - source j)] at hb
    constructor <;> linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ source j - cut),
      abs_of_nonpos (by linarith : target j - cut ≤ 0)]
    rw [abs_of_nonpos (by linarith : target j - source j ≤ 0)] at hb
    constructor <;> linarith

private theorem cubic_sum_bound {J : Type*} [Fintype J] (cost : J → ℝ)
    {C theta : ℝ} (hC : 0 ≤ C)
    (hcount : (Fintype.card J : ℝ) ≤ theta)
    (hcost : ∀ j, cost j ≤ C * (2 * theta) ^ 2) :
    ∑ j, cost j ≤ 4 * C * theta ^ 3 := by
  calc
    _ ≤ ∑ _j : J, C * (2 * theta) ^ 2 := Finset.sum_le_sum fun j _ ↦ hcost j
    _ = (Fintype.card J : ℝ) * (C * (2 * theta) ^ 2) := by simp
    _ ≤ theta * (C * (2 * theta) ^ 2) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hC (sq_nonneg _))
    _ = 4 * C * theta ^ 3 := by ring

private theorem repair_fiber_cost_le {J : Type*} [Fintype J]
    (source target : J → ℝ) (cost : J → J → ℝ) (tau : Equiv.Perm J)
    (p : J → Prop) [DecidablePred p] {cut theta C : ℝ} (hC : 0 ≤ C)
    (htheta : 0 ≤ theta)
    (hcount : (Fintype.card {j // Crosses cut (source j) (target j)} : ℝ) ≤ theta)
    (hlength : (∑ j : {j // Crosses cut (source j) (target j)},
      |target j - source j|) ≤ theta)
    (hcross : ∀ j : {j // p j}, Crosses cut (source j) (target j) ∧
      Crosses cut (source (tau j)) (target (tau j)))
    (hcost : ∀ i j, cost i j ≤ C * (target j - source i) ^ 2) :
    (∑ j : {j // p j}, cost j (tau j)) ≤ 4 * C * theta ^ 3 := by
  apply cubic_sum_bound _ hC
  · apply le_trans _ hcount
    exact_mod_cast Fintype.card_subtype_mono p
      (fun j ↦ Crosses cut (source j) (target j)) (fun j hj ↦ (hcross ⟨j, hj⟩).1)
  · intro j
    have hs := (crossing_endpoint_distance source target cut theta hlength (hcross j).1).1
    have ht := (crossing_endpoint_distance source target cut theta hlength (hcross j).2).2
    have hd : |target (tau j) - source j| ≤ 2 * theta := by
      calc
        _ ≤ |target (tau j) - cut| + |cut - source j| := abs_sub_le _ _ _
        _ ≤ theta + theta := add_le_add ht (by simpa only [abs_sub_comm] using hs)
        _ = 2 * theta := by ring
    apply (hcost j (tau j)).trans
    apply mul_le_mul_of_nonneg_left _ hC
    nlinarith [sq_abs (target (tau j) - source j),
      abs_nonneg (target (tau j) - source j)]

/-- Actual two-cut competitor. Every selected old edge meets the interval between the
cuts. The interior bijection is supplied by the finite environmental cell matching;
both exterior bijections and their cubic cost bounds are constructed here. -/
theorem exists_two_cut_competitor {J : Type*} [Fintype J]
    (source target : J → ℝ) (cost : J → J → ℝ) {left right theta C W : ℝ}
    (hlr : left < right) (htheta : 0 ≤ theta) (hC : 0 ≤ C)
    (hne : ∀ j, source j ≠ right ∧ target j ≠ right)
    (hselected : ∀ j, (source j < right ∨ target j < right) ∧
      (left < source j ∨ left < target j))
    (hleft : finiteCurrent source target left = 0)
    (hright : finiteCurrent source target right = 0)
    (hcount : ∀ cut ∈ ({left, right} : Set ℝ),
      (Fintype.card {j // Crosses cut (source j) (target j)} : ℝ) ≤ theta)
    (hlength : ∀ cut ∈ ({left, right} : Set ℝ),
      (∑ j : {j // Crosses cut (source j) (target j)}, |target j - source j|) ≤ theta)
    (middle : {j // cutRegion left right (source j) = 1} ≃
      {j // cutRegion left right (target j) = 1})
    (hcomparison : (∑ j : {j // cutRegion left right (source j) = 1},
      cost j (middle j)) ≤ W)
    (hcost : ∀ i j, cost i j ≤ C * (target j - source i) ^ 2) :
    ∃ tau : Equiv.Perm J,
      (∀ j, cutRegion left right (target (tau j)) = cutRegion left right (source j)) ∧
      (∀ j : {j // cutRegion left right (source j) = 1}, tau j = middle j) ∧
      (∑ j, cost j (tau j)) ≤ W + 8 * C * theta ^ 3 := by
  let s := fun j ↦ cutRegion left right (source j)
  let t := fun j ↦ cutRegion left right (target j)
  let e : ∀ k : Fin 3, {j // s j = k} ≃ {j // t j = k} := fun k ↦
    if hk : k = 1 then by subst k; exact middle
    else Fintype.equivOfCardEq (card_cutRegion_eq source target hlr hleft hright k)
  let tau := glueRegions s t e
  have hpres (j : J) : t (tau j) = s j := glueRegions_region s t e j
  have hmid (j : {j // s j = 1}) : tau j = middle j := by
    simpa only [e, dite_eq_left] using glueRegions_apply s t e 1 j
  have hleftSource (j : J) (hj : source j < left) :
      Crosses left (source j) (target j) := by
    apply Or.inl
    refine ⟨hj, ?_⟩
    rcases (hselected j).2 with h | h
    · linarith
    · exact h
  have hleftTarget (j : J) (hj : target j < left) :
      Crosses left (source j) (target j) := by
    apply Or.inr
    refine ⟨hj, ?_⟩
    rcases (hselected j).2 with h | h
    · exact h
    · linarith
  have hrightSource (j : J) (hj : ¬source j < right) :
      Crosses right (source j) (target j) := by
    apply Or.inr
    have hr : right < source j := lt_of_le_of_ne (not_lt.mp hj) (hne j).1.symm
    refine ⟨?_, hr⟩
    rcases (hselected j).1 with h | h
    · exact (hj h).elim
    · exact h
  have hrightTarget (j : J) (hj : ¬target j < right) :
      Crosses right (source j) (target j) := by
    apply Or.inl
    have hr : right < target j := lt_of_le_of_ne (not_lt.mp hj) (hne j).2.symm
    refine ⟨?_, hr⟩
    rcases (hselected j).1 with h | h
    · exact h
    · exact (hj h).elim
  have hcost0 : (∑ j : {j // s j = 0}, cost j (tau j)) ≤ 4 * C * theta ^ 3 := by
    apply repair_fiber_cost_le source target cost tau (fun j ↦ s j = 0) hC htheta
      (hcount left (by simp)) (hlength left (by simp)) _ hcost
    intro j
    have hj : source j < left := cutRegion_eq_zero.mp j.property
    have ht : target (tau j) < left := cutRegion_eq_zero.mp ((hpres j).trans j.property)
    exact ⟨hleftSource j hj, hleftTarget (tau j) ht⟩
  have hcost2 : (∑ j : {j // s j = 2}, cost j (tau j)) ≤ 4 * C * theta ^ 3 := by
    apply repair_fiber_cost_le source target cost tau (fun j ↦ s j = 2) hC htheta
      (hcount right (by simp)) (hlength right (by simp)) _ hcost
    intro j
    have hj : ¬source j < right := (cutRegion_eq_two hlr).mp j.property
    have ht : ¬target (tau j) < right :=
      (cutRegion_eq_two hlr).mp ((hpres j).trans j.property)
    exact ⟨hrightSource j hj, hrightTarget (tau j) ht⟩
  have hcost1 : (∑ j : {j // s j = 1}, cost j (tau j)) ≤ W := by
    simpa only [hmid] using hcomparison
  refine ⟨tau, hpres, hmid, ?_⟩
  rw [← Fintype.sum_fiberwise s (fun j ↦ cost j (tau j)), Fin.sum_univ_three]
  linarith

/-- The actual finite sum `T + S`, with the half-open edge convention. -/
noncomputable def finiteCrossingEnergy {J : Type*} [Fintype J]
    (source target : J → ℝ) (x : ℝ) : ℝ :=
  ∑ j, |(crossingSign (source j) (target j) x : ℝ)| * (1 + |target j - source j|)

theorem abs_crossingSign_non_event {s t x : ℝ} (hs : s ≠ x) (ht : t ≠ x) :
    |(crossingSign s t x : ℝ)| = if Crosses x s t then 1 else 0 := by
  by_cases hsl : s < x <;> by_cases htl : t < x
  · simp [crossingSign, Crosses, le_iff_lt_or_eq, hs, ht, hsl, htl,
      not_lt_of_ge hsl.le, not_lt_of_ge htl.le]
  · have htr : x < t := lt_of_le_of_ne (not_lt.mp htl) ht.symm
    simp [crossingSign, Crosses, le_iff_lt_or_eq, hs, ht, hsl, htl, htr]
  · have hsr : x < s := lt_of_le_of_ne (not_lt.mp hsl) hs.symm
    simp [crossingSign, Crosses, le_iff_lt_or_eq, hs, ht, hsl, htl, hsr]
  · simp [crossingSign, Crosses, le_iff_lt_or_eq, hs, ht, hsl, htl]

/-- At a non-event cut the literal crossing count and total length are bounded by `T+S`. -/
theorem crossing_count_length_le_energy {J : Type*} [Fintype J]
    (source target : J → ℝ) (cut : ℝ)
    (hne : ∀ j, source j ≠ cut ∧ target j ≠ cut) :
    (Fintype.card {j // Crosses cut (source j) (target j)} : ℝ) ≤
        finiteCrossingEnergy source target cut ∧
      (∑ j : {j // Crosses cut (source j) (target j)}, |target j - source j|) ≤
        finiteCrossingEnergy source target cut := by
  have heq : finiteCrossingEnergy source target cut =
      (Fintype.card {j // Crosses cut (source j) (target j)} : ℝ) +
        ∑ j : {j // Crosses cut (source j) (target j)}, |target j - source j| := by
    unfold finiteCrossingEnergy
    simp_rw [abs_crossingSign_non_event (hne _).1 (hne _).2, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.sum_subtype _
      (p := fun j ↦ Crosses cut (source j) (target j)) (F := inferInstance) (by simp)]
    simp [Finset.sum_add_distrib]
  rw [heq]
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  · exact le_add_of_nonneg_left (Nat.cast_nonneg _)

theorem finiteCrossingEnergy_nonneg {J : Type*} [Fintype J]
    (source target : J → ℝ) (x : ℝ) : 0 ≤ finiteCrossingEnergy source target x :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (by positivity)

theorem integrable_finiteCrossingEnergy {J : Type*} [Fintype J]
    (source target : J → ℝ) : Integrable (finiteCrossingEnergy source target) := by
  apply integrable_finsetSum
  intro j _
  exact (PointProcess.FiniteMatching.integrable_abs_crossingSign
    (source j) (target j)).mul_const _

theorem integral_finiteCrossingEnergy {J : Type*} [Fintype J]
    (source target : J → ℝ) :
    (∫ x, finiteCrossingEnergy source target x) =
      ∑ j, (|target j - source j| + (target j - source j) ^ 2) := by
  unfold finiteCrossingEnergy
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const, PointProcess.FiniteMatching.integral_abs_crossingSign]
    nlinarith [sq_abs (target j - source j)]
  · intro j _
    exact (PointProcess.FiniteMatching.integrable_abs_crossingSign
      (source j) (target j)).mul_const _

/-- Integrating the actual crossings over any spatial set is bounded by count and
squared length. Young's elementary inequality removes the square-root estimate. -/
theorem setIntegral_finiteCrossingEnergy_le {J : Type*} [Fintype J]
    (source target : J → ℝ) (I : Set ℝ) :
    (∫ x in I, finiteCrossingEnergy source target x) ≤
      (Fintype.card J : ℝ) / 2 + (3 / 2) * ∑ j, (target j - source j) ^ 2 := by
  calc
    _ ≤ ∫ x, finiteCrossingEnergy source target x :=
      setIntegral_le_integral (integrable_finiteCrossingEnergy source target)
        (ae_of_all _ (finiteCrossingEnergy_nonneg source target))
    _ = ∑ j, (|target j - source j| + (target j - source j) ^ 2) :=
      integral_finiteCrossingEnergy source target
    _ ≤ ∑ j, ((1 : ℝ) / 2 + (3 / 2) * (target j - source j) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (|target j - source j| - 1), sq_abs (target j - source j)]
    _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]; ring

/-- The number of selected rows is controlled by interior source events and the two
crossing counts, even if some selected sources lie outside the cut interval. -/
theorem selected_card_le {J : Type*} [Fintype J]
    (source target : J → ℝ) {left right theta N : ℝ} (hlr : left < right)
    (hne : ∀ j, source j ≠ right)
    (hselected : ∀ j, (source j < right ∨ target j < right) ∧
      (left < source j ∨ left < target j))
    (hcount : ∀ cut ∈ ({left, right} : Set ℝ),
      (Fintype.card {j // Crosses cut (source j) (target j)} : ℝ) ≤ theta)
    (hinterior : (Fintype.card {j // cutRegion left right (source j) = 1} : ℝ) ≤ N) :
    (Fintype.card J : ℝ) ≤ N + 2 * theta := by
  have h0 : (Fintype.card {j // cutRegion left right (source j) = 0} : ℝ) ≤ theta := by
    apply le_trans _ (hcount left (by simp))
    exact_mod_cast Fintype.card_subtype_mono
      (fun j ↦ cutRegion left right (source j) = 0)
      (fun j ↦ Crosses left (source j) (target j)) (fun j hj ↦ by
        have hs := cutRegion_eq_zero.mp hj
        refine Or.inl ⟨hs, ?_⟩
        rcases (hselected j).2 with h | h
        · linarith
        · exact h)
  have h2 : (Fintype.card {j // cutRegion left right (source j) = 2} : ℝ) ≤ theta := by
    apply le_trans _ (hcount right (by simp))
    exact_mod_cast Fintype.card_subtype_mono
      (fun j ↦ cutRegion left right (source j) = 2)
      (fun j ↦ Crosses right (source j) (target j)) (fun j hj ↦ by
        have hs : right < source j :=
          lt_of_le_of_ne (not_lt.mp ((cutRegion_eq_two hlr).mp hj)) (hne j).symm
        refine Or.inr ⟨?_, hs⟩
        rcases (hselected j).1 with h | h
        · linarith
        · exact h)
  have hcard := Fintype.sum_fiberwise (fun j ↦ cutRegion left right (source j))
    (fun _j : J ↦ (1 : ℝ))
  simp only [Fin.sum_univ_three, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hcard
  linarith

/-- Two good cuts give the actual local-energy estimate through a constructed finite
competitor and local minimality. All repair terms are proved by the preceding surgery. -/
theorem two_cut_local_energy_le {J : Type*} [Fintype J]
    (source target : J → ℝ) (cost : J → J → ℝ) (I : Set ℝ)
    {left right theta C W lower N : ℝ}
    (hlr : left < right) (htheta : 0 ≤ theta) (hC : 0 ≤ C) (hlower : 0 < lower)
    (hne : ∀ j, source j ≠ right ∧ target j ≠ right)
    (hselected : ∀ j, (source j < right ∨ target j < right) ∧
      (left < source j ∨ left < target j))
    (hleft : finiteCurrent source target left = 0)
    (hright : finiteCurrent source target right = 0)
    (hcount : ∀ cut ∈ ({left, right} : Set ℝ),
      (Fintype.card {j // Crosses cut (source j) (target j)} : ℝ) ≤ theta)
    (hlength : ∀ cut ∈ ({left, right} : Set ℝ),
      (∑ j : {j // Crosses cut (source j) (target j)}, |target j - source j|) ≤ theta)
    (middle : {j // cutRegion left right (source j) = 1} ≃
      {j // cutRegion left right (target j) = 1})
    (hcomparison : (∑ j : {j // cutRegion left right (source j) = 1},
      cost j (middle j)) ≤ W)
    (hcost : ∀ i j, cost i j ≤ C * (target j - source i) ^ 2)
    (hcoercive : ∀ j, lower * (target j - source j) ^ 2 ≤ cost j j)
    (hminimal : ∀ tau : Equiv.Perm J, (∑ j, cost j j) ≤ ∑ j, cost j (tau j))
    (hinterior : (Fintype.card {j // cutRegion left right (source j) = 1} : ℝ) ≤ N) :
    (∫ x in I, finiteCrossingEnergy source target x) ≤
      N / 2 + theta + (3 / 2) * ((W + 8 * C * theta ^ 3) / lower) := by
  obtain ⟨tau, _, _, hrepair⟩ := exists_two_cut_competitor source target cost hlr htheta hC
    hne hselected hleft hright hcount hlength middle hcomparison hcost
  have henergy : (∑ j, (target j - source j) ^ 2) ≤ (W + 8 * C * theta ^ 3) / lower := by
    apply (le_div_iff₀ hlower).mpr
    calc
      _ = ∑ j, lower * (target j - source j) ^ 2 := by
        rw [mul_comm, Finset.mul_sum]
      _ ≤ ∑ j, cost j j := Finset.sum_le_sum fun j _ ↦ hcoercive j
      _ ≤ ∑ j, cost j (tau j) := hminimal tau
      _ ≤ _ := hrepair
  have hcard := selected_card_le source target hlr (fun j ↦ (hne j).1)
    hselected hcount hinterior
  have hbound := setIntegral_finiteCrossingEnergy_le source target I
  linarith

/-- An explicit small cubic coefficient and a large level absorb the two-cut estimate.
Here `theta³ = eta³ * r * L`; this is the deterministic normalization used by the iteration. -/
theorem bootstrap_absorption {A B eta r L theta H : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hlevel : 2 * A ≤ r) (hsmall : B * eta ^ 3 ≤ 1 / 2)
    (hscale : theta ^ 3 = eta ^ 3 * r * L)
    (henergy : H ≤ A * L + B * theta ^ 3) : H ≤ r * L := by
  rw [hscale] at henergy
  have h1 := mul_le_mul_of_nonneg_right hlevel hL
  have h2 := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hr hL)
  nlinarith

/-- A search region containing no low-energy cut forces energy in the enlarged window.
The zero-current occupation estimate supplies `volume.real Z`; this is an integral
consequence, with no probabilistic or matching-moment assumption. -/
theorem no_good_cut_energy_lower {f : ℝ → ℝ} {Z I : Set ℝ} {theta : ℝ}
    (hZ : MeasurableSet Z) (hZfinite : volume Z ≠ ⊤) (hZI : Z ⊆ I)
    (hf : IntegrableOn f I) (hzero : ∀ x, 0 ≤ f x)
    (hbad : ∀ x ∈ Z, theta < f x) :
    theta * volume.real Z ≤ ∫ x in I, f x := by
  calc
    _ = ∫ x in Z, theta := by rw [setIntegral_const]; simp [mul_comm]
    _ ≤ ∫ x in Z, f x := setIntegral_mono_on (integrableOn_const hZfinite)
      (hf.mono_set hZI) hZ (fun x hx ↦ (hbad x hx).le)
    _ ≤ ∫ x in I, f x := setIntegral_mono_set hf (ae_of_all _ hzero) (ae_of_all _ hZI)

/-- Quantitative final step of the bootstrap: positive zero occupation in either search
interval gives a strict energy bound on the length-`4L` enlarged interval. -/
theorem no_good_cut_energy_gt {f : ℝ → ℝ} {Z I : Set ℝ} {theta c L : ℝ}
    (hZ : MeasurableSet Z) (hZfinite : volume Z ≠ ⊤) (hZI : Z ⊆ I)
    (hf : IntegrableOn f I) (hzero : ∀ x, 0 ≤ f x)
    (hbad : ∀ x ∈ Z, theta < f x)
    (htheta : 0 < theta) (hc : 0 < c) (hL : 0 < L)
    (hoccupation : c * L ≤ volume.real Z) :
    (c / 8) * theta * (4 * L) < ∫ x in I, f x := by
  have hbound := no_good_cut_energy_lower hZ hZfinite hZI hf hzero hbad
  have hmul := mul_le_mul_of_nonneg_left hoccupation htheta.le
  have hpos : 0 < c * theta * L := mul_pos (mul_pos hc htheta) hL
  nlinarith

/-- The small cubic coefficient required in the iteration is always available. -/
theorem exists_bootstrap_coefficient (B : ℝ) (hB : 0 ≤ B) :
    ∃ eta : ℝ, 0 < eta ∧ B * eta ^ 3 ≤ 1 / 2 := by
  let eta := 1 / (2 * (B + 1))
  have hden : 0 < 2 * (B + 1) := by positivity
  have he0 : 0 < eta := by dsimp [eta]; positivity
  have he1 : eta ≤ 1 := by
    dsimp [eta]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hesq : eta ^ 2 ≤ 1 := by nlinarith
  have hecube : eta ^ 3 ≤ eta := by
    have := mul_le_mul_of_nonneg_left hesq he0.le
    nlinarith
  refine ⟨eta, he0, (mul_le_mul_of_nonneg_left hecube hB).trans ?_⟩
  change B * (1 / (2 * (B + 1))) ≤ 1 / 2
  rw [mul_one_div]
  apply (div_le_iff₀ hden).mpr
  linarith

namespace SpatialMatching

variable {S T : Type*}

/-- The oriented crossing current of the concrete matching. -/
noncomputable def current (M : SpatialMatching S T) (x : ℝ) : ℤ :=
  ∑' i, crossingSign (M.source i) (M.target (M.assignment i)) x

/-- Local minimality tests actual finite target permutations, extended by `rematch`. -/
def IsLocallyMinimizing (M : SpatialMatching S T) (cost : S → T → ℝ) : Prop :=
  ∀ (rows : Finset S) (tau : Equiv.Perm rows),
    (∑ i : rows, cost i (M.assignment i)) ≤
      ∑ i : rows, cost i (M.assignment (tau i))

/-- Restricting to a finite family containing every crossing preserves the actual
oriented current. Non-event cuts reconcile strict crossing with half-open currents. -/
theorem finiteCurrent_selected_eq (M : SpatialMatching S T) (rows : Finset S) (cut : ℝ)
    (hne : ∀ i, M.source i ≠ cut ∧ M.target (M.assignment i) ≠ cut)
    (hcontains : ∀ i, Crosses cut (M.source i) (M.target (M.assignment i)) → i ∈ rows) :
    finiteCurrent (fun i : rows ↦ M.source i)
      (fun i : rows ↦ M.target (M.assignment i)) cut = M.current cut := by
  have hsign (i : S) : crossingSign (M.source i) (M.target (M.assignment i)) cut =
      (if M.source i < cut then (1 : ℤ) else 0) -
        (if M.target (M.assignment i) < cut then 1 else 0) := by
    simp only [crossingSign, le_iff_lt_or_eq, (hne i).1, (hne i).2, or_false]
  unfold current
  rw [tsum_eq_sum (s := rows)]
  · rw [Finset.sum_subtype rows (p := fun i ↦ i ∈ rows) (F := inferInstance) (by simp)]
    unfold finiteCurrent
    simp_rw [hsign]
  · intro i hi
    by_cases hs : M.source i < cut <;> by_cases ht : M.target (M.assignment i) < cut
    · simp [hsign, hs, ht]
    · exact (hi (hcontains i (Or.inl ⟨hs,
        lt_of_le_of_ne (not_lt.mp ht) (hne i).2.symm⟩))).elim
    · exact (hi (hcontains i (Or.inr ⟨ht,
        lt_of_le_of_ne (not_lt.mp hs) (hne i).1.symm⟩))).elim
    · simp [hsign, hs, ht]

/-- Both boundary crossing families belong to the selected finite modification. -/
theorem boundary_crossing_mem_edgesMeeting (M : SpatialMatching S T)
    {left right cut : ℝ} (hlr : left < right) (hcut : cut ∈ ({left, right} : Set ℝ))
    {i : S} (hi : Crosses cut (M.source i) (M.target (M.assignment i))) :
    i ∈ M.edgesMeeting left right := by
  rcases hcut with rfl | hcut
  · rcases hi with hi | hi
    · exact ⟨Or.inl (hi.1.trans hlr), Or.inr hi.2⟩
    · exact ⟨Or.inr (hi.1.trans hlr), Or.inl hi.2⟩
  · have heq : cut = right := hcut
    subst cut
    rcases hi with hi | hi
    · exact ⟨Or.inl hi.1, Or.inr (hlr.trans hi.2)⟩
    · exact ⟨Or.inr hi.1, Or.inl (hlr.trans hi.2)⟩

/-- The actual unsigned crossing count plus crossing length sum of a spatial matching. -/
noncomputable def crossingEnergy (M : SpatialMatching S T) (x : ℝ) : ℝ :=
  ∑' i, |(crossingSign (M.source i) (M.target (M.assignment i)) x : ℝ)| *
    (1 + |M.target (M.assignment i) - M.source i|)

theorem crossingEnergy_nonneg (M : SpatialMatching S T) (x : ℝ) :
    0 ≤ M.crossingEnergy x :=
  tsum_nonneg fun _ ↦ mul_nonneg (abs_nonneg _) (by positivity)

/-- The global crossing energy at a non-event cut is exactly its selected finite sum. -/
theorem crossingEnergy_selected_eq (M : SpatialMatching S T) (rows : Finset S) (cut : ℝ)
    (hne : ∀ i, M.source i ≠ cut ∧ M.target (M.assignment i) ≠ cut)
    (hcontains : ∀ i, Crosses cut (M.source i) (M.target (M.assignment i)) → i ∈ rows) :
    M.crossingEnergy cut = finiteCrossingEnergy
      (fun i : rows ↦ M.source i) (fun i : rows ↦ M.target (M.assignment i)) cut := by
  unfold crossingEnergy finiteCrossingEnergy
  rw [tsum_eq_sum (s := rows)]
  · exact Finset.sum_subtype rows (by simp) _
  · intro i hi
    rw [abs_crossingSign_non_event (hne i).1 (hne i).2]
    have hnot : ¬Crosses cut (M.source i) (M.target (M.assignment i)) :=
      fun hc ↦ hi (hcontains i hc)
    simp [hnot]

/-- The infinite crossing sum on the open cut interval is literally the finite selected
sum. This justifies use of the finite energy bound for an infinite matching. -/
theorem crossingEnergy_eq_selected (M : SpatialMatching S T) {left right : ℝ}
    (rows : Finset S) (hrows : (rows : Set S) = M.edgesMeeting left right)
    {x : ℝ} (hx : x ∈ Ioo left right) :
    M.crossingEnergy x = finiteCrossingEnergy
      (fun i : rows ↦ M.source i) (fun i : rows ↦ M.target (M.assignment i)) x := by
  unfold crossingEnergy finiteCrossingEnergy
  rw [tsum_eq_sum (s := rows)]
  · exact Finset.sum_subtype rows (by simp) _
  · intro i hi
    have hnot : i ∉ M.edgesMeeting left right := by rw [← hrows]; exact hi
    have hz : crossingSign (M.source i) (M.target (M.assignment i)) x = 0 := by
      by_cases hs : M.source i ≤ x <;> by_cases ht : M.target (M.assignment i) ≤ x
      · simp [crossingSign, hs, ht]
      · exfalso
        apply hnot
        exact ⟨Or.inl (hs.trans_lt hx.2), Or.inr (hx.1.trans (lt_of_not_ge ht))⟩
      · exfalso
        apply hnot
        exact ⟨Or.inr (ht.trans_lt hx.2), Or.inl (hx.1.trans (lt_of_not_ge hs))⟩
      · simp [crossingSign, hs, ht]
    simp [hz]

/-- Local crossing energy of an infinite matching is bounded by the finite selected
count and squared lengths once its boundary crossing families are finite. -/
theorem setIntegral_crossingEnergy_le_selected (M : SpatialMatching S T)
    {left right : ℝ} (rows : Finset S)
    (hrows : (rows : Set S) = M.edgesMeeting left right) {I : Set ℝ}
    (hI : I ⊆ Ioo left right) (hImeas : MeasurableSet I) :
    (∫ x in I, M.crossingEnergy x) ≤
      (rows.card : ℝ) / 2 + (3 / 2) *
        ∑ i : rows, (M.target (M.assignment i) - M.source i) ^ 2 := by
  have heq : (∫ x in I, M.crossingEnergy x) = ∫ x in I, finiteCrossingEnergy
      (fun i : rows ↦ M.source i) (fun i : rows ↦ M.target (M.assignment i)) x := by
    apply setIntegral_congr_fun hImeas
    intro x hx
    exact M.crossingEnergy_eq_selected rows hrows (hI hx)
  rw [heq]
  simpa using setIntegral_finiteCrossingEnergy_le
    (fun i : rows ↦ M.source i) (fun i : rows ↦ M.target (M.assignment i)) I

/-- Local integrability follows already from local endpoint finiteness and finite
boundary crossing families. It requires no moment estimate or energy-tail hypothesis. -/
theorem integrableOn_crossingEnergy (M : SpatialMatching S T) (hloc : M.LocallyFinite)
    {left right : ℝ}
    (hleft : {i | Crosses left (M.source i) (M.target (M.assignment i))}.Finite)
    (hright : {i | Crosses right (M.source i) (M.target (M.assignment i))}.Finite)
    {I : Set ℝ} (hI : I ⊆ Ioo left right) (hImeas : MeasurableSet I) :
    IntegrableOn M.crossingEnergy I := by
  let hfinite := M.finite_edgesMeeting hloc left right hleft hright
  let rows := hfinite.toFinset
  have hrows : (rows : Set S) = M.edgesMeeting left right := hfinite.coe_toFinset
  apply (integrable_finiteCrossingEnergy
    (fun i : rows ↦ M.source i) (fun i : rows ↦ M.target (M.assignment i))).integrableOn.congr_fun
  · intro x hx
    exact (M.crossingEnergy_eq_selected rows hrows (hI hx)).symm
  · exact hImeas

/-- Finite environmental data between two cuts: the actual affected old rows and an
interior source-to-target bijection. The only cost bound concerns that environmental
comparison matching; no exterior repair or local-energy estimate is stored. -/
structure WindowComparison (M : SpatialMatching S T) (cost : S → T → ℝ)
    (left right N W : ℝ) where
  rows : Finset S
  rows_eq : (rows : Set S) = M.edgesMeeting left right
  middle : {i : rows // cutRegion left right (M.source i) = 1} ≃
    {i : rows // cutRegion left right (M.target (M.assignment i)) = 1}
  comparison_cost : (∑ i : {i : rows // cutRegion left right (M.source i) = 1},
    cost i.val (M.assignment (middle i).val)) ≤ W
  interior_count : (Fintype.card {i : rows // cutRegion left right (M.source i) = 1} : ℝ) ≤ N

/-- The two-cut bound for an actual infinite matching. Vanishing current is restricted
to the selected rows, low crossing energy supplies both cut budgets, and local minimality
is applied to the genuinely constructed finite rematching. -/
theorem WindowComparison.local_energy_le {M : SpatialMatching S T} {cost : S → T → ℝ}
    {left right N W theta C lower : ℝ} (comparison : M.WindowComparison cost left right N W)
    (hlr : left < right) (htheta : 0 ≤ theta) (hC : 0 ≤ C) (hlower : 0 < lower)
    (hnoevent : ∀ cut ∈ ({left, right} : Set ℝ),
      ∀ i, M.source i ≠ cut ∧ M.target (M.assignment i) ≠ cut)
    (hcurrent : ∀ cut ∈ ({left, right} : Set ℝ), M.current cut = 0)
    (hgood : ∀ cut ∈ ({left, right} : Set ℝ), M.crossingEnergy cut ≤ theta)
    (hupper : ∀ i j, cost i j ≤ C * (M.target j - M.source i) ^ 2)
    (hlowerCost : ∀ i, lower * (M.target (M.assignment i) - M.source i) ^ 2 ≤
      cost i (M.assignment i))
    (hminimal : M.IsLocallyMinimizing cost) {I : Set ℝ}
    (hI : I ⊆ Ioo left right) (hImeas : MeasurableSet I) :
    (∫ x in I, M.crossingEnergy x) ≤
      N / 2 + theta + (3 / 2) * ((W + 8 * C * theta ^ 3) / lower) := by
  let source := fun i : comparison.rows ↦ M.source i
  let target := fun i : comparison.rows ↦ M.target (M.assignment i)
  have hcontains (cut : ℝ) (hc : cut ∈ ({left, right} : Set ℝ)) (i : S)
      (hi : Crosses cut (M.source i) (M.target (M.assignment i))) : i ∈ comparison.rows := by
    have hmem := M.boundary_crossing_mem_edgesMeeting hlr hc hi
    rw [← comparison.rows_eq] at hmem
    exact hmem
  have hcur (cut : ℝ) (hc : cut ∈ ({left, right} : Set ℝ)) :
      finiteCurrent source target cut = 0 :=
    (M.finiteCurrent_selected_eq comparison.rows cut (hnoevent cut hc)
      (hcontains cut hc)).trans (hcurrent cut hc)
  have hbudget (cut : ℝ) (hc : cut ∈ ({left, right} : Set ℝ)) :
      (Fintype.card {j // Crosses cut (source j) (target j)} : ℝ) ≤ theta ∧
        (∑ j : {j // Crosses cut (source j) (target j)}, |target j - source j|) ≤ theta := by
    have hb := crossing_count_length_le_energy source target cut
      (fun j ↦ hnoevent cut hc j)
    have heq := M.crossingEnergy_selected_eq comparison.rows cut (hnoevent cut hc)
      (hcontains cut hc)
    change M.crossingEnergy cut = finiteCrossingEnergy source target cut at heq
    rw [← heq] at hb
    exact ⟨hb.1.trans (hgood cut hc), hb.2.trans (hgood cut hc)⟩
  have hsel (j : comparison.rows) : (source j < right ∨ target j < right) ∧
      (left < source j ∨ left < target j) := by
    have hj : (j : S) ∈ (comparison.rows : Set S) := j.property
    rw [comparison.rows_eq] at hj
    exact hj
  have hfinite := two_cut_local_energy_le source target
    (fun i j ↦ cost i (M.assignment j)) I hlr htheta hC hlower
    (fun j ↦ hnoevent right (by simp) j) hsel (hcur left (by simp)) (hcur right (by simp))
    (fun cut hc ↦ (hbudget cut hc).1) (fun cut hc ↦ (hbudget cut hc).2)
    comparison.middle comparison.comparison_cost (fun i j ↦ hupper i (M.assignment j))
    (fun j ↦ hlowerCost j) (hminimal comparison.rows) comparison.interior_count
  have heq : (∫ x in I, M.crossingEnergy x) = ∫ x in I,
      finiteCrossingEnergy source target x := by
    apply setIntegral_congr_fun hImeas
    intro x hx
    exact M.crossingEnergy_eq_selected comparison.rows comparison.rows_eq (hI hx)
  rwa [← heq] at hfinite

/-- Deterministic one-step bootstrap. Environmental regularity supplies actual finite
interior comparison matchings for pairs of zero cuts. The proof constructs the exterior
repairs, applies local minimality, and then uses zero-set occupation in a search interval.
No local-energy estimate or repair inequality is an input. -/
theorem one_step_bootstrap (M : SpatialMatching S T) (cost : S → T → ℝ)
    {I enlarged Zminus Zplus : Set ℝ} {L r theta C0 c0 C lower : ℝ}
    (hL : 0 < L) (htheta : 0 < theta) (hthetaL : theta ≤ L)
    (hc0 : 0 < c0) (hC : 0 ≤ C) (hlower : 0 < lower)
    (hImeas : MeasurableSet I)
    (hZmeas : MeasurableSet Zminus ∧ MeasurableSet Zplus)
    (hZfinite : volume Zminus ≠ ⊤ ∧ volume Zplus ≠ ⊤)
    (hZsub : Zminus ⊆ enlarged ∧ Zplus ⊆ enlarged)
    (hoccupation : c0 * L ≤ volume.real Zminus ∧ c0 * L ≤ volume.real Zplus)
    (hintegrable : IntegrableOn M.crossingEnergy enlarged)
    (hgeometry : ∀ left ∈ Zminus, ∀ right ∈ Zplus,
      left < right ∧ I ⊆ Ioo left right)
    (hnoevent : ∀ cut ∈ Zminus ∪ Zplus,
      ∀ i, M.source i ≠ cut ∧ M.target (M.assignment i) ≠ cut)
    (hcurrent : ∀ cut ∈ Zminus ∪ Zplus, M.current cut = 0)
    (hcomparison : ∀ left ∈ Zminus, ∀ right ∈ Zplus,
      Nonempty (M.WindowComparison cost left right (C0 * L) (C0 * L)))
    (hupper : ∀ i j, cost i j ≤ C * (M.target j - M.source i) ^ 2)
    (hlowerCost : ∀ i, lower * (M.target (M.assignment i) - M.source i) ^ 2 ≤
      cost i (M.assignment i))
    (hminimal : M.IsLocallyMinimizing cost)
    (hlevel : 2 * (C0 / 2 + 1 + (3 / 2) * C0 / lower) ≤ r)
    (hcubic : (12 * C / lower) * theta ^ 3 ≤ r * L / 2)
    (hlarge : r * L < ∫ x in I, M.crossingEnergy x) :
    (c0 / 8) * theta * (4 * L) < ∫ x in enlarged, M.crossingEnergy x := by
  by_contra hnot
  have hout : (∫ x in enlarged, M.crossingEnergy x) ≤ (c0 / 8) * theta * (4 * L) :=
    not_lt.mp hnot
  have hexists (Z : Set ℝ) (hZ : MeasurableSet Z) (hfinite : volume Z ≠ ⊤)
      (hsub : Z ⊆ enlarged) (hocc : c0 * L ≤ volume.real Z) :
      ∃ x ∈ Z, M.crossingEnergy x ≤ theta := by
    by_contra hnone
    push Not at hnone
    have hbad := no_good_cut_energy_gt hZ hfinite hsub hintegrable
      M.crossingEnergy_nonneg hnone htheta hc0 hL hocc
    exact (not_lt_of_ge hout) hbad
  obtain ⟨left, hl, hgl⟩ := hexists Zminus hZmeas.1 hZfinite.1 hZsub.1 hoccupation.1
  obtain ⟨right, hrZ, hgr⟩ := hexists Zplus hZmeas.2 hZfinite.2 hZsub.2 hoccupation.2
  obtain ⟨comparison⟩ := hcomparison left hl right hrZ
  have hcutsub : ({left, right} : Set ℝ) ⊆ Zminus ∪ Zplus := by
    intro x hx
    rcases hx with rfl | hx
    · exact Or.inl hl
    · have heq : x = right := hx
      subst x
      exact Or.inr hrZ
  have hgood : ∀ cut ∈ ({left, right} : Set ℝ), M.crossingEnergy cut ≤ theta := by
    intro cut hc
    rcases hc with rfl | hc
    · exact hgl
    · have heq : cut = right := hc
      subst cut
      exact hgr
  have hbound := comparison.local_energy_le (hgeometry left hl right hrZ).1
    htheta.le hC hlower (fun cut hc ↦ hnoevent cut (hcutsub hc))
    (fun cut hc ↦ hcurrent cut (hcutsub hc)) hgood hupper hlowerCost hminimal
    (hgeometry left hl right hrZ).2 hImeas
  have halgebra : C0 * L / 2 + theta + (3 / 2) * ((C0 * L + 8 * C * theta ^ 3) / lower) =
      (C0 / 2 + 1 + (3 / 2) * C0 / lower) * L +
        (12 * C / lower) * theta ^ 3 + (theta - L) := by ring
  rw [halgebra] at hbound
  have henergy : (∫ x in I, M.crossingEnergy x) ≤
      (C0 / 2 + 1 + (3 / 2) * C0 / lower) * L + (12 * C / lower) * theta ^ 3 := by
    linarith
  have hlinear := mul_le_mul_of_nonneg_right hlevel hL.le
  exact (not_le_of_gt hlarge) (by linarith)

end SpatialMatching

end OTSelector.Matching
