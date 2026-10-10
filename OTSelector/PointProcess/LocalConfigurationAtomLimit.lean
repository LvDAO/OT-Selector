import OTSelector.PointProcess.LocalConfigurationBorel

/-!
# Atom correspondence under actual vague convergence

An isolated simple limit atom has exactly one nearby atom eventually, and that atom
converges in the full point space.  Thus positions and marks converge together.  The
proof uses the defining compactly supported test integrals and integer multiplicities.
-/

open Function Set Filter Topology
open scoped BigOperators Classical CompactlySupported

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [ProperSpace X] {base : X}

noncomputable local instance atomLimitTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base

omit [ProperSpace X] in
theorem testSummand_nonneg (c : LocalConfiguration base) {f : C_c(X, ℝ)}
    (hf : ∀ x, 0 ≤ f x) (x : X) : 0 ≤ testSummand c f x :=
  mul_nonneg (Nat.cast_nonneg _) (hf x)

omit [ProperSpace X] in
theorem testSummand_le_testIntegral (c : LocalConfiguration base) {f : C_c(X, ℝ)}
    (hf : ∀ x, 0 ≤ f x) (x : X) : testSummand c f x ≤ testIntegral c f :=
  single_le_finsum x (finite_support_testSummand c f) (testSummand_nonneg c hf)

omit [ProperSpace X] in
theorem pair_testSummand_le_testIntegral (c : LocalConfiguration base) {f : C_c(X, ℝ)}
    (hf : ∀ x, 0 ≤ f x) {x y : X} (hxy : x ≠ y) :
    testSummand c f x + testSummand c f y ≤ testIntegral c f := by
  let S := insert x (insert y (finite_support_testSummand c f).toFinset)
  have hS : support (testSummand c f) ⊆ S := by
    intro z hz
    simp only [S, Finset.mem_coe, Finset.mem_insert]
    exact Or.inr (Or.inr ((finite_support_testSummand c f).mem_toFinset.2 hz))
  rw [testIntegral, finsum_eq_sum_of_support_subset _ hS]
  have hs : ({x, y} : Finset X) ⊆ S := by simp [S, Finset.insert_subset_iff]
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun z _ _ ↦ testSummand_nonneg c hf z)
  simpa [hxy] using hh

/-- An isolated atom computes the tent integral exactly, including its multiplicity. -/
theorem testIntegral_distanceTent_of_isolated (c : LocalConfiguration base)
    {x : X} {r : ℝ} (hr : 0 < r)
    (hisolate : ∀ y, dist y x < r → y ≠ x → multiplicity c y = 0) :
    testIntegral c (distanceTent x r) = (multiplicity c x : ℝ) * r := by
  have hsum : testIntegral c (distanceTent x r) =
      testSummand c (distanceTent x r) x := by
    apply finsum_eq_single
    intro y hy
    by_cases ht : distanceTent x r y = 0
    · simp [testSummand, ht]
    · simp [testSummand, hisolate y (support_distanceTent_subset_ball x r ht) hy]
  rw [hsum]
  simp [testSummand, distanceTent_apply, hr.le]

/-- A positive test integral forces a genuine configuration atom inside its tent support. -/
theorem exists_atom_of_testIntegral_distanceTent_pos (c : LocalConfiguration base)
    {x : X} {r : ℝ} (hpos : 0 < testIntegral c (distanceTent x r)) :
    ∃ y, dist y x < r ∧ multiplicity c y ≠ 0 := by
  by_contra! h
  have hz : testIntegral c (distanceTent x r) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro y
    by_cases hy : dist y x < r
    · simp [testSummand, h y hy]
    · have ht : distanceTent x r y = 0 := by
        simp only [distanceTent_apply]
        exact max_eq_left (sub_nonpos.2 (le_of_not_gt hy))
      simp [testSummand, ht]
  linarith

/-- Every neighborhood of a positive limit atom contains an approximating atom eventually. -/
theorem eventually_exists_atom_near_of_tendsto
    {ι : Type*} {l : Filter ι} {c : ι → LocalConfiguration base}
    {limit : LocalConfiguration base} (hc : Tendsto c l (𝓝 limit))
    {x : X} (hx : multiplicity limit x ≠ 0) {e : ℝ} (he : 0 < e) :
    ∀ᶠ k in l, ∃ y, dist y x < e ∧ multiplicity (c k) y ≠ 0 := by
  have hnonneg (y : X) : 0 ≤ distanceTent x e y := le_max_left _ _
  have hlower := testSummand_le_testIntegral limit hnonneg x
  have hnat : (0 : ℝ) < multiplicity limit x := by exact_mod_cast Nat.pos_of_ne_zero hx
  have hpos : 0 < testIntegral limit (distanceTent x e) := by
    have hs : testSummand limit (distanceTent x e) x = (multiplicity limit x : ℝ) * e := by
      simp [testSummand, distanceTent_apply, he.le]
    rw [hs] at hlower
    exact (mul_pos hnat he).trans_le hlower
  have htest := ((continuous_testIntegral (distanceTent x e)).tendsto limit).comp hc
  filter_upwards [htest.eventually (lt_mem_nhds hpos)] with k hk
  exact exists_atom_of_testIntegral_distanceTent_pos (c k) hk

/-- A simple isolated atom excludes both a second nearby site and multiplicity greater than one.
No simplicity assumption is made on the approximating configurations. -/
theorem eventually_unique_atom_near_of_tendsto
    {ι : Type*} {l : Filter ι} {c : ι → LocalConfiguration base}
    {limit : LocalConfiguration base} (hc : Tendsto c l (𝓝 limit))
    {x : X} (hx : multiplicity limit x = 1) :
    ∃ r > 0, ∀ᶠ k in l, ∃ y, dist y x < r ∧ multiplicity (c k) y = 1 ∧
      ∀ z, dist z x < r → multiplicity (c k) z ≠ 0 → z = y := by
  obtain ⟨R, hR, hIso⟩ := exists_isolating_ball limit limit x
  have hI : testIntegral limit (distanceTent x R) = R := by
    rw [testIntegral_distanceTent_of_isolated limit hR (fun y hy hyx ↦ (hIso y hy hyx).1), hx]
    norm_num
  have htest := ((continuous_testIntegral (distanceTent x R)).tendsto limit).comp hc
  rw [hI] at htest
  refine ⟨R / 4, by positivity, ?_⟩
  filter_upwards [htest.eventually (gt_mem_nhds (show R < 3 * R / 2 by linarith)),
    eventually_exists_atom_near_of_tendsto (x := x) hc (by simp [hx])
      (show 0 < R / 4 by positivity)]
    with k hupper ⟨y, hy, hmy⟩
  dsimp only [Function.comp_def] at hupper
  have hnonneg (z : X) : 0 ≤ distanceTent x R z := le_max_left _ _
  have hweight (z : X) (hz : dist z x < R / 4) :
      3 * R / 4 < distanceTent x R z := by
    change _ < max 0 (R - dist z x)
    exact lt_max_of_lt_right (by linarith)
  have hmult : multiplicity (c k) y = 1 := by
    have hs := testSummand_le_testIntegral (c k) hnonneg y
    have hm : 1 ≤ multiplicity (c k) y := Nat.one_le_iff_ne_zero.2 hmy
    by_contra hne
    have hm2 : (2 : ℝ) ≤ multiplicity (c k) y := by exact_mod_cast (by omega : 2 ≤ _)
    have hw := hweight y hy
    unfold testSummand at hs
    nlinarith [mul_le_mul_of_nonneg_right hm2 (hnonneg y)]
  refine ⟨y, hy, hmult, ?_⟩
  intro z hz hmz
  by_contra hzy
  have hpair := pair_testSummand_le_testIntegral (c k) hnonneg (Ne.symm hzy)
  have hmz1 : (1 : ℝ) ≤ multiplicity (c k) z :=
    by exact_mod_cast Nat.one_le_iff_ne_zero.2 hmz
  have hwz := hweight z hz
  have hwy := hweight y hy
  unfold testSummand at hpair
  rw [hmult] at hpair
  simp only [Nat.cast_one, one_mul] at hpair
  nlinarith [mul_le_mul_of_nonneg_right hmz1 (hnonneg z)]

/-- A simple limit atom admits an actual sequence of unique nearby atoms converging to it. -/
theorem exists_atom_tendsto_of_simple
    {ι : Type*} {l : Filter ι} {c : ι → LocalConfiguration base}
    {limit : LocalConfiguration base} (hc : Tendsto c l (𝓝 limit))
    {x : X} (hx : multiplicity limit x = 1) :
    ∃ r > 0, ∃ point : ι → X, Tendsto point l (𝓝 x) ∧
      ∀ᶠ k in l, dist (point k) x < r ∧ multiplicity (c k) (point k) = 1 ∧
        ∀ z, dist z x < r → multiplicity (c k) z ≠ 0 → z = point k := by
  obtain ⟨r, hr, hlocal⟩ := eventually_unique_atom_near_of_tendsto hc hx
  let P (k : ι) (y : X) := dist y x < r ∧ multiplicity (c k) y = 1 ∧
    ∀ z, dist z x < r → multiplicity (c k) z ≠ 0 → z = y
  let point (k : ι) : X := if hk : ∃ y, P k y then Classical.choose hk else x
  have hgood : ∀ᶠ k in l, P k (point k) := by
    filter_upwards [hlocal] with k hk
    dsimp [point]
    rw [dite_eq_left hk]
    exact Classical.choose_spec hk
  refine ⟨r, hr, point, Metric.tendsto_nhds.2 ?_, hgood⟩
  intro e he
  filter_upwards [hgood, eventually_exists_atom_near_of_tendsto (x := x) hc
    (by simp [hx]) (lt_min he hr)] with k hk ⟨y, hy, hmy⟩
  have heq := hk.2.2 y (hy.trans_le (min_le_right _ _)) hmy
  rw [← heq]
  exact hy.trans_le (min_le_left _ _)

/-- Simultaneous correspondence for any finite family of distinct simple limit atoms.
Each approximating atom has multiplicity one, and the chosen finite map is eventually injective. -/
theorem exists_finite_atoms_tendsto
    {ι J : Type*} [Finite J] {l : Filter ι} {c : ι → LocalConfiguration base}
    {limit : LocalConfiguration base} (hc : Tendsto c l (𝓝 limit))
    {points : J → X} (hinj : Injective points)
    (hsimple : ∀ j, multiplicity limit (points j) = 1) :
    ∃ approx : ι → J → X, (∀ j, Tendsto (fun k ↦ approx k j) l (𝓝 (points j))) ∧
      ∀ᶠ k in l, Injective (approx k) ∧ ∀ j, multiplicity (c k) (approx k j) = 1 := by
  choose r hr p hp hlocal using (fun j ↦ exists_atom_tendsto_of_simple hc (hsimple j))
  refine ⟨fun k j ↦ p j k, hp, ?_⟩
  have hm : ∀ᶠ k in l, ∀ j, multiplicity (c k) (p j k) = 1 := by
    apply eventually_all.2
    intro j
    exact (hlocal j).mono fun _ hk ↦ hk.2.1
  have hi : ∀ᶠ k in l, ∀ i j, i ≠ j → p i k ≠ p j k := by
    apply eventually_all.2
    intro i
    apply eventually_all.2
    intro j
    by_cases hij : i = j
    · simp [hij]
    · have hd : 0 < dist (points i) (points j) := dist_pos.2 (hinj.ne hij)
      have ht := (hp i).dist (hp j)
      filter_upwards [ht.eventually (lt_mem_nhds hd)] with k hk _
      exact dist_pos.1 hk
  filter_upwards [hm, hi] with k hk hki
  exact ⟨fun i j hij ↦ by_contra fun hne ↦ hki i j hne hij, hk⟩

/-- A vacant limit site has an eventually vacant neighborhood. -/
theorem eventually_no_atom_near_of_tendsto
    {ι : Type*} {l : Filter ι} {c : ι → LocalConfiguration base}
    {limit : LocalConfiguration base} (hc : Tendsto c l (𝓝 limit))
    {x : X} (hx : multiplicity limit x = 0) :
    ∃ r > 0, ∀ᶠ k in l, ∀ y, dist y x < r → multiplicity (c k) y = 0 := by
  obtain ⟨R, hR, hIso⟩ := exists_isolating_ball limit limit x
  have hI : testIntegral limit (distanceTent x R) = 0 := by
    rw [testIntegral_distanceTent_of_isolated limit hR (fun y hy hyx ↦ (hIso y hy hyx).1), hx]
    simp
  have htest := ((continuous_testIntegral (distanceTent x R)).tendsto limit).comp hc
  rw [hI] at htest
  refine ⟨R / 2, by positivity, ?_⟩
  filter_upwards [htest.eventually (gt_mem_nhds (show 0 < R / 2 by positivity))]
    with k hk
  dsimp only [Function.comp_def] at hk
  intro y hy
  by_contra hm
  have hm1 : (1 : ℝ) ≤ multiplicity (c k) y := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
  have hf0 (z : X) : 0 ≤ distanceTent x R z := le_max_left _ _
  have hs := testSummand_le_testIntegral (c k) hf0 y
  have hw : R / 2 < distanceTent x R y := lt_max_of_lt_right (by linarith)
  unfold testSummand at hs
  nlinarith [mul_le_mul_of_nonneg_right hm1 (hf0 y)]

/-- Vague convergence excludes extra atoms from any compact set vacant in the limit. -/
theorem eventually_no_atoms_on_compact
    {ι : Type*} {l : Filter ι} {c : ι → LocalConfiguration base}
    {limit : LocalConfiguration base} (hc : Tendsto c l (𝓝 limit))
    {K : Set X} (hK : IsCompact K) (hzero : ∀ x ∈ K, multiplicity limit x = 0) :
    ∀ᶠ k in l, ∀ x ∈ K, multiplicity (c k) x = 0 := by
  choose r hr hlocal using (fun x : K ↦
    eventually_no_atom_near_of_tendsto hc (hzero x x.property))
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ Metric.ball x (r x))
    (fun _ ↦ Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  have hev : ∀ᶠ k in l, ∀ x ∈ s, ∀ y, dist y x.val < r x → multiplicity (c k) y = 0 :=
    (eventually_all_finset s).2 (fun x _ ↦ hlocal x)
  filter_upwards [hev] with k hk
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 (hs hy)
  exact hk x hx y hxy

/-- All atoms in a compact continuity window have one-to-one convergent labels.  The index
type is the actual finite support of the limit in that window, not a supplied correspondence. -/
theorem exists_window_atoms_tendsto
    {ι : Type*} {l : Filter ι} {c : ι → LocalConfiguration base}
    {limit : LocalConfiguration base} (hc : Tendsto c l (𝓝 limit))
    {K : Set X} (hK : IsCompact K)
    (hsimple : ∀ x ∈ K, multiplicity limit x ≤ 1)
    (hboundary : ∀ x ∈ frontier K, multiplicity limit x = 0) :
    ∃ approx : ι → ↥(K ∩ support (multiplicity limit)) → X,
      (∀ j, Tendsto (fun k ↦ approx k j) l (𝓝 j.val)) ∧
      ∀ᶠ k in l, Injective (approx k) ∧
        (∀ j, approx k j ∈ K ∧ multiplicity (c k) (approx k j) = 1) ∧
        (∀ y ∈ K, multiplicity (c k) y ≠ 0 ↔ ∃ j, approx k j = y) := by
  let J := K ∩ support (multiplicity limit)
  have hJ : J.Finite :=
    (locallyFiniteSupport_multiplicity limit).finite_inter_support_of_isCompact hK
  let : Finite J := hJ.to_subtype
  have hj1 (j : J) : multiplicity limit j.val = 1 := by
    have hn := j.property.2
    have hu := hsimple j j.property.1
    change multiplicity limit j.val ≠ 0 at hn
    omega
  obtain ⟨p, hp, hevp⟩ := exists_finite_atoms_tendsto hc
    (Subtype.val_injective : Injective (Subtype.val : J → X)) hj1
  choose r hr hnear using (fun j : J ↦ eventually_unique_atom_near_of_tendsto hc (hj1 j))
  let U : Set X := ⋃ j : J, Metric.ball j.val (r j)
  have hU : IsOpen U := isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  have hempty : ∀ x ∈ K \ U, multiplicity limit x = 0 := by
    intro x hx
    by_contra hm
    let j : J := ⟨x, hx.1, hm⟩
    exact hx.2 (mem_iUnion.2 ⟨j, Metric.mem_ball_self (hr j)⟩)
  have hno := eventually_no_atoms_on_compact hc (hK.diff hU) hempty
  have hinside : ∀ᶠ k in l, ∀ j : J, p k j ∈ K ∧ dist (p k j) j.val < r j := by
    apply eventually_all.2
    intro j
    have hjInt : j.val ∈ interior K := by
      apply (mem_interior_iff_notMem_frontier j.property.1).2
      intro hjbd
      have hz := hboundary j hjbd
      rw [hj1 j] at hz
      contradiction
    have hk := (hp j).eventually (mem_of_superset
      (isOpen_interior.mem_nhds hjInt) interior_subset)
    have hb := (hp j).eventually (Metric.ball_mem_nhds j.val (hr j))
    exact hk.and hb
  have huni : ∀ᶠ k in l, ∀ j : J, ∃ y, dist y j.val < r j ∧
      multiplicity (c k) y = 1 ∧
        ∀ z, dist z j.val < r j → multiplicity (c k) z ≠ 0 → z = y :=
    eventually_all.2 hnear
  refine ⟨p, hp, ?_⟩
  filter_upwards [hevp, hinside, huni, hno] with k hk hi hu hn
  refine ⟨hk.1, fun j ↦ ⟨(hi j).1, hk.2 j⟩, ?_⟩
  intro y hy
  constructor
  · intro hmy
    have hyU : y ∈ U := by
      by_contra hny
      exact hmy (hn y ⟨hy, hny⟩)
    obtain ⟨j, hj⟩ := mem_iUnion.1 hyU
    obtain ⟨z, hz, hmz, huniq⟩ := hu j
    have hpy := huniq (p k j) (hi j).2 (by rw [hk.2 j]; norm_num)
    exact ⟨j, hpy.trans (huniq y hj hmy).symm⟩
  · rintro ⟨j, rfl⟩
    rw [hk.2 j]
    norm_num

end OTSelector.PointProcess.LocalConfiguration
