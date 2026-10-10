import OTSelector.PointProcess.LocalConfigurationCloudTopology

/-!
# Compact containment from actual local point counts

Closed annuli provide compact coordinate spaces.  Their clouds are assembled by adding all
point multiplicities, including coincidences at annulus boundaries.  Compactly supported tests
see only finitely many annuli, so assembly is continuous for the actual vague topology.  The
compact image covers every shell-coded configuration satisfying prescribed shell count bounds.
-/

open Function Set Topology
open scoped BigOperators Classical CompactlySupported

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] {base : X}

/-- The compact replacement of a half-open coding shell. -/
abbrev ClosedAnnulus (base : X) (n : ℕ) :=
  {x : X // (n : ℝ) ≤ dist x base ∧ dist x base ≤ (n : ℝ) + 1}

/-- Labeled finite clouds in every closed annulus. -/
abbrev AnnulusClouds (base : X) := ∀ n, FinitePointCloud (ClosedAnnulus base n)

local instance (n : ℕ) : TopologicalSpace (FinitePointCloud (ClosedAnnulus base n)) :=
  FinitePointCloud.cloudTopology _

/-- The finite multiset formed by the first `N` annulus clouds. -/
noncomputable def annulusPrefix (clouds : AnnulusClouds base) (N : ℕ) : Multiset X :=
  ∑ n ∈ Finset.range N, (clouds n).toMultiset.map Subtype.val

private theorem count_annulus_zero (clouds : AnnulusClouds base) (n : ℕ) (x : X)
    (hn : shellIndex base x < n) :
    ((clouds n).toMultiset.map Subtype.val).count x = 0 := by
  apply Multiset.count_eq_zero_of_notMem
  intro hx
  obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
  exact (Nat.not_le_of_gt hn) (Nat.le_floor y.property.1)

/-- All contributions to a point occur at annulus indices no greater than its coding index. -/
noncomputable def annulusMultiplicity (clouds : AnnulusClouds base) (x : X) : ℕ :=
  (annulusPrefix clouds (shellIndex base x + 1)).count x

/-- Once a prefix reaches a point, its count is the complete assembled multiplicity. -/
theorem count_annulusPrefix (clouds : AnnulusClouds base) (N : ℕ) (x : X)
    (hx : dist x base < (N : ℝ)) :
    (annulusPrefix clouds N).count x = annulusMultiplicity clouds x := by
  have hxN := (shellIndex_lt_iff base x N).mpr hx
  change (Multiset.countAddMonoidHom x) (∑ n ∈ Finset.range N, _) =
    (Multiset.countAddMonoidHom x) (∑ n ∈ Finset.range (shellIndex base x + 1), _)
  rw [map_sum, map_sum]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hn'
  apply count_annulus_zero clouds n x
  simp only [Finset.mem_range] at hn'
  omega

/-- The assembled multiplicities have locally finite support by finite-prefix containment. -/
theorem locallyFiniteSupport_annulusMultiplicity (clouds : AnnulusClouds base) :
    LocallyFiniteSupport (annulusMultiplicity clouds) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (dist x base)
  refine ⟨Metric.ball base (N : ℝ), Metric.isOpen_ball.mem_nhds hN, ?_⟩
  apply (annulusPrefix clouds N).toFinset.finite_toSet.subset
  intro y hy
  apply Multiset.mem_toFinset.mpr
  apply Multiset.count_ne_zero.mp
  rw [count_annulusPrefix clouds N y hy.1]
  exact hy.2

section Proper

variable [ProperSpace X]

/-- Add the actual annulus clouds, retaining all multiplicities at shared boundaries. -/
noncomputable def assembleAnnuli (clouds : AnnulusClouds base) : LocalConfiguration base :=
  ofLocallyFinsupp {
    toFun := annulusMultiplicity clouds
    supportWithinDomain' := subset_univ _
    supportLocallyFiniteWithinDomain' := fun x _ ↦
      locallyFiniteSupport_annulusMultiplicity clouds x }

@[simp]
theorem multiplicity_assembleAnnuli (clouds : AnnulusClouds base) (x : X) :
    multiplicity (assembleAnnuli clouds) x = annulusMultiplicity clouds x :=
  multiplicity_ofLocallyFinsupp _ x

/-- A compactly supported test of the assembly is exactly its finite-prefix multiset sum. -/
theorem testIntegral_assembleAnnuli_eq_prefix (clouds : AnnulusClouds base)
    (f : C_c(X, ℝ)) {N : ℕ} (hN : tsupport f ⊆ Metric.ball base (N : ℝ)) :
    testIntegral (assembleAnnuli clouds) f =
      ((annulusPrefix clouds N).map (fun x ↦ f x)).sum := by
  have hs : Function.support (testSummand (assembleAnnuli clouds) f) ⊆
      (annulusPrefix clouds N).toFinset := by
    intro x hx
    have hfx : f x ≠ 0 := by
      intro hzero
      exact hx (by simp [testSummand, hzero])
    have hcx : annulusMultiplicity clouds x ≠ 0 := by
      intro hzero
      exact hx (by simp [testSummand, hzero])
    apply Multiset.mem_toFinset.mpr
    apply Multiset.count_ne_zero.mp
    rw [count_annulusPrefix clouds N x (hN (subset_tsupport _ hfx))]
    exact hcx
  rw [testIntegral, finsum_eq_sum_of_support_subset _ hs,
    Finset.sum_multiset_map_count]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hfx : f x = 0
  · simp [testSummand, hfx]
  · simp only [testSummand, multiplicity_assembleAnnuli, nsmul_eq_mul,
      count_annulusPrefix clouds N x (hN (subset_tsupport _ hfx))]

/-- The finite-prefix identity in coordinate form, suitable for proving continuity. -/
theorem testIntegral_assembleAnnuli (clouds : AnnulusClouds base)
    (f : C_c(X, ℝ)) {N : ℕ} (hN : tsupport f ⊆ Metric.ball base (N : ℝ)) :
    testIntegral (assembleAnnuli clouds) f =
      ∑ n ∈ Finset.range N, ((clouds n).toMultiset.map (fun x ↦ f x.val)).sum := by
  rw [testIntegral_assembleAnnuli_eq_prefix clouds f hN]
  suffices ∀ N : ℕ, ((annulusPrefix clouds N).map (fun x ↦ f x)).sum =
      ∑ n ∈ Finset.range N, ((clouds n).toMultiset.map (fun x ↦ f x.val)).sum from this N
  intro N
  induction N with
  | zero => simp [annulusPrefix]
  | succ N h =>
      simp only [annulusPrefix, Finset.sum_range_succ] at h ⊢
      rw [Multiset.map_add, Multiset.sum_add, h, Multiset.map_map]
      rfl

/-- Annulus assembly is continuous for the actual vague topology. -/
theorem continuous_assembleAnnuli :
    Continuous[inferInstance, vagueTopology base] (assembleAnnuli : AnnulusClouds base → _) := by
  apply continuous_iInf_rng.mpr
  intro f
  apply continuous_induced_rng.mpr
  obtain ⟨N, hN⟩ := exists_testSupport_subset_ball f base
  have h : Continuous (fun clouds : AnnulusClouds base ↦
      ∑ n ∈ Finset.range N, ((clouds n).toMultiset.map (fun x ↦ f x.val)).sum) := by
    apply continuous_finsetSum
    intro n hn
    exact (FinitePointCloud.continuous_sum_toMultiset
      (f.continuous.comp continuous_subtype_val)).comp (_root_.continuous_apply n)
  convert h using 1
  funext clouds
  exact testIntegral_assembleAnnuli clouds f hN

private instance compactSpace_closedAnnulus (n : ℕ) : CompactSpace (ClosedAnnulus base n) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall base ((n : ℝ) + 1)).of_isClosed_subset
  · exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  · exact fun x hx ↦ hx.2

/-- Moving labeled atoms in their closed annuli with uniformly bounded cardinalities produces a
compact family of actual configurations. -/
theorem isCompact_assembleAnnuli_card_le (N : ℕ → ℕ) :
    @IsCompact _ (vagueTopology base)
      (assembleAnnuli '' {clouds : AnnulusClouds base | ∀ n, (clouds n).card ≤ N n}) := by
  let : TopologicalSpace (LocalConfiguration base) := vagueTopology base
  exact (isCompact_pi_infinite fun n ↦ FinitePointCloud.isCompact_card_le (N n)).image
    continuous_assembleAnnuli

/-- Include a coding shell into its closed annulus. -/
def shellToClosedAnnulus (n : ℕ) (x : Shell base n) : ClosedAnnulus base n :=
  ⟨x.val, ((shellIndex_eq_iff base x n).mp x.property).1,
    ((shellIndex_eq_iff base x n).mp x.property).2.le⟩

private theorem exists_cloud_toMultiset {Y : Type*} (m : Multiset Y) :
    ∃ cloud : FinitePointCloud Y, cloud.toMultiset = m := by
  refine ⟨⟨m.toList.length, m.toList.get⟩, ?_⟩
  simpa only [FinitePointCloud.toMultiset, FinitePointCloud.toList, List.ofFn_get] using
    Multiset.coe_toList m

/-- Every shell count bounded configuration belongs to a genuinely compact vague set.  Passing to
closed annuli permits atoms to cross shell boundaries without losing their multiplicities. -/
theorem exists_isCompact_superset_shellCard_le (N : ℕ → ℕ) :
    ∃ K : Set (LocalConfiguration base), @IsCompact _ (vagueTopology base) K ∧
      {config | ∀ n, (config n).card ≤ N n} ⊆ K := by
  refine ⟨_, isCompact_assembleAnnuli_card_le N, ?_⟩
  intro config hconfig
  choose clouds hclouds using fun n ↦
    exists_cloud_toMultiset ((config n).map (shellToClosedAnnulus n))
  have hcard : ∀ n, (clouds n).card ≤ N n := by
    intro n
    rw [← FinitePointCloud.card_toMultiset, hclouds n, Multiset.card_map]
    exact hconfig n
  refine ⟨clouds, hcard, ?_⟩
  apply toLocallyFinsupp_injective
  ext x
  simp only [toLocallyFinsupp_apply, multiplicity_assembleAnnuli, annulusMultiplicity]
  have hpref : ∀ M, annulusPrefix clouds M = window config M := by
    intro M
    unfold annulusPrefix window
    apply Finset.sum_congr rfl
    intro n hn
    rw [hclouds n, Multiset.map_map]
    rfl
  have hx := (shellIndex_lt_iff base x (shellIndex base x + 1)).mp (Nat.lt_succ_self _)
  simp only [hpref, count_window, hx, ↓reduceIte]

end Proper

end OTSelector.PointProcess.LocalConfiguration
