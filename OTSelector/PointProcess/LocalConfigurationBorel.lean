import OTSelector.PointProcess.LocalConfigurationCloudTopology
import Mathlib.Topology.Sequences
import Mathlib.Topology.Metrizable.Basic

/-!
# Vague Borel compatibility of actual locally finite configurations

Distance tents centered at a fixed countable dense set, with rational radii, separate locally
finite integer configurations: isolate one occupied site and choose a tent supported in its
isolating neighborhood.  The resulting countable continuous test code is a measurable embedding
by Lusin–Souslin.  Together with the labeled-cloud construction this proves that the original
shell-code sigma algebra is exactly the Borel sigma algebra of the actual vague topology.
-/

open Function MeasureTheory Set Topology TopologicalSpace
open scoped BigOperators Classical CompactlySupported

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [ProperSpace X] {base : X}

/-- A nonnegative distance tent; properness makes its closed-ball support compact. -/
noncomputable def distanceTent (center : X) (radius : ℝ) : C_c(X, ℝ) where
  toFun x := max 0 (radius - dist x center)
  continuous_toFun := continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall center radius)
    intro x hx
    change dist x center ≤ radius
    apply le_of_lt
    by_contra h
    exact hx (max_eq_left (sub_nonpos.mpr (le_of_not_gt h)))

@[simp]
theorem distanceTent_apply (center : X) (radius : ℝ) (x : X) :
    distanceTent center radius x = max 0 (radius - dist x center) := rfl

theorem support_distanceTent_subset_ball (center : X) (radius : ℝ) :
    Function.support (distanceTent center radius) ⊆ Metric.ball center radius := by
  intro x hx
  change dist x center < radius
  by_contra h
  exact hx (max_eq_left (sub_nonpos.mpr (le_of_not_gt h)))

/-- Around any site, two locally finite configurations have no other occupied sites in a
sufficiently small ball. -/
theorem exists_isolating_ball (config config' : LocalConfiguration base) (x : X) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y, dist y x < ε → y ≠ x →
      multiplicity config y = 0 ∧ multiplicity config' y = 0 := by
  let S := (Metric.closedBall x 1 ∩ Function.support (multiplicity config)) ∪
    (Metric.closedBall x 1 ∩ Function.support (multiplicity config'))
  have hS : S.Finite :=
    ((locallyFiniteSupport_multiplicity config).finite_inter_support_of_isCompact
      (isCompact_closedBall x 1)).union
    ((locallyFiniteSupport_multiplicity config').finite_inter_support_of_isCompact
      (isCompact_closedBall x 1))
  have hnhds : (S \ {x})ᶜ ∈ 𝓝 x :=
    (hS.sdiff (t := {x})).isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩
  intro y hy hyx
  have hy1 : dist y x ≤ 1 := (hy.trans_le (min_le_left _ _)).le
  have hynot : y ∉ S := by
    intro hyS
    exact hsub (hy.trans_le (min_le_right _ _)) ⟨hyS, by simpa using hyx⟩
  constructor
  · by_contra hc
    exact hynot (Or.inl ⟨hy1, hc⟩)
  · by_contra hc
    exact hynot (Or.inr ⟨hy1, hc⟩)

section CountableTests

variable [SecondCountableTopology X]

/-- A fixed countable family of compactly supported tests, chosen from the geometry alone. -/
noncomputable def separatingTest (base : X) (i : ℕ × ℚ) : C_c(X, ℝ) := by
  let : Nonempty X := ⟨base⟩
  exact distanceTent (TopologicalSpace.denseSeq X i.1) (i.2 : ℝ)

/-- The values of the countable geometric test family on the actual configuration. -/
noncomputable def separatingTestCode (config : LocalConfiguration base) (i : ℕ × ℚ) : ℝ :=
  testIntegral config (separatingTest base i)

/-- The countable distance-tent tests distinguish every multiplicity at every location. -/
theorem separatingTestCode_injective :
    Function.Injective (separatingTestCode : LocalConfiguration base → (ℕ × ℚ → ℝ)) := by
  intro config config' heq
  apply toLocallyFinsupp_injective
  ext x
  obtain ⟨ε, hε, hisolate⟩ := exists_isolating_ball config config' x
  let : Nonempty X := ⟨base⟩
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq X).exists_dist_lt x
    (show 0 < ε / 4 by positivity)
  obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
  let f := distanceTent (TopologicalSpace.denseSeq X n) (r : ℝ)
  have hfx : 0 < f x := by
    change 0 < max 0 ((r : ℝ) - dist x (TopologicalSpace.denseSeq X n))
    exact lt_max_of_lt_right (by linarith)
  have hfsmall {y : X} (hy : f y ≠ 0) : dist y x < ε := by
    have hyr := support_distanceTent_subset_ball _ _ hy
    have htri := dist_triangle y (TopologicalSpace.denseSeq X n) x
    rw [dist_comm (TopologicalSpace.denseSeq X n) x] at htri
    change dist y (TopologicalSpace.denseSeq X n) < (r : ℝ) at hyr
    linarith
  have hsum (c : LocalConfiguration base)
      (hc : ∀ y, dist y x < ε → y ≠ x → multiplicity c y = 0) :
      testIntegral c f = (multiplicity c x : ℝ) * f x := by
    apply finsum_eq_single (testSummand c f) x
    intro y hyx
    by_cases hfy : f y = 0
    · simp [testSummand, hfy]
    · simp [testSummand, hc y (hfsmall hfy) hyx]
  have hc := hsum config (fun y hy hyx ↦ (hisolate y hy hyx).1)
  have hc' := hsum config' (fun y hy hyx ↦ (hisolate y hy hyx).2)
  have htest := congrFun heq (n, r)
  change testIntegral config f = testIntegral config' f at htest
  rw [hc, hc'] at htest
  exact_mod_cast mul_right_cancel₀ hfx.ne' htest

/-- The separating code is continuous for the vague topology because each coordinate is an
actual compactly supported test integral. -/
theorem continuous_separatingTestCode :
    Continuous[vagueTopology base, inferInstance]
      (separatingTestCode : LocalConfiguration base → (ℕ × ℚ → ℝ)) := by
  let : TopologicalSpace (LocalConfiguration base) := vagueTopology base
  apply continuous_pi
  intro i
  exact continuous_testIntegral (separatingTest base i)

/-- The actual vague topology is Hausdorff, as witnessed by the geometric separating tests. -/
theorem vagueT2Space : @T2Space (LocalConfiguration base) (vagueTopology base) := by
  let : TopologicalSpace (LocalConfiguration base) := vagueTopology base
  exact T2Space.of_injective_continuous separatingTestCode_injective continuous_separatingTestCode

section CompactSets

noncomputable local instance : TopologicalSpace (LocalConfiguration base) := vagueTopology base

/-- On every genuinely compact set, the countable geometric test code is a topological embedding;
thus that compact set is metrizable without asserting metrizability of the full carrier. -/
theorem metrizableSpace_of_isCompact {K : Set (LocalConfiguration base)} (hK : IsCompact K) :
    MetrizableSpace K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcont := (continuous_separatingTestCode (base := base)).comp
    (continuous_subtype_val : Continuous (Subtype.val : K → LocalConfiguration base))
  exact (hcont.isClosedEmbedding
    (separatingTestCode_injective.comp Subtype.val_injective)).isEmbedding.metrizableSpace

/-- Any sequence contained in a compact set of actual configurations has a vaguely convergent
subsequence.  This uses the proved geometric test code on the compact set. -/
theorem isSeqCompact_of_isCompact {K : Set (LocalConfiguration base)} (hK : IsCompact K) :
    IsSeqCompact K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MetrizableSpace K := metrizableSpace_of_isCompact hK
  intro config hconfig
  obtain ⟨limit, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq
    (fun n ↦ (⟨config n, hconfig n⟩ : K))
  exact ⟨limit.val, limit.property, φ, hφ,
    (continuous_subtype_val.tendsto limit).comp hlim⟩

end CompactSets

end CountableTests

section Borel

variable [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X] [SecondCountableTopology X]

theorem measurable_separatingTestCode :
    Measurable (separatingTestCode : LocalConfiguration base → (ℕ × ℚ → ℝ)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_testIntegral (separatingTest base i)

/-- The actual vague topology and the shell encoding have precisely the same measurable sets. -/
theorem vagueBorel_eq : @borel (LocalConfiguration base) (vagueTopology base) =
    (inferInstance : MeasurableSpace (LocalConfiguration base)) := by
  apply le_antisymm vagueBorel_le
  have hEmbedding := measurable_separatingTestCode.measurableEmbedding
    (separatingTestCode_injective (base := base))
  have hId : @Measurable (LocalConfiguration base) (LocalConfiguration base)
      (@borel _ (vagueTopology base)) inferInstance id := by
    let : TopologicalSpace (LocalConfiguration base) := vagueTopology base
    have hcomp := (continuous_separatingTestCode (base := base)).borel_measurable
    rw [← BorelSpace.measurable_eq (α := ℕ × ℚ → ℝ)] at hcomp
    exact hEmbedding.measurable_comp_iff.mp hcomp
  intro s hs
  exact hId hs

/-- Borel compatibility is a proved property of the vague topology, not an imposed convention. -/
theorem vagueBorelSpace :
    @BorelSpace (LocalConfiguration base) (vagueTopology base) inferInstance := by
  let : TopologicalSpace (LocalConfiguration base) := vagueTopology base
  exact ⟨vagueBorel_eq.symm⟩

end Borel

end OTSelector.PointProcess.LocalConfiguration
