import OTSelector.PointProcess.MatchingSceneTransportFlux
import OTSelector.Matching.OneStepBootstrap

/-!
# Actual edge sums and finite crossing recovery

Counting integrals enumerate precisely the atoms of the original configuration. For a simple
perfect scene this enumeration is the actual source-to-target assignment, so the transported
continuous crossing tests recover the matching current.
-/

open MeasureTheory Set Function Filter Topology
open scoped BigOperators Classical ENNReal CompactlySupported

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {base : X}

omit [MeasurableSpace X] [BorelSpace X] in
theorem countable_multiplicity_support (config : LocalConfiguration base) :
    (Function.support (multiplicity config)).Countable := by
  apply (Set.countable_iUnion (fun n ↦ (windowSupport config n).finite_toSet.countable)).mono
  intro x hx
  exact mem_iUnion.mpr ⟨shellIndex base x + 1,
    (mem_windowSupport_iff config _ x).mpr ⟨Nat.lt_succ_self _, hx⟩⟩

theorem ae_mem_multiplicity_support (config : LocalConfiguration base) :
    ∀ᵐ x ∂countingMeasure config, x ∈ Function.support (multiplicity config) := by
  rw [ae_iff]
  change countingMeasure config (Function.support (multiplicity config))ᶜ = 0
  rw [countingMeasure_apply config (countable_multiplicity_support config).measurableSet.compl]
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  rw [shellMeasure_apply _ _ (countable_multiplicity_support config).measurableSet.compl]
  apply Multiset.sum_eq_zero
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hv
  apply Set.indicator_of_notMem
  change ¬ ¬ multiplicity config x.val ≠ 0
  rw [multiplicity_shell]
  exact not_not.mpr (Multiset.count_ne_zero.mpr hx)

/-- Exact enumeration of every nonnegative counting observable, retaining multiplicities. -/
theorem lintegral_eq_tsum_atoms (config : LocalConfiguration base) (f : X → ℝ≥0∞) :
    (∫⁻ x, f x ∂countingMeasure config) =
      ∑' x : {x // multiplicity config x ≠ 0}, f x.val * multiplicity config x.val := by
  have hres := Measure.restrict_eq_self_of_ae_mem (ae_mem_multiplicity_support config)
  rw [← hres, lintegral_countable f (countable_multiplicity_support config)]
  simp only [countingMeasure_singleton, Function.support, Set.coe_ofPred]

/-- Integrable signed counting observables have the same exact atom enumeration. -/
theorem integral_eq_tsum_atoms (config : LocalConfiguration base) {f : X → ℝ}
    (hf : Integrable f (countingMeasure config)) :
    (∫ x, f x ∂countingMeasure config) =
      ∑' x : {x // multiplicity config x ≠ 0}, (multiplicity config x.val : ℝ) * f x.val := by
  have hres := Measure.restrict_eq_self_of_ae_mem (ae_mem_multiplicity_support config)
  have h := setIntegral_countable f (countable_multiplicity_support config) hf.integrableOn
  rw [hres] at h
  simpa only [measureReal_def, countingMeasure_singleton, ENNReal.toReal_natCast, smul_eq_mul,
    Function.support, Set.coe_ofPred] using h

/-- Only finitely many actual atoms can each contribute at least one to a finite counting
integral. This is the standard finite-superlevel property of a convergent nonnegative sum. -/
theorem finite_atoms_one_le_of_lintegral_lt_top (config : LocalConfiguration base)
    {f : X → ℝ≥0∞} (hf : (∫⁻ x, f x ∂countingMeasure config) < ∞) :
    {x | multiplicity config x ≠ 0 ∧ 1 ≤ f x}.Finite := by
  rw [lintegral_eq_tsum_atoms] at hf
  have hfin := ENNReal.finite_const_le_of_tsum_ne_top hf.ne (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
  apply (hfin.image Subtype.val).subset
  intro x hx
  refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
  change 1 ≤ f x * (multiplicity config x : ℝ≥0∞)
  have hm : (1 : ℝ≥0∞) ≤ multiplicity config x := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hx.1)
  simpa using mul_le_mul hx.2 hm

end OTSelector.PointProcess.LocalConfiguration

namespace OTSelector.PointProcess.MatchingScene

/-- The actual source labels and actual edge labels are in canonical bijection. -/
noncomputable def sourceEdgeEquiv {scene : MatchingScene} (h : IsSimplePerfectMatching scene) :
    SourceAtom scene ≃ {e // LocalConfiguration.multiplicity scene.edges e ≠ 0} where
  toFun x := ⟨(x.val, (atomAssignment h x).val), atomAssignment_edge h x⟩
  invFun e := ⟨e.val.1, (h.endpoints _ e.property).1⟩
  left_inv _ := rfl
  right_inv e := by
    apply Subtype.ext
    exact h.source_injective (atomAssignment_edge h _) e.property rfl

/-- A perfect simple scene's actual edge counting integral is its assignment sum. -/
theorem lintegral_edges_eq_tsum_source {scene : MatchingScene}
    (h : IsSimplePerfectMatching scene) (f : MatchingPoint × MatchingPoint → ℝ≥0∞) :
    (∫⁻ e, f e ∂LocalConfiguration.countingMeasure scene.edges) =
      ∑' x : SourceAtom scene, f (x.val, (atomAssignment h x).val) := by
  rw [LocalConfiguration.lintegral_eq_tsum_atoms, ← (sourceEdgeEquiv h).tsum_eq]
  apply tsum_congr
  intro x
  have hm : LocalConfiguration.multiplicity scene.edges (x.val, (atomAssignment h x).val) = 1 :=
    Nat.le_antisymm (h.simple_edges _) (Nat.one_le_iff_ne_zero.mpr (atomAssignment_edge h x))
  change f (x.val, (atomAssignment h x).val) *
    (LocalConfiguration.multiplicity scene.edges (x.val, (atomAssignment h x).val) : ℝ≥0∞) = _
  rw [hm, Nat.cast_one, mul_one]

/-- Signed integrable edge observables enumerate the same actual assignment. -/
theorem integral_edges_eq_tsum_source {scene : MatchingScene}
    (h : IsSimplePerfectMatching scene) {f : MatchingPoint × MatchingPoint → ℝ}
    (hf : Integrable f (LocalConfiguration.countingMeasure scene.edges)) :
    (∫ e, f e ∂LocalConfiguration.countingMeasure scene.edges) =
      ∑' x : SourceAtom scene, f (x.val, (atomAssignment h x).val) := by
  rw [LocalConfiguration.integral_eq_tsum_atoms _ hf, ← (sourceEdgeEquiv h).tsum_eq]
  apply tsum_congr
  intro x
  have hm : LocalConfiguration.multiplicity scene.edges (x.val, (atomAssignment h x).val) = 1 :=
    Nat.le_antisymm (h.simple_edges _) (Nat.one_le_iff_ne_zero.mpr (atomAssignment_edge h x))
  change (LocalConfiguration.multiplicity scene.edges (x.val, (atomAssignment h x).val) : ℝ) *
    f (x.val, (atomAssignment h x).val) = _
  rw [hm, Nat.cast_one, one_mul]

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.PointProcess.MatchingScene

private theorem eventually_invNat_lt_abs {ι : Type*} (f : ι → ℝ)
    (hfinite : {i | f i ∈ Icc (-1 : ℝ) 1}.Finite) (hzero : ∀ i, f i ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∀ i, 1 / ((n : ℝ) + 1) < |f i| := by
  have hlim : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlocal : ∀ᶠ n : ℕ in atTop, ∀ i ∈ {i | f i ∈ Icc (-1 : ℝ) 1},
      1 / ((n : ℝ) + 1) < |f i| :=
    hfinite.eventually_all.mpr (fun i _ ↦ hlim.eventually (gt_mem_nhds (abs_pos.mpr (hzero i))))
  filter_upwards [hlocal, hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hn1 i
  by_cases hi : f i ∈ Icc (-1 : ℝ) 1
  · exact hn i hi
  · exact hn1.trans (lt_of_not_ge (fun h ↦ hi (abs_le.mp h)))

/-- At a cut containing no source or target atom, shrinking soft crossings eventually equal
all actual assignment crossings simultaneously. Local finiteness supplies the common gap. -/
theorem eventually_softCrossing_eq_crossingSign {scene : MatchingScene}
    (h : IsSimplePerfectMatching scene)
    (hsource : ∀ x : SourceAtom scene, x.val.1 ≠ 0)
    (htarget : ∀ y : TargetAtom scene, y.val.1 ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∀ x : SourceAtom scene,
      softCrossing (1 / ((n : ℝ) + 1)) (x.val, (atomAssignment h x).val) =
        (crossingSign x.val.1 (atomAssignment h x).val.1 0 : ℝ) := by
  have hs := eventually_invNat_lt_abs (fun x : SourceAtom scene ↦ x.val.1)
    (finite_sourceAtoms_window scene (-1) 1) hsource
  have ht := eventually_invNat_lt_abs (fun y : TargetAtom scene ↦ y.val.1)
    (finite_targetAtoms_window scene (-1) 1) htarget
  filter_upwards [hs, ht] with n hnS hnT x
  have he := abs_crossingSign_sub_softCrossing_le
    (by positivity : 0 < 1 / ((n : ℝ) + 1)) (x.val, (atomAssignment h x).val)
  simp only [not_le.mpr (hnS x), not_le.mpr (hnT (atomAssignment h x)),
    ite_false, add_zero] at he
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))).symm

/-- The signed crossing support is finite once the genuine counting moments of the soft
crossings are finite. No bound on unknown partners is assumed. -/
theorem finite_crossingSupport_zero_of_soft_moments {scene : MatchingScene}
    (h : IsSimplePerfectMatching scene)
    (hsource : ∀ x : SourceAtom scene, x.val.1 ≠ 0)
    (htarget : ∀ y : TargetAtom scene, y.val.1 ≠ 0)
    (hmoment : ∀ n : ℕ, (∫⁻ e, ENNReal.ofReal |softCrossing (1 / ((n : ℝ) + 1)) e|
      ∂LocalConfiguration.countingMeasure scene.edges) < ∞) :
    (Function.support (fun x : SourceAtom scene ↦
      crossingSign x.val.1 (atomAssignment h x).val.1 0)).Finite := by
  obtain ⟨n, hn⟩ := (eventually_softCrossing_eq_crossingSign h hsource htarget).exists
  have hm := hmoment n
  rw [lintegral_edges_eq_tsum_source h] at hm
  simp_rw [hn] at hm
  have hfin := ENNReal.finite_const_le_of_tsum_ne_top hm.ne
    (one_ne_zero : (1 : ℝ≥0∞) ≠ 0)
  apply hfin.subset
  intro x hx
  change 1 ≤ ENNReal.ofReal |(crossingSign x.val.1 (atomAssignment h x).val.1 0 : ℝ)|
  have habs : |(crossingSign x.val.1 (atomAssignment h x).val.1 0 : ℝ)| = 1 := by
    have hx' : crossingSign x.val.1 (atomAssignment h x).val.1 0 ≠ 0 := hx
    unfold crossingSign at hx' ⊢
    split_ifs at hx' ⊢ <;> norm_num at *
  rw [habs, ENNReal.ofReal_one]

/-- Genuine strict crossings are among the finite signed crossing support. -/
theorem finite_crosses_zero_of_soft_moments {scene : MatchingScene}
    (h : IsSimplePerfectMatching scene)
    (hsource : ∀ x : SourceAtom scene, x.val.1 ≠ 0)
    (htarget : ∀ y : TargetAtom scene, y.val.1 ≠ 0)
    (hmoment : ∀ n : ℕ, (∫⁻ e, ENNReal.ofReal |softCrossing (1 / ((n : ℝ) + 1)) e|
      ∂LocalConfiguration.countingMeasure scene.edges) < ∞) :
    {x : SourceAtom scene | OTSelector.Matching.Crosses 0
      ((spatialMatching h).source x) ((spatialMatching h).target ((spatialMatching h).assignment x))}.Finite := by
  apply (finite_crossingSupport_zero_of_soft_moments h hsource htarget hmoment).subset
  intro x hx
  change crossingSign x.val.1 (atomAssignment h x).val.1 0 ≠ 0
  rcases hx with hx | hx
  · simp only [spatialMatching] at hx
    simp [crossingSign, hx.1.le, not_le.mpr hx.2]
  · simp only [spatialMatching] at hx
    simp [crossingSign, hx.1.le, not_le.mpr hx.2]

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.PointProcess.MatchingScene

/-- Once a root is not an endpoint, the compact continuous tests eventually equal the
actual (finite) crossing sum, with exactly the original integer-current convention. -/
theorem eventually_crossingTest_eq_current {scene : MatchingScene}
    (h : IsSimplePerfectMatching scene)
    (hsource : ∀ x : SourceAtom scene, x.val.1 ≠ 0)
    (htarget : ∀ y : TargetAtom scene, y.val.1 ≠ 0)
    (hmoment : ∀ n : ℕ, (∫⁻ e, ENNReal.ofReal |softCrossing (1 / ((n : ℝ) + 1)) e|
      ∂LocalConfiguration.countingMeasure scene.edges) < ∞) :
    ∀ᶠ n : ℕ in atTop, LocalConfiguration.testIntegral scene.edges
      (crossingTest (1 / ((n : ℝ) + 1)) (n + 1)) = ((spatialMatching h).current 0 : ℝ) := by
  let S := Function.support (fun x : SourceAtom scene ↦
    crossingSign x.val.1 (atomAssignment h x).val.1 0)
  have hS : S.Finite := finite_crossingSupport_zero_of_soft_moments h hsource htarget hmoment
  have hcut : ∀ᶠ n : ℕ in atTop, ∀ x ∈ S,
      dist (x.val, (atomAssignment h x).val) (matchingPointBase, matchingPointBase) ≤ n + 1 := by
    apply hS.eventually_all.mpr
    intro x hx
    obtain ⟨k, hk⟩ := exists_nat_ge
      (dist (x.val, (atomAssignment h x).val) (matchingPointBase, matchingPointBase))
    filter_upwards [eventually_ge_atTop k] with n hn
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  filter_upwards [eventually_softCrossing_eq_crossingSign h hsource htarget, hcut] with n hn hnc
  rw [← LocalConfiguration.integral_countingMeasure,
    integral_edges_eq_tsum_source h (LocalConfiguration.integrable_countingMeasure _ _)]
  have hval (x : SourceAtom scene) :
      crossingTest (1 / ((n : ℝ) + 1)) (n + 1) (x.val, (atomAssignment h x).val) =
        (crossingSign x.val.1 (atomAssignment h x).val.1 0 : ℝ) := by
    change min 1 (max 0 (((n + 1 : ℕ) : ℝ) + 1 -
      dist (x.val, (atomAssignment h x).val) (matchingPointBase, matchingPointBase))) *
      softCrossing (1 / ((n : ℝ) + 1)) (x.val, (atomAssignment h x).val) = _
    rw [hn x]
    by_cases hx : x ∈ S
    · have hc := hnc x hx
      have hχ : (1 : ℝ) ≤ max 0 (((n + 1 : ℕ) : ℝ) + 1 -
          dist (x.val, (atomAssignment h x).val) (matchingPointBase, matchingPointBase)) :=
        (show (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 1 -
          dist (x.val, (atomAssignment h x).val) (matchingPointBase, matchingPointBase) by
            push_cast; linarith).trans (le_max_right _ _)
      rw [min_eq_left hχ, one_mul]
    · have hz : crossingSign x.val.1 (atomAssignment h x).val.1 0 = 0 :=
        not_not.mp hx
      rw [hz, Int.cast_zero, mul_zero]
  simp_rw [hval]
  have hout (x : SourceAtom scene) (hx : x ∉ hS.toFinset) :
      crossingSign x.val.1 (atomAssignment h x).val.1 0 = 0 := by
    apply not_not.mp
    simpa only [Set.Finite.mem_toFinset, S, Function.mem_support] using hx
  rw [tsum_eq_sum (s := hS.toFinset) (fun x hx ↦ by rw [hout x hx, Int.cast_zero])]
  change _ = ((∑' x : SourceAtom scene,
    crossingSign x.val.1 (atomAssignment h x).val.1 0 : ℤ) : ℝ)
  rw [tsum_eq_sum (s := hS.toFinset) hout, Int.cast_sum]

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.PointProcess.MatchingScene

/-- The complete soft-crossing moment is a measurable observable of the actual edge code. -/
theorem measurable_softCrossingMoment (ε : ℝ) : Measurable
    (fun scene : MatchingScene ↦ ∫⁻ e, ENNReal.ofReal |softCrossing ε e|
      ∂LocalConfiguration.countingMeasure scene.edges) := by
  simp_rw [LocalConfiguration.lintegral_countingWeight_eq_iSup_test _
    (continuous_softCrossing ε).abs (fun _ ↦ abs_nonneg _)]
  exact Measurable.iSup fun n ↦ (continuous_edgeTest
    (LocalConfiguration.compactWeightTest _ (continuous_softCrossing ε).abs n)).measurable.ennreal_ofReal

/-- Every perfect scene in the actual weak-limit law has finite root crossings and its actual
crossing current equals the transported root-current coordinate. Endpoint non-atomicity at zero
is supplied by the environment marginal; no flux or matching tail is assumed. -/
theorem ae_current_zero_of_rootedMatchingSceneLaw_tendsto
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
      (∀ x : SourceAtom scene, x.val.1 ≠ 0) ∧ (∀ y : TargetAtom scene, y.val.1 ≠ 0)) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), ∀ hp : IsSimplePerfectMatching scene,
      (Function.support (fun x : SourceAtom scene ↦
        crossingSign x.val.1 (atomAssignment hp x).val.1 0)).Finite ∧
      (spatialMatching hp).current 0 = scene.path.rootCurrent := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hsoft (n : ℕ) : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      (∫⁻ e, ENNReal.ofReal |softCrossing (ε n) e|
        ∂LocalConfiguration.countingMeasure scene.edges) < ∞ := by
    apply ae_lt_top (measurable_softCrossingMoment (ε n))
    exact ((lintegral_abs_softCrossing_of_rootedMatchingSceneLaw_tendsto
      sample graph assignment a b hab hlaw hμ henergy hcount (hε n)).trans_lt
      ENNReal.ofReal_lt_top).ne
  have hsoftall := ae_all_iff.mpr hsoft
  let f (n : ℕ) (scene : MatchingScene) : ℝ≥0∞ := ENNReal.ofReal
    |(scene.path.rootCurrent : ℝ) - LocalConfiguration.testIntegral scene.edges
      (crossingTest (ε n) (n + 1))|
  have hf (n : ℕ) : Measurable (f n) := by
    have hcurrent : Continuous (fun scene : MatchingScene ↦ (scene.path.rootCurrent : ℝ)) :=
      (continuous_of_discreteTopology : Continuous (fun k : ℤ ↦ (k : ℝ))).comp
        continuous_rootCurrent
    exact (hcurrent.sub (continuous_edgeTest _)).abs.measurable.ennreal_ofReal
  have hbound (n : ℕ) : (∫⁻ scene, f n scene ∂(ν : Measure MatchingScene)) ≤
      ENNReal.ofReal (C / ((n : ℝ) + 1) + 4 * ε n * ρ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      lintegral_rootCurrent_sub_crossingTest_of_rootedMatchingSceneLaw_tendsto
        sample graph assignment a b hab hlaw hμ henergy hcount (hε n) (Nat.le_add_left 1 n)
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C / ((n : ℝ) + 1) + 4 * ε n * ρ))
      atTop (𝓝 0) := by
    have heps : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have heq (n : ℕ) : C / ((n : ℝ) + 1) + 4 * ε n * ρ = (C + 4 * ρ) * ε n := by
      dsimp [ε]; ring
    simp_rw [heq]
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (heps.const_mul (C + 4 * ρ))
  have hintlim : Tendsto (fun n ↦ ∫⁻ scene, f n scene ∂(ν : Measure MatchingScene))
      atTop (𝓝 0) := tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hlim (fun _ ↦ zero_le) hbound
  have hfatou : (∫⁻ scene, liminf (fun n ↦ f n scene) atTop
      ∂(ν : Measure MatchingScene)) = 0 :=
    le_antisymm ((lintegral_liminf_le hf).trans_eq hintlim.liminf_eq) zero_le
  have hae := (lintegral_eq_zero_iff (Measurable.liminf hf)).mp hfatou
  filter_upwards [hzero, hsoftall, hae] with scene hz hs he hp
  have hfinite := finite_crossingSupport_zero_of_soft_moments hp hz.1 hz.2 hs
  refine ⟨hfinite, ?_⟩
  have htest := eventually_crossingTest_eq_current hp hz.1 hz.2 hs
  have hevent : ∀ᶠ n : ℕ in atTop, f n scene =
      ENNReal.ofReal |(scene.path.rootCurrent : ℝ) - ((spatialMatching hp).current 0 : ℝ)| := by
    filter_upwards [htest] with n hn
    change ENNReal.ofReal |(scene.path.rootCurrent : ℝ) - _| = _
    rw [hn]
  have hevent' : (fun n ↦ f n scene) =ᶠ[atTop] (fun _ ↦
      ENNReal.ofReal |(scene.path.rootCurrent : ℝ) - ((spatialMatching hp).current 0 : ℝ)|) := hevent
  have hval := (tendsto_const_nhds.congr' hevent'.symm).liminf_eq
  have hzeroReal : |(scene.path.rootCurrent : ℝ) - ((spatialMatching hp).current 0 : ℝ)| = 0 := by
    have hval0 : ENNReal.ofReal
        |(scene.path.rootCurrent : ℝ) - ((spatialMatching hp).current 0 : ℝ)| = 0 := hval.symm.trans he
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hval0) (abs_nonneg _)
  exact_mod_cast (sub_eq_zero.mp (abs_eq_zero.mp hzeroReal)).symm

end OTSelector.PointProcess.MatchingScene
