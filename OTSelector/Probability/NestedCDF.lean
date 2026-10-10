/-
Adapted from StatLean/Stat-Lean commit
`e1ef06bf52d2a8896439c5b59d982d9aad28a254`, source
`StatLean/HypothesisTesting/ForMathlib/DKWUniform.lean` (unreachable audited blob
`364185fc3ec43fe8ad438d509a4b2455044cb9e0`). Original source licensed under Apache-2.0.
-/

import OTSelector.Probability.Symmetrization.Empirical
import Mathlib.Probability.CDF
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Closed empirical CDF and Kolmogorov distance

This module provides the closed-threshold empirical CDF, its Kolmogorov distance, the
rational-supremum measurability reduction, the sign-walk expectation bound with constant four,
and a Markov tail corollary. McDiarmid concentration and the exponential DKW theorem are omitted.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSelector.Probability.NestedCDF

set_option linter.style.haveILetI false

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The **empirical distribution function** of a finite sample:
`F̂ₙ(t) = n⁻¹ #{i : Xᵢ ≤ t}`. For `n = 0` it is identically `0` (junk, excluded by the
side conditions of every statement below). -/
noncomputable def empCDF {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, if X i ω ≤ t then (1 : ℝ) else 0

/-- The **Kolmogorov distance** between the empirical distribution function of a sample and
the distribution function of a law `μ`: `Dₙ = supₜ |F̂ₙ(t) − F(t)|`.

The supremum ranges over all of `ℝ`; by right-continuity of both functions it agrees with
the supremum over the rationals, which is how measurability of `Dₙ` is obtained. -/
noncomputable def ksDist {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure ℝ) (ω : Ω) : ℝ :=
  ⨆ t : ℝ, |empCDF X ω t - cdf μ t|

omit [MeasurableSpace Ω] in
/-- The closed empirical CDF is nonnegative. -/
theorem empCDF_nonneg {n : ℕ} (X : Fin n → Ω → ℝ)
    (ω : Ω) (t : ℝ) :
    0 ≤ empCDF X ω t := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ ?_)
  split_ifs <;> norm_num

omit [MeasurableSpace Ω] in
/-- For a nonempty sample, the closed empirical CDF is at most one. -/
theorem empCDF_le_one {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (ω : Ω)
    (t : ℝ) : empCDF X ω t ≤ 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    empCDF X ω t
        ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (1 : ℝ) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ ?_) (by positivity)
          split_ifs <;> norm_num
    _ = (n : ℝ)⁻¹ * n := by simp
    _ = 1 := inv_mul_cancel₀ hn0

/-- At a fixed threshold, the closed empirical CDF is measurable in the sample outcome. -/
theorem measurable_empCDF {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (t : ℝ) : Measurable (fun ω ↦ empCDF X ω t) := by
  refine Measurable.const_mul (Finset.measurable_sum Finset.univ fun i _ ↦ ?_) _
  exact Measurable.ite (measurableSet_le (hmeas i) measurable_const)
    measurable_const measurable_const

/-! ### Deterministic reduction to a rational supremum -/

/-- The step indicator `t ↦ 1{a ≤ t}` is right continuous. -/
private lemma dkw_rightCont_step (a s : ℝ) :
    Filter.Tendsto (fun t => if a ≤ t then (1 : ℝ) else 0)
      (nhdsWithin s (Set.Ioi s)) (nhds (if a ≤ s then (1 : ℝ) else 0)) := by
  have hl : (fun _ : ℝ => if a ≤ s then (1 : ℝ) else 0)
      =ᶠ[nhdsWithin s (Set.Ioi s)] (fun t => if a ≤ t then (1 : ℝ) else 0) := by
    by_cases h : a ≤ s
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [ite_eq_left h, ite_eq_left (h.trans ht.le)]
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.mp h))] with t ht
      rw [ite_eq_right h, ite_eq_right (not_le.mpr ht)]
  exact Filter.Tendsto.congr' hl tendsto_const_nhds

/-- A real supremum of a right-continuous function over `ℝ` agrees with the supremum over
the rationals. -/
private lemma dkw_iSup_real_eq_iSup_rat (g : ℝ → ℝ)
    (hrc : ∀ s, Filter.Tendsto g (nhdsWithin s (Set.Ioi s)) (nhds (g s))) :
    ⨆ t : ℝ, g t = ⨆ q : ℚ, g (q : ℝ) := by
  by_cases hbdd : BddAbove (Set.range fun q : ℚ => g (q : ℝ))
  · have hle : ∀ t : ℝ, g t ≤ ⨆ q : ℚ, g (q : ℝ) := by
      intro t
      obtain ⟨u, hu_gt, hu_lt⟩ : ∃ u : ℕ → ℚ,
          (∀ k, t < (u k : ℝ)) ∧ (∀ k, (u k : ℝ) < t + 1 / ((k : ℝ) + 1)) := by
        choose u hu using fun k : ℕ =>
          exists_rat_btwn (show t < t + 1 / ((k : ℝ) + 1) from
            lt_add_of_pos_right t (by positivity))
        exact ⟨u, fun k => (hu k).1, fun k => (hu k).2⟩
      have hupper : Filter.Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) Filter.atTop (nhds t) := by
        have := (tendsto_const_nhds (x := t)).add tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using this
      have hnhds : Filter.Tendsto (fun k => (u k : ℝ)) Filter.atTop (nhds t) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
          (Filter.Eventually.of_forall fun k => (hu_gt k).le)
          (Filter.Eventually.of_forall fun k => (hu_lt k).le)
      have htend : Filter.Tendsto (fun k => (u k : ℝ)) Filter.atTop (nhdsWithin t (Set.Ioi t)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hnhds, Filter.Eventually.of_forall fun k => hu_gt k⟩
      exact le_of_tendsto ((hrc t).comp htend)
        (Filter.Eventually.of_forall fun k => le_ciSup hbdd (u k))
    have hbddR : BddAbove (Set.range g) :=
      ⟨⨆ q : ℚ, g (q : ℝ), by rintro _ ⟨t, rfl⟩; exact hle t⟩
    exact le_antisymm (ciSup_le hle) (ciSup_le fun q => le_ciSup hbddR (q : ℝ))
  · have hbddR : ¬ BddAbove (Set.range g) := by
      intro hR
      obtain ⟨M, hM⟩ := hR
      exact hbdd ⟨M, by rintro _ ⟨q, rfl⟩; exact hM ⟨(q : ℝ), rfl⟩⟩
    rw [ciSup_of_not_bddAbove hbddR, ciSup_of_not_bddAbove hbdd]

omit [MeasurableSpace Ω] in
/-- The unrestricted Kolmogorov supremum equals the supremum over rational thresholds. -/
theorem ksDist_eq_iSup_rat {n : ℕ}
    (X : Fin n → Ω → ℝ) (μ : Measure ℝ) (ω : Ω) :
    ksDist X μ ω = ⨆ q : ℚ, |empCDF X ω (q : ℝ) - cdf μ (q : ℝ)| := by
  refine dkw_iSup_real_eq_iSup_rat (fun t ↦ |empCDF X ω t - cdf μ t|) fun s ↦ ?_
  have hempRC : Tendsto (fun t ↦ empCDF X ω t) (nhdsWithin s (Set.Ioi s))
      (nhds (empCDF X ω s)) := by
    simp only [empCDF]
    exact (tendsto_finsetSum Finset.univ
      fun i _ ↦ dkw_rightCont_step (X i ω) s).const_mul _
  have hcdfRC : Tendsto (fun t ↦ cdf μ t) (nhdsWithin s (Set.Ioi s)) (nhds (cdf μ s)) :=
    ((cdf μ).right_continuous s).mono Set.Ioi_subset_Ici_self
  exact Filter.Tendsto.abs (hempRC.sub hcdfRC)

omit [MeasurableSpace Ω] in
/-- Every empirical/population CDF discrepancy is at most one. -/
theorem abs_empCDF_sub_cdf_le_one {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (μ : Measure ℝ) (ω : Ω) (t : ℝ) : |empCDF X ω t - cdf μ t| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [empCDF_nonneg X ω t, empCDF_le_one hn X ω t,
    cdf_nonneg μ t, cdf_le_one μ t]

omit [MeasurableSpace Ω] in
/-- The Kolmogorov distance is nonnegative for a nonempty sample. -/
theorem ksDist_nonneg {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (μ : Measure ℝ)
    (ω : Ω) : 0 ≤ ksDist X μ ω := by
  rw [ksDist_eq_iSup_rat]
  refine le_ciSup_of_le ?_ (0 : ℚ) (abs_nonneg _)
  exact ⟨1, by
    rintro _ ⟨q, rfl⟩
    exact abs_empCDF_sub_cdf_le_one hn X μ ω q⟩

omit [MeasurableSpace Ω] in
/-- The Kolmogorov distance is bounded by one for a nonempty sample. -/
theorem ksDist_le_one {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (μ : Measure ℝ)
    (ω : Ω) : ksDist X μ ω ≤ 1 := by
  rw [ksDist_eq_iSup_rat]
  exact ciSup_le fun q ↦ abs_empCDF_sub_cdf_le_one hn X μ ω q

/-- The Kolmogorov distance is measurable when every sample coordinate is measurable. -/
theorem measurable_ksDist {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure ℝ)
    (hmeas : ∀ i, Measurable (X i)) : Measurable (ksDist X μ) := by
  have hfun : ksDist X μ = fun ω ↦
      ⨆ q : ℚ, |empCDF X ω (q : ℝ) - cdf μ (q : ℝ)| := by
    funext ω
    exact ksDist_eq_iSup_rat X μ ω
  rw [hfun]
  exact Measurable.iSup fun q ↦ continuous_abs.measurable.comp
    ((measurable_empCDF X hmeas (q : ℝ)).sub measurable_const)

/-- The Kolmogorov distance is integrable for a nonempty measurable sample. -/
theorem integrable_ksDist {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (μ : Measure ℝ)
    (hmeas : ∀ i, Measurable (X i)) : Integrable (ksDist X μ) P := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_ksDist X μ hmeas).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (ksDist_nonneg hn X μ ω)]
  exact ksDist_le_one hn X μ ω

/-! ### The symmetrised sign process: Lévy's maximal inequality for the `±1` walk

This section supplies the second half of route (4) of the header: conditionally on the
sample, the Rademacher process over half-lines is the `±1` walk along the sorted sample,
and its running maximum has `L¹` norm at most `2√n`.  Everything here is elementary; the
sign randomisation lives on `OTSelector.Probability.Symmetrization.signVec`. -/

section SignWalk

open OTSelector.Probability.Symmetrization

variable {n : ℕ}

/-- The `σ`-prefix of size `j`: the indices whose `σ`-rank is `< j`. -/
private def dkwPre (σ : Equiv.Perm (Fin n)) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ((σ.symm i : ℕ) < j))

/-- The `±1` walk along the `σ`-order, stopped after `j` steps. -/
private def dkwWalk (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ dkwPre σ j, s i

/-- The running maximum of `|dkwWalk|` over the `n + 1` prefixes. -/
private noncomputable def dkwMax (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) : ℝ :=
  ⨆ j : Fin (n + 1), |dkwWalk σ s (j : ℕ)|

private lemma dkwPre_mono (σ : Equiv.Perm (Fin n)) {j j' : ℕ} (h : j ≤ j') :
    dkwPre σ j ⊆ dkwPre σ j' := by
  intro i hi
  simp only [dkwPre, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact lt_of_lt_of_le hi h

private lemma dkwPre_zero (σ : Equiv.Perm (Fin n)) : dkwPre σ 0 = ∅ := by
  simp [dkwPre]

private lemma dkwPre_full (σ : Equiv.Perm (Fin n)) : dkwPre σ n = Finset.univ := by
  ext i
  simp only [dkwPre, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact (σ.symm i).isLt

private lemma dkwWalk_zero (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    dkwWalk σ s 0 = 0 := by
  simp [dkwWalk, dkwPre_zero]

private lemma measurable_dkwWalk (σ : Equiv.Perm (Fin n)) (j : ℕ) :
    Measurable (fun s : Fin n → ℝ => dkwWalk σ s j) :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

private lemma measurable_dkwMax (σ : Equiv.Perm (Fin n)) :
    Measurable (dkwMax σ) :=
  Measurable.iSup fun j => (measurable_dkwWalk σ (j : ℕ)).abs

private lemma dkwWalk_le_dkwMax (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) {j : ℕ}
    (hj : j ≤ n) : |dkwWalk σ s j| ≤ dkwMax σ s := by
  refine le_ciSup (f := fun j : Fin (n + 1) => |dkwWalk σ s (j : ℕ)|) ?_ ⟨j, by omega⟩
  exact (Set.finite_range _).bddAbove

private lemma dkwMax_nonneg (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    0 ≤ dkwMax σ s :=
  le_trans (abs_nonneg _) (dkwWalk_le_dkwMax σ s (Nat.zero_le n))

private lemma exists_dkwMax_eq (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    ∃ j : Fin (n + 1), dkwMax σ s = |dkwWalk σ s (j : ℕ)| := by
  obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j : Fin (n + 1) => |dkwWalk σ s (j : ℕ)|)
  refine ⟨j0, le_antisymm (ciSup_le hj0) ?_⟩
  exact dkwWalk_le_dkwMax σ s (Nat.lt_succ_iff.mp j0.isLt)

/-! ### The reflected sign pattern -/

private noncomputable def dkwSign (σ : Equiv.Perm (Fin n)) (j : ℕ) : Fin n → ℝ :=
  fun i => if i ∈ dkwPre σ j then 1 else -1

private lemma dkwSign_pm (σ : Equiv.Perm (Fin n)) (j : ℕ) (i : Fin n) :
    dkwSign σ j i = 1 ∨ dkwSign σ j i = -1 := by
  unfold dkwSign; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma dkwWalk_refl_le (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) {j l : ℕ}
    (hl : l ≤ j) :
    dkwWalk σ (fun i => dkwSign σ j i * s i) l = dkwWalk σ s l := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have : i ∈ dkwPre σ j := dkwPre_mono σ hl hi
  simp [dkwSign, this]

private lemma dkwWalk_refl_full (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (j : ℕ) :
    dkwWalk σ (fun i => dkwSign σ j i * s i) n
      = 2 * dkwWalk σ s j - dkwWalk σ s n := by
  have hj : dkwPre σ j ⊆ dkwPre σ n := by rw [dkwPre_full]; exact Finset.subset_univ _
  have hsplit : ∑ i ∈ dkwPre σ n, dkwSign σ j i * s i
      = ∑ i ∈ dkwPre σ n \ dkwPre σ j, dkwSign σ j i * s i
        + ∑ i ∈ dkwPre σ j, dkwSign σ j i * s i :=
    (Finset.sum_sdiff hj).symm
  have h1 : ∑ i ∈ dkwPre σ j, dkwSign σ j i * s i = dkwWalk σ s j :=
    Finset.sum_congr rfl fun i hi => by simp [dkwSign, hi]
  have hsub : dkwWalk σ s n - dkwWalk σ s j = ∑ i ∈ dkwPre σ n \ dkwPre σ j, s i := by
    simp only [dkwWalk]
    exact (Finset.sum_sdiff_eq_sub hj).symm
  have h2 : ∑ i ∈ dkwPre σ n \ dkwPre σ j, dkwSign σ j i * s i
      = -(dkwWalk σ s n - dkwWalk σ s j) := by
    rw [hsub, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i ∉ dkwPre σ j := (Finset.mem_sdiff.mp hi).2
    simp [dkwSign, this]
  simp only [dkwWalk] at hsplit h1 h2 ⊢
  rw [hsplit, h1, h2]
  ring



namespace Levy

variable (σ : Equiv.Perm (Fin n))

/-- The first-passage level sets of the walk. -/
private def dkwPass (a : ℝ) (j : ℕ) : Set (Fin n → ℝ) :=
  {s | ∀ l < j, |dkwWalk σ s l| < a} ∩ {s | a ≤ |dkwWalk σ s j|}

private lemma measurableSet_dkwPass (a : ℝ) (j : ℕ) :
    MeasurableSet (dkwPass σ a j) := by
  have h1 : {s : Fin n → ℝ | ∀ l < j, |dkwWalk σ s l| < a}
      = ⋂ l ∈ (Set.Iio j : Set ℕ), {s : Fin n → ℝ | |dkwWalk σ s l| < a} := by
    ext s; simp [Set.mem_iInter]
  rw [dkwPass, h1]
  refine MeasurableSet.inter (MeasurableSet.biInter (Set.to_countable _) fun l _ => ?_) ?_
  · exact measurableSet_lt (measurable_dkwWalk σ l).abs measurable_const
  · exact measurableSet_le measurable_const (measurable_dkwWalk σ j).abs

private lemma dkwPass_disjoint (a : ℝ) :
    ((Finset.range (n + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (dkwPass σ a) := by
  intro j _ j' _ hne
  refine Set.disjoint_left.mpr fun s hs hs' => ?_
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hs.2 (not_le.mpr (hs'.1 j h))
  · exact absurd hs'.2 (not_le.mpr (hs.1 j' h))

private lemma dkwMax_subset_iUnion {a : ℝ} :
    {s : Fin n → ℝ | a ≤ dkwMax σ s} ⊆ ⋃ j ∈ Finset.range (n + 1), dkwPass σ a j := by
  intro s hs
  obtain ⟨j0, hj0⟩ := exists_dkwMax_eq σ s
  have hex : ∃ l, a ≤ |dkwWalk σ s l| := ⟨(j0 : ℕ), hj0 ▸ hs⟩
  classical
  set j := Nat.find hex with hjdef
  have hjspec : a ≤ |dkwWalk σ s j| := Nat.find_spec hex
  have hjle : j ≤ n := le_trans (Nat.find_le (hj0 ▸ hs)) (Nat.lt_succ_iff.mp j0.isLt)
  refine Set.mem_biUnion (Finset.mem_range.mpr (by omega)) ⟨fun l hl => ?_, hjspec⟩
  exact not_le.mp (Nat.find_min hex hl)

private lemma signVec_dkwPass_le (a : ℝ) (_ha : 0 < a) (j : ℕ) :
    signVec n (dkwPass σ a j)
      ≤ 2 * signVec n (dkwPass σ a j ∩ {s | a ≤ |dkwWalk σ s n|}) := by
  classical
  set R : (Fin n → ℝ) → (Fin n → ℝ) := fun s i => dkwSign σ j i * s i with hR
  have hRmeas : Measurable R :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul _
  have hmap : (signVec n).map R = signVec n := signVec_map_mul_pm (dkwSign_pm σ j)
  set B : Set (Fin n → ℝ) := {s | a ≤ |dkwWalk σ s n|} with hB
  have hBmeas : MeasurableSet B := measurableSet_le measurable_const (measurable_dkwWalk σ n).abs
  have hSmeas : MeasurableSet (dkwPass σ a j ∩ B) :=
    (measurableSet_dkwPass σ a j).inter hBmeas
  -- the reflection preserves the measure of the target set
  have hpre : signVec n (R ⁻¹' (dkwPass σ a j ∩ B)) = signVec n (dkwPass σ a j ∩ B) := by
    conv_rhs => rw [← hmap]
    rw [Measure.map_apply hRmeas hSmeas]
  -- coverage
  have hcover : dkwPass σ a j ⊆ (dkwPass σ a j ∩ B) ∪ (R ⁻¹' (dkwPass σ a j ∩ B)) := by
    intro s hs
    by_cases hb : a ≤ |dkwWalk σ s n|
    · exact Or.inl ⟨hs, hb⟩
    · push Not at hb
      refine Or.inr ⟨⟨fun l hl => ?_, ?_⟩, ?_⟩
      · change |dkwWalk σ (fun i => dkwSign σ j i * s i) l| < a
        rw [dkwWalk_refl_le σ s (le_of_lt hl)]; exact hs.1 l hl
      · change a ≤ |dkwWalk σ (fun i => dkwSign σ j i * s i) j|
        rw [dkwWalk_refl_le σ s (le_refl j)]; exact hs.2
      · change a ≤ |dkwWalk σ (fun i => dkwSign σ j i * s i) n|
        rw [dkwWalk_refl_full σ s j]
        have h1 : a ≤ |dkwWalk σ s j| := hs.2
        have h2 : |2 * dkwWalk σ s j - dkwWalk σ s n|
            ≥ 2 * |dkwWalk σ s j| - |dkwWalk σ s n| := by
          have := abs_sub_abs_le_abs_sub (2 * dkwWalk σ s j) (dkwWalk σ s n)
          rw [abs_mul] at this
          simp only [abs_two] at this
          linarith
        linarith
  calc signVec n (dkwPass σ a j)
      ≤ signVec n ((dkwPass σ a j ∩ B) ∪ (R ⁻¹' (dkwPass σ a j ∩ B))) := measure_mono hcover
    _ ≤ signVec n (dkwPass σ a j ∩ B) + signVec n (R ⁻¹' (dkwPass σ a j ∩ B)) :=
        measure_union_le _ _
    _ = 2 * signVec n (dkwPass σ a j ∩ B) := by rw [hpre]; ring

/-- **Lévy's maximal inequality for the `±1` walk.** -/
private lemma dkw_levy {a : ℝ} (ha : 0 < a) :
    signVec n {s | a ≤ dkwMax σ s} ≤ 2 * signVec n {s | a ≤ |dkwWalk σ s n|} := by
  classical
  set B : Set (Fin n → ℝ) := {s | a ≤ |dkwWalk σ s n|} with hB
  have hBmeas : MeasurableSet B := measurableSet_le measurable_const (measurable_dkwWalk σ n).abs
  have hdisj : ((Finset.range (n + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun j => dkwPass σ a j ∩ B) := fun j hj j' hj' hne =>
    Disjoint.mono Set.inter_subset_left Set.inter_subset_left
      (dkwPass_disjoint σ a hj hj' hne)
  calc signVec n {s : Fin n → ℝ | a ≤ dkwMax σ s}
      ≤ signVec n (⋃ j ∈ Finset.range (n + 1), dkwPass σ a j) :=
        measure_mono (dkwMax_subset_iUnion σ)
    _ ≤ ∑ j ∈ Finset.range (n + 1), signVec n (dkwPass σ a j) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), 2 * signVec n (dkwPass σ a j ∩ B) :=
        Finset.sum_le_sum fun j _ => signVec_dkwPass_le σ a ha j
    _ = 2 * ∑ j ∈ Finset.range (n + 1), signVec n (dkwPass σ a j ∩ B) := by
        rw [Finset.mul_sum]
    _ = 2 * signVec n (⋃ j ∈ Finset.range (n + 1), (dkwPass σ a j ∩ B)) := by
        rw [measure_biUnion_finset hdisj
          (fun j _ => (measurableSet_dkwPass σ a j).inter hBmeas)]
    _ ≤ 2 * signVec n B := by
        refine mul_le_mul_of_nonneg_left (measure_mono ?_) (by positivity)
        exact Set.iUnion₂_subset fun j _ => Set.inter_subset_right

end Levy


section Moments

variable (σ : Equiv.Perm (Fin n))

private lemma signVec_ae_abs_le : ∀ᵐ s ∂signVec n, ∀ i, |s i| ≤ 1 := by
  filter_upwards [signVec_ae_pm n] with s hs i
  rcases hs i with h | h <;> simp [h]

private lemma dkwWalk_abs_le {s : Fin n → ℝ} (hs : ∀ i, |s i| ≤ 1) (j : ℕ) :
    |dkwWalk σ s j| ≤ n := by
  calc |dkwWalk σ s j| ≤ ∑ i ∈ dkwPre σ j, |s i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ dkwPre σ j, (1 : ℝ) := Finset.sum_le_sum fun i _ => hs i
    _ = ((dkwPre σ j).card : ℝ) := by simp
    _ ≤ (n : ℝ) := by
        have := Finset.card_le_univ (dkwPre σ j)
        simp only [Fintype.card_fin] at this
        exact_mod_cast this

private lemma dkwMax_abs_le {s : Fin n → ℝ} (hs : ∀ i, |s i| ≤ 1) :
    dkwMax σ s ≤ n := by
  obtain ⟨j, hj⟩ := exists_dkwMax_eq σ s
  rw [hj]; exact dkwWalk_abs_le σ hs _

private lemma integrable_dkwMax : Integrable (dkwMax σ) (signVec n) := by
  refine Integrable.mono' (integrable_const (n : ℝ))
    (measurable_dkwMax σ).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (dkwMax_nonneg σ s)]
  exact dkwMax_abs_le σ hs

private lemma integrable_dkwWalk (j : ℕ) :
    Integrable (fun s => dkwWalk σ s j) (signVec n) := by
  refine Integrable.mono' (integrable_const (n : ℝ))
    (measurable_dkwWalk σ j).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs]
  exact dkwWalk_abs_le σ hs j

private lemma integrable_dkwWalk_sq (j : ℕ) :
    Integrable (fun s => dkwWalk σ s j ^ 2) (signVec n) := by
  refine Integrable.mono' (integrable_const ((n : ℝ) ^ 2))
    ((measurable_dkwWalk σ j).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : |dkwWalk σ s j| ≤ (n : ℝ) := dkwWalk_abs_le σ hs j
  have h0 : (0 : ℝ) ≤ |dkwWalk σ s j| := abs_nonneg _
  have h2 : dkwWalk σ s j ^ 2 = |dkwWalk σ s j| ^ 2 := (sq_abs _).symm
  rw [h2]
  nlinarith

/-! Coordinate moments of the sign vector. -/

private lemma integral_coord (i : Fin n) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ s, f (s i) ∂signVec n = ∫ x, f x ∂radLaw := by
  have hmp := measurePreserving_eval_signVec n i
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]

private lemma integrable_coord (i : Fin n) :
    Integrable (fun s : Fin n → ℝ => s i) (signVec n) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_pi_apply i).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs]; exact hs i

private lemma integrable_coord_mul (i j : Fin n) :
    Integrable (fun s : Fin n → ℝ => s i * s j) (signVec n) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_pi_apply i).mul (measurable_pi_apply j))).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hs i
  have h2 := hs j
  nlinarith [abs_nonneg (s i), abs_nonneg (s j)]

private lemma integral_coord_id (i : Fin n) : ∫ s : Fin n → ℝ, s i ∂signVec n = 0 := by
  have h := integral_coord (n := n) i (f := fun x => x) measurable_id
  rw [h]; exact radLaw_integral_id

private lemma integral_coord_sq (i : Fin n) :
    ∫ s : Fin n → ℝ, s i * s i ∂signVec n = 1 := by
  have h := integral_coord (n := n) i (f := fun x => x * x)
    (measurable_id.mul measurable_id)
  rw [h, radLaw_integral]; norm_num

private lemma integral_coord_cross {i j : Fin n} (hij : i ≠ j) :
    ∫ s : Fin n → ℝ, s i * s j ∂signVec n = 0 := by
  have hind : IndepFun (fun s : Fin n → ℝ => s i) (fun s : Fin n → ℝ => s j) (signVec n) :=
    (iIndepFun_eval_signVec n).indepFun hij
  rw [hind.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable]
  change (∫ s : Fin n → ℝ, s i ∂signVec n) * (∫ s : Fin n → ℝ, s j ∂signVec n) = 0
  rw [integral_coord_id, zero_mul]

private lemma integral_dkwWalk_sq_full :
    ∫ s, dkwWalk σ s n ^ 2 ∂signVec n = n := by
  classical
  have hW : (fun s : Fin n → ℝ => dkwWalk σ s n ^ 2)
      = fun s : Fin n → ℝ => ∑ i, ∑ j, s i * s j := by
    funext s
    simp only [dkwWalk, dkwPre_full]
    rw [sq, Finset.sum_mul_sum]
  rw [hW]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => integrable_coord_mul i j))]
  have hrow : ∀ i : Fin n, ∫ s : Fin n → ℝ, ∑ j, s i * s j ∂signVec n = 1 := by
    intro i
    rw [integral_finsetSum _ (fun j _ => integrable_coord_mul i j)]
    rw [Finset.sum_eq_single i (fun j _ hji => integral_coord_cross (Ne.symm hji))
      (fun h => absurd (Finset.mem_univ i) h)]
    exact integral_coord_sq i
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  simp

private lemma integral_abs_dkwWalk_le (hn : 0 < n) :
    ∫ s, |dkwWalk σ s n| ∂signVec n ≤ Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hss : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have hpt : ∀ s : Fin n → ℝ,
      |dkwWalk σ s n| ≤ (dkwWalk σ s n ^ 2 + (n : ℝ)) / (2 * Real.sqrt n) := by
    intro s
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|dkwWalk σ s n| - Real.sqrt n), sq_abs (dkwWalk σ s n)]
  have hint2 : Integrable (fun s : Fin n → ℝ =>
      (dkwWalk σ s n ^ 2 + (n : ℝ)) / (2 * Real.sqrt n)) (signVec n) :=
    ((integrable_dkwWalk_sq σ n).add (integrable_const _)).div_const _
  calc ∫ s, |dkwWalk σ s n| ∂signVec n
      ≤ ∫ s, (dkwWalk σ s n ^ 2 + (n : ℝ)) / (2 * Real.sqrt n) ∂signVec n :=
        integral_mono ((integrable_dkwWalk σ n).abs) hint2 hpt
    _ = ((∫ s, dkwWalk σ s n ^ 2 ∂signVec n) + (n : ℝ)) / (2 * Real.sqrt n) := by
        rw [integral_div, integral_add (integrable_dkwWalk_sq σ n) (integrable_const _)]
        simp
    _ = Real.sqrt n := by
        rw [integral_dkwWalk_sq_full σ]
        field_simp
        nlinarith [hss]

/-- **The `L¹` maximal bound**: `E max_j |S_j| ≤ 2 √n`. -/
private lemma integral_dkwMax_le (hn : 0 < n) :
    ∫ s, dkwMax σ s ∂signVec n ≤ 2 * Real.sqrt n := by
  have hAbsInt : Integrable (fun s => |dkwWalk σ s n|) (signVec n) :=
    (integrable_dkwWalk σ n).abs
  -- layer cake in `ℝ≥0∞`
  have hlc1 : ∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n
      = ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ dkwMax σ s} :=
    lintegral_eq_lintegral_meas_le _
      (Filter.Eventually.of_forall (dkwMax_nonneg σ)) (measurable_dkwMax σ).aemeasurable
  have hlc2 : ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n
      = ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ |dkwWalk σ s n|} :=
    lintegral_eq_lintegral_meas_le _
      (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (measurable_dkwWalk σ n).abs.aemeasurable
  have hmono : ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ dkwMax σ s}
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), 2 * signVec n {s | t ≤ |dkwWalk σ s n|} := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact Levy.dkw_levy σ ht
  have hconst : ∫⁻ t in Set.Ioi (0 : ℝ), 2 * signVec n {s | t ≤ |dkwWalk σ s n|}
      = 2 * ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ |dkwWalk σ s n|} :=
    lintegral_const_mul' _ _ (by simp)
  have hkey : ∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n
      ≤ 2 * ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n := by
    rw [hlc1, hlc2]; exact hmono.trans_eq hconst
  -- transfer to the Bochner integral
  have hfin : ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n ≠ ⊤ := by
    have h := hAbsInt.hasFiniteIntegral
    have heq : ∀ s : Fin n → ℝ, ENNReal.ofReal |dkwWalk σ s n| = ‖|dkwWalk σ s n|‖ₑ :=
      fun s => (Real.enorm_eq_ofReal (abs_nonneg _)).symm
    simp_rw [heq]
    exact h.ne
  have he1 : ∫ s, dkwMax σ s ∂signVec n
      = (∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (dkwMax_nonneg σ))
      (measurable_dkwMax σ).aestronglyMeasurable
  have he2 : ∫ s, |dkwWalk σ s n| ∂signVec n
      = (∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (measurable_dkwWalk σ n).abs.aestronglyMeasurable
  calc ∫ s, dkwMax σ s ∂signVec n
      = (∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n).toReal := he1
    _ ≤ (2 * ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n).toReal := by
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) hkey
    _ = 2 * ∫ s, |dkwWalk σ s n| ∂signVec n := by
        rw [he2, ENNReal.toReal_mul]; norm_num
    _ ≤ 2 * Real.sqrt n := by
        have := integral_abs_dkwWalk_le σ hn
        linarith

end Moments

/-! ### The sorted-prefix representation -/

section Sorting

/-- For a monotone tuple, the sublevel set at `c` is the initial segment of length
`#{l | y l ≤ c}`. -/
private lemma monotone_le_iff_lt_card {y : Fin n → ℝ} (hy : Monotone y) (c : ℝ) (l : Fin n) :
    y l ≤ c ↔ (l : ℕ) < (Finset.univ.filter (fun l : Fin n => y l ≤ c)).card := by
  classical
  set T : Finset (Fin n) := Finset.univ.filter (fun l : Fin n => y l ≤ c) with hT
  have hmemT : ∀ l' : Fin n, l' ∈ T ↔ y l' ≤ c := by intro l'; simp [hT]
  constructor
  · intro hl
    have hsub : Finset.Iic l ⊆ T := fun l' hl' =>
      (hmemT l').mpr (le_trans (hy (Finset.mem_Iic.mp hl')) hl)
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hl
    by_contra hnot
    have hsub : T ⊆ Finset.Iio l := by
      intro l' hl'
      rw [Finset.mem_Iio]
      by_contra hge
      exact hnot (le_trans (hy (not_lt.mp hge)) ((hmemT l').mp hl'))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

/-- For every threshold `c`, the set of sample indices below `c` is a prefix of the
sorted order, so the signed count is a value of the `±1` walk. -/
private lemma exists_dkwWalk_eq (x : Fin n → ℝ) (s : Fin n → ℝ) (c : ℝ) :
    ∃ j ≤ n, ∑ i, s i * (if x i ≤ c then (1 : ℝ) else 0)
      = dkwWalk (Tuple.sort x) s j := by
  classical
  set σ : Equiv.Perm (Fin n) := Tuple.sort x with hσ
  have hy : Monotone (x ∘ σ) := Tuple.monotone_sort x
  set T : Finset (Fin n) := Finset.univ.filter (fun l : Fin n => (x ∘ σ) l ≤ c) with hT
  refine ⟨T.card, le_trans (Finset.card_le_univ T) (by simp), ?_⟩
  have hsum : ∑ i, s i * (if x i ≤ c then (1 : ℝ) else 0)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin n => x i ≤ c), s i := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hset : Finset.univ.filter (fun i : Fin n => x i ≤ c) = dkwPre σ T.card := by
    ext i
    simp only [dkwPre, Finset.mem_filter, Finset.mem_univ, true_and]
    have hpt := monotone_le_iff_lt_card hy c (σ.symm i)
    rw [← hT] at hpt
    simpa [Function.comp_def] using hpt
  rw [hsum, hset]
  rfl

private lemma abs_signed_count_le_dkwMax (x : Fin n → ℝ) (s : Fin n → ℝ) (c : ℝ) :
    |∑ i, s i * (if x i ≤ c then (1 : ℝ) else 0)| ≤ dkwMax (Tuple.sort x) s := by
  obtain ⟨j, hj, hval⟩ := exists_dkwWalk_eq x s c
  rw [hval]
  exact dkwWalk_le_dkwMax _ s hj

end Sorting

/-! ### The conditional sign integral -/

section SignIntegral

private lemma measurable_signSup (x : Fin n → ℝ) :
    Measurable (fun s : Fin n → ℝ =>
      ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|) := by
  refine Measurable.iSup fun q => Measurable.abs (Measurable.const_mul ?_ _)
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul measurable_const

private lemma signSup_le (x : Fin n → ℝ) (s : Fin n → ℝ) :
    (⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|)
      ≤ (n : ℝ)⁻¹ * dkwMax (Tuple.sort x) s := by
  refine ciSup_le fun q => ?_
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (abs_signed_count_le_dkwMax x s _) (by positivity)

private lemma signSup_bddAbove (x : Fin n → ℝ) (s : Fin n → ℝ) :
    BddAbove (Set.range fun q : ℚ =>
      |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|) := by
  refine ⟨(n : ℝ)⁻¹ * dkwMax (Tuple.sort x) s, ?_⟩
  rintro y ⟨q, rfl⟩
  dsimp only
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (abs_signed_count_le_dkwMax x s _) (by positivity)

private lemma signSup_nonneg (x : Fin n → ℝ) (s : Fin n → ℝ) :
    0 ≤ ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)| :=
  le_ciSup_of_le (signSup_bddAbove x s) 0 (abs_nonneg _)

/-- **The conditional sign bound**: for every realisation `x` of the sample,
`E_ε sup_q |n⁻¹ ∑ᵢ εᵢ 1{xᵢ ≤ q}| ≤ 2/√n`. -/
private lemma integral_signSup_le (hn : 0 < n) (x : Fin n → ℝ) :
    ∫ s, (⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|)
        ∂signVec n ≤ 2 / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hss : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  set σ : Equiv.Perm (Fin n) := Tuple.sort x with hσ
  have hdom : Integrable (fun s => (n : ℝ)⁻¹ * dkwMax σ s) (signVec n) :=
    (integrable_dkwMax σ).const_mul _
  have hint : Integrable (fun s : Fin n → ℝ =>
      ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|)
      (signVec n) := by
    refine Integrable.mono' hdom (measurable_signSup x).aestronglyMeasurable ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (signSup_nonneg x s)]
    exact signSup_le x s
  calc ∫ s, (⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|)
        ∂signVec n
      ≤ ∫ s, (n : ℝ)⁻¹ * dkwMax σ s ∂signVec n :=
        integral_mono hint hdom (fun s => signSup_le x s)
    _ = (n : ℝ)⁻¹ * ∫ s, dkwMax σ s ∂signVec n := integral_const_mul _ _
    _ ≤ (n : ℝ)⁻¹ * (2 * Real.sqrt n) := by
        exact mul_le_mul_of_nonneg_left (integral_dkwMax_le σ hn) (by positivity)
    _ = 2 / Real.sqrt n := by
        field_simp
        nlinarith [hss]

end SignIntegral

end SignWalk

open OTSelector.Probability.Symmetrization in
/-- **Mean of the Kolmogorov distance.** For an i.i.d. sample of size `n ≥ 1`,
`√n · E Dₙ ≤ 4`, uniformly in the sampling law.

Proved by symmetrisation (`empirical_symmetrization_countable`), the sorted-prefix walk
representation of the Rademacher process over half-lines, and Lévy's maximal inequality
plus the layer-cake formula (`integral_dkwMax_le`).  See the file header for why the
constant is `4` and not the sharp `0.87…`. -/
theorem integral_ksDist_le {n : ℕ}
    (hn : 0 < n) (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = μ) :
    ∫ ω, ksDist X μ ω ∂P ≤ 4 / Real.sqrt n := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  set F : ℚ → ℝ → ℝ := fun q x => if x ≤ (q : ℝ) then (1 : ℝ) else 0 with hFdef
  have hFmeas : ∀ q, Measurable (F q) := fun q =>
    Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  have hFbdd : ∀ q x, |F q x| ≤ 1 := by
    intro q x; simp only [hFdef]; split_ifs <;> norm_num
  have hFmean : ∀ q : ℚ, ∫ x, F q x ∂μ = cdf μ (q : ℝ) := by
    intro q
    have hind : F q = Set.indicator (Set.Iic ((q : ℝ))) (fun _ => (1 : ℝ)) := by
      funext x
      simp [hFdef, Set.indicator_apply, Set.mem_Iic]
    rw [hind, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one,
      cdf_eq_real]
  -- Step 1: symmetrisation over the countable class of half-lines.
  have hsym := OTSelector.Probability.Symmetrization.empirical_symmetrization_countable
    (μ := P) (P := μ) (X := X) (F := F) hmeas hindep hlaw hFmeas hFbdd
  -- Step 2: the left-hand side is the mean Kolmogorov distance.
  have hLHS : ∫ ω, ⨆ q : ℚ, |(n : ℝ)⁻¹ * (∑ i, F q (X i ω)) - ∫ x, F q x ∂μ| ∂P
      = ∫ ω, ksDist X μ ω ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hrat : ksDist X μ ω = ⨆ q : ℚ, |empCDF X ω (q : ℝ) - cdf μ (q : ℝ)| := by
      refine dkw_iSup_real_eq_iSup_rat (fun t => |empCDF X ω t - cdf μ t|) fun s => ?_
      have hempRC : Tendsto (fun t => empCDF X ω t) (nhdsWithin s (Set.Ioi s))
          (nhds (empCDF X ω s)) := by
        simp only [empCDF]
        exact (tendsto_finsetSum Finset.univ
          fun i _ => dkw_rightCont_step (X i ω) s).const_mul _
      have hcdfRC : Tendsto (fun t => cdf μ t) (nhdsWithin s (Set.Ioi s)) (nhds (cdf μ s)) :=
        ((cdf μ).right_continuous s).mono Set.Ioi_subset_Ici_self
      exact Filter.Tendsto.abs (hempRC.sub hcdfRC)
    rw [hrat]
    refine iSup_congr fun q => ?_
    rw [hFmean q]
    rfl
  -- Step 3: Fubini on the product with the sign randomisation.
  set G : Ω × (Fin n → ℝ) → ℝ :=
    fun p => ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F q (X i p.1)| with hGdef
  have hGmeas : Measurable G := by
    refine Measurable.iSup fun q => Measurable.abs (Measurable.const_mul ?_ _)
    refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
    · exact (measurable_pi_apply i).comp measurable_snd
    · exact (hFmeas q).comp ((hmeas i).comp measurable_fst)
  have hGbdd : ∀ p : Ω × (Fin n → ℝ), (∀ i, |p.2 i| ≤ 1) → |G p| ≤ 1 := by
    intro p hp
    have hb : ∀ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F q (X i p.1)| ≤ 1 := by
      intro q
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      have h1 : |∑ i, p.2 i * F q (X i p.1)| ≤ (n : ℝ) := by
        calc |∑ i, p.2 i * F q (X i p.1)| ≤ ∑ i, |p.2 i * F q (X i p.1)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul]
              exact mul_le_one₀ (hp i) (abs_nonneg _) (hFbdd q _)
          _ = (n : ℝ) := by simp
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [inv_mul_le_iff₀ hn0]
      linarith
    have hbdd : BddAbove (Set.range fun q : ℚ => |(n : ℝ)⁻¹ * ∑ i, p.2 i * F q (X i p.1)|) :=
      ⟨1, by rintro y ⟨q, rfl⟩; exact hb q⟩
    rw [abs_of_nonneg (le_ciSup_of_le hbdd 0 (abs_nonneg _))]
    exact ciSup_le hb
  have hae : ∀ᵐ p ∂(P.prod (signVec n)), ∀ i, |p.2 i| ≤ 1 :=
    (Measure.quasiMeasurePreserving_snd).ae (signVec_ae_abs_le (n := n))
  have hGint : Integrable G (P.prod (signVec n)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hGmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs]
    exact hGbdd p hp
  have hfub : ∫ p, G p ∂(P.prod (signVec n)) = ∫ ω, ∫ s, G (ω, s) ∂signVec n ∂P :=
    integral_prod G hGint
  -- Step 4: the conditional sign bound, uniformly in the sample.
  have hinner : ∀ ω, ∫ s, G (ω, s) ∂signVec n ≤ 2 / Real.sqrt n := by
    intro ω
    have := integral_signSup_le (n := n) hn (fun i => X i ω)
    simpa [hGdef, hFdef] using this
  have hGnonneg : ∀ p : Ω × (Fin n → ℝ), 0 ≤ G p := by
    intro p
    refine le_ciSup_of_le ⟨(n : ℝ)⁻¹ * ∑ i, |p.2 i|, ?_⟩ 0 (abs_nonneg _)
    rintro y ⟨q, rfl⟩
    dsimp only
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |∑ i, p.2 i * F q (X i p.1)| ≤ ∑ i, |p.2 i * F q (X i p.1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |p.2 i| := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hFbdd q _)
  have hinner0 : ∀ ω, 0 ≤ ∫ s, G (ω, s) ∂signVec n :=
    fun ω => integral_nonneg fun s => hGnonneg (ω, s)
  have hRHS : ∫ p, G p ∂(P.prod (signVec n)) ≤ 2 / Real.sqrt n := by
    rw [hfub]
    calc ∫ ω, ∫ s, G (ω, s) ∂signVec n ∂P
        ≤ ∫ _ω, 2 / Real.sqrt n ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hinner0)
            (integrable_const _) (Filter.Eventually.of_forall hinner)
      _ = 2 / Real.sqrt n := by simp
  -- Assemble.
  rw [← hLHS]
  calc ∫ ω, ⨆ q : ℚ, |(n : ℝ)⁻¹ * (∑ i, F q (X i ω)) - ∫ x, F q x ∂μ| ∂P
      ≤ 2 * ∫ p, ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F q (X i p.1)|
          ∂(P.prod (signVec n)) := hsym
    _ = 2 * ∫ p, G p ∂(P.prod (signVec n)) := rfl
    _ ≤ 2 * (2 / Real.sqrt n) := by linarith [hRHS]
    _ = 4 / Real.sqrt n := by ring

/-- Markov's inequality combined with `integral_ksDist_le`. -/
theorem ksDist_tail_markov {n : ℕ} (hn : 0 < n) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ ksDist X μ ω} ≤ 4 / (ε * Real.sqrt n) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := ksDist X μ)
    (Filter.Eventually.of_forall fun ω ↦ ksDist_nonneg hn X μ ω)
    (integrable_ksDist hn X μ hmeas) ε
  calc
    P.real {ω | ε ≤ ksDist X μ ω}
        ≤ (∫ ω, ksDist X μ ω ∂P) / ε := by
          rw [le_div_iff₀ hε]
          simpa [mul_comm] using hmarkov
    _ ≤ (4 / Real.sqrt n) / ε :=
      div_le_div_of_nonneg_right (integral_ksDist_le hn μ X hmeas hindep hlaw) hε.le
    _ = 4 / (ε * Real.sqrt n) := by ring


end OTSelector.Probability.NestedCDF
