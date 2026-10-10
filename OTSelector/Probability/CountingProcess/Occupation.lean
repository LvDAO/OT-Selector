import OTSelector.Probability.CountingProcess.Closure
import OTSelector.Probability.CountingProcess.Exponential
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.NNRat.Encodable

/-!
# Predictable processes used by counting occupation bounds

This file supplies the predictable-process infrastructure needed for `lem:occupation` in
`main.tex`.  The exponential martingale and the resulting probability bounds are proved in
later modules.

The route is the classical exponential martingale `exp(-θ N + (1 - exp(-θ)) ∫ Λ)`.  The central
task is the path identity expressing this exponential as `1 + ∫ H dN - ∫ H Λ ds` for the bounded
predictable left-weight `H s = (e^{-θ} - 1) e^{-θ N(s-)} e^{(1-e^{-θ}) A(s)}`; bounded
predictability then feeds the closure theorem in `Closure.lean`.

Along the way this file develops two structural facts used to build the predictable mask:

* `stronglyMeasurable_countBefore`: the jump count strictly before `s` is strongly predictable
  for an adapted monotone counting path;
* `IsStronglyPredictable.of_continuous_adapted`: a continuous adapted real process is strongly
  predictable (dyadic left-continuous approximation by predictable simple steps).
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Jump counts strictly before a time -/

/-- The number of jumps of the counting path attained strictly before time `s`.  The filtration
index bound `N s ω + 1` keeps the count finite also on paths that are not monotone; on monotone
paths it is immaterial. -/
noncomputable def countBefore (N : ℝ≥0 → Ω → ℕ) (s : ℝ≥0) (ω : Ω) : ℕ := by
  classical
  exact ((Finset.range (N s ω + 1)).filter (fun k ↦ ∃ u : ℝ≥0, u < s ∧ k < N u ω)).card

omit [MeasurableSpace Ω] in
/-- On a monotone path, the count strictly before `s` exceeds `n` exactly when some time before
`s` already carries more than `n` attained jumps. -/
theorem countBefore_succ_le_iff {N : ℝ≥0 → Ω → ℕ} {s : ℝ≥0} {ω : Ω} {n : ℕ}
    (hmono : Monotone fun t ↦ N t ω) :
    n + 1 ≤ countBefore N s ω ↔ ∃ u : ℝ≥0, u < s ∧ n < N u ω := by
  classical
  let S : Finset ℕ :=
    (Finset.range (N s ω + 1)).filter (fun k ↦ ∃ u : ℝ≥0, u < s ∧ k < N u ω)
  have hS_down : ∀ ⦃k m⦄, k ∈ S → m < k → m ∈ S := by
    intro k m hk hm
    rcases (Finset.mem_filter.mp hk).2 with ⟨u, hus, hku⟩
    refine Finset.mem_filter.mpr ⟨?_, ⟨u, hus, Nat.lt_trans hm hku⟩⟩
    apply Finset.mem_range.mpr
    exact Nat.lt_of_lt_of_le (Nat.lt_trans hm hku) (Nat.le.step (hmono hus.le))
  constructor
  · intro h
    by_contra hnS
    -- `hnS : ¬ ∃ u : ℝ≥0, u < s ∧ n < N u ω`
    have hsub : S ⊆ Finset.range n := by
      intro k hk
      apply Finset.mem_range.mpr
      by_contra hnk
      rcases (Finset.mem_filter.mp hk).2 with ⟨u, hus, hku⟩
      exact hnS ⟨u, hus, Nat.lt_of_le_of_lt (Nat.le_of_not_gt hnk) hku⟩
    have hcard : countBefore N s ω ≤ n := by
      rw [countBefore]
      exact (Finset.card_le_card hsub).trans_eq (Finset.card_range n)
    omega
  · rintro ⟨u, hus, hnu⟩
    have hnS : n ∈ S := by
      refine Finset.mem_filter.mpr ⟨?_, ⟨u, hus, hnu⟩⟩
      apply Finset.mem_range.mpr
      exact Nat.lt_of_lt_of_le hnu (Nat.le.step (hmono hus.le))
    have hsub : Finset.range (n + 1) ⊆ S := by
      intro k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) with hlt | heq
      · exact hS_down hnS hlt
      · subst heq
        exact hnS
    rw [countBefore]
    exact (Finset.card_range (n + 1)).symm.trans_le (Finset.card_le_card hsub)

omit [MeasurableSpace Ω] in
/-- The event `{n + 1 ≤ countBefore}` is the union over nonnegative rationals `q` of the
predictable cylinders `(q, ∞) × {n < N q}`. -/
theorem countBefore_ge_set_eq {N : ℝ≥0 → Ω → ℕ} {n : ℕ}
    (hmono : ∀ ω, Monotone fun t ↦ N t ω) :
    {z : ℝ≥0 × Ω | n + 1 ≤ countBefore N z.1 z.2} =
      ⋃ q : ℚ≥0, Ioi ((q : ℝ≥0)) ×ˢ {ω : Ω | n < N ((q : ℝ≥0)) ω} := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_ofPred_eq] at hz
    rw [countBefore_succ_le_iff (hmono z.2)] at hz
    rcases hz with ⟨u, hus, hnu⟩
    have hu1 : (u : ℝ) < (z.1 : ℝ) := by exact_mod_cast hus
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hu1
    have hqnonneg : (0 : ℚ) ≤ q := by
      exact_mod_cast (le_trans (show (0 : ℝ) ≤ (u : ℝ) by exact u.2) (le_of_lt hq1))
    let q' : ℚ≥0 := ⟨q, hqnonneg⟩
    rw [Set.mem_iUnion]
    refine ⟨q', ?_, ?_⟩
    · -- z.1 ∈ Ioi (q' : ℝ≥0)
      change (q' : ℝ≥0) < z.1
      change ((q' : ℝ≥0) : ℝ) < (z.1 : ℝ)
      exact_mod_cast hq2
    · refine Nat.lt_of_lt_of_le hnu ?_
      have hle : u ≤ (q' : ℝ≥0) := by
        change (u : ℝ) ≤ ((q' : ℝ≥0) : ℝ)
        exact_mod_cast (le_of_lt hq1)
      exact hmono z.2 hle
  · rw [Set.mem_iUnion]
    rintro ⟨q, hq1, hq2⟩
    change n + 1 ≤ countBefore N z.1 z.2
    rw [countBefore_succ_le_iff (hmono z.2)]
    exact ⟨(q : ℝ≥0), hq1, hq2⟩

omit [MeasurableSpace Ω] in
/-- The level set `{n + 1 ≤ countBefore}` is predictable for an adapted monotone counting
path. -/
theorem measurableSet_countBefore_ge {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {N : ℝ≥0 → Ω → ℕ} (hNadapt : StronglyAdapted ℱ (fun t ω ↦ (N t ω : ℝ)))
    (hmono : ∀ ω, Monotone fun t ↦ N t ω) (n : ℕ) :
    MeasurableSet[ℱ.predictable] {z : ℝ≥0 × Ω | n + 1 ≤ countBefore N z.1 z.2} := by
  rw [countBefore_ge_set_eq hmono]
  refine MeasurableSet.iUnion fun q ↦ ?_
  refine measurableSet_predictable_Ioi_prod (𝓕 := ℱ) (i := ((q : ℚ≥0) : ℝ≥0)) ?_
  have hset : {ω : Ω | n < N ((q : ℚ≥0) : ℝ≥0) ω} =
      (fun ω ↦ (N ((q : ℚ≥0) : ℝ≥0) ω : ℝ)) ⁻¹' Ioi (n : ℝ) := by
    ext ω
    simp
  rw [hset]
  exact (hNadapt ((q : ℚ≥0) : ℝ≥0)).measurable measurableSet_Ioi

omit [MeasurableSpace Ω] in
/-- The level set `{countBefore = n}` is predictable for an adapted monotone counting path. -/
theorem measurableSet_countBefore_eq {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {N : ℝ≥0 → Ω → ℕ} (hNadapt : StronglyAdapted ℱ (fun t ω ↦ (N t ω : ℝ)))
    (hmono : ∀ ω, Monotone fun t ↦ N t ω) (n : ℕ) :
    MeasurableSet[ℱ.predictable] {z : ℝ≥0 × Ω | countBefore N z.1 z.2 = n} := by
  rcases n with _ | k
  · have h0 : {z : ℝ≥0 × Ω | countBefore N z.1 z.2 = (0 : ℕ)} =
        ({z : ℝ≥0 × Ω | (0 : ℕ) + 1 ≤ countBefore N z.1 z.2})ᶜ := by
      ext z
      constructor <;> intro hz <;> simp at hz ⊢ <;> omega
    rw [h0]
    exact (measurableSet_countBefore_ge hNadapt hmono 0).compl
  · have hk : {z : ℝ≥0 × Ω | countBefore N z.1 z.2 = (k + 1 : ℕ)} =
        {z : ℝ≥0 × Ω | (k : ℕ) + 1 ≤ countBefore N z.1 z.2} ∩
          ({z : ℝ≥0 × Ω | (k + 1 : ℕ) + 1 ≤ countBefore N z.1 z.2})ᶜ := by
      ext z
      constructor <;> intro hz <;> simp at hz ⊢ <;> omega
    rw [hk]
    exact (measurableSet_countBefore_ge hNadapt hmono k).inter
      (measurableSet_countBefore_ge hNadapt hmono (k + 1)).compl

omit [MeasurableSpace Ω] in
/-- The real-valued cast of `countBefore` is strongly predictable. -/
theorem stronglyMeasurable_countBefore {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {N : ℝ≥0 → Ω → ℕ} (hNadapt : StronglyAdapted ℱ (fun t ω ↦ (N t ω : ℝ)))
    (hmono : ∀ ω, Monotone fun t ↦ N t ω) :
    StronglyMeasurable[ℱ.predictable] (fun z : ℝ≥0 × Ω ↦ (countBefore N z.1 z.2 : ℝ)) := by
  have hsm : Measurable[ℱ.predictable] (fun z : ℝ≥0 × Ω ↦ (countBefore N z.1 z.2 : ℝ)) := by
    intro B hB
    have hpre : (fun z : ℝ≥0 × Ω ↦ (countBefore N z.1 z.2 : ℝ)) ⁻¹' B =
        ⋃ n : {n : ℕ // (n : ℝ) ∈ B}, {z : ℝ≥0 × Ω | countBefore N z.1 z.2 = (n : ℕ)} := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_iUnion]
        refine ⟨⟨countBefore N z.1 z.2, hz⟩, rfl⟩
      · rw [Set.mem_iUnion]
        rintro ⟨n, hn⟩
        have hn' : countBefore N z.1 z.2 = (n : ℕ) := by simpa using hn
        change (countBefore N z.1 z.2 : ℝ) ∈ B
        rw [hn']
        exact n.2
    rw [hpre]
    refine MeasurableSet.iUnion fun n => ?_
    exact measurableSet_countBefore_eq hNadapt hmono (n : ℕ)
  exact hsm.stronglyMeasurable

/-! ## Continuous adapted processes are predictable -/

namespace MeasureTheory.IsStronglyPredictable

omit [MeasurableSpace Ω] in
/-- A continuous adapted real process is strongly predictable: its dyadic left-continuous
adaptation is a limit of predictable simple steps. -/
theorem of_continuous_adapted {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ}
    (hAdapted : ∀ t, StronglyMeasurable[ℱ t] (X t))
    (hCont : ∀ ω, Continuous (fun t ↦ X t ω)) :
    IsStronglyPredictable ℱ X := by
  -- On the dyadic cell `(j / 2ⁿ, (j + 1) / 2ⁿ]` the grid takes the value `j / 2ⁿ`; at `0` it
  -- takes the value `0`.
  let grid : ℕ → ℝ≥0 → ℝ≥0 := fun n t ↦
    (((Nat.ceil ((2 : ℝ≥0) ^ n * t)) - 1 : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ n)
  have h2pos : ∀ n : ℕ, (0 : ℝ≥0) < (2 : ℝ≥0) ^ n := fun n ↦
    pow_pos (by norm_num : (0 : ℝ≥0) < 2) n
  have h2ne : ∀ n : ℕ, (2 : ℝ≥0) ^ n ≠ 0 := fun n ↦ ne_of_gt (h2pos n)
  have ht0_of_hc0 : ∀ (n : ℕ) (t : ℝ≥0), Nat.ceil ((2 : ℝ≥0) ^ n * t) = 0 → t = 0 := by
    intro n t hc0
    have hle0 : (2 : ℝ≥0) ^ n * t ≤ 0 := by
      simpa using (Nat.ceil_le.mp hc0.le)
    have hmul0 : (2 : ℝ≥0) ^ n * t = 0 :=
      le_antisymm hle0 (mul_nonneg (le_of_lt (h2pos n)) t.2)
    have hreal : ((2 : ℝ≥0) ^ n : ℝ) * (t : ℝ) = 0 := by exact_mod_cast hmul0
    have htr : (t : ℝ) = 0 := (mul_eq_zero.mp hreal).resolve_left (by exact_mod_cast (h2ne n))
    exact NNReal.coe_eq_zero.mp htr
  -- Cell structure of the grid.
  have hgrid_cell : ∀ (n j : ℕ), j ≠ 0 →
      {t : ℝ≥0 | grid n t = (j : ℝ≥0) / (2 : ℝ≥0) ^ n} =
        Ioc ((j : ℝ≥0) / (2 : ℝ≥0) ^ n) (((j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) := by
    intro n j hj
    ext t
    constructor
    · intro ht
      have hmul := congrArg (fun x : ℝ≥0 => x * (2 : ℝ≥0) ^ n) ht
      have hjc : ((Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 : ℕ) : ℝ≥0) = (j : ℝ≥0) := by
        simpa [grid, div_mul_cancel₀ _ (h2ne n)] using hmul
      have hceilj : Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 = j := by exact_mod_cast hjc
      have hceil : Nat.ceil ((2 : ℝ≥0) ^ n * t) = j + 1 := by omega
      have hceileq := (Nat.ceil_eq_iff (R := ℝ≥0) (Nat.succ_ne_zero j)).mp hceil
      have hceileq' : (j : ℝ≥0) < (2 : ℝ≥0) ^ n * t ∧
          (2 : ℝ≥0) ^ n * t ≤ ((j + 1 : ℕ) : ℝ≥0) := by
        simpa [Nat.succ_sub_one] using hceileq
      constructor
      · have hlt' : (j : ℝ≥0) < t * (2 : ℝ≥0) ^ n := by
          simpa [mul_comm] using hceileq'.1
        exact (div_lt_iff₀ (h2pos n)).mpr hlt'
      · have hle' : t * (2 : ℝ≥0) ^ n ≤ ((j + 1 : ℕ) : ℝ≥0) := by
          simpa [mul_comm] using hceileq'.2
        exact (le_div_iff₀ (h2pos n)).mpr hle'
    · intro ht
      have hlt : (j : ℝ≥0) < (2 : ℝ≥0) ^ n * t := by
        have hlt' : (j : ℝ≥0) < t * (2 : ℝ≥0) ^ n :=
          (div_lt_iff₀ (h2pos n)).mp ht.1
        simpa [mul_comm] using hlt'
      have hle : (2 : ℝ≥0) ^ n * t ≤ ((j + 1 : ℕ) : ℝ≥0) := by
        have hle' : t * (2 : ℝ≥0) ^ n ≤ ((j + 1 : ℕ) : ℝ≥0) :=
          (le_div_iff₀ (h2pos n)).mp ht.2
        simpa [mul_comm] using hle'
      have hceil : Nat.ceil ((2 : ℝ≥0) ^ n * t) = j + 1 := by
        refine (Nat.ceil_eq_iff (R := ℝ≥0) (Nat.succ_ne_zero j)).mpr ?_
        constructor
        · simpa [Nat.succ_sub_one] using hlt
        · simpa using hle
      have hsub : Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 = j := by omega
      have hjc : ((Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 : ℕ) : ℝ≥0) = (j : ℝ≥0) := by
        exact_mod_cast hsub
      change grid n t = (j : ℝ≥0) / (2 : ℝ≥0) ^ n
      unfold grid
      rw [hjc]
  have hgrid_zero : ∀ n : ℕ, {t : ℝ≥0 | grid n t = 0} =
      {0} ∪ Ioc 0 ((1 : ℝ≥0) / (2 : ℝ≥0) ^ n) := by
    intro n
    ext t
    constructor
    · intro ht
      by_cases ht0 : t = 0
      · left; exact ht0
      · right
        constructor
        · exact lt_of_le_of_ne t.2 (Ne.symm ht0)
        · have hmul := congrArg (fun x : ℝ≥0 => x * (2 : ℝ≥0) ^ n) ht
          have hzc : ((Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 : ℕ) : ℝ≥0) = 0 := by
            simpa [grid, div_mul_cancel₀ _ (h2ne n)] using hmul
          have hzc' : Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 = 0 := by exact_mod_cast hzc
          have hcle : Nat.ceil ((2 : ℝ≥0) ^ n * t) ≤ 1 := by omega
          have hle1 : (2 : ℝ≥0) ^ n * t ≤ ((1 : ℕ) : ℝ≥0) := Nat.ceil_le.mp hcle
          have hle1' : t * (2 : ℝ≥0) ^ n ≤ ((1 : ℕ) : ℝ≥0) := by simpa [mul_comm] using hle1
          have hle1'' : t * (2 : ℝ≥0) ^ n ≤ (1 : ℝ≥0) := by simpa using hle1'
          exact (le_div_iff₀ (h2pos n)).mpr hle1''
    · intro ht
      rcases ht with rfl | ht
      · simp [grid]
      · have hle1 : (2 : ℝ≥0) ^ n * t ≤ ((1 : ℕ) : ℝ≥0) := by
          have hle1' : t * (2 : ℝ≥0) ^ n ≤ (1 : ℝ≥0) := (le_div_iff₀ (h2pos n)).mp ht.2
          have hle1'' : t * (2 : ℝ≥0) ^ n ≤ ((1 : ℕ) : ℝ≥0) := by simpa using hle1'
          simpa [mul_comm] using hle1''
        have hcle : Nat.ceil ((2 : ℝ≥0) ^ n * t) ≤ 1 := Nat.ceil_le.mpr hle1
        have hsub : Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 = 0 := by omega
        have hzc : ((Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 : ℕ) : ℝ≥0) = 0 := by
          exact_mod_cast hsub
        change grid n t = 0
        unfold grid
        rw [hzc]
        simp
  -- The grid approaches the identity from the left, uniformly in dyadic scale.
  have hgrid_le : ∀ (n : ℕ) (t : ℝ≥0), grid n t ≤ t := by
    intro n t
    by_cases hc0 : Nat.ceil ((2 : ℝ≥0) ^ n * t) = 0
    · have ht0 : t = 0 := ht0_of_hc0 n t hc0
      subst ht0
      simp [grid]
    · have hlt : (Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 : ℕ) < Nat.ceil ((2 : ℝ≥0) ^ n * t) :=
        Nat.sub_one_lt hc0
      have hup : ((Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 : ℕ) : ℝ≥0) < (2 : ℝ≥0) ^ n * t :=
        Nat.lt_ceil.mp hlt
      have hup' : ((Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 : ℕ) : ℝ≥0) ≤ t * (2 : ℝ≥0) ^ n := by
        simpa [mul_comm] using le_of_lt hup
      simpa [grid] using (div_le_iff₀ (h2pos n)).mpr hup'
  have hgrid_diff : ∀ (n : ℕ) (t : ℝ≥0), t - grid n t ≤ (1 : ℝ≥0) / (2 : ℝ≥0) ^ n := by
    intro n t
    have hup : t ≤ (((Nat.ceil ((2 : ℝ≥0) ^ n * t)) : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := by
      have hle' : t * (2 : ℝ≥0) ^ n ≤ ((Nat.ceil ((2 : ℝ≥0) ^ n * t) : ℕ) : ℝ≥0) := by
        simpa [mul_comm] using (Nat.le_ceil ((2 : ℝ≥0) ^ n * t))
      exact (le_div_iff₀ (h2pos n)).mpr hle'
    by_cases hc0 : Nat.ceil ((2 : ℝ≥0) ^ n * t) = 0
    · have ht0 : t = 0 := ht0_of_hc0 n t hc0
      subst ht0
      simp [grid]
    · have hsplit : (((Nat.ceil ((2 : ℝ≥0) ^ n * t)) : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n =
          grid n t + (1 : ℝ≥0) / (2 : ℝ≥0) ^ n := by
        have hsucc : (Nat.ceil ((2 : ℝ≥0) ^ n * t) : ℕ) =
            (Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 : ℕ) + 1 := by omega
        unfold grid
        have hcast : (((Nat.ceil ((2 : ℝ≥0) ^ n * t)) : ℕ) : ℝ≥0) =
            ((((Nat.ceil ((2 : ℝ≥0) ^ n * t) - 1 : ℕ) + 1 : ℕ) : ℝ≥0)) := by
          exact_mod_cast hsucc
        rw [hcast, Nat.cast_add, Nat.cast_one, add_div]
      have htsum : t ≤ grid n t + (1 : ℝ≥0) / (2 : ℝ≥0) ^ n := by
        simpa [hsplit] using hup
      have htsum' : t ≤ (1 : ℝ≥0) / (2 : ℝ≥0) ^ n + grid n t := by
        simpa [add_comm] using htsum
      exact (tsub_le_iff_right (a := t) (b := grid n t)
        (c := (1 : ℝ≥0) / (2 : ℝ≥0) ^ n)).mpr htsum'
  have hgrid_conv : ∀ t : ℝ≥0, Tendsto (fun n : ℕ => grid n t) atTop (𝓝 t) := by
    intro t
    rw [← NNReal.tendsto_coe]
    have hpowReal : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
        (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num))
    have hsq : Tendsto (fun n : ℕ => ((t - grid n t : ℝ≥0) : ℝ)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpowReal
        (fun n ↦ (t - grid n t : ℝ≥0).2)
        (fun n ↦ by
          have hbd : ((t - grid n t : ℝ≥0) : ℝ) ≤ (((1 : ℝ≥0) / (2 : ℝ≥0) ^ n) : ℝ) := by
            exact_mod_cast (hgrid_diff n t)
          simpa [one_div] using hbd)
    have hsub : Tendsto (fun n : ℕ => (t : ℝ) - (grid n t : ℝ)) atTop (𝓝 0) := by
      have hdiff : ∀ n : ℕ, (t : ℝ) - (grid n t : ℝ) = ((t - grid n t : ℝ≥0) : ℝ) := by
        intro n
        exact (NNReal.coe_sub (hgrid_le n t)).symm
      simpa [hdiff] using hsq
    have htconst : Tendsto (fun _ : ℕ => (t : ℝ)) atTop (𝓝 (t : ℝ)) := tendsto_const_nhds
    have hh : Tendsto (fun n : ℕ => (t : ℝ) - ((t : ℝ) - (grid n t : ℝ))) atTop
        (𝓝 ((t : ℝ) - 0)) := htconst.sub hsub
    simpa [sub_sub_cancel, sub_zero] using hh
  -- Each dyadic step is measurable for the predictable σ-algebra.
  have hmeasStep : ∀ n : ℕ, Measurable[ℱ.predictable] (fun z : ℝ≥0 × Ω => X (grid n z.1) z.2) := by
    intro n B hB
    have hpre : (fun z : ℝ≥0 × Ω => X (grid n z.1) z.2) ⁻¹' B =
        ⋃ j : ℕ, {t : ℝ≥0 | grid n t = (j : ℝ≥0) / (2 : ℝ≥0) ^ n} ×ˢ
          {ω : Ω | X ((j : ℝ≥0) / (2 : ℝ≥0) ^ n) ω ∈ B} := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_iUnion]
        refine ⟨Nat.ceil ((2 : ℝ≥0) ^ n * z.1) - 1, ?_, ?_⟩
        · simp [grid]
        · simpa [grid] using hz
      · rw [Set.mem_iUnion]
        rintro ⟨j, ht, hω⟩
        have ht' : grid n z.1 = (j : ℝ≥0) / (2 : ℝ≥0) ^ n := by simpa using ht
        change X (grid n z.1) z.2 ∈ B
        rw [ht']
        exact hω
    rw [hpre]
    refine MeasurableSet.iUnion fun j => ?_
    rcases j with _ | k
    · have hcell : ({t : ℝ≥0 | grid n t = ((0 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n} ×ˢ
          {ω : Ω | X (((0 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω ∈ B}) =
          (({0} ∪ Ioc 0 ((1 : ℝ≥0) / (2 : ℝ≥0) ^ n)) ×ˢ (X 0 ⁻¹' B)) := by
        rw [Nat.cast_zero, zero_div]
        change ({t : ℝ≥0 | grid n t = 0} ×ˢ (X 0 ⁻¹' B)) =
          (({0} ∪ Ioc 0 ((1 : ℝ≥0) / (2 : ℝ≥0) ^ n)) ×ˢ (X 0 ⁻¹' B))
        rw [hgrid_zero n]
      rw [hcell]
      rw [Set.union_prod]
      have hsing : MeasurableSet[ℱ.predictable] ({0} ×ˢ (X 0 ⁻¹' B)) := by
        simpa using (measurableSet_predictable_singleton_bot_prod (𝓕 := ℱ)
          ((hAdapted 0).measurable hB))
      exact hsing.union
        (measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 ((1 : ℝ≥0) / (2 : ℝ≥0) ^ n)
          ((hAdapted 0).measurable hB))
    · have hcell : ({t : ℝ≥0 | grid n t = ((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n} ×ˢ
          {ω : Ω | X (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ω ∈ B}) =
          (Ioc (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n)
            ((((k + 1 : ℕ) + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ×ˢ
            (X (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ⁻¹' B)) := by
        change ({t : ℝ≥0 | grid n t = ((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n} ×ˢ
            (X (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ⁻¹' B)) =
          (Ioc (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n)
            ((((k + 1 : ℕ) + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ×ˢ
            (X (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ⁻¹' B))
        rw [hgrid_cell n (k + 1) (Nat.succ_ne_zero k)]
      rw [hcell]
      exact measurableSet_predictable_Ioc_prod (𝓕 := ℱ) (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n)
        ((((k + 1 : ℕ) + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n)
        ((hAdapted (((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n)).measurable hB)
  -- Pointwise convergence of the dyadic steps to `X`.
  have hconv : ∀ z : ℝ≥0 × Ω, Tendsto (fun n : ℕ => X (grid n z.1) z.2) atTop (𝓝 (X z.1 z.2)) := by
    intro z
    exact (hCont z.2).continuousAt.tendsto.comp (hgrid_conv z.1)
  let _ : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hmeas : Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2) :=
    measurable_of_tendsto_metrizable (fun n => hmeasStep n) (tendsto_pi_nhds.mpr hconv)
  exact hmeas.stronglyMeasurable

end MeasureTheory.IsStronglyPredictable

end OTSelector.CountingProcess
