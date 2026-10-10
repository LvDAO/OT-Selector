import OTSelector.Probability.CountingProcess.JumpCounting

/-!
# Two-colour counting currents

This file contains the deterministic bookkeeping for a current driven by two natural-valued
counting paths.  It stops before any merged-jump chain rule or martingale statement: the only
process hypotheses below are those needed to use the monotonicity and zero-value accessors of
`IsSimpleCountingProcess`.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology BigOperators

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Current coordinates -/

/-- The integer current obtained from an initial current and two cumulative counts. -/
def currentOfCounts (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ)
    (t : ℝ≥0) (ω : Ω) : ℤ :=
  K0 ω + (Nplus t ω : ℤ) - (Nminus t ω : ℤ)

/-- The current just before `t`, using the count of jumps strictly before `t`. -/
noncomputable def leftCurrentOfCounts (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ)
    (t : ℝ≥0) (ω : Ω) : ℤ :=
  K0 ω + (countBefore Nplus t ω : ℤ) - (countBefore Nminus t ω : ℤ)

/-- The two colours have no common attained jump time up to the deterministic horizon `T`.

The guards are horizon-local: only labels attained by time `T` are compared. -/
def NoSimultaneousJumpsOn (Nplus Nminus : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) : Prop :=
  ∀ ⦃ω : Ω⦄ ⦃i j : ℕ⦄, i < Nplus T ω → j < Nminus T ω →
    jumpTime Nplus i ω ≠ jumpTime Nminus j ω

/-! ## Zero and horizon accessors -/

omit [MeasurableSpace Ω] in
/-- `countBefore` is zero at the bottom time. -/
@[simp]
theorem countBefore_zero (N : ℝ≥0 → Ω → ℕ) (ω : Ω) :
    countBefore N 0 ω = 0 := by
  simp [countBefore]

/-- A simple counting current starts from its initial current. -/
@[simp]
theorem currentOfCounts_zero
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus) (ω : Ω) :
    currentOfCounts K0 Nplus Nminus 0 ω = K0 ω := by
  simp [currentOfCounts, hplus.zero, hminus.zero]

omit [MeasurableSpace Ω] in
/-- The left current at time zero is the initial current. -/
@[simp]
theorem leftCurrentOfCounts_zero
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ) (ω : Ω) :
    leftCurrentOfCounts K0 Nplus Nminus 0 ω = K0 ω := by
  simp [leftCurrentOfCounts]

/-- No cross-colour jump can occur before a zero horizon when both paths start at zero. -/
theorem NoSimultaneousJumpsOn.zero
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus) :
    NoSimultaneousJumpsOn Nplus Nminus 0 := by
  intro ω i j hi hj
  rw [hplus.zero] at hi
  rw [hminus.zero] at hj
  have hi0 : i < 0 := hi
  have hj0 : j < 0 := hj
  omega

/-- A no-simultaneous-jumps assertion restricts to every smaller horizon.

The only hypotheses needed for the restriction are pathwise monotonicity of the two counts;
`IsSimpleCountingProcess` supplies those hypotheses through its accessor theorem. -/
theorem NoSimultaneousJumpsOn.mono
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {S T : ℝ≥0}
    (hT : NoSimultaneousJumpsOn Nplus Nminus T)
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus) (hST : S ≤ T) :
    NoSimultaneousJumpsOn Nplus Nminus S := by
  intro ω i j hi hj
  apply hT
  · exact lt_of_lt_of_le hi (hplus.monotone ω hST)
  · exact lt_of_lt_of_le hj (hminus.monotone ω hST)

/-! ## The endpoint jump relative to the strict-left count -/

/-- The strict-left count never exceeds the count at the evaluation time. -/
theorem IsSimpleCountingProcess.countBefore_le_at
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} (hN : IsSimpleCountingProcess ℱ N)
    (t : ℝ≥0) (ω : Ω) :
    countBefore N t ω ≤ N t ω := by
  by_contra hnot
  have hsucc : N t ω + 1 ≤ countBefore N t ω := by omega
  rw [countBefore_succ_le_iff (hN.monotone ω)] at hsucc
  rcases hsucc with ⟨u, hut, hNu⟩
  exact (not_lt_of_ge (hN.monotone ω hut.le)) hNu

/-- Every attained jump label between the strict-left count and the current count occurs exactly
at the evaluation time. -/
theorem IsSimpleCountingProcess.jumpTime_eq_of_countBefore_le_of_lt
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} (hN : IsSimpleCountingProcess ℱ N)
    {t : ℝ≥0} {ω : Ω} {k : ℕ}
    (hleft : countBefore N t ω ≤ k) (hright : k < N t ω) :
    jumpTime N k ω = t := by
  apply le_antisymm (jumpTime_le_of_lt hright)
  apply le_of_not_gt
  intro hjump
  have hkBefore := (jumpTime_lt_iff_lt_countBefore
    (hN.monotone ω) (hN.rightContinuous ω) (hN.jumpTime_injOn ω t) hright).mp hjump
  exact (not_lt_of_ge hleft) hkBefore

/-- A simple counting path has either no jump or exactly one jump at a fixed time. -/
theorem IsSimpleCountingProcess.count_eq_countBefore_or_eq_add_one
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} (hN : IsSimpleCountingProcess ℱ N)
    (t : ℝ≥0) (ω : Ω) :
    N t ω = countBefore N t ω ∨ N t ω = countBefore N t ω + 1 := by
  have hleft := hN.countBefore_le_at t ω
  have hright : N t ω ≤ countBefore N t ω + 1 := by
    by_contra hnot
    have hk : countBefore N t ω < N t ω := by omega
    have hksucc : countBefore N t ω + 1 < N t ω := by omega
    have hkTime := hN.jumpTime_eq_of_countBefore_le_of_lt (le_refl _) hk
    have hksuccTime := hN.jumpTime_eq_of_countBefore_le_of_lt
      (Nat.le_succ _) hksucc
    have heq : countBefore N t ω = countBefore N t ω + 1 :=
      hN.jumpTime_injOn ω t hk hksucc (hkTime.trans hksuccTime.symm)
    omega
  omega

/-- With no cross-colour simultaneous jump, the post-current and strict-left current differ by at
most one. -/
theorem abs_currentOfCounts_sub_leftCurrentOfCounts_le_one
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    {t : ℝ≥0} {ω : Ω} (hNo : NoSimultaneousJumpsOn Nplus Nminus t) :
    |(currentOfCounts K0 Nplus Nminus t ω : ℝ) -
        (leftCurrentOfCounts K0 Nplus Nminus t ω : ℝ)| ≤ 1 := by
  rcases hplus.count_eq_countBefore_or_eq_add_one t ω with hplusEq | hplusSucc
  · rcases hminus.count_eq_countBefore_or_eq_add_one t ω with hminusEq | hminusSucc
    · simp [currentOfCounts, leftCurrentOfCounts, hplusEq, hminusEq]
    · norm_num [currentOfCounts, leftCurrentOfCounts, hplusEq, hminusSucc]
  · rcases hminus.count_eq_countBefore_or_eq_add_one t ω with hminusEq | hminusSucc
    · norm_num [currentOfCounts, leftCurrentOfCounts, hplusSucc, hminusEq]
    · exfalso
      have hplusLt : countBefore Nplus t ω < Nplus t ω := by omega
      have hminusLt : countBefore Nminus t ω < Nminus t ω := by omega
      have hplusTime := hplus.jumpTime_eq_of_countBefore_le_of_lt
        (le_refl _) hplusLt
      have hminusTime := hminus.jumpTime_eq_of_countBefore_le_of_lt
        (le_refl _) hminusLt
      exact (hNo hplusLt hminusLt) (hplusTime.trans hminusTime.symm)

/-! ## Exact count increments -/

omit [MeasurableSpace Ω] in
/-- The current increment is exactly the signed difference of the two count increments. -/
theorem currentOfCounts_sub
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ) (s t : ℝ≥0) (ω : Ω) :
    currentOfCounts K0 Nplus Nminus t ω - currentOfCounts K0 Nplus Nminus s ω =
      ((Nplus t ω : ℤ) - (Nplus s ω : ℤ)) -
        ((Nminus t ω : ℤ) - (Nminus s ω : ℤ)) := by
  dsimp [currentOfCounts]
  ring

/-- The same current increment with each count difference written as a natural subtraction.

The order assumption and the two simple-counting-process hypotheses are mathematically necessary
for replacing an integer difference of counts by the cast of a natural difference. -/
theorem currentOfCounts_sub_natSub
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (K0 : Ω → ℤ) {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus) {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    currentOfCounts K0 Nplus Nminus t ω - currentOfCounts K0 Nplus Nminus s ω =
      ((Nplus t ω - Nplus s ω : ℕ) : ℤ) -
        ((Nminus t ω - Nminus s ω : ℕ) : ℤ) := by
  rw [currentOfCounts_sub]
  rw [Nat.cast_sub (hplus.monotone ω hst), Nat.cast_sub (hminus.monotone ω hst)]

omit [MeasurableSpace Ω] in
/-- The left-current increment is exactly the signed difference of the two left-count increments. -/
theorem leftCurrentOfCounts_sub
    (K0 : Ω → ℤ) (Nplus Nminus : ℝ≥0 → Ω → ℕ) (s t : ℝ≥0) (ω : Ω) :
    leftCurrentOfCounts K0 Nplus Nminus t ω - leftCurrentOfCounts K0 Nplus Nminus s ω =
      ((countBefore Nplus t ω : ℤ) - (countBefore Nplus s ω : ℤ)) -
        ((countBefore Nminus t ω : ℤ) - (countBefore Nminus s ω : ℤ)) := by
  dsimp [leftCurrentOfCounts]
  ring

/-! ## One-step telescoping -/

/-- Summing arbitrary `+1` increments of `f` telescopes over a finite integer interval. -/
theorem telescoping_add_one (f : ℤ → ℝ) (k : ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      (f (k + (i : ℤ) + 1) - f (k + (i : ℤ)))) =
      f (k + (n : ℤ)) - f k := by
  simpa [Nat.cast_add, add_assoc] using
    (Finset.sum_range_sub (fun i : ℕ => f (k + (i : ℤ))) n)

/-- Summing arbitrary `-1` increments of `f` telescopes over a finite integer interval. -/
theorem telescoping_sub_one (f : ℤ → ℝ) (k : ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      (f (k - (i : ℤ) - 1) - f (k - (i : ℤ)))) =
      f (k - (n : ℤ)) - f k := by
  simpa [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Finset.sum_range_sub (fun i : ℕ => f (k - (i : ℤ))) n)

end OTSelector.CountingProcess
