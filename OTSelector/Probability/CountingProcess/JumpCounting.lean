import OTSelector.Probability.CountingProcess.OccupationBound

/-!
# Counting attained jump labels before a time

The two-colour current chain rule needs to compare the left count of one counting process at a
jump time of the other process.  This file identifies `countBefore` with the cardinality of the
attained jump labels whose generalized jump times are strictly earlier than the evaluation time.
The horizon is explicit so that no unattained label, whose `jumpTime` may be `sInf ∅`, enters the
finite set.
-/

open Set
open scoped NNReal

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- For an attained label, being strictly before `s` is equivalent to being counted by the
left-limit count at `s`. -/
theorem jumpTime_lt_iff_lt_countBefore
    {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {k : ℕ} {s T : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun u ↦ (N u ω : ℝ)) (Ici t) t)
    (hinj : Set.InjOn (fun j ↦ jumpTime N j ω) (Iio (N T ω)))
    (hkT : k < N T ω) :
    jumpTime N k ω < s ↔ k < countBefore N s ω := by
  constructor
  · intro hks
    rw [← Nat.succ_le_iff, countBefore_succ_le_iff hmono]
    refine ⟨jumpTime N k ω, hks, ?_⟩
    rw [N_jumpTime_of_lt hmono hrc hinj hkT]
    exact Nat.lt_succ_self k
  · intro hk
    rw [← Nat.succ_le_iff, countBefore_succ_le_iff hmono] at hk
    rcases hk with ⟨u, hus, hku⟩
    exact (jumpTime_le_of_lt hku).trans_lt hus

omit [MeasurableSpace Ω] in
/-- The labels attained by `T` and strictly earlier than `s ≤ T` are exactly
`0, ..., countBefore N s - 1`. -/
theorem filter_jumpTime_lt_eq_range_countBefore
    {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {s T : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun u ↦ (N u ω : ℝ)) (Ici t) t)
    (hinj : Set.InjOn (fun j ↦ jumpTime N j ω) (Iio (N T ω)))
    (hsT : s ≤ T) :
    (Finset.range (N T ω)).filter (fun k ↦ jumpTime N k ω < s) =
      Finset.range (countBefore N s ω) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hkT, hks⟩
    exact (jumpTime_lt_iff_lt_countBefore hmono hrc hinj hkT).mp hks
  · intro hk
    have hkT : k < N T ω := by
      rw [← Nat.succ_le_iff, countBefore_succ_le_iff hmono] at hk
      rcases hk with ⟨u, hus, hku⟩
      exact hku.trans_le (hmono (hus.le.trans hsT))
    exact ⟨hkT, (jumpTime_lt_iff_lt_countBefore hmono hrc hinj hkT).mpr hk⟩

omit [MeasurableSpace Ω] in
/-- Cardinal form of `filter_jumpTime_lt_eq_range_countBefore`. -/
theorem card_filter_jumpTime_lt_eq_countBefore_of_path
    {N : ℝ≥0 → Ω → ℕ} {ω : Ω} {s T : ℝ≥0}
    (hmono : Monotone fun t ↦ N t ω)
    (hrc : ∀ t, ContinuousWithinAt (fun u ↦ (N u ω : ℝ)) (Ici t) t)
    (hinj : Set.InjOn (fun j ↦ jumpTime N j ω) (Iio (N T ω)))
    (hsT : s ≤ T) :
    ((Finset.range (N T ω)).filter (fun k ↦ jumpTime N k ω < s)).card =
      countBefore N s ω := by
  rw [filter_jumpTime_lt_eq_range_countBefore hmono hrc hinj hsT,
    Finset.card_range]

/-- Public specialization using the path properties of a simple counting process. -/
theorem IsSimpleCountingProcess.card_filter_jumpTime_lt_eq_countBefore
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    (hN : IsSimpleCountingProcess ℱ N) {ω : Ω} {s T : ℝ≥0} (hsT : s ≤ T) :
    ((Finset.range (N T ω)).filter (fun k ↦ jumpTime N k ω < s)).card =
      countBefore N s ω :=
  card_filter_jumpTime_lt_eq_countBefore_of_path (hN.monotone ω) (hN.rightContinuous ω)
    (hN.jumpTime_injOn ω T) hsT

end OTSelector.CountingProcess
