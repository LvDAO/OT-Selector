import OTSelector.Probability.CountingProcess.JumpCounting
import OTSelector.Probability.CountingProcess.MarkedCurrent
import OTSelector.Probability.CountingProcess.OrderedTelescoping
import Mathlib.Data.Prod.Lex

/-!
# Pathwise chain rule for a two-colour counting current

The attained labels of the two counting paths form a finite disjoint sum.  We order those events
by the injective lexicographic key `(jump time, colour, label)`.  Under the explicit
no-simultaneous-jumps hypothesis, key order on attained events is exactly strict time order.
`JumpCounting.lean` then identifies the ordered prefix state with `leftCurrentOfCounts`, and the
finite ordered telescoping theorem yields the two-colour chain rule without assuming it.
-/

open Set
open scoped BigOperators NNReal

namespace OTSelector.CountingProcess

open _root_.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Finite marked event set -/

/-- The time of a source (`inl`) or target (`inr`) jump label. -/
noncomputable def markedEventTime (Nplus Nminus : ℝ≥0 → Ω → ℕ) (ω : Ω) :
    ℕ ⊕ ℕ → ℝ≥0
  | Sum.inl i => jumpTime Nplus i ω
  | Sum.inr j => jumpTime Nminus j ω

/-- Signed current increment carried by a marked event. -/
def markedEventStep : ℕ ⊕ ℕ → ℤ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- An injective deterministic colour-and-label identifier. -/
def markedEventId : ℕ ⊕ ℕ → Bool ×ₗ ℕ
  | Sum.inl i => toLex (false, i)
  | Sum.inr j => toLex (true, j)

/-- Lexicographic event key.  The identifier breaks ties globally; attained cross-colour ties are
later excluded by `NoSimultaneousJumpsOn`. -/
noncomputable def markedEventKey (Nplus Nminus : ℝ≥0 → Ω → ℕ) (ω : Ω) :
    ℕ ⊕ ℕ → ℝ≥0 ×ₗ (Bool ×ₗ ℕ) :=
  fun e => toLex (markedEventTime Nplus Nminus ω e, markedEventId e)

/-- All source and target labels attained by `T`. -/
def markedEventSet (Nplus Nminus : ℝ≥0 → Ω → ℕ) (T : ℝ≥0) (ω : Ω) :
    Finset (ℕ ⊕ ℕ) :=
  (Finset.range (Nplus T ω)).disjSum (Finset.range (Nminus T ω))

omit [MeasurableSpace Ω] in
theorem markedEventId_injective : Function.Injective markedEventId := by
  intro e e' h
  cases e with
  | inl i =>
      cases e' with
      | inl i' =>
          simp only [markedEventId, toLex_inj, Prod.mk.injEq, true_and] at h
          exact congrArg Sum.inl h
      | inr j =>
          simp [markedEventId] at h
  | inr j =>
      cases e' with
      | inl i =>
          simp [markedEventId] at h
      | inr j' =>
          simp only [markedEventId, toLex_inj, Prod.mk.injEq, true_and] at h
          exact congrArg Sum.inr h

omit [MeasurableSpace Ω] in
theorem markedEventKey_injective (Nplus Nminus : ℝ≥0 → Ω → ℕ) (ω : Ω) :
    Function.Injective (markedEventKey Nplus Nminus ω) := by
  intro e e' h
  have hpair := toLex_inj.mp h
  exact markedEventId_injective (congrArg Prod.snd hpair)

omit [MeasurableSpace Ω] in
theorem mem_markedEventSet_iff
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {T : ℝ≥0} {ω : Ω} {e : ℕ ⊕ ℕ} :
    e ∈ markedEventSet Nplus Nminus T ω ↔
      (∃ i < Nplus T ω, e = Sum.inl i) ∨
        ∃ j < Nminus T ω, e = Sum.inr j := by
  cases e <;> simp [markedEventSet]

omit [MeasurableSpace Ω] in
theorem markedEventTime_le_horizon
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {T : ℝ≥0} {ω : Ω} {e : ℕ ⊕ ℕ}
    (he : e ∈ markedEventSet Nplus Nminus T ω) :
    markedEventTime Nplus Nminus ω e ≤ T := by
  rw [mem_markedEventSet_iff] at he
  rcases he with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact jumpTime_le_of_lt hi
  · exact jumpTime_le_of_lt hj

omit [MeasurableSpace Ω] in
theorem markedEventTime_injOn
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {T : ℝ≥0} {ω : Ω}
    (hplusInj : Set.InjOn (fun i => jumpTime Nplus i ω) (Iio (Nplus T ω)))
    (hminusInj : Set.InjOn (fun j => jumpTime Nminus j ω) (Iio (Nminus T ω)))
    (hNo : NoSimultaneousJumpsOn Nplus Nminus T) :
    Set.InjOn (markedEventTime Nplus Nminus ω)
      (markedEventSet Nplus Nminus T ω : Set (ℕ ⊕ ℕ)) := by
  intro e he e' he' htime
  change e ∈ markedEventSet Nplus Nminus T ω at he
  change e' ∈ markedEventSet Nplus Nminus T ω at he'
  rw [mem_markedEventSet_iff] at he he'
  rcases he with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ <;>
    rcases he' with ⟨i', hi', rfl⟩ | ⟨j', hj', rfl⟩
  · exact congrArg Sum.inl (hplusInj hi hi' htime)
  · exact (hNo hi hj' htime).elim
  · exact (hNo hi' hj htime.symm).elim
  · exact congrArg Sum.inr (hminusInj hj hj' htime)

omit [MeasurableSpace Ω] in
/-- On attained events, the injective lexicographic key orders exactly by strict jump time. -/
theorem markedEventKey_lt_iff_time_lt
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {T : ℝ≥0} {ω : Ω} {e x : ℕ ⊕ ℕ}
    (htimeInj : Set.InjOn (markedEventTime Nplus Nminus ω)
      (markedEventSet Nplus Nminus T ω : Set (ℕ ⊕ ℕ)))
    (he : e ∈ markedEventSet Nplus Nminus T ω)
    (hx : x ∈ markedEventSet Nplus Nminus T ω) :
    markedEventKey Nplus Nminus ω e < markedEventKey Nplus Nminus ω x ↔
      markedEventTime Nplus Nminus ω e < markedEventTime Nplus Nminus ω x := by
  change toLex (markedEventTime Nplus Nminus ω e, markedEventId e) <
      toLex (markedEventTime Nplus Nminus ω x, markedEventId x) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hlt | ⟨heq, hid⟩)
    · exact hlt
    · have hex : e = x := htimeInj he hx heq
      subst x
      exact (lt_irrefl (markedEventId e) hid).elim
  · intro hlt
    exact Or.inl hlt

/-! ## Earlier-event signed sum -/

omit [MeasurableSpace Ω] in
theorem sum_markedEventStep_before_eq
    {Nplus Nminus : ℝ≥0 → Ω → ℕ} {T : ℝ≥0} {ω : Ω} {x : ℕ ⊕ ℕ}
    (hplusMono : Monotone fun t => Nplus t ω)
    (hplusRC : ∀ t, ContinuousWithinAt (fun u => (Nplus u ω : ℝ)) (Ici t) t)
    (hplusInj : Set.InjOn (fun i => jumpTime Nplus i ω) (Iio (Nplus T ω)))
    (hminusMono : Monotone fun t => Nminus t ω)
    (hminusRC : ∀ t, ContinuousWithinAt (fun u => (Nminus u ω : ℝ)) (Ici t) t)
    (hminusInj : Set.InjOn (fun j => jumpTime Nminus j ω) (Iio (Nminus T ω)))
    (hx : x ∈ markedEventSet Nplus Nminus T ω) :
    (∑ e ∈ (markedEventSet Nplus Nminus T ω).filter
        (fun e => markedEventTime Nplus Nminus ω e <
          markedEventTime Nplus Nminus ω x), markedEventStep e) =
      (countBefore Nplus (markedEventTime Nplus Nminus ω x) ω : ℤ) -
        (countBefore Nminus (markedEventTime Nplus Nminus ω x) ω : ℤ) := by
  classical
  let S := (markedEventSet Nplus Nminus T ω).filter
    (fun e => markedEventTime Nplus Nminus ω e < markedEventTime Nplus Nminus ω x)
  have hleft : S.toLeft = (Finset.range (Nplus T ω)).filter
      (fun i => jumpTime Nplus i ω < markedEventTime Nplus Nminus ω x) := by
    ext i
    rw [Finset.mem_toLeft]
    constructor
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨hiS, hit⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.inl_mem_disjSum.mp hiS
      · exact hit
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨hiR, hit⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.inl_mem_disjSum.mpr hiR
      · exact hit
  have hright : S.toRight = (Finset.range (Nminus T ω)).filter
      (fun j => jumpTime Nminus j ω < markedEventTime Nplus Nminus ω x) := by
    ext j
    rw [Finset.mem_toRight]
    constructor
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hjS, hjt⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.inr_mem_disjSum.mp hjS
      · exact hjt
    · intro hj
      rcases Finset.mem_filter.mp hj with ⟨hjR, hjt⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.inr_mem_disjSum.mpr hjR
      · exact hjt
  have hxT : markedEventTime Nplus Nminus ω x ≤ T := markedEventTime_le_horizon hx
  have hplusCard := card_filter_jumpTime_lt_eq_countBefore_of_path
    hplusMono hplusRC hplusInj hxT
  have hminusCard := card_filter_jumpTime_lt_eq_countBefore_of_path
    hminusMono hminusRC hminusInj hxT
  have hsumLeft : (∑ i ∈ S.toLeft, markedEventStep (Sum.inl i)) =
      (S.toLeft.card : ℤ) := by
    simp [markedEventStep]
  have hsumRight : (∑ j ∈ S.toRight, markedEventStep (Sum.inr j)) =
      -(S.toRight.card : ℤ) := by
    simp [markedEventStep]
  change (∑ e ∈ S, markedEventStep e) = _
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hsumLeft, hsumRight,
    hleft, hright]
  rw [hplusCard, hminusCard]
  ring

/-! ## Two-colour chain rule -/

/-- Exact pathwise chain rule for a current driven by two simple counting processes. -/
theorem currentOfCounts_chain_rule
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {K0 : Ω → ℤ} {Nplus Nminus : ℝ≥0 → Ω → ℕ}
    (hplus : IsSimpleCountingProcess ℱ Nplus)
    (hminus : IsSimpleCountingProcess ℱ Nminus)
    {T : ℝ≥0} (hNo : NoSimultaneousJumpsOn Nplus Nminus T)
    (f : ℤ → ℝ) (ω : Ω) :
    f (currentOfCounts K0 Nplus Nminus T ω) - f (K0 ω) =
      countingIntegral Nplus
          (fun s ω' => f (leftCurrentOfCounts K0 Nplus Nminus s ω' + 1) -
            f (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω +
        countingIntegral Nminus
          (fun s ω' => f (leftCurrentOfCounts K0 Nplus Nminus s ω' - 1) -
            f (leftCurrentOfCounts K0 Nplus Nminus s ω')) T ω := by
  classical
  let s := markedEventSet Nplus Nminus T ω
  let time := markedEventTime Nplus Nminus ω
  let key := markedEventKey Nplus Nminus ω
  let step := markedEventStep
  have htimeInj : Set.InjOn time (s : Set (ℕ ⊕ ℕ)) := by
    exact markedEventTime_injOn (hplus.jumpTime_injOn ω T)
      (hminus.jumpTime_injOn ω T) hNo
  have hkeyOrder : ∀ e ∈ s, ∀ x ∈ s, key e < key x ↔ time e < time x := by
    intro e he x hx
    exact markedEventKey_lt_iff_time_lt htimeInj he hx
  have hbefore : ∀ x ∈ s,
      (∑ e ∈ s.filter (fun e => key e < key x), step e) =
        (countBefore Nplus (time x) ω : ℤ) - (countBefore Nminus (time x) ω : ℤ) := by
    intro x hx
    have hfilter : s.filter (fun e => key e < key x) =
        s.filter (fun e => time e < time x) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, hek⟩
        exact ⟨he, (hkeyOrder e he x hx).mp hek⟩
      · rintro ⟨he, het⟩
        exact ⟨he, (hkeyOrder e he x hx).mpr het⟩
    rw [hfilter]
    exact sum_markedEventStep_before_eq (hplus.monotone ω) (hplus.rightContinuous ω)
      (hplus.jumpTime_injOn ω T) (hminus.monotone ω) (hminus.rightContinuous ω)
      (hminus.jumpTime_injOn ω T) hx
  have htel := sum_keyOrdered_increment_eq s key
    (markedEventKey_injective Nplus Nminus ω) step f (K0 ω)
  have htotal : (∑ e ∈ s, step e) = (Nplus T ω : ℤ) - (Nminus T ω : ℤ) := by
    dsimp [s, step]
    unfold markedEventSet
    rw [Finset.sum_disjSum]
    simp [markedEventStep]
    ring
  have hsum :
      (∑ e ∈ s,
          (f (K0 ω + (∑ y ∈ s.filter (fun y => key y < key e), step y) + step e) -
            f (K0 ω + ∑ y ∈ s.filter (fun y => key y < key e), step y))) =
        countingIntegral Nplus
            (fun u ω' => f (leftCurrentOfCounts K0 Nplus Nminus u ω' + 1) -
              f (leftCurrentOfCounts K0 Nplus Nminus u ω')) T ω +
          countingIntegral Nminus
            (fun u ω' => f (leftCurrentOfCounts K0 Nplus Nminus u ω' - 1) -
              f (leftCurrentOfCounts K0 Nplus Nminus u ω')) T ω := by
    dsimp [s]
    unfold markedEventSet
    rw [Finset.sum_disjSum]
    unfold countingIntegral
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hxi : Sum.inl i ∈ s := by simp [s, markedEventSet, hi]
      have hb := hbefore (Sum.inl i) hxi
      dsimp [s, step, time] at hb
      unfold markedEventSet at hb
      rw [hb]
      simp [step, markedEventStep, markedEventTime, leftCurrentOfCounts]
      ring_nf
    · apply Finset.sum_congr rfl
      intro j hj
      have hxj : Sum.inr j ∈ s := by simp [s, markedEventSet, hj]
      have hb := hbefore (Sum.inr j) hxj
      dsimp [s, step, time] at hb
      unfold markedEventSet at hb
      rw [hb]
      simp [step, markedEventStep, markedEventTime, leftCurrentOfCounts]
      ring_nf
  calc
    f (currentOfCounts K0 Nplus Nminus T ω) - f (K0 ω) =
        f (K0 ω + ∑ e ∈ s, step e) - f (K0 ω) := by
      rw [htotal]
      unfold currentOfCounts
      congr 2
      ring
    _ = ∑ e ∈ s,
          (f (K0 ω + (∑ y ∈ s.filter (fun y => key y < key e), step y) + step e) -
            f (K0 ω + ∑ y ∈ s.filter (fun y => key y < key e), step y)) := htel.symm
    _ = countingIntegral Nplus
          (fun u ω' => f (leftCurrentOfCounts K0 Nplus Nminus u ω' + 1) -
            f (leftCurrentOfCounts K0 Nplus Nminus u ω')) T ω +
        countingIntegral Nminus
          (fun u ω' => f (leftCurrentOfCounts K0 Nplus Nminus u ω' - 1) -
            f (leftCurrentOfCounts K0 Nplus Nminus u ω')) T ω := hsum

end OTSelector.CountingProcess
