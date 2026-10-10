import OTSelector.Limit.FeedbackStationaryFutureGeometry

/-!
# The jumps of the complete future are actual environment events

The jump-index concatenation preserves each cell's physical clock and sampled marks. Its
positive jump labels correspond bijectively to the valid labels in the positive cells, so event
multiplicities are retained.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace OTSelector.Limit

open PointProcess

attribute [local instance] Classical.propDecidable

/-- Bounds between consecutive jump offsets characterize the containing cell uniquely. -/
theorem feedbackCellJumpIndex_eq_of_bounds (ω : ℕ → FeedbackCellPath) (m j : ℕ)
    (hlo : feedbackCellJumpOffset ω j ≤ m)
    (hhi : m < feedbackCellJumpOffset ω (j + 1)) : feedbackCellJumpIndex ω m = j := by
  have hb := feedbackCellJumpIndex_bounds ω m
  have hm := (feedbackCellJumpOffset_strictMono ω).monotone
  rcases lt_trichotomy (feedbackCellJumpIndex ω m) j with h | h | h
  · have hh := hm (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hh
    omega
  · exact h
  · have hh := hm (Nat.succ_le_of_lt h)
    simp only [Nat.succ_eq_add_one] at hh
    omega

/-- Every real coordinate of a cell is read at its exact concatenated jump index. -/
theorem feedbackConcatCellPaths_cell_coordinate (ω : ℕ → FeedbackCellPath) (j n : ℕ)
    (hn : n < feedbackCellJumpCount (ω j)) :
    feedbackConcatCellPaths ω (feedbackCellJumpOffset ω j + n + 1) = ω j (n + 1) := by
  have hi : feedbackCellJumpIndex ω (feedbackCellJumpOffset ω j + n) = j := by
    apply feedbackCellJumpIndex_eq_of_bounds
    · omega
    · rw [feedbackCellJumpOffset_succ]
      omega
  simp only [feedbackConcatCellPaths, hi]
  congr 1
  omega

/-- Physical clocks inside a cell differ from its local clocks by the cell's starting clock. -/
theorem feedbackConcatCellPaths_clock_add (ω : ℕ → FeedbackCellPath) (j n : ℕ)
    (hn : n ≤ feedbackCellJumpCount (ω j)) :
    feedbackCellClock (feedbackConcatCellPaths ω) (feedbackCellJumpOffset ω j + n) =
      feedbackCellClock (feedbackConcatCellPaths ω) (feedbackCellJumpOffset ω j) +
        feedbackCellClock (ω j) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, feedbackCellClock_succ,
        feedbackConcatCellPaths_cell_coordinate ω j n (by omega), ih (by omega),
        feedbackCellClock_succ]
      ring

/-- Concatenated cell-start clocks are exactly the sums of the preceding physical cell lengths. -/
theorem feedbackConcatCellPaths_offset_clock (ω : ℕ → FeedbackCellPath)
    (hw : ∀ j n, 0 < (ω j (n + 1)).1)
    (hτ : ∀ j, 0 < feedbackMarkedFirstReturnIndex (ω j)) (j : ℕ) :
    feedbackCellClock (feedbackConcatCellPaths ω) (feedbackCellJumpOffset ω j) =
      ∑ i ∈ Finset.range j, feedbackCellLength (ω i) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [feedbackCellJumpOffset_succ, feedbackConcatCellPaths_clock_add ω j _ le_rfl,
        ih, Finset.sum_range_succ]
      congr 1
      rw [feedbackCellJumpCount, max_eq_right (hτ j),
        ← feedbackCellLength_eq_clock (ω j) (hw j) (hτ j)]

/-- The physical time of every cell coordinate agrees with its local clock plus preceding lengths. -/
theorem feedbackConcatCellPaths_cell_clock (ω : ℕ → FeedbackCellPath)
    (hw : ∀ j n, 0 < (ω j (n + 1)).1)
    (hτ : ∀ j, 0 < feedbackMarkedFirstReturnIndex (ω j)) (j n : ℕ)
    (hn : n ≤ feedbackMarkedFirstReturnIndex (ω j)) :
    feedbackCellClock (feedbackConcatCellPaths ω) (feedbackCellJumpOffset ω j + n) =
      (∑ i ∈ Finset.range j, feedbackCellLength (ω i)) + feedbackCellClock (ω j) n := by
  rw [feedbackConcatCellPaths_clock_add ω j n (hn.trans (le_max_right _ _)),
    feedbackConcatCellPaths_offset_clock ω hw hτ j]

/-- Every global jump has exactly one valid positive-cell event label. -/
theorem feedbackConcatCellPaths_event_exists_unique (ω : ℕ → FeedbackCellPath)
    (hτ : ∀ j, 0 < feedbackMarkedFirstReturnIndex (ω j)) (m : ℕ) :
    ∃! p : ℕ × ℕ, p.2 < feedbackMarkedFirstReturnIndex (ω p.1) ∧
      m = feedbackCellJumpOffset ω p.1 + p.2 := by
  let j := feedbackCellJumpIndex ω m
  have hb := feedbackCellJumpIndex_bounds ω m
  have hcount (i : ℕ) : feedbackCellJumpCount (ω i) = feedbackMarkedFirstReturnIndex (ω i) :=
    max_eq_right (hτ i)
  refine ⟨(j, m - feedbackCellJumpOffset ω j), ?_, ?_⟩
  · dsimp only
    rw [feedbackCellJumpOffset_succ, hcount] at hb
    change feedbackCellJumpOffset ω j ≤ m ∧
      m < feedbackCellJumpOffset ω j + feedbackMarkedFirstReturnIndex (ω j) at hb
    omega
  · rintro ⟨i, n⟩ ⟨hn, hm⟩
    dsimp only at hn hm ⊢
    have hi : feedbackCellJumpIndex ω m = i := by
      apply feedbackCellJumpIndex_eq_of_bounds
      · omega
      · rw [feedbackCellJumpOffset_succ, hcount]
        omega
    have hij : i = j := hi.symm
    apply Prod.ext hij
    dsimp only
    rw [hij] at hm
    omega

/-- In the two-sided construction, the same clock formula uses the actual spatial cell root. -/
theorem feedbackConcatPositiveCellPaths_cell_clock (w : FeedbackCellSequence)
    (hw : ∀ j : ℤ, ∀ n, 0 < (w j (n + 1)).1)
    (hτ : ∀ j : ℤ, 0 < feedbackMarkedFirstReturnIndex (w j)) (j n : ℕ)
    (hn : n ≤ feedbackMarkedFirstReturnIndex (w (j : ℤ))) :
    feedbackCellClock (feedbackConcatPositiveCellPaths w)
      (feedbackCellJumpOffset (fun i : ℕ ↦ w (i : ℤ)) j + n) =
        feedbackCellRoot w (j : ℤ) + feedbackCellClock (w (j : ℤ)) n := by
  exact feedbackConcatCellPaths_cell_clock (fun i : ℕ ↦ w (i : ℤ))
    (fun j ↦ hw j) (fun j ↦ hτ j) j n hn

/-- Every valid positive-cell label is the identical physical point and sampled mark in the
complete concatenated path. The event coordinates include terminal return jumps. -/
theorem feedbackConcatPositiveCellPaths_cell_eventPoint (w : FeedbackCellSequence)
    (hw : ∀ j : ℤ, ∀ n, 0 < (w j (n + 1)).1)
    (hτ : ∀ j : ℤ, 0 < feedbackMarkedFirstReturnIndex (w j)) (j n : ℕ)
    (hn : n < feedbackMarkedFirstReturnIndex (w (j : ℤ))) :
    (feedbackCellClock (feedbackConcatPositiveCellPaths w)
        (feedbackCellJumpOffset (fun i : ℕ ↦ w (i : ℤ)) j + n + 1),
      (feedbackConcatPositiveCellPaths w
        (feedbackCellJumpOffset (fun i : ℕ ↦ w (i : ℤ)) j + n + 1)).2.1) =
      feedbackCellEventPoint w ((j : ℤ), n) := by
  rw [show feedbackCellJumpOffset (fun i : ℕ ↦ w (i : ℤ)) j + n + 1 =
      feedbackCellJumpOffset (fun i : ℕ ↦ w (i : ℤ)) j + (n + 1) by omega,
    feedbackConcatPositiveCellPaths_cell_clock w hw hτ j (n + 1) (by omega)]
  congr 1
  change (feedbackConcatCellPaths (fun i : ℕ ↦ w (i : ℤ))
    (feedbackCellJumpOffset (fun i : ℕ ↦ w (i : ℤ)) j + n + 1)).2.1 = _
  rw [feedbackConcatCellPaths_cell_coordinate _ j n (hn.trans_le (le_max_right _ _))]

private theorem feedbackCellJumpCount_eq_return (w : FeedbackCellPath)
    (hτ : 0 < feedbackMarkedFirstReturnIndex w) :
    feedbackCellJumpCount w = feedbackMarkedFirstReturnIndex w := max_eq_right hτ

/-- Every cell boundary of the concatenated trajectory has current zero. -/
theorem feedbackConcatCellPaths_offset_current (ω : ℕ → FeedbackCellPath)
    (hτ : ∀ j, 0 < feedbackMarkedFirstReturnIndex (ω j)) (j : ℕ) :
    (feedbackConcatCellPaths ω (feedbackCellJumpOffset ω j)).2.2 = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (hτ j).ne'
      rw [feedbackCellJumpOffset_succ, feedbackCellJumpCount_eq_return _ (hτ j), hn]
      rw [show feedbackCellJumpOffset ω j + (n + 1) =
        feedbackCellJumpOffset ω j + n + 1 by omega,
        feedbackConcatCellPaths_cell_coordinate ω j n
          (by rw [feedbackCellJumpCount_eq_return _ (hτ j), hn]; omega)]
      simpa only [hn] using feedbackMarkedFirstReturnIndex_current (ω j) (hτ j)

/-- The jump direction, including a first jump after a return, is preserved by concatenation. -/
theorem feedbackConcatCellPaths_cell_jump (ω : ℕ → FeedbackCellPath)
    (hτ : ∀ j, 0 < feedbackMarkedFirstReturnIndex (ω j))
    (hstart : ∀ j, (ω j 0).2.2 = 0) (j n : ℕ)
    (hn : n < feedbackMarkedFirstReturnIndex (ω j)) :
    feedbackCellJump (feedbackConcatCellPaths ω) (feedbackCellJumpOffset ω j + n) =
      feedbackCellJump (ω j) n := by
  have hbefore : (feedbackConcatCellPaths ω (feedbackCellJumpOffset ω j + n)).2.2 =
      (ω j n).2.2 := by
    cases n with
    | zero => simpa only [Nat.add_zero, hstart j] using feedbackConcatCellPaths_offset_current ω hτ j
    | succ n => rw [Nat.add_succ, feedbackConcatCellPaths_cell_coordinate ω j n
        (by exact (by omega : n < feedbackMarkedFirstReturnIndex (ω j)).trans_le (le_max_right _ _))]
  unfold feedbackCellJump
  rw [feedbackConcatCellPaths_cell_coordinate ω j n (hn.trans_le (le_max_right _ _)), hbefore]

private theorem feedbackCellEventPoint_nonpositive_of_neg {w : FeedbackCellSequence}
    {direction : ℤ} {i : ℤ × ℕ} (hi : feedbackCellEventActive w direction i) (hj : i.1 < 0) :
    (feedbackCellEventPoint w i).1 ≤ 0 := by
  have hc := feedbackCellEventPoint_mem_cell hi
  have hm := (strictMono_feedbackCellRoot hi.1.1.1).monotone
  have hle := hm (show i.1 + 1 ≤ 0 by omega)
  rw [feedbackCellRoot_zero] at hle
  exact hc.2.trans hle

/-- The actual event-label sum equals the complete concatenated path's jump sum. A test which
vanishes at nonpositive positions removes exactly the cells lying before the observation origin. -/
theorem tsum_feedbackCellEvent_eq_concatPositive (w : FeedbackCellSequence)
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    (direction : ℤ) (t : ℝ) (ht : 0 ≤ t) (g : MatchingPoint → ℝ≥0∞)
    (hg0 : ∀ p, p.1 ≤ 0 → g p = 0) :
    (∑' i : ℤ × ℕ, if feedbackCellEventActive w direction i then
      g ((feedbackCellEventPoint w i).1 - t, (feedbackCellEventPoint w i).2) else 0) =
    ∑' m : ℕ, if feedbackCellJump (feedbackConcatPositiveCellPaths w) m = direction then
      g (feedbackCellClock (feedbackConcatPositiveCellPaths w) (m + 1) - t,
        (feedbackConcatPositiveCellPaths w (m + 1)).2.1) else 0 := by
  classical
  let ω : ℕ → FeedbackCellPath := fun j ↦ w (j : ℤ)
  let A (i : ℤ × ℕ) : ℝ≥0∞ := if feedbackCellEventActive w direction i then
    g ((feedbackCellEventPoint w i).1 - t, (feedbackCellEventPoint w i).2) else 0
  let B (m : ℕ) : ℝ≥0∞ := if feedbackCellJump (feedbackConcatPositiveCellPaths w) m = direction then
    g (feedbackCellClock (feedbackConcatPositiveCellPaths w) (m + 1) - t,
      (feedbackConcatPositiveCellPaths w (m + 1)).2.1) else 0
  have hτ : ∀ j, 0 < feedbackMarkedFirstReturnIndex (ω j) := fun j ↦ (hw.2 j).2
  have hmatch (j n : ℕ) (hn : n < feedbackMarkedFirstReturnIndex (ω j)) :
      A ((j : ℤ), n) = B (feedbackCellJumpOffset ω j + n) := by
    have hp := feedbackConcatPositiveCellPaths_cell_eventPoint w
      (fun j ↦ (hw.2 j).1) (fun j ↦ (hw.2 j).2) j n hn
    have hd := feedbackConcatCellPaths_cell_jump ω hτ (fun j ↦ hstart j) j n hn
    change feedbackCellJump (feedbackConcatPositiveCellPaths w)
      (feedbackCellJumpOffset ω j + n) = feedbackCellJump (w (j : ℤ)) n at hd
    change n < feedbackMarkedFirstReturnIndex (w (j : ℤ)) at hn
    dsimp only [A, B]
    rw [hd]
    simp only [feedbackCellEventActive, hw, hn, true_and]
    rw [← hp]
    rfl
  let idx (m : ℕ) : ℤ × ℕ :=
    ((feedbackCellJumpIndex ω m : ℕ), m - feedbackCellJumpOffset ω (feedbackCellJumpIndex ω m))
  have hidx (m : ℕ) :
      (idx m).2 < feedbackMarkedFirstReturnIndex (w (idx m).1) ∧
        m = feedbackCellJumpOffset ω (feedbackCellJumpIndex ω m) + (idx m).2 := by
    have hb := feedbackCellJumpIndex_bounds ω m
    rw [feedbackCellJumpOffset_succ, feedbackCellJumpCount_eq_return _ (hτ _)] at hb
    dsimp only [idx]
    change feedbackCellJumpOffset ω (feedbackCellJumpIndex ω m) ≤ m ∧
      m < feedbackCellJumpOffset ω (feedbackCellJumpIndex ω m) +
        feedbackMarkedFirstReturnIndex (w (feedbackCellJumpIndex ω m : ℤ)) at hb
    omega
  change (∑' i, A i) = ∑' m, B m
  apply tsum_eq_tsum_of_ne_zero_bij (fun m : Function.support B ↦ idx m)
  · intro m n heq
    have hj : feedbackCellJumpIndex ω m = feedbackCellJumpIndex ω n := by
      have he := congrArg Prod.fst heq
      change (feedbackCellJumpIndex ω m : ℤ) = (feedbackCellJumpIndex ω n : ℤ) at he
      exact_mod_cast he
    have hn := congrArg Prod.snd heq
    change (idx m).2 = (idx n).2 at hn
    apply Subtype.ext
    have hm := (hidx m).2
    have hn' := (hidx n).2
    rw [hj] at hm
    omega
  · intro i hi
    have ha : feedbackCellEventActive w direction i := by
      by_contra h
      exact hi (by simp [A, h])
    have hipos : 0 ≤ i.1 := by
      by_contra h
      have hz := feedbackCellEventPoint_nonpositive_of_neg ha (lt_of_not_ge h)
      exact hi (by simp [A, ha, hg0 ((feedbackCellEventPoint w i).1 - t, (feedbackCellEventPoint w i).2)
        (show (feedbackCellEventPoint w i).1 - t ≤ 0 by linarith)])
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hipos
    rcases i with ⟨i, n⟩
    dsimp only at hj
    subst i
    let m := feedbackCellJumpOffset ω j + n
    have hm : B m ≠ 0 := by
      rw [← hmatch j n ha.2.1]
      exact hi
    refine ⟨⟨m, hm⟩, ?_⟩
    have hind : feedbackCellJumpIndex ω m = j := by
      apply feedbackCellJumpIndex_eq_of_bounds
      · dsimp [m]; omega
      · rw [feedbackCellJumpOffset_succ, feedbackCellJumpCount_eq_return _ (hτ j)]
        dsimp [m]
        have hh := ha.2.1
        change n < feedbackMarkedFirstReturnIndex (ω j) at hh
        omega
    simp only [idx, hind, m, Nat.add_sub_cancel_left]
  · intro m
    rw [hmatch _ _ (hidx m).1, ← (hidx m).2]

/-- On the physical return roof, the holding index has the exact adjacent clock bounds. -/
theorem feedbackCellHoldingIndex_bounds (w : FeedbackCellPath)
    (hw : ∀ i, 0 < (w (i + 1)).1) (hτ : 0 < feedbackMarkedFirstReturnIndex w)
    (t : ℝ) (ht0 : 0 ≤ t) (htL : t < feedbackCellLength w) :
    feedbackCellHoldingIndex w t < feedbackMarkedFirstReturnIndex w ∧
      feedbackCellClock w (feedbackCellHoldingIndex w t) ≤ t ∧
      t < feedbackCellClock w (feedbackCellHoldingIndex w t + 1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hτ.ne'
  simp only [Nat.succ_eq_add_one] at hk
  have hterm : t < feedbackCellClock w (k + 1) := by
    rw [← hk, ← feedbackCellLength_eq_clock w hw hτ]
    exact htL
  have hex : ∃ n : ℕ, t < feedbackCellClock w (n + 1) := ⟨k, hterm⟩
  let n := Nat.find hex
  have hn : n ≤ k := Nat.find_min' hex hterm
  have hhi : t < feedbackCellClock w (n + 1) := Nat.find_spec hex
  have hlo : feedbackCellClock w n ≤ t := by
    cases hn0 : n with
    | zero => simpa only [hn0, feedbackCellClock_zero] using ht0
    | succ m =>
        exact le_of_not_gt (Nat.find_min hex (show m < Nat.find hex by change m < n; omega))
  rw [feedbackCellHoldingIndex_eq_of_clock_bounds w n t (by omega)
    (feedbackCellClock_strictMono w hw) hlo hhi]
  exact ⟨by omega, hlo, hhi⟩

/-- The current coordinates of the future follow the original jump tail, including its virtual origin. -/
theorem feedbackCellFuture_current (w : FeedbackCellPath) (t : ℝ) (m : ℕ) :
    (feedbackCellFuture w t m).2.2 = (w (feedbackCellHoldingIndex w t + m)).2.2 := by
  cases m with
  | zero => simp [feedbackMarkedVirtual]
  | succ m => cases m with
    | zero => simp [feedbackCellFuture_one]
    | succ m => simp [feedbackCellFuture_add_two, Nat.add_assoc]

/-- Arrival marks of every positive future coordinate are the original arrival marks. -/
theorem feedbackCellFuture_mark (w : FeedbackCellPath) (t : ℝ) (m : ℕ) :
    (feedbackCellFuture w t (m + 1)).2.1 =
      (w (feedbackCellHoldingIndex w t + m + 1)).2.1 := by
  cases m with
  | zero => simp [feedbackCellFuture_one]
  | succ m => simp [feedbackCellFuture_add_two, Nat.add_assoc]

/-- Jump directions of the complete future are exactly the original directions after the cut. -/
theorem feedbackCellFuture_jump (w : FeedbackCellPath) (t : ℝ) (m : ℕ) :
    feedbackCellJump (feedbackCellFuture w t) m =
      feedbackCellJump w (feedbackCellHoldingIndex w t + m) := by
  simp only [feedbackCellJump, feedbackCellFuture_current, Nat.add_assoc]

/-- Removing the jumps at or before the cut preserves every positive-position weighted jump sum. -/
theorem tsum_feedbackCellFuture (w : FeedbackCellPath) (hw : Monotone (feedbackCellClock w))
    (t : ℝ) (hlo : feedbackCellClock w (feedbackCellHoldingIndex w t) ≤ t)
    (direction : ℤ) (g : MatchingPoint → ℝ≥0∞) (hg0 : ∀ p, p.1 ≤ 0 → g p = 0) :
    (∑' m : ℕ, if feedbackCellJump w m = direction then
      g (feedbackCellClock w (m + 1) - t, (w (m + 1)).2.1) else 0) =
    ∑' m : ℕ, if feedbackCellJump (feedbackCellFuture w t) m = direction then
      g (feedbackCellClock (feedbackCellFuture w t) (m + 1),
        (feedbackCellFuture w t (m + 1)).2.1) else 0 := by
  classical
  let n := feedbackCellHoldingIndex w t
  let A (m : ℕ) : ℝ≥0∞ := if feedbackCellJump w m = direction then
    g (feedbackCellClock w (m + 1) - t, (w (m + 1)).2.1) else 0
  let B (m : ℕ) : ℝ≥0∞ := if feedbackCellJump (feedbackCellFuture w t) m = direction then
    g (feedbackCellClock (feedbackCellFuture w t) (m + 1),
      (feedbackCellFuture w t (m + 1)).2.1) else 0
  have hmatch (m : ℕ) : A (n + m) = B m := by
    simp only [A, B, feedbackCellFuture_jump, feedbackCellFuture_clock, feedbackCellFuture_mark, n]
  change (∑' m, A m) = ∑' m, B m
  apply tsum_eq_tsum_of_ne_zero_bij (fun m : Function.support B ↦ n + m)
  · intro m k h
    dsimp only at h
    apply Subtype.ext
    omega
  · intro m hm
    have hnm : n ≤ m := by
      by_contra h
      have hc := (hw (show m + 1 ≤ n by omega)).trans hlo
      have hz := hg0 (feedbackCellClock w (m + 1) - t, (w (m + 1)).2.1)
        (by dsimp only; linarith)
      exact hm (by simp [A, hz])
    have hB : B (m - n) ≠ 0 := by
      rw [← hmatch, Nat.add_sub_of_le hnm]
      exact hm
    exact ⟨⟨m - n, hB⟩, Nat.add_sub_of_le hnm⟩
  · intro m
    exact hmatch m

/-- Actual rerooted event counts against any nonnegative test supported at strictly positive
positions are the jump sum of the complete future. Both source and target directions are covered. -/
theorem lintegral_feedbackConcatenatedPoints_eq_future (w : FeedbackCellSequence)
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    (direction : ℤ) (t : ℝ) (ht0 : 0 ≤ t) (htL : t < feedbackCellLength (w 0))
    {g : MatchingPoint → ℝ≥0∞} (hg : Measurable g) (hg0 : ∀ p, p.1 ≤ 0 → g p = 0) :
    ∫⁻ p, g p ∂LocalConfiguration.countingMeasure
      (LocalConfiguration.reroot t (feedbackConcatenatedPoints direction w)) =
    ∑' m : ℕ, if feedbackCellJump (feedbackCellFuture (feedbackConcatPositiveCellPaths w) t) m = direction then
      g (feedbackCellClock (feedbackCellFuture (feedbackConcatPositiveCellPaths w) t) (m + 1),
        (feedbackCellFuture (feedbackConcatPositiveCellPaths w) t (m + 1)).2.1) else 0 := by
  rw [LocalConfiguration.countingMeasure_reroot,
    lintegral_map hg (Configuration.pointTranslation (-t)).measurable,
    countingMeasure_feedbackConcatenatedPoints, lintegral_sum_measure]
  calc
    _ = ∑' i : ℤ × ℕ, if feedbackCellEventActive w direction i then
        g ((feedbackCellEventPoint w i).1 - t, (feedbackCellEventPoint w i).2) else 0 := by
      apply tsum_congr
      intro i
      by_cases hi : feedbackCellEventActive w direction i
      · simp only [hi, ↓reduceIte, lintegral_dirac]
        congr 1
      · simp [hi]
    _ = ∑' m : ℕ, if feedbackCellJump (feedbackConcatPositiveCellPaths w) m = direction then
        g (feedbackCellClock (feedbackConcatPositiveCellPaths w) (m + 1) - t,
          (feedbackConcatPositiveCellPaths w (m + 1)).2.1) else 0 :=
      tsum_feedbackCellEvent_eq_concatPositive w hw hstart direction t ht0 g hg0
    _ = _ := by
      have hwait := feedbackConcatCellPaths_wait_pos (fun j : ℕ ↦ w (j : ℤ))
        (fun j ↦ (hw.2 j).1)
      have hret : 0 < feedbackMarkedFirstReturnIndex (feedbackConcatPositiveCellPaths w) := by
        rw [feedbackConcatPositiveCellPaths, feedbackConcatCellPaths_first_return _ (hw.2 0).2]
        exact (hw.2 0).2
      have hlen := feedbackConcatPositiveCellPaths_length w
        (fun j ↦ (hw.2 j).1) (hw.2 0).2
      have hb := feedbackCellHoldingIndex_bounds (feedbackConcatPositiveCellPaths w)
        hwait hret t ht0 (by rw [hlen]; exact htL)
      exact tsum_feedbackCellFuture _ (feedbackCellClock_strictMono _ hwait).monotone
        t hb.2.1 direction g hg0

/-- Every jump of the future read from an interior return-roof cut has strictly positive time. -/
theorem feedbackCellFuture_clock_pos (w : FeedbackCellPath)
    (hw : ∀ i, 0 < (w (i + 1)).1) (hτ : 0 < feedbackMarkedFirstReturnIndex w)
    (t : ℝ) (ht0 : 0 ≤ t) (htL : t < feedbackCellLength w) (m : ℕ) :
    0 < feedbackCellClock (feedbackCellFuture w t) (m + 1) := by
  have hb := feedbackCellHoldingIndex_bounds w hw hτ t ht0 htL
  have hc := (feedbackCellClock_strictMono w hw).monotone
    (show feedbackCellHoldingIndex w t + 1 ≤ feedbackCellHoldingIndex w t + m + 1 by omega)
  rw [feedbackCellFuture_clock]
  linarith [hb.2.2]

/-- The actual rerooted configuration on the open positive half-line is precisely the counting
measure of all marked future jumps in the chosen direction. The measure sum preserves multiplicity. -/
theorem countingMeasure_feedbackConcatenatedPoints_positive_eq_future (w : FeedbackCellSequence)
    (hw : feedbackCellConfigurationGood w) (hstart : ∀ j, (w j 0).2.2 = 0)
    (direction : ℤ) (t : ℝ) (ht0 : 0 ≤ t) (htL : t < feedbackCellLength (w 0)) :
    (LocalConfiguration.countingMeasure
      (LocalConfiguration.reroot t (feedbackConcatenatedPoints direction w))).restrict
        (Ioi (0 : ℝ) ×ˢ (univ : Set UnitMark)) =
      Measure.sum (fun m : ℕ ↦
        if feedbackCellJump (feedbackCellFuture (feedbackConcatPositiveCellPaths w) t) m = direction then
          Measure.dirac
            (feedbackCellClock (feedbackCellFuture (feedbackConcatPositiveCellPaths w) t) (m + 1),
              (feedbackCellFuture (feedbackConcatPositiveCellPaths w) t (m + 1)).2.1)
        else 0) := by
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set UnitMark)) :=
    measurableSet_Ioi.prod MeasurableSet.univ
  have hwait := feedbackConcatCellPaths_wait_pos (fun j : ℕ ↦ w (j : ℤ))
    (fun j ↦ (hw.2 j).1)
  have hret : 0 < feedbackMarkedFirstReturnIndex (feedbackConcatPositiveCellPaths w) := by
    rw [feedbackConcatPositiveCellPaths, feedbackConcatCellPaths_first_return _ (hw.2 0).2]
    exact (hw.2 0).2
  have hlen := feedbackConcatPositiveCellPaths_length w
    (fun j ↦ (hw.2 j).1) (hw.2 0).2
  have hpos (m : ℕ) :
      0 < feedbackCellClock (feedbackCellFuture (feedbackConcatPositiveCellPaths w) t) (m + 1) :=
    feedbackCellFuture_clock_pos (feedbackConcatPositiveCellPaths w) hwait hret t ht0
      (by rw [hlen]; exact htL) m
  apply Measure.ext_of_lintegral
  intro g hg
  rw [← lintegral_indicator hS,
    lintegral_feedbackConcatenatedPoints_eq_future w hw hstart direction t ht0 htL
      (hg.indicator hS) (by
        intro p hp
        apply indicator_of_notMem
        intro hpS
        exact (not_lt_of_ge hp) hpS.1), lintegral_sum_measure]
  apply tsum_congr
  intro m
  by_cases hm : feedbackCellJump (feedbackCellFuture (feedbackConcatPositiveCellPaths w) t) m = direction
  · simp only [hm, ↓reduceIte, lintegral_dirac]
    simp [hpos m]
  · simp [hm]

/-- Under the actual normalized return roof, the entire positive point measure of either event
configuration is recovered from the complete future, simultaneously for every direction. -/
theorem ae_countingMeasure_feedbackConcatenatedPoints_positive_eq_future
    (lam : ℝ) (hlam0 : 0 < lam) (hlam : lam < 1 / 2) :
    ∀ᵐ p ∂feedbackReturnRoofLaw lam hlam0 hlam, ∀ direction : ℤ,
      (LocalConfiguration.countingMeasure
        (LocalConfiguration.reroot p.2 (feedbackConcatenatedPoints direction p.1))).restrict
          (Ioi (0 : ℝ) ×ˢ (univ : Set UnitMark)) =
        Measure.sum (fun m : ℕ ↦
          if feedbackCellJump (feedbackCellFuture (feedbackConcatPositiveCellPaths p.1) p.2) m = direction then
            Measure.dirac
              (feedbackCellClock (feedbackCellFuture (feedbackConcatPositiveCellPaths p.1) p.2) (m + 1),
                (feedbackCellFuture (feedbackConcatPositiveCellPaths p.1) p.2 (m + 1)).2.1)
          else 0) := by
  unfold feedbackReturnRoofLaw
  apply Measure.ae_smul_measure
  have hroof : MeasurableSet {p : FeedbackCellSequence × ℝ |
      0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd
        (measurable_feedbackCellLength.comp ((measurable_pi_apply 0).comp measurable_fst)))
  have hbase := Measure.quasiMeasurePreserving_fst (μ := feedbackCellBase lam hlam0 hlam)
    (ν := (volume : Measure ℝ)) |>.ae (feedbackCellBase_identification_good hlam0 hlam)
  change ∀ᵐ p ∂((feedbackCellBase lam hlam0 hlam).prod volume).restrict
    {p : FeedbackCellSequence × ℝ | 0 ≤ p.2 ∧ p.2 < feedbackCellLength (p.1 0)}, _
  filter_upwards [ae_restrict_of_ae hbase, ae_restrict_mem hroof] with p hp ht direction
  exact countingMeasure_feedbackConcatenatedPoints_positive_eq_future p.1 hp.1 hp.2.2.1
    direction p.2 ht.1 ht.2

end OTSelector.Limit
