import OTSelector.Limit.FeedbackCellTrajectory
import OTSelector.Limit.FeedbackCellGeometry
import OTSelector.Limit.FeedbackCellConcatenation
import OTSelector.Limit.FeedbackStationaryFutureHolding

/-!
# Reading a future from the actual cell occupation construction

Positive cells are concatenated in their real jump order. The first-return interval of the
resulting infinite path is exactly the distinguished cell roof. Inside that interval a finite
clock count determines the current holding segment.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace OTSelector.Limit

attribute [local instance] Classical.propDecidable

/-- Before the first return, concatenation reads precisely the first cell's real jumps. -/
theorem feedbackConcatCellPaths_first_cell_coordinate (ω : ℕ → FeedbackCellPath)
    (n : ℕ) (hn : n < feedbackMarkedFirstReturnIndex (ω 0)) :
    feedbackConcatCellPaths ω (n + 1) = ω 0 (n + 1) := by
  have hi : feedbackCellJumpIndex ω n = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Nat.find_min'
    simp only [feedbackCellJumpOffset_succ, feedbackCellJumpOffset_zero, zero_add]
    exact hn.trans_le (le_max_right _ _)
  simp only [feedbackConcatCellPaths, hi, feedbackCellJumpOffset_zero, Nat.sub_zero]

/-- The first return of the positive concatenation is the first return of the distinguished cell. -/
theorem feedbackConcatCellPaths_first_return (ω : ℕ → FeedbackCellPath)
    (hτ : 0 < feedbackMarkedFirstReturnIndex (ω 0)) :
    feedbackMarkedFirstReturnIndex (feedbackConcatCellPaths ω) =
      feedbackMarkedFirstReturnIndex (ω 0) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hτ)
  rw [hn, feedbackMarkedFirstReturnIndex_eq_succ_iff]
  have hfirst := (feedbackMarkedFirstReturnIndex_eq_succ_iff (ω 0) n).mp hn
  constructor
  · rw [feedbackConcatCellPaths_first_cell_coordinate ω n (by omega)]
    exact hfirst.1
  · intro j hj
    rw [feedbackConcatCellPaths_first_cell_coordinate ω j (by omega)]
    exact hfirst.2 j hj

/-- Concatenation preserves positivity of all holding times. -/
theorem feedbackConcatCellPaths_wait_pos (ω : ℕ → FeedbackCellPath)
    (hw : ∀ j n, 0 < (ω j (n + 1)).1) :
    ∀ n, 0 < (feedbackConcatCellPaths ω (n + 1)).1 := by
  intro n
  have hb := (feedbackCellJumpIndex_local_bounds ω n).1
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  simp only [feedbackConcatCellPaths, hm]
  exact hw _ m

/-- The clocks of the first cell are unchanged by subsequent cell concatenation. -/
theorem feedbackConcatCellPaths_first_cell_clock (ω : ℕ → FeedbackCellPath)
    (n : ℕ) (hn : n ≤ feedbackMarkedFirstReturnIndex (ω 0)) :
    feedbackCellClock (feedbackConcatCellPaths ω) n = feedbackCellClock (ω 0) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [feedbackCellClock_succ, feedbackCellClock_succ, ih (by omega),
        feedbackConcatCellPaths_first_cell_coordinate ω n (by omega)]

/-- The literal occupation roof is preserved by the positive path assembly. -/
theorem feedbackConcatPositiveCellPaths_length (ω : FeedbackCellSequence)
    (hw : ∀ j : ℤ, ∀ n, 0 < (ω j (n + 1)).1)
    (hτ : 0 < feedbackMarkedFirstReturnIndex (ω 0)) :
    feedbackCellLength (feedbackConcatPositiveCellPaths ω) = feedbackCellLength (ω 0) := by
  let v : ℕ → FeedbackCellPath := fun j ↦ ω (j : ℤ)
  have hr := feedbackConcatCellPaths_first_return v hτ
  change feedbackCellLength (feedbackConcatCellPaths v) = feedbackCellLength (ω 0)
  rw [feedbackCellLength_eq_clock _ (feedbackConcatCellPaths_wait_pos v (fun j ↦ hw j))
    (by rw [hr]; exact hτ), hr,
    feedbackConcatCellPaths_first_cell_clock v _ le_rfl]
  simpa only [v, Int.natCast_zero] using
    (feedbackCellLength_eq_clock (ω 0) (hw 0) hτ).symm

/-- Number of cell jumps at or before a cut; on the cell roof this is its holding-segment index. -/
noncomputable def feedbackCellHoldingIndex (w : FeedbackCellPath) (t : ℝ) : ℕ :=
  ∑ i ∈ Finset.range (feedbackMarkedFirstReturnIndex w),
    if feedbackCellClock w (i + 1) ≤ t then 1 else 0

private theorem measurable_feedbackCellHoldingIndex_partial :
    Measurable (fun p : (FeedbackCellPath × ℝ) × ℕ ↦
      ∑ i ∈ Finset.range p.2, if feedbackCellClock p.1.1 (i + 1) ≤ p.1.2 then 1 else 0) := by
  apply measurable_from_prod_countable_left
  intro n
  dsimp only
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.ite
    (measurableSet_le ((measurable_feedbackCellClock (i + 1)).comp measurable_fst)
      measurable_snd) measurable_const

@[fun_prop]
theorem measurable_feedbackCellHoldingIndex :
    Measurable (fun p : FeedbackCellPath × ℝ ↦ feedbackCellHoldingIndex p.1 p.2) :=
  measurable_feedbackCellHoldingIndex_partial.comp
    (f := fun p : FeedbackCellPath × ℝ ↦ (p, feedbackMarkedFirstReturnIndex p.1))
    (measurable_id.prodMk (measurable_feedbackMarkedFirstReturnIndex.comp measurable_fst))

/-- Consecutive clock bounds determine the holding index exactly. -/
theorem feedbackCellHoldingIndex_eq_of_clock_bounds (w : FeedbackCellPath) (n : ℕ) (t : ℝ)
    (hn : n ≤ feedbackMarkedFirstReturnIndex w) (hclock : StrictMono (feedbackCellClock w))
    (hlo : feedbackCellClock w n ≤ t) (hhi : t < feedbackCellClock w (n + 1)) :
    feedbackCellHoldingIndex w t = n := by
  have hsplit (i : ℕ) : feedbackCellClock w (i + 1) ≤ t ↔ i < n := by
    constructor
    · intro h
      by_contra hni
      have hh := hclock.monotone (Nat.add_le_add_right (Nat.le_of_not_gt hni) 1)
      linarith
    · intro h
      exact (hclock.monotone (Nat.succ_le_iff.mpr h)).trans hlo
  simp_rw [feedbackCellHoldingIndex, hsplit]
  have heq : (∑ i ∈ Finset.range (feedbackMarkedFirstReturnIndex w),
      if i < n then (1 : ℕ) else 0) = ∑ i ∈ Finset.range n, 1 := by
    calc
      _ = ∑ i ∈ Finset.range n, if i < n then (1 : ℕ) else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono hn)
        intro i hi hin
        simp only [Finset.mem_range] at hin
        simp only [hin, ↓reduceIte]
      _ = _ := Finset.sum_congr rfl fun i hi ↦ ite_eq_left (Finset.mem_range.mp hi)
  simpa using heq

/-- The complete future at a cut in the distinguished cell. Only the unspent first wait changes;
all later jumps are read from the infinite concatenated marked path. -/
noncomputable def feedbackCellFuture (w : FeedbackCellPath) (t : ℝ) : FeedbackCellPath :=
  feedbackMarkedResidual (feedbackMarkedRestart (feedbackCellHoldingIndex w t) w)
    (t - feedbackCellClock w (feedbackCellHoldingIndex w t))

private theorem measurable_feedbackCellFuture_indexed :
    Measurable (fun p : (FeedbackCellPath × ℝ) × ℕ ↦
      feedbackMarkedResidual (feedbackMarkedRestart p.2 p.1.1)
        (p.1.2 - feedbackCellClock p.1.1 p.2)) := by
  apply measurable_from_prod_countable_left
  intro n
  exact measurable_feedbackMarkedResidual.comp
    (((measurable_feedbackMarkedRestart n).comp measurable_fst).prodMk
      (measurable_snd.sub ((measurable_feedbackCellClock n).comp measurable_fst)))

@[fun_prop]
theorem measurable_feedbackCellFuture :
    Measurable (fun p : FeedbackCellPath × ℝ ↦ feedbackCellFuture p.1 p.2) :=
  measurable_feedbackCellFuture_indexed.comp
    (f := fun p : FeedbackCellPath × ℝ ↦ (p, feedbackCellHoldingIndex p.1 p.2))
    (measurable_id.prodMk measurable_feedbackCellHoldingIndex)

@[simp]
theorem feedbackCellFuture_zero (w : FeedbackCellPath) (t : ℝ) :
    feedbackCellFuture w t 0 = feedbackMarkedVirtual (w (feedbackCellHoldingIndex w t)).2.2 := by
  simp [feedbackCellFuture]

private theorem lintegral_Ico_sub_translate {f : ℝ → ℝ≥0∞} (hf : Measurable f) (a b : ℝ) :
    (∫⁻ x in Ico a (a + b), f (x - a)) = ∫⁻ u in Ico 0 b, f u := by
  have hm : Measurable ((Ico a (a + b)).indicator (fun x ↦ f (x - a))) :=
    (hf.comp (measurable_id.sub measurable_const)).indicator measurableSet_Ico
  rw [← lintegral_indicator measurableSet_Ico,
    ← (measurePreserving_add_right (volume : Measure ℝ) a).lintegral_comp hm]
  have heq : (fun u ↦ (Ico a (a + b)).indicator (fun x ↦ f (x - a)) (u + a)) =
      (Ico 0 b).indicator f := by
    funext u
    have hmem : u + a ∈ Ico a (a + b) ↔ u ∈ Ico 0 b := by
      simp only [mem_Ico]
      constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
    simp only [Set.indicator_apply, hmem, add_sub_cancel_right]
  rw [heq, lintegral_indicator measurableSet_Ico]

/-- The literal cell-roof integral splits into its actual holding segments, retaining the
entire marked future at each observation point. -/
theorem lintegral_feedbackCellFuture_eq_holding_sum (w : FeedbackCellPath) (k : ℤ)
    (hw : ∀ i, 0 < (w (i + 1)).1) (ht : 0 < feedbackMarkedFirstReturnIndex w)
    (hstart : (w 0).2.2 = 0) {f : FeedbackCellPath → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t in Ico 0 (feedbackCellLength w),
      if feedbackCellCurrent w t = k then f (feedbackCellFuture w t) else 0) =
    ∑' n : ℕ, if n < feedbackMarkedFirstReturnIndex w ∧ (w n).2.2 = k then
      ∫⁻ a in Ico 0 (w (n + 1)).1,
        f (feedbackMarkedResidual (feedbackMarkedRestart n w) a) else 0 := by
  have hc := feedbackCellClock_strictMono w hw
  have hu : (⋃ n ∈ Finset.range (feedbackMarkedFirstReturnIndex w),
      Ico (feedbackCellClock w n) (feedbackCellClock w (n + 1))) =
        Ico 0 (feedbackCellLength w) := by
    rw [feedbackCellLength_eq_clock w hw ht, ← feedbackCellClock_zero w]
    apply le_antisymm
    · apply iUnion_subset
      intro n
      apply iUnion_subset
      intro hn
      exact Ico_subset_Ico (hc.monotone (Nat.zero_le _))
        (hc.monotone (Nat.succ_le_of_lt (Finset.mem_range.mp hn)))
    · exact Ico_subset_biUnion_Ico _ _
  have hd : Set.PairwiseDisjoint (↑(Finset.range (feedbackMarkedFirstReturnIndex w)) : Set ℕ)
      (fun n ↦ Ico (feedbackCellClock w n) (feedbackCellClock w (n + 1))) := by
    intro n hn m hm hnm
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hnm with h | h
    · have hh := hc.monotone (Nat.succ_le_of_lt h)
      linarith [hx.2, hy.1]
    · have hh := hc.monotone (Nat.succ_le_of_lt h)
      linarith [hy.2, hx.1]
  rw [← hu, lintegral_biUnion_finset hd (fun _ _ ↦ measurableSet_Ico),
    tsum_eq_sum (s := Finset.range (feedbackMarkedFirstReturnIndex w))
      (fun n hn ↦ by simp only [Finset.mem_range] at hn; simp [hn])]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_range.mp hn
  have heq : (fun t ↦ if feedbackCellCurrent w t = k then f (feedbackCellFuture w t) else 0) =ᵐ[
      volume.restrict (Ico (feedbackCellClock w n) (feedbackCellClock w (n + 1)))]
      (fun t ↦ if (w n).2.2 = k then
        f (feedbackMarkedResidual (feedbackMarkedRestart n w) (t - feedbackCellClock w n)) else 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    rw [feedbackCellCurrent_eq_of_clock_bounds w n t hn'.le hstart hc ht.1 ht.2]
    simp only [feedbackCellFuture,
      feedbackCellHoldingIndex_eq_of_clock_bounds w n t hn'.le hc ht.1 ht.2]
  rw [lintegral_congr_ae heq]
  by_cases hk : (w n).2.2 = k
  · simp only [hk, hn', and_self, ↓reduceIte]
    rw [feedbackCellClock_succ]
    exact lintegral_Ico_sub_translate
      (f := fun a ↦ f (feedbackMarkedResidual (feedbackMarkedRestart n w) a))
      (hf.comp (measurable_feedbackMarkedResidual.comp measurable_prodMk_left)) _ _
  · simp [hk]

end OTSelector.Limit
