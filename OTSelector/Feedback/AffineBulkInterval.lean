import OTSelector.Feedback.FeedbackBulkMask

/-!
# Bulk intervals on one affine feedback segment

For a fixed state the height is affine in the coordinate.  Consequently the bulk strip is an
interval in that coordinate.  This file makes the endpoints explicit.  The bulk strip is closed,
so its intersection with an `Ioc` interval is in general a half-closed interval rather than an
`Ioc` interval; the exact intersection and the useful `Ioc` special case are recorded below.
-/

open MeasureTheory Set
open scoped Classical

namespace OTSelector

/-! ## Explicit affine endpoints -/

set_option linter.unusedVariables false in
/-- Lower endpoint of the bulk part of an affine continuation. -/
noncomputable def feedbackBulkSegmentLower
    (n : ℕ) (B x0 p0 q : ℝ) : ℝ :=
  if _hq : 0 < q then
    max B (x0 + (-B / 8 - p0) / q)
  else if _hq : q < 0 then
    max B (x0 + (B / 8 - p0) / q)
  else if |p0| ≤ B / 8 then
    B
  else
    1

/-- Upper endpoint of the bulk part of an affine continuation. -/
noncomputable def feedbackBulkSegmentUpper
    (n : ℕ) (B x0 p0 q : ℝ) : ℝ :=
  if _hq : 0 < q then
    min ((n : ℝ) - B) (x0 + (B / 8 - p0) / q)
  else if _hq : q < 0 then
    min ((n : ℝ) - B) (x0 + (-B / 8 - p0) / q)
  else if |p0| ≤ B / 8 then
    (n : ℝ) - B
  else
    0

private theorem segmentCurve_eq_affine
    (x0 p0 q y : ℝ) :
    segmentCurve x0 p0 q y = p0 + q * (y - x0) := rfl

private theorem affine_bulk_iff_of_pos
    {n : ℕ} {B x0 p0 q y : ℝ} (hq : 0 < q) :
    feedbackBulkRegion n B y (segmentCurve x0 p0 q y) ↔
      y ∈ Icc
        (max B (x0 + (-B / 8 - p0) / q))
        (min ((n : ℝ) - B) (x0 + (B / 8 - p0) / q)) := by
  rw [feedbackBulkRegion]
  constructor
  · rintro ⟨hyB, hyN, hp⟩
    have hp' := abs_le.mp hp
    have hlow : x0 + (-B / 8 - p0) / q ≤ y := by
      have hmul : -B / 8 - p0 ≤ (y - x0) * q := by
        have hp1 : -(B / 8) ≤ p0 + q * (y - x0) := by
          simpa [segmentCurve] using hp'.1
        nlinarith [hp1]
      have hdiv : (-B / 8 - p0) / q ≤ y - x0 := (div_le_iff₀ hq).2 hmul
      linarith
    have hupp : y ≤ x0 + (B / 8 - p0) / q := by
      have hmul : (y - x0) * q ≤ B / 8 - p0 := by
        have hp2 : p0 + q * (y - x0) ≤ B / 8 := by
          simpa [segmentCurve] using hp'.2
        nlinarith [hp2]
      have hdiv : y - x0 ≤ (B / 8 - p0) / q := (le_div_iff₀ hq).2 hmul
      linarith
    constructor
    · exact (max_le_iff.mpr ⟨hyB, hlow⟩)
    · exact (le_min_iff.mpr ⟨hyN, hupp⟩)
  · intro hy
    have hyB : B ≤ y :=
      le_trans (le_max_left _ _) hy.1
    have hyN : y ≤ (n : ℝ) - B :=
      le_trans hy.2 (min_le_left _ _)
    have hlow : x0 + (-B / 8 - p0) / q ≤ y :=
      le_trans (le_max_right _ _) hy.1
    have hupp : y ≤ x0 + (B / 8 - p0) / q :=
      le_trans hy.2 (min_le_right _ _)
    have hlow' : -B / 8 - p0 ≤ (y - x0) * q :=
      (div_le_iff₀ hq).1 (by linarith : (-B / 8 - p0) / q ≤ y - x0)
    have hupp' : (y - x0) * q ≤ B / 8 - p0 :=
      (le_div_iff₀ hq).1 (by linarith : y - x0 ≤ (B / 8 - p0) / q)
    refine ⟨hyB, hyN, ?_⟩
    rw [abs_le]
    constructor
    · change -(B / 8) ≤ p0 + q * (y - x0)
      nlinarith [hlow']
    · change p0 + q * (y - x0) ≤ B / 8
      nlinarith [hupp']

private theorem affine_bulk_iff_of_neg
    {n : ℕ} {B x0 p0 q y : ℝ} (hq : q < 0) :
    feedbackBulkRegion n B y (segmentCurve x0 p0 q y) ↔
      y ∈ Icc
        (max B (x0 + (B / 8 - p0) / q))
        (min ((n : ℝ) - B) (x0 + (-B / 8 - p0) / q)) := by
  rw [feedbackBulkRegion]
  constructor
  · rintro ⟨hyB, hyN, hp⟩
    have hp' := abs_le.mp hp
    have hlow : x0 + (B / 8 - p0) / q ≤ y := by
      have hmul : (y - x0) * q ≤ B / 8 - p0 := by
        have hp2 : p0 + q * (y - x0) ≤ B / 8 := by
          simpa [segmentCurve] using hp'.2
        nlinarith [hp2]
      have hdiv : (B / 8 - p0) / q ≤ y - x0 := (div_le_iff_of_neg hq).2 hmul
      linarith
    have hupp : y ≤ x0 + (-B / 8 - p0) / q := by
      have hmul : -B / 8 - p0 ≤ (y - x0) * q := by
        have hp1 : -(B / 8) ≤ p0 + q * (y - x0) := by
          simpa [segmentCurve] using hp'.1
        nlinarith [hp1]
      have hdiv : y - x0 ≤ (-B / 8 - p0) / q := (le_div_iff_of_neg hq).2 hmul
      linarith
    constructor
    · exact (max_le_iff.mpr ⟨hyB, hlow⟩)
    · exact (le_min_iff.mpr ⟨hyN, hupp⟩)
  · intro hy
    have hyB : B ≤ y :=
      le_trans (le_max_left _ _) hy.1
    have hyN : y ≤ (n : ℝ) - B :=
      le_trans hy.2 (min_le_left _ _)
    have hlow : x0 + (B / 8 - p0) / q ≤ y :=
      le_trans (le_max_right _ _) hy.1
    have hupp : y ≤ x0 + (-B / 8 - p0) / q :=
      le_trans hy.2 (min_le_right _ _)
    have hlow' : (y - x0) * q ≤ B / 8 - p0 :=
      (div_le_iff_of_neg hq).1 (by linarith : (B / 8 - p0) / q ≤ y - x0)
    have hupp' : -B / 8 - p0 ≤ (y - x0) * q :=
      (le_div_iff_of_neg hq).1 (by linarith : y - x0 ≤ (-B / 8 - p0) / q)
    refine ⟨hyB, hyN, ?_⟩
    rw [abs_le]
    constructor
    · change -(B / 8) ≤ p0 + q * (y - x0)
      nlinarith [hupp']
    · change p0 + q * (y - x0) ≤ B / 8
      nlinarith [hlow']

private theorem affine_bulk_iff_of_zero
    {n : ℕ} {B x0 p0 q y : ℝ} (hq : q = 0) :
    feedbackBulkRegion n B y (segmentCurve x0 p0 q y) ↔
      (if |p0| ≤ B / 8 then y ∈ Icc B ((n : ℝ) - B) else y ∈ Icc 1 0) := by
  subst q
  by_cases hp : |p0| ≤ B / 8
  · simp [feedbackBulkRegion, segmentCurve, hp]
  · simp [feedbackBulkRegion, segmentCurve, hp]

/-! ## Interval characterization -/

set_option linter.unusedVariables false in
theorem feedbackBulkRegion_segment_iff_mem_Icc
    {n : ℕ} {B x0 p0 q y : ℝ} (hB : 0 < B) :
    feedbackBulkRegion n B y (segmentCurve x0 p0 q y) ↔
      y ∈ Icc
        (feedbackBulkSegmentLower n B x0 p0 q)
        (feedbackBulkSegmentUpper n B x0 p0 q) := by
  by_cases hq : 0 < q
  · simpa [feedbackBulkSegmentLower, feedbackBulkSegmentUpper, hq] using
      (affine_bulk_iff_of_pos (n := n) (B := B) (x0 := x0) (p0 := p0)
        (q := q) (y := y) hq)
  · by_cases hq' : q < 0
    · simpa [feedbackBulkSegmentLower, feedbackBulkSegmentUpper, hq, hq'] using
        (affine_bulk_iff_of_neg (n := n) (B := B) (x0 := x0) (p0 := p0)
          (q := q) (y := y) hq')
    · have hq0 : q = 0 := by
        exact le_antisymm (le_of_not_gt hq) (le_of_not_gt hq')
      subst q
      by_cases hp : |p0| ≤ B / 8
      · simp [feedbackBulkSegmentLower, feedbackBulkSegmentUpper, hp,
          feedbackBulkRegion, segmentCurve]
      · simp [feedbackBulkSegmentLower, feedbackBulkSegmentUpper, hp,
          feedbackBulkRegion, segmentCurve]

theorem feedbackBulkRegion_segment_mem_Icc
    {n : ℕ} {B x0 p0 q y : ℝ} (hB : 0 < B)
    (hy : y ∈ Icc
      (feedbackBulkSegmentLower n B x0 p0 q)
      (feedbackBulkSegmentUpper n B x0 p0 q)) :
    feedbackBulkRegion n B y (segmentCurve x0 p0 q y) :=
  (feedbackBulkRegion_segment_iff_mem_Icc hB).2 hy

/-! ## Rank-strip bounds on the interval -/

theorem feedbackBulkRegion_segment_boundary_bounds
    {n : ℕ} {B x0 p0 q y : ℝ} (hB : 0 < B)
    (hy : y ∈ Icc
      (feedbackBulkSegmentLower n B x0 p0 q)
      (feedbackBulkSegmentUpper n B x0 p0 q)) :
    (∀ u : UnitMark,
      0 ≤ sourceBoundary (segmentCurve x0 p0 q y) y u ∧
        sourceBoundary (segmentCurve x0 p0 q y) y u ≤ n) ∧
    (∀ v : UnitMark,
      0 ≤ targetBoundary (segmentCurve x0 p0 q y) y v ∧
        targetBoundary (segmentCurve x0 p0 q y) y v ≤ n) := by
  have hbulk := feedbackBulkRegion_segment_mem_Icc hB hy
  constructor
  · intro u
    exact ⟨le_of_lt (feedbackBulkRegion_sourceBoundary_pos hB hbulk u),
      (feedbackBulkRegion_sourceBoundary_lt hB hbulk u).le⟩
  · intro v
    exact ⟨le_of_lt (feedbackBulkRegion_targetBoundary_pos hB hbulk v),
      (feedbackBulkRegion_targetBoundary_lt hB hbulk v).le⟩

/-! ## Intersections with time slabs -/

theorem feedbackBulkRegion_segment_inter_Ioc_eq
    {n : ℕ} {B x0 p0 q a b : ℝ} (hB : 0 < B) :
    {y : ℝ | feedbackBulkRegion n B y (segmentCurve x0 p0 q y)} ∩ Ioc a b =
      Icc (feedbackBulkSegmentLower n B x0 p0 q)
        (feedbackBulkSegmentUpper n B x0 p0 q) ∩ Ioc a b := by
  ext y
  change (feedbackBulkRegion n B y (segmentCurve x0 p0 q y) ∧ y ∈ Ioc a b) ↔
    (y ∈ Icc (feedbackBulkSegmentLower n B x0 p0 q)
      (feedbackBulkSegmentUpper n B x0 p0 q) ∧ y ∈ Ioc a b)
  rw [feedbackBulkRegion_segment_iff_mem_Icc hB]

/-- If the lower bulk boundary is already before the slab, the intersection is an `Ioc`. -/
theorem feedbackBulkRegion_segment_inter_Ioc_eq_Ioc_of_lower_le
    {n : ℕ} {B x0 p0 q a b : ℝ} (hB : 0 < B)
    (hlower : feedbackBulkSegmentLower n B x0 p0 q ≤ a) :
    {y : ℝ | feedbackBulkRegion n B y (segmentCurve x0 p0 q y)} ∩ Ioc a b =
      Ioc a (min b (feedbackBulkSegmentUpper n B x0 p0 q)) := by
  ext y
  change (feedbackBulkRegion n B y (segmentCurve x0 p0 q y) ∧ y ∈ Ioc a b) ↔
    y ∈ Ioc a (min b (feedbackBulkSegmentUpper n B x0 p0 q))
  rw [feedbackBulkRegion_segment_iff_mem_Icc hB]
  constructor
  · rintro ⟨hybulk, hyab⟩
    rcases hybulk with ⟨hly, hyu⟩
    rcases hyab with ⟨hya, hyb⟩
    exact ⟨hya, le_min hyb hyu⟩
  · intro hy
    rcases hy with ⟨hya, hyb⟩
    have hya' : feedbackBulkSegmentLower n B x0 p0 q ≤ y :=
      le_trans hlower (le_of_lt hya)
    have hyb' := le_min_iff.mp hyb
    exact ⟨⟨hya', hyb'.2⟩, ⟨hya, hyb'.1⟩⟩

/-! ## State-level names used by the adaptive proof -/

noncomputable def feedbackBulkStateLower
    {n : ℕ} (B : ℝ) (lam : ℝ) (state : FeedbackStepState n) : ℝ :=
  feedbackBulkSegmentLower n B state.x state.p (state.slope lam)

noncomputable def feedbackBulkStateUpper
    {n : ℕ} (B : ℝ) (lam : ℝ) (state : FeedbackStepState n) : ℝ :=
  feedbackBulkSegmentUpper n B state.x state.p (state.slope lam)

theorem feedbackBulkRegion_state_iff_mem_Icc
    {n : ℕ} {B lam y : ℝ} (state : FeedbackStepState n) (hB : 0 < B) :
    feedbackBulkRegion n B y
        (segmentCurve state.x state.p (state.slope lam) y) ↔
      y ∈ Icc (feedbackBulkStateLower B lam state)
        (feedbackBulkStateUpper B lam state) := by
  exact feedbackBulkRegion_segment_iff_mem_Icc hB

theorem feedbackBulkState_boundary_bounds
    {n : ℕ} {B lam y : ℝ} (state : FeedbackStepState n) (hB : 0 < B)
    (hy : y ∈ Icc (feedbackBulkStateLower B lam state)
      (feedbackBulkStateUpper B lam state)) :
    (∀ u : UnitMark,
      0 ≤ sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ∧
        sourceBoundary (segmentCurve state.x state.p (state.slope lam) y) y u ≤ n) ∧
    (∀ v : UnitMark,
      0 ≤ targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ∧
        targetBoundary (segmentCurve state.x state.p (state.slope lam) y) y v ≤ n) := by
  exact feedbackBulkRegion_segment_boundary_bounds hB hy

theorem feedbackBulkRegion_segment_nonempty_iff
    {n : ℕ} {B x0 p0 q : ℝ} (hB : 0 < B) :
    ({y : ℝ | feedbackBulkRegion n B y (segmentCurve x0 p0 q y)}).Nonempty ↔
      feedbackBulkSegmentLower n B x0 p0 q ≤
        feedbackBulkSegmentUpper n B x0 p0 q := by
  rw [show {y : ℝ | feedbackBulkRegion n B y (segmentCurve x0 p0 q y)} =
      Icc (feedbackBulkSegmentLower n B x0 p0 q)
        (feedbackBulkSegmentUpper n B x0 p0 q) by
    ext y
    exact feedbackBulkRegion_segment_iff_mem_Icc hB]
  exact nonempty_Icc

end OTSelector
