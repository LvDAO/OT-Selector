import OTSelector.Feedback.Graph

/-!
# Deterministic geometry on one affine feedback segment

The graph is affine between two successive events.  This file records the explicit source and
target crossing coordinates on such a segment.  All statements are deterministic: no stochastic
or recursive construction is used here.
-/

namespace OTSelector

/-! ## Affine segment and inverse coordinates -/

/-- The affine continuation with value `p0` at `x0` and slope `q`. -/
def segmentCurve (x0 p0 q x : ℝ) : ℝ :=
  p0 + q * (x - x0)

/-- The source inverse coordinate `x - a g(x)` on an affine segment. -/
def sourceSegmentTransform (x0 p0 q a x : ℝ) : ℝ :=
  x - a * segmentCurve x0 p0 q x

/-- The target inverse coordinate `x + b g(x)` on an affine segment. -/
def targetSegmentTransform (x0 p0 q b x : ℝ) : ℝ :=
  x + b * segmentCurve x0 p0 q x

/-- Explicit source crossing coordinate for the rank line `t + a g(x) = x`. -/
noncomputable def sourceSegmentCrossing (x0 p0 q t a : ℝ) : ℝ :=
  (t + a * (p0 - q * x0)) / (1 - a * q)

/-- Explicit target crossing coordinate for the rank line `s - b g(x) = x`. -/
noncomputable def targetSegmentCrossing (x0 p0 q s b : ℝ) : ℝ :=
  (s - b * p0 + b * q * x0) / (1 + b * q)

/-! ## Denominator bounds -/

theorem sourceSegment_denominator_pos {lam q a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    0 < 1 - a * q := by
  have hq_le : q ≤ lam := (le_abs_self q).trans hq
  have haq : a * q ≤ a * lam := mul_le_mul_of_nonneg_left hq_le ha0
  have halam : a * lam ≤ lam := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 hlam0
  have hlt : a * q < 1 := by
    have hbound : a * q ≤ lam := haq.trans halam
    linarith
  linarith

theorem targetSegment_denominator_pos {lam q b : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    0 < 1 + b * q := by
  have hb_nonneg : 0 ≤ b := le_trans (by norm_num) hb0
  have hq_lower : -lam ≤ q := neg_le_of_abs_le hq
  have hleft : b * (-lam) ≤ b * q :=
    mul_le_mul_of_nonneg_left hq_lower hb_nonneg
  have hright : b * lam ≤ 2 * lam := by
    simpa only using mul_le_mul_of_nonneg_right hb2 hlam0
  nlinarith

/-! ## Exact intersections -/

theorem sourceSegmentCrossing_intersects {lam x0 p0 q t a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    t + a * segmentCurve x0 p0 q (sourceSegmentCrossing x0 p0 q t a) =
      sourceSegmentCrossing x0 p0 q t a := by
  have hden := sourceSegment_denominator_pos ha0 ha1 hq hlam0 hlam_half
  have hden0 : 1 - a * q ≠ 0 := ne_of_gt hden
  simp only [sourceSegmentCrossing, segmentCurve]
  field_simp [hden0]
  ring

theorem targetSegmentCrossing_intersects {lam x0 p0 q s b : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    s - b * segmentCurve x0 p0 q (targetSegmentCrossing x0 p0 q s b) =
      targetSegmentCrossing x0 p0 q s b := by
  have hden := targetSegment_denominator_pos hb0 hb2 hq hlam0 hlam_half
  have hden0 : 1 + b * q ≠ 0 := ne_of_gt hden
  simp only [targetSegmentCrossing, segmentCurve]
  field_simp [hden0]
  ring

/-! ## Future-coordinate characterizations -/

theorem x_lt_sourceSegmentCrossing_iff {lam x0 p0 q t a x : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    x < sourceSegmentCrossing x0 p0 q t a ↔
      x < t + a * segmentCurve x0 p0 q x := by
  have hden := sourceSegment_denominator_pos ha0 ha1 hq hlam0 hlam_half
  rw [sourceSegmentCrossing, lt_div_iff₀ hden]
  simp only [segmentCurve]
  constructor <;> intro h <;> nlinarith [h]

theorem x_le_sourceSegmentCrossing_iff {lam x0 p0 q t a x : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    x ≤ sourceSegmentCrossing x0 p0 q t a ↔
      x ≤ t + a * segmentCurve x0 p0 q x := by
  have hden := sourceSegment_denominator_pos ha0 ha1 hq hlam0 hlam_half
  rw [sourceSegmentCrossing, le_div_iff₀ hden]
  simp only [segmentCurve]
  constructor <;> intro h <;> nlinarith [h]

theorem x_lt_targetSegmentCrossing_iff {lam x0 p0 q s b x : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    x < targetSegmentCrossing x0 p0 q s b ↔
      x < s - b * segmentCurve x0 p0 q x := by
  have hden := targetSegment_denominator_pos hb0 hb2 hq hlam0 hlam_half
  rw [targetSegmentCrossing, lt_div_iff₀ hden]
  simp only [segmentCurve]
  constructor <;> intro h <;> nlinarith [h]

theorem x_le_targetSegmentCrossing_iff {lam x0 p0 q s b x : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    x ≤ targetSegmentCrossing x0 p0 q s b ↔
      x ≤ s - b * segmentCurve x0 p0 q x := by
  have hden := targetSegment_denominator_pos hb0 hb2 hq hlam0 hlam_half
  rw [targetSegmentCrossing, le_div_iff₀ hden]
  simp only [segmentCurve]
  constructor <;> intro h <;> nlinarith [h]

theorem x0_lt_sourceSegmentCrossing_iff {lam x0 p0 q t a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    x0 < sourceSegmentCrossing x0 p0 q t a ↔ x0 < t + a * p0 := by
  simpa [segmentCurve] using
    (x_lt_sourceSegmentCrossing_iff (lam := lam) (x0 := x0) (p0 := p0)
      (q := q) (t := t) (a := a) (x := x0) ha0 ha1 hq hlam0 hlam_half)

theorem x0_le_sourceSegmentCrossing_iff {lam x0 p0 q t a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    x0 ≤ sourceSegmentCrossing x0 p0 q t a ↔ x0 ≤ t + a * p0 := by
  simpa [segmentCurve] using
    (x_le_sourceSegmentCrossing_iff (lam := lam) (x0 := x0) (p0 := p0)
      (q := q) (t := t) (a := a) (x := x0) ha0 ha1 hq hlam0 hlam_half)

theorem x0_lt_targetSegmentCrossing_iff {lam x0 p0 q s b : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    x0 < targetSegmentCrossing x0 p0 q s b ↔ x0 < s - b * p0 := by
  simpa [segmentCurve] using
    (x_lt_targetSegmentCrossing_iff (lam := lam) (x0 := x0) (p0 := p0)
      (q := q) (s := s) (b := b) (x := x0) hb0 hb2 hq hlam0 hlam_half)

theorem x0_le_targetSegmentCrossing_iff {lam x0 p0 q s b : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    x0 ≤ targetSegmentCrossing x0 p0 q s b ↔ x0 ≤ s - b * p0 := by
  simpa [segmentCurve] using
    (x_le_targetSegmentCrossing_iff (lam := lam) (x0 := x0) (p0 := p0)
      (q := q) (s := s) (b := b) (x := x0) hb0 hb2 hq hlam0 hlam_half)

/-! ## Uniqueness and strict monotonicity -/

theorem sourceSegmentCrossing_unique {lam x0 p0 q t a x : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2)
    (hx : t + a * segmentCurve x0 p0 q x = x) :
    x = sourceSegmentCrossing x0 p0 q t a := by
  have hden := sourceSegment_denominator_pos ha0 ha1 hq hlam0 hlam_half
  have hden0 : 1 - a * q ≠ 0 := ne_of_gt hden
  rw [sourceSegmentCrossing]
  apply (eq_div_iff hden0).2
  dsimp [segmentCurve] at hx
  nlinarith [hx]

theorem targetSegmentCrossing_unique {lam x0 p0 q s b x : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2)
    (hx : s - b * segmentCurve x0 p0 q x = x) :
    x = targetSegmentCrossing x0 p0 q s b := by
  have hden := targetSegment_denominator_pos hb0 hb2 hq hlam0 hlam_half
  have hden0 : 1 + b * q ≠ 0 := ne_of_gt hden
  rw [targetSegmentCrossing]
  apply (eq_div_iff hden0).2
  dsimp [segmentCurve] at hx
  nlinarith [hx]

private theorem sourceSegmentTransform_sub {x0 p0 q a x y : ℝ} :
    sourceSegmentTransform x0 p0 q a y - sourceSegmentTransform x0 p0 q a x =
      (1 - a * q) * (y - x) := by
  dsimp [sourceSegmentTransform, segmentCurve]
  ring

private theorem targetSegmentTransform_sub {x0 p0 q b x y : ℝ} :
    targetSegmentTransform x0 p0 q b y - targetSegmentTransform x0 p0 q b x =
      (1 + b * q) * (y - x) := by
  dsimp [targetSegmentTransform, segmentCurve]
  ring

theorem sourceSegmentTransform_strictMono_of_pos {x0 p0 q a : ℝ}
    (hden : 0 < 1 - a * q) :
    StrictMono (sourceSegmentTransform x0 p0 q a) := by
  intro x y hxy
  rw [← sub_pos] at hxy ⊢
  rw [sourceSegmentTransform_sub]
  exact mul_pos hden hxy

theorem targetSegmentTransform_strictMono_of_pos {x0 p0 q b : ℝ}
    (hden : 0 < 1 + b * q) :
    StrictMono (targetSegmentTransform x0 p0 q b) := by
  intro x y hxy
  rw [← sub_pos] at hxy ⊢
  rw [targetSegmentTransform_sub]
  exact mul_pos hden hxy

theorem sourceSegmentTransform_strictMono {lam x0 p0 q a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    StrictMono (sourceSegmentTransform x0 p0 q a) :=
  sourceSegmentTransform_strictMono_of_pos
    (sourceSegment_denominator_pos ha0 ha1 hq hlam0 hlam_half)

theorem targetSegmentTransform_strictMono {lam x0 p0 q b : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    StrictMono (targetSegmentTransform x0 p0 q b) :=
  targetSegmentTransform_strictMono_of_pos
    (targetSegment_denominator_pos hb0 hb2 hq hlam0 hlam_half)

end OTSelector
