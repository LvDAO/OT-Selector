import OTSelector.Feedback.FeedbackStep
import OTSelector.Feedback.RateBounds

/-!
# Singleton fibres of deterministic crossing coordinates

The event coordinates are affine functions of the height coordinate once the affine feedback
state and the corresponding mark are fixed.  This file records only that deterministic algebra.
In particular, none of the statements below asserts that an adaptive state is independent of a
sample coordinate; that independence belongs to the deferred-decision/no-ties argument.
-/

open Set

namespace OTSelector

/-! ## Scalar-height maps -/

/-- The source crossing coordinate when the rank-scaled height is `n * t`. -/
noncomputable def sourceNatHeightCrossing (n : ℕ) (x0 p0 q a t : ℝ) : ℝ :=
  sourceSegmentCrossing x0 p0 q ((n : ℝ) * t) a

/-- The target crossing coordinate when the rank-scaled height is `n * t`. -/
noncomputable def targetNatHeightCrossing (n : ℕ) (x0 p0 q b t : ℝ) : ℝ :=
  targetSegmentCrossing x0 p0 q ((n : ℝ) * t) b

theorem sourceNatHeightCrossing_strictMono
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    StrictMono (sourceNatHeightCrossing n x0 p0 q a) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < 1 - a * q :=
    sourceSegment_denominator_pos ha0 ha1 hq hlam0 hlam_half
  intro t₁ t₂ ht
  rw [sourceNatHeightCrossing, sourceNatHeightCrossing,
    sourceSegmentCrossing, sourceSegmentCrossing]
  apply (div_lt_div_iff_of_pos_right hden).2
  nlinarith

theorem targetNatHeightCrossing_strictMono
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q b : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    StrictMono (targetNatHeightCrossing n x0 p0 q b) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < 1 + b * q :=
    targetSegment_denominator_pos hb0 hb2 hq hlam0 hlam_half
  intro t₁ t₂ ht
  rw [targetNatHeightCrossing, targetNatHeightCrossing,
    targetSegmentCrossing, targetSegmentCrossing]
  apply (div_lt_div_iff_of_pos_right hden).2
  nlinarith

theorem sourceNatHeightCrossing_injective
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    Function.Injective (sourceNatHeightCrossing n x0 p0 q a) :=
  (sourceNatHeightCrossing_strictMono hn ha0 ha1 hq hlam0 hlam_half).injective

theorem targetNatHeightCrossing_injective
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q b : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    Function.Injective (targetNatHeightCrossing n x0 p0 q b) :=
  (targetNatHeightCrossing_strictMono hn hb0 hb2 hq hlam0 hlam_half).injective

/-! ## Real and unit-interval fibres -/

theorem sourceNatHeightCrossing_fibre_subsingleton
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) (c : ℝ) :
    ({t : ℝ | sourceNatHeightCrossing n x0 p0 q a t = c}).Subsingleton := by
  have hinj := sourceNatHeightCrossing_injective (x0 := x0) (p0 := p0) (q := q)
    (a := a) hn ha0 ha1 hq hlam0 hlam_half
  intro t₁ ht₁ t₂ ht₂
  apply hinj
  exact ht₁.trans ht₂.symm

theorem targetNatHeightCrossing_fibre_subsingleton
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q b : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) (c : ℝ) :
    ({t : ℝ | targetNatHeightCrossing n x0 p0 q b t = c}).Subsingleton := by
  have hinj := targetNatHeightCrossing_injective (x0 := x0) (p0 := p0) (q := q)
    (b := b) hn hb0 hb2 hq hlam0 hlam_half
  intro t₁ ht₁ t₂ ht₂
  apply hinj
  exact ht₁.trans ht₂.symm

theorem sourceNatHeightCrossing_unit_fibre_subsingleton
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) (c : ℝ) :
    ({t : UnitMark |
      sourceNatHeightCrossing n x0 p0 q a (t : ℝ) = c}).Subsingleton := by
  have hmono : StrictMono (fun t : UnitMark ↦
      sourceNatHeightCrossing n x0 p0 q a (t : ℝ)) := by
    intro t₁ t₂ ht
    exact sourceNatHeightCrossing_strictMono hn ha0 ha1 hq hlam0 hlam_half
      (show (t₁ : ℝ) < (t₂ : ℝ) from ht)
  have hinj := hmono.injective
  intro t₁ ht₁ t₂ ht₂
  apply hinj
  exact ht₁.trans ht₂.symm

theorem targetNatHeightCrossing_unit_fibre_subsingleton
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q b : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) (c : ℝ) :
    ({t : UnitMark |
      targetNatHeightCrossing n x0 p0 q b (t : ℝ) = c}).Subsingleton := by
  have hmono : StrictMono (fun t : UnitMark ↦
      targetNatHeightCrossing n x0 p0 q b (t : ℝ)) := by
    intro t₁ t₂ ht
    exact targetNatHeightCrossing_strictMono hn hb0 hb2 hq hlam0 hlam_half
      (show (t₁ : ℝ) < (t₂ : ℝ) from ht)
  have hinj := hmono.injective
  intro t₁ ht₁ t₂ ht₂
  apply hinj
  exact ht₁.trans ht₂.symm

/-! ## Pairwise candidate equalities -/

theorem sourceSource_natHeightCrossing_fibre_subsingleton
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q a₁ a₂ t₂ : ℝ}
    (ha₁0 : 0 ≤ a₁) (ha₁1 : a₁ ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    ({t₁ : ℝ |
      sourceNatHeightCrossing n x0 p0 q a₁ t₁ =
        sourceNatHeightCrossing n x0 p0 q a₂ t₂}).Subsingleton := by
  exact sourceNatHeightCrossing_fibre_subsingleton hn ha₁0 ha₁1 hq hlam0 hlam_half
    (sourceNatHeightCrossing n x0 p0 q a₂ t₂)

theorem sourceTarget_natHeightCrossing_fibre_subsingleton
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q a b s : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    ({t : ℝ |
      sourceNatHeightCrossing n x0 p0 q a t =
        targetNatHeightCrossing n x0 p0 q b s}).Subsingleton := by
  exact sourceNatHeightCrossing_fibre_subsingleton hn ha0 ha1 hq hlam0 hlam_half
    (targetNatHeightCrossing n x0 p0 q b s)

theorem targetSource_natHeightCrossing_fibre_subsingleton
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q b a t₂ : ℝ}
    (hb0 : 1 ≤ b) (hb2 : b ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    ({s : ℝ |
      targetNatHeightCrossing n x0 p0 q b s =
        sourceNatHeightCrossing n x0 p0 q a t₂}).Subsingleton := by
  exact targetNatHeightCrossing_fibre_subsingleton hn hb0 hb2 hq hlam0 hlam_half
    (sourceNatHeightCrossing n x0 p0 q a t₂)

theorem targetTarget_natHeightCrossing_fibre_subsingleton
    {n : ℕ} (hn : 0 < n) {lam x0 p0 q b₁ b₂ s₂ : ℝ}
    (hb₁0 : 1 ≤ b₁) (hb₁2 : b₁ ≤ 2) (hq : |q| ≤ lam) (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) :
    ({s₁ : ℝ |
      targetNatHeightCrossing n x0 p0 q b₁ s₁ =
        targetNatHeightCrossing n x0 p0 q b₂ s₂}).Subsingleton := by
  exact targetNatHeightCrossing_fibre_subsingleton hn hb₁0 hb₁2 hq hlam0 hlam_half
    (targetNatHeightCrossing n x0 p0 q b₂ s₂)

/-! ## State-specialized forms -/

namespace FeedbackStepState

variable {n : ℕ}

theorem sourceHeightCrossing_strictMono
    (state : FeedbackStepState n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hn : 0 < n) :
    StrictMono (sourceNatHeightCrossing n state.x state.p (state.slope lam) a) := by
  exact sourceNatHeightCrossing_strictMono hn ha0 ha1
    (by simpa [FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
    hlam0 hlam_half

theorem targetHeightCrossing_strictMono
    (state : FeedbackStepState n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) {b : ℝ} (hb0 : 1 ≤ b) (hb2 : b ≤ 2)
    (hn : 0 < n) :
    StrictMono (targetNatHeightCrossing n state.x state.p (state.slope lam) b) := by
  exact targetNatHeightCrossing_strictMono hn hb0 hb2
    (by simpa [FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
    hlam0 hlam_half

theorem sourceHeightCrossing_unit_fibre_subsingleton
    (state : FeedbackStepState n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hn : 0 < n) (c : ℝ) :
    ({t : UnitMark |
      sourceNatHeightCrossing n state.x state.p (state.slope lam) a (t : ℝ) = c}).Subsingleton := by
  exact sourceNatHeightCrossing_unit_fibre_subsingleton hn ha0 ha1
    (by simpa [FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
    hlam0 hlam_half c

theorem targetHeightCrossing_unit_fibre_subsingleton
    (state : FeedbackStepState n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam_half : lam < 1 / 2) {b : ℝ} (hb0 : 1 ≤ b) (hb2 : b ≤ 2)
    (hn : 0 < n) (c : ℝ) :
    ({t : UnitMark |
      targetNatHeightCrossing n state.x state.p (state.slope lam) b (t : ℝ) = c}).Subsingleton := by
  exact targetNatHeightCrossing_unit_fibre_subsingleton hn hb0 hb2
    (by simpa [FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
    hlam0 hlam_half c

end FeedbackStepState

end OTSelector
