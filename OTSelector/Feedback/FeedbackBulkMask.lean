import OTSelector.Feedback.FeedbackPredictableRate
import OTSelector.Feedback.TrueArea
import OTSelector.Feedback.FiniteHistoryBeforeState
import OTSelector.Probability.CountingProcess.OccupationBound

/-!
# A globally bounded predictable bulk feedback rate

The algebraic rates in `FeedbackPredictableRate` are useful on a bulk cell, but they need not be
nonnegative or bounded after the feedback graph has left that cell.  This file adds a predictable
zero--one bulk mask and clips the algebraic rates at a deterministic finite level.  The last
section records the strict-cell identity: on a bulk `HistoryBeforeCoordinate`, the mask is one
and clipping is inactive.

No compensator or intensity assertion is made here.
-/

open MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

variable {n : ℕ}

open FiniteSample

/-! ## Bulk geometry and the cap -/

/-- The bulk strip for a graph point `(x,p)`. -/
def feedbackBulkRegion (n : ℕ) (B x p : ℝ) : Prop :=
  B ≤ x ∧ x ≤ (n : ℝ) - B ∧ |p| ≤ B / 8

/-- A deterministic cap for both feedback rates.  The `max` makes the definition total in `B`. -/
noncomputable def feedbackBulkRateCap (n : ℕ) (B : ℝ) : ℝ :=
  max 0 (4 * (n : ℝ) / B)

theorem feedbackBulkRegion_measurableSet (n : ℕ) (B : ℝ) :
    MeasurableSet {z : ℝ × ℝ | feedbackBulkRegion n B z.1 z.2} := by
  have hleft : MeasurableSet {z : ℝ × ℝ | B ≤ z.1} := by
    exact (isClosed_le continuous_const continuous_fst).measurableSet
  have hright : MeasurableSet {z : ℝ × ℝ | z.1 ≤ (n : ℝ) - B} := by
    exact (isClosed_le continuous_fst continuous_const).measurableSet
  have hp : MeasurableSet {z : ℝ × ℝ | |z.2| ≤ B / 8} := by
    exact (isClosed_le (continuous_abs.comp continuous_snd) continuous_const).measurableSet
  have heq : {z : ℝ × ℝ | feedbackBulkRegion n B z.1 z.2} =
      {z : ℝ × ℝ | B ≤ z.1} ∩
        ({z : ℝ × ℝ | z.1 ≤ (n : ℝ) - B} ∩
          {z : ℝ × ℝ | |z.2| ≤ B / 8}) := by
    ext z
    simp [feedbackBulkRegion]
  rw [heq]
  exact hleft.inter (hright.inter hp)

theorem feedbackBulkRateCap_nonneg (n : ℕ) (B : ℝ) :
    0 ≤ feedbackBulkRateCap n B := by
  exact le_max_left _ _

theorem feedbackBulkRateCap_eq_div {n : ℕ} {B : ℝ} (hB : 0 < B) :
    feedbackBulkRateCap n B = 4 * (n : ℝ) / B := by
  rw [feedbackBulkRateCap, max_eq_right]
  exact div_nonneg (by positivity) hB.le

theorem sourceUnclippedRemainingMass_ge_of_feedbackBulkRegion
    {n : ℕ} {B x p : ℝ} (_hB : 0 < B)
    (hbulk : feedbackBulkRegion n B x p) :
    15 * B / 16 ≤ sourceUnclippedRemainingMass n p x := by
  rcases hbulk with ⟨_, hxN, hp⟩
  have hp' := (abs_le.mp hp).1
  dsimp [sourceUnclippedRemainingMass]
  nlinarith

theorem targetUnclippedRemainingMass_ge_of_feedbackBulkRegion
    {n : ℕ} {B x p : ℝ} (_hB : 0 < B)
    (hbulk : feedbackBulkRegion n B x p) :
    13 * B / 16 ≤ targetUnclippedRemainingMass n p x := by
  rcases hbulk with ⟨_, hxN, hp⟩
  have hp' := (abs_le.mp hp).2
  dsimp [targetUnclippedRemainingMass]
  nlinarith

/-! The strip geometry is useful when the clipped area formulas are invoked downstream. -/

theorem feedbackBulkRegion_sourceBoundary_pos
    {n : ℕ} {B x p : ℝ} (hB : 0 < B)
    (hbulk : feedbackBulkRegion n B x p) (u : UnitMark) :
    0 < sourceBoundary p x u := by
  rcases hbulk with ⟨hx0, _, hp⟩
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have hu1 : (u : ℝ) ≤ 1 := u.property.2
  have hfactor0 : 0 ≤ 1 - (u : ℝ) := by linarith
  have hfactor1 : 1 - (u : ℝ) ≤ 1 := by linarith
  have habs : |p * (1 - (u : ℝ))| ≤ B / 8 := by
    rw [abs_mul, abs_of_nonneg hfactor0]
    calc
      |p| * (1 - (u : ℝ)) ≤ (B / 8) * (1 - (u : ℝ)) :=
        mul_le_mul_of_nonneg_right hp hfactor0
      _ ≤ (B / 8) * 1 :=
        mul_le_mul_of_nonneg_left hfactor1 (by positivity)
      _ = B / 8 := by ring
  have hmul := abs_le.mp habs
  simp only [sourceBoundary]
  nlinarith [hmul.2]

theorem feedbackBulkRegion_sourceBoundary_lt
    {n : ℕ} {B x p : ℝ} (hB : 0 < B)
    (hbulk : feedbackBulkRegion n B x p) (u : UnitMark) :
    sourceBoundary p x u < n := by
  rcases hbulk with ⟨_, hxN, hp⟩
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have hu1 : (u : ℝ) ≤ 1 := u.property.2
  have hfactor0 : 0 ≤ 1 - (u : ℝ) := by linarith
  have hfactor1 : 1 - (u : ℝ) ≤ 1 := by linarith
  have habs : |p * (1 - (u : ℝ))| ≤ B / 8 := by
    rw [abs_mul, abs_of_nonneg hfactor0]
    calc
      |p| * (1 - (u : ℝ)) ≤ (B / 8) * (1 - (u : ℝ)) :=
        mul_le_mul_of_nonneg_right hp hfactor0
      _ ≤ (B / 8) * 1 :=
        mul_le_mul_of_nonneg_left hfactor1 (by positivity)
      _ = B / 8 := by ring
  have hmul := abs_le.mp habs
  simp only [sourceBoundary]
  nlinarith [hmul.1]

theorem feedbackBulkRegion_targetBoundary_pos
    {n : ℕ} {B x p : ℝ} (hB : 0 < B)
    (hbulk : feedbackBulkRegion n B x p) (v : UnitMark) :
    0 < targetBoundary p x v := by
  rcases hbulk with ⟨hx0, _, hp⟩
  have hv0 : 0 ≤ (v : ℝ) := v.property.1
  have hv1 : (v : ℝ) ≤ 1 := v.property.2
  have hfactor0 : 0 ≤ 1 + (v : ℝ) := by linarith
  have hfactor2 : 1 + (v : ℝ) ≤ 2 := by linarith
  have habs : |p * (1 + (v : ℝ))| ≤ B / 4 := by
    rw [abs_mul, abs_of_nonneg hfactor0]
    calc
      |p| * (1 + (v : ℝ)) ≤ (B / 8) * (1 + (v : ℝ)) :=
        mul_le_mul_of_nonneg_right hp hfactor0
      _ ≤ (B / 8) * 2 :=
        mul_le_mul_of_nonneg_left hfactor2 (by positivity)
      _ = B / 4 := by ring
  have hmul := abs_le.mp habs
  simp only [targetBoundary]
  nlinarith [hmul.1]

theorem feedbackBulkRegion_targetBoundary_lt
    {n : ℕ} {B x p : ℝ} (hB : 0 < B)
    (hbulk : feedbackBulkRegion n B x p) (v : UnitMark) :
    targetBoundary p x v < n := by
  rcases hbulk with ⟨_, hxN, hp⟩
  have hv0 : 0 ≤ (v : ℝ) := v.property.1
  have hv1 : (v : ℝ) ≤ 1 := v.property.2
  have hfactor0 : 0 ≤ 1 + (v : ℝ) := by linarith
  have hfactor2 : 1 + (v : ℝ) ≤ 2 := by linarith
  have habs : |p * (1 + (v : ℝ))| ≤ B / 4 := by
    rw [abs_mul, abs_of_nonneg hfactor0]
    calc
      |p| * (1 + (v : ℝ)) ≤ (B / 8) * (1 + (v : ℝ)) :=
        mul_le_mul_of_nonneg_right hp hfactor0
      _ ≤ (B / 8) * 2 :=
        mul_le_mul_of_nonneg_left hfactor2 (by positivity)
      _ = B / 4 := by ring
  have hmul := abs_le.mp habs
  simp only [targetBoundary]
  nlinarith [hmul.2]

/-! ## The predictable mask -/

/-- The predictable zero--one indicator of the bulk region along the safe graph. -/
noncomputable def safeFeedbackBulkMask
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  if feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) then
    1 else 0

theorem safeFeedbackBulkMask_predictable
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hx : IsStronglyPredictable ℱ
      (fun t (_ : FiniteSample n) ↦ elapsedFeedbackCoordinate x0 t) :=
    CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
      (fun _ ↦ stronglyMeasurable_const)
      (fun _ ↦ continuous_const.add continuous_subtype_val)
  have hp := safeFeedbackHeightAtElapsed_predictable
    (n := n) hlam0 hlamHalf x0 p0
  have hpair : Measurable[ℱ.predictable]
      (fun z : ℝ≥0 × FiniteSample n ↦
        (elapsedFeedbackCoordinate x0 z.1,
          safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 z.1 z.2)) :=
    hx.measurable.prodMk hp.measurable
  have hset : MeasurableSet[ℱ.predictable]
      {z : ℝ≥0 × FiniteSample n |
        feedbackBulkRegion n B
          (elapsedFeedbackCoordinate x0 z.1)
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 z.1 z.2)} := by
    simpa only [Set.preimage_ofPred_eq, Function.comp_apply] using
      (feedbackBulkRegion_measurableSet n B).preimage hpair
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × FiniteSample n ↦
      if feedbackBulkRegion n B
          (elapsedFeedbackCoordinate x0 z.1)
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 z.1 z.2) then
        1 else 0)
  exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable

theorem safeFeedbackBulkMask_nonneg
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    0 ≤ safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample := by
  by_cases h : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) <;>
    simp [safeFeedbackBulkMask, h]

theorem safeFeedbackBulkMask_le_one
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample ≤ 1 := by
  by_cases h : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) <;>
    simp [safeFeedbackBulkMask, h]

theorem safeFeedbackBulkMask_range_finite
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    (Set.range (Function.uncurry
      (safeFeedbackBulkMask (n := n) hlam0 hlamHalf B x0 p0))).Finite := by
  have hfin : ({0, 1} : Set ℝ).Finite := Set.toFinite _
  refine hfin.subset ?_
  rintro y ⟨⟨t, sample⟩, rfl⟩
  by_cases h : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
  · simp [safeFeedbackBulkMask, h]
  · simp [safeFeedbackBulkMask, h]

/-! ## Clipped rates -/

private theorem clipToStrip_predictable
    {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {f : ℝ≥0 → Ω → ℝ} (C : ℝ)
    (hf : IsStronglyPredictable ℱ f) :
    IsStronglyPredictable ℱ (fun t ω ↦ clipToStrip C (f t ω)) := by
  have hclip : Continuous (fun z : ℝ ↦ clipToStrip C z) := by
    change Continuous (fun z : ℝ ↦ max 0 (min C z))
    exact continuous_const.max (continuous_const.min continuous_id)
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × Ω ↦ clipToStrip C (f z.1 z.2))
  exact (hclip.measurable.comp hf.measurable).stronglyMeasurable

private theorem measurable_time_section_predictable
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) :
    @Measurable ℝ≥0 (ℝ≥0 × FiniteSample n)
      (inferInstance : MeasurableSpace ℝ≥0)
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).predictable
      (fun s ↦ (s, sample)) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  rw [measurable_iff_comap_le]
  rw [MeasurableSpace.comap_le_iff_le_map]
  refine MeasurableSpace.generateFrom_le ?_
  rintro - (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · rw [MeasurableSpace.map_def]
    by_cases hs : sample ∈ A
    · simp [hs]
    · simp [hs]
  · rw [MeasurableSpace.map_def]
    by_cases hs : sample ∈ A
    · simp [hs]
    · simp [hs]

noncomputable def safeSourceBulkRate
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample *
    clipToStrip (feedbackBulkRateCap n B)
      (safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample)

noncomputable def safeTargetBulkRate
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample *
    clipToStrip (feedbackBulkRateCap n B)
      (safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample)

theorem safeSourceBulkRate_predictable
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hm := safeFeedbackBulkMask_predictable (n := n) hlam0 hlamHalf B x0 p0
  have hr := safeSourceUnclippedRateAt_predictable
    (n := n) hlam0 hlamHalf x0 p0
  have hc := clipToStrip_predictable (feedbackBulkRateCap n B) hr
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × FiniteSample n ↦
      safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 z.1 z.2 *
        clipToStrip (feedbackBulkRateCap n B)
          (safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 z.1 z.2))
  exact hm.mul hc

theorem safeTargetBulkRate_predictable
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hm := safeFeedbackBulkMask_predictable (n := n) hlam0 hlamHalf B x0 p0
  have hr := safeTargetUnclippedRateAt_predictable
    (n := n) hlam0 hlamHalf x0 p0
  have hc := clipToStrip_predictable (feedbackBulkRateCap n B) hr
  change StronglyMeasurable[ℱ.predictable]
    (fun z : ℝ≥0 × FiniteSample n ↦
      safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 z.1 z.2 *
        clipToStrip (feedbackBulkRateCap n B)
          (safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 z.1 z.2))
  exact hm.mul hc

theorem safeSourceBulkRate_nonneg
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    0 ≤ safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample := by
  unfold safeSourceBulkRate
  exact mul_nonneg (safeFeedbackBulkMask_nonneg hlam0 hlamHalf B x0 p0 t sample)
    (clipToStrip_nonneg _ _)

theorem safeTargetBulkRate_nonneg
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    0 ≤ safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample := by
  unfold safeTargetBulkRate
  exact mul_nonneg (safeFeedbackBulkMask_nonneg hlam0 hlamHalf B x0 p0 t sample)
    (clipToStrip_nonneg _ _)

theorem safeSourceBulkRate_le_cap
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample ≤
      feedbackBulkRateCap n B := by
  unfold safeSourceBulkRate
  by_cases h : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
  · have hclip := clipToStrip_le_width
      (z := safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample)
      (feedbackBulkRateCap_nonneg n B)
    simpa [safeFeedbackBulkMask, h] using hclip
  · simp [safeFeedbackBulkMask, h, feedbackBulkRateCap_nonneg n B]

theorem safeTargetBulkRate_le_cap
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample ≤
      feedbackBulkRateCap n B := by
  unfold safeTargetBulkRate
  by_cases h : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
  · have hclip := clipToStrip_le_width
      (z := safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample)
      (feedbackBulkRateCap_nonneg n B)
    simpa [safeFeedbackBulkMask, h] using hclip
  · simp [safeFeedbackBulkMask, h, feedbackBulkRateCap_nonneg n B]

/-! ## Local integrability on finite time intervals -/

theorem safeSourceBulkRate_integrableOn
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    IntegrableOn (fun s ↦ safeSourceBulkRate hlam0 hlamHalf B x0 p0 s sample)
      (Ioc (0 : ℝ≥0) t) CountingProcess.timeMeasure := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hp := safeSourceBulkRate_predictable (n := n) hlam0 hlamHalf B x0 p0
  have hmeas : Measurable (fun s : ℝ≥0 ↦
      safeSourceBulkRate hlam0 hlamHalf B x0 p0 s sample) := by
    exact hp.measurable.comp
      (measurable_time_section_predictable hlam0 hlamHalf x0 p0 sample)
  change Integrable (fun s : ℝ≥0 ↦
      safeSourceBulkRate hlam0 hlamHalf B x0 p0 s sample)
    (CountingProcess.timeMeasure.restrict (Ioc (0 : ℝ≥0) t))
  have hconst : Integrable (fun _ : ℝ≥0 ↦ feedbackBulkRateCap n B)
      (CountingProcess.timeMeasure.restrict (Ioc (0 : ℝ≥0) t)) := by
    exact integrableOn_const (C := feedbackBulkRateCap n B)
      (CountingProcess.timeMeasure_Ioc_lt_top 0 t).ne
  refine hconst.mono' hmeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun s ↦ by
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (safeSourceBulkRate_nonneg hlam0 hlamHalf B x0 p0 s sample),
      abs_of_nonneg (feedbackBulkRateCap_nonneg n B)] using
      (safeSourceBulkRate_le_cap hlam0 hlamHalf B x0 p0 s sample)

theorem safeTargetBulkRate_integrableOn
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    IntegrableOn (fun s ↦ safeTargetBulkRate hlam0 hlamHalf B x0 p0 s sample)
      (Ioc (0 : ℝ≥0) t) CountingProcess.timeMeasure := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  have hp := safeTargetBulkRate_predictable (n := n) hlam0 hlamHalf B x0 p0
  have hmeas : Measurable (fun s : ℝ≥0 ↦
      safeTargetBulkRate hlam0 hlamHalf B x0 p0 s sample) := by
    exact hp.measurable.comp
      (measurable_time_section_predictable hlam0 hlamHalf x0 p0 sample)
  change Integrable (fun s : ℝ≥0 ↦
      safeTargetBulkRate hlam0 hlamHalf B x0 p0 s sample)
    (CountingProcess.timeMeasure.restrict (Ioc (0 : ℝ≥0) t))
  have hconst : Integrable (fun _ : ℝ≥0 ↦ feedbackBulkRateCap n B)
      (CountingProcess.timeMeasure.restrict (Ioc (0 : ℝ≥0) t)) := by
    exact integrableOn_const (C := feedbackBulkRateCap n B)
      (CountingProcess.timeMeasure_Ioc_lt_top 0 t).ne
  refine hconst.mono' hmeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun s ↦ by
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (safeTargetBulkRate_nonneg hlam0 hlamHalf B x0 p0 s sample),
      abs_of_nonneg (feedbackBulkRateCap_nonneg n B)] using
      (safeTargetBulkRate_le_cap hlam0 hlamHalf B x0 p0 s sample)

/-! ## Fixed-history rate and strict-cell identities -/

namespace FeedbackStepState

/-- Source unclipped rate along the affine continuation of a fixed state, evaluated at `x`. -/
noncomputable def sourceUnclippedStateRateAt
    {n : ℕ} (lam : ℝ) (state : FeedbackStepState n) (x : ℝ) : ℝ :=
  ((n : ℝ) - (state.seenSource.card : ℝ)) /
      sourceUnclippedRemainingMass n
        (segmentCurve state.x state.p (state.slope lam) x) x *
    (1 - state.slope lam / 2)

/-- Target unclipped rate along the affine continuation of a fixed state, evaluated at `x`. -/
noncomputable def targetUnclippedStateRateAt
    {n : ℕ} (lam : ℝ) (state : FeedbackStepState n) (x : ℝ) : ℝ :=
  ((n : ℝ) - (state.seenTarget.card : ℝ)) /
      targetUnclippedRemainingMass n
        (segmentCurve state.x state.p (state.slope lam) x) x *
    (1 + 3 * state.slope lam / 2)

end FeedbackStepState

private theorem rate_le_four_n_div_B
    {B N a d q : ℝ} (hB : 0 < B) (hd : 0 < d)
    (hdhalf : B / 2 ≤ d) (hN : 0 ≤ N) (_ha0 : 0 ≤ a) (haN : a ≤ N)
    (hq0 : 0 ≤ q) (hq2 : q ≤ 2) :
    a / d * q ≤ 4 * N / B := by
  have hhalf : 0 < B / 2 := by positivity
  have hinv : 1 / d ≤ 1 / (B / 2) :=
    one_div_le_one_div_of_le hhalf hdhalf
  have hratio : a / d ≤ N / (B / 2) := by
    calc
      a / d = a * (1 / d) := by ring
      _ ≤ N * (1 / d) :=
        mul_le_mul_of_nonneg_right haN (by positivity)
      _ ≤ N * (1 / (B / 2)) :=
        mul_le_mul_of_nonneg_left hinv hN
      _ = N / (B / 2) := by ring
  calc
    a / d * q ≤ (N / (B / 2)) * q :=
      mul_le_mul_of_nonneg_right hratio hq0
    _ ≤ (N / (B / 2)) * 2 :=
      mul_le_mul_of_nonneg_left hq2 (div_nonneg hN hhalf.le)
    _ = 4 * N / B := by
      field_simp [ne_of_gt hB]
      ring

theorem safeSourceUnclippedRateAt_eq_sourceUnclippedStateRateAt_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x)
    (t : ℝ≥0) (ht : elapsedFeedbackCoordinate x0 t = x) :
    safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample =
      FeedbackStepState.sourceUnclippedStateRateAt lam
        (sample.scheduledState lam x0 p0
          (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history) x := by
  classical
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have ht0 : t = ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ := by
    apply NNReal.eq
    change (t : ℝ) = x - x0
    dsimp [elapsedFeedbackCoordinate] at ht
    linarith
  have hstate0 := HistoryBeforeCoordinate.feedbackStateAtElapsed_eq_scheduledState
    sample hlam0 hlamHalf hx0x hbefore
  have hstate : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t = terminal := by
    rw [ht0]
    simpa [terminal] using hstate0
  have hheight0 := sample.feedbackHeightAtElapsed_eq_segmentCurve
    hlam0 hlamHalf x0 p0 t
  have hheight : safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
      segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
    have hsafe : safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
        feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample := by
      simp [safeFeedbackHeightAtElapsed, hbefore.2]
    calc
      safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
          feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample := hsafe
      _ = segmentCurve
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).x
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).p
          ((sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).slope lam)
          (x0 + (t : ℝ)) := hheight0
      _ = segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
        rw [hstate]
        congr 1
  have hsource0 := safeSourceRemainingBefore_eq_n_sub_terminal_seenSource_card
    sample hlam0 hlamHalf hx0x hbefore
  have hsource : safeSourceRemainingBefore hlam0 hlamHalf x0 p0 t sample =
      (n : ℝ) - (terminal.seenSource.card : ℝ) := by
    rw [ht0]
    simpa [terminal] using hsource0
  have hmass : safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample =
      sourceUnclippedRemainingMass n
        (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x := by
    simp only [safeSourceUnclippedRemainingMassAt, hheight]
    rw [ht]
  have hslope0 := safePreFeedbackSlope_eq_terminal_slope
    sample hlam0 hlamHalf hx0x hbefore
  have hslope : safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample =
      terminal.slope lam := by
    rw [ht0]
    simpa [terminal] using hslope0
  simp only [safeSourceUnclippedRateAt, sourceTotalRate,
    safeSourceUnclippedResidualDensityAt,
    FeedbackStepState.sourceUnclippedStateRateAt]
  rw [hsource, hmass, hslope]

theorem safeTargetUnclippedRateAt_eq_targetUnclippedStateRateAt_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x)
    (t : ℝ≥0) (ht : elapsedFeedbackCoordinate x0 t = x) :
    safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample =
      FeedbackStepState.targetUnclippedStateRateAt lam
        (sample.scheduledState lam x0 p0
          (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history) x := by
  classical
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have ht0 : t = ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ := by
    apply NNReal.eq
    change (t : ℝ) = x - x0
    dsimp [elapsedFeedbackCoordinate] at ht
    linarith
  have hstate0 := HistoryBeforeCoordinate.feedbackStateAtElapsed_eq_scheduledState
    sample hlam0 hlamHalf hx0x hbefore
  have hstate : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t = terminal := by
    rw [ht0]
    simpa [terminal] using hstate0
  have hheight0 := sample.feedbackHeightAtElapsed_eq_segmentCurve
    hlam0 hlamHalf x0 p0 t
  have hheight : safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
      segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
    have hsafe : safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
        feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample := by
      simp [safeFeedbackHeightAtElapsed, hbefore.2]
    calc
      safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
          feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample := hsafe
      _ = segmentCurve
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).x
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).p
          ((sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).slope lam)
          (x0 + (t : ℝ)) := hheight0
      _ = segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
        rw [hstate]
        congr 1
  have htarget0 := safeTargetRemainingBefore_eq_n_sub_terminal_seenTarget_card
    sample hlam0 hlamHalf hx0x hbefore
  have htarget : safeTargetRemainingBefore hlam0 hlamHalf x0 p0 t sample =
      (n : ℝ) - (terminal.seenTarget.card : ℝ) := by
    rw [ht0]
    simpa [terminal] using htarget0
  have hmass : safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample =
      targetUnclippedRemainingMass n
        (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x := by
    simp only [safeTargetUnclippedRemainingMassAt, hheight]
    rw [ht]
  have hslope0 := safePreFeedbackSlope_eq_terminal_slope
    sample hlam0 hlamHalf hx0x hbefore
  have hslope : safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample =
      terminal.slope lam := by
    rw [ht0]
    simpa [terminal] using hslope0
  simp only [safeTargetUnclippedRateAt, targetTotalRate,
    safeTargetUnclippedResidualDensityAt,
    FeedbackStepState.targetUnclippedStateRateAt]
  rw [htarget, hmass, hslope]

/-! ## Inactive clipping on a strict bulk cell -/

theorem safeSourceBulkRate_eq_safeSourceUnclippedRateAt_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hB : 0 < B)
    (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x)
    (t : ℝ≥0) (ht : elapsedFeedbackCoordinate x0 t = x)
    (hbulk : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample =
      safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
  classical
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have ht0 : t = ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ := by
    apply NNReal.eq
    change (t : ℝ) = x - x0
    dsimp [elapsedFeedbackCoordinate] at ht
    linarith
  have hstate0 := HistoryBeforeCoordinate.feedbackStateAtElapsed_eq_scheduledState
    sample hlam0 hlamHalf hx0x hbefore
  have hstate : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t = terminal := by
    rw [ht0]
    simpa [terminal] using hstate0
  have hheight0 := sample.feedbackHeightAtElapsed_eq_segmentCurve
    hlam0 hlamHalf x0 p0 t
  have hheight : safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
      segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
    have hsafe : safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
        feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample := by
      simp [safeFeedbackHeightAtElapsed, hbefore.2]
    calc
      safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
          feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample := hsafe
      _ = segmentCurve
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).x
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).p
          ((sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).slope lam)
          (x0 + (t : ℝ)) := hheight0
      _ = segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
        rw [hstate]
        congr 1
  have hbulk' : feedbackBulkRegion n B x
      (segmentCurve terminal.x terminal.p (terminal.slope lam) x) := by
    simpa [ht, hheight] using hbulk
  have hden_ge := sourceUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk'
  have hden : 0 < sourceUnclippedRemainingMass n
      (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x := by
    have : 0 < B / 2 := by positivity
    exact lt_of_lt_of_le this (by nlinarith [hden_ge])
  have hsource0 := safeSourceRemainingBefore_eq_n_sub_terminal_seenSource_card
    sample hlam0 hlamHalf hx0x hbefore
  have hsource : safeSourceRemainingBefore hlam0 hlamHalf x0 p0 t sample =
      (n : ℝ) - (terminal.seenSource.card : ℝ) := by
    rw [ht0]
    simpa [terminal] using hsource0
  have hmass : safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample =
      sourceUnclippedRemainingMass n
        (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x := by
    simp only [safeSourceUnclippedRemainingMassAt, hheight]
    rw [ht]
  have hslope0 := safePreFeedbackSlope_eq_terminal_slope
    sample hlam0 hlamHalf hx0x hbefore
  have hslope : safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample =
      terminal.slope lam := by
    rw [ht0]
    simpa [terminal] using hslope0
  have hcard_le : terminal.seenSource.card ≤ n := by
    simpa using (Finset.card_le_card (Finset.subset_univ terminal.seenSource))
  have hcard_le_real : (terminal.seenSource.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcard_le
  have hnum0 : 0 ≤ (n : ℝ) - (terminal.seenSource.card : ℝ) := by
    exact sub_nonneg.mpr hcard_le_real
  have hnumN : (n : ℝ) - (terminal.seenSource.card : ℝ) ≤ (n : ℝ) := by
    have hcard0 : (0 : ℝ) ≤ (terminal.seenSource.card : ℝ) := by
      exact_mod_cast (Nat.zero_le terminal.seenSource.card)
    exact sub_le_self _ hcard0
  have hsl : |terminal.slope lam| ≤ lam := by
    simpa [FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (terminal.current : ℝ)) hlam0)
  have hslb := abs_le.mp hsl
  have hfac0 : 0 ≤ 1 - terminal.slope lam / 2 := by nlinarith [hslb.2]
  have hfac2 : 1 - terminal.slope lam / 2 ≤ 2 := by
    nlinarith [hslb.1, hlamHalf]
  have hunclip_nonneg : 0 ≤ safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
    simp only [safeSourceUnclippedRateAt, sourceTotalRate,
      safeSourceUnclippedResidualDensityAt]
    rw [hsource, hmass, hslope]
    exact mul_nonneg (div_nonneg hnum0 hden.le) hfac0
  have hunclip_le_div : safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample ≤
      4 * (n : ℝ) / B := by
    simp only [safeSourceUnclippedRateAt, sourceTotalRate,
      safeSourceUnclippedResidualDensityAt]
    rw [hsource, hmass, hslope]
    apply rate_le_four_n_div_B hB hden
    · nlinarith [hden_ge]
    · positivity
    · exact hnum0
    · exact hnumN
    · exact hfac0
    · exact hfac2
  have hunclip_le_cap : safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample ≤
      feedbackBulkRateCap n B := by
    rw [feedbackBulkRateCap_eq_div hB]
    exact hunclip_le_div
  have hclip := clipToStrip_eq_of_mem hunclip_nonneg hunclip_le_cap
  have hmask : safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample = 1 := by
    simp [safeFeedbackBulkMask, hbulk]
  unfold safeSourceBulkRate
  rw [hmask, one_mul, hclip]

theorem safeTargetBulkRate_eq_safeTargetUnclippedRateAt_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hB : 0 < B)
    (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x)
    (t : ℝ≥0) (ht : elapsedFeedbackCoordinate x0 t = x)
    (hbulk : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample =
      safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
  classical
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have ht0 : t = ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ := by
    apply NNReal.eq
    change (t : ℝ) = x - x0
    dsimp [elapsedFeedbackCoordinate] at ht
    linarith
  have hstate0 := HistoryBeforeCoordinate.feedbackStateAtElapsed_eq_scheduledState
    sample hlam0 hlamHalf hx0x hbefore
  have hstate : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t = terminal := by
    rw [ht0]
    simpa [terminal] using hstate0
  have hheight0 := sample.feedbackHeightAtElapsed_eq_segmentCurve
    hlam0 hlamHalf x0 p0 t
  have hheight : safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
      segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
    have hsafe : safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
        feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample := by
      simp [safeFeedbackHeightAtElapsed, hbefore.2]
    calc
      safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
          feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample := hsafe
      _ = segmentCurve
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).x
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).p
          ((sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).slope lam)
          (x0 + (t : ℝ)) := hheight0
      _ = segmentCurve terminal.x terminal.p (terminal.slope lam) x := by
        rw [hstate]
        congr 1
  have hbulk' : feedbackBulkRegion n B x
      (segmentCurve terminal.x terminal.p (terminal.slope lam) x) := by
    simpa [ht, hheight] using hbulk
  have hden_ge := targetUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk'
  have hden : 0 < targetUnclippedRemainingMass n
      (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x := by
    have : 0 < B / 2 := by positivity
    exact lt_of_lt_of_le this (by nlinarith [hden_ge])
  have htarget0 := safeTargetRemainingBefore_eq_n_sub_terminal_seenTarget_card
    sample hlam0 hlamHalf hx0x hbefore
  have htarget : safeTargetRemainingBefore hlam0 hlamHalf x0 p0 t sample =
      (n : ℝ) - (terminal.seenTarget.card : ℝ) := by
    rw [ht0]
    simpa [terminal] using htarget0
  have hmass : safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample =
      targetUnclippedRemainingMass n
        (segmentCurve terminal.x terminal.p (terminal.slope lam) x) x := by
    simp only [safeTargetUnclippedRemainingMassAt, hheight]
    rw [ht]
  have hslope0 := safePreFeedbackSlope_eq_terminal_slope
    sample hlam0 hlamHalf hx0x hbefore
  have hslope : safePreFeedbackSlope hlam0 hlamHalf x0 p0 t sample =
      terminal.slope lam := by
    rw [ht0]
    simpa [terminal] using hslope0
  have hcard_le : terminal.seenTarget.card ≤ n := by
    simpa using (Finset.card_le_card (Finset.subset_univ terminal.seenTarget))
  have hcard_le_real : (terminal.seenTarget.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcard_le
  have hnum0 : 0 ≤ (n : ℝ) - (terminal.seenTarget.card : ℝ) := by
    exact sub_nonneg.mpr hcard_le_real
  have hnumN : (n : ℝ) - (terminal.seenTarget.card : ℝ) ≤ (n : ℝ) := by
    have hcard0 : (0 : ℝ) ≤ (terminal.seenTarget.card : ℝ) := by
      exact_mod_cast (Nat.zero_le terminal.seenTarget.card)
    exact sub_le_self _ hcard0
  have hsl : |terminal.slope lam| ≤ lam := by
    simpa [FeedbackStepState.slope] using
      (abs_feedbackSlope_le (lam := lam) (k := (terminal.current : ℝ)) hlam0)
  have hslb := abs_le.mp hsl
  have hfac0 : 0 ≤ 1 + 3 * terminal.slope lam / 2 := by
    nlinarith [hslb.1, hlamHalf]
  have hfac2 : 1 + 3 * terminal.slope lam / 2 ≤ 2 := by
    nlinarith [hslb.2, hlamHalf]
  have hunclip_nonneg : 0 ≤ safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample := by
    simp only [safeTargetUnclippedRateAt, targetTotalRate,
      safeTargetUnclippedResidualDensityAt]
    rw [htarget, hmass, hslope]
    exact mul_nonneg (div_nonneg hnum0 hden.le) hfac0
  have hunclip_le_div : safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample ≤
      4 * (n : ℝ) / B := by
    simp only [safeTargetUnclippedRateAt, targetTotalRate,
      safeTargetUnclippedResidualDensityAt]
    rw [htarget, hmass, hslope]
    apply rate_le_four_n_div_B hB hden
    · nlinarith [hden_ge]
    · positivity
    · exact hnum0
    · exact hnumN
    · exact hfac0
    · exact hfac2
  have hunclip_le_cap : safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample ≤
      feedbackBulkRateCap n B := by
    rw [feedbackBulkRateCap_eq_div hB]
    exact hunclip_le_div
  have hclip := clipToStrip_eq_of_mem hunclip_nonneg hunclip_le_cap
  have hmask : safeFeedbackBulkMask hlam0 hlamHalf B x0 p0 t sample = 1 := by
    simp [safeFeedbackBulkMask, hbulk]
  unfold safeTargetBulkRate
  rw [hmask, one_mul, hclip]

theorem safeSourceBulkRate_eq_sourceUnclippedStateRateAt_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hB : 0 < B)
    (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x)
    (t : ℝ≥0) (ht : elapsedFeedbackCoordinate x0 t = x)
    (hbulk : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample =
      FeedbackStepState.sourceUnclippedStateRateAt lam
        (sample.scheduledState lam x0 p0
          (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history) x := by
  calc
    safeSourceBulkRate hlam0 hlamHalf B x0 p0 t sample =
        safeSourceUnclippedRateAt hlam0 hlamHalf x0 p0 t sample :=
      safeSourceBulkRate_eq_safeSourceUnclippedRateAt_of_historyBeforeCoordinate
        sample hlam0 hlamHalf hB hx0x hbefore t ht hbulk
    _ = FeedbackStepState.sourceUnclippedStateRateAt lam
        (sample.scheduledState lam x0 p0
          (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history) x :=
      safeSourceUnclippedRateAt_eq_sourceUnclippedStateRateAt_of_historyBeforeCoordinate
        sample hlam0 hlamHalf hx0x hbefore t ht

theorem safeTargetBulkRate_eq_targetUnclippedStateRateAt_of_historyBeforeCoordinate
    (sample : FiniteSample n) {lam x0 p0 x B : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hB : 0 < B)
    (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x)
    (t : ℝ≥0) (ht : elapsedFeedbackCoordinate x0 t = x)
    (hbulk : feedbackBulkRegion n B
      (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample =
      FeedbackStepState.targetUnclippedStateRateAt lam
        (sample.scheduledState lam x0 p0
          (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history) x := by
  calc
    safeTargetBulkRate hlam0 hlamHalf B x0 p0 t sample =
        safeTargetUnclippedRateAt hlam0 hlamHalf x0 p0 t sample :=
      safeTargetBulkRate_eq_safeTargetUnclippedRateAt_of_historyBeforeCoordinate
        sample hlam0 hlamHalf hB hx0x hbefore t ht hbulk
    _ = FeedbackStepState.targetUnclippedStateRateAt lam
        (sample.scheduledState lam x0 p0
          (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history) x :=
      safeTargetUnclippedRateAt_eq_targetUnclippedStateRateAt_of_historyBeforeCoordinate
        sample hlam0 hlamHalf hx0x hbefore t ht

end OTSelector
