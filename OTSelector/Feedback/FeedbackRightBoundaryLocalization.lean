import OTSelector.Feedback.FeedbackRightIntervalCountsActual
import OTSelector.Feedback.FeedbackA2Assembly
import OTSelector.Feedback.FeedbackRightTailRelativeVC

/-!
# Concrete right-boundary localization for the interval-count estimate

The fixed density `1/8` follows from a small frozen height and at least `B/2` unseen labels of
each color.  The terminal strip ends at `n-ell`, with `ell` covering the frozen shear.  These
lemmas discharge the geometric and population inputs to the actual conditional estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical

namespace OTSelector.FiniteSample

variable {n : ℕ}

/-- The square-root-buffer boundary is inside all four affine strip constraints. -/
theorem rightTailUnclippedRegion_of_buffer
    {B q : ℝ} (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2) (hq : |q| ≤ B / 8) :
    ((n : ℝ) - B, q) ∈ rightTailUnclippedRegion n := by
  rcases abs_le.mp hq with ⟨hqm, hqp⟩
  change (n : ℝ) - B ∈ Ioo 0 (n : ℝ) ∧ (n : ℝ) - B - q ∈ Ioo 0 (n : ℝ) ∧
    (n : ℝ) - B + q ∈ Ioo 0 (n : ℝ) ∧ (n : ℝ) - B + 2 * q ∈ Ioo 0 (n : ℝ)
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  constructor <;> constructor <;> linarith

/-- A shear-sized terminal strip keeps every preceding right-tail cut unclipped. -/
theorem rightTailUnclippedRegion_on_buffer_interval
    {B q ell : ℝ} (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2)
    (hq : |q| ≤ B / 8) (hell : 0 < ell) (hqe : 8 * |q| ≤ ell)
    {u : ℝ} (hu : u ∈ Icc ((n : ℝ) - B) ((n : ℝ) - ell)) :
    (u, q) ∈ rightTailUnclippedRegion n := by
  rcases abs_le.mp hq with ⟨hqm, hqp⟩
  have hqa := le_abs_self q
  have hqa' := neg_abs_le q
  change u ∈ Ioo 0 (n : ℝ) ∧ u - q ∈ Ioo 0 (n : ℝ) ∧ u + q ∈ Ioo 0 (n : ℝ) ∧ u + 2 * q ∈ Ioo 0 (n : ℝ)
  constructor
  · constructor <;> linarith [hu.1, hu.2]
  constructor
  · constructor <;> linarith [hu.1, hu.2]
  constructor <;> constructor <;> linarith [hu.1, hu.2]

/-- Natural boundary component bounds imply the genuine fixed interval density `1/8`. -/
theorem rightBoundaryIntervalRegular_of_buffer_components
    (hn : 0 < n) (lam : ℝ) {B ell : ℝ} (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2)
    (hi : RevealedSnapshot n → ℝ) (boundary : RevealedSnapshot n)
    (hhi : hi boundary = (n : ℝ) - ell)
    (hq : |rightBoundaryFrozenHeight lam ((n : ℝ) - B) boundary| ≤ B / 8)
    (hell : 0 < ell)
    (hqe : 8 * |rightBoundaryFrozenHeight lam ((n : ℝ) - B) boundary| ≤ ell)
    (hsource : B / 2 ≤ (rightBoundarySourceUnseenCount (revealedSnapshotState boundary) : ℝ))
    (htarget : B / 2 ≤ (rightBoundaryTargetUnseenCount (revealedSnapshotState boundary) : ℝ)) :
    rightBoundaryIntervalRegular lam ((n : ℝ) - B) (1 / 8) hi boundary := by
  let q := rightBoundaryFrozenHeight lam ((n : ℝ) - B) boundary
  have hR := rightTailUnclippedRegion_of_buffer hB hBn hq
  have hs := sourceBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have ht := targetBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsourceMass : (n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n q ((n : ℝ) - B)) = sourceUnclippedRemainingMass n q ((n : ℝ) - B) := by
    rw [unitSquareUniform_sourceRawRemainingSet hn (fun u ↦ (hs u).1.le) (fun u ↦ (hs u).2.le)]
    field_simp
    rfl
  have htargetMass : (n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSet n q ((n : ℝ) - B)) = targetUnclippedRemainingMass n q ((n : ℝ) - B) := by
    rw [unitSquareUniform_targetRawRemainingSet hn (fun u ↦ (ht u).1.le) (fun u ↦ (ht u).2.le)]
    field_simp
    rfl
  refine ⟨hR, ?_, ?_, ?_⟩
  · intro u hu
    rw [hhi] at hu
    exact rightTailUnclippedRegion_on_buffer_interval hB hBn hq hell hqe hu
  · change 2 * (1 / 8 : ℝ) * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n q ((n : ℝ) - B))) ≤ _
    rw [hsourceMass]
    have hqp : q ≤ B / 8 := (le_abs_self q).trans hq
    unfold sourceUnclippedRemainingMass
    linarith
  · change 2 * (1 / 8 : ℝ) * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSet n q ((n : ℝ) - B))) ≤ _
    rw [htargetMass]
    have hqm : -(B / 8) ≤ q := (abs_le.mp hq).1
    unfold targetUnclippedRemainingMass
    linarith

/-- The decoded actual snapshot retains the post-jump source cardinality. -/
theorem rightBoundarySourceUnseenCount_actual_eq_safeRemaining
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    (rightBoundarySourceUnseenCount (revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) =
      safeSourceRemainingAt hlam0 hlamHalf x0 p0 T sample := by
  rw [safeSourceRemainingAt_eq_unseen_card hlam0 hlamHalf x0 p0 T sample hNoTie]
  change (Fintype.card {i : Fin n // i ∉
    (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 T).seenSource} : ℝ) = _
  congr 1
  apply Fintype.card_of_subtype
  intro i
  simp

/-- Target counterpart of the decoded source cardinality identity. -/
theorem rightBoundaryTargetUnseenCount_actual_eq_safeRemaining
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    (rightBoundaryTargetUnseenCount (revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) =
      safeTargetRemainingAt hlam0 hlamHalf x0 p0 T sample := by
  rw [safeTargetRemainingAt_eq_unseen_card hlam0 hlamHalf x0 p0 T sample hNoTie]
  change (Fintype.card {i : Fin n // i ∉
    (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 T).seenTarget} : ℝ) = _
  congr 1
  apply Fintype.card_of_subtype
  intro i
  simp

/-- The unseen target-minus-source population is exactly the actual boundary rank current. -/
theorem rightBoundaryUnseenGap_eq_rankDiscrepancy
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    (rightBoundaryTargetUnseenCount (revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) -
    (rightBoundarySourceUnseenCount (revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) =
      RelativeVC.feedbackRankDiscrepancy (feedbackSourceRankArray sample)
        (feedbackTargetRankArray sample) (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ)) := by
  rw [rightBoundarySourceUnseenCount_actual_eq_safeRemaining hlam0 hlamHalf x0 p0 T sample hNoTie,
    rightBoundaryTargetUnseenCount_actual_eq_safeRemaining hlam0 hlamHalf x0 p0 T sample hNoTie,
    safeSourceRemainingAt_eq_n_sub_sourceCutCount hlam0 hlamHalf x0 p0 T sample hNoTie,
    safeTargetRemainingAt_eq_n_sub_targetCutCount hlam0 hlamHalf x0 p0 T sample hNoTie]
  unfold RelativeVC.feedbackRankDiscrepancy rightBoundaryHeight elapsedFeedbackCoordinate
  ring

/-- At an unclipped boundary, the remaining source count is area minus cut defect. -/
theorem rightBoundarySourceUnseenCount_eq_area_sub_defect
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hR : (x0 + (T : ℝ), rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample) ∈
      rightTailUnclippedRegion n) :
    (rightBoundarySourceUnseenCount (revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) =
      sourceUnclippedRemainingMass n (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ)) -
      RelativeVC.sourceCutDefect (rankStripLaw n : Measure (ℝ × UnitMark))
        (feedbackSourceRankArray sample) (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ)) := by
  rw [rightBoundarySourceUnseenCount_actual_eq_safeRemaining hlam0 hlamHalf x0 p0 T sample hNoTie,
    safeSourceRemainingAt_eq_n_sub_sourceCutCount hlam0 hlamHalf x0 p0 T sample hNoTie]
  have hs := sourceBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have hm := RelativeVC.rankStripLaw_real_sourceCut (Nat.cast_pos.mpr hn)
    (fun u ↦ (hs u).1.le) (fun u ↦ (hs u).2.le)
  unfold RelativeVC.sourceCutDefect
  rw [hm]
  simp only [sourceUnclippedRemainingMass, rightBoundaryHeight, elapsedFeedbackCoordinate]
  field_simp
  ring

/-- At an unclipped boundary, the remaining target count is area minus cut defect. -/
theorem rightBoundaryTargetUnseenCount_eq_area_sub_defect
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hR : (x0 + (T : ℝ), rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample) ∈
      rightTailUnclippedRegion n) :
    (rightBoundaryTargetUnseenCount (revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) =
      targetUnclippedRemainingMass n (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ)) -
      RelativeVC.targetCutDefect (rankStripLaw n : Measure (ℝ × UnitMark))
        (feedbackTargetRankArray sample) (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ)) := by
  rw [rightBoundaryTargetUnseenCount_actual_eq_safeRemaining hlam0 hlamHalf x0 p0 T sample hNoTie,
    safeTargetRemainingAt_eq_n_sub_targetCutCount hlam0 hlamHalf x0 p0 T sample hNoTie]
  have ht := targetBoundary_mem_Ioo_of_rightTailUnclippedRegion hR
  have hm := RelativeVC.rankStripLaw_real_targetCut (Nat.cast_pos.mpr hn)
    (fun u ↦ (ht u).1.le) (fun u ↦ (ht u).2.le)
  unfold RelativeVC.targetCutDefect
  rw [hm]
  simp only [targetUnclippedRemainingMass, rightBoundaryHeight, elapsedFeedbackCoordinate]
  field_simp
  ring

/-- The existing endpoint cut event localizes both actual unseen populations to `[B/2,2B]`.
The envelope condition is deterministic and holds eventually for every fixed endpoint tuning. -/
theorem actual_unseenCounts_mem_Icc_of_endpointGood
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) {amplitude q : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - RelativeVC.endpointBuffer amplitude n)
    (hB : 1 ≤ RelativeVC.endpointBuffer amplitude n)
    (hBn : RelativeVC.endpointBuffer amplitude n ≤ (n : ℝ) / 2) (hq : 1 ≤ q)
    (hgood : sample ∈ OTSelector.feedbackA2EndpointGoodEvent amplitude q n)
    (hp : |rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample| ≤
      RelativeVC.endpointBuffer amplitude n / 8)
    (henv : RelativeVC.endpointEnvelopeCoefficient q * RelativeVC.endpointScale amplitude n ≤
      RelativeVC.endpointBuffer amplitude n / 8) :
    (rightBoundarySourceUnseenCount (revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (RelativeVC.endpointBuffer amplitude n / 2)
          (2 * RelativeVC.endpointBuffer amplitude n) ∧
    (rightBoundaryTargetUnseenCount (revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (RelativeVC.endpointBuffer amplitude n / 2)
          (2 * RelativeVC.endpointBuffer amplitude n) := by
  have hBpos : 0 < RelativeVC.endpointBuffer amplitude n := lt_of_lt_of_le zero_lt_one hB
  have hfitS : 9 * RelativeVC.endpointBuffer amplitude n / 8 ≤ (n : ℝ) := by linarith
  have hfitT : 5 * RelativeVC.endpointBuffer amplitude n / 4 ≤ (n : ℝ) := by linarith
  have hsource := RelativeVC.sourceEndpointValue_lt_envelope hn hBpos hfitS hB hq hp
    (OTSelector.feedbackA2EndpointGoodEvent.source_raw hgood)
  have htarget := RelativeVC.targetEndpointValue_lt_envelope hn hBpos hfitT hB hq hp
    (OTSelector.feedbackA2EndpointGoodEvent.target_raw hgood)
  have hR : (x0 + (T : ℝ), rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample) ∈
      rightTailUnclippedRegion n := by
    rw [hboundary]
    exact rightTailUnclippedRegion_of_buffer hBpos hBn hp
  rw [rightBoundarySourceUnseenCount_eq_area_sub_defect hn hlam0 hlamHalf x0 p0 T sample hNoTie hR,
    rightBoundaryTargetUnseenCount_eq_area_sub_defect hn hlam0 hlamHalf x0 p0 T sample hNoTie hR,
    hboundary]
  rcases abs_le.mp hp with ⟨hpm, hpp⟩
  rcases abs_lt.mp hsource with ⟨hsm, hsp⟩
  rcases abs_lt.mp htarget with ⟨htm, htp⟩
  simp only [sourceUnclippedRemainingMass, targetUnclippedRemainingMass, mem_Icc]
  constructor <;> constructor <;> linarith

/-- Boundary localization uses only the frozen height and the two revealed unseen counts. -/
def rightBoundaryBufferGood (lam xR B H : ℝ) (boundary : RevealedSnapshot n) : Prop :=
  |rightBoundaryFrozenHeight lam xR boundary| ≤ H ∧
  (rightBoundarySourceUnseenCount (revealedSnapshotState boundary) : ℝ) ∈ Icc (B / 2) (2 * B) ∧
  (rightBoundaryTargetUnseenCount (revealedSnapshotState boundary) : ℝ) ∈ Icc (B / 2) (2 * B)

@[fun_prop]
theorem measurable_rightBoundarySourceUnseenCount :
    Measurable (rightBoundarySourceUnseenCount : FeedbackStepState n → ℕ) :=
  (measurable_of_finite (fun J : Finset (Fin n) ↦ Fintype.card {i // i ∉ J})).comp
    FeedbackStepState.measurable_seenSource

@[fun_prop]
theorem measurable_rightBoundaryTargetUnseenCount :
    Measurable (rightBoundaryTargetUnseenCount : FeedbackStepState n → ℕ) :=
  (measurable_of_finite (fun J : Finset (Fin n) ↦ Fintype.card {i // i ∉ J})).comp
    FeedbackStepState.measurable_seenTarget

theorem measurableSet_rightBoundaryBufferGood (lam xR B H : ℝ) :
    MeasurableSet {boundary : RevealedSnapshot n | rightBoundaryBufferGood lam xR B H boundary} := by
  have hs := (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
    ((measurable_rightBoundarySourceUnseenCount (n := n)).comp measurable_revealedSnapshotState)
  have ht := (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
    ((measurable_rightBoundaryTargetUnseenCount (n := n)).comp measurable_revealedSnapshotState)
  exact (measurableSet_le (measurable_rightBoundaryFrozenHeight lam xR).abs measurable_const).inter
    ((measurableSet_Icc.preimage hs).inter (measurableSet_Icc.preimage ht))

/-- This event is measurable in the full bulk boundary sigma field, as needed for conditioning. -/
theorem measurableSet_actual_rightBoundaryBufferGood
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (B H : ℝ) :
    MeasurableSet[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      {sample | rightBoundaryBufferGood lam (x0 + T) B H
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)} := by
  exact (measurableSet_rightBoundaryBufferGood lam (x0 + T) B H).preimage
    ((stronglyAdapted_rawRevealedSnapshot hlam0 hlamHalf x0 p0 T).mono
      (rawRevealedFiltration_le_usual hlam0 hlamHalf x0 p0 T)).measurable

/-- Existing endpoint regularity and endpoint current control imply the actual boundary event. -/
theorem rightBoundaryBufferGood_of_endpoint_controls
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) {amplitude q currentBound : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - RelativeVC.endpointBuffer amplitude n)
    (hB : 1 ≤ RelativeVC.endpointBuffer amplitude n)
    (hBn : RelativeVC.endpointBuffer amplitude n ≤ (n : ℝ) / 2) (hq : 1 ≤ q)
    (hgood : sample ∈ OTSelector.feedbackA2EndpointGoodEvent amplitude q n)
    (hp : |rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample| ≤
      RelativeVC.endpointBuffer amplitude n / 8)
    (henv : RelativeVC.endpointEnvelopeCoefficient q * RelativeVC.endpointScale amplitude n ≤
      RelativeVC.endpointBuffer amplitude n / 8)
    (hcurrent : |RelativeVC.feedbackRankDiscrepancy (feedbackSourceRankArray sample)
      (feedbackTargetRankArray sample) (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
      ((n : ℝ) - RelativeVC.endpointBuffer amplitude n)| ≤ currentBound) :
    rightBoundaryBufferGood lam (x0 + T) (RelativeVC.endpointBuffer amplitude n)
      (RelativeVC.endpointEnvelopeCoefficient q * RelativeVC.endpointScale amplitude n + currentBound / 2)
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) := by
  have hcounts := actual_unseenCounts_mem_Icc_of_endpointGood hn hlam0 hlamHalf
    x0 p0 T sample hNoTie hboundary hB hBn hq hgood hp henv
  refine ⟨?_, hcounts⟩
  rw [rightBoundaryFrozenHeight_revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T sample hNoTie]
  exact OTSelector.feedbackA2EndpointGoodEvent.abs_actual_endpoint_height_le hn
    (lt_of_lt_of_le zero_lt_one hB) (by linarith) (by linarith) hB hq hgood hp hcurrent

/-- A deterministic terminal strip of width `8 H + 1` makes this boundary event regular. -/
theorem rightBoundaryBufferGood.intervalRegular
    (hn : 0 < n) {lam B H : ℝ} (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2)
    (hH : 0 ≤ H) (hHB : H ≤ B / 8) {boundary : RevealedSnapshot n}
    (hgood : rightBoundaryBufferGood lam ((n : ℝ) - B) B H boundary) :
    rightBoundaryIntervalRegular lam ((n : ℝ) - B) (1 / 8)
      (fun _ ↦ (n : ℝ) - (8 * H + 1)) boundary := by
  exact rightBoundaryIntervalRegular_of_buffer_components hn lam hB hBn _ boundary rfl
    (hgood.1.trans hHB) (by linarith) (by linarith [hgood.1]) hgood.2.1.1 hgood.2.2.1

/-- The boundary event has a genuine original-law probability bound.  Its only remaining losses
are the already-defined bulk shear and endpoint-current tails, in addition to `44 / q`. -/
theorem measureReal_not_rightBoundaryBufferGood_le
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) {amplitude q currentBound : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - RelativeVC.endpointBuffer amplitude n)
    (hB : 1 ≤ RelativeVC.endpointBuffer amplitude n)
    (hBn : RelativeVC.endpointBuffer amplitude n ≤ (n : ℝ) / 2) (hq : 1 ≤ q)
    (henv : RelativeVC.endpointEnvelopeCoefficient q * RelativeVC.endpointScale amplitude n ≤
      RelativeVC.endpointBuffer amplitude n / 8) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {sample | ¬rightBoundaryBufferGood lam (x0 + T) (RelativeVC.endpointBuffer amplitude n)
        (RelativeVC.endpointEnvelopeCoefficient q * RelativeVC.endpointScale amplitude n + currentBound / 2)
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)} ≤
      44 / q +
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample | RelativeVC.endpointBuffer amplitude n / 8 <
          |rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample|} +
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample | currentBound < |RelativeVC.feedbackRankDiscrepancy
          (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
          (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
          ((n : ℝ) - RelativeVC.endpointBuffer amplitude n)|} := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let shear : Set (FiniteSample n) := {sample | RelativeVC.endpointBuffer amplitude n / 8 <
    |rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample|}
  let current : Set (FiniteSample n) := {sample | currentBound <
    |RelativeVC.feedbackRankDiscrepancy (feedbackSourceRankArray sample)
      (feedbackTargetRankArray sample) (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
      ((n : ℝ) - RelativeVC.endpointBuffer amplitude n)|}
  have hsubset : {sample | ¬rightBoundaryBufferGood lam (x0 + T)
      (RelativeVC.endpointBuffer amplitude n)
      (RelativeVC.endpointEnvelopeCoefficient q * RelativeVC.endpointScale amplitude n + currentBound / 2)
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)} ⊆
      OTSelector.feedbackA2EndpointBadEvent amplitude q n ∪
        (feedbackTieEvent lam x0 p0 ∪ (shear ∪ current)) := by
    intro sample hbad
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have hgood : sample ∈ OTSelector.feedbackA2EndpointGoodEvent amplitude q n := hnot.1
    have hNoTie : sample.NoFeedbackTies lam x0 p0 := by
      simpa only [feedbackTieEvent, mem_ofPred_eq, not_not] using hnot.2.1
    have hp : |rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample| ≤
        RelativeVC.endpointBuffer amplitude n / 8 := by
      simpa only [shear, mem_ofPred_eq, not_lt] using hnot.2.2.1
    have hk : |RelativeVC.feedbackRankDiscrepancy (feedbackSourceRankArray sample)
        (feedbackTargetRankArray sample) (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
        ((n : ℝ) - RelativeVC.endpointBuffer amplitude n)| ≤ currentBound := by
      simpa only [current, mem_ofPred_eq, not_lt] using hnot.2.2.2
    exact hbad (rightBoundaryBufferGood_of_endpoint_controls hn hlam0 hlamHalf x0 p0 T
      sample hNoTie hboundary hB hBn hq hgood hp henv hk)
  have htie : μ.real (feedbackTieEvent lam x0 p0) = 0 := by
    simp only [Measure.real, μ, feedbackTieEvent_measure_zero hlam0 hlamHalf x0 p0, ENNReal.toReal_zero]
  have hendpoint := OTSelector.finiteSampleLaw_real_feedbackA2EndpointBadEvent_le hn
    (lt_of_lt_of_le zero_lt_one hB) (by linarith : 9 * RelativeVC.endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (by linarith : 5 * RelativeVC.endpointBuffer amplitude n / 4 ≤ (n : ℝ)) hB hq
  have hbound := measureReal_mono (μ := μ) hsubset
  have h1 := measureReal_union_le (μ := μ) (OTSelector.feedbackA2EndpointBadEvent amplitude q n)
    (feedbackTieEvent lam x0 p0 ∪ (shear ∪ current))
  have h2 := measureReal_union_le (μ := μ) (feedbackTieEvent lam x0 p0) (shear ∪ current)
  have h3 := measureReal_union_le (μ := μ) shear current
  rw [htie] at h2
  change μ.real _ ≤ 44 / q + μ.real shear + μ.real current
  change μ.real (OTSelector.feedbackA2EndpointBadEvent amplitude q n) ≤ 44 / q at hendpoint
  linarith

/-- The actual two-color grid estimate on this concrete boundary event has failure `16 / n³`.
All conditioning is under the original finite-sample law. -/
theorem measureReal_actual_intervalGridFailure_on_buffer_le
    (hn : 1 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT : 0 < T) {B H : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2) (hH : 0 ≤ H) (hHB : H ≤ B / 8) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      ({sample | rightBoundaryBufferGood lam (x0 + T) B H
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)} ∩
       {sample | ¬rightBoundaryIntervalGridGood n lam (x0 + T) (1 / 8) (60 * Real.log n)
        (fun _ ↦ (n : ℝ) - (8 * H + 1))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample}) ≤
      16 / (n : ℝ) ^ 3 := by
  apply (measureReal_actual_intervalGridFailure_inter_le (Nat.zero_lt_of_lt hn)
    hlam0 hlamHalf x0 p0 T hT (1 / 8) (60 * Real.log n) measurable_const _
    (measurableSet_actual_rightBoundaryBufferGood hlam0 hlamHalf x0 p0 T B H) ?_ ?_).trans
    (RightTail.intervalGridFailureBound_log_le (by omega))
  · intro sample hsample
    rw [hboundary] at hsample ⊢
    exact hsample.intervalRegular (Nat.zero_lt_of_lt hn) hB hBn hH hHB
  · exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))

end OTSelector.FiniteSample
