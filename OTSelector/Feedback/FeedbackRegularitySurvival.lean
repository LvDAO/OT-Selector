import OTSelector.Basic.FiniteSamplePointLaw
import OTSelector.Feedback.CrossingCounts
import OTSelector.Feedback.FeedbackHazard
import OTSelector.Feedback.FeedbackRegularityStopping
import OTSelector.Feedback.RegularityTail
import OTSelector.Feedback.RecursiveIntersectionBridge

/-!
# Finite-sample survival of feedback regularity

This module transports the uniform rank-strip VC event to the actual four-array sample law.
The shell event in `RegularityTail` is not exposed as a Borel set, so the transported event uses
the measurable hull of its bad set.  Its complement is a measurable subset of the original good
event and has exactly the same probability bound.

The file also records the deterministic count/defect identities and the denominator-sensitive
numerical estimate used to rule out a regularity exit while the affine mass remains in the bulk.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace OTSelector

open FiniteSample

/-! ## Rank-array pushforwards -/

/-- The rank-scaled source array extracted from the actual four-array sample. -/
def feedbackSourceRankArray {n : ℕ} (sample : FiniteSample n) :
    Fin n → ℝ × UnitMark :=
  fun i ↦ rankStripMap n (sample.sourcePoint i)

/-- The rank-scaled target array extracted from the actual four-array sample. -/
def feedbackTargetRankArray {n : ℕ} (sample : FiniteSample n) :
    Fin n → ℝ × UnitMark :=
  fun j ↦ rankStripMap n (sample.targetPoint j)

@[simp] theorem feedbackSourceRankArray_apply {n : ℕ}
    (sample : FiniteSample n) (i : Fin n) :
    feedbackSourceRankArray sample i = sample.rankSourcePoint i := by
  rfl

@[simp] theorem feedbackTargetRankArray_apply {n : ℕ}
    (sample : FiniteSample n) (j : Fin n) :
    feedbackTargetRankArray sample j = sample.rankTargetPoint j := by
  rfl

theorem measurable_feedbackSourceRankArray {n : ℕ} :
    Measurable (feedbackSourceRankArray : FiniteSample n → Fin n → ℝ × UnitMark) := by
  exact measurable_pi_lambda _ fun i ↦
    (measurable_rankStripMap n).comp
      ((FiniteSample.measurable_sourceHeight i).prodMk
        (FiniteSample.measurable_sourceMark i))

theorem measurable_feedbackTargetRankArray {n : ℕ} :
    Measurable (feedbackTargetRankArray : FiniteSample n → Fin n → ℝ × UnitMark) := by
  exact measurable_pi_lambda _ fun j ↦
    (measurable_rankStripMap n).comp
      ((FiniteSample.measurable_targetHeight j).prodMk
        (FiniteSample.measurable_targetMark j))

private theorem measurable_sourcePointArray {n : ℕ} :
    Measurable (fun sample : FiniteSample n ↦ fun i ↦ sample.sourcePoint i) := by
  exact measurable_pi_lambda _ fun i ↦
    (FiniteSample.measurable_sourceHeight i).prodMk
      (FiniteSample.measurable_sourceMark i)

private theorem measurable_targetPointArray {n : ℕ} :
    Measurable (fun sample : FiniteSample n ↦ fun j ↦ sample.targetPoint j) := by
  exact measurable_pi_lambda _ fun j ↦
    (FiniteSample.measurable_targetHeight j).prodMk
      (FiniteSample.measurable_targetMark j)

private theorem finiteSampleLaw_map_sourcePointArray_measure (n : ℕ) :
    Measure.map (fun sample : FiniteSample n ↦ fun i ↦ sample.sourcePoint i)
        (finiteSampleLaw n : Measure (FiniteSample n)) =
      Measure.pi fun _ : Fin n ↦ (unitSquareUniform : Measure MarkedHeight) := by
  let takeSource : (Fin 2 → Fin n → MarkedHeight) → Fin n → MarkedHeight :=
    fun points ↦ points 0
  have htake : Measurable takeSource := measurable_pi_apply 0
  have hcomp : (fun sample : FiniteSample n ↦ fun i ↦ sample.sourcePoint i) =
      takeSource ∘ pointArray := by
    funext sample i
    rfl
  rw [hcomp, ← Measure.map_map htake measurable_pointArray,
    finiteSampleLaw_map_pointArray_measure]
  exact (measurePreserving_eval
    (fun _ : Fin 2 ↦ Measure.pi fun _ : Fin n ↦
      (unitSquareUniform : Measure MarkedHeight)) 0).map_eq

private theorem finiteSampleLaw_map_targetPointArray_measure (n : ℕ) :
    Measure.map (fun sample : FiniteSample n ↦ fun j ↦ sample.targetPoint j)
        (finiteSampleLaw n : Measure (FiniteSample n)) =
      Measure.pi fun _ : Fin n ↦ (unitSquareUniform : Measure MarkedHeight) := by
  let takeTarget : (Fin 2 → Fin n → MarkedHeight) → Fin n → MarkedHeight :=
    fun points ↦ points 1
  have htake : Measurable takeTarget := measurable_pi_apply 1
  have hcomp : (fun sample : FiniteSample n ↦ fun j ↦ sample.targetPoint j) =
      takeTarget ∘ pointArray := by
    funext sample j
    rfl
  rw [hcomp, ← Measure.map_map htake measurable_pointArray,
    finiteSampleLaw_map_pointArray_measure]
  exact (measurePreserving_eval
    (fun _ : Fin 2 ↦ Measure.pi fun _ : Fin n ↦
      (unitSquareUniform : Measure MarkedHeight)) 1).map_eq

/-- Exact source rank-array pushforward under the actual finite-sample law. -/
theorem finiteSampleLaw_map_feedbackSourceRankArray_measure (n : ℕ) :
    Measure.map feedbackSourceRankArray
        (finiteSampleLaw n : Measure (FiniteSample n)) =
      (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark)) := by
  let rankArray : (Fin n → MarkedHeight) → Fin n → ℝ × UnitMark :=
    fun points i ↦ rankStripMap n (points i)
  have hrank : Measurable rankArray := measurable_pi_lambda _ fun i ↦
    (measurable_rankStripMap n).comp (measurable_pi_apply i)
  have hcomp : feedbackSourceRankArray = rankArray ∘
      (fun sample : FiniteSample n ↦ fun i ↦ sample.sourcePoint i) := by
    rfl
  rw [hcomp, ← Measure.map_map hrank measurable_sourcePointArray,
    finiteSampleLaw_map_sourcePointArray_measure]
  rw [Measure.pi_map_pi fun _ ↦ (measurable_rankStripMap n).aemeasurable]
  congr 1

/-- Exact target rank-array pushforward under the actual finite-sample law. -/
theorem finiteSampleLaw_map_feedbackTargetRankArray_measure (n : ℕ) :
    Measure.map feedbackTargetRankArray
        (finiteSampleLaw n : Measure (FiniteSample n)) =
      (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark)) := by
  let rankArray : (Fin n → MarkedHeight) → Fin n → ℝ × UnitMark :=
    fun points i ↦ rankStripMap n (points i)
  have hrank : Measurable rankArray := measurable_pi_lambda _ fun i ↦
    (measurable_rankStripMap n).comp (measurable_pi_apply i)
  have hcomp : feedbackTargetRankArray = rankArray ∘
      (fun sample : FiniteSample n ↦ fun j ↦ sample.targetPoint j) := by
    rfl
  rw [hcomp, ← Measure.map_map hrank measurable_targetPointArray,
    finiteSampleLaw_map_targetPointArray_measure]
  rw [Measure.pi_map_pi fun _ ↦ (measurable_rankStripMap n).aemeasurable]
  congr 1

/-! ## A measurable actual-sample VC event -/

/-- Measurable hull of the canonical rank-array regularity bad event. -/
noncomputable def rankRegularityBadEventHull (n : ℕ) :
    Set (Fin n → ℝ × UnitMark) :=
  toMeasurable (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark))
    (RelativeVC.finiteHalfspaceRegularityGoodEvent
      (rankStripLaw n : Measure (ℝ × UnitMark)) n n (n + 1) 64)ᶜ

/-- Canonical measurable good set; it is contained in the raw finite-peeling good event. -/
noncomputable def rankRegularityGoodEvent (n : ℕ) :
    Set (Fin n → ℝ × UnitMark) :=
  (rankRegularityBadEventHull n)ᶜ

/-- Both actual rank arrays satisfy the measurable finite-peeling VC event. -/
noncomputable def feedbackVCRegularityGoodEvent (n : ℕ) : Set (FiniteSample n) :=
  {sample | feedbackSourceRankArray sample ∈ rankRegularityGoodEvent n ∧
    feedbackTargetRankArray sample ∈ rankRegularityGoodEvent n}

theorem measurableSet_rankRegularityBadEventHull (n : ℕ) :
    MeasurableSet (rankRegularityBadEventHull n) :=
  measurableSet_toMeasurable _ _

theorem measurableSet_rankRegularityGoodEvent (n : ℕ) :
    MeasurableSet (rankRegularityGoodEvent n) :=
  (measurableSet_rankRegularityBadEventHull n).compl

theorem measurableSet_feedbackVCRegularityGoodEvent (n : ℕ) :
    MeasurableSet (feedbackVCRegularityGoodEvent n) := by
  exact ((measurableSet_rankRegularityGoodEvent n).preimage
    measurable_feedbackSourceRankArray).inter
      ((measurableSet_rankRegularityGoodEvent n).preimage
        measurable_feedbackTargetRankArray)

theorem rankRegularityGoodEvent_subset_raw (n : ℕ) :
    rankRegularityGoodEvent n ⊆
      RelativeVC.finiteHalfspaceRegularityGoodEvent
        (rankStripLaw n : Measure (ℝ × UnitMark)) n n (n + 1) 64 := by
  intro points hpoints
  by_contra hbad
  exact hpoints (subset_toMeasurable
    (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark)) _ hbad)

theorem feedbackVCRegularityGoodEvent.source_raw
    {n : ℕ} {sample : FiniteSample n}
    (hgood : sample ∈ feedbackVCRegularityGoodEvent n) :
    feedbackSourceRankArray sample ∈
      RelativeVC.finiteHalfspaceRegularityGoodEvent
        (rankStripLaw n : Measure (ℝ × UnitMark)) n n (n + 1) 64 :=
  rankRegularityGoodEvent_subset_raw n hgood.1

theorem feedbackVCRegularityGoodEvent.target_raw
    {n : ℕ} {sample : FiniteSample n}
    (hgood : sample ∈ feedbackVCRegularityGoodEvent n) :
    feedbackTargetRankArray sample ∈
      RelativeVC.finiteHalfspaceRegularityGoodEvent
        (rankStripLaw n : Measure (ℝ × UnitMark)) n n (n + 1) 64 :=
  rankRegularityGoodEvent_subset_raw n hgood.2

theorem rankRegularityBadEventHull_measure_le
    (n : ℕ) (hn : 4 ≤ n) :
    (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark))
        (rankRegularityBadEventHull n) ≤
      RelativeVC.regularityPolynomialBadBound n := by
  rw [rankRegularityBadEventHull, measure_toMeasurable]
  exact RelativeVC.finiteHalfspaceRegularityGoodEvent_compl_le_polynomial
    (rankStripLaw n : Measure (ℝ × UnitMark)) n hn

/-- Under the actual four-array law, failure of either rank-array event has the explicit
two-array polynomial bound. -/
theorem feedbackVCRegularityGoodEvent_compl_le
    (n : ℕ) (hn : 4 ≤ n) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        (feedbackVCRegularityGoodEvent n)ᶜ ≤
      2 * RelativeVC.regularityPolynomialBadBound n := by
  let bad := rankRegularityBadEventHull n
  have hbad : MeasurableSet bad := measurableSet_rankRegularityBadEventHull n
  have hsource :
      (finiteSampleLaw n : Measure (FiniteSample n))
          (feedbackSourceRankArray ⁻¹' bad) =
        (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark)) bad := by
    calc
      (finiteSampleLaw n : Measure (FiniteSample n))
          (feedbackSourceRankArray ⁻¹' bad) =
          Measure.map feedbackSourceRankArray
            (finiteSampleLaw n : Measure (FiniteSample n)) bad :=
        (Measure.map_apply measurable_feedbackSourceRankArray hbad).symm
      _ = (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark)) bad := by
        rw [finiteSampleLaw_map_feedbackSourceRankArray_measure]
  have htarget :
      (finiteSampleLaw n : Measure (FiniteSample n))
          (feedbackTargetRankArray ⁻¹' bad) =
        (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark)) bad := by
    calc
      (finiteSampleLaw n : Measure (FiniteSample n))
          (feedbackTargetRankArray ⁻¹' bad) =
          Measure.map feedbackTargetRankArray
            (finiteSampleLaw n : Measure (FiniteSample n)) bad :=
        (Measure.map_apply measurable_feedbackTargetRankArray hbad).symm
      _ = (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark)) bad := by
        rw [finiteSampleLaw_map_feedbackTargetRankArray_measure]
  have hcompl : (feedbackVCRegularityGoodEvent n)ᶜ =
      feedbackSourceRankArray ⁻¹' bad ∪ feedbackTargetRankArray ⁻¹' bad := by
    classical
    ext sample
    simp only [feedbackVCRegularityGoodEvent, rankRegularityGoodEvent,
      Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, Set.mem_preimage,
      not_and_or, not_not, bad]
  rw [hcompl]
  calc
    (finiteSampleLaw n : Measure (FiniteSample n))
        (feedbackSourceRankArray ⁻¹' bad ∪ feedbackTargetRankArray ⁻¹' bad) ≤
        (finiteSampleLaw n : Measure (FiniteSample n))
            (feedbackSourceRankArray ⁻¹' bad) +
          (finiteSampleLaw n : Measure (FiniteSample n))
            (feedbackTargetRankArray ⁻¹' bad) := measure_union_le _ _
    _ = 2 * (rankStripSampleLaw n n : Measure (Fin n → ℝ × UnitMark)) bad := by
      rw [hsource, htarget]
      ring
    _ ≤ 2 * RelativeVC.regularityPolynomialBadBound n := by
      gcongr
      exact rankRegularityBadEventHull_measure_le n hn

theorem tendsto_feedbackVCRegularity_bad_probability :
    Filter.Tendsto
      (fun n ↦ (finiteSampleLaw n : Measure (FiniteSample n))
        (feedbackVCRegularityGoodEvent n)ᶜ)
      Filter.atTop (nhds 0) := by
  have hupper : Filter.Tendsto
      (fun n ↦ 2 * RelativeVC.regularityPolynomialBadBound n)
      Filter.atTop (nhds 0) := by
    simpa [two_mul] using
      (RelativeVC.tendsto_regularityPolynomialBadBound.add
        RelativeVC.tendsto_regularityPolynomialBadBound)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun _ ↦ bot_le
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    exact feedbackVCRegularityGoodEvent_compl_le n hn

/-! ## Deterministic remaining-count identities -/

theorem feedbackStateAtElapsed_seenSource_card_eq_sourceIntersectionCount
    {n : ℕ} {lam : ℝ} (sample : FiniteSample n)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) :
    (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource.card =
      sample.sourceIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (elapsedFeedbackCoordinate x0 t) := by
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 t
  have hmem := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
  by_cases hm : I.val < 2 * n
  · have hleftNN : sample.elapsedFeedbackKnot
        hlam0 hlamHalf x0 p0 I.val ≤ t := by
      simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    have hleft : feedbackKnot sample lam x0 p0 I.val ≤
        elapsedFeedbackCoordinate x0 t := by
      have hleft' := NNReal.coe_le_coe.mp hleftNN
      change sample.feedbackKnot lam x0 p0 I.val - x0 ≤ (t : ℝ) at hleft'
      simp only [elapsedFeedbackCoordinate]
      linarith
    have hright : elapsedFeedbackCoordinate x0 t <
        feedbackKnot sample lam x0 p0 (I.val + 1) := by
      simpa only [elapsedFeedbackCoordinate] using
        sample.elapsedIndex_next_knot_gt_of_val_lt
          hlam0 hlamHalf x0 p0 t hm
    have hcount :=
      sample.sourceIntersectionCount_eq_seenSource_card_of_knot_le_of_lt_next
        hlam0 hlamHalf x0 p0 hm hleft hright
    change (feedbackState sample lam x0 p0 I.val).seenSource.card = _
    exact hcount.symm
  · have hI : I.val = 2 * n := by omega
    have htermNN : sample.elapsedFeedbackKnot
        hlam0 hlamHalf x0 p0 (2 * n) ≤ t := by
      have hmem' : sample.elapsedFeedbackKnot
          hlam0 hlamHalf x0 p0 I.val ≤ t := by
        simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
      simpa [hI] using hmem'
    have hge : feedbackKnot sample lam x0 p0 (2 * n) ≤
        elapsedFeedbackCoordinate x0 t := by
      have hge' := NNReal.coe_le_coe.mp htermNN
      change sample.feedbackKnot lam x0 p0 (2 * n) - x0 ≤ (t : ℝ) at hge'
      simp only [elapsedFeedbackCoordinate]
      linarith
    have hstate := sample.feedbackStateAtElapsed_eq_terminal_of_terminal_le
      hlam0 hlamHalf x0 p0 htermNN
    rw [hstate]
    exact (sample.sourceIntersectionCount_eq_terminal_seenSource_card_of_ge_terminal
      hlam0 hlamHalf x0 p0 hge).symm

theorem feedbackStateAtElapsed_seenTarget_card_eq_targetIntersectionCount
    {n : ℕ} {lam : ℝ} (sample : FiniteSample n)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) :
    (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget.card =
      sample.targetIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (elapsedFeedbackCoordinate x0 t) := by
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 t
  have hmem := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
  by_cases hm : I.val < 2 * n
  · have hleftNN : sample.elapsedFeedbackKnot
        hlam0 hlamHalf x0 p0 I.val ≤ t := by
      simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    have hleft : feedbackKnot sample lam x0 p0 I.val ≤
        elapsedFeedbackCoordinate x0 t := by
      have hleft' := NNReal.coe_le_coe.mp hleftNN
      change sample.feedbackKnot lam x0 p0 I.val - x0 ≤ (t : ℝ) at hleft'
      simp only [elapsedFeedbackCoordinate]
      linarith
    have hright : elapsedFeedbackCoordinate x0 t <
        feedbackKnot sample lam x0 p0 (I.val + 1) := by
      simpa only [elapsedFeedbackCoordinate] using
        sample.elapsedIndex_next_knot_gt_of_val_lt
          hlam0 hlamHalf x0 p0 t hm
    have hcount :=
      sample.targetIntersectionCount_eq_seenTarget_card_of_knot_le_of_lt_next
        hlam0 hlamHalf x0 p0 hm hleft hright
    change (feedbackState sample lam x0 p0 I.val).seenTarget.card = _
    exact hcount.symm
  · have hI : I.val = 2 * n := by omega
    have htermNN : sample.elapsedFeedbackKnot
        hlam0 hlamHalf x0 p0 (2 * n) ≤ t := by
      have hmem' : sample.elapsedFeedbackKnot
          hlam0 hlamHalf x0 p0 I.val ≤ t := by
        simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
      simpa [hI] using hmem'
    have hge : feedbackKnot sample lam x0 p0 (2 * n) ≤
        elapsedFeedbackCoordinate x0 t := by
      have hge' := NNReal.coe_le_coe.mp htermNN
      change sample.feedbackKnot lam x0 p0 (2 * n) - x0 ≤ (t : ℝ) at hge'
      simp only [elapsedFeedbackCoordinate]
      linarith
    have hstate := sample.feedbackStateAtElapsed_eq_terminal_of_terminal_le
      hlam0 hlamHalf x0 p0 htermNN
    rw [hstate]
    exact (sample.targetIntersectionCount_eq_terminal_seenTarget_card_of_ge_terminal
      hlam0 hlamHalf x0 p0 hge).symm

/-- The actual post-jump source remainder is exactly the unswept source rank count. -/
theorem safeSourceRemainingAt_eq_n_sub_sourceCutCount
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    sample.safeSourceRemainingAt hlam0 hlamHalf x0 p0 t =
      (n : ℝ) - RelativeVC.sourceCutCount (feedbackSourceRankArray sample)
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t) := by
  classical
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t
  have hsubset : sample.initialSeenSource x0 p0 ⊆ state.seenSource := by
    intro i hi
    apply sample.mem_feedbackState_seenSource_mono lam x0 p0 i (Nat.zero_le _)
    simpa [state, feedbackStateAtElapsed, feedbackState_zero,
      initialFeedbackState] using hi
  have hcardNat :
      (state.seenSource \ sample.initialSeenSource x0 p0).card +
          (sample.initialSeenSource x0 p0).card = state.seenSource.card := by
    have hcard := Finset.card_sdiff_add_card state.seenSource
      (sample.initialSeenSource x0 p0)
    rwa [Finset.union_eq_left.mpr hsubset] at hcard
  have hcard :
      ((state.seenSource \ sample.initialSeenSource x0 p0).card : ℝ) +
          (sample.initialSeenSource x0 p0).card = state.seenSource.card := by
    exact_mod_cast hcardNat
  have hremaining :
      sample.safeSourceRemainingAt hlam0 hlamHalf x0 p0 t =
        (n : ℝ) - state.seenSource.card := by
    rw [safeSourceRemainingAt, safeInitialSourceRemainingReal,
      safeSourceCount_eq_card_diff]
    simp only [hNoTie, ite_true, initialSourceRemainingReal]
    linarith
  have hstateCount := feedbackStateAtElapsed_seenSource_card_eq_sourceIntersectionCount
    sample hlam0 hlamHalf x0 p0 t
  have hcut := sample.sourceIntersectionCount_cast_eq_sourceCutCount
    (sample.feedbackGraph hlam0 hlamHalf x0 p0) (elapsedFeedbackCoordinate x0 t)
  have hheight := sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
    hlam0 hlamHalf x0 p0 t hNoTie
  rw [hremaining, hstateCount, hcut]
  rw [hheight]
  rfl

/-- The actual post-jump target remainder is exactly the unswept target rank count. -/
theorem safeTargetRemainingAt_eq_n_sub_targetCutCount
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    sample.safeTargetRemainingAt hlam0 hlamHalf x0 p0 t =
      (n : ℝ) - RelativeVC.targetCutCount (feedbackTargetRankArray sample)
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t) := by
  classical
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t
  have hsubset : sample.initialSeenTarget x0 p0 ⊆ state.seenTarget := by
    intro j hj
    apply sample.mem_feedbackState_seenTarget_mono lam x0 p0 j (Nat.zero_le _)
    simpa [state, feedbackStateAtElapsed, feedbackState_zero,
      initialFeedbackState] using hj
  have hcardNat :
      (state.seenTarget \ sample.initialSeenTarget x0 p0).card +
          (sample.initialSeenTarget x0 p0).card = state.seenTarget.card := by
    have hcard := Finset.card_sdiff_add_card state.seenTarget
      (sample.initialSeenTarget x0 p0)
    rwa [Finset.union_eq_left.mpr hsubset] at hcard
  have hcard :
      ((state.seenTarget \ sample.initialSeenTarget x0 p0).card : ℝ) +
          (sample.initialSeenTarget x0 p0).card = state.seenTarget.card := by
    exact_mod_cast hcardNat
  have hremaining :
      sample.safeTargetRemainingAt hlam0 hlamHalf x0 p0 t =
        (n : ℝ) - state.seenTarget.card := by
    rw [safeTargetRemainingAt, safeInitialTargetRemainingReal,
      safeTargetCount_eq_card_diff]
    simp only [hNoTie, ite_true, initialTargetRemainingReal]
    linarith
  have hstateCount := feedbackStateAtElapsed_seenTarget_card_eq_targetIntersectionCount
    sample hlam0 hlamHalf x0 p0 t
  have hcut := sample.targetIntersectionCount_cast_eq_targetCutCount
    (sample.feedbackGraph hlam0 hlamHalf x0 p0) (elapsedFeedbackCoordinate x0 t)
  have hheight := sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
    hlam0 hlamHalf x0 p0 t hNoTie
  rw [hremaining, hstateCount, hcut]
  rw [hheight]
  rfl

theorem sourceRankRemaining_eq_complementMass_sub_defect
    {n : ℕ} (points : Fin n → ℝ × UnitMark) (p x : ℝ) :
    (n : ℝ) - RelativeVC.sourceCutCount points p x =
      (n : ℝ) * (1 - (rankStripLaw n : Measure (ℝ × UnitMark)).real
        (RelativeVC.errorSet (RelativeVC.sourceCutEval (p, x))
          RelativeVC.falseCutTarget)) -
        RelativeVC.sourceCutDefect
          (rankStripLaw n : Measure (ℝ × UnitMark)) points p x := by
  rw [RelativeVC.sourceCutDefect]
  ring

theorem targetRankRemaining_eq_complementMass_sub_defect
    {n : ℕ} (points : Fin n → ℝ × UnitMark) (p x : ℝ) :
    (n : ℝ) - RelativeVC.targetCutCount points p x =
      (n : ℝ) * (1 - (rankStripLaw n : Measure (ℝ × UnitMark)).real
        (RelativeVC.errorSet (RelativeVC.targetCutEval (p, x))
          RelativeVC.falseCutTarget)) -
        RelativeVC.targetCutDefect
          (rankStripLaw n : Measure (ℝ × UnitMark)) points p x := by
  rw [RelativeVC.targetCutDefect]
  ring

theorem sourceRankRemaining_eq_affineMass_sub_defect
    {n : ℕ} (hn : 0 < n) (points : Fin n → ℝ × UnitMark) {p x : ℝ}
    (hsection0 : ∀ u : UnitMark, 0 ≤ sourceBoundary p x u)
    (hsectionN : ∀ u : UnitMark, sourceBoundary p x u ≤ n) :
    (n : ℝ) - RelativeVC.sourceCutCount points p x =
      sourceUnclippedRemainingMass n p x -
        RelativeVC.sourceCutDefect
          (rankStripLaw n : Measure (ℝ × UnitMark)) points p x := by
  rw [sourceRankRemaining_eq_complementMass_sub_defect,
    rankStripLaw_source_complement_mass hn hsection0 hsectionN]

theorem targetRankRemaining_eq_affineMass_sub_defect
    {n : ℕ} (hn : 0 < n) (points : Fin n → ℝ × UnitMark) {p x : ℝ}
    (hsection0 : ∀ v : UnitMark, 0 ≤ targetBoundary p x v)
    (hsectionN : ∀ v : UnitMark, targetBoundary p x v ≤ n) :
    (n : ℝ) - RelativeVC.targetCutCount points p x =
      targetUnclippedRemainingMass n p x -
        RelativeVC.targetCutDefect
          (rankStripLaw n : Measure (ℝ × UnitMark)) points p x := by
  rw [targetRankRemaining_eq_complementMass_sub_defect,
    rankStripLaw_target_complement_mass hn hsection0 hsectionN]

theorem safeSourceRemainingAt_eq_affineMass_sub_defect_of_bulk
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    sample.safeSourceRemainingAt hlam0 hlamHalf x0 p0 t =
      safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample -
        RelativeVC.sourceCutDefect
          (rankStripLaw n : Measure (ℝ × UnitMark))
          (feedbackSourceRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
          (elapsedFeedbackCoordinate x0 t) := by
  have hnReal : 0 < (n : ℝ) := by
    rcases hbulk with ⟨hxB, hxN, _⟩
    nlinarith
  have hn : 0 < n := by exact_mod_cast hnReal
  have hsource0 : ∀ u : UnitMark,
      0 ≤ sourceBoundary
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t) u := fun u ↦
    (feedbackBulkRegion_sourceBoundary_pos hB hbulk u).le
  have hsourceN : ∀ u : UnitMark,
      sourceBoundary
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t) u ≤ n := fun u ↦
    (feedbackBulkRegion_sourceBoundary_lt hB hbulk u).le
  calc
    sample.safeSourceRemainingAt hlam0 hlamHalf x0 p0 t =
        (n : ℝ) - RelativeVC.sourceCutCount (feedbackSourceRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
          (elapsedFeedbackCoordinate x0 t) :=
      safeSourceRemainingAt_eq_n_sub_sourceCutCount
        hlam0 hlamHalf x0 p0 t sample hNoTie
    _ = sourceUnclippedRemainingMass n
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
          (elapsedFeedbackCoordinate x0 t) -
        RelativeVC.sourceCutDefect
          (rankStripLaw n : Measure (ℝ × UnitMark))
          (feedbackSourceRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
          (elapsedFeedbackCoordinate x0 t) :=
      sourceRankRemaining_eq_affineMass_sub_defect
        hn (feedbackSourceRankArray sample) hsource0 hsourceN
    _ = _ := rfl

theorem safeTargetRemainingAt_eq_affineMass_sub_defect_of_bulk
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    sample.safeTargetRemainingAt hlam0 hlamHalf x0 p0 t =
      safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample -
        RelativeVC.targetCutDefect
          (rankStripLaw n : Measure (ℝ × UnitMark))
          (feedbackTargetRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
          (elapsedFeedbackCoordinate x0 t) := by
  have hnReal : 0 < (n : ℝ) := by
    rcases hbulk with ⟨hxB, hxN, _⟩
    nlinarith
  have hn : 0 < n := by exact_mod_cast hnReal
  have htarget0 : ∀ v : UnitMark,
      0 ≤ targetBoundary
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t) v := fun v ↦
    (feedbackBulkRegion_targetBoundary_pos hB hbulk v).le
  have htargetN : ∀ v : UnitMark,
      targetBoundary
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t) v ≤ n := fun v ↦
    (feedbackBulkRegion_targetBoundary_lt hB hbulk v).le
  calc
    sample.safeTargetRemainingAt hlam0 hlamHalf x0 p0 t =
        (n : ℝ) - RelativeVC.targetCutCount (feedbackTargetRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
          (elapsedFeedbackCoordinate x0 t) :=
      safeTargetRemainingAt_eq_n_sub_targetCutCount
        hlam0 hlamHalf x0 p0 t sample hNoTie
    _ = targetUnclippedRemainingMass n
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
          (elapsedFeedbackCoordinate x0 t) -
        RelativeVC.targetCutDefect
          (rankStripLaw n : Measure (ℝ × UnitMark))
          (feedbackTargetRankArray sample)
          (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
          (elapsedFeedbackCoordinate x0 t) :=
      targetRankRemaining_eq_affineMass_sub_defect
        hn (feedbackTargetRankArray sample) htarget0 htargetN
    _ = _ := rfl

/-! ## Denominator-sensitive Bernstein arithmetic -/

/-- Two scalar Bernstein side conditions at the smallest allowed denominator control every
larger denominator. -/
theorem bernsteinCountBound_le_relative_of_denom_ge
    {constant logTerm eta d₀ D : ℝ}
    (hconstant : 0 ≤ constant) (hlog : 0 ≤ logTerm) (heta : 0 ≤ eta)
    (hd₀ : 0 ≤ d₀) (hD : d₀ ≤ D)
    (hsqrt : 4 * constant ^ 2 * logTerm ≤ eta ^ 2 * d₀)
    (hlinear : 2 * constant * logTerm ≤ eta * d₀) :
    constant * (Real.sqrt (D * logTerm) + logTerm) ≤ eta * D := by
  have hD0 : 0 ≤ D := hd₀.trans hD
  have hprod : 0 ≤ D * logTerm := mul_nonneg hD0 hlog
  have hsqrt_sq : Real.sqrt (D * logTerm) ^ 2 = D * logTerm :=
    Real.sq_sqrt hprod
  have hsqrt_nonneg : 0 ≤ Real.sqrt (D * logTerm) := Real.sqrt_nonneg _
  have hsq_scaled :
      (2 * constant * Real.sqrt (D * logTerm)) ^ 2 ≤ (eta * D) ^ 2 := by
    have heta_sq : 0 ≤ eta ^ 2 := sq_nonneg eta
    have hbase : 4 * constant ^ 2 * logTerm ≤ eta ^ 2 * D :=
      hsqrt.trans (mul_le_mul_of_nonneg_left hD heta_sq)
    have hmul := mul_le_mul_of_nonneg_right hbase hD0
    calc
      (2 * constant * Real.sqrt (D * logTerm)) ^ 2 =
          4 * constant ^ 2 * Real.sqrt (D * logTerm) ^ 2 := by ring
      _ = (4 * constant ^ 2 * logTerm) * D := by rw [hsqrt_sq]; ring
      _ ≤ (eta ^ 2 * D) * D := hmul
      _ = (eta * D) ^ 2 := by ring
  have hroot : 2 * constant * Real.sqrt (D * logTerm) ≤ eta * D := by
    have hleft0 : 0 ≤ 2 * constant * Real.sqrt (D * logTerm) := by positivity
    have hright0 : 0 ≤ eta * D := mul_nonneg heta hD0
    nlinarith
  have hlin : 2 * constant * logTerm ≤ eta * D := by
    exact hlinear.trans (mul_le_mul_of_nonneg_left hD heta)
  nlinarith

/-- The numerical constant delivered by the finite-peeling theorem. -/
theorem regularityCountBound_le_relative_of_denom_ge
    {logTerm eta d₀ D : ℝ}
    (hlog : 0 ≤ logTerm) (heta : 0 ≤ eta)
    (hd₀ : 0 ≤ d₀) (hD : d₀ ≤ D)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * logTerm ≤ eta ^ 2 * d₀)
    (hlinear : 2 * (33280 : ℝ) * logTerm ≤ eta * d₀) :
    33280 * (Real.sqrt (D * logTerm) + logTerm) ≤ eta * D := by
  exact bernsteinCountBound_le_relative_of_denom_ge
    (by norm_num) hlog heta hd₀ hD hsqrt hlinear

/-! ## VC control of the post-jump residual path -/

private theorem sourceCutDefect_abs_le_countBound_of_feedback_good
    {n : ℕ} (hn : 4 ≤ n) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) (hVC : sample ∈ feedbackVCRegularityGoodEvent n)
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    |RelativeVC.sourceCutDefect
        (rankStripLaw n : Measure (ℝ × UnitMark))
        (feedbackSourceRankArray sample)
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t)| ≤
      33280 *
        (Real.sqrt (safeSourceUnclippedRemainingMassAt
          hlam0 hlamHalf x0 p0 t sample * Real.log n) + Real.log n) := by
  let p := safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample
  let x := elapsedFeedbackCoordinate x0 t
  let P : Measure (ℝ × UnitMark) := rankStripLaw n
  let event := RelativeVC.errorSet (RelativeVC.sourceCutEval (p, x))
    RelativeVC.falseCutTarget
  have hnReal : 0 < (n : ℝ) := by
    rcases hbulk with ⟨hxB, hxN, _⟩
    nlinarith
  have hnNat : 0 < n := by exact_mod_cast hnReal
  have hsource0 : ∀ u : UnitMark, 0 ≤ sourceBoundary p x u := fun u ↦
    (feedbackBulkRegion_sourceBoundary_pos hB hbulk u).le
  have hsourceN : ∀ u : UnitMark, sourceBoundary p x u ≤ n := fun u ↦
    (feedbackBulkRegion_sourceBoundary_lt hB hbulk u).le
  have hevent : MeasurableSet event :=
    RelativeVC.measurableSet_errorSet
      (RelativeVC.measurable_sourceCutClass _ ⟨p, x, rfl⟩)
      RelativeVC.measurable_falseCutTarget
  have hbalanced : RelativeVC.balancedMass P event ≤ P.real eventᶜ :=
    min_le_right _ _
  have hcomplement : P.real eventᶜ = 1 - P.real event :=
    probReal_compl_eq_one_sub hevent
  have hmass : (n : ℝ) * RelativeVC.balancedMass P event ≤
      safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample := by
    have hmul := mul_le_mul_of_nonneg_left hbalanced (Nat.cast_nonneg n)
    rw [hcomplement] at hmul
    have hpop := rankStripLaw_source_complement_mass hnNat hsource0 hsourceN
    change (n : ℝ) * (1 - P.real event) =
      safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample at hpop
    exact hmul.trans_eq hpop
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    exact (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).le
  have hsqrt : Real.sqrt (((n : ℝ) * RelativeVC.balancedMass P event) *
      Real.log n) ≤
      Real.sqrt (safeSourceUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 t sample * Real.log n) := by
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmass hlog)
  have hraw := feedbackVCRegularityGoodEvent.source_raw
    (n := n) (sample := sample) hVC
  have hdefect := RelativeVC.sourceCutDefect_uniform_regularity_on_goodEvent
    (rankStripLaw n : Measure (ℝ × UnitMark)) hn hraw p x
  change |RelativeVC.sourceCutDefect P (feedbackSourceRankArray sample) p x| ≤ _
  calc
    |RelativeVC.sourceCutDefect P (feedbackSourceRankArray sample) p x| ≤
        33280 *
          (Real.sqrt (((n : ℝ) * RelativeVC.balancedMass P event) *
            Real.log n) + Real.log n) := hdefect
    _ ≤ 33280 *
        (Real.sqrt (safeSourceUnclippedRemainingMassAt
          hlam0 hlamHalf x0 p0 t sample * Real.log n) + Real.log n) := by
      gcongr

private theorem targetCutDefect_abs_le_countBound_of_feedback_good
    {n : ℕ} (hn : 4 ≤ n) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) (x0 p0 : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) (hVC : sample ∈ feedbackVCRegularityGoodEvent n)
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    |RelativeVC.targetCutDefect
        (rankStripLaw n : Measure (ℝ × UnitMark))
        (feedbackTargetRankArray sample)
        (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
        (elapsedFeedbackCoordinate x0 t)| ≤
      33280 *
        (Real.sqrt (safeTargetUnclippedRemainingMassAt
          hlam0 hlamHalf x0 p0 t sample * Real.log n) + Real.log n) := by
  let p := safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample
  let x := elapsedFeedbackCoordinate x0 t
  let P : Measure (ℝ × UnitMark) := rankStripLaw n
  let event := RelativeVC.errorSet (RelativeVC.targetCutEval (p, x))
    RelativeVC.falseCutTarget
  have hnReal : 0 < (n : ℝ) := by
    rcases hbulk with ⟨hxB, hxN, _⟩
    nlinarith
  have hnNat : 0 < n := by exact_mod_cast hnReal
  have htarget0 : ∀ v : UnitMark, 0 ≤ targetBoundary p x v := fun v ↦
    (feedbackBulkRegion_targetBoundary_pos hB hbulk v).le
  have htargetN : ∀ v : UnitMark, targetBoundary p x v ≤ n := fun v ↦
    (feedbackBulkRegion_targetBoundary_lt hB hbulk v).le
  have hevent : MeasurableSet event :=
    RelativeVC.measurableSet_errorSet
      (RelativeVC.measurable_targetCutClass _ ⟨p, x, rfl⟩)
      RelativeVC.measurable_falseCutTarget
  have hbalanced : RelativeVC.balancedMass P event ≤ P.real eventᶜ :=
    min_le_right _ _
  have hcomplement : P.real eventᶜ = 1 - P.real event :=
    probReal_compl_eq_one_sub hevent
  have hmass : (n : ℝ) * RelativeVC.balancedMass P event ≤
      safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample := by
    have hmul := mul_le_mul_of_nonneg_left hbalanced (Nat.cast_nonneg n)
    rw [hcomplement] at hmul
    have hpop := rankStripLaw_target_complement_mass hnNat htarget0 htargetN
    change (n : ℝ) * (1 - P.real event) =
      safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample at hpop
    exact hmul.trans_eq hpop
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    exact (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).le
  have hsqrt : Real.sqrt (((n : ℝ) * RelativeVC.balancedMass P event) *
      Real.log n) ≤
      Real.sqrt (safeTargetUnclippedRemainingMassAt
        hlam0 hlamHalf x0 p0 t sample * Real.log n) := by
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmass hlog)
  have hraw := feedbackVCRegularityGoodEvent.target_raw
    (n := n) (sample := sample) hVC
  have hdefect := RelativeVC.targetCutDefect_uniform_regularity_on_goodEvent
    (rankStripLaw n : Measure (ℝ × UnitMark)) hn hraw p x
  change |RelativeVC.targetCutDefect P (feedbackTargetRankArray sample) p x| ≤ _
  calc
    |RelativeVC.targetCutDefect P (feedbackTargetRankArray sample) p x| ≤
        33280 *
          (Real.sqrt (((n : ℝ) * RelativeVC.balancedMass P event) *
            Real.log n) + Real.log n) := hdefect
    _ ≤ 33280 *
        (Real.sqrt (safeTargetUnclippedRemainingMassAt
          hlam0 hlamHalf x0 p0 t sample * Real.log n) + Real.log n) := by
      gcongr

/-- On the actual VC event, bulk survival and the two numerical inequalities keep the
right-continuous post-jump residual path inside the regularity square. -/
theorem safeFeedbackPostResidualPath_mem_regularityRegion_of_good_of_bulk
    {n : ℕ} (hn : 4 ≤ n) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {eta B : ℝ} (heta : 0 ≤ eta) (hB : 0 < B)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hVC : sample ∈ feedbackVCRegularityGoodEvent n)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤
      eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤
      eta * (13 * B / 16))
    (hbulk : feedbackBulkRegion n B (elapsedFeedbackCoordinate x0 t)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)) :
    safeFeedbackPostResidualPath hlam0 hlamHalf B x0 p0 t sample ∈
      feedbackRegularityRegion eta := by
  let Ds := safeSourceUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample
  let Dt := safeTargetUnclippedRemainingMassAt hlam0 hlamHalf x0 p0 t sample
  let Δs := RelativeVC.sourceCutDefect
    (rankStripLaw n : Measure (ℝ × UnitMark))
    (feedbackSourceRankArray sample)
    (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
    (elapsedFeedbackCoordinate x0 t)
  let Δt := RelativeVC.targetCutDefect
    (rankStripLaw n : Measure (ℝ × UnitMark))
    (feedbackTargetRankArray sample)
    (safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample)
    (elapsedFeedbackCoordinate x0 t)
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    exact (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).le
  have hDsGe : 13 * B / 16 ≤ Ds := by
    have h := sourceUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
    dsimp [Ds, safeSourceUnclippedRemainingMassAt]
    nlinarith [hB]
  have hDtGe : 13 * B / 16 ≤ Dt := by
    simpa [Dt, safeTargetUnclippedRemainingMassAt] using
      targetUnclippedRemainingMass_ge_of_feedbackBulkRegion hB hbulk
  have hd₀ : 0 ≤ 13 * B / 16 := by positivity
  have hDsPos : 0 < Ds := lt_of_lt_of_le (by positivity : 0 < 13 * B / 16) hDsGe
  have hDtPos : 0 < Dt := lt_of_lt_of_le (by positivity : 0 < 13 * B / 16) hDtGe
  have hΔsCount := sourceCutDefect_abs_le_countBound_of_feedback_good
    hn hlam0 hlamHalf hB x0 p0 t sample hVC hbulk
  have hΔtCount := targetCutDefect_abs_le_countBound_of_feedback_good
    hn hlam0 hlamHalf hB x0 p0 t sample hVC hbulk
  have hΔs : |Δs| ≤ eta * Ds := hΔsCount.trans
    (regularityCountBound_le_relative_of_denom_ge
      hlog heta hd₀ hDsGe hsqrt hlinear)
  have hΔt : |Δt| ≤ eta * Dt := hΔtCount.trans
    (regularityCountBound_le_relative_of_denom_ge
      hlog heta hd₀ hDtGe hsqrt hlinear)
  have hsourceRemaining := safeSourceRemainingAt_eq_affineMass_sub_defect_of_bulk
    hlam0 hlamHalf hB x0 p0 t sample hNoTie hbulk
  have htargetRemaining := safeTargetRemainingAt_eq_affineMass_sub_defect_of_bulk
    hlam0 hlamHalf hB x0 p0 t sample hNoTie hbulk
  have hsourceDen : safeSourceStabilizedRemainingMassAt
      hlam0 hlamHalf B x0 p0 t sample = Ds := by
    rw [safeSourceStabilizedRemainingMassAt, max_eq_right]
    exact (by dsimp [Ds]; nlinarith [hDsPos, hB] : B / 2 ≤ Ds)
  have htargetDen : safeTargetStabilizedRemainingMassAt
      hlam0 hlamHalf B x0 p0 t sample = Dt := by
    rw [safeTargetStabilizedRemainingMassAt, max_eq_right]
    exact (by dsimp [Dt]; nlinarith [hDtPos, hB] : B / 2 ≤ Dt)
  have hsourceRatio : safeSourcePostResidualDensityAt
      hlam0 hlamHalf B x0 p0 t sample = (Ds - Δs) / Ds := by
    rw [safeSourcePostResidualDensityAt, hsourceDen, hsourceRemaining]
  have htargetRatio : safeTargetPostResidualDensityAt
      hlam0 hlamHalf B x0 p0 t sample = (Dt - Δt) / Dt := by
    rw [safeTargetPostResidualDensityAt, htargetDen, htargetRemaining]
  have hΔsSides := abs_le.mp hΔs
  have hΔtSides := abs_le.mp hΔt
  have hsLower : 1 - eta ≤ (Ds - Δs) / Ds := by
    rw [le_div_iff₀ hDsPos]
    nlinarith
  have hsUpper : (Ds - Δs) / Ds ≤ 1 + eta := by
    rw [div_le_iff₀ hDsPos]
    nlinarith
  have htLower : 1 - eta ≤ (Dt - Δt) / Dt := by
    rw [le_div_iff₀ hDtPos]
    nlinarith
  have htUpper : (Dt - Δt) / Dt ≤ 1 + eta := by
    rw [div_le_iff₀ hDtPos]
    nlinarith
  change 1 - eta ≤ safeSourcePostResidualDensityAt
      hlam0 hlamHalf B x0 p0 t sample ∧
    safeSourcePostResidualDensityAt hlam0 hlamHalf B x0 p0 t sample ≤ 1 + eta ∧
    1 - eta ≤ safeTargetPostResidualDensityAt
      hlam0 hlamHalf B x0 p0 t sample ∧
    safeTargetPostResidualDensityAt hlam0 hlamHalf B x0 p0 t sample ≤ 1 + eta
  rw [hsourceRatio, htargetRatio]
  exact ⟨hsLower, hsUpper, htLower, htUpper⟩

/-- The VC event rules out a regularity exit strictly before both the bulk exit and the
deterministic horizon. -/
theorem min_bulkExit_horizon_le_regularityExitTime_of_feedback_good
    {n : ℕ} (hn : 4 ≤ n) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {eta B : ℝ} (heta : 0 ≤ eta) (hB : 0 < B)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hVC : sample ∈ feedbackVCRegularityGoodEvent n)
    (hsqrt : 4 * (33280 : ℝ) ^ 2 * Real.log n ≤
      eta ^ 2 * (13 * B / 16))
    (hlinear : 2 * (33280 : ℝ) * Real.log n ≤
      eta * (13 * B / 16)) :
    min (safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample)
        (T : WithTop ℝ≥0) ≤
      safeFeedbackRegularityExitTime
        hlam0 hlamHalf eta B x0 p0 sample := by
  apply le_of_not_gt
  intro hlt
  change MeasureTheory.hittingAfter
      (safeFeedbackPostResidualPath (n := n) hlam0 hlamHalf B x0 p0)
      (feedbackRegularityBadSet eta) 0 sample < _ at hlt
  have hminNe : min (safeFeedbackBulkExitTime
      hlam0 hlamHalf B x0 p0 sample) (T : WithTop ℝ≥0) ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_right _ _) (WithTop.coe_lt_top T)).ne
  obtain ⟨S, hS⟩ := WithTop.ne_top_iff_exists.mp hminNe
  rw [← hS] at hlt
  rw [MeasureTheory.hittingAfter_lt_iff] at hlt
  obtain ⟨t, ht, htbad⟩ := hlt
  have htMin : (t : WithTop ℝ≥0) < min
      (safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample)
      (T : WithTop ℝ≥0) := by
    rw [← hS]
    exact_mod_cast ht.2
  have htBulk : (t : WithTop ℝ≥0) <
      safeFeedbackBulkExitTime hlam0 hlamHalf B x0 p0 sample :=
    htMin.trans_le (min_le_left _ _)
  have hbulk := feedbackBulkRegion_of_lt_safeFeedbackBulkExitTime
    hlam0 hlamHalf B x0 p0 t sample htBulk
  have htgood := safeFeedbackPostResidualPath_mem_regularityRegion_of_good_of_bulk
    hn hlam0 hlamHalf heta hB x0 p0 t sample hNoTie hVC hsqrt hlinear hbulk
  exact htbad htgood

end OTSelector
