import OTSelector.Feedback.FeedbackRightIntervalCountsBoundary
import OTSelector.Feedback.FeedbackRightIntervalCountsProduct

/-!
# Frozen interval estimates under the original finite-sample law

The failure indicator is a bounded jointly measurable function of the boundary snapshot and a
completed sample.  The exact boundary conditional law therefore transfers the independent
product estimate while retaining the full revealed bulk history.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical

namespace OTSelector
namespace RightTail

variable {n : ℕ}

theorem unseenSourceGroup_card_eq
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource) :
    (unseenSourceGroup S).card = FiniteSample.rightBoundarySourceUnseenCount state := by
  classical
  have h := sum_unseenSourceGroup S (fun _ ↦ (1 : ℝ))
  simp only [hsource, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_boole] at h
  have hc : (Finset.univ.filter fun i : Fin n ↦ i ∉ state.seenSource).card =
      FiniteSample.rightBoundarySourceUnseenCount state := by
    simp [FiniteSample.rightBoundarySourceUnseenCount, Fintype.card_subtype]
  exact_mod_cast h.trans (congrArg (fun k : ℕ ↦ (k : ℝ)) hc)

theorem unseenTargetGroup_card_eq
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (htarget : ∀ i : Fin n, (Sum.inr i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenTarget) :
    ((unseenSourceGroup S)ᶜ).card = FiniteSample.rightBoundaryTargetUnseenCount state := by
  classical
  have h := sum_unseenTargetGroup S (fun _ ↦ (1 : ℝ))
  simp only [htarget, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_boole] at h
  have hc : (Finset.univ.filter fun i : Fin n ↦ i ∉ state.seenTarget).card =
      FiniteSample.rightBoundaryTargetUnseenCount state := by
    simp [FiniteSample.rightBoundaryTargetUnseenCount, Fintype.card_subtype]
  exact_mod_cast h.trans (congrArg (fun k : ℕ ↦ (k : ℝ)) hc)

/-- Completing the canonical snapshot gives exactly the two color certificates on its unseen
product, for every completion, including completions with tied crossing coordinates. -/
theorem intervalGridGood_merge_iff
    (N : ℕ) (lam xR c r : ℝ) (hi : FiniteSample.RevealedSnapshot n → ℝ)
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ i : Fin n, (Sum.inr i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenTarget)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    FiniteSample.rightBoundaryIntervalGridGood N lam xR c r hi
        (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) ↔
      FiniteIntervalCounts.groupGridGood N (unseenSourceGroup S)
        (sourcePhase n (segmentCurve state.x state.p (state.slope lam) xR)) xR
        (hi (sample.revealedSnapshotFromState state)) c r unseen ∧
      FiniteIntervalCounts.groupGridGood N (unseenSourceGroup S)ᶜ
        (targetPhase n (segmentCurve state.x state.p (state.slope lam) xR)) xR
        (hi (sample.revealedSnapshotFromState state)) c r unseen := by
  simp only [FiniteSample.rightBoundaryIntervalGridGood,
    sourceIntervalCount_merge_eq_groupCount lam xR _ _ state S hsource sample seen unseen,
    targetIntervalCount_merge_eq_groupCount lam xR _ _ state S htarget sample seen unseen,
    FiniteIntervalCounts.groupGridGood, forall_and]

/-- Boundary interval-grid failure as a bounded scalar observable. -/
noncomputable def intervalGridFailureIndicator
    (N : ℕ) (lam xR c r : ℝ) (hi : FiniteSample.RevealedSnapshot n → ℝ)
    (boundary : FiniteSample.RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  if ¬FiniteSample.rightBoundaryIntervalGridGood N lam xR c r hi boundary completed then 1 else 0

theorem measurable_intervalGridFailureIndicator
    (N : ℕ) (lam xR c r : ℝ) {hi : FiniteSample.RevealedSnapshot n → ℝ}
    (hhi : Measurable hi) :
    Measurable fun p : FiniteSample.RevealedSnapshot n × FiniteSample n ↦
      intervalGridFailureIndicator N lam xR c r hi p.1 p.2 :=
  Measurable.ite
    (FiniteSample.measurableSet_rightBoundaryIntervalGridGood N lam xR c r hhi).compl
    measurable_const measurable_const

theorem norm_intervalGridFailureIndicator_le
    (N : ℕ) (lam xR c r : ℝ) (hi : FiniteSample.RevealedSnapshot n → ℝ)
    (boundary : FiniteSample.RevealedSnapshot n) (completed : FiniteSample n) :
    ‖intervalGridFailureIndicator N lam xR c r hi boundary completed‖ ≤ 1 := by
  unfold intervalGridFailureIndicator
  split_ifs <;> norm_num

/-- The actual normalized unseen integral satisfies the two-color grid estimate. -/
theorem normalized_intervalGridFailure_le
    {N : ℕ} (hn : 0 < n) (lam xR c r : ℝ)
    {hi : FiniteSample.RevealedSnapshot n → ℝ} (hhi : Measurable hi)
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ i : Fin n, (Sum.inr i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenTarget)
    (sample : FiniteSample n)
    (hR : (xR, segmentCurve state.x state.p (state.slope lam) xR) ∈
      FiniteSample.rightTailUnclippedRegion n)
    (hstrip : ∀ u ∈ Icc xR (hi (sample.revealedSnapshotFromState state)),
      (u, segmentCurve state.x state.p (state.slope lam) xR) ∈
        FiniteSample.rightTailUnclippedRegion n)
    (hsdensity : 2 * c * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n (segmentCurve state.x state.p (state.slope lam) xR) xR)) ≤
        FiniteSample.rightBoundarySourceUnseenCount state)
    (htdensity : 2 * c * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSet n (segmentCurve state.x state.p (state.slope lam) xR) xR)) ≤
        FiniteSample.rightBoundaryTargetUnseenCount state) (hr : 0 < r) :
    normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
      (feedbackUnseenRectangularSetAt lam state xR S)
      (fun unseen ↦ intervalGridFailureIndicator N lam xR c r hi
        (sample.revealedSnapshotFromState state)
        (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen)) ≤
      intervalGridFailureBound N r := by
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let P := fixedLaw n q xR (unseenSourceGroup S)
  have : ∀ i, IsProbabilityMeasure (P i) :=
    fixedLaw_isProbabilityMeasure hn (unseenSourceGroup S) hR
  let E : Set (feedbackUnseenFinset S → MarkedHeight) := {unseen |
    ¬FiniteSample.rightBoundaryIntervalGridGood N lam xR c r hi
      (sample.revealedSnapshotFromState state)
      (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen)}
  have hmap : Measurable fun unseen : feedbackUnseenFinset S → MarkedHeight ↦
      (sample.revealedSnapshotFromState state,
        finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen) :=
    measurable_const.prodMk ((measurable_finiteSampleSeenUnseenMerge S).comp
      (measurable_const.prodMk measurable_id))
  have hE : MeasurableSet E :=
    (FiniteSample.measurableSet_rightBoundaryIntervalGridGood N lam xR c r hhi).compl.preimage hmap
  rw [normalized_unseen_eq_integral_fixedLaw hn lam xR state S hR]
  have hfun : (fun unseen ↦ intervalGridFailureIndicator N lam xR c r hi
      (sample.revealedSnapshotFromState state)
      (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen)) =
      E.indicator (fun _ ↦ (1 : ℝ)) := by
    funext unseen
    simp only [intervalGridFailureIndicator, Set.indicator_apply, E, mem_ofPred_eq]
  rw [hfun]
  change (∫ unseen, E.indicator (1 : (feedbackUnseenFinset S → MarkedHeight) → ℝ) unseen
    ∂Measure.pi P) ≤ _
  rw [integral_indicator_one hE]
  have hbound := fixedLaw_twoColorGrid_failure_le (N := N) hn (unseenSourceGroup S) hR hstrip
    (by simpa only [unseenSourceGroup_card_eq state S hsource] using hsdensity)
    (by simpa only [unseenTargetGroup_card_eq state S htarget] using htdensity) hr
  have hset : E = {unseen |
      ¬(FiniteIntervalCounts.groupGridGood N (unseenSourceGroup S) (sourcePhase n q) xR
          (hi (sample.revealedSnapshotFromState state)) c r unseen ∧
        FiniteIntervalCounts.groupGridGood N (unseenSourceGroup S)ᶜ (targetPhase n q) xR
          (hi (sample.revealedSnapshotFromState state)) c r unseen)} := by
    ext unseen
    exact not_congr (intervalGridGood_merge_iff N lam xR c r hi state S hsource htarget
      sample (feedbackSeenTuple S sample) unseen)
  rw [hset]
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hbound
    |>.trans_eq (ENNReal.toReal_ofReal (intervalGridFailureBound_nonneg N r))

end RightTail
namespace FiniteSample

variable {n : ℕ}

/-- The geometric and population conditions ensuring a fixed positive interval density. -/
def rightBoundaryIntervalRegular (lam xR c : ℝ)
    (hi : RevealedSnapshot n → ℝ) (boundary : RevealedSnapshot n) : Prop :=
  (xR, rightBoundaryFrozenHeight lam xR boundary) ∈ rightTailUnclippedRegion n ∧
  (∀ u ∈ Icc xR (hi boundary),
    (u, rightBoundaryFrozenHeight lam xR boundary) ∈ rightTailUnclippedRegion n) ∧
  2 * c * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (sourceRawRemainingSet n (rightBoundaryFrozenHeight lam xR boundary) xR)) ≤
    rightBoundarySourceUnseenCount (revealedSnapshotState boundary) ∧
  2 * c * ((n : ℝ) * (unitSquareUniform : Measure MarkedHeight).real
      (targetRawRemainingSet n (rightBoundaryFrozenHeight lam xR boundary) xR)) ≤
    rightBoundaryTargetUnseenCount (revealedSnapshotState boundary)

/-- Pointwise evaluation of the conditional-law candidate for the actual boundary snapshot. -/
theorem rightBoundaryScalarCandidate_intervalGridFailure_le
    {N : ℕ} (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (c r : ℝ)
    {hi : RevealedSnapshot n → ℝ} (hhi : Measurable hi)
    (sample : FiniteSample n)
    (hregular : rightBoundaryIntervalRegular lam (x0 + T) c hi
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) (hr : 0 < r) :
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
      (RightTail.intervalGridFailureIndicator N lam (x0 + T) c r hi) sample ≤
        RightTail.intervalGridFailureBound N r := by
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 T
  let S := state.seenSource.disjSum state.seenTarget
  have hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource := by
    intro i
    simp [S]
  have htarget : ∀ i : Fin n, (Sum.inr i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenTarget := by
    intro i
    simp [S]
  have hF := (RightTail.measurable_intervalGridFailureIndicator N lam (x0 + T) c r
    hhi).stronglyMeasurable
  change twoSnapshotNormalizedScalar lam (x0 + T)
    (RightTail.intervalGridFailureIndicator N lam (x0 + T) c r hi)
      (sample.revealedSnapshotFromState state) (sample.revealedSnapshotFromState state) ≤ _
  rw [twoSnapshotNormalizedScalar_revealedSnapshotFromState_eq _ _ _ hF _ state S
    hsource htarget sample]
  apply RightTail.normalized_intervalGridFailure_le hn lam (x0 + T) c r hhi
    state S hsource htarget sample
  · exact hregular.1
  · exact hregular.2.1
  · exact hregular.2.2.1
  · exact hregular.2.2.2
  · exact hr

/-- Actual two-color interval-grid failure has a uniform conditional probability bound under the
original law, tested on any measurable boundary-localization set. -/
theorem condExp_actual_intervalGridFailure_le
    {N : ℕ} (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT : 0 < T) (c r : ℝ)
    {hi : RevealedSnapshot n → ℝ} (hhi : Measurable hi)
    (G : Set (FiniteSample n)) (hG : MeasurableSet G)
    (hregular : ∀ sample ∈ G, rightBoundaryIntervalRegular lam (x0 + T) c hi
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) (hr : 0 < r) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
      (fun sample ↦ RightTail.intervalGridFailureIndicator N lam (x0 + T) c r hi
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample) |
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
        (finiteSampleLaw n : Measure (FiniteSample n)).restrict G]
      fun _ ↦ RightTail.intervalGridFailureBound N r := by
  have hF := (RightTail.measurable_intervalGridFailureIndicator N lam (x0 + T) c r
    hhi).stronglyMeasurable
  have heq := condExp_actualBoundaryEvaluation_eq_candidate hn hlam0 hlamHalf x0 p0 T hT
    (RightTail.intervalGridFailureIndicator N lam (x0 + T) c r hi) hF (by norm_num : (0 : ℝ) ≤ 1)
    (RightTail.norm_intervalGridFailureIndicator_le N lam (x0 + T) c r hi)
  filter_upwards [ae_restrict_of_ae heq, ae_restrict_mem hG] with sample heq hmem
  rw [heq]
  exact rightBoundaryScalarCandidate_intervalGridFailure_le hn hlam0 hlamHalf x0 p0 T
    c r hhi sample (hregular sample hmem) hr

/-- On a bulk-boundary measurable localization event, the actual grid failure has the same
unconditional envelope.  The ambient law is unchanged. -/
theorem measureReal_actual_intervalGridFailure_inter_le
    {N : ℕ} (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT : 0 < T) (c r : ℝ)
    {hi : RevealedSnapshot n → ℝ} (hhi : Measurable hi)
    (G : Set (FiniteSample n))
    (hG : MeasurableSet[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] G)
    (hregular : ∀ sample ∈ G, rightBoundaryIntervalRegular lam (x0 + T) c hi
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) (hr : 0 < r) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      (G ∩ {sample | ¬rightBoundaryIntervalGridGood N lam (x0 + T) c r hi
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample}) ≤
      RightTail.intervalGridFailureBound N r := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let bad : Set (FiniteSample n) := {sample |
    ¬rightBoundaryIntervalGridGood N lam (x0 + T) c r hi
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample}
  let F : FiniteSample n → ℝ := fun sample ↦
    RightTail.intervalGridFailureIndicator N lam (x0 + T) c r hi
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample
  have hGambient : MeasurableSet G :=
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le T G hG
  have hmap := (measurable_revealedSnapshotAtElapsed (n := n) hlam0 hlamHalf x0 p0 T).prodMk
    measurable_id
  have hbad : MeasurableSet bad :=
    (measurableSet_rightBoundaryIntervalGridGood N lam (x0 + T) c r hhi).compl.preimage hmap
  have hF : Measurable F :=
    (RightTail.measurable_intervalGridFailureIndicator N lam (x0 + T) c r hhi).comp hmap
  have hFint : Integrable F μ := Integrable.of_bound hF.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun sample ↦
      RightTail.norm_intervalGridFailureIndicator_le N lam (x0 + T) c r hi _ _)
  have hcond := condExp_actual_intervalGridFailure_le (N := N) hn hlam0 hlamHalf x0 p0 T hT
    c r hhi G hGambient hregular hr
  have hmono : (∫ sample in G, μ[F | usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] sample ∂μ) ≤
      ∫ _sample in G, RightTail.intervalGridFailureBound N r ∂μ :=
    integral_mono_ae integrable_condExp.integrableOn (integrable_const _) hcond
  rw [setIntegral_condExp
    ((usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le T) hFint hG] at hmono
  have hfind : F = bad.indicator (1 : FiniteSample n → ℝ) := by
    funext sample
    simp only [F, bad, RightTail.intervalGridFailureIndicator, Set.indicator_apply,
      mem_ofPred_eq, Pi.one_apply]
  rw [hfind, integral_indicator_one hbad, measureReal_restrict_apply hbad,
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hmono
  have hlast : μ.real G * RightTail.intervalGridFailureBound N r ≤
      RightTail.intervalGridFailureBound N r := by
    simpa using mul_le_mul_of_nonneg_right (measureReal_le_one (μ := μ) (s := G))
      (RightTail.intervalGridFailureBound_nonneg N r)
  simpa only [inter_comm, μ] using hmono.trans hlast

end FiniteSample
end OTSelector
