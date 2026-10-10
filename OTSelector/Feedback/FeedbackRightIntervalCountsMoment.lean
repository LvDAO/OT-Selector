import OTSelector.Feedback.FeedbackRightBoundaryLocalization

/-!
# Fixed-endpoint current control under the actual boundary law

The iid second moment on the unseen rectangle is transported to the full bulk conditional
sigma field.  This supplies the terminal-window current bound without a right-tail compensator.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical

namespace OTSelector.FiniteSample

variable {n : ℕ}

private theorem measurable_frozenCurrent_sq (lam xR y : ℝ) :
    Measurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      rightBoundaryFrozenCurrent lam xR y pair.1 pair.2 ^ 2 :=
  ((measurable_rightBoundaryFrozenCurrent lam xR).comp
    (measurable_const.prodMk measurable_id)).pow_const 2

attribute [local irreducible] rightBoundaryFrozenCurrent rightBoundaryFrozenEnergy

/-- Composition is proved before substituting the dependent actual snapshot, preventing
unnecessary unfolding of the complete feedback history in measurability elaboration. -/
theorem measurable_frozenCurrent_comp
    {Ω : Type*} [MeasurableSpace Ω] (lam xR y : ℝ)
    (boundary : Ω → RevealedSnapshot n) (sample : Ω → FiniteSample n)
    (hboundary : Measurable boundary) (hsample : Measurable sample) :
    Measurable fun ω ↦ rightBoundaryFrozenCurrent lam xR y (boundary ω) (sample ω) :=
  (measurable_rightBoundaryFrozenCurrent (n := n) lam xR).comp
    (measurable_const.prodMk (hboundary.prodMk hsample))

theorem stronglyMeasurable_frozenEnergy_comp
    {Ω : Type*} [MeasurableSpace Ω] (lam xR xEnd : ℝ)
    (boundary : Ω → RevealedSnapshot n) (sample : Ω → FiniteSample n)
    (hboundary : Measurable boundary) (hsample : Measurable sample) :
    StronglyMeasurable fun ω ↦ rightBoundaryFrozenEnergy lam xR xEnd (boundary ω) (sample ω) :=
  (stronglyMeasurable_rightBoundaryFrozenEnergy (n := n) lam xR xEnd).comp_measurable
    (hboundary.prodMk hsample)

private theorem norm_frozenCurrent_sq_le (lam xR y : ℝ)
    (boundary : RevealedSnapshot n) (sample : FiniteSample n) :
    ‖rightBoundaryFrozenCurrent lam xR y boundary sample ^ 2‖ ≤ (3 * (n : ℝ)) ^ 2 := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_rightBoundaryFrozenCurrent_le lam xR y boundary sample) 2

/-- The boundary moment localization includes the constant-size boundary current gap. -/
def rightBoundaryMomentGood (lam xR B L : ℝ) (boundary : RevealedSnapshot n) : Prop :=
  (rightBoundarySourceUnseenCount (revealedSnapshotState boundary) : ℝ) ∈ Icc (B / 2) (2 * B) ∧
  (rightBoundaryTargetUnseenCount (revealedSnapshotState boundary) : ℝ) ∈ Icc (B / 2) (2 * B) ∧
  |(rightBoundaryTargetUnseenCount (revealedSnapshotState boundary) : ℝ) -
    (rightBoundarySourceUnseenCount (revealedSnapshotState boundary) : ℝ)| ≤ L ∧
  |rightBoundaryFrozenHeight lam xR boundary| ≤ L * Real.sqrt B ∧
  |rightBoundaryFrozenHeight lam xR boundary| ≤ B / 8

/-- The actual boundary scalar candidate has a linear-buffer second moment. -/
theorem rightBoundaryScalarCandidate_frozenCurrent_sq_le
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) {y B L : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 1 ≤ B) (hBn : B ≤ (n : ℝ) / 2) (hL : 0 ≤ L) (hy : x0 + (T : ℝ) ≤ y)
    (sample : FiniteSample n)
    (hgood : rightBoundaryMomentGood lam (x0 + T) B L
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) :
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
      (fun boundary completed ↦ rightBoundaryFrozenCurrent lam (x0 + T) y boundary completed ^ 2)
      sample ≤ (4 + (17 * L) ^ 2) * B := by
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 T
  let S := state.seenSource.disjSum state.seenTarget
  have hdecoded : revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) = state := by
    simp [state, revealedSnapshotState, revealedSnapshotAtElapsed, revealedSnapshotFromState]
  simp only [rightBoundaryMomentGood, hdecoded] at hgood
  have hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource := by
    intro i
    simp [S]
  have htarget : ∀ i : Fin n, (Sum.inr i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenTarget := by
    intro i
    simp [S]
  have hR : (x0 + (T : ℝ), segmentCurve state.x state.p (state.slope lam) (x0 + T)) ∈
      rightTailUnclippedRegion n := by
    have hsmall := hgood.2.2.2.2
    change |segmentCurve state.x state.p (state.slope lam) (x0 + T)| ≤ B / 8 at hsmall
    rw [hboundary] at hsmall ⊢
    exact rightTailUnclippedRegion_of_buffer (lt_of_lt_of_le zero_lt_one hB) hBn hsmall
  have hpositive : ∀ label : feedbackUnseenFinset S,
      (unitSquareUniform : Measure MarkedHeight)
        (feedbackLabelRemainingSetAt lam state (x0 + T) (label : FeedbackLabel n)) ≠ 0 := by
    intro label
    let : IsProbabilityMeasure
        ((unitSquareUniform : Measure MarkedHeight)[|
          feedbackLabelRemainingSetAt lam state (x0 + T) (label : FeedbackLabel n)]) := by
      change IsProbabilityMeasure (rightBoundaryHistoryFactorLaw lam (x0 + T) state _)
      rw [RightTail.historyFactorLaw_eq_fixedLaw]
      exact RightTail.fixedLaw_isProbabilityMeasure hn (RightTail.unseenSourceGroup S) hR label
    intro hzero
    exact (IsProbabilityMeasure.ne_zero _) (cond_eq_zero_of_meas_eq_zero hzero)
  have hF := (measurable_frozenCurrent_sq (n := n) lam (x0 + T) y).stronglyMeasurable
  change twoSnapshotNormalizedScalar lam (x0 + T) _
    (sample.revealedSnapshotFromState state) (sample.revealedSnapshotFromState state) ≤ _
  rw [twoSnapshotNormalizedScalar_revealedSnapshotFromState_eq _ _ _ hF _ state S
    hsource htarget sample, RightTail.normalized_unseen_eq_integral_fixedLaw hn lam (x0 + T) state S hR]
  have hm := rightBoundaryHistoryCurrent_secondMoment_le_components lam (x0 + T) y B
    (1 / 2) 2 L 8 state S hsource htarget sample (feedbackSeenTuple S sample) hpositive
    hB (by norm_num) (by norm_num) hL (by norm_num)
    (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hgood.1)
    (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hgood.2.1)
    hgood.2.2.1 hgood.2.2.2.1
    (rightBoundaryHistoryProbability_difference_le hn lam (x0 + T) y B state hboundary
      (lt_of_lt_of_le zero_lt_one hB) hBn hgood.2.2.2.2 hy)
  simp_rw [RightTail.historyFactorLaw_eq_fixedLaw lam (x0 + T) state S] at hm
  convert hm using 1
  ring

/-- The frozen endpoint current has second moment `O(B)` conditional on the entire bulk history. -/
theorem condExp_actual_frozenCurrent_sq_le
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT : 0 < T) {y B L : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 1 ≤ B) (hBn : B ≤ (n : ℝ) / 2) (hL : 0 ≤ L) (hy : x0 + (T : ℝ) ≤ y)
    (G : Set (FiniteSample n)) (hG : MeasurableSet G)
    (hgood : ∀ sample ∈ G, rightBoundaryMomentGood lam (x0 + T) B L
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
      (fun sample ↦ rightBoundaryFrozenCurrent lam (x0 + T) y
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample ^ 2) |
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
        (finiteSampleLaw n : Measure (FiniteSample n)).restrict G]
      fun _ ↦ (4 + (17 * L) ^ 2) * B := by
  have heq := condExp_actualBoundaryEvaluation_eq_candidate hn hlam0 hlamHalf x0 p0 T hT
    (fun boundary sample ↦ rightBoundaryFrozenCurrent lam (x0 + T) y boundary sample ^ 2)
    (measurable_frozenCurrent_sq (n := n) lam (x0 + T) y).stronglyMeasurable (sq_nonneg (3 * (n : ℝ)))
    (norm_frozenCurrent_sq_le lam (x0 + T) y)
  filter_upwards [ae_restrict_of_ae heq, ae_restrict_mem hG] with sample heq hmem
  rw [heq]
  exact rightBoundaryScalarCandidate_frozenCurrent_sq_le hn hlam0 hlamHalf x0 p0 T
    hboundary hB hBn hL hy sample (hgood sample hmem)

private theorem measureReal_inter_abs_ge_le_of_condExp_sq_le
    {Ω : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ m0)
    (f : Ω → ℝ) (hf : Measurable fun ω ↦ f ω ^ 2)
    (hint : Integrable (fun ω ↦ f ω ^ 2) μ)
    {G : Set Ω} (hG : MeasurableSet[m] G) {a V : ℝ} (ha : 0 < a) (hV : 0 ≤ V)
    (hcond : μ[(fun ω ↦ f ω ^ 2) | m] ≤ᵐ[μ.restrict G] fun _ ↦ V) :
    μ.real (G ∩ {ω | a ≤ |f ω|}) ≤ V / a ^ 2 := by
  have hce : Integrable (μ[(fun ω ↦ f ω ^ 2) | m]) μ := integrable_condExp
  have hmono : (∫ ω in G, μ[(fun ω ↦ f ω ^ 2) | m] ω ∂μ) ≤ ∫ _ω in G, V ∂μ :=
    integral_mono_ae hce.integrableOn (integrable_const _) hcond
  rw [setIntegral_condExp hm hint hG, integral_const,
    measureReal_restrict_apply_univ, smul_eq_mul] at hmono
  have hupper : (∫ ω in G, f ω ^ 2 ∂μ) ≤ V :=
    hmono.trans (by simpa using mul_le_mul_of_nonneg_right (measureReal_le_one (μ := μ) (s := G)) hV)
  have hmarkov : a ^ 2 * (μ.restrict G).real {ω | a ^ 2 ≤ f ω ^ 2} ≤ ∫ ω in G, f ω ^ 2 ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω ↦ sq_nonneg (f ω)) hint.integrableOn (a ^ 2)
  rw [measureReal_restrict_apply (measurableSet_le measurable_const hf), inter_comm] at hmarkov
  have hset : {ω | a ^ 2 ≤ f ω ^ 2} = {ω | a ≤ |f ω|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [← sq_abs (f ω)]
    exact sq_le_sq₀ ha.le (abs_nonneg _)
  rw [hset] at hmarkov
  exact (le_div_iff₀ (sq_pos_of_pos ha)).mpr (by
    simpa only [mul_comm] using hmarkov.trans hupper)

/-- Markov control of the actual frozen endpoint current on a bulk-measurable localization. -/
theorem measureReal_actual_frozenCurrent_tail_inter_le
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT : 0 < T) {y B L a : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 1 ≤ B) (hBn : B ≤ (n : ℝ) / 2) (hL : 0 ≤ L) (hy : x0 + (T : ℝ) ≤ y)
    (ha : 0 < a) (G : Set (FiniteSample n))
    (hG : MeasurableSet[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] G)
    (hgood : ∀ sample ∈ G, rightBoundaryMomentGood lam (x0 + T) B L
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      (G ∩ {sample | a ≤ |rightBoundaryFrozenCurrent lam (x0 + T) y
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample|}) ≤
      (4 + (17 * L) ^ 2) * B / a ^ 2 := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let K : FiniteSample n → ℝ := fun sample ↦ rightBoundaryFrozenCurrent lam (x0 + T) y
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample
  have hK : Measurable K := measurable_frozenCurrent_comp lam (x0 + T) y _ _
    (measurable_revealedSnapshotAtElapsed (n := n) hlam0 hlamHalf x0 p0 T) measurable_id
  have hKsq : Measurable fun sample ↦ K sample ^ 2 := hK.pow_const 2
  have hKsqint : Integrable (fun sample ↦ K sample ^ 2) μ :=
    Integrable.of_bound hKsq.aestronglyMeasurable ((3 * (n : ℝ)) ^ 2)
      (Filter.Eventually.of_forall fun sample ↦ norm_frozenCurrent_sq_le lam (x0 + T) y _ sample)
  exact measureReal_inter_abs_ge_le_of_condExp_sq_le μ
    ((usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le T) K hKsq hKsqint hG ha
    (mul_nonneg (by positivity) (zero_le_one.trans hB))
    (condExp_actual_frozenCurrent_sq_le hn hlam0 hlamHalf x0 p0 T hT hboundary hB hBn hL hy G
      ((usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le T G hG) hgood)

/-- The complete moment localization is measurable in the full bulk boundary sigma field. -/
theorem measurableSet_actual_rightBoundaryMomentGood
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (B L : ℝ) :
    MeasurableSet[usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      {sample | rightBoundaryMomentGood lam (x0 + T) B L
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)} := by
  have hs : Measurable fun boundary : RevealedSnapshot n ↦
      (rightBoundarySourceUnseenCount (revealedSnapshotState boundary) : ℝ) :=
    (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_rightBoundarySourceUnseenCount.comp measurable_revealedSnapshotState)
  have ht : Measurable fun boundary : RevealedSnapshot n ↦
      (rightBoundaryTargetUnseenCount (revealedSnapshotState boundary) : ℝ) :=
    (measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_rightBoundaryTargetUnseenCount.comp measurable_revealedSnapshotState)
  have hq := (measurable_rightBoundaryFrozenHeight (n := n) lam (x0 + T)).abs
  have hset : MeasurableSet {boundary : RevealedSnapshot n |
      rightBoundaryMomentGood lam (x0 + T) B L boundary} :=
    (measurableSet_Icc.preimage hs).inter ((measurableSet_Icc.preimage ht).inter
      ((measurableSet_le (ht.sub hs).abs measurable_const).inter
        ((measurableSet_le hq measurable_const).inter (measurableSet_le hq measurable_const))))
  exact hset.preimage ((stronglyAdapted_rawRevealedSnapshot hlam0 hlamHalf x0 p0 T).mono
    (rawRevealedFiltration_le_usual hlam0 hlamHalf x0 p0 T)).measurable

/-- The only additional loss beyond buffer localization is the actual endpoint current tail.
The no-tie identities hold almost surely under the original law. -/
theorem measureReal_not_rightBoundaryMomentGood_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) {B H L : ℝ}
    (hHL : H ≤ L * Real.sqrt B) (hHB : H ≤ B / 8) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      {sample | ¬rightBoundaryMomentGood lam (x0 + T) B L
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)} ≤
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample | ¬rightBoundaryBufferGood lam (x0 + T) B H
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)} +
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample | L < |RelativeVC.feedbackRankDiscrepancy (feedbackSourceRankArray sample)
          (feedbackTargetRankArray sample) (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
          (x0 + (T : ℝ))|} := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let E : Set (FiniteSample n) := {sample | ¬rightBoundaryBufferGood lam (x0 + T) B H
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)}
  let C : Set (FiniteSample n) := {sample | L < |RelativeVC.feedbackRankDiscrepancy
    (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
    (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample) (x0 + (T : ℝ))|}
  have hsubset : {sample | ¬rightBoundaryMomentGood lam (x0 + T) B L
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)} ⊆
      E ∪ (C ∪ feedbackTieEvent lam x0 p0) := by
    intro sample hbad
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have hbuffer : rightBoundaryBufferGood lam (x0 + T) B H
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) := by
      simpa only [E, mem_ofPred_eq, not_not] using hnot.1
    have hcurrent : |RelativeVC.feedbackRankDiscrepancy (feedbackSourceRankArray sample)
        (feedbackTargetRankArray sample) (rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ))| ≤ L := by
      simpa only [C, mem_ofPred_eq, not_lt] using hnot.2.1
    have hNoTie : sample.NoFeedbackTies lam x0 p0 := by
      simpa only [feedbackTieEvent, mem_ofPred_eq, not_not] using hnot.2.2
    apply hbad
    refine ⟨hbuffer.2.1, hbuffer.2.2, ?_, hbuffer.1.trans hHL, hbuffer.1.trans hHB⟩
    rwa [rightBoundaryUnseenGap_eq_rankDiscrepancy hlam0 hlamHalf x0 p0 T sample hNoTie]
  have htie : μ.real (feedbackTieEvent lam x0 p0) = 0 := by
    simp only [Measure.real, μ, feedbackTieEvent_measure_zero hlam0 hlamHalf x0 p0, ENNReal.toReal_zero]
  have h0 := measureReal_mono (μ := μ) hsubset
  have h1 := measureReal_union_le (μ := μ) E (C ∪ feedbackTieEvent lam x0 p0)
  have h2 := measureReal_union_le (μ := μ) C (feedbackTieEvent lam x0 p0)
  rw [htie] at h2
  change μ.real _ ≤ μ.real E + μ.real C
  linarith

/-- The moment event also supplies the entire interval-density regularity condition. -/
theorem rightBoundaryMomentGood.intervalRegular
    (hn : 0 < n) {lam B L : ℝ} (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2)
    (hL : 0 ≤ L) {boundary : RevealedSnapshot n}
    (hgood : rightBoundaryMomentGood lam ((n : ℝ) - B) B L boundary) :
    rightBoundaryIntervalRegular lam ((n : ℝ) - B) (1 / 8)
      (fun _ ↦ (n : ℝ) - (8 * L * Real.sqrt B + 1)) boundary := by
  apply rightBoundaryIntervalRegular_of_buffer_components hn lam hB hBn _ boundary rfl
    hgood.2.2.2.2
  · positivity
  · nlinarith [hgood.2.2.2.1]
  · exact hgood.1.1
  · exact hgood.2.1.1

/-- The same actual moment event supports the two-color density grid, with failure `16 / n³`. -/
theorem measureReal_actual_intervalGridFailure_on_moment_le
    (hn : 1 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT : 0 < T) {B L : ℝ}
    (hboundary : x0 + (T : ℝ) = (n : ℝ) - B)
    (hB : 0 < B) (hBn : B ≤ (n : ℝ) / 2) (hL : 0 ≤ L) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
      ({sample | rightBoundaryMomentGood lam (x0 + T) B L
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)} ∩
       {sample | ¬rightBoundaryIntervalGridGood n lam (x0 + T) (1 / 8) (60 * Real.log n)
        (fun _ ↦ (n : ℝ) - (8 * L * Real.sqrt B + 1))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample}) ≤
      16 / (n : ℝ) ^ 3 := by
  apply (measureReal_actual_intervalGridFailure_inter_le (Nat.zero_lt_of_lt hn)
    hlam0 hlamHalf x0 p0 T hT (1 / 8) (60 * Real.log n) measurable_const _
    (measurableSet_actual_rightBoundaryMomentGood hlam0 hlamHalf x0 p0 T B L) ?_ ?_).trans
    (RightTail.intervalGridFailureBound_log_le (by omega))
  · intro sample hsample
    rw [hboundary] at hsample ⊢
    exact hsample.intervalRegular (Nat.zero_lt_of_lt hn) hB hBn hL
  · exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))

end OTSelector.FiniteSample
