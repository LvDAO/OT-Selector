import OTSelector.Feedback.FeedbackRightTailStopping
import OTSelector.Feedback.FiniteHistoryRawScalar
import OTSelector.Feedback.FiniteHistorySnapshotSection
import OTSelector.Feedback.FiniteHistoryPathSection
import OTSelector.Feedback.FiniteHistoryCrossingAtomless
import OTSelector.Feedback.RankGapTail
import OTSelector.Probability.FiniteProductIndicatorMoment
import OTSelector.Probability.NormalizedRestrictionTV
import OTSelector.Probability.CountingProcess.UsualRectangleLift

/-!
# Scalar conditioning at the actual right boundary

The revealed filtration stores a state and masked arrays rather than a dependent tuple of unseen
labels.  This file gives a measurable evaluator for the scalar conditional averages used at the
right boundary.  It reads two snapshots: the first freezes the boundary data, while the second
supplies the later revealed state.  Unseen coordinates are filled from an independent auxiliary
finite sample and restricted to the second snapshot's strict remaining rectangle.

No regular conditional kernel or bundled proof interface is introduced.  The evaluator is an
ordinary normalized set integral and is measurable in both snapshots.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Decoding and completing a revealed snapshot -/

/-- The post-jump state stored in a revealed snapshot. -/
def revealedSnapshotState (snapshot : RevealedSnapshot n) : FeedbackStepState n :=
  FeedbackStepState.unpack snapshot.1

@[fun_prop]
theorem measurable_revealedSnapshotState :
    Measurable (revealedSnapshotState : RevealedSnapshot n → FeedbackStepState n) :=
  FeedbackStepState.measurable_unpack.comp measurable_fst

/-- Height obtained by continuing the state stored in a boundary snapshot to the deterministic
boundary coordinate `xR`. -/
noncomputable def rightBoundaryFrozenHeight
    (lam xR : ℝ) (boundary : RevealedSnapshot n) : ℝ :=
  let state := revealedSnapshotState boundary
  segmentCurve state.x state.p (state.slope lam) xR

@[fun_prop]
theorem measurable_rightBoundaryFrozenHeight (lam xR : ℝ) :
    Measurable (rightBoundaryFrozenHeight (n := n) lam xR) := by
  have hstate := measurable_revealedSnapshotState (n := n)
  have hx := FeedbackStepState.measurable_x.comp hstate
  have hp := FeedbackStepState.measurable_p.comp hstate
  have hslope := (FeedbackStepState.measurable_slope lam).comp hstate
  change Measurable fun boundary : RevealedSnapshot n ↦
    (revealedSnapshotState boundary).p +
      (revealedSnapshotState boundary).slope lam *
        (xR - (revealedSnapshotState boundary).x)
  exact hp.add (hslope.mul (measurable_const.sub hx))

/-- On the no-tie component, decoding the actual snapshot returns the actual safe boundary
height. -/
theorem rightBoundaryFrozenHeight_revealedSnapshotAtElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) =
      rightBoundaryHeight hlam0 hlamHalf x0 p0 T sample := by
  rw [rightBoundaryHeight, safeFeedbackHeightAtElapsed, ite_eq_left hNoTie,
    sample.feedbackHeightAtElapsed_eq_segmentCurve hlam0 hlamHalf x0 p0 T]
  rfl

/-! ## Frozen-height future energy -/

/-- One-label fixed-height remaining region at coordinate `y`. -/
def rightBoundaryFrozenRemainingSet (q y : ℝ) : FeedbackLabel n → Set MarkedHeight
  | Sum.inl _ =>
      {z | y < (n : ℝ) * (z.1 : ℝ) + (1 - (z.2 : ℝ)) * q}
  | Sum.inr _ =>
      {z | y < (n : ℝ) * (z.1 : ℝ) - (1 + (z.2 : ℝ)) * q}

/-- Target remaining labels have positive sign and source remaining labels negative sign. -/
def rightBoundaryLabelSign : FeedbackLabel n → ℝ
  | Sum.inl _ => -1
  | Sum.inr _ => 1

theorem measurableSet_rightBoundaryFrozenRemainingSet
    (q y : ℝ) (label : FeedbackLabel n) :
    MeasurableSet (rightBoundaryFrozenRemainingSet (n := n) q y label) := by
  cases label with
  | inl i =>
      simpa [rightBoundaryFrozenRemainingSet, sourceRawRemainingSet, mul_comm] using
        (isOpen_sourceRawRemainingSet n q y).measurableSet
  | inr j =>
      simpa [rightBoundaryFrozenRemainingSet, targetRawRemainingSet, mul_comm] using
        (isOpen_targetRawRemainingSet n q y).measurableSet

/-- Source labels still to the right of `y`, with height frozen from the boundary snapshot. -/
noncomputable def rightBoundaryFrozenSourceCount
    (lam xR y : ℝ) (boundary : RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  ∑ i : Fin n, if i ∉ (revealedSnapshotState boundary).seenSource ∧
      y < completed.sourcePhase i (rightBoundaryFrozenHeight lam xR boundary)
    then 1 else 0

/-- Target analogue of `rightBoundaryFrozenSourceCount`. -/
noncomputable def rightBoundaryFrozenTargetCount
    (lam xR y : ℝ) (boundary : RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  ∑ j : Fin n, if j ∉ (revealedSnapshotState boundary).seenTarget ∧
      y < completed.targetPhase j (rightBoundaryFrozenHeight lam xR boundary)
    then 1 else 0

/-- Frozen-height continuation of the signed current, written as target remaining minus source
remaining.  On an actual boundary snapshot this equals boundary current plus later source
crossings minus later target crossings. -/
noncomputable def rightBoundaryFrozenCurrent
    (lam xR y : ℝ) (boundary : RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  rightBoundaryFrozenTargetCount lam xR y boundary completed -
    rightBoundaryFrozenSourceCount lam xR y boundary completed

/-- Quadratic current energy of the frozen continuation on `(xR, xEnd]`. -/
noncomputable def rightBoundaryFrozenEnergy
    (lam xR xEnd : ℝ) (boundary : RevealedSnapshot n)
    (completed : FiniteSample n) : ℝ :=
  ∫ y : ℝ in Ioc xR xEnd,
    rightBoundaryFrozenCurrent lam xR y boundary completed ^ 2 ∂volume

theorem measurable_rightBoundaryFrozenSourceCount (lam xR : ℝ) :
    Measurable fun p : ℝ × (RevealedSnapshot n × FiniteSample n) ↦
      rightBoundaryFrozenSourceCount lam xR p.1 p.2.1 p.2.2 := by
  classical
  unfold rightBoundaryFrozenSourceCount
  apply Finset.measurable_sum
  intro i _hi
  have hphase : Measurable fun p : ℝ × (RevealedSnapshot n × FiniteSample n) ↦
      p.2.2.sourcePhase i (rightBoundaryFrozenHeight lam xR p.2.1) := by
    unfold FiniteSample.sourcePhase FiniteSample.sourceSlope
    fun_prop
  have hstate : Measurable fun p : ℝ × (RevealedSnapshot n × FiniteSample n) ↦
      revealedSnapshotState p.2.1 :=
    measurable_revealedSnapshotState.comp (measurable_fst.comp measurable_snd)
  have hseen : MeasurableSet {p : ℝ × (RevealedSnapshot n × FiniteSample n) |
      i ∈ (revealedSnapshotState p.2.1).seenSource} :=
    (FeedbackStepState.measurable_seenSource.comp hstate) (measurableSet_mem_finset i)
  have hset : MeasurableSet {p : ℝ × (RevealedSnapshot n × FiniteSample n) |
      i ∉ (revealedSnapshotState p.2.1).seenSource ∧
      p.1 < p.2.2.sourcePhase i (rightBoundaryFrozenHeight lam xR p.2.1)} :=
    hseen.compl.inter (measurableSet_lt measurable_fst hphase)
  exact Measurable.ite hset measurable_const measurable_const

theorem measurable_rightBoundaryFrozenTargetCount (lam xR : ℝ) :
    Measurable fun p : ℝ × (RevealedSnapshot n × FiniteSample n) ↦
      rightBoundaryFrozenTargetCount lam xR p.1 p.2.1 p.2.2 := by
  classical
  unfold rightBoundaryFrozenTargetCount
  apply Finset.measurable_sum
  intro j _hj
  have hphase : Measurable fun p : ℝ × (RevealedSnapshot n × FiniteSample n) ↦
      p.2.2.targetPhase j (rightBoundaryFrozenHeight lam xR p.2.1) := by
    unfold FiniteSample.targetPhase FiniteSample.targetSlope
    fun_prop
  have hstate : Measurable fun p : ℝ × (RevealedSnapshot n × FiniteSample n) ↦
      revealedSnapshotState p.2.1 :=
    measurable_revealedSnapshotState.comp (measurable_fst.comp measurable_snd)
  have hseen : MeasurableSet {p : ℝ × (RevealedSnapshot n × FiniteSample n) |
      j ∈ (revealedSnapshotState p.2.1).seenTarget} :=
    (FeedbackStepState.measurable_seenTarget.comp hstate) (measurableSet_mem_finset j)
  have hset : MeasurableSet {p : ℝ × (RevealedSnapshot n × FiniteSample n) |
      j ∉ (revealedSnapshotState p.2.1).seenTarget ∧
      p.1 < p.2.2.targetPhase j (rightBoundaryFrozenHeight lam xR p.2.1)} :=
    hseen.compl.inter (measurableSet_lt measurable_fst hphase)
  exact Measurable.ite hset measurable_const measurable_const

theorem measurable_rightBoundaryFrozenCurrent (lam xR : ℝ) :
    Measurable fun p : ℝ × (RevealedSnapshot n × FiniteSample n) ↦
      rightBoundaryFrozenCurrent lam xR p.1 p.2.1 p.2.2 := by
  exact (measurable_rightBoundaryFrozenTargetCount (n := n) lam xR).sub
    (measurable_rightBoundaryFrozenSourceCount (n := n) lam xR)

theorem measurable_rightBoundaryFrozenCurrent_seenUnseenMerge
    (lam xR xBase : ℝ) (boundary : RevealedSnapshot n)
    (S : Finset (FeedbackLabel n)) (seen : S → MarkedHeight) :
    Measurable fun pair : ℝ × (feedbackUnseenFinset S → MarkedHeight) ↦
      rightBoundaryFrozenCurrent lam xR (xBase + pair.1) boundary
        (finiteSampleSeenUnseenMerge S seen pair.2) := by
  classical
  have hmerge : Measurable fun unseen : feedbackUnseenFinset S → MarkedHeight ↦
      finiteSampleSeenUnseenMerge S seen unseen :=
    (measurable_finiteSampleSeenUnseenMerge S).comp
      (measurable_const.prodMk measurable_id)
  have hcompleted : Measurable fun pair :
      ℝ × (feedbackUnseenFinset S → MarkedHeight) ↦
      finiteSampleSeenUnseenMerge S seen pair.2 := hmerge.comp measurable_snd
  have hsourcePhase (i : Fin n) : Measurable fun pair :
      ℝ × (feedbackUnseenFinset S → MarkedHeight) ↦
      (finiteSampleSeenUnseenMerge S seen pair.2).sourcePhase i
        (rightBoundaryFrozenHeight lam xR boundary) := by
    unfold FiniteSample.sourcePhase FiniteSample.sourceSlope
    exact (measurable_const.mul
      (((FiniteSample.measurable_sourceHeight i).subtype_coe).comp hcompleted)).add
        ((measurable_const.sub
          (((FiniteSample.measurable_sourceMark i).subtype_coe).comp hcompleted)).mul
            measurable_const)
  have htargetPhase (j : Fin n) : Measurable fun pair :
      ℝ × (feedbackUnseenFinset S → MarkedHeight) ↦
      (finiteSampleSeenUnseenMerge S seen pair.2).targetPhase j
        (rightBoundaryFrozenHeight lam xR boundary) := by
    unfold FiniteSample.targetPhase FiniteSample.targetSlope
    exact (measurable_const.mul
      (((FiniteSample.measurable_targetHeight j).subtype_coe).comp hcompleted)).sub
        ((measurable_const.add
          (((FiniteSample.measurable_targetMark j).subtype_coe).comp hcompleted)).mul
            measurable_const)
  have hsource : Measurable fun pair :
      ℝ × (feedbackUnseenFinset S → MarkedHeight) ↦
      rightBoundaryFrozenSourceCount lam xR (xBase + pair.1) boundary
        (finiteSampleSeenUnseenMerge S seen pair.2) := by
    unfold rightBoundaryFrozenSourceCount
    apply Finset.measurable_sum
    intro i _hi
    by_cases hseen : i ∉ (revealedSnapshotState boundary).seenSource
    · have hset : MeasurableSet {pair :
          ℝ × (feedbackUnseenFinset S → MarkedHeight) |
          xBase + pair.1 <
            (finiteSampleSeenUnseenMerge S seen pair.2).sourcePhase i
              (rightBoundaryFrozenHeight lam xR boundary)} :=
        measurableSet_lt (measurable_const.add measurable_fst) (hsourcePhase i)
      simpa [hseen] using
        (Measurable.ite hset (measurable_const : Measurable fun _ ↦ (1 : ℝ))
          measurable_const)
    · simp [hseen]
  have htarget : Measurable fun pair :
      ℝ × (feedbackUnseenFinset S → MarkedHeight) ↦
      rightBoundaryFrozenTargetCount lam xR (xBase + pair.1) boundary
        (finiteSampleSeenUnseenMerge S seen pair.2) := by
    unfold rightBoundaryFrozenTargetCount
    apply Finset.measurable_sum
    intro j _hj
    by_cases hseen : j ∉ (revealedSnapshotState boundary).seenTarget
    · have hset : MeasurableSet {pair :
          ℝ × (feedbackUnseenFinset S → MarkedHeight) |
          xBase + pair.1 <
            (finiteSampleSeenUnseenMerge S seen pair.2).targetPhase j
              (rightBoundaryFrozenHeight lam xR boundary)} :=
        measurableSet_lt (measurable_const.add measurable_fst) (htargetPhase j)
      simpa [hseen] using
        (Measurable.ite hset (measurable_const : Measurable fun _ ↦ (1 : ℝ))
          measurable_const)
    · simp [hseen]
  unfold rightBoundaryFrozenCurrent
  exact htarget.sub hsource

theorem stronglyMeasurable_rightBoundaryFrozenEnergy
    (lam xR xEnd : ℝ) :
    StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      rightBoundaryFrozenEnergy lam xR xEnd p.1 p.2 := by
  let G : (RevealedSnapshot n × FiniteSample n) → ℝ → ℝ :=
    fun p y ↦ (Ioc xR xEnd).indicator
      (fun y' ↦ rightBoundaryFrozenCurrent lam xR y' p.1 p.2 ^ 2) y
  have hG : StronglyMeasurable fun
      p : (RevealedSnapshot n × FiniteSample n) × ℝ ↦ G p.1 p.2 := by
    have hmap : Measurable fun
        p : (RevealedSnapshot n × FiniteSample n) × ℝ ↦
          (p.2, (p.1.1, p.1.2)) := measurable_snd.prodMk measurable_fst
    have hcurrent :=
      (measurable_rightBoundaryFrozenCurrent (n := n) lam xR).comp hmap
    exact (hcurrent.pow measurable_const).stronglyMeasurable.indicator
      (measurableSet_Ioc.preimage measurable_snd)
  have hG' : StronglyMeasurable (Function.uncurry G) := by
    change StronglyMeasurable fun
      p : (RevealedSnapshot n × FiniteSample n) × ℝ ↦ G p.1 p.2
    exact hG
  have hint := hG'.integral_prod_right (ν := volume)
  simpa [G, rightBoundaryFrozenEnergy, integral_indicator measurableSet_Ioc] using hint

theorem rightBoundaryFrozenSourceCount_mem_Icc
    (lam xR y : ℝ) (boundary : RevealedSnapshot n) (completed : FiniteSample n) :
    rightBoundaryFrozenSourceCount lam xR y boundary completed ∈
      Icc (0 : ℝ) (n : ℝ) := by
  classical
  constructor
  · unfold rightBoundaryFrozenSourceCount
    positivity
  · unfold rightBoundaryFrozenSourceCount
    calc
      (∑ i : Fin n, if i ∉ (revealedSnapshotState boundary).seenSource ∧
            y < completed.sourcePhase i (rightBoundaryFrozenHeight lam xR boundary)
          then (1 : ℝ) else 0) ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _hi
        split_ifs <;> norm_num
      _ = n := by simp

theorem rightBoundaryFrozenTargetCount_mem_Icc
    (lam xR y : ℝ) (boundary : RevealedSnapshot n) (completed : FiniteSample n) :
    rightBoundaryFrozenTargetCount lam xR y boundary completed ∈
      Icc (0 : ℝ) (n : ℝ) := by
  classical
  constructor
  · unfold rightBoundaryFrozenTargetCount
    positivity
  · unfold rightBoundaryFrozenTargetCount
    calc
      (∑ j : Fin n, if j ∉ (revealedSnapshotState boundary).seenTarget ∧
            y < completed.targetPhase j (rightBoundaryFrozenHeight lam xR boundary)
          then (1 : ℝ) else 0) ≤ ∑ _j : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _hj
        split_ifs <;> norm_num
      _ = n := by simp

theorem norm_rightBoundaryFrozenCurrent_le
    (lam xR y : ℝ) (boundary : RevealedSnapshot n) (completed : FiniteSample n) :
    ‖rightBoundaryFrozenCurrent lam xR y boundary completed‖ ≤ 3 * n := by
  have hs := rightBoundaryFrozenSourceCount_mem_Icc
    (n := n) lam xR y boundary completed
  have ht := rightBoundaryFrozenTargetCount_mem_Icc
    (n := n) lam xR y boundary completed
  rcases hs with ⟨hs0, hsN⟩
  rcases ht with ⟨ht0, htN⟩
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> unfold rightBoundaryFrozenCurrent <;> linarith

theorem norm_rightBoundaryFrozenEnergy_le
    (lam : ℝ) {xR xEnd : ℝ} (hx : xR ≤ xEnd)
    (boundary : RevealedSnapshot n) (completed : FiniteSample n) :
    ‖rightBoundaryFrozenEnergy lam xR xEnd boundary completed‖ ≤
      (xEnd - xR) * (3 * n) ^ 2 := by
  have hpoint : ∀ y ∈ Ioc xR xEnd,
      ‖rightBoundaryFrozenCurrent lam xR y boundary completed ^ 2‖ ≤
        (3 * (n : ℝ)) ^ 2 := by
    intro y _hy
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_rightBoundaryFrozenCurrent_le
      (n := n) lam xR y boundary completed) 2
  have hint := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure ℝ)) (s := Ioc xR xEnd)
    (f := fun y ↦ rightBoundaryFrozenCurrent lam xR y boundary completed ^ 2)
    (measure_Ioc_lt_top (μ := (volume : Measure ℝ))) hpoint
  simpa [rightBoundaryFrozenEnergy, Real.volume_Ioc, hx, max_eq_left,
    mul_comm] using hint

/-! ## Product-coordinate form -/

private noncomputable def rightBoundaryTargetUnseenEquiv
    (S : Finset (FeedbackLabel n)) (state : FeedbackStepState n)
    (htarget : ∀ j : Fin n, (Sum.inr j : FeedbackLabel n) ∈ S ↔
      j ∈ state.seenTarget) :
    {label : feedbackUnseenFinset S //
      ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j} ≃
      {j : Fin n // j ∉ state.seenTarget} where
  toFun label := ⟨Classical.choose label.property, by
    have hspec := Classical.choose_spec label.property
    have hnotS : (label : FeedbackLabel n) ∉ S :=
      (Finset.mem_sdiff.mp label.1.property).2
    intro hj
    exact hnotS (by rw [hspec]; exact (htarget _).2 hj)⟩
  invFun j := ⟨⟨Sum.inr j, by
    have hnotS : (Sum.inr (j : Fin n) : FeedbackLabel n) ∉ S := by
      intro hjS
      exact j.property ((htarget j).1 hjS)
    simpa [feedbackUnseenFinset] using hnotS⟩, ⟨j, rfl⟩⟩
  left_inv label := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec label.property).symm
  right_inv j := by
    apply Subtype.ext
    have hspec := Classical.choose_spec
      (show ∃ k : Fin n, (Sum.inr (j : Fin n) : FeedbackLabel n) = Sum.inr k from
        ⟨j, rfl⟩)
    exact (Sum.inr_injective hspec).symm

private noncomputable def rightBoundarySourceUnseenEquiv
    (S : Finset (FeedbackLabel n)) (state : FeedbackStepState n)
    (hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔
      i ∈ state.seenSource) :
    {label : feedbackUnseenFinset S //
      ¬ ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j} ≃
      {i : Fin n // i ∉ state.seenSource} where
  toFun label := ⟨Classical.choose (by
    rcases hlabel : (label : FeedbackLabel n) with i | j
    · exact ⟨i, hlabel⟩
    · exact False.elim (label.property ⟨j, hlabel⟩)), by
    have hspec := Classical.choose_spec (by
      rcases hlabel : (label : FeedbackLabel n) with i | j
      · exact ⟨i, hlabel⟩
      · exact False.elim (label.property ⟨j, hlabel⟩))
    have hnotS : (label : FeedbackLabel n) ∉ S :=
      (Finset.mem_sdiff.mp label.1.property).2
    intro hi
    exact hnotS (by rw [hspec]; exact (hsource _).2 hi)⟩
  invFun i := ⟨⟨Sum.inl i, by
    have hnotS : (Sum.inl (i : Fin n) : FeedbackLabel n) ∉ S := by
      intro hiS
      exact i.property ((hsource i).1 hiS)
    simpa [feedbackUnseenFinset] using hnotS⟩, by simp⟩
  left_inv label := by
    apply Subtype.ext
    apply Subtype.ext
    have hspec := Classical.choose_spec (by
      rcases hlabel : (label : FeedbackLabel n) with i | j
      · exact ⟨i, hlabel⟩
      · exact False.elim (label.property ⟨j, hlabel⟩))
    exact hspec.symm
  right_inv i := by
    apply Subtype.ext
    have hspec := Classical.choose_spec
      (show ∃ k : Fin n, (Sum.inl (i : Fin n) : FeedbackLabel n) = Sum.inl k from
        ⟨i, rfl⟩)
    exact (Sum.inl_injective hspec).symm

/-- On canonical seen/unseen coordinates, frozen current is the signed sum of the remaining
one-label indicators. -/
theorem rightBoundaryFrozenCurrent_merge_eq_signedIndicatorSum
    (lam xR y : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    rightBoundaryFrozenCurrent lam xR y (revealedSnapshotFromState sample state)
        (finiteSampleSeenUnseenMerge S seen unseen) =
      ∑ label : feedbackUnseenFinset S,
        rightBoundaryLabelSign (label : FeedbackLabel n) *
          if unseen label ∈ rightBoundaryFrozenRemainingSet (n := n)
              (segmentCurve state.x state.p (state.slope lam) xR) y
              (label : FeedbackLabel n)
          then 1 else 0 := by
  classical
  change
    (∑ j : Fin n, if j ∉ state.seenTarget ∧
        y < (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j
          (segmentCurve state.x state.p (state.slope lam) xR)
      then 1 else 0) -
      (∑ i : Fin n, if i ∉ state.seenSource ∧
        y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
          (segmentCurve state.x state.p (state.slope lam) xR)
      then 1 else 0) = _
  let targetTerm := fun label : feedbackUnseenFinset S ↦
    rightBoundaryLabelSign (label : FeedbackLabel n) *
      if unseen label ∈ rightBoundaryFrozenRemainingSet (n := n)
          (segmentCurve state.x state.p (state.slope lam) xR) y
          (label : FeedbackLabel n)
      then 1 else 0
  let targetIndexTerm := fun j : {j : Fin n // j ∉ state.seenTarget} ↦
    if y < (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j
        (segmentCurve state.x state.p (state.slope lam) xR)
    then (1 : ℝ) else 0
  have htargetReindex :
      (∑ label : {label : feedbackUnseenFinset S //
          ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j},
        targetTerm label) = ∑ j, targetIndexTerm j := by
    apply Fintype.sum_equiv (rightBoundaryTargetUnseenEquiv S state htarget)
    intro label
    let j := rightBoundaryTargetUnseenEquiv S state htarget label
    have hspec : (label : FeedbackLabel n) = Sum.inr (j : Fin n) :=
      Classical.choose_spec label.property
    have hlabelEq : label.1 =
        (⟨Sum.inr (j : Fin n), by
          have hnotS : (Sum.inr (j : Fin n) : FeedbackLabel n) ∉ S := by
            rw [← hspec]
            exact (Finset.mem_sdiff.mp label.1.property).2
          simpa [feedbackUnseenFinset] using hnotS⟩ : feedbackUnseenFinset S) := by
      apply Subtype.ext
      exact hspec
    have hpoint := congrFun
      (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen) label.1
    rw [hlabelEq] at hpoint
    simp only [feedbackUnseenTuple, feedbackLabelTuple,
      feedbackLabelPoint] at hpoint
    change targetTerm label = targetIndexTerm j
    simp only [targetTerm, targetIndexTerm]
    rw [hlabelEq]
    simp only [rightBoundaryLabelSign, one_mul]
    rw [← hpoint]
    simp [rightBoundaryFrozenRemainingSet,
      FiniteSample.targetPhase, FiniteSample.targetSlope,
      FiniteSample.targetPoint]
    rfl
  let sourceTerm := fun label : feedbackUnseenFinset S ↦
    rightBoundaryLabelSign (label : FeedbackLabel n) *
      if unseen label ∈ rightBoundaryFrozenRemainingSet (n := n)
          (segmentCurve state.x state.p (state.slope lam) xR) y
          (label : FeedbackLabel n)
      then 1 else 0
  let sourceIndexTerm := fun i : {i : Fin n // i ∉ state.seenSource} ↦
    if y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
        (segmentCurve state.x state.p (state.slope lam) xR)
    then (-1 : ℝ) else 0
  have hsourceReindex :
      (∑ label : {label : feedbackUnseenFinset S //
          ¬ ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j},
        sourceTerm label) = ∑ i, sourceIndexTerm i := by
    apply Fintype.sum_equiv (rightBoundarySourceUnseenEquiv S state hsource)
    intro label
    let i := rightBoundarySourceUnseenEquiv S state hsource label
    have hspec : (label : FeedbackLabel n) = Sum.inl (i : Fin n) :=
      Classical.choose_spec (by
        rcases hlabel : (label : FeedbackLabel n) with k | j
        · exact ⟨k, hlabel⟩
        · exact False.elim (label.property ⟨j, hlabel⟩))
    have hlabelEq : label.1 =
        (⟨Sum.inl (i : Fin n), by
          have hnotS : (Sum.inl (i : Fin n) : FeedbackLabel n) ∉ S := by
            rw [← hspec]
            exact (Finset.mem_sdiff.mp label.1.property).2
          simpa [feedbackUnseenFinset] using hnotS⟩ : feedbackUnseenFinset S) := by
      apply Subtype.ext
      exact hspec
    have hpoint := congrFun
      (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen) label.1
    rw [hlabelEq] at hpoint
    simp only [feedbackUnseenTuple, feedbackLabelTuple,
      feedbackLabelPoint] at hpoint
    change sourceTerm label = sourceIndexTerm i
    simp only [sourceTerm, sourceIndexTerm]
    rw [hlabelEq]
    simp only [rightBoundaryLabelSign, neg_one_mul]
    rw [← hpoint]
    simp [rightBoundaryFrozenRemainingSet,
      FiniteSample.sourcePhase, FiniteSample.sourceSlope,
      FiniteSample.sourcePoint]
    have hite (P : Prop) [Decidable P] :
        -(if P then (1 : ℝ) else 0) = if P then (-1 : ℝ) else 0 := by
      by_cases hP : P <;> simp [hP]
    exact hite _
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun label : feedbackUnseenFinset S ↦
      ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j)]
  rw [htargetReindex, hsourceReindex]
  have htargetAmbient :
      (∑ j : Fin n, if j ∉ state.seenTarget ∧
          y < (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j
            (segmentCurve state.x state.p (state.slope lam) xR)
        then (1 : ℝ) else 0) = ∑ j, targetIndexTerm j := by
    calc
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j ∉ state.seenTarget),
          if y < (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j
              (segmentCurve state.x state.p (state.slope lam) xR)
          then (1 : ℝ) else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hseen : j ∉ state.seenTarget <;>
          by_cases hphase : y <
            (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j
              (segmentCurve state.x state.p (state.slope lam) xR) <;>
          simp [hseen, hphase]
      _ = ∑ j, targetIndexTerm j := by
        simpa [targetIndexTerm] using
          (Finset.sum_subtype
            (Finset.univ.filter (fun j : Fin n ↦ j ∉ state.seenTarget))
            (fun j ↦ by simp) (fun j ↦
              if y < (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j
                  (segmentCurve state.x state.p (state.slope lam) xR)
              then (1 : ℝ) else 0))
  have hsourceAmbient :
      (∑ i : Fin n, if i ∉ state.seenSource ∧
          y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
            (segmentCurve state.x state.p (state.slope lam) xR)
        then (1 : ℝ) else 0) =
        ∑ i : {i : Fin n // i ∉ state.seenSource},
          if y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
              (segmentCurve state.x state.p (state.slope lam) xR)
          then (1 : ℝ) else 0 := by
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i ∉ state.seenSource),
          if y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
              (segmentCurve state.x state.p (state.slope lam) xR)
          then (1 : ℝ) else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hseen : i ∉ state.seenSource <;>
          by_cases hphase : y <
            (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
              (segmentCurve state.x state.p (state.slope lam) xR) <;>
          simp [hseen, hphase]
      _ = _ := by
        exact Finset.sum_subtype
          (Finset.univ.filter (fun i : Fin n ↦ i ∉ state.seenSource))
          (fun i ↦ by simp) (fun i ↦
            if y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
                (segmentCurve state.x state.p (state.slope lam) xR)
            then (1 : ℝ) else 0)
  rw [htargetAmbient, hsourceAmbient]
  simp only [sourceIndexTerm]
  have hsourceNeg :
      (∑ i : {i : Fin n // i ∉ state.seenSource},
        if y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
            (segmentCurve state.x state.p (state.slope lam) xR)
        then (-1 : ℝ) else 0) =
      -(∑ i : {i : Fin n // i ∉ state.seenSource},
        if y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
            (segmentCurve state.x state.p (state.slope lam) xR)
        then (1 : ℝ) else 0) := by
    calc
      _ = ∑ i : {i : Fin n // i ∉ state.seenSource},
          -(if y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i
              (segmentCurve state.x state.p (state.slope lam) xR)
            then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hite (P : Prop) [Decidable P] :
            (if P then (-1 : ℝ) else 0) = -(if P then (1 : ℝ) else 0) := by
          by_cases hP : P <;> simp [hP]
        exact hite _
      _ = _ := by
        simp only [Finset.sum_neg_distrib]
  rw [hsourceNeg]
  ring

/-! ## Conditioned one-label moments -/

/-- One unseen coordinate's conditional law in a realized boundary-history section. -/
noncomputable def rightBoundaryHistoryFactorLaw
    (lam xR : ℝ) (state : FeedbackStepState n)
    (label : FeedbackLabel n) : Measure MarkedHeight :=
  (unitSquareUniform : Measure MarkedHeight)[|
    feedbackLabelRemainingSetAt lam state xR label]

/-- Probability that one conditioned unseen coordinate remains beyond `y`. -/
noncomputable def rightBoundaryHistoryFactorProbability
    (lam xR y : ℝ) (state : FeedbackStepState n)
    (label : FeedbackLabel n) : ℝ :=
  (rightBoundaryHistoryFactorLaw lam xR state label).real
    (rightBoundaryFrozenRemainingSet (n := n)
      (segmentCurve state.x state.p (state.slope lam) xR) y label)

/-- The finite-product Bernoulli estimate applied to the exact frozen current in a realized
seen/unseen section. -/
theorem rightBoundaryHistoryCurrent_secondMoment_le
    (lam xR y : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    (hpositive : ∀ label : feedbackUnseenFinset S,
      (unitSquareUniform : Measure MarkedHeight)
        (feedbackLabelRemainingSetAt lam state xR
          (label : FeedbackLabel n)) ≠ 0) :
    ∫ unseen : feedbackUnseenFinset S → MarkedHeight,
        rightBoundaryFrozenCurrent lam xR y
          (revealedSnapshotFromState sample state)
          (finiteSampleSeenUnseenMerge S seen unseen) ^ 2
        ∂(Measure.pi fun label : feedbackUnseenFinset S ↦
          rightBoundaryHistoryFactorLaw lam xR state
            (label : FeedbackLabel n))
      ≤ (∑ label : feedbackUnseenFinset S,
          rightBoundaryHistoryFactorProbability lam xR y state
            (label : FeedbackLabel n)) +
        (∑ label : feedbackUnseenFinset S,
          rightBoundaryLabelSign (label : FeedbackLabel n) *
            rightBoundaryHistoryFactorProbability lam xR y state
              (label : FeedbackLabel n)) ^ 2 := by
  let P : feedbackUnseenFinset S → Measure MarkedHeight := fun label ↦
    rightBoundaryHistoryFactorLaw lam xR state (label : FeedbackLabel n)
  let A : feedbackUnseenFinset S → Set MarkedHeight := fun label ↦
    rightBoundaryFrozenRemainingSet
      (segmentCurve state.x state.p (state.slope lam) xR) y
        (label : FeedbackLabel n)
  let sign : feedbackUnseenFinset S → ℝ := fun label ↦
    rightBoundaryLabelSign (label : FeedbackLabel n)
  let _ : ∀ label : feedbackUnseenFinset S, IsProbabilityMeasure (P label) :=
    fun label ↦ cond_isProbabilityMeasure (hpositive label)
  have hA : ∀ label, MeasurableSet (A label) := by
    intro label
    exact measurableSet_rightBoundaryFrozenRemainingSet _ _ _
  have hsign : ∀ label, sign label = 1 ∨ sign label = -1 := by
    intro label
    cases hlabel : (label : FeedbackLabel n) with
    | inl i => exact Or.inr (by simp [sign, rightBoundaryLabelSign, hlabel])
    | inr j => exact Or.inl (by simp [sign, rightBoundaryLabelSign, hlabel])
  have hmoment := Probability.integral_sq_const_add_signedIndicatorSum_le
    P A hA sign hsign 0
  have hcurrent : ∀ unseen,
      rightBoundaryFrozenCurrent lam xR y
          (revealedSnapshotFromState sample state)
          (finiteSampleSeenUnseenMerge S seen unseen) =
        0 + ∑ label, sign label *
          if unseen label ∈ A label then (1 : ℝ) else 0 := by
    intro unseen
    simpa [P, A, sign] using
      (rightBoundaryFrozenCurrent_merge_eq_signedIndicatorSum
        lam xR y state S hsource htarget sample seen unseen)
  calc
    ∫ unseen : feedbackUnseenFinset S → MarkedHeight,
        rightBoundaryFrozenCurrent lam xR y
          (revealedSnapshotFromState sample state)
          (finiteSampleSeenUnseenMerge S seen unseen) ^ 2 ∂Measure.pi P =
        ∫ unseen,
          (0 + ∑ label, sign label *
            if unseen label ∈ A label then (1 : ℝ) else 0) ^ 2
          ∂Measure.pi P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun unseen ↦ congrArg (fun z : ℝ ↦ z ^ 2)
        (hcurrent unseen)
    _ ≤ (∑ label, (P label).real (A label)) +
        (0 + ∑ label, sign label * (P label).real (A label)) ^ 2 := hmoment
    _ = _ := by simp [P, A, sign, rightBoundaryHistoryFactorProbability]

/-- One source coordinate's conditional remaining probability. -/
noncomputable def rightBoundaryHistorySourceProbability
    (n : ℕ) (lam xR y : ℝ) (state : FeedbackStepState n) : ℝ :=
  ((unitSquareUniform : Measure MarkedHeight)[|
      sourceRawRemainingSetAt n lam state xR]).real
    (sourceRawRemainingSet n
      (segmentCurve state.x state.p (state.slope lam) xR) y)

/-- One target coordinate's conditional remaining probability. -/
noncomputable def rightBoundaryHistoryTargetProbability
    (n : ℕ) (lam xR y : ℝ) (state : FeedbackStepState n) : ℝ :=
  ((unitSquareUniform : Measure MarkedHeight)[|
      targetRawRemainingSetAt n lam state xR]).real
    (targetRawRemainingSet n
      (segmentCurve state.x state.p (state.slope lam) xR) y)

/-- Number of source coordinates not yet revealed by `state`. -/
def rightBoundarySourceUnseenCount (state : FeedbackStepState n) : ℕ :=
  Fintype.card {i : Fin n // i ∉ state.seenSource}

/-- Number of target coordinates not yet revealed by `state`. -/
def rightBoundaryTargetUnseenCount (state : FeedbackStepState n) : ℕ :=
  Fintype.card {j : Fin n // j ∉ state.seenTarget}

/-- The two sums in the Bernoulli second-moment estimate reduce to the two colour counts and
their one-coordinate conditional probabilities. -/
theorem rightBoundaryHistoryFactorProbability_sums
    (lam xR y : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget) :
    (∑ label : feedbackUnseenFinset S,
        rightBoundaryHistoryFactorProbability lam xR y state
          (label : FeedbackLabel n)) =
      (rightBoundarySourceUnseenCount state : ℝ) *
          rightBoundaryHistorySourceProbability n lam xR y state +
        (rightBoundaryTargetUnseenCount state : ℝ) *
          rightBoundaryHistoryTargetProbability n lam xR y state ∧
    (∑ label : feedbackUnseenFinset S,
        rightBoundaryLabelSign (label : FeedbackLabel n) *
          rightBoundaryHistoryFactorProbability lam xR y state
            (label : FeedbackLabel n)) =
      (rightBoundaryTargetUnseenCount state : ℝ) *
          rightBoundaryHistoryTargetProbability n lam xR y state -
        (rightBoundarySourceUnseenCount state : ℝ) *
          rightBoundaryHistorySourceProbability n lam xR y state := by
  classical
  let targetP := rightBoundaryHistoryTargetProbability n lam xR y state
  let sourceP := rightBoundaryHistorySourceProbability n lam xR y state
  have htargetUnsigned :
      (∑ label : {label : feedbackUnseenFinset S //
          ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j},
        rightBoundaryHistoryFactorProbability lam xR y state
          (label : FeedbackLabel n)) =
        (rightBoundaryTargetUnseenCount state : ℝ) * targetP := by
    calc
      _ = ∑ _j : {j : Fin n // j ∉ state.seenTarget}, targetP := by
        apply Fintype.sum_equiv (rightBoundaryTargetUnseenEquiv S state htarget)
        intro label
        let j := rightBoundaryTargetUnseenEquiv S state htarget label
        have hspec : (label : FeedbackLabel n) = Sum.inr (j : Fin n) :=
          Classical.choose_spec label.property
        simp [rightBoundaryHistoryFactorProbability,
          rightBoundaryHistoryFactorLaw, rightBoundaryFrozenRemainingSet,
          feedbackLabelRemainingSetAt, targetP,
          rightBoundaryHistoryTargetProbability, targetRawRemainingSet,
          hspec, mul_comm]
      _ = _ := by simp [rightBoundaryTargetUnseenCount]
  have hsourceUnsigned :
      (∑ label : {label : feedbackUnseenFinset S //
          ¬ ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j},
        rightBoundaryHistoryFactorProbability lam xR y state
          (label : FeedbackLabel n)) =
        (rightBoundarySourceUnseenCount state : ℝ) * sourceP := by
    calc
      _ = ∑ _i : {i : Fin n // i ∉ state.seenSource}, sourceP := by
        apply Fintype.sum_equiv (rightBoundarySourceUnseenEquiv S state hsource)
        intro label
        let i := rightBoundarySourceUnseenEquiv S state hsource label
        have hspec : (label : FeedbackLabel n) = Sum.inl (i : Fin n) :=
          Classical.choose_spec (by
            rcases hlabel : (label : FeedbackLabel n) with k | j
            · exact ⟨k, hlabel⟩
            · exact False.elim (label.property ⟨j, hlabel⟩))
        simp [rightBoundaryHistoryFactorProbability,
          rightBoundaryHistoryFactorLaw, rightBoundaryFrozenRemainingSet,
          feedbackLabelRemainingSetAt, sourceP,
          rightBoundaryHistorySourceProbability, sourceRawRemainingSet,
          hspec, mul_comm]
      _ = _ := by simp [rightBoundarySourceUnseenCount]
  have htargetSigned :
      (∑ label : {label : feedbackUnseenFinset S //
          ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j},
        rightBoundaryLabelSign (label : FeedbackLabel n) *
          rightBoundaryHistoryFactorProbability lam xR y state
            (label : FeedbackLabel n)) =
        (rightBoundaryTargetUnseenCount state : ℝ) * targetP := by
    calc
      _ = ∑ _j : {j : Fin n // j ∉ state.seenTarget}, targetP := by
        apply Fintype.sum_equiv (rightBoundaryTargetUnseenEquiv S state htarget)
        intro label
        let j := rightBoundaryTargetUnseenEquiv S state htarget label
        have hspec : (label : FeedbackLabel n) = Sum.inr (j : Fin n) :=
          Classical.choose_spec label.property
        simp [rightBoundaryHistoryFactorProbability,
          rightBoundaryHistoryFactorLaw, rightBoundaryFrozenRemainingSet,
          feedbackLabelRemainingSetAt, rightBoundaryLabelSign, targetP,
          rightBoundaryHistoryTargetProbability, targetRawRemainingSet,
          hspec, mul_comm]
      _ = _ := by simp [rightBoundaryTargetUnseenCount]
  have hsourceSigned :
      (∑ label : {label : feedbackUnseenFinset S //
          ¬ ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j},
        rightBoundaryLabelSign (label : FeedbackLabel n) *
          rightBoundaryHistoryFactorProbability lam xR y state
            (label : FeedbackLabel n)) =
        -(rightBoundarySourceUnseenCount state : ℝ) * sourceP := by
    calc
      _ = ∑ _i : {i : Fin n // i ∉ state.seenSource}, -sourceP := by
        apply Fintype.sum_equiv (rightBoundarySourceUnseenEquiv S state hsource)
        intro label
        let i := rightBoundarySourceUnseenEquiv S state hsource label
        have hspec : (label : FeedbackLabel n) = Sum.inl (i : Fin n) :=
          Classical.choose_spec (by
            rcases hlabel : (label : FeedbackLabel n) with k | j
            · exact ⟨k, hlabel⟩
            · exact False.elim (label.property ⟨j, hlabel⟩))
        simp [rightBoundaryHistoryFactorProbability,
          rightBoundaryHistoryFactorLaw, rightBoundaryFrozenRemainingSet,
          feedbackLabelRemainingSetAt, rightBoundaryLabelSign, sourceP,
          rightBoundaryHistorySourceProbability, sourceRawRemainingSet,
          hspec, mul_comm]
      _ = _ := by simp [rightBoundarySourceUnseenCount]
  constructor
  · rw [← Fintype.sum_subtype_add_sum_subtype
      (fun label : feedbackUnseenFinset S ↦
        ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j)]
    rw [htargetUnsigned, hsourceUnsigned]
    ring
  · rw [← Fintype.sum_subtype_add_sum_subtype
      (fun label : feedbackUnseenFinset S ↦
        ∃ j : Fin n, (label : FeedbackLabel n) = Sum.inr j)]
    rw [htargetSigned, hsourceSigned]
    ring

/-- Pointwise second-moment estimate from the right-boundary component bounds and the
deterministic difference between the two one-colour conditional areas. -/
theorem rightBoundaryHistoryCurrent_secondMoment_le_components
    (lam xR y B c C L D : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    (hpositive : ∀ label : feedbackUnseenFinset S,
      (unitSquareUniform : Measure MarkedHeight)
        (feedbackLabelRemainingSetAt lam state xR
          (label : FeedbackLabel n)) ≠ 0)
    (hB : 1 ≤ B) (_hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hsourceBounds : (rightBoundarySourceUnseenCount state : ℝ) ∈ Icc (c * B) (C * B))
    (htargetBounds : (rightBoundaryTargetUnseenCount state : ℝ) ∈ Icc (c * B) (C * B))
    (hgap : |(rightBoundaryTargetUnseenCount state : ℝ) -
        (rightBoundarySourceUnseenCount state : ℝ)| ≤ L)
    (hq : |segmentCurve state.x state.p (state.slope lam) xR| ≤ L * Real.sqrt B)
    (hdifference :
      |rightBoundaryHistoryTargetProbability n lam xR y state -
          rightBoundaryHistorySourceProbability n lam xR y state| ≤
        D * |segmentCurve state.x state.p (state.slope lam) xR| / B) :
    ∫ unseen : feedbackUnseenFinset S → MarkedHeight,
        rightBoundaryFrozenCurrent lam xR y
          (revealedSnapshotFromState sample state)
          (finiteSampleSeenUnseenMerge S seen unseen) ^ 2
        ∂(Measure.pi fun label : feedbackUnseenFinset S ↦
          rightBoundaryHistoryFactorLaw lam xR state
            (label : FeedbackLabel n))
      ≤ (2 * C + (L * (1 + C * D)) ^ 2) * B := by
  let ms : ℝ := rightBoundarySourceUnseenCount state
  let mt : ℝ := rightBoundaryTargetUnseenCount state
  let ps : ℝ := rightBoundaryHistorySourceProbability n lam xR y state
  let pt : ℝ := rightBoundaryHistoryTargetProbability n lam xR y state
  let q : ℝ := segmentCurve state.x state.p (state.slope lam) xR
  have hps0 : 0 ≤ ps := measureReal_nonneg
  have hpt0 : 0 ≤ pt := measureReal_nonneg
  have hps1 : ps ≤ 1 := by
    exact MeasureTheory.measureReal_le_one
  have hpt1 : pt ≤ 1 := by
    exact MeasureTheory.measureReal_le_one
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hsqrt0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hsqrtSq : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0.le
  have hsqrt1 : 1 ≤ Real.sqrt B := by nlinarith
  have hsum := rightBoundaryHistoryFactorProbability_sums
    lam xR y state S hsource htarget
  have hmoment := rightBoundaryHistoryCurrent_secondMoment_le
    lam xR y state S hsource htarget sample seen hpositive
  have hms0 : 0 ≤ ms := by positivity
  have hmt0 : 0 ≤ mt := by positivity
  have hmsUpper : ms ≤ C * B := hsourceBounds.2
  have hmtUpper : mt ≤ C * B := htargetBounds.2
  have hsumBound : ms * ps + mt * pt ≤ 2 * C * B := by
    have hs : ms * ps ≤ C * B := by
      calc
        ms * ps ≤ ms * 1 := mul_le_mul_of_nonneg_left hps1 hms0
        _ ≤ C * B := by simpa using hmsUpper
    have ht : mt * pt ≤ C * B := by
      calc
        mt * pt ≤ mt * 1 := mul_le_mul_of_nonneg_left hpt1 hmt0
        _ ≤ C * B := by simpa using hmtUpper
    linarith
  have hptAbs : |pt| ≤ 1 := by simpa [abs_of_nonneg hpt0] using hpt1
  have hdiffNonneg : 0 ≤ D * |q| / B := by positivity
  have hmsDiff : ms * |pt - ps| ≤ C * D * |q| := by
    calc
      ms * |pt - ps| ≤ ms * (D * |q| / B) :=
        mul_le_mul_of_nonneg_left hdifference hms0
      _ ≤ (C * B) * (D * |q| / B) :=
        mul_le_mul_of_nonneg_right hmsUpper hdiffNonneg
      _ = C * D * |q| := by field_simp
  have hgapTerm : |mt - ms| * |pt| ≤ L := by
    calc
      |mt - ms| * |pt| ≤ L * 1 :=
        mul_le_mul hgap hptAbs (abs_nonneg _) hL
      _ = L := mul_one L
  have hmeanAbs : |mt * pt - ms * ps| ≤
      L * (1 + C * D) * Real.sqrt B := by
    calc
      |mt * pt - ms * ps| = |(mt - ms) * pt + ms * (pt - ps)| := by
        congr 1
        ring
      _ ≤ |mt - ms| * |pt| + ms * |pt - ps| := by
        calc
          _ ≤ |(mt - ms) * pt| + |ms * (pt - ps)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hms0]
      _ ≤ L + C * D * |q| := add_le_add hgapTerm hmsDiff
      _ ≤ L + C * D * (L * Real.sqrt B) := by
        change |q| ≤ L * Real.sqrt B at hq
        simpa [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_left hq (mul_nonneg hC hD)) L
      _ ≤ L * (1 + C * D) * Real.sqrt B := by
        nlinarith [mul_nonneg hL (sub_nonneg.mpr hsqrt1),
          mul_nonneg (mul_nonneg hC hD) (mul_nonneg hL hsqrt0)]
  have hmeanUpper0 : 0 ≤ L * (1 + C * D) * Real.sqrt B := by positivity
  have hmeanSq : (mt * pt - ms * ps) ^ 2 ≤
      (L * (1 + C * D)) ^ 2 * B := by
    have hsquare : (mt * pt - ms * ps) ^ 2 ≤
        (L * (1 + C * D) * Real.sqrt B) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hmeanUpper0] using hmeanAbs
    calc
      _ ≤ (L * (1 + C * D) * Real.sqrt B) ^ 2 := hsquare
      _ = (L * (1 + C * D)) ^ 2 * B := by rw [mul_pow, hsqrtSq]
  rw [hsum.1, hsum.2] at hmoment
  dsimp only [ms, mt, ps, pt, q] at hsumBound hmeanSq ⊢
  calc
    _ ≤ (rightBoundarySourceUnseenCount state : ℝ) *
          rightBoundaryHistorySourceProbability n lam xR y state +
        (rightBoundaryTargetUnseenCount state : ℝ) *
          rightBoundaryHistoryTargetProbability n lam xR y state +
        ((rightBoundaryTargetUnseenCount state : ℝ) *
            rightBoundaryHistoryTargetProbability n lam xR y state -
          (rightBoundarySourceUnseenCount state : ℝ) *
            rightBoundaryHistorySourceProbability n lam xR y state) ^ 2 := hmoment
    _ ≤ 2 * C * B + (L * (1 + C * D)) ^ 2 * B :=
      add_le_add hsumBound hmeanSq
    _ = (2 * C + (L * (1 + C * D)) ^ 2) * B := by ring

/-- Complete the masked arrays of `snapshot` with the coordinates of `auxiliary`.  Coordinates
marked as seen are read from the snapshot; all other coordinates are read from `auxiliary`. -/
noncomputable def completeRevealedSnapshot
    (snapshot : RevealedSnapshot n) (auxiliary : FiniteSample n) : FiniteSample n :=
  feedbackPointArrayToSample fun label ↦
    match label with
    | Sum.inl i =>
        if i ∈ (revealedSnapshotState snapshot).seenSource then
          (snapshot.2.1 i).2
        else auxiliary.sourcePoint i
    | Sum.inr j =>
        if j ∈ (revealedSnapshotState snapshot).seenTarget then
          (snapshot.2.2 j).2
        else auxiliary.targetPoint j

@[fun_prop]
theorem measurable_completeRevealedSnapshot :
    Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
      completeRevealedSnapshot p.1 p.2 := by
  apply measurable_feedbackPointArrayToSample.comp
  refine measurable_pi_lambda _ fun label ↦ ?_
  cases label with
  | inl i =>
      have hstate : Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
          revealedSnapshotState p.1 :=
        measurable_revealedSnapshotState.comp measurable_fst
      have hseen : MeasurableSet {p : RevealedSnapshot n × FiniteSample n |
          i ∈ (revealedSnapshotState p.1).seenSource} := by
        have hset : MeasurableSet {S : Finset (Fin n) | i ∈ S} :=
          measurableSet_mem_finset i
        exact (FeedbackStepState.measurable_seenSource.comp hstate) hset
      have hstored : Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
          (p.1.2.1 i).2 := by fun_prop
      have haux : Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
          p.2.sourcePoint i :=
        (FiniteSample.measurable_sourcePoint i).comp measurable_snd
      exact Measurable.ite hseen hstored haux
  | inr j =>
      have hstate : Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
          revealedSnapshotState p.1 :=
        measurable_revealedSnapshotState.comp measurable_fst
      have hseen : MeasurableSet {p : RevealedSnapshot n × FiniteSample n |
          j ∈ (revealedSnapshotState p.1).seenTarget} := by
        have hset : MeasurableSet {S : Finset (Fin n) | j ∈ S} :=
          measurableSet_mem_finset j
        exact (FeedbackStepState.measurable_seenTarget.comp hstate) hset
      have hstored : Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
          (p.1.2.2 j).2 := by fun_prop
      have haux : Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
          p.2.targetPoint j :=
        (FiniteSample.measurable_targetPoint j).comp measurable_snd
      exact Measurable.ite hseen hstored haux

/-- Completing a genuine snapshot keeps exactly the coordinates marked seen by its state and
takes every other coordinate from the auxiliary sample. -/
theorem completeRevealedSnapshot_revealedSnapshotFromState_eq_merge
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample auxiliary : FiniteSample n) :
    completeRevealedSnapshot (revealedSnapshotFromState sample state) auxiliary =
      finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample)
        (feedbackUnseenTuple S auxiliary) := by
  apply (finiteSampleSeenUnseenMeasurableEquiv S).injective
  rw [finiteSampleSeenUnseenMeasurableEquiv_apply,
    show finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample)
        (feedbackUnseenTuple S auxiliary) =
      (finiteSampleSeenUnseenMeasurableEquiv S).symm
        (feedbackSeenTuple S sample, feedbackUnseenTuple S auxiliary) from rfl,
    (finiteSampleSeenUnseenMeasurableEquiv S).apply_symm_apply]
  apply Prod.ext
  · funext label
    rcases label with ⟨label, hlabel⟩
    cases label with
    | inl i =>
        have hi : i ∈ state.seenSource := (hsource i).1 hlabel
        simp [feedbackSeenTuple, feedbackLabelTuple, feedbackLabelPoint,
          completeRevealedSnapshot, revealedSnapshotState, revealedSnapshotFromState,
          maskedSourceArray, maskedSourcePoint, hi]
    | inr j =>
        have hj : j ∈ state.seenTarget := (htarget j).1 hlabel
        simp [feedbackSeenTuple, feedbackLabelTuple, feedbackLabelPoint,
          completeRevealedSnapshot, revealedSnapshotState, revealedSnapshotFromState,
          maskedTargetArray, maskedTargetPoint, hj]
  · funext label
    rcases label with ⟨label, hlabel⟩
    have hnot : label ∉ S := by simpa [feedbackUnseenFinset] using hlabel
    cases label with
    | inl i =>
        have hi : i ∉ state.seenSource := fun hi ↦ hnot ((hsource i).2 hi)
        simp [feedbackUnseenTuple, feedbackLabelTuple, feedbackLabelPoint,
          completeRevealedSnapshot, revealedSnapshotState, revealedSnapshotFromState,
          maskedSourceArray, maskedSourcePoint, hi]
    | inr j =>
        have hj : j ∉ state.seenTarget := fun hj ↦ hnot ((htarget j).2 hj)
        simp [feedbackUnseenTuple, feedbackLabelTuple, feedbackLabelPoint,
          completeRevealedSnapshot, revealedSnapshotState, revealedSnapshotFromState,
          maskedTargetArray, maskedTargetPoint, hj]
/-! ## The auxiliary remaining rectangle -/

/-- Auxiliary samples whose coordinates not marked seen by `snapshot` lie in the strict remaining
regions at coordinate `x`.  Auxiliary coordinates corresponding to seen labels are unrestricted.
-/
def snapshotRemainingAuxSetAt
    (lam x : ℝ) (snapshot : RevealedSnapshot n) : Set (FiniteSample n) :=
  {auxiliary |
    LiesInStateRemainingAt lam (revealedSnapshotState snapshot) x auxiliary}

theorem measurableSet_snapshotRemainingAuxSetAt_pair (lam x : ℝ) :
    MeasurableSet {p : RevealedSnapshot n × FiniteSample n |
      p.2 ∈ snapshotRemainingAuxSetAt lam x p.1} := by
  have hpair : Measurable fun p : RevealedSnapshot n × FiniteSample n ↦
      (p.2, revealedSnapshotState p.1) :=
    measurable_snd.prodMk (measurable_revealedSnapshotState.comp measurable_fst)
  exact hpair (measurableSet_liesInStateRemainingAt_pair (n := n) lam x)

theorem measurableSet_snapshotRemainingAuxSetAt
    (lam x : ℝ) (snapshot : RevealedSnapshot n) :
    MeasurableSet (snapshotRemainingAuxSetAt lam x snapshot) := by
  exact (measurable_prodMk_left (x := snapshot))
    (measurableSet_snapshotRemainingAuxSetAt_pair (n := n) lam x)

/-- For a genuine snapshot, the auxiliary remaining set is the inverse image of the dependent
unseen rectangle. -/
theorem snapshotRemainingAuxSetAt_revealedSnapshotFromState
    (lam x : ℝ) (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) :
    snapshotRemainingAuxSetAt lam x (revealedSnapshotFromState sample state) =
      feedbackUnseenTuple S ⁻¹' feedbackUnseenRectangularSetAt lam state x S := by
  ext auxiliary
  change LiesInStateRemainingAt lam state x auxiliary ↔
    feedbackUnseenTuple S auxiliary ∈ feedbackUnseenRectangularSetAt lam state x S
  rw [← finiteSampleSeenUnseenMerge_split S auxiliary,
    liesInStateRemainingAt_finiteSampleSeenUnseenMerge_iff
      lam state x S hsource htarget,
    mem_feedbackUnseenRectangularSetAt_iff]
  simp

/-! ## Two-snapshot normalized scalar evaluator -/

/-- Normalized remaining-rectangle average of a scalar `F`.  The first snapshot is available to
`F` and is intended to freeze the deterministic right-boundary height/state.  The second snapshot
determines which labels have since been revealed and the rectangle on which the remaining labels
are averaged. -/
noncomputable def twoSnapshotNormalizedScalar
    (lam x : ℝ) (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (boundary current : RevealedSnapshot n) : ℝ :=
  normalizedRestrictionIntegral (finiteSampleLaw n : Measure (FiniteSample n))
    (snapshotRemainingAuxSetAt lam x current)
    (fun auxiliary ↦ F boundary (completeRevealedSnapshot current auxiliary))

theorem stronglyMeasurable_twoSnapshotNormalizedScalar
    (lam x : ℝ) (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2) :
    StronglyMeasurable fun p : RevealedSnapshot n × RevealedSnapshot n ↦
      twoSnapshotNormalizedScalar lam x F p.1 p.2 := by
  let C : Set (((RevealedSnapshot n) × RevealedSnapshot n) × FiniteSample n) :=
    {p | p.2 ∈ snapshotRemainingAuxSetAt lam x p.1.2}
  have hC : MeasurableSet C := by
    have hmap : Measurable fun p :
        ((RevealedSnapshot n) × RevealedSnapshot n) × FiniteSample n ↦
        (p.1.2, p.2) := by fun_prop
    exact hmap (measurableSet_snapshotRemainingAuxSetAt_pair (n := n) lam x)
  let G : (RevealedSnapshot n × RevealedSnapshot n) → FiniteSample n → ℝ :=
    fun snapshots auxiliary ↦
      F snapshots.1 (completeRevealedSnapshot snapshots.2 auxiliary)
  have hG : StronglyMeasurable fun p :
      ((RevealedSnapshot n) × RevealedSnapshot n) × FiniteSample n ↦
      G p.1 p.2 := by
    have hmap : Measurable fun p :
        ((RevealedSnapshot n) × RevealedSnapshot n) × FiniteSample n ↦
        (p.1.1, completeRevealedSnapshot p.1.2 p.2) := by
      exact (measurable_fst.comp measurable_fst).prodMk
        (measurable_completeRevealedSnapshot.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact hF.comp_measurable hmap
  have hbase := stronglyMeasurable_normalizedRestrictionIntegral
    (finiteSampleLaw n : Measure (FiniteSample n)) C hC G hG
  simpa [twoSnapshotNormalizedScalar, C, G] using hbase

/-- A uniform bound on the completed scalar passes unchanged through normalization. -/
theorem norm_twoSnapshotNormalizedScalar_le
    (lam x : ℝ) (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (boundary current : RevealedSnapshot n) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ completed, ‖F boundary completed‖ ≤ C) :
    ‖twoSnapshotNormalizedScalar lam x F boundary current‖ ≤ C := by
  unfold twoSnapshotNormalizedScalar
  apply norm_normalizedRestrictionIntegral_le_of_norm_le_const
    (finiteSampleLaw n : Measure (FiniteSample n)) _ _ hC
  intro auxiliary _hauxiliary
  exact hbound (completeRevealedSnapshot current auxiliary)

/-- On a genuine current snapshot, the full-sample auxiliary evaluator is exactly the normalized
integral over the dependent unseen product rectangle. -/
theorem twoSnapshotNormalizedScalar_revealedSnapshotFromState_eq
    (lam x : ℝ) (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (boundary : RevealedSnapshot n) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) :
    twoSnapshotNormalizedScalar lam x F boundary
        (revealedSnapshotFromState sample state) =
      normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
        (feedbackUnseenRectangularSetAt lam state x S)
        (fun unseen ↦ F boundary
          (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen)) := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let R := feedbackUnseenRectangularSetAt lam state x S
  let H : (feedbackUnseenFinset S → MarkedHeight) → ℝ := fun unseen ↦
    F boundary (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen)
  have hR : MeasurableSet R :=
    measurableSet_feedbackUnseenRectangularSetAt lam state x S
  have hH : StronglyMeasurable H := by
    have hFb : StronglyMeasurable fun completed : FiniteSample n ↦ F boundary completed :=
      hF.comp_measurable (measurable_const.prodMk measurable_id)
    have hmerge : Measurable fun unseen : feedbackUnseenFinset S → MarkedHeight ↦
        finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen :=
      (measurable_finiteSampleSeenUnseenMerge S).comp
        (measurable_const.prodMk measurable_id)
    exact hFb.comp_measurable hmerge
  have hmap : Measure.map (feedbackUnseenTuple S) μ = feedbackUnseenTupleLaw S := by
    simpa [μ, feedbackUnseenTupleLaw] using
      (finiteSampleLaw_map_feedbackUnseenTuple (n := n) S)
  have hmass : μ.real ((feedbackUnseenTuple S) ⁻¹' R) =
      (feedbackUnseenTupleLaw S).real R := by
    rw [Measure.real, Measure.real, ← hmap,
      Measure.map_apply (measurable_feedbackUnseenTuple S) hR]
  have htransport :
      (∫ auxiliary in (feedbackUnseenTuple S) ⁻¹' R,
          H (feedbackUnseenTuple S auxiliary) ∂μ) =
        ∫ unseen in R, H unseen ∂(feedbackUnseenTupleLaw S) := by
    have h := setIntegral_map (μ := μ) hR hH.aestronglyMeasurable
      (measurable_feedbackUnseenTuple S).aemeasurable
    rw [hmap] at h
    exact h.symm
  rw [twoSnapshotNormalizedScalar,
    snapshotRemainingAuxSetAt_revealedSnapshotFromState
      lam x state S hsource htarget sample,
    normalizedRestrictionIntegral, normalizedRestrictionIntegral, hmass]
  congr 1
  rw [← htransport]
  apply setIntegral_congr_fun (measurableSet_preimage
    (measurable_feedbackUnseenTuple S) hR)
  intro auxiliary _haux
  change F boundary
      (completeRevealedSnapshot (revealedSnapshotFromState sample state) auxiliary) =
    F boundary
      (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample)
        (feedbackUnseenTuple S auxiliary))
  rw [completeRevealedSnapshot_revealedSnapshotFromState_eq_merge
    state S hsource htarget sample auxiliary]

/-- With the revealed state fixed, moving the strict remaining boundary continuously changes the
normalized scalar average.  The only excluded auxiliary configurations are the finitely many
fixed-state crossings exactly at the limiting boundary, which have product measure zero. -/
theorem tendsto_twoSnapshotNormalizedScalar_revealedSnapshotFromState
    (hn : 0 < n) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) (boundary : RevealedSnapshot n)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (C : ℝ)
    (hbound : ∀ completed : FiniteSample n, ‖F boundary completed‖ ≤ C)
    {xk : ℕ → ℝ} {x : ℝ} (hxk : Tendsto xk atTop (𝓝 x))
    (hpos : (feedbackUnseenTupleLaw S).real
      (feedbackUnseenRectangularSetAt lam state x S) ≠ 0) :
    Tendsto (fun k ↦ twoSnapshotNormalizedScalar lam (xk k) F boundary
      (revealedSnapshotFromState sample state)) atTop
      (𝓝 (twoSnapshotNormalizedScalar lam x F boundary
        (revealedSnapshotFromState sample state))) := by
  let ν := feedbackUnseenTupleLaw S
  let _ : IsProbabilityMeasure ν := by
    dsimp [ν, feedbackUnseenTupleLaw]
    infer_instance
  let R : ℕ → Set (feedbackUnseenFinset S → MarkedHeight) := fun k ↦
    feedbackUnseenRectangularSetAt lam state (xk k) S
  let R0 := feedbackUnseenRectangularSetAt lam state x S
  let H : (feedbackUnseenFinset S → MarkedHeight) → ℝ := fun unseen ↦
    F boundary (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen)
  have hR : ∀ k, MeasurableSet (R k) := fun k ↦
    measurableSet_feedbackUnseenRectangularSetAt lam state (xk k) S
  have hR0 : MeasurableSet R0 :=
    measurableSet_feedbackUnseenRectangularSetAt lam state x S
  have hH : StronglyMeasurable H := by
    have hFb : StronglyMeasurable fun completed : FiniteSample n ↦ F boundary completed :=
      hF.comp_measurable (measurable_const.prodMk measurable_id)
    have hmerge : Measurable fun unseen : feedbackUnseenFinset S → MarkedHeight ↦
        finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen :=
      (measurable_finiteSampleSeenUnseenMerge S).comp
        (measurable_const.prodMk measurable_id)
    exact hFb.comp_measurable hmerge
  have hnoCrossing : ∀ᵐ unseen ∂ν, ∀ label : feedbackUnseenFinset S,
      feedbackLabelFixedStateCrossing n lam state (label : FeedbackLabel n)
        (unseen label) ≠ x := by
    apply ae_all_iff.2
    intro label
    have hzero := feedbackUnseenTupleLaw_fixedStateCrossing_singleton_eq_zero
      state lam S label x hn hlam0 hlamHalf
    have hae := measure_eq_zero_iff_ae_notMem.mp hzero
    exact hae.mono fun unseen hunseen heq ↦ hunseen heq
  have hmem : ∀ᵐ unseen ∂ν, ∀ᶠ k in atTop,
      (unseen ∈ R k ↔ unseen ∈ R0) := by
    filter_upwards [hnoCrossing] with unseen hno
    have hlabel : ∀ label : feedbackUnseenFinset S, ∀ᶠ k in atTop,
        (xk k < feedbackLabelFixedStateCrossing n lam state
            (label : FeedbackLabel n) (unseen label) ↔
          x < feedbackLabelFixedStateCrossing n lam state
            (label : FeedbackLabel n) (unseen label)) := by
      intro label
      let crossing := feedbackLabelFixedStateCrossing n lam state
        (label : FeedbackLabel n) (unseen label)
      rcases lt_or_gt_of_ne (hno label) with hcrossx | hxcross
      · have hevent : ∀ᶠ k in atTop, crossing < xk k :=
          hxk.eventually (Ioi_mem_nhds hcrossx)
        exact hevent.mono fun k hk ↦ iff_of_false (not_lt_of_ge hk.le)
          (not_lt_of_ge hcrossx.le)
      · have hevent : ∀ᶠ k in atTop, xk k < crossing :=
          hxk.eventually (Iio_mem_nhds hxcross)
        exact hevent.mono fun k hk ↦ iff_of_true hk hxcross
    filter_upwards [Filter.eventually_all.mpr hlabel] with k hk
    rw [show unseen ∈ R k ↔ ∀ label : feedbackUnseenFinset S,
        xk k < feedbackLabelFixedStateCrossing n lam state
          (label : FeedbackLabel n) (unseen label) by
      rw [mem_feedbackUnseenRectangularSetAt_iff]
      exact forall_congr' fun label ↦
        mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
          state lam (label : FeedbackLabel n) (unseen label) (xk k) hlam0 hlamHalf,
      show unseen ∈ R0 ↔ ∀ label : feedbackUnseenFinset S,
        x < feedbackLabelFixedStateCrossing n lam state
          (label : FeedbackLabel n) (unseen label) by
      rw [mem_feedbackUnseenRectangularSetAt_iff]
      exact forall_congr' fun label ↦
        mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
          state lam (label : FeedbackLabel n) (unseen label) x hlam0 hlamHalf]
    exact forall_congr' hk
  have hnorm : Tendsto
      (fun k ↦ normalizedRestrictionIntegral ν (R k) H) atTop
      (𝓝 (normalizedRestrictionIntegral ν R0 H)) := by
    apply tendsto_normalizedRestrictionIntegral_of_ae ν R R0 hR hR0
      (fun _ ↦ H) H (fun _ ↦ hH.aestronglyMeasurable) hH.aestronglyMeasurable
      (fun _ ↦ C)
    · intro k
      exact Filter.Eventually.of_forall fun unseen ↦ by
        simpa [H] using hbound
          (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S sample) unseen)
    · exact integrable_const C
    · exact hmem
    · exact Filter.Eventually.of_forall fun unseen ↦ tendsto_const_nhds
    · exact hpos
  have heq : (fun k ↦ twoSnapshotNormalizedScalar lam (xk k) F boundary
      (revealedSnapshotFromState sample state)) =
      fun k ↦ normalizedRestrictionIntegral ν (R k) H := by
    funext k
    simpa [ν, R, H] using
      (twoSnapshotNormalizedScalar_revealedSnapshotFromState_eq
        (n := n) lam (xk k) F hF boundary state S hsource htarget sample)
  have heq0 : twoSnapshotNormalizedScalar lam x F boundary
      (revealedSnapshotFromState sample state) =
      normalizedRestrictionIntegral ν R0 H := by
    simpa [ν, R0, H] using
      (twoSnapshotNormalizedScalar_revealedSnapshotFromState_eq
        (n := n) lam x F hF boundary state S hsource htarget sample)
  rw [heq, heq0]
  exact hnorm

/-- A strict finite-history cell is open in its deterministic coordinate argument. -/
theorem historyBeforeCoordinate_eventually_of_tendsto
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) {x : ℝ}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history x)
    {xk : ℕ → ℝ} (hxk : Tendsto xk atTop (𝓝 x)) :
    ∀ᶠ k in atTop, HistoryBeforeCoordinate sample lam x0 p0
      sourcePattern targetPattern history (xk k) := by
  let terminal := sample.scheduledState lam x0 p0
    sourcePattern targetPattern history
  have hbase : HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      terminal.x < x ∧
      (∀ i, i ∉ terminal.seenSource →
        x < terminal.sourceCoordinate sample lam i) ∧
      (∀ j, j ∉ terminal.seenTarget →
        x < terminal.targetCoordinate sample lam j) := hbefore.1
  have hterminal : ∀ᶠ k in atTop, terminal.x < xk k :=
    hxk.eventually (Ioi_mem_nhds hbase.2.1)
  have hsource : ∀ᶠ k in atTop, ∀ i, i ∉ terminal.seenSource →
      xk k < terminal.sourceCoordinate sample lam i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ terminal.seenSource
    · exact Filter.Eventually.of_forall fun _k hnot ↦ False.elim (hnot hi)
    · have hevent := hxk.eventually (Iio_mem_nhds (hbase.2.2.1 i hi))
      exact hevent.mono fun _k hk _hnot ↦ hk
  have htarget : ∀ᶠ k in atTop, ∀ j, j ∉ terminal.seenTarget →
      xk k < terminal.targetCoordinate sample lam j := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j ∈ terminal.seenTarget
    · exact Filter.Eventually.of_forall fun _k hnot ↦ False.elim (hnot hj)
    · have hevent := hxk.eventually (Iio_mem_nhds (hbase.2.2.2 j hj))
      exact hevent.mono fun _k hk _hnot ↦ hk
  filter_upwards [hterminal, hsource, htarget] with k hk hsk htk
  exact ⟨⟨hbase.1, hk, hsk, htk⟩, hbefore.2⟩

/- On a strict realized history cell, the actual two-snapshot evaluator is right-continuous
along every strictly right-approaching sequence. -/
set_option maxHeartbeats 4000000 in
theorem tendsto_actualTwoSnapshotScalar_of_historyBefore
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T s : ℝ≥0) (hs0 : 0 < s)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (C : ℝ) (hbound : ∀ boundary completed, ‖F boundary completed‖ ≤ C)
    (sample : FiniteSample n) (history : List (FeedbackLabel n))
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0)
      history (x0 + (s : ℝ)))
    {r : ℕ → ℝ≥0} (hr : Tendsto r atTop (𝓝 s))
    (hrRight : ∀ᶠ k in atTop, s < r k) :
    Tendsto (fun k ↦
      twoSnapshotNormalizedScalar lam (x0 + (r k : ℝ)) F
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 (r k)))
      atTop (𝓝 (twoSnapshotNormalizedScalar lam (x0 + (s : ℝ)) F
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 s))) := by
  let sourcePattern := sample.initialSeenSource x0 p0
  let targetPattern := sample.initialSeenTarget x0 p0
  let terminal := sample.scheduledState lam x0 p0
    sourcePattern targetPattern history
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let boundary := sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T
  let xk : ℕ → ℝ := fun k ↦ x0 + (r k : ℝ)
  let x : ℝ := x0 + (s : ℝ)
  have hx0x : x0 < x := by
    dsimp [x]
    exact lt_add_of_pos_right x0 (NNReal.coe_pos.mpr hs0)
  have hxk : Tendsto xk atTop (𝓝 x) := by
    have hcoe : Tendsto (fun k ↦ (r k : ℝ)) atTop (𝓝 (s : ℝ)) :=
      NNReal.tendsto_coe.2 hr
    simpa [xk, x] using tendsto_const_nhds.add hcoe
  have hbeforeEventually : ∀ᶠ k in atTop,
      HistoryBeforeCoordinate sample lam x0 p0 sourcePattern targetPattern history (xk k) := by
    exact historyBeforeCoordinate_eventually_of_tendsto sample lam x0 p0
      sourcePattern targetPattern history hbefore hxk
  have hstate : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 s = terminal := by
    have h := HistoryBeforeCoordinate.feedbackStateAtElapsed_eq_scheduledState
      sample hlam0 hlamHalf hx0x (history := history) hbefore
    have hsEndpoint : (⟨x - x0, sub_nonneg.mpr hx0x.le⟩ : ℝ≥0) = s := by
      apply NNReal.eq
      exact sub_eq_iff_eq_add.mpr (by dsimp [x]; ring)
    rw [hsEndpoint] at h
    simpa [sourcePattern, targetPattern, terminal] using h
  have hsnapshotEventually : ∀ᶠ k in atTop,
      sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 (r k) =
        revealedSnapshotFromState sample terminal := by
    filter_upwards [hrRight, hbeforeEventually] with k hsr hk
    have hx0k : x0 < xk k := by
      dsimp [xk]
      exact lt_add_of_pos_right x0 (NNReal.coe_pos.mpr (hs0.trans hsr))
    have hkState : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 (r k) =
        terminal := by
      have h := HistoryBeforeCoordinate.feedbackStateAtElapsed_eq_scheduledState
        sample hlam0 hlamHalf hx0k (history := history) hk
      have hrEndpoint :
          (⟨xk k - x0, sub_nonneg.mpr hx0k.le⟩ : ℝ≥0) = r k := by
        apply NNReal.eq
        exact sub_eq_iff_eq_add.mpr (by dsimp [xk]; ring)
      rw [hrEndpoint] at h
      simpa [sourcePattern, targetPattern, terminal] using h
    simp [FiniteSample.revealedSnapshotAtElapsed, hkState]
  have hAt : HistoryAtCoordinate sample lam x0 p0
      sourcePattern targetPattern history x := by
    exact historyBeforeCoordinate_imp_historyAtCoordinate
      sample hlam0 hlamHalf hbefore
  have hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ terminal.seenSource := by
    intro i
    exact mem_feedbackTerminalLabelSet_inl_iff_seenSource
      sample lam x0 p0 sourcePattern targetPattern history i
  have htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ terminal.seenTarget := by
    intro j
    exact mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      sample lam x0 p0 sourcePattern targetPattern history j
  let remaining : feedbackUnseenFinset S → Set MarkedHeight := fun label ↦
    feedbackLabelRemainingSetAt lam terminal x (label : FeedbackLabel n)
  have hremaining : ∀ label, MeasurableSet (remaining label) := by
    intro label
    exact measurableSet_feedbackLabelRemainingSetAt lam terminal x
      (label : FeedbackLabel n)
  have hpositive : ∀ label,
      (unitSquareUniform : Measure MarkedHeight) (remaining label) ≠ 0 := by
    intro label
    exact ne_of_gt (unitSquareUniform_feedbackUnseenRectangularSetAt_factor_pos
      sample hlam0 hlamHalf hAt label)
  have hmeasure : (feedbackUnseenTupleLaw S)
      (feedbackUnseenRectangularSetAt lam terminal x S) ≠ 0 := by
    simpa [feedbackUnseenTupleLaw, feedbackUnseenRectangularSetAt, remaining] using
      (Probability.measure_univ_pi_ne_zero
        (unitSquareUniform : Measure MarkedHeight) remaining hremaining hpositive)
  let _ : IsProbabilityMeasure (feedbackUnseenTupleLaw S) := by
    dsimp [feedbackUnseenTupleLaw]
    infer_instance
  have hpos : (feedbackUnseenTupleLaw S).real
      (feedbackUnseenRectangularSetAt lam terminal x S) ≠ 0 :=
    (measureReal_ne_zero_iff).2 hmeasure
  have hfixed := tendsto_twoSnapshotNormalizedScalar_revealedSnapshotFromState
    (n := n) hn lam hlam0 hlamHalf terminal S hsource htarget sample boundary
    F hF C (hbound boundary) hxk hpos
  have heqEventually : ∀ᶠ k in atTop,
      twoSnapshotNormalizedScalar lam (x0 + (r k : ℝ)) F boundary
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 (r k)) =
        twoSnapshotNormalizedScalar lam (xk k) F boundary
          (revealedSnapshotFromState sample terminal) := by
    filter_upwards [hsnapshotEventually] with k hk
    rw [hk]
  have heq0 : twoSnapshotNormalizedScalar lam (x0 + (s : ℝ)) F boundary
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 s) =
      twoSnapshotNormalizedScalar lam x F boundary
        (revealedSnapshotFromState sample terminal) := by
    rw [show x0 + (s : ℝ) = x from rfl]
    rw [FiniteSample.revealedSnapshotAtElapsed, hstate]
  rw [heq0]
  exact Tendsto.congr' (Filter.EventuallyEq.symm heqEventually) hfixed

/-- The concrete candidate at elapsed boundary time `T` and later raw time `u`. -/
noncomputable def rightBoundaryScalarCandidate
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T u : ℝ≥0)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (sample : FiniteSample n) : ℝ :=
  twoSnapshotNormalizedScalar lam (x0 + (u : ℝ)) F
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 u)

/-- The actual right-boundary candidate inherits the completed scalar's uniform bound. -/
theorem norm_rightBoundaryScalarCandidate_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T u : ℝ≥0)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ boundary completed, ‖F boundary completed‖ ≤ C)
    (sample : FiniteSample n) :
    ‖rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F sample‖ ≤ C := by
  exact norm_twoSnapshotNormalizedScalar_le
    lam (x0 + (u : ℝ)) F
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 u)
    hC (hbound _)

/-- On a strict realized history cell, the actual scalar candidate is right-continuous along
every strictly right-approaching sequence. -/
theorem tendsto_rightBoundaryScalarCandidate_of_historyBefore
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T s : ℝ≥0) (hs0 : 0 < s)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (C : ℝ) (hbound : ∀ boundary completed, ‖F boundary completed‖ ≤ C)
    (sample : FiniteSample n) (history : List (FeedbackLabel n))
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0)
      history (x0 + (s : ℝ)))
    {r : ℕ → ℝ≥0} (hr : Tendsto r atTop (𝓝 s))
    (hrRight : ∀ᶠ k in atTop, s < r k) :
    Tendsto (fun k ↦
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T (r k) F sample)
      atTop (𝓝 (rightBoundaryScalarCandidate
        hlam0 hlamHalf x0 p0 T s F sample)) := by
  simpa only [rightBoundaryScalarCandidate] using
    (tendsto_actualTwoSnapshotScalar_of_historyBefore
      (n := n) hn hlam0 hlamHalf x0 p0 T s hs0 F hF C hbound
      sample history hbefore hr hrRight)

set_option maxHeartbeats 4000000 in
theorem measurable_rightBoundaryScalarCandidate_of_snapshots
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T u : ℝ≥0)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    {m : MeasurableSpace (FiniteSample n)}
    (hT : Measurable[m] fun sample : FiniteSample n ↦
      sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
    (hu : Measurable[m] fun sample : FiniteSample n ↦
      sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 u) :
    Measurable[m] (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F) := by
  have hsnapshots : Measurable[m] fun sample : FiniteSample n ↦
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T,
        sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 u) :=
    hT.prodMk hu
  have hscalar : Measurable fun p : RevealedSnapshot n × RevealedSnapshot n ↦
      twoSnapshotNormalizedScalar lam (x0 + (u : ℝ)) F p.1 p.2 :=
    (stronglyMeasurable_twoSnapshotNormalizedScalar
      (n := n) lam (x0 + (u : ℝ)) F hF).measurable
  have hcomp := hscalar.comp hsnapshots
  convert hcomp using 1
  funext sample
  rfl

/- The two-snapshot scalar candidate is measurable in the actual raw revealed filtration at the
later time. -/
theorem rightBoundaryScalarCandidate_measurable_raw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {T u : ℝ≥0} (hTu : T ≤ u)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2) :
    Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 u]
      (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F) := by
  apply measurable_rightBoundaryScalarCandidate_of_snapshots
    (n := n) hlam0 hlamHalf x0 p0 T u F hF
  · exact (stronglyAdapted_rawRevealedSnapshot
    (n := n) hlam0 hlamHalf x0 p0 T).mono
      ((rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).mono hTu) |>.measurable
  · exact (stronglyAdapted_rawRevealedSnapshot
      (n := n) hlam0 hlamHalf x0 p0 u).measurable

/-! ## Identification on a realized finite-history section -/

/-- On a realized history cell, the actual scalar candidate is the normalized dependent-product
section integral.  The boundary snapshot is still taken at the deterministic earlier time `T`.
-/
theorem rightBoundaryScalarCandidate_eq_historySectionNormalized
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 ≤ x) (T : ℝ≥0)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (reference : FiniteSample n)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history x) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T
        ⟨x - x0, sub_nonneg.mpr hx0x⟩ F reference =
      normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
        (feedbackUnseenRectangularSetAt lam terminal x S)
        (fun unseen ↦ F
          (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
          (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)) := by
  let endpoint : ℝ≥0 := ⟨x - x0, sub_nonneg.mpr hx0x⟩
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  have hrefInitial :
      reference.initialFeedbackState x0 p0 =
        FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern :=
    href.1.1
  have hsourcePattern : reference.initialSeenSource x0 p0 = sourcePattern := by
    have h := congrArg FeedbackStepState.seenSource hrefInitial
    simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h
  have htargetPattern : reference.initialSeenTarget x0 p0 = targetPattern := by
    have h := congrArg FeedbackStepState.seenTarget hrefInitial
    simpa [FiniteSample.initialFeedbackState, FiniteSample.forcedInitialState] using h
  have hrefActual : HistoryAtCoordinate reference lam x0 p0
      (reference.initialSeenSource x0 p0) (reference.initialSeenTarget x0 p0) history x := by
    rw [hsourcePattern, htargetPattern]
    exact href
  have hstate : reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 endpoint =
      terminal := by
    simpa [endpoint, terminal, hsourcePattern, htargetPattern] using
      (HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
        reference hlam0 hlamHalf hx0x history hrefActual)
  have hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ terminal.seenSource := by
    intro i
    exact mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 sourcePattern targetPattern history i
  have htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ terminal.seenTarget := by
    intro j
    exact mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 sourcePattern targetPattern history j
  dsimp only
  unfold rightBoundaryScalarCandidate
  have hxeq : x0 + (endpoint : ℝ) = x := by
    change x0 + (x - x0) = x
    ring
  rw [hxeq]
  change twoSnapshotNormalizedScalar lam x F
      (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
      (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 endpoint) = _
  simp only [FiniteSample.revealedSnapshotAtElapsed]
  rw [hstate]
  exact twoSnapshotNormalizedScalar_revealedSnapshotFromState_eq
    lam x F hF
    (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
    terminal S hsource htarget reference

/-- Samples in the same realized history section and with the same terminal seen tuple have the
same actual two-snapshot scalar candidate, provided the frozen time is no later than the section
endpoint. -/
theorem rightBoundaryScalarCandidate_eq_of_historyAtCoordinate
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 ≤ x) (T : ℝ≥0)
    (hT : T ≤ ⟨x - x0, sub_nonneg.mpr hx0x⟩)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (reference sample : FiniteSample n)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history x)
    (hsample : HistoryAtCoordinate sample lam x0 p0
      sourcePattern targetPattern history x)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T
        ⟨x - x0, sub_nonneg.mpr hx0x⟩ F reference =
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T
        ⟨x - x0, sub_nonneg.mpr hx0x⟩ F sample := by
  let endpoint : ℝ≥0 := ⟨x - x0, sub_nonneg.mpr hx0x⟩
  have hboundary := revealedSnapshotAtElapsed_eq_of_historyAtCoordinate_of_le
    reference sample hlam0 hlamHalf hx0x href hsample htuple T hT
  have hcurrent := revealedSnapshotAtElapsed_eq_of_historyAtCoordinate
    reference sample hlam0 hlamHalf hx0x href hsample htuple
  unfold rightBoundaryScalarCandidate
  rw [hboundary, hcurrent]

/-- Integrating the actual candidate over one realized unseen rectangle returns the unnormalized
section integral of `F`.  This is the exact scalar identity consumed by raw-history assembly. -/
theorem rightBoundaryScalarCandidate_historySection_setIntegral_eq
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 ≤ x) (T : ℝ≥0)
    (hT : T ≤ ⟨x - x0, sub_nonneg.mpr hx0x⟩)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (reference : FiniteSample n)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history x) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let terminal := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    (∫ unseen in feedbackUnseenRectangularSetAt lam terminal x S,
        rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T
          ⟨x - x0, sub_nonneg.mpr hx0x⟩ F
          (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
        ∂(feedbackUnseenTupleLaw S)) =
      ∫ unseen in feedbackUnseenRectangularSetAt lam terminal x S,
        F (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
          (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
        ∂(feedbackUnseenTupleLaw S) := by
  let endpoint : ℝ≥0 := ⟨x - x0, sub_nonneg.mpr hx0x⟩
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let terminal := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  let R := feedbackUnseenRectangularSetAt lam terminal x S
  let ν := feedbackUnseenTupleLaw S
  let _ : IsProbabilityMeasure ν := by
    dsimp [ν, feedbackUnseenTupleLaw]
    infer_instance
  let candidate := rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T endpoint F
  let sectionIntegrand : (feedbackUnseenFinset S → MarkedHeight) → ℝ := fun unseen ↦
    F (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
      (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
  have hR : MeasurableSet R :=
    measurableSet_feedbackUnseenRectangularSetAt lam terminal x S
  have hcand : ∀ unseen ∈ R,
      candidate (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen) =
        candidate reference := by
    intro unseen hunseen
    have hsample : HistoryAtCoordinate
        (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
        lam x0 p0 sourcePattern targetPattern history x := by
      exact (historyAtCoordinate_finiteSampleSeenUnseenMerge_iff
        reference hlam0 hlamHalf href (feedbackSeenTuple S reference) unseen rfl).2 hunseen
    have htuple : feedbackSeenTuple S reference =
        feedbackSeenTuple S
          (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen) := by
      simp
    exact (rightBoundaryScalarCandidate_eq_of_historyAtCoordinate
      hlam0 hlamHalf hx0x T hT F reference
      (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
      sourcePattern targetPattern history href hsample htuple).symm
  have hconstant :
      (∫ unseen in R, candidate
          (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen) ∂ν) =
        ∫ _unseen in R, candidate reference ∂ν := by
    apply setIntegral_congr_fun hR
    intro unseen hunseen
    exact hcand unseen hunseen
  have hnormalized : candidate reference =
      normalizedRestrictionIntegral ν R sectionIntegrand := by
    simpa [candidate, endpoint, S, terminal, R, ν, sectionIntegrand] using
      (rightBoundaryScalarCandidate_eq_historySectionNormalized
        hlam0 hlamHalf hx0x T F hF reference sourcePattern targetPattern history href)
  let remaining : feedbackUnseenFinset S → Set MarkedHeight := fun label ↦
    feedbackLabelRemainingSetAt lam terminal x (label : FeedbackLabel n)
  have hremaining : ∀ label, MeasurableSet (remaining label) := by
    intro label
    exact measurableSet_feedbackLabelRemainingSetAt lam terminal x
      (label : FeedbackLabel n)
  have hpositive : ∀ label,
      (unitSquareUniform : Measure MarkedHeight) (remaining label) ≠ 0 := by
    intro label
    exact ne_of_gt (unitSquareUniform_feedbackUnseenRectangularSetAt_factor_pos
      reference hlam0 hlamHalf href label)
  have hmeasure : ν R ≠ 0 := by
    simpa [ν, R, feedbackUnseenTupleLaw, feedbackUnseenRectangularSetAt, remaining] using
      (Probability.measure_univ_pi_ne_zero
        (unitSquareUniform : Measure MarkedHeight) remaining hremaining hpositive)
  have hreal : ν.real R ≠ 0 := (measureReal_ne_zero_iff).2 hmeasure
  dsimp only
  rw [hconstant, setIntegral_const, smul_eq_mul, hnormalized,
    normalizedRestrictionIntegral]
  field_simp
  rfl

/-! ## Raw and usual-filtration scalar endpoints -/

/- A section bound for `F` gives the corresponding raw revealed set-integral bound for the
actual candidate. -/
set_option maxHeartbeats 4000000 in
theorem setIntegral_le_rightBoundaryScalarCandidate_of_historySection
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T u : ℝ≥0) (hT0 : 0 < T) (hTu : T ≤ u)
    (Y : FiniteSample n → ℝ)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (hYIntegrable : Integrable Y (finiteSampleLaw n : Measure (FiniteSample n)))
    (hCandidateIntegrable : Integrable
      (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F)
      (finiteSampleLaw n : Measure (FiniteSample n)))
    (hsection : ∀ (index : HistoryCellIndex n) (reference : FiniteSample n),
      reference ∈ historyCell index lam x0 p0 (x0 + (u : ℝ)) →
        let S := feedbackTerminalLabelSet
          index.sourcePattern index.targetPattern index.history
        let terminal := reference.scheduledState lam x0 p0
          index.sourcePattern index.targetPattern index.history
        (∫ unseen in feedbackUnseenRectangularSetAt lam terminal (x0 + (u : ℝ)) S,
            Y (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S)) ≤
          ∫ unseen in feedbackUnseenRectangularSetAt lam terminal (x0 + (u : ℝ)) S,
            F (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
              (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S))
    (A : Set (FiniteSample n))
    (hA : MeasurableSet[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 u] A) :
    (∫ sample in A, Y sample ∂(finiteSampleLaw n : Measure (FiniteSample n))) ≤
      ∫ sample in A,
        rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
  have hu0 : 0 < u := hT0.trans_le hTu
  have hx0u : x0 < x0 + (u : ℝ) := by
    exact lt_add_of_pos_right x0 (NNReal.coe_pos.mpr hu0)
  have huEndpoint :
      (⟨(x0 + (u : ℝ)) - x0, sub_nonneg.mpr hx0u.le⟩ : ℝ≥0) = u := by
    apply NNReal.eq
    exact sub_eq_iff_eq_add.mpr (by ring)
  have hA' : MeasurableSet[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨(x0 + (u : ℝ)) - x0, sub_nonneg.mpr hx0u.le⟩] A := by
    rw [huEndpoint]
    exact hA
  apply setIntegral_le_of_historySection_le
    (n := n) (lam := lam) (x0 := x0) (p0 := p0) (x := x0 + (u : ℝ))
    hlam0 hlamHalf hx0u A hA' hYIntegrable hCandidateIntegrable
  intro index reference href
  have heq := rightBoundaryScalarCandidate_historySection_setIntegral_eq
    (n := n) hlam0 hlamHalf hx0u.le T
    (show T ≤ (⟨(x0 + (u : ℝ)) - x0, sub_nonneg.mpr hx0u.le⟩ : ℝ≥0) by
      rw [huEndpoint]
      exact hTu) F hF reference
    index.sourcePattern index.targetPattern index.history href
  rw [huEndpoint] at heq
  dsimp only at heq ⊢
  rw [heq]
  simpa only using hsection index reference href

/-- The scalar process used by the usual-augmentation lift.  Before the frozen boundary it is
equal to `Y`; from the boundary onward it is the actual two-snapshot candidate. -/
noncomputable def rightBoundaryScalarProcess
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0)
    (Y : FiniteSample n → ℝ)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (u : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  if T ≤ u then
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F sample
  else Y sample

@[simp]
theorem rightBoundaryScalarProcess_at_boundary
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0)
    (Y : FiniteSample n → ℝ)
    (F : RevealedSnapshot n → FiniteSample n → ℝ) :
    rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F T =
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T F := by
  funext sample
  simp [rightBoundaryScalarProcess]

/- The actual scalar process is right continuous in `L¹`.  Before `T` it is locally constant.
At and after `T`, strict finite-history coverage gives almost-everywhere pointwise convergence,
while the normalized-restriction bound supplies domination. -/
set_option maxHeartbeats 4000000 in
theorem rightBoundaryScalarProcess_rightL1
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T)
    (Y : FiniteSample n → ℝ)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (hYIntegrable : Integrable Y (finiteSampleLaw n : Measure (FiniteSample n)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ boundary completed, ‖F boundary completed‖ ≤ C) :
    ∀ s : ℝ≥0, ∀ {r : ℕ → ℝ≥0},
      Tendsto r atTop (𝓝 s) →
      (∀ᶠ k in atTop, s < r k) →
      Tendsto (fun k ↦ ∫⁻ sample,
        ‖rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F (r k) sample -
          rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F s sample‖ₑ
        ∂(finiteSampleLaw n : Measure (FiniteSample n))) atTop (𝓝 0) := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let g := rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F
  have hCandidateIntegrable : ∀ u : ℝ≥0, Integrable
      (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F) μ := by
    intro u
    have hmeas : Measurable
        (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F) :=
      measurable_rightBoundaryScalarCandidate_of_snapshots
        (n := n) hlam0 hlamHalf x0 p0 T u F hF
        (measurable_revealedSnapshotAtElapsed
          (n := n) hlam0 hlamHalf x0 p0 T)
        (measurable_revealedSnapshotAtElapsed
          (n := n) hlam0 hlamHalf x0 p0 u)
    refine Integrable.of_bound hmeas.aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun sample ↦
      norm_rightBoundaryScalarCandidate_le
        (n := n) hlam0 hlamHalf x0 p0 T u F hC hbound sample
  have hgIntegrable : ∀ u : ℝ≥0, Integrable (g u) μ := by
    intro u
    change Integrable
      (rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F u)
      (finiteSampleLaw n : Measure (FiniteSample n))
    by_cases hTu : T ≤ u
    · rw [show rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F u =
          rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F by
        funext sample
        exact ite_eq_left hTu]
      exact hCandidateIntegrable u
    · rw [show rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F u = Y by
        funext sample
        exact ite_eq_right hTu]
      exact hYIntegrable
  intro s r hr hrRight
  by_cases hTs : T ≤ s
  · have hs0 : 0 < s := lt_of_lt_of_le hT0 hTs
    have hx0s : x0 < x0 + (s : ℝ) :=
      lt_add_of_pos_right x0 (NNReal.coe_pos.mpr hs0)
    have hPointwise : ∀ᵐ sample ∂μ,
        Tendsto (fun k ↦ ‖g (r k) sample - g s sample‖ₑ)
          atTop (𝓝 0) := by
      filter_upwards [FiniteSample.finiteSampleLaw_noFeedbackTies_ae
          (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf,
        FiniteSample.noFeedbackEventAt_ae
          (n := n) (p0 := p0) hlam0 hlamHalf hx0s] with
          sample hNoTie hNoEvent
      obtain ⟨history, hbefore, _hlength⟩ :=
        sample.exists_historyBeforeCoordinate_of_noFeedbackTies_of_noFeedbackEventAt
          hlam0 hlamHalf hx0s hNoTie hNoEvent
      have hCandidate := tendsto_rightBoundaryScalarCandidate_of_historyBefore
        (n := n) hn hlam0 hlamHalf x0 p0 T s hs0 F hF C hbound
        sample history hbefore hr hrRight
      have hEventually : ∀ᶠ k in atTop,
          g (r k) sample =
            rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T (r k) F sample :=
        hrRight.mono fun k hsk ↦ by
          simp [g, rightBoundaryScalarProcess, hTs.trans hsk.le]
      have hAt : g s sample =
          rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T s F sample := by
        simp [g, rightBoundaryScalarProcess, hTs]
      have hProcess : Tendsto (fun k ↦ g (r k) sample) atTop
          (𝓝 (g s sample)) := by
        rw [hAt]
        exact Tendsto.congr' (Filter.EventuallyEq.symm hEventually) hCandidate
      have hzero : Tendsto (fun k ↦ g (r k) sample - g s sample)
          atTop (𝓝 0) := by
        simpa using hProcess.sub_const (g s sample)
      simpa [Function.comp_def] using
        (continuous_enorm.tendsto (0 : ℝ)).comp hzero
    have hMeas : ∀ᶠ k in atTop,
        AEMeasurable (fun sample ↦ ‖g (r k) sample - g s sample‖ₑ) μ :=
      Filter.Eventually.of_forall fun k ↦
        ((hgIntegrable (r k)).sub (hgIntegrable s)).aestronglyMeasurable.enorm
    have hBound : ∀ᶠ k in atTop, ∀ᵐ sample ∂μ,
        ‖g (r k) sample - g s sample‖ₑ ≤ ENNReal.ofReal (2 * C) := by
      filter_upwards [hrRight] with k hsk
      exact Filter.Eventually.of_forall fun sample ↦ by
        have hTk : T ≤ r k := hTs.trans hsk.le
        have hkr := norm_rightBoundaryScalarCandidate_le
          (n := n) hlam0 hlamHalf x0 p0 T (r k) F hC hbound sample
        have hsr := norm_rightBoundaryScalarCandidate_le
          (n := n) hlam0 hlamHalf x0 p0 T s F hC hbound sample
        have hnorm : ‖g (r k) sample - g s sample‖ ≤ 2 * C := by
          rw [show g (r k) sample =
              rightBoundaryScalarCandidate hlam0 hlamHalf
                x0 p0 T (r k) F sample by
            simp [g, rightBoundaryScalarProcess, hTk],
            show g s sample =
              rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T s F sample by
            simp [g, rightBoundaryScalarProcess, hTs]]
          exact (norm_sub_le _ _).trans (by linarith)
        simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm
    have hFinite : (∫⁻ _ : FiniteSample n, ENNReal.ofReal (2 * C) ∂μ) ≠ ⊤ :=
      (lintegral_const_lt_top (μ := μ) ENNReal.ofReal_ne_top).ne
    have hDCT := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := μ) (l := atTop)
      (F := fun k sample ↦ ‖g (r k) sample - g s sample‖ₑ)
      (f := fun _ ↦ (0 : ENNReal))
      (fun _ ↦ ENNReal.ofReal (2 * C)) hMeas hBound hFinite hPointwise
    simpa only [g, μ, lintegral_zero] using hDCT
  · have hsT : s < T := lt_of_not_ge hTs
    have hrBefore : ∀ᶠ k in atTop, r k < T :=
      hr.eventually (Iio_mem_nhds hsT)
    have hzero : ∀ᶠ k in atTop,
        (∫⁻ sample,
          ‖g (r k) sample - g s sample‖ₑ ∂μ) = 0 := by
      filter_upwards [hrBefore] with k hk
      simp [g, μ, rightBoundaryScalarProcess, not_le.mpr hk, hTs]
    have ht := Tendsto.congr' (Filter.EventuallyEq.symm hzero) tendsto_const_nhds
    simpa only [g, μ] using ht

/- The actual usual-filtration conditional-expectation endpoint.  Its hypotheses are ordinary
section inequalities and right `L¹` convergence, not a bundled conditional-law interface. -/
set_option maxHeartbeats 4000000 in
theorem condExp_le_rightBoundaryScalarCandidate_of_historySection_of_rightL1
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T)
    (Y : FiniteSample n → ℝ)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (hYIntegrable : Integrable Y (finiteSampleLaw n : Measure (FiniteSample n)))
    (hCandidateIntegrable : ∀ u : ℝ≥0, T ≤ u → Integrable
      (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F)
      (finiteSampleLaw n : Measure (FiniteSample n)))
    (hsection : ∀ (u : ℝ≥0), T ≤ u →
      ∀ (index : HistoryCellIndex n) (reference : FiniteSample n),
      reference ∈ historyCell index lam x0 p0 (x0 + (u : ℝ)) →
        let S := feedbackTerminalLabelSet
          index.sourcePattern index.targetPattern index.history
        let terminal := reference.scheduledState lam x0 p0
          index.sourcePattern index.targetPattern index.history
        (∫ unseen in feedbackUnseenRectangularSetAt lam terminal (x0 + (u : ℝ)) S,
            Y (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S)) ≤
          ∫ unseen in feedbackUnseenRectangularSetAt lam terminal (x0 + (u : ℝ)) S,
            F (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
              (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S))
    (hRightL1 : ∀ s : ℝ≥0, ∀ {r : ℕ → ℝ≥0},
      Tendsto r atTop (𝓝 s) →
      (∀ᶠ k in atTop, s < r k) →
      Tendsto (fun k ↦ ∫⁻ sample,
        ‖rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F (r k) sample -
          rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F s sample‖ₑ
        ∂(finiteSampleLaw n : Measure (FiniteSample n))) atTop (𝓝 0)) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
        Y | usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n))]
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T F := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  let ℱ := rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
  let g := rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F
  have hgIntegrable : ∀ u : ℝ≥0, Integrable (g u) μ := by
    intro u
    change Integrable
      (rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F u)
      (finiteSampleLaw n : Measure (FiniteSample n))
    by_cases hTu : T ≤ u
    · rw [show rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F u =
          rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F by
        funext sample
        exact ite_eq_left hTu]
      exact hCandidateIntegrable u hTu
    · rw [show rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F u = Y by
        funext sample
        exact ite_eq_right hTu]
      exact hYIntegrable
  have hRaw : ∀ {u : ℝ≥0}, ∀ A : Set (FiniteSample n), MeasurableSet[ℱ u] A →
      (∫ sample in A, Y sample ∂μ) ≤ ∫ sample in A, g u sample ∂μ := by
    intro u A hA
    by_cases hTu : T ≤ u
    · have h := setIntegral_le_rightBoundaryScalarCandidate_of_historySection
        (n := n) hlam0 hlamHalf x0 p0 T u hT0 hTu Y F hF hYIntegrable
        (hCandidateIntegrable u hTu) (hsection u hTu) A hA
      simpa [g, μ, ℱ, rightBoundaryScalarProcess, hTu] using h
    · simp [g, rightBoundaryScalarProcess, hTu]
  have hUsual : ∀ B : Set (FiniteSample n),
      MeasurableSet[usualRevealedFiltration (n := n)
        hlam0 hlamHalf x0 p0 T] B →
      (∫ sample in B, Y sample ∂μ) ≤ ∫ sample in B, g T sample ∂μ := by
    intro B hB
    exact CountingProcess.setIntegral_le_of_usualAugmentation_of_rightL1
      ℱ Y g hgIntegrable hRaw hRightL1 hB
  have hCandidateMeasRaw : Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T F) :=
    rightBoundaryScalarCandidate_measurable_raw
      (n := n) hlam0 hlamHalf x0 p0 le_rfl F hF
  have hCandidateMeasUsual : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T]
      (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T F) :=
    hCandidateMeasRaw.mono
      (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf x0 p0 T) le_rfl
  have hm : usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T ≤
      (inferInstance : MeasurableSpace (FiniteSample n)) :=
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).le T
  apply (condExp_le_iff_forall_setIntegral_le hm hYIntegrable
    (hCandidateIntegrable T le_rfl) hCandidateMeasUsual.stronglyMeasurable).2
  intro B hB
  have h := hUsual B hB
  change (∫ sample in B, Y sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n))) ≤
    ∫ sample in B,
      rightBoundaryScalarProcess hlam0 hlamHalf x0 p0 T Y F T sample
      ∂(finiteSampleLaw n : Measure (FiniteSample n)) at h
  rw [rightBoundaryScalarProcess_at_boundary] at h
  exact h

/- The closed scalar right-boundary endpoint.  Boundedness supplies candidate integrability and
the right-`L¹` hypothesis required by the raw-to-usual bridge. -/
set_option maxHeartbeats 4000000 in
theorem condExp_le_rightBoundaryScalarCandidate_of_historySection
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T)
    (Y : FiniteSample n → ℝ)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    (hYIntegrable : Integrable Y (finiteSampleLaw n : Measure (FiniteSample n)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ boundary completed, ‖F boundary completed‖ ≤ C)
    (hsection : ∀ (u : ℝ≥0), T ≤ u →
      ∀ (index : HistoryCellIndex n) (reference : FiniteSample n),
      reference ∈ historyCell index lam x0 p0 (x0 + (u : ℝ)) →
        let S := feedbackTerminalLabelSet
          index.sourcePattern index.targetPattern index.history
        let terminal := reference.scheduledState lam x0 p0
          index.sourcePattern index.targetPattern index.history
        (∫ unseen in feedbackUnseenRectangularSetAt lam terminal (x0 + (u : ℝ)) S,
            Y (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S)) ≤
          ∫ unseen in feedbackUnseenRectangularSetAt lam terminal (x0 + (u : ℝ)) S,
            F (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
              (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen)
            ∂(feedbackUnseenTupleLaw S)) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
        Y | usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n))]
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T F := by
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  have hCandidateIntegrable : ∀ u : ℝ≥0, T ≤ u → Integrable
      (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F) μ := by
    intro u _hTu
    have hmeas : Measurable
        (rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T u F) :=
      measurable_rightBoundaryScalarCandidate_of_snapshots
        (n := n) hlam0 hlamHalf x0 p0 T u F hF
        (measurable_revealedSnapshotAtElapsed
          (n := n) hlam0 hlamHalf x0 p0 T)
        (measurable_revealedSnapshotAtElapsed
          (n := n) hlam0 hlamHalf x0 p0 u)
    refine Integrable.of_bound hmeas.aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun sample ↦
      norm_rightBoundaryScalarCandidate_le
        (n := n) hlam0 hlamHalf x0 p0 T u F hC hbound sample
  have hRightL1 := rightBoundaryScalarProcess_rightL1
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0 Y F hF hYIntegrable hC hbound
  exact condExp_le_rightBoundaryScalarCandidate_of_historySection_of_rightL1
    (n := n) hlam0 hlamHalf x0 p0 T hT0 Y F hF hYIntegrable
    hCandidateIntegrable hsection hRightL1

/- The integrand obtained by evaluating `F` at the actual boundary snapshot needs no separate
section premise.  On each later history rectangle, that boundary snapshot is fixed by the
revealed history and seen tuple. -/
set_option maxHeartbeats 4000000 in
theorem condExp_actualBoundaryEvaluation_le_candidate
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T)
    (F : RevealedSnapshot n → FiniteSample n → ℝ)
    (hF : StronglyMeasurable fun p : RevealedSnapshot n × FiniteSample n ↦
      F p.1 p.2)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ boundary completed, ‖F boundary completed‖ ≤ C) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
        (fun sample ↦ F
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample) |
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n))]
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T F := by
  let Y : FiniteSample n → ℝ := fun sample ↦
    F (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample
  have hY : StronglyMeasurable Y := by
    exact hF.comp_measurable
      ((measurable_revealedSnapshotAtElapsed
        (n := n) hlam0 hlamHalf x0 p0 T).prodMk measurable_id)
  have hYIntegrable : Integrable Y
      (finiteSampleLaw n : Measure (FiniteSample n)) :=
    Integrable.of_bound hY.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun sample ↦ hbound _ sample)
  apply condExp_le_rightBoundaryScalarCandidate_of_historySection
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0 Y F hF hYIntegrable hC hbound
  intro u hTu index reference href
  let S := feedbackTerminalLabelSet
    index.sourcePattern index.targetPattern index.history
  let terminal := reference.scheduledState lam x0 p0
    index.sourcePattern index.targetPattern index.history
  have hx0u : x0 ≤ x0 + (u : ℝ) := le_add_of_nonneg_right u.coe_nonneg
  have huEndpoint :
      (⟨(x0 + (u : ℝ)) - x0, sub_nonneg.mpr hx0u⟩ : ℝ≥0) = u := by
    apply NNReal.eq
    exact sub_eq_iff_eq_add.mpr (by ring)
  have hTendpoint : T ≤
      (⟨(x0 + (u : ℝ)) - x0, sub_nonneg.mpr hx0u⟩ : ℝ≥0) := by
    rw [huEndpoint]
    exact hTu
  have hR : MeasurableSet
      (feedbackUnseenRectangularSetAt lam terminal (x0 + (u : ℝ)) S) :=
    measurableSet_feedbackUnseenRectangularSetAt
      lam terminal (x0 + (u : ℝ)) S
  dsimp only
  apply le_of_eq
  apply setIntegral_congr_fun hR
  intro unseen hunseen
  let completed := finiteSampleSeenUnseenMerge S
    (feedbackSeenTuple S reference) unseen
  have hcompleted : HistoryAtCoordinate completed lam x0 p0
      index.sourcePattern index.targetPattern index.history (x0 + (u : ℝ)) := by
    exact (historyAtCoordinate_finiteSampleSeenUnseenMerge_iff
      reference hlam0 hlamHalf href (feedbackSeenTuple S reference) unseen rfl).2 hunseen
  have htuple : feedbackSeenTuple S reference = feedbackSeenTuple S completed := by
    simp [completed]
  have hboundary := revealedSnapshotAtElapsed_eq_of_historyAtCoordinate_of_le
    reference completed hlam0 hlamHalf hx0u href hcompleted htuple T
      hTendpoint
  exact congrArg (fun boundary ↦ F boundary completed) hboundary.symm

/-! ## The explicit right-boundary energy estimate -/

set_option maxHeartbeats 10000000 in
/-- On a realized boundary history, the actual scalar candidate is bounded by `B²` from the
paper's component count/height bounds and a deterministic normalized source-target area
difference estimate.  The latter is the only geometric input not proved in this scalar file. -/
theorem rightBoundaryScalarCandidate_frozenEnergy_le_of_history
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (xEnd B c C L D : ℝ)
    (reference : FiniteSample n)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history (x0 + (T : ℝ)))
    (hB : 1 ≤ B) (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hxEnd : x0 + (T : ℝ) ≤ xEnd)
    (hlength : xEnd - (x0 + (T : ℝ)) ≤ 3 * B)
    (hsourceBounds :
      (rightBoundarySourceUnseenCount
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) : ℝ) ∈
          Icc (c * B) (C * B))
    (htargetBounds :
      (rightBoundaryTargetUnseenCount
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) : ℝ) ∈
          Icc (c * B) (C * B))
    (hgap :
      |(rightBoundaryTargetUnseenCount
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) : ℝ) -
        (rightBoundarySourceUnseenCount
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) : ℝ)| ≤ L)
    (hq :
      |segmentCurve
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
          ((reference.scheduledState lam x0 p0 sourcePattern targetPattern history).slope lam)
          (x0 + (T : ℝ))| ≤ L * Real.sqrt B)
    (hdifference : ∀ y ∈ Ioc (x0 + (T : ℝ)) xEnd,
      |rightBoundaryHistoryTargetProbability n lam (x0 + (T : ℝ)) y
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) -
        rightBoundaryHistorySourceProbability n lam (x0 + (T : ℝ)) y
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history)| ≤
        D * |segmentCurve
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).x
          (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).p
          ((reference.scheduledState lam x0 p0 sourcePattern targetPattern history).slope lam)
          (x0 + (T : ℝ))| / B) :
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
        (rightBoundaryFrozenEnergy lam (x0 + (T : ℝ)) xEnd) reference ≤
      3 * (2 * C + (L * (1 + C * D)) ^ 2) * B ^ 2 := by
  let xR : ℝ := x0 + (T : ℝ)
  let delta : ℝ := xEnd - xR
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let state := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  let seen := feedbackSeenTuple S reference
  let boundary := revealedSnapshotFromState reference state
  let P : feedbackUnseenFinset S → Measure MarkedHeight := fun label ↦
    rightBoundaryHistoryFactorLaw lam xR state (label : FeedbackLabel n)
  let K : ℝ → (feedbackUnseenFinset S → MarkedHeight) → ℝ := fun t unseen ↦
    rightBoundaryFrozenCurrent lam xR (xR + t) boundary
      (finiteSampleSeenUnseenMerge S seen unseen)
  let V : ℝ := (2 * C + (L * (1 + C * D)) ^ 2) * B
  have hx0xR : x0 ≤ xR := by dsimp [xR]; exact le_add_of_nonneg_right T.coe_nonneg
  have hdelta0 : 0 ≤ delta := sub_nonneg.mpr hxEnd
  have hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource := by
    intro i
    exact mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 sourcePattern targetPattern history i
  have htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget := by
    intro j
    exact mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 sourcePattern targetPattern history j
  have hpositive : ∀ label : feedbackUnseenFinset S,
      (unitSquareUniform : Measure MarkedHeight)
        (feedbackLabelRemainingSetAt lam state xR
          (label : FeedbackLabel n)) ≠ 0 := by
    intro label
    exact ne_of_gt (unitSquareUniform_feedbackUnseenRectangularSetAt_factor_pos
      reference hlam0 hlamHalf href label)
  let _ : ∀ label : feedbackUnseenFinset S, IsProbabilityMeasure (P label) :=
    fun label ↦ cond_isProbabilityMeasure (hpositive label)
  let productLaw : Measure (feedbackUnseenFinset S → MarkedHeight) := Measure.pi P
  let _ : IsProbabilityMeasure productLaw := by
    dsimp only [productLaw]
    infer_instance
  have hKmeas : Measurable fun pair :
      ℝ × (feedbackUnseenFinset S → MarkedHeight) ↦ K pair.1 pair.2 := by
    exact measurable_rightBoundaryFrozenCurrent_seenUnseenMerge
      (n := n) lam xR xR boundary S seen
  have hKsqInt : ∀ t ∈ Ioc (0 : ℝ) delta,
      Integrable (fun unseen ↦ K t unseen ^ 2) productLaw := by
    intro t _ht
    have hKt : Measurable (K t) := hKmeas.comp (measurable_const.prodMk measurable_id)
    apply Integrable.of_bound (hKt.pow measurable_const).aestronglyMeasurable
      ((3 * (n : ℝ)) ^ 2)
    exact Filter.Eventually.of_forall fun unseen ↦ by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_rightBoundaryFrozenCurrent_le
          (n := n) lam xR (xR + t) boundary
            (finiteSampleSeenUnseenMerge S seen unseen)) 2
  have hpoint : ∀ t ∈ Ioc (0 : ℝ) delta,
      ∫ unseen, K t unseen ^ 2 ∂productLaw ≤ V := by
    intro t ht
    have hy : xR + t ∈ Ioc xR xEnd := by
      rcases ht with ⟨ht0, htEnd⟩
      constructor <;> dsimp [delta] at htEnd ⊢ <;> linarith
    simpa [P, productLaw, K, V, boundary, seen, xR, state, S] using
      (rightBoundaryHistoryCurrent_secondMoment_le_components
        (n := n) lam xR (xR + t) B c C L D state S hsource htarget
        reference seen hpositive hB hc hC hL hD hsourceBounds htargetBounds
        hgap hq (hdifference (xR + t) hy))
  have hV0 : 0 ≤ V := by
    dsimp [V]
    positivity
  have hVmeas : Measurable (fun _t : ℝ ↦ V) := measurable_const
  have hVint : IntegrableOn (fun _t : ℝ ↦ V) (Ioc (0 : ℝ) delta) :=
    integrableOn_const (measure_Ioc_lt_top (μ := (volume : Measure ℝ))).ne
  have hVarea : ∫ _t : ℝ in Ioc 0 delta, V ≤ V * delta := by
    rw [setIntegral_const, smul_eq_mul]
    simp [Measure.real, Real.volume_Ioc, hdelta0, mul_comm]
  have harea := expected_area_le_of_pointwise_bound productLaw K
    (fun _t : ℝ ↦ V) (V * delta) hKmeas hKsqInt hVmeas
    (fun _t _ht ↦ hV0) hpoint hVint hVarea
  have htranslate : ∀ unseen,
      (∫ t : ℝ in Ioc 0 delta, K t unseen ^ 2 ∂volume) =
        rightBoundaryFrozenEnergy lam xR xEnd boundary
          (finiteSampleSeenUnseenMerge S seen unseen) := by
    intro unseen
    change (∫ t : ℝ in Ioc 0 delta,
        rightBoundaryFrozenCurrent lam xR (xR + t) boundary
          (finiteSampleSeenUnseenMerge S seen unseen) ^ 2 ∂volume) =
      ∫ y : ℝ in Ioc xR xEnd,
        rightBoundaryFrozenCurrent lam xR y boundary
          (finiteSampleSeenUnseenMerge S seen unseen) ^ 2 ∂volume
    rw [← intervalIntegral.integral_of_le hdelta0,
      ← intervalIntegral.integral_of_le hxEnd]
    simpa [delta, add_assoc] using
      (intervalIntegral.integral_comp_add_left
        (a := (0 : ℝ)) (b := delta)
        (fun y : ℝ ↦ rightBoundaryFrozenCurrent lam xR y boundary
          (finiteSampleSeenUnseenMerge S seen unseen) ^ 2) xR)
  have hproductEnergy :
      (∫ unseen, rightBoundaryFrozenEnergy lam xR xEnd boundary
          (finiteSampleSeenUnseenMerge S seen unseen) ∂productLaw) ≤
        V * delta := by
    rw [show (fun unseen ↦ rightBoundaryFrozenEnergy lam xR xEnd boundary
        (finiteSampleSeenUnseenMerge S seen unseen)) =
      (fun unseen ↦ ∫ t : ℝ in Ioc 0 delta, K t unseen ^ 2 ∂volume) by
        funext unseen
        exact (htranslate unseen).symm]
    exact harea
  have hcandNormalized :=
    rightBoundaryScalarCandidate_eq_historySectionNormalized
      (n := n) hlam0 hlamHalf hx0xR T
      (rightBoundaryFrozenEnergy lam xR xEnd)
      (stronglyMeasurable_rightBoundaryFrozenEnergy (n := n) lam xR xEnd)
      reference sourcePattern targetPattern history href
  have hlaw := feedbackUnseenTupleLaw_cond_historySection_eq_pi
    reference hlam0 hlamHalf href
  have hsection :
      {unseen | HistoryAtCoordinate
        (finiteSampleSeenUnseenMerge S seen unseen)
        lam x0 p0 sourcePattern targetPattern history xR} =
        feedbackUnseenRectangularSetAt lam state xR S := by
    ext unseen
    exact historyAtCoordinate_finiteSampleSeenUnseenMerge_iff
      reference hlam0 hlamHalf href seen unseen rfl
  dsimp only at hlaw
  rw [hsection] at hlaw
  have hlaw' :
      (feedbackUnseenTupleLaw S)[|
          feedbackUnseenRectangularSetAt lam state xR S] = productLaw := by
    simpa [P, productLaw, rightBoundaryHistoryFactorLaw,
      S, state, xR] using hlaw
  have hcandPi :
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
          (rightBoundaryFrozenEnergy lam xR xEnd) reference =
        ∫ unseen, rightBoundaryFrozenEnergy lam xR xEnd boundary
          (finiteSampleSeenUnseenMerge S seen unseen) ∂productLaw := by
    have hendpoint :
        (⟨xR - x0, sub_nonneg.mpr hx0xR⟩ : ℝ≥0) = T := by
      apply NNReal.eq
      change xR - x0 = (T : ℝ)
      dsimp only [xR]
      ring
    have hrefInitial :
        reference.initialFeedbackState x0 p0 =
          FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern :=
      href.1.1
    have hsourcePattern : reference.initialSeenSource x0 p0 = sourcePattern := by
      have h := congrArg FeedbackStepState.seenSource hrefInitial
      simpa [FiniteSample.initialFeedbackState,
        FiniteSample.forcedInitialState] using h
    have htargetPattern : reference.initialSeenTarget x0 p0 = targetPattern := by
      have h := congrArg FeedbackStepState.seenTarget hrefInitial
      simpa [FiniteSample.initialFeedbackState,
        FiniteSample.forcedInitialState] using h
    have hrefActual : HistoryAtCoordinate reference lam x0 p0
        (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history xR := by
      rw [hsourcePattern, htargetPattern]
      exact href
    have hstateAt : reference.feedbackStateAtElapsed
        hlam0 hlamHalf x0 p0 T = state := by
      have h := HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
        reference hlam0 hlamHalf hx0xR history hrefActual
      rw [hendpoint] at h
      simpa [state, hsourcePattern, htargetPattern] using h
    have hboundaryEq :
        reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T =
          boundary := by
      simp [FiniteSample.revealedSnapshotAtElapsed, boundary, hstateAt]
    have hcandNormalized' :
        rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
            (rightBoundaryFrozenEnergy lam xR xEnd) reference =
          normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
            (feedbackUnseenRectangularSetAt lam state xR S)
            (fun unseen ↦ rightBoundaryFrozenEnergy lam xR xEnd
              (reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)
              (finiteSampleSeenUnseenMerge S seen unseen)) := by
      simpa only [hendpoint] using hcandNormalized
    rw [hcandNormalized']
    rw [← integral_cond_eq_normalizedRestrictionIntegral]
    rw [hlaw']
    simp only [hboundaryEq]
  rw [hcandPi]
  calc
    _ ≤ V * delta := hproductEnergy
    _ ≤ V * (3 * B) := mul_le_mul_of_nonneg_left hlength hV0
    _ = 3 * (2 * C + (L * (1 + C * D)) ^ 2) * B ^ 2 := by
      dsimp [V]
      ring

set_option maxHeartbeats 10000000 in
/-- Actual-sample form of the `B²` candidate estimate.  Finite-history coverage and the exact
snapshot decoding remove every history/section parameter from the public endpoint. -/
theorem rightBoundaryScalarCandidate_frozenEnergy_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (xEnd B c C L D : ℝ)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hB : 1 ≤ B) (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hxEnd : x0 + (T : ℝ) ≤ xEnd)
    (hlength : xEnd - (x0 + (T : ℝ)) ≤ 3 * B)
    (hsourceBounds :
      (rightBoundarySourceUnseenCount
        (revealedSnapshotState
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (c * B) (C * B))
    (htargetBounds :
      (rightBoundaryTargetUnseenCount
        (revealedSnapshotState
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (c * B) (C * B))
    (hgap :
      |(rightBoundaryTargetUnseenCount
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) -
        (rightBoundarySourceUnseenCount
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ)| ≤ L)
    (hq : |rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)| ≤
      L * Real.sqrt B)
    (hdifference : ∀ y ∈ Ioc (x0 + (T : ℝ)) xEnd,
      |rightBoundaryHistoryTargetProbability n lam (x0 + (T : ℝ)) y
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) -
        rightBoundaryHistorySourceProbability n lam (x0 + (T : ℝ)) y
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T))| ≤
        D * |rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)| / B) :
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
        (rightBoundaryFrozenEnergy lam (x0 + (T : ℝ)) xEnd) sample ≤
      3 * (2 * C + (L * (1 + C * D)) ^ 2) * B ^ 2 := by
  let xR : ℝ := x0 + (T : ℝ)
  have hx0xR : x0 ≤ xR := by dsimp [xR]; exact le_add_of_nonneg_right T.coe_nonneg
  obtain ⟨history, href, _hlength⟩ :=
    sample.exists_historyAtCoordinate_of_noFeedbackTies
      hlam0 hlamHalf hx0xR hNoTie
  let sourcePattern := sample.initialSeenSource x0 p0
  let targetPattern := sample.initialSeenTarget x0 p0
  let state := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  let boundary := sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T
  have hendpoint : (⟨xR - x0, sub_nonneg.mpr hx0xR⟩ : ℝ≥0) = T := by
    apply NNReal.eq
    change xR - x0 = (T : ℝ)
    dsimp only [xR]
    ring
  have hfeedbackState : sample.feedbackStateAtElapsed
      hlam0 hlamHalf x0 p0 T = state := by
    have h := HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
      sample hlam0 hlamHalf hx0xR history href
    rwa [hendpoint] at h
  have hboundaryState : revealedSnapshotState boundary = state := by
    simp [boundary, revealedSnapshotState, FiniteSample.revealedSnapshotAtElapsed,
      revealedSnapshotFromState, hfeedbackState]
  have hactualState : revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) = state := by
    simpa [boundary] using hboundaryState
  have hsourceBounds' : (rightBoundarySourceUnseenCount state : ℝ) ∈
      Icc (c * B) (C * B) := by
    rw [← hboundaryState]
    exact hsourceBounds
  have htargetBounds' : (rightBoundaryTargetUnseenCount state : ℝ) ∈
      Icc (c * B) (C * B) := by
    rw [← hboundaryState]
    exact htargetBounds
  have hgap' : |(rightBoundaryTargetUnseenCount state : ℝ) -
      (rightBoundarySourceUnseenCount state : ℝ)| ≤ L := by
    rw [← hboundaryState]
    exact hgap
  have hq' : |segmentCurve state.x state.p (state.slope lam) xR| ≤
      L * Real.sqrt B := by
    simpa [rightBoundaryFrozenHeight, hactualState, xR] using hq
  have hdifference' : ∀ y ∈ Ioc xR xEnd,
      |rightBoundaryHistoryTargetProbability n lam xR y state -
        rightBoundaryHistorySourceProbability n lam xR y state| ≤
        D * |segmentCurve state.x state.p (state.slope lam) xR| / B := by
    intro y hy
    simpa [hactualState, rightBoundaryFrozenHeight, xR] using
      hdifference y hy
  exact rightBoundaryScalarCandidate_frozenEnergy_le_of_history
    (n := n) hlam0 hlamHalf x0 p0 T xEnd B c C L D sample
      sourcePattern targetPattern history href hB hc hC hL hD hxEnd hlength
      hsourceBounds' htargetBounds' hgap' hq' hdifference'

/- Actual conditional frozen-current energy at a deterministic right boundary.  Both the
integrand and the candidate use the boundary snapshot's frozen height. -/
set_option maxHeartbeats 4000000 in
theorem condExp_rightBoundaryFrozenEnergy_le
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T)
    (xEnd : ℝ) (hxEnd : x0 + (T : ℝ) ≤ xEnd) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
        (fun sample ↦ rightBoundaryFrozenEnergy lam (x0 + (T : ℝ)) xEnd
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample) |
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n))]
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
        (rightBoundaryFrozenEnergy lam (x0 + (T : ℝ)) xEnd) := by
  let C : ℝ := (xEnd - (x0 + (T : ℝ))) * (3 * n) ^ 2
  have hC : 0 ≤ C := mul_nonneg (sub_nonneg.mpr hxEnd) (sq_nonneg _)
  exact condExp_actualBoundaryEvaluation_le_candidate
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0
      (rightBoundaryFrozenEnergy lam (x0 + (T : ℝ)) xEnd)
      (stronglyMeasurable_rightBoundaryFrozenEnergy
        (n := n) lam (x0 + (T : ℝ)) xEnd)
      hC (fun boundary completed ↦ by
        simpa [C] using norm_rightBoundaryFrozenEnergy_le
          (n := n) lam hxEnd boundary completed)

set_option maxHeartbeats 10000000 in
/-- Actual equation (1.32) on any measurable right-boundary component satisfying the paper's
count/height bounds and the deterministic normalized area-difference estimate.  The conditional
expectation is for the original finite-sample law; only the comparison is restricted to `G`. -/
theorem condExp_rightBoundaryFrozenEnergy_le_on_component
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T)
    (xEnd B c C L D : ℝ)
    (G : Set (FiniteSample n)) (hG : MeasurableSet G)
    (hB : 1 ≤ B) (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hxEnd : x0 + (T : ℝ) ≤ xEnd)
    (hlength : xEnd - (x0 + (T : ℝ)) ≤ 3 * B)
    (hsourceBounds : ∀ sample ∈ G,
      (rightBoundarySourceUnseenCount
        (revealedSnapshotState
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (c * B) (C * B))
    (htargetBounds : ∀ sample ∈ G,
      (rightBoundaryTargetUnseenCount
        (revealedSnapshotState
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) ∈
        Icc (c * B) (C * B))
    (hgap : ∀ sample ∈ G,
      |(rightBoundaryTargetUnseenCount
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ) -
        (rightBoundarySourceUnseenCount
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) : ℝ)| ≤ L)
    (hq : ∀ sample ∈ G,
      |rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)| ≤
        L * Real.sqrt B)
    (hdifference : ∀ sample ∈ G, ∀ y ∈ Ioc (x0 + (T : ℝ)) xEnd,
      |rightBoundaryHistoryTargetProbability n lam (x0 + (T : ℝ)) y
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) -
        rightBoundaryHistorySourceProbability n lam (x0 + (T : ℝ)) y
          (revealedSnapshotState
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T))| ≤
        D * |rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)| / B) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
        (fun sample ↦ rightBoundaryFrozenEnergy lam (x0 + (T : ℝ)) xEnd
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample) |
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n)).restrict G]
      fun _sample ↦ 3 * (2 * C + (L * (1 + C * D)) ^ 2) * B ^ 2 := by
  have hcond := condExp_rightBoundaryFrozenEnergy_le
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0 xEnd hxEnd
  have hcondG := ae_restrict_of_ae (s := G) hcond
  have hNoTieG := ae_restrict_of_ae (s := G)
    (FiniteSample.finiteSampleLaw_noFeedbackTies_ae
      (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf)
  filter_upwards [hcondG, hNoTieG, ae_restrict_mem hG] with
      sample hconditional hNoTie hsample
  exact hconditional.trans (rightBoundaryScalarCandidate_frozenEnergy_le
    (n := n) hlam0 hlamHalf x0 p0 T xEnd B c C L D sample hNoTie
      hB hc hC hL hD hxEnd hlength
      (hsourceBounds sample hsample) (htargetBounds sample hsample)
      (hgap sample hsample) (hq sample hsample)
      (hdifference sample hsample))

/- A bounded scalar may be used as its own completed-sample integrand.  On every realized
history section the two inner integrals are then definitionally equal, so no local probabilistic
premise remains. -/
set_option maxHeartbeats 4000000 in
theorem condExp_le_normalizedRightBoundaryCandidate
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T)
    (Y : FiniteSample n → ℝ) (hY : StronglyMeasurable Y)
    {C : ℝ} (hC : 0 ≤ C) (hYBound : ∀ sample, ‖Y sample‖ ≤ C) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
        Y | usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n))]
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
        (fun _boundary completed ↦ Y completed) := by
  have hYIntegrable : Integrable Y
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
    exact Integrable.of_bound hY.aestronglyMeasurable C
      (Filter.Eventually.of_forall hYBound)
  have hF : StronglyMeasurable fun
      p : RevealedSnapshot n × FiniteSample n ↦ Y p.2 :=
    hY.comp_measurable measurable_snd
  apply condExp_le_rightBoundaryScalarCandidate_of_historySection
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0 Y
      (fun _boundary completed ↦ Y completed) hF hYIntegrable hC
      (fun _boundary completed ↦ hYBound completed)
  intro u _hTu index reference _href
  rfl

end FiniteSample

end OTSelector
