import OTSelector.Feedback.FeedbackRightBoundaryScalar
import OTSelector.Feedback.FeedbackRegularitySurvival
import OTSelector.Feedback.RegularityTail

/-!
# Relative-VC control at the actual frozen right boundary

The boundary snapshot stores the last revealed feedback state, whose `p` field is the height at
the last revealed knot.  The height frozen for the right continuation is instead obtained by
continuing that state's affine segment to the deterministic boundary coordinate.  All future
evaluators in this file use that decoded height; the completed sample supplies only unseen
source and target points.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## A measurable frozen continuation -/

/-- Number of source labels strictly beyond `x`, with the height decoded once from `boundary`.
The completed sample supplies only the labelled point coordinates. -/
noncomputable def rightTailFrozenSourceCount
    (lam xR x : ℝ) (boundary : RevealedSnapshot n)
    (completed : FiniteSample n) : ℝ :=
  rightBoundaryFrozenSourceCount lam xR x boundary completed

/-- Target analogue of `rightTailFrozenSourceCount`. -/
noncomputable def rightTailFrozenTargetCount
    (lam xR x : ℝ) (boundary : RevealedSnapshot n)
    (completed : FiniteSample n) : ℝ :=
  rightBoundaryFrozenTargetCount lam xR x boundary completed

/-- Source remaining-label density along the continuation with frozen boundary height. -/
noncomputable def rightTailFrozenSourceRate
    (n : ℕ) (lam xR x : ℝ) (boundary : RevealedSnapshot n)
    (completed : FiniteSample n) : ℝ :=
  rightTailFrozenSourceCount lam xR x boundary completed /
    sourceUnclippedRemainingMass n (rightBoundaryFrozenHeight lam xR boundary) x

/-- Target remaining-label density along the continuation with frozen boundary height. -/
noncomputable def rightTailFrozenTargetRate
    (n : ℕ) (lam xR x : ℝ) (boundary : RevealedSnapshot n)
    (completed : FiniteSample n) : ℝ :=
  rightTailFrozenTargetCount lam xR x boundary completed /
    targetUnclippedRemainingMass n (rightBoundaryFrozenHeight lam xR boundary) x

/-- At coordinate `x`, at least one frozen continuation density has left `[c, C]`. -/
def rightTailFrozenRateBadAt
    (n : ℕ) (lam xR c C x : ℝ) (boundary : RevealedSnapshot n)
    (completed : FiniteSample n) : Prop :=
  rightTailFrozenSourceRate n lam xR x boundary completed ∉ Icc c C ∨
    rightTailFrozenTargetRate n lam xR x boundary completed ∉ Icc c C

/-- Rate failure on the complete nested interval.  Interior rational coordinates suffice because
the strict-complement count paths are right-continuous; the possibly isolated right endpoint is
included separately. -/
def rightTailRateFailureSet
    (n : ℕ) (lam xR xStar c C : ℝ) :
    Set (RevealedSnapshot n × FiniteSample n) :=
  {pair | rightTailFrozenRateBadAt n lam xR c C xR pair.1 pair.2} ∪
  {pair | rightTailFrozenRateBadAt n lam xR c C xStar pair.1 pair.2} ∪
  ⋃ r : ℚ, if xR + (Real.toNNReal (r : ℝ) : ℝ) < xStar then
    {pair | rightTailFrozenRateBadAt n lam xR c C
      (xR + (Real.toNNReal (r : ℝ) : ℝ)) pair.1 pair.2}
  else ∅

/-- The actual scalar integrand for a right-tail rate failure. -/
noncomputable def rightTailRateFailureIndicator
    (n : ℕ) (lam xR xStar c C : ℝ)
    (boundary : RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  (rightTailRateFailureSet n lam xR xStar c C).indicator 1 (boundary, completed)

private theorem measurable_rightTailFrozenSourcePhase
    (lam xR : ℝ) (i : Fin n) :
    Measurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      pair.2.sourcePhase i (rightBoundaryFrozenHeight lam xR pair.1) := by
  simp only [FiniteSample.sourcePhase, FiniteSample.sourceSlope]
  fun_prop

private theorem measurable_rightTailFrozenTargetPhase
    (lam xR : ℝ) (j : Fin n) :
    Measurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      pair.2.targetPhase j (rightBoundaryFrozenHeight lam xR pair.1) := by
  simp only [FiniteSample.targetPhase, FiniteSample.targetSlope]
  fun_prop

@[fun_prop]
theorem measurable_rightTailFrozenSourceCount (lam xR x : ℝ) :
    Measurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      rightTailFrozenSourceCount lam xR x pair.1 pair.2 := by
  unfold rightTailFrozenSourceCount rightBoundaryFrozenSourceCount
  apply Finset.measurable_sum
  intro i _hi
  have hstate : Measurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      revealedSnapshotState pair.1 :=
    measurable_revealedSnapshotState.comp measurable_fst
  have hseen : MeasurableSet {pair : RevealedSnapshot n × FiniteSample n |
      i ∈ (revealedSnapshotState pair.1).seenSource} :=
    (FeedbackStepState.measurable_seenSource.comp hstate)
      (measurableSet_mem_finset i)
  exact Measurable.ite
    (hseen.compl.inter (measurableSet_lt measurable_const
      (measurable_rightTailFrozenSourcePhase lam xR i)))
    measurable_const measurable_const

@[fun_prop]
theorem measurable_rightTailFrozenTargetCount (lam xR x : ℝ) :
    Measurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      rightTailFrozenTargetCount lam xR x pair.1 pair.2 := by
  unfold rightTailFrozenTargetCount rightBoundaryFrozenTargetCount
  apply Finset.measurable_sum
  intro j _hj
  have hstate : Measurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      revealedSnapshotState pair.1 :=
    measurable_revealedSnapshotState.comp measurable_fst
  have hseen : MeasurableSet {pair : RevealedSnapshot n × FiniteSample n |
      j ∈ (revealedSnapshotState pair.1).seenTarget} :=
    (FeedbackStepState.measurable_seenTarget.comp hstate)
      (measurableSet_mem_finset j)
  exact Measurable.ite
    (hseen.compl.inter (measurableSet_lt measurable_const
      (measurable_rightTailFrozenTargetPhase lam xR j)))
    measurable_const measurable_const

@[fun_prop]
theorem measurable_rightTailFrozenSourceRate
    (n : ℕ) (lam xR x : ℝ) :
    Measurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      rightTailFrozenSourceRate n lam xR x pair.1 pair.2 := by
  unfold rightTailFrozenSourceRate sourceUnclippedRemainingMass
  fun_prop

@[fun_prop]
theorem measurable_rightTailFrozenTargetRate
    (n : ℕ) (lam xR x : ℝ) :
    Measurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      rightTailFrozenTargetRate n lam xR x pair.1 pair.2 := by
  unfold rightTailFrozenTargetRate targetUnclippedRemainingMass
  fun_prop

theorem measurableSet_rightTailFrozenRateBadAt
    (n : ℕ) (lam xR c C x : ℝ) :
    MeasurableSet {pair : RevealedSnapshot n × FiniteSample n |
      rightTailFrozenRateBadAt n lam xR c C x pair.1 pair.2} := by
  have hsource := measurable_rightTailFrozenSourceRate n lam xR x
  have htarget := measurable_rightTailFrozenTargetRate n lam xR x
  have hsourceGood : MeasurableSet {pair : RevealedSnapshot n × FiniteSample n |
      rightTailFrozenSourceRate n lam xR x pair.1 pair.2 ∈ Icc c C} :=
    (measurableSet_Icc.preimage hsource)
  have htargetGood : MeasurableSet {pair : RevealedSnapshot n × FiniteSample n |
      rightTailFrozenTargetRate n lam xR x pair.1 pair.2 ∈ Icc c C} :=
    (measurableSet_Icc.preimage htarget)
  change MeasurableSet
    ({pair : RevealedSnapshot n × FiniteSample n |
        rightTailFrozenSourceRate n lam xR x pair.1 pair.2 ∈ Icc c C}ᶜ ∪
      {pair : RevealedSnapshot n × FiniteSample n |
        rightTailFrozenTargetRate n lam xR x pair.1 pair.2 ∈ Icc c C}ᶜ)
  exact hsourceGood.compl.union htargetGood.compl

theorem measurableSet_rightTailRateFailureSet
    (n : ℕ) (lam xR xStar c C : ℝ) :
    MeasurableSet (rightTailRateFailureSet n lam xR xStar c C) := by
  have hinterior : MeasurableSet
      (⋃ r : ℚ, if xR + (Real.toNNReal (r : ℝ) : ℝ) < xStar then
        {pair : RevealedSnapshot n × FiniteSample n |
          rightTailFrozenRateBadAt n lam xR c C
            (xR + (Real.toNNReal (r : ℝ) : ℝ)) pair.1 pair.2}
      else ∅) := by
    apply MeasurableSet.iUnion
    intro r
    split_ifs
    · exact measurableSet_rightTailFrozenRateBadAt n lam xR c C
        (xR + (Real.toNNReal (r : ℝ) : ℝ))
    · exact MeasurableSet.empty
  exact ((measurableSet_rightTailFrozenRateBadAt n lam xR c C xR).union
    (measurableSet_rightTailFrozenRateBadAt n lam xR c C xStar)).union hinterior

theorem stronglyMeasurable_rightTailRateFailureIndicator
    (n : ℕ) (lam xR xStar c C : ℝ) :
    StronglyMeasurable fun pair : RevealedSnapshot n × FiniteSample n ↦
      rightTailRateFailureIndicator n lam xR xStar c C pair.1 pair.2 := by
  exact (measurable_const.indicator
    (measurableSet_rightTailRateFailureSet n lam xR xStar c C)).stronglyMeasurable

theorem norm_rightTailRateFailureIndicator_le_one
    (n : ℕ) (lam xR xStar c C : ℝ)
    (boundary : RevealedSnapshot n) (completed : FiniteSample n) :
    ‖rightTailRateFailureIndicator n lam xR xStar c C boundary completed‖ ≤ 1 := by
  by_cases hfailure : (boundary, completed) ∈
      rightTailRateFailureSet n lam xR xStar c C
  · simp [rightTailRateFailureIndicator, hfailure]
  · simp [rightTailRateFailureIndicator, hfailure]

/-! ## Deterministic conversion from relative-VC defects to rates -/

/-- The explicit source count threshold supplied by the finite relative-VC good event. -/
noncomputable def rightTailSourceVCBound
    (P : Measure (ℝ × UnitMark)) (m : ℕ) (q x : ℝ) : ℝ :=
  33280 *
    (Real.sqrt (((m : ℝ) * RelativeVC.balancedMass P
      (RelativeVC.errorSet (RelativeVC.sourceCutEval (q, x))
        RelativeVC.falseCutTarget)) * Real.log m) + Real.log m)

/-- Target analogue of `rightTailSourceVCBound`. -/
noncomputable def rightTailTargetVCBound
    (P : Measure (ℝ × UnitMark)) (m : ℕ) (q x : ℝ) : ℝ :=
  33280 *
    (Real.sqrt (((m : ℝ) * RelativeVC.balancedMass P
      (RelativeVC.errorSet (RelativeVC.targetCutEval (q, x))
        RelativeVC.falseCutTarget)) * Real.log m) + Real.log m)

/-- Purely numerical source margin needed to turn the relative-VC count bound into `[c, C]`
rate control.  It contains population masses and algebraic areas, but no empirical or
probabilistic conclusion. -/
def RightTailSourceNumericCondition
    (P : Measure (ℝ × UnitMark)) (m n : ℕ)
    (q xR xStar c C : ℝ) : Prop :=
  ∀ x ∈ Icc xR xStar,
    let area := sourceUnclippedRemainingMass n q x
    let expected := (m : ℝ) * P.real (RelativeVC.sourceCutComplementSet q x)
    0 < area ∧
      c * area + rightTailSourceVCBound P m q x ≤ expected ∧
      expected + rightTailSourceVCBound P m q x ≤ C * area

/-- Purely numerical target margin corresponding to `RightTailSourceNumericCondition`. -/
def RightTailTargetNumericCondition
    (P : Measure (ℝ × UnitMark)) (m n : ℕ)
    (q xR xStar c C : ℝ) : Prop :=
  ∀ x ∈ Icc xR xStar,
    let area := targetUnclippedRemainingMass n q x
    let expected := (m : ℝ) * P.real (RelativeVC.targetCutComplementSet q x)
    0 < area ∧
      c * area + rightTailTargetVCBound P m q x ≤ expected ∧
      expected + rightTailTargetVCBound P m q x ≤ C * area

private theorem sourceComplementDefect_eq_centeredSetCount
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (xs : Fin m → ℝ × UnitMark) (q x : ℝ) :
    RelativeVC.sourceComplementDefect P xs q x =
      RelativeVC.centeredSetCount P xs
        (RelativeVC.sourceCutComplementSet q x) := by
  rw [RelativeVC.sourceComplementDefect,
    RelativeVC.centeredErrorSum_eq_centeredSetCount,
    ← RelativeVC.sourceCutComplementSet_eq_errorSet]

private theorem targetComplementDefect_eq_centeredSetCount
    (P : Measure (ℝ × UnitMark)) {m : ℕ}
    (xs : Fin m → ℝ × UnitMark) (q x : ℝ) :
    RelativeVC.targetComplementDefect P xs q x =
      RelativeVC.centeredSetCount P xs
        (RelativeVC.targetCutComplementSet q x) := by
  rw [RelativeVC.targetComplementDefect,
    RelativeVC.centeredErrorSum_eq_centeredSetCount,
    ← RelativeVC.targetCutComplementSet_eq_errorSet]

theorem sourceSelectedRate_mem_Icc_of_regularityGood
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m n : ℕ} (hm : 4 ≤ m) {xs : Fin m → ℝ × UnitMark}
    (hgood : xs ∈ RelativeVC.finiteHalfspaceRegularityGoodEvent
      P m m (m + 1) 64)
    {q xR xStar c C x : ℝ}
    (hnumeric : RightTailSourceNumericCondition P m n q xR xStar c C)
    (hx : x ∈ Icc xR xStar) :
    RelativeVC.sampleSetCountReal xs
        (RelativeVC.sourceCutComplementSet q x) /
      sourceUnclippedRemainingMass n q x ∈ Icc c C := by
  have hdefect := RelativeVC.sourceCutDefect_uniform_regularity_on_goodEvent
    P hm hgood q x
  have habs :
      |RelativeVC.centeredSetCount P xs
        (RelativeVC.sourceCutComplementSet q x)| ≤
        rightTailSourceVCBound P m q x := by
    rw [← sourceComplementDefect_eq_centeredSetCount,
      ← RelativeVC.abs_sourceCutDefect_eq_abs_complementDefect]
    exact hdefect
  obtain ⟨harea, hlower, hupper⟩ := hnumeric x hx
  have hcenter := abs_le.mp habs
  unfold RelativeVC.centeredSetCount at hcenter
  constructor
  · rw [le_div_iff₀ harea]
    linarith
  · rw [div_le_iff₀ harea]
    linarith

theorem targetSelectedRate_mem_Icc_of_regularityGood
    (P : Measure (ℝ × UnitMark)) [IsProbabilityMeasure P]
    {m n : ℕ} (hm : 4 ≤ m) {xs : Fin m → ℝ × UnitMark}
    (hgood : xs ∈ RelativeVC.finiteHalfspaceRegularityGoodEvent
      P m m (m + 1) 64)
    {q xR xStar c C x : ℝ}
    (hnumeric : RightTailTargetNumericCondition P m n q xR xStar c C)
    (hx : x ∈ Icc xR xStar) :
    RelativeVC.sampleSetCountReal xs
        (RelativeVC.targetCutComplementSet q x) /
      targetUnclippedRemainingMass n q x ∈ Icc c C := by
  have hdefect := RelativeVC.targetCutDefect_uniform_regularity_on_goodEvent
    P hm hgood q x
  have habs :
      |RelativeVC.centeredSetCount P xs
        (RelativeVC.targetCutComplementSet q x)| ≤
        rightTailTargetVCBound P m q x := by
    rw [← targetComplementDefect_eq_centeredSetCount,
      ← RelativeVC.abs_targetCutDefect_eq_abs_complementDefect]
    exact hdefect
  obtain ⟨harea, hlower, hupper⟩ := hnumeric x hx
  have hcenter := abs_le.mp habs
  unfold RelativeVC.centeredSetCount at hcenter
  constructor
  · rw [le_div_iff₀ harea]
    linarith
  · rw [div_le_iff₀ harea]
    linarith

/-! ## Exact one-colour transport from a heterogeneous finite product -/

/-- Select distinct coordinates from a finite product and apply the rank-strip map.  The
pushforward is the product of the separately mapped coordinate laws; no equality between source
and target factors is used. -/
private theorem map_selectedRankArray_pi_eq
    {ι : Type*} [Fintype ι]
    (μ : ι → Measure MarkedHeight) [∀ i, IsProbabilityMeasure (μ i)]
    {m : ℕ} (select : Fin m ↪ ι) (scale : ℝ) :
    Measure.map
        (fun unseen : ι → MarkedHeight ↦ fun k : Fin m ↦
          rankStripMap scale (unseen (select k)))
        (Measure.pi μ) =
      Measure.pi fun k : Fin m ↦
        Measure.map (rankStripMap scale) (μ (select k)) := by
  let coordinate : ι → (ι → MarkedHeight) → MarkedHeight :=
    fun i unseen ↦ unseen i
  have hindependent : iIndepFun coordinate (Measure.pi μ) := by
    exact iIndepFun_pi (X := fun _i ↦ id)
      (fun _i ↦ measurable_id.aemeasurable)
  have hselected : iIndepFun
      (fun k : Fin m ↦ coordinate (select k)) (Measure.pi μ) :=
    hindependent.precomp select.injective
  have hrank : iIndepFun
      (fun k : Fin m ↦ (rankStripMap scale) ∘ coordinate (select k))
      (Measure.pi μ) :=
    hselected.comp (fun _k ↦ rankStripMap scale)
      (fun _k ↦ measurable_rankStripMap scale)
  have hmap := hrank.map_fun_eq_pi_map
    (fun _k ↦ ((measurable_rankStripMap scale).comp
      (measurable_pi_apply (select _k))).aemeasurable)
  change Measure.map
      (fun unseen : ι → MarkedHeight ↦ fun k : Fin m ↦
        rankStripMap scale (unseen (select k)))
      (Measure.pi μ) = _ at hmap
  rw [hmap]
  congr 1
  funext k
  rw [← Measure.map_map (measurable_rankStripMap scale)
    (measurable_pi_apply (select k)),
    (measurePreserving_eval μ (select k)).map_eq]

/-- Increasing reindexing of the unseen source labels of a realized terminal state. -/
private noncomputable def rightTailSourceLabelEmbedding
    (S : Finset (FeedbackLabel n)) (state : FeedbackStepState n)
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource) :
    Fin (Finset.univ \ state.seenSource).card ↪ feedbackUnseenFinset S where
  toFun k := by
    let J : Finset (Fin n) := Finset.univ \ state.seenSource
    let i : Fin n := J.orderEmbOfFin rfl k
    refine ⟨Sum.inl i, ?_⟩
    simp only [feedbackUnseenFinset, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hiS
    have hiSeen : i ∈ state.seenSource := (hsource i).mp hiS
    exact (Finset.mem_sdiff.mp (J.orderEmbOfFin_mem rfl k)).2 hiSeen
  inj' := by
    intro a b hab
    let J : Finset (Fin n) := Finset.univ \ state.seenSource
    apply (J.orderEmbOfFin rfl).injective
    have hlabels := congrArg
      (fun label : feedbackUnseenFinset S ↦ (label : FeedbackLabel n)) hab
    exact Sum.inl.inj hlabels

/-- Increasing reindexing of the unseen target labels of a realized terminal state. -/
private noncomputable def rightTailTargetLabelEmbedding
    (S : Finset (FeedbackLabel n)) (state : FeedbackStepState n)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget) :
    Fin (Finset.univ \ state.seenTarget).card ↪ feedbackUnseenFinset S where
  toFun k := by
    let J : Finset (Fin n) := Finset.univ \ state.seenTarget
    let j : Fin n := J.orderEmbOfFin rfl k
    refine ⟨Sum.inr j, ?_⟩
    simp only [feedbackUnseenFinset, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hjS
    have hjSeen : j ∈ state.seenTarget := (htarget j).mp hjS
    exact (Finset.mem_sdiff.mp (J.orderEmbOfFin_mem rfl k)).2 hjSeen
  inj' := by
    intro a b hab
    let J : Finset (Fin n) := Finset.univ \ state.seenTarget
    apply (J.orderEmbOfFin rfl).injective
    have hlabels := congrArg
      (fun label : feedbackUnseenFinset S ↦ (label : FeedbackLabel n)) hab
    exact Sum.inr.inj hlabels

/-- The one-source-coordinate rank law inside a realized history section. -/
noncomputable def rightTailSourceHistoryRankLaw
    (n : ℕ) (lam : ℝ) (state : FeedbackStepState n) (x : ℝ) :
    Measure (ℝ × UnitMark) :=
  Measure.map (rankStripMap (n : ℝ))
    ((unitSquareUniform : Measure MarkedHeight)[|
      sourceRawRemainingSetAt n lam state x])

/-- The one-target-coordinate rank law inside a realized history section. -/
noncomputable def rightTailTargetHistoryRankLaw
    (n : ℕ) (lam : ℝ) (state : FeedbackStepState n) (x : ℝ) :
    Measure (ℝ × UnitMark) :=
  Measure.map (rankStripMap (n : ℝ))
    ((unitSquareUniform : Measure MarkedHeight)[|
      targetRawRemainingSetAt n lam state x])

private noncomputable def rightTailSourceSelectedRankArray
    (n : ℕ) (S : Finset (FeedbackLabel n)) (state : FeedbackStepState n)
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    Fin (Finset.univ \ state.seenSource).card → ℝ × UnitMark :=
  fun k ↦ rankStripMap (n : ℝ)
    (unseen (rightTailSourceLabelEmbedding S state hsource k))

private noncomputable def rightTailTargetSelectedRankArray
    (n : ℕ) (S : Finset (FeedbackLabel n)) (state : FeedbackStepState n)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    Fin (Finset.univ \ state.seenTarget).card → ℝ × UnitMark :=
  fun k ↦ rankStripMap (n : ℝ)
    (unseen (rightTailTargetLabelEmbedding S state htarget k))

/-- Exact source pushforward of the conditioned heterogeneous unseen product. -/
private theorem map_rightTailSourceSelectedRankArray_eq
    (reference : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history x) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let state := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    let hsource : ∀ i : Fin n,
        (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource :=
      fun i ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
        reference lam x0 p0 sourcePattern targetPattern history i
    Measure.map (rightTailSourceSelectedRankArray n S state hsource)
        (Measure.pi fun label : feedbackUnseenFinset S ↦
          (unitSquareUniform : Measure MarkedHeight)[|
            feedbackLabelRemainingSetAt lam state x
              (label : FeedbackLabel n)]) =
      Measure.pi fun _k : Fin (Finset.univ \ state.seenSource).card ↦
        rightTailSourceHistoryRankLaw n lam state x := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let state := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  let remaining : feedbackUnseenFinset S → Set MarkedHeight := fun label ↦
    feedbackLabelRemainingSetAt lam state x (label : FeedbackLabel n)
  have hpositive : ∀ label,
      (unitSquareUniform : Measure MarkedHeight) (remaining label) ≠ 0 := by
    intro label
    exact ne_of_gt (unitSquareUniform_feedbackUnseenRectangularSetAt_factor_pos
      reference hlam0 hlamHalf href label)
  let _ : ∀ label : feedbackUnseenFinset S, IsProbabilityMeasure
      ((unitSquareUniform : Measure MarkedHeight)[|remaining label]) :=
    fun label ↦ cond_isProbabilityMeasure (hpositive label)
  let hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource :=
    fun i ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 sourcePattern targetPattern history i
  have hmap := map_selectedRankArray_pi_eq
    (fun label : feedbackUnseenFinset S ↦
      (unitSquareUniform : Measure MarkedHeight)[|remaining label])
    (rightTailSourceLabelEmbedding S state hsource) (n : ℝ)
  dsimp only
  rw [show rightTailSourceSelectedRankArray n S state hsource =
      fun unseen k ↦ rankStripMap (n : ℝ)
        (unseen (rightTailSourceLabelEmbedding S state hsource k)) from rfl]
  rw [hmap]
  congr 1

/-- Exact target pushforward; its one-coordinate law is kept separate from the source law. -/
private theorem map_rightTailTargetSelectedRankArray_eq
    (reference : FiniteSample n) {lam x0 p0 x : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryAtCoordinate reference lam x0 p0
      sourcePattern targetPattern history x) :
    let S := feedbackTerminalLabelSet sourcePattern targetPattern history
    let state := reference.scheduledState lam x0 p0
      sourcePattern targetPattern history
    let htarget : ∀ j : Fin n,
        (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget :=
      fun j ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
        reference lam x0 p0 sourcePattern targetPattern history j
    Measure.map (rightTailTargetSelectedRankArray n S state htarget)
        (Measure.pi fun label : feedbackUnseenFinset S ↦
          (unitSquareUniform : Measure MarkedHeight)[|
            feedbackLabelRemainingSetAt lam state x
              (label : FeedbackLabel n)]) =
      Measure.pi fun _k : Fin (Finset.univ \ state.seenTarget).card ↦
        rightTailTargetHistoryRankLaw n lam state x := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let state := reference.scheduledState lam x0 p0
    sourcePattern targetPattern history
  let remaining : feedbackUnseenFinset S → Set MarkedHeight := fun label ↦
    feedbackLabelRemainingSetAt lam state x (label : FeedbackLabel n)
  have hpositive : ∀ label,
      (unitSquareUniform : Measure MarkedHeight) (remaining label) ≠ 0 := by
    intro label
    exact ne_of_gt (unitSquareUniform_feedbackUnseenRectangularSetAt_factor_pos
      reference hlam0 hlamHalf href label)
  let _ : ∀ label : feedbackUnseenFinset S, IsProbabilityMeasure
      ((unitSquareUniform : Measure MarkedHeight)[|remaining label]) :=
    fun label ↦ cond_isProbabilityMeasure (hpositive label)
  let htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget :=
    fun j ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 sourcePattern targetPattern history j
  have hmap := map_selectedRankArray_pi_eq
    (fun label : feedbackUnseenFinset S ↦
      (unitSquareUniform : Measure MarkedHeight)[|remaining label])
    (rightTailTargetLabelEmbedding S state htarget) (n : ℝ)
  dsimp only
  rw [show rightTailTargetSelectedRankArray n S state htarget =
      fun unseen k ↦ rankStripMap (n : ℝ)
        (unseen (rightTailTargetLabelEmbedding S state htarget k)) from rfl]
  rw [hmap]
  congr 1

/-! ## Frozen counts as one-colour nested-complement counts -/

private theorem rightTailFrozenSourceCount_merge_eq
    (lam xR x : ℝ) (S : Finset (FeedbackLabel n))
    (state : FeedbackStepState n)
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (boundary : RevealedSnapshot n)
    (hstate : revealedSnapshotState boundary = state)
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    rightTailFrozenSourceCount lam xR x boundary
        (finiteSampleSeenUnseenMerge S seen unseen) =
      RelativeVC.sampleSetCountReal
        (rightTailSourceSelectedRankArray n S state hsource unseen)
        (RelativeVC.sourceCutComplementSet
          (segmentCurve state.x state.p (state.slope lam) xR) x) := by
  classical
  let J : Finset (Fin n) := Finset.univ \ state.seenSource
  let completed := finiteSampleSeenUnseenMerge S seen unseen
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let fullRank : Fin n → ℝ × UnitMark := fun i ↦
    rankStripMap (n : ℝ) (completed.sourcePoint i)
  have hselected : CountConditioning.selectedCoordinates J rfl fullRank =
      rightTailSourceSelectedRankArray n S state hsource unseen := by
    funext k
    have hiJ : J.orderEmbOfFin rfl k ∈ J := J.orderEmbOfFin_mem rfl k
    have hiNotSeen : J.orderEmbOfFin rfl k ∉ state.seenSource :=
      (Finset.mem_sdiff.mp hiJ).2
    have hiNotS : (Sum.inl (J.orderEmbOfFin rfl k) : FeedbackLabel n) ∉ S := by
      intro hiS
      exact hiNotSeen ((hsource _).mp hiS)
    have hpoint := congrFun
      (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen)
      (⟨Sum.inl (J.orderEmbOfFin rfl k), by
        simpa [feedbackUnseenFinset] using hiNotS⟩ : feedbackUnseenFinset S)
    change rankStripMap (n : ℝ)
        (completed.sourcePoint (J.orderEmbOfFin rfl k)) = _
    rw [show completed.sourcePoint (J.orderEmbOfFin rfl k) =
        unseen ⟨Sum.inl (J.orderEmbOfFin rfl k), by
          simpa [feedbackUnseenFinset] using hiNotS⟩ by
      simpa [completed, feedbackUnseenTuple, feedbackLabelTuple] using hpoint]
    rfl
  have hq : rightBoundaryFrozenHeight lam xR boundary = q := by
    simp [rightBoundaryFrozenHeight, hstate, q]
  rw [rightTailFrozenSourceCount, rightBoundaryFrozenSourceCount, hstate, hq]
  change (∑ i : Fin n, if i ∉ state.seenSource ∧
      x < completed.sourcePhase i q then 1 else 0) = _
  rw [show rightTailSourceSelectedRankArray n S state hsource unseen =
      CountConditioning.selectedCoordinates J rfl fullRank from hselected.symm]
  unfold RelativeVC.sampleSetCountReal
  rw [RelativeVC.sum_selectedCoordinates J rfl fullRank
    (fun z ↦ if z ∈ RelativeVC.sourceCutComplementSet q x
      then (1 : ℝ) else 0)]
  simp only [ite_and]
  rw [← Finset.sum_filter]
  dsimp only [J]
  apply Finset.sum_congr (by ext i; simp)
  intro i _hi
  simp [fullRank, completed, RelativeVC.sourceCutComplementSet,
    rankStripMap, rankCoordinateMap, FiniteSample.sourcePoint,
    FiniteSample.sourcePhase, FiniteSample.sourceSlope, mul_comm]

private theorem rightTailFrozenTargetCount_merge_eq
    (lam xR x : ℝ) (S : Finset (FeedbackLabel n))
    (state : FeedbackStepState n)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (boundary : RevealedSnapshot n)
    (hstate : revealedSnapshotState boundary = state)
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    rightTailFrozenTargetCount lam xR x boundary
        (finiteSampleSeenUnseenMerge S seen unseen) =
      RelativeVC.sampleSetCountReal
        (rightTailTargetSelectedRankArray n S state htarget unseen)
        (RelativeVC.targetCutComplementSet
          (segmentCurve state.x state.p (state.slope lam) xR) x) := by
  classical
  let J : Finset (Fin n) := Finset.univ \ state.seenTarget
  let completed := finiteSampleSeenUnseenMerge S seen unseen
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let fullRank : Fin n → ℝ × UnitMark := fun j ↦
    rankStripMap (n : ℝ) (completed.targetPoint j)
  have hselected : CountConditioning.selectedCoordinates J rfl fullRank =
      rightTailTargetSelectedRankArray n S state htarget unseen := by
    funext k
    have hjJ : J.orderEmbOfFin rfl k ∈ J := J.orderEmbOfFin_mem rfl k
    have hjNotSeen : J.orderEmbOfFin rfl k ∉ state.seenTarget :=
      (Finset.mem_sdiff.mp hjJ).2
    have hjNotS : (Sum.inr (J.orderEmbOfFin rfl k) : FeedbackLabel n) ∉ S := by
      intro hjS
      exact hjNotSeen ((htarget _).mp hjS)
    have hpoint := congrFun
      (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen)
      (⟨Sum.inr (J.orderEmbOfFin rfl k), by
        simpa [feedbackUnseenFinset] using hjNotS⟩ : feedbackUnseenFinset S)
    change rankStripMap (n : ℝ)
        (completed.targetPoint (J.orderEmbOfFin rfl k)) = _
    rw [show completed.targetPoint (J.orderEmbOfFin rfl k) =
        unseen ⟨Sum.inr (J.orderEmbOfFin rfl k), by
          simpa [feedbackUnseenFinset] using hjNotS⟩ by
      simpa [completed, feedbackUnseenTuple, feedbackLabelTuple] using hpoint]
    rfl
  have hq : rightBoundaryFrozenHeight lam xR boundary = q := by
    simp [rightBoundaryFrozenHeight, hstate, q]
  rw [rightTailFrozenTargetCount, rightBoundaryFrozenTargetCount, hstate, hq]
  change (∑ j : Fin n, if j ∉ state.seenTarget ∧
      x < completed.targetPhase j q then 1 else 0) = _
  rw [show rightTailTargetSelectedRankArray n S state htarget unseen =
      CountConditioning.selectedCoordinates J rfl fullRank from hselected.symm]
  unfold RelativeVC.sampleSetCountReal
  rw [RelativeVC.sum_selectedCoordinates J rfl fullRank
    (fun z ↦ if z ∈ RelativeVC.targetCutComplementSet q x
      then (1 : ℝ) else 0)]
  simp only [ite_and]
  rw [← Finset.sum_filter]
  dsimp only [J]
  apply Finset.sum_congr (by ext j; simp)
  intro j _hj
  simp [fullRank, completed, RelativeVC.targetCutComplementSet,
    rankStripMap, rankCoordinateMap, FiniteSample.targetPoint,
    FiniteSample.targetPhase, FiniteSample.targetSlope, mul_comm]

/-- On one realized boundary section, simultaneous source and target relative-VC goodness rules
out the complete nested rate-failure event. -/
private theorem rightTailRateFailureIndicator_merge_eq_zero_of_regularityGood
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (xStar c C : ℝ)
    (hxStar : x0 + (T : ℝ) ≤ xStar)
    (reference : FiniteSample n) (history : List (FeedbackLabel n))
    (href : HistoryAtCoordinate reference lam x0 p0
      (reference.initialSeenSource x0 p0) (reference.initialSeenTarget x0 p0)
      history (x0 + (T : ℝ)))
    (hSourcePos : (unitSquareUniform : Measure MarkedHeight)
      (sourceRawRemainingSetAt n lam
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history)
        (x0 + (T : ℝ))) ≠ 0)
    (hTargetPos : (unitSquareUniform : Measure MarkedHeight)
      (targetRawRemainingSetAt n lam
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history)
        (x0 + (T : ℝ))) ≠ 0)
    (hmSource : 4 ≤ (Finset.univ \
      (reference.scheduledState lam x0 p0
        (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history).seenSource).card)
    (hmTarget : 4 ≤ (Finset.univ \
      (reference.scheduledState lam x0 p0
        (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history).seenTarget).card)
    (hSourceNumeric : RightTailSourceNumericCondition
      (rightTailSourceHistoryRankLaw n lam
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history)
        (x0 + (T : ℝ)))
      (Finset.univ \
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history).seenSource).card n
      (segmentCurve
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history).x
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history).p
        ((reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history).slope lam)
        (x0 + (T : ℝ)))
      (x0 + (T : ℝ)) xStar c C)
    (hTargetNumeric : RightTailTargetNumericCondition
      (rightTailTargetHistoryRankLaw n lam
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history)
        (x0 + (T : ℝ)))
      (Finset.univ \
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history).seenTarget).card n
      (segmentCurve
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history).x
        (reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history).p
        ((reference.scheduledState lam x0 p0
          (reference.initialSeenSource x0 p0)
          (reference.initialSeenTarget x0 p0) history).slope lam)
        (x0 + (T : ℝ)))
      (x0 + (T : ℝ)) xStar c C)
    (unseen : feedbackUnseenFinset
      (feedbackTerminalLabelSet
        (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history) → MarkedHeight)
    (hSourceGood : rightTailSourceSelectedRankArray n
      (feedbackTerminalLabelSet
        (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history)
      (reference.scheduledState lam x0 p0
        (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history)
      (fun i ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
        reference lam x0 p0 (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history i)
      unseen ∈ RelativeVC.finiteHalfspaceRegularityGoodEvent
        (rightTailSourceHistoryRankLaw n lam
          (reference.scheduledState lam x0 p0
            (reference.initialSeenSource x0 p0)
            (reference.initialSeenTarget x0 p0) history)
          (x0 + (T : ℝ)))
        (Finset.univ \
          (reference.scheduledState lam x0 p0
            (reference.initialSeenSource x0 p0)
            (reference.initialSeenTarget x0 p0) history).seenSource).card
        (Finset.univ \
          (reference.scheduledState lam x0 p0
            (reference.initialSeenSource x0 p0)
            (reference.initialSeenTarget x0 p0) history).seenSource).card
        ((Finset.univ \
          (reference.scheduledState lam x0 p0
            (reference.initialSeenSource x0 p0)
            (reference.initialSeenTarget x0 p0) history).seenSource).card + 1) 64)
    (hTargetGood : rightTailTargetSelectedRankArray n
      (feedbackTerminalLabelSet
        (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history)
      (reference.scheduledState lam x0 p0
        (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history)
      (fun j ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
        reference lam x0 p0 (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history j)
      unseen ∈ RelativeVC.finiteHalfspaceRegularityGoodEvent
        (rightTailTargetHistoryRankLaw n lam
          (reference.scheduledState lam x0 p0
            (reference.initialSeenSource x0 p0)
            (reference.initialSeenTarget x0 p0) history)
          (x0 + (T : ℝ)))
        (Finset.univ \
          (reference.scheduledState lam x0 p0
            (reference.initialSeenSource x0 p0)
            (reference.initialSeenTarget x0 p0) history).seenTarget).card
        (Finset.univ \
          (reference.scheduledState lam x0 p0
            (reference.initialSeenSource x0 p0)
            (reference.initialSeenTarget x0 p0) history).seenTarget).card
        ((Finset.univ \
          (reference.scheduledState lam x0 p0
            (reference.initialSeenSource x0 p0)
            (reference.initialSeenTarget x0 p0) history).seenTarget).card + 1) 64) :
    let S := feedbackTerminalLabelSet
      (reference.initialSeenSource x0 p0)
      (reference.initialSeenTarget x0 p0) history
    let boundary := reference.revealedSnapshotAtElapsed
      hlam0 hlamHalf x0 p0 T
    rightTailRateFailureIndicator n lam (x0 + (T : ℝ)) xStar c C boundary
      (finiteSampleSeenUnseenMerge S (feedbackSeenTuple S reference) unseen) = 0 := by
  classical
  let xR := x0 + (T : ℝ)
  let S := feedbackTerminalLabelSet
    (reference.initialSeenSource x0 p0)
    (reference.initialSeenTarget x0 p0) history
  let state := reference.scheduledState lam x0 p0
    (reference.initialSeenSource x0 p0)
    (reference.initialSeenTarget x0 p0) history
  let boundary := reference.revealedSnapshotAtElapsed
    hlam0 hlamHalf x0 p0 T
  let completed := finiteSampleSeenUnseenMerge S
    (feedbackSeenTuple S reference) unseen
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let mSource := (Finset.univ \ state.seenSource).card
  let mTarget := (Finset.univ \ state.seenTarget).card
  let PSource := rightTailSourceHistoryRankLaw n lam state xR
  let PTarget := rightTailTargetHistoryRankLaw n lam state xR
  let hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource :=
    fun i ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 (reference.initialSeenSource x0 p0)
      (reference.initialSeenTarget x0 p0) history i
  let htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget :=
    fun j ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 (reference.initialSeenSource x0 p0)
      (reference.initialSeenTarget x0 p0) history j
  let _ : IsProbabilityMeasure
      ((unitSquareUniform : Measure MarkedHeight)[|
        sourceRawRemainingSetAt n lam state xR]) :=
    cond_isProbabilityMeasure hSourcePos
  let _ : IsProbabilityMeasure PSource :=
    Measure.isProbabilityMeasure_map (measurable_rankStripMap (n : ℝ)).aemeasurable
  let _ : IsProbabilityMeasure
      ((unitSquareUniform : Measure MarkedHeight)[|
        targetRawRemainingSetAt n lam state xR]) :=
    cond_isProbabilityMeasure hTargetPos
  let _ : IsProbabilityMeasure PTarget :=
    Measure.isProbabilityMeasure_map (measurable_rankStripMap (n : ℝ)).aemeasurable
  have hx0R : x0 ≤ xR := le_add_of_nonneg_right T.coe_nonneg
  have hendpoint : (⟨xR - x0, sub_nonneg.mpr hx0R⟩ : ℝ≥0) = T := by
    apply NNReal.eq
    change xR - x0 = (T : ℝ)
    dsimp only [xR]
    ring
  have hfeedbackState : reference.feedbackStateAtElapsed
      hlam0 hlamHalf x0 p0 T = state := by
    have h := HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
      reference hlam0 hlamHalf hx0R history href
    rwa [hendpoint] at h
  have hboundaryState : revealedSnapshotState boundary = state := by
    simp [boundary, revealedSnapshotState, FiniteSample.revealedSnapshotAtElapsed,
      revealedSnapshotFromState, hfeedbackState]
  have hq : rightBoundaryFrozenHeight lam xR boundary = q := by
    simp [rightBoundaryFrozenHeight, hboundaryState, q]
  have hgoodAt : ∀ y ∈ Icc xR xStar,
      ¬rightTailFrozenRateBadAt n lam xR c C y boundary completed := by
    intro y hy
    have hsourceCount := rightTailFrozenSourceCount_merge_eq
      lam xR y S state hsource boundary hboundaryState
      (feedbackSeenTuple S reference) unseen
    have htargetCount := rightTailFrozenTargetCount_merge_eq
      lam xR y S state htarget boundary hboundaryState
      (feedbackSeenTuple S reference) unseen
    have hsourceRate := sourceSelectedRate_mem_Icc_of_regularityGood
      PSource hmSource hSourceGood hSourceNumeric hy
    have htargetRate := targetSelectedRate_mem_Icc_of_regularityGood
      PTarget hmTarget hTargetGood hTargetNumeric hy
    have hsourceMem : rightTailFrozenSourceRate n lam xR y boundary completed ∈
        Icc c C := by
      unfold rightTailFrozenSourceRate
      rw [hsourceCount, hq]
      exact hsourceRate
    have htargetMem : rightTailFrozenTargetRate n lam xR y boundary completed ∈
        Icc c C := by
      unfold rightTailFrozenTargetRate
      rw [htargetCount, hq]
      exact htargetRate
    intro hbad
    exact hbad.elim (fun h ↦ h hsourceMem) (fun h ↦ h htargetMem)
  have hnotFailure : (boundary, completed) ∉
      rightTailRateFailureSet n lam xR xStar c C := by
    intro hfailure
    rw [rightTailRateFailureSet] at hfailure
    rcases hfailure with hboundary | hinterior
    · rcases hboundary with hleft | hright
      · exact (hgoodAt xR ⟨le_rfl, hxStar⟩) hleft
      · exact (hgoodAt xStar ⟨hxStar, le_rfl⟩) hright
    · rcases Set.mem_iUnion.mp hinterior with ⟨r, hr⟩
      split_ifs at hr with hrx
      · exact (hgoodAt (xR + (Real.toNNReal (r : ℝ) : ℝ))
          ⟨le_add_of_nonneg_right (Real.toNNReal (r : ℝ)).coe_nonneg,
            hrx.le⟩) hr
      · exact hr.elim
  change rightTailRateFailureIndicator n lam xR xStar c C boundary completed = 0
  rw [rightTailRateFailureIndicator, Set.indicator_of_notMem hnotFailure]

/-! ## Finite conditional failure bound -/

/-- Explicit geometric and numerical hypotheses on one realized right-boundary history.  This
predicate contains no empirical regularity conclusion and no failure-probability premise. -/
def RightTailBoundaryVCCondition
    (n : ℕ) (lam x0 p0 : ℝ) (T : ℝ≥0) (xStar c C : ℝ)
    (reference : FiniteSample n) (history : List (FeedbackLabel n)) : Prop :=
  let xR := x0 + (T : ℝ)
  let state := reference.scheduledState lam x0 p0
    (reference.initialSeenSource x0 p0)
    (reference.initialSeenTarget x0 p0) history
  let mSource := (Finset.univ \ state.seenSource).card
  let mTarget := (Finset.univ \ state.seenTarget).card
  let q := segmentCurve state.x state.p (state.slope lam) xR
  (unitSquareUniform : Measure MarkedHeight)
      (sourceRawRemainingSetAt n lam state xR) ≠ 0 ∧
    (unitSquareUniform : Measure MarkedHeight)
      (targetRawRemainingSetAt n lam state xR) ≠ 0 ∧
    4 ≤ mSource ∧ 4 ≤ mTarget ∧
    RightTailSourceNumericCondition
      (rightTailSourceHistoryRankLaw n lam state xR)
      mSource n q xR xStar c C ∧
    RightTailTargetNumericCondition
      (rightTailTargetHistoryRankLaw n lam state xR)
      mTarget n q xR xStar c C

/-- Source-plus-target explicit finite-sample failure envelope. -/
noncomputable def rightTailRateFailureEpsilon (mSource mTarget : ℕ) : ℝ :=
  (RelativeVC.regularityPolynomialBadBound mSource +
    RelativeVC.regularityPolynomialBadBound mTarget).toReal

/-- The explicit two-colour failure envelope is bounded by the sum of its two inverse-power
envelopes. -/
theorem rightTailRateFailureEpsilon_le_individual
    (mSource mTarget : ℕ) (hmSource : 1 ≤ mSource) (hmTarget : 1 ≤ mTarget) :
    rightTailRateFailureEpsilon mSource mTarget ≤
      256 * ((mSource : ℝ)⁻¹) ^ 12 + 256 * ((mTarget : ℝ)⁻¹) ^ 12 := by
  have hSourceFinite : RelativeVC.regularityPolynomialBadBound mSource ≠ ∞ := by
    unfold RelativeVC.regularityPolynomialBadBound
      RelativeVC.regularityPolynomialShellBound
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by simp))
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
  have hTargetFinite : RelativeVC.regularityPolynomialBadBound mTarget ≠ ∞ := by
    unfold RelativeVC.regularityPolynomialBadBound
      RelativeVC.regularityPolynomialShellBound
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by simp))
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
  rw [rightTailRateFailureEpsilon,
    ENNReal.toReal_add hSourceFinite hTargetFinite]
  apply add_le_add
  · have hSourcePos : (0 : ℝ) < mSource := by exact_mod_cast hmSource
    have h := ENNReal.toReal_mono (by finiteness)
      (RelativeVC.regularityPolynomialBadBound_le_inv_pow mSource hmSource)
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  · have hTargetPos : (0 : ℝ) < mTarget := by exact_mod_cast hmTarget
    have h := ENNReal.toReal_mono (by finiteness)
      (RelativeVC.regularityPolynomialBadBound_le_inv_pow mTarget hmTarget)
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    exact h

/-- If both boundary components contain at least `c A √n` unseen labels, the random
source-plus-target envelope has a deterministic `512 (c A √n)⁻¹²` bound. -/
theorem rightTailRateFailureEpsilon_le_scalingEnvelope
    (mSource mTarget n : ℕ) (A c : ℝ)
    (hscale : 1 ≤ c * A * Real.sqrt n)
    (hmSource : c * A * Real.sqrt n ≤ mSource)
    (hmTarget : c * A * Real.sqrt n ≤ mTarget) :
    rightTailRateFailureEpsilon mSource mTarget ≤
      512 * ((c * A * Real.sqrt n)⁻¹) ^ 12 := by
  have hmSourceOne : 1 ≤ mSource := by exact_mod_cast hscale.trans hmSource
  have hmTargetOne : 1 ≤ mTarget := by exact_mod_cast hscale.trans hmTarget
  have hsourceInv : ((mSource : ℝ)⁻¹) ≤ (c * A * Real.sqrt n)⁻¹ := by
    exact inv_anti₀ (by positivity) hmSource
  have htargetInv : ((mTarget : ℝ)⁻¹) ≤ (c * A * Real.sqrt n)⁻¹ := by
    exact inv_anti₀ (by positivity) hmTarget
  calc
    rightTailRateFailureEpsilon mSource mTarget ≤
        256 * ((mSource : ℝ)⁻¹) ^ 12 +
          256 * ((mTarget : ℝ)⁻¹) ^ 12 :=
      rightTailRateFailureEpsilon_le_individual
        mSource mTarget hmSourceOne hmTargetOne
    _ ≤ 256 * ((c * A * Real.sqrt n)⁻¹) ^ 12 +
          256 * ((c * A * Real.sqrt n)⁻¹) ^ 12 := by
      gcongr
    _ = 512 * ((c * A * Real.sqrt n)⁻¹) ^ 12 := by ring

/-- The deterministic paper-scale envelope tends to zero for every fixed `A` and `c`. -/
theorem tendsto_rightTailRateFailureScalingEnvelope (A c : ℝ) :
    Tendsto (fun n : ℕ ↦ 512 * ((c * A * Real.sqrt n)⁻¹) ^ 12)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹)
      atTop (nhds 0) := hsqrt.inv_tendsto_atTop
  have hscaled : Tendsto
      (fun n : ℕ ↦ (c * A)⁻¹ * (Real.sqrt (n : ℝ))⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hinv)
  have hpow := hscaled.pow 12
  have hmul := (tendsto_const_nhds (x := (512 : ℝ))).mul hpow
  convert hmul using 1
  · funext n
    congr 2
    rw [mul_inv_rev, mul_inv_rev]
    ring
  · norm_num

/-- More generally, the source-plus-target envelope tends to zero whenever both component
sample sizes tend to infinity. -/
theorem tendsto_rightTailRateFailureEpsilon_of_counts
    {mSource mTarget : ℕ → ℕ}
    (hSource : Tendsto mSource atTop atTop)
    (hTarget : Tendsto mTarget atTop atTop) :
    Tendsto (fun k ↦ rightTailRateFailureEpsilon (mSource k) (mTarget k))
      atTop (nhds 0) := by
  have hSourceBound :=
    RelativeVC.tendsto_regularityPolynomialBadBound.comp hSource
  have hTargetBound :=
    RelativeVC.tendsto_regularityPolynomialBadBound.comp hTarget
  have hsum : Tendsto
      (fun k ↦ RelativeVC.regularityPolynomialBadBound (mSource k) +
        RelativeVC.regularityPolynomialBadBound (mTarget k))
      atTop (nhds 0) := by
    simpa using hSourceBound.add hTargetBound
  convert (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsum using 1 <;>
    simp [rightTailRateFailureEpsilon, Function.comp_def]

/-- Finite-`n` right-boundary failure bound on one realized history section.  The two colours are
transported to their own conditional rank laws before the relative-VC estimates are applied. -/
theorem rightBoundaryScalarCandidate_rightTailRateFailure_le
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (xStar c C : ℝ)
    (hxStar : x0 + (T : ℝ) ≤ xStar)
    (reference : FiniteSample n) (history : List (FeedbackLabel n))
    (href : HistoryAtCoordinate reference lam x0 p0
      (reference.initialSeenSource x0 p0) (reference.initialSeenTarget x0 p0)
      history (x0 + (T : ℝ)))
    (hcondition : RightTailBoundaryVCCondition
      n lam x0 p0 T xStar c C reference history) :
    let state := reference.scheduledState lam x0 p0
      (reference.initialSeenSource x0 p0)
      (reference.initialSeenTarget x0 p0) history
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
        (rightTailRateFailureIndicator n lam (x0 + (T : ℝ)) xStar c C)
        reference ≤
      rightTailRateFailureEpsilon
        (Finset.univ \ state.seenSource).card
        (Finset.univ \ state.seenTarget).card := by
  classical
  let xR := x0 + (T : ℝ)
  let S := feedbackTerminalLabelSet
    (reference.initialSeenSource x0 p0)
    (reference.initialSeenTarget x0 p0) history
  let state := reference.scheduledState lam x0 p0
    (reference.initialSeenSource x0 p0)
    (reference.initialSeenTarget x0 p0) history
  let boundary := reference.revealedSnapshotAtElapsed
    hlam0 hlamHalf x0 p0 T
  let mSource := (Finset.univ \ state.seenSource).card
  let mTarget := (Finset.univ \ state.seenTarget).card
  let PSource := rightTailSourceHistoryRankLaw n lam state xR
  let PTarget := rightTailTargetHistoryRankLaw n lam state xR
  let hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource :=
    fun i ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 (reference.initialSeenSource x0 p0)
      (reference.initialSeenTarget x0 p0) history i
  let htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget :=
    fun j ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 (reference.initialSeenSource x0 p0)
      (reference.initialSeenTarget x0 p0) history j
  dsimp only [RightTailBoundaryVCCondition] at hcondition
  rcases hcondition with
    ⟨hSourcePos, hTargetPos, hmSource, hmTarget,
      hSourceNumeric, hTargetNumeric⟩
  let remaining : feedbackUnseenFinset S → Set MarkedHeight := fun label ↦
    feedbackLabelRemainingSetAt lam state xR (label : FeedbackLabel n)
  let factors : feedbackUnseenFinset S → Measure MarkedHeight := fun label ↦
    (unitSquareUniform : Measure MarkedHeight)[|remaining label]
  let ν := feedbackUnseenTupleLaw S
  let μ := Measure.pi factors
  let R := feedbackUnseenRectangularSetAt lam state xR S
  let merge : (feedbackUnseenFinset S → MarkedHeight) → FiniteSample n :=
    fun unseen ↦ finiteSampleSeenUnseenMerge S
      (feedbackSeenTuple S reference) unseen
  let E : Set (feedbackUnseenFinset S → MarkedHeight) :=
    {unseen | (boundary, merge unseen) ∈
      rightTailRateFailureSet n lam xR xStar c C}
  let sourceGood := RelativeVC.finiteHalfspaceRegularityGoodEvent
    PSource mSource mSource (mSource + 1) 64
  let targetGood := RelativeVC.finiteHalfspaceRegularityGoodEvent
    PTarget mTarget mTarget (mTarget + 1) 64
  let sourceBad :=
    (rightTailSourceSelectedRankArray n S state hsource) ⁻¹' sourceGoodᶜ
  let targetBad :=
    (rightTailTargetSelectedRankArray n S state htarget) ⁻¹' targetGoodᶜ
  have hpositive : ∀ label,
      (unitSquareUniform : Measure MarkedHeight) (remaining label) ≠ 0 := by
    intro label
    exact ne_of_gt (unitSquareUniform_feedbackUnseenRectangularSetAt_factor_pos
      reference hlam0 hlamHalf href label)
  let _ : ∀ label : feedbackUnseenFinset S,
      IsProbabilityMeasure (factors label) := fun label ↦
    cond_isProbabilityMeasure (hpositive label)
  let _ : IsProbabilityMeasure
      ((unitSquareUniform : Measure MarkedHeight)[|
        sourceRawRemainingSetAt n lam state xR]) :=
    cond_isProbabilityMeasure hSourcePos
  let _ : IsProbabilityMeasure PSource :=
    Measure.isProbabilityMeasure_map (measurable_rankStripMap (n : ℝ)).aemeasurable
  let _ : IsProbabilityMeasure
      ((unitSquareUniform : Measure MarkedHeight)[|
        targetRawRemainingSetAt n lam state xR]) :=
    cond_isProbabilityMeasure hTargetPos
  let _ : IsProbabilityMeasure PTarget :=
    Measure.isProbabilityMeasure_map (measurable_rankStripMap (n : ℝ)).aemeasurable
  have hx0R : x0 ≤ xR := le_add_of_nonneg_right T.coe_nonneg
  have hendpoint : (⟨xR - x0, sub_nonneg.mpr hx0R⟩ : ℝ≥0) = T := by
    apply NNReal.eq
    change xR - x0 = (T : ℝ)
    dsimp only [xR]
    ring
  have hmerge : Measurable merge := by
    exact (measurable_finiteSampleSeenUnseenMerge S).comp
      (measurable_const.prodMk measurable_id)
  have hE : MeasurableSet E := by
    exact (measurableSet_rightTailRateFailureSet n lam xR xStar c C).preimage
      (measurable_const.prodMk hmerge)
  have hsection :
      {unseen | HistoryAtCoordinate (merge unseen) lam x0 p0
        (reference.initialSeenSource x0 p0)
        (reference.initialSeenTarget x0 p0) history xR} = R := by
    ext unseen
    exact historyAtCoordinate_finiteSampleSeenUnseenMerge_iff
      reference hlam0 hlamHalf href (feedbackSeenTuple S reference) unseen rfl
  have hcond : ν[|R] = μ := by
    have h := feedbackUnseenTupleLaw_cond_historySection_eq_pi
      reference hlam0 hlamHalf href
    dsimp only at h
    rw [hsection] at h
    simpa [ν, μ, factors, remaining, S, state, xR] using h
  have hnormalized : normalizedRestrictionIntegral ν R
      (fun unseen ↦ rightTailRateFailureIndicator n lam xR xStar c C
        boundary (merge unseen)) = (ν[|R]).real E := by
    rw [← integral_cond_eq_normalizedRestrictionIntegral]
    change (∫ unseen, E.indicator (fun _ ↦ (1 : ℝ)) unseen ∂ν[|R]) =
      (ν[|R]).real E
    exact integral_indicator_one hE
  have hsubset : E ⊆ sourceBad ∪ targetBad := by
    intro unseen hunseen
    by_cases hs : rightTailSourceSelectedRankArray n S state hsource unseen ∈
        sourceGood
    · by_cases ht : rightTailTargetSelectedRankArray n S state htarget unseen ∈
          targetGood
      · have hzero :=
          rightTailRateFailureIndicator_merge_eq_zero_of_regularityGood
            (n := n) hlam0 hlamHalf x0 p0 T xStar c C hxStar reference history
            href hSourcePos hTargetPos hmSource hmTarget hSourceNumeric
            hTargetNumeric unseen hs ht
        dsimp only at hzero
        have hpair : (boundary, merge unseen) ∈
            rightTailRateFailureSet n lam xR xStar c C := by
          exact hunseen
        have hone : rightTailRateFailureIndicator n lam xR xStar c C boundary
            (merge unseen) = 1 := by
          rw [rightTailRateFailureIndicator, Set.indicator_of_mem hpair]
          rfl
        rw [hone] at hzero
        norm_num at hzero
      · exact Set.mem_union_right _ ht
    · exact Set.mem_union_left _ hs
  have hsourceMeas : Measurable
      (rightTailSourceSelectedRankArray n S state hsource) := by
    apply measurable_pi_lambda
    intro k
    exact (measurable_rankStripMap (n : ℝ)).comp
      (measurable_pi_apply (rightTailSourceLabelEmbedding S state hsource k))
  have htargetMeas : Measurable
      (rightTailTargetSelectedRankArray n S state htarget) := by
    apply measurable_pi_lambda
    intro k
    exact (measurable_rankStripMap (n : ℝ)).comp
      (measurable_pi_apply (rightTailTargetLabelEmbedding S state htarget k))
  have hsourceMap : Measure.map
      (rightTailSourceSelectedRankArray n S state hsource) μ =
      Measure.pi (fun _k : Fin mSource ↦ PSource) := by
    simpa [μ, factors, remaining, mSource, PSource, S, state, xR, hsource]
      using map_rightTailSourceSelectedRankArray_eq
        reference hlam0 hlamHalf href
  have htargetMap : Measure.map
      (rightTailTargetSelectedRankArray n S state htarget) μ =
      Measure.pi (fun _k : Fin mTarget ↦ PTarget) := by
    simpa [μ, factors, remaining, mTarget, PTarget, S, state, xR, htarget]
      using map_rightTailTargetSelectedRankArray_eq
        reference hlam0 hlamHalf href
  have hsourceMeasure : μ sourceBad ≤
      RelativeVC.regularityPolynomialBadBound mSource := by
    have hle := Measure.le_map_apply (μ := μ)
      hsourceMeas.aemeasurable sourceGoodᶜ
    rw [hsourceMap] at hle
    exact hle.trans
      (RelativeVC.finiteHalfspaceRegularityGoodEvent_compl_le_polynomial
        PSource mSource hmSource)
  have htargetMeasure : μ targetBad ≤
      RelativeVC.regularityPolynomialBadBound mTarget := by
    have hle := Measure.le_map_apply (μ := μ)
      htargetMeas.aemeasurable targetGoodᶜ
    rw [htargetMap] at hle
    exact hle.trans
      (RelativeVC.finiteHalfspaceRegularityGoodEvent_compl_le_polynomial
        PTarget mTarget hmTarget)
  have hmeasure : μ E ≤
      RelativeVC.regularityPolynomialBadBound mSource +
        RelativeVC.regularityPolynomialBadBound mTarget := by
    calc
      μ E ≤ μ (sourceBad ∪ targetBad) := measure_mono hsubset
      _ ≤ μ sourceBad + μ targetBad := measure_union_le _ _
      _ ≤ RelativeVC.regularityPolynomialBadBound mSource +
          RelativeVC.regularityPolynomialBadBound mTarget :=
        add_le_add hsourceMeasure htargetMeasure
  have hreal : μ.real E ≤ rightTailRateFailureEpsilon mSource mTarget := by
    rw [rightTailRateFailureEpsilon]
    have hpolyFinite : ∀ m : ℕ,
        RelativeVC.regularityPolynomialBadBound m ≠ ⊤ := by
      intro m
      unfold RelativeVC.regularityPolynomialBadBound
        RelativeVC.regularityPolynomialShellBound
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp))
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    exact (ENNReal.toReal_le_toReal (measure_ne_top μ E)
      (ENNReal.add_ne_top.mpr
        ⟨hpolyFinite mSource, hpolyFinite mTarget⟩)).2 hmeasure
  have hcandidate := rightBoundaryScalarCandidate_eq_historySectionNormalized
    (n := n) hlam0 hlamHalf hx0R T
    (rightTailRateFailureIndicator n lam xR xStar c C)
    (stronglyMeasurable_rightTailRateFailureIndicator n lam xR xStar c C)
    reference (reference.initialSeenSource x0 p0)
    (reference.initialSeenTarget x0 p0) history href
  dsimp only at hcandidate
  rw [hendpoint] at hcandidate
  change rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
      (rightTailRateFailureIndicator n lam xR xStar c C) reference ≤ _
  rw [hcandidate, hnormalized, hcond]
  exact hreal

/-! ## Actual boundary and usual-filtration endpoint -/

/-- Number of source labels declared unseen by the actual boundary snapshot. -/
noncomputable def rightTailBoundarySourceLabelCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℕ :=
  (Finset.univ \
    (revealedSnapshotState (sample.revealedSnapshotAtElapsed
      hlam0 hlamHalf x0 p0 T)).seenSource).card

/-- Target analogue of `rightTailBoundarySourceLabelCount`. -/
noncomputable def rightTailBoundaryTargetLabelCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℕ :=
  (Finset.univ \
    (revealedSnapshotState (sample.revealedSnapshotAtElapsed
      hlam0 hlamHalf x0 p0 T)).seenTarget).card

/-- Every realized history at the boundary satisfies the explicit geometric/numerical VC
conditions.  This is the paper boundary-good component used below. -/
def RightTailBoundaryVCGood
    (n : ℕ) (lam x0 p0 : ℝ) (T : ℝ≥0) (xStar c C : ℝ)
    (sample : FiniteSample n) : Prop :=
  ∀ history : List (FeedbackLabel n),
    HistoryAtCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0)
      history (x0 + (T : ℝ)) →
    RightTailBoundaryVCCondition n lam x0 p0 T xStar c C sample history

/-- The actual completed-sample event evaluates the frozen failure integrand at its own boundary
snapshot. -/
noncomputable def actualRightTailRateFailure
    (n : ℕ) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (xStar c C : ℝ)
    (sample : FiniteSample n) : ℝ :=
  rightTailRateFailureIndicator n lam (x0 + (T : ℝ)) xStar c C
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample

/-- The stopping construction's height process, decoded from each sample's actual boundary
snapshot at the deterministic coordinate `x0 + T`. -/
noncomputable def actualRightTailFrozenHeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)

theorem measurable_actualRightTailFrozenHeight
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) :
    Measurable (actualRightTailFrozenHeight
      (n := n) hlam0 hlamHalf x0 p0 T) := by
  exact (measurable_rightBoundaryFrozenHeight
    (n := n) lam (x0 + (T : ℝ))).comp
      (measurable_revealedSnapshotAtElapsed
        (n := n) hlam0 hlamHalf x0 p0 T)

theorem norm_actualRightTailRateFailure_le_one
    (n : ℕ) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (xStar c C : ℝ)
    (sample : FiniteSample n) :
    ‖actualRightTailRateFailure n hlam0 hlamHalf x0 p0 T xStar c C sample‖ ≤ 1 := by
  exact norm_rightTailRateFailureIndicator_le_one
    n lam (x0 + (T : ℝ)) xStar c C _ sample

/-- Actual self-integrand conditional expectation is bounded by the normalized boundary
candidate, with no history-section premise. -/
theorem condExp_rightTailRateFailure_le_candidate
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T) (xStar c C : ℝ) :
    (finiteSampleLaw n : Measure (FiniteSample n))[
        actualRightTailRateFailure n hlam0 hlamHalf x0 p0 T xStar c C |
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] ≤ᵐ[
      (finiteSampleLaw n : Measure (FiniteSample n))]
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
        (rightTailRateFailureIndicator n lam (x0 + (T : ℝ)) xStar c C) := by
  exact condExp_actualBoundaryEvaluation_le_candidate
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0
      (rightTailRateFailureIndicator n lam (x0 + (T : ℝ)) xStar c C)
      (stronglyMeasurable_rightTailRateFailureIndicator
        n lam (x0 + (T : ℝ)) xStar c C)
      (by norm_num) (fun boundary completed ↦
        norm_rightTailRateFailureIndicator_le_one
          n lam (x0 + (T : ℝ)) xStar c C boundary completed)

/-- On the actual no-tie boundary-good component, the candidate has the deterministic explicit
source-plus-target polynomial bound. -/
theorem rightBoundaryScalarCandidate_rightTailRateFailure_le_epsilon
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (xStar c C : ℝ)
    (hxStar : x0 + (T : ℝ) ≤ xStar)
    (sample : FiniteSample n) (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hgood : RightTailBoundaryVCGood n lam x0 p0 T xStar c C sample) :
    rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
        (rightTailRateFailureIndicator n lam (x0 + (T : ℝ)) xStar c C)
        sample ≤
      rightTailRateFailureEpsilon
        (rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample)
        (rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample) := by
  obtain ⟨history, href, _hlen⟩ :=
    sample.exists_historyAtCoordinate_of_noFeedbackTies
      hlam0 hlamHalf (le_add_of_nonneg_right T.coe_nonneg) hNoTie
  let state := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have hbound := rightBoundaryScalarCandidate_rightTailRateFailure_le
    (n := n) hlam0 hlamHalf x0 p0 T xStar c C hxStar sample history href
      (hgood history href)
  have hstateAt : sample.feedbackStateAtElapsed
      hlam0 hlamHalf x0 p0 T = state := by
    let xR := x0 + (T : ℝ)
    have hx0R : x0 ≤ xR := le_add_of_nonneg_right T.coe_nonneg
    have hendpoint : (⟨xR - x0, sub_nonneg.mpr hx0R⟩ : ℝ≥0) = T := by
      apply NNReal.eq
      change xR - x0 = (T : ℝ)
      dsimp only [xR]
      ring
    have h := HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
      sample hlam0 hlamHalf hx0R history href
    rwa [hendpoint] at h
  have hsnapshotState : revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) = state := by
    simp [revealedSnapshotState, FiniteSample.revealedSnapshotAtElapsed,
      revealedSnapshotFromState, hstateAt]
  simpa [rightTailBoundarySourceLabelCount,
    rightTailBoundaryTargetLabelCount, hsnapshotState, state] using hbound

/-- Paper-ready finite-`n` actual conditional failure bound on the boundary-good component. -/
theorem condExp_rightTailRateFailure_le_epsilon_on_boundaryGood
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T) (xStar c C : ℝ)
    (hxStar : x0 + (T : ℝ) ≤ xStar) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      sample.NoFeedbackTies lam x0 p0 →
      RightTailBoundaryVCGood n lam x0 p0 T xStar c C sample →
      (finiteSampleLaw n : Measure (FiniteSample n))[
          actualRightTailRateFailure n hlam0 hlamHalf x0 p0 T xStar c C |
          usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] sample ≤
        rightTailRateFailureEpsilon
          (rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample)
          (rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample) := by
  filter_upwards [condExp_rightTailRateFailure_le_candidate
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0 xStar c C] with sample hcandidate
  intro hNoTie hgood
  exact hcandidate.trans
    (rightBoundaryScalarCandidate_rightTailRateFailure_le_epsilon
      (n := n) hlam0 hlamHalf x0 p0 T xStar c C hxStar sample hNoTie hgood)

/-- The paper's two-step actual chain, retaining the normalized boundary candidate as the
intermediate quantity. -/
theorem condExp_rightTailRateFailure_le_candidate_le_epsilon_on_boundaryGood
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T) (xStar c C : ℝ)
    (hxStar : x0 + (T : ℝ) ≤ xStar) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      sample.NoFeedbackTies lam x0 p0 →
      RightTailBoundaryVCGood n lam x0 p0 T xStar c C sample →
      (finiteSampleLaw n : Measure (FiniteSample n))[
          actualRightTailRateFailure n hlam0 hlamHalf x0 p0 T xStar c C |
          usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] sample ≤
        rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
          (rightTailRateFailureIndicator
            n lam (x0 + (T : ℝ)) xStar c C) sample ∧
      rightBoundaryScalarCandidate hlam0 hlamHalf x0 p0 T T
          (rightTailRateFailureIndicator
            n lam (x0 + (T : ℝ)) xStar c C) sample ≤
        rightTailRateFailureEpsilon
          (rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample)
          (rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample) := by
  filter_upwards [condExp_rightTailRateFailure_le_candidate
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0 xStar c C]
      with sample hcandidate
  intro hNoTie hgood
  exact ⟨hcandidate,
    rightBoundaryScalarCandidate_rightTailRateFailure_le_epsilon
      (n := n) hlam0 hlamHalf x0 p0 T xStar c C
        hxStar sample hNoTie hgood⟩

/-- Deterministic paper-scale version of the actual finite-`n` conditional failure bound. -/
theorem condExp_rightTailRateFailure_le_scalingEnvelope_on_boundaryGood
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (hT0 : 0 < T) (xStar c C A density : ℝ)
    (hxStar : x0 + (T : ℝ) ≤ xStar)
    (hscale : 1 ≤ density * A * Real.sqrt n) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      sample.NoFeedbackTies lam x0 p0 →
      RightTailBoundaryVCGood n lam x0 p0 T xStar c C sample →
      density * A * Real.sqrt n ≤
        rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample →
      density * A * Real.sqrt n ≤
        rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample →
      (finiteSampleLaw n : Measure (FiniteSample n))[
          actualRightTailRateFailure n hlam0 hlamHalf x0 p0 T xStar c C |
          usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] sample ≤
        512 * ((density * A * Real.sqrt n)⁻¹) ^ 12 := by
  filter_upwards [condExp_rightTailRateFailure_le_epsilon_on_boundaryGood
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0 xStar c C hxStar]
      with sample hsample
  intro hNoTie hgood hSource hTarget
  exact (hsample hNoTie hgood).trans
    (rightTailRateFailureEpsilon_le_scalingEnvelope
      (rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample)
      (rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample)
      n A density hscale hSource hTarget)

/-! ## Actual boundary cardinalities -/

/-- On the no-tie component, the strict frozen source pattern has exactly the actual number of
source labels remaining at the boundary. -/
theorem rightSourceInitialPattern_card_eq_rightBoundarySourceRemaining
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    ((rightSourceInitialPattern
      (fun _completed ↦ rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T))
      (x0 + (T : ℝ)) sample).card : ℝ) =
      rightBoundarySourceRemaining hlam0 hlamHalf x0 p0 T sample := by
  rw [rightBoundarySourceRemaining,
    safeSourceRemainingAt_eq_n_sub_sourceCutCount
      hlam0 hlamHalf x0 p0 T sample hNoTie,
    rightBoundaryFrozenHeight_revealedSnapshotAtElapsed
      hlam0 hlamHalf x0 p0 T sample hNoTie]
  classical
  simp only [rightSourceInitialPattern, RelativeVC.sourceCutCount,
    RelativeVC.sampleErrorSum, RelativeVC.sourceCutEval,
    RelativeVC.falseCutTarget, zeroOneLoss,
    feedbackSourceRankArray, rankStripMap, rankCoordinateMap,
    FiniteSample.sourcePoint, Finset.card_filter]
  push_cast
  have hone : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
  conv_rhs => lhs; rw [hone]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  change (if x0 + (T : ℝ) <
      (n : ℝ) * sample.sourceHeight i + (1 - sample.sourceMark i) *
        safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 T sample
    then 1 else 0) =
      1 - if decide ((n : ℝ) * sample.sourceHeight i +
        safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 T sample *
          (1 - sample.sourceMark i) ≤ x0 + (T : ℝ)) = false
      then 0 else 1
  ring_nf
  simp only [decide_eq_false_iff_not]
  split_ifs <;> norm_num <;> linarith

/-- Target analogue of
`rightSourceInitialPattern_card_eq_rightBoundarySourceRemaining`. -/
theorem rightTargetInitialPattern_card_eq_rightBoundaryTargetRemaining
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    ((rightTargetInitialPattern
      (fun _completed ↦ rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T))
      (x0 + (T : ℝ)) sample).card : ℝ) =
      rightBoundaryTargetRemaining hlam0 hlamHalf x0 p0 T sample := by
  rw [rightBoundaryTargetRemaining,
    safeTargetRemainingAt_eq_n_sub_targetCutCount
      hlam0 hlamHalf x0 p0 T sample hNoTie,
    rightBoundaryFrozenHeight_revealedSnapshotAtElapsed
      hlam0 hlamHalf x0 p0 T sample hNoTie]
  classical
  simp only [rightTargetInitialPattern, RelativeVC.targetCutCount,
    RelativeVC.sampleErrorSum, RelativeVC.targetCutEval,
    RelativeVC.falseCutTarget, zeroOneLoss,
    feedbackTargetRankArray, rankStripMap, rankCoordinateMap,
    FiniteSample.targetPoint, Finset.card_filter]
  push_cast
  have hone : (n : ℝ) = ∑ _j : Fin n, (1 : ℝ) := by simp
  conv_rhs => lhs; rw [hone]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  change (if x0 + (T : ℝ) <
      (n : ℝ) * sample.targetHeight j - (1 + sample.targetMark j) *
        safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 T sample
    then 1 else 0) =
      1 - if decide ((n : ℝ) * sample.targetHeight j -
        safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 T sample *
          (1 + sample.targetMark j) ≤ x0 + (T : ℝ)) = false
      then 0 else 1
  ring_nf
  simp only [decide_eq_false_iff_not]
  split_ifs <;> norm_num <;> linarith

/-! ## From the grid event to the strict right-tail stopping event -/

/-- The actual source remainder is the number of labels not yet present in the post-jump
boundary state. -/
theorem safeSourceRemainingAt_eq_unseen_card
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    safeSourceRemainingAt hlam0 hlamHalf x0 p0 T sample =
      ((Finset.univ \ (sample.feedbackStateAtElapsed
        hlam0 hlamHalf x0 p0 T).seenSource).card : ℝ) := by
  classical
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 T
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
  have hcount :
      ((state.seenSource \ sample.initialSeenSource x0 p0).card : ℝ) +
          (sample.initialSeenSource x0 p0).card = state.seenSource.card := by
    exact_mod_cast hcardNat
  have hseenLe : state.seenSource.card ≤ n := by
    simpa using state.seenSource.card_le_univ
  have hcard : ((Finset.univ \ state.seenSource).card : ℝ) =
      (n : ℝ) - state.seenSource.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub hseenLe]
  rw [show sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 T = state by rfl]
  rw [hcard]
  unfold safeSourceRemainingAt safeInitialSourceRemainingReal
    initialSourceRemainingReal
  rw [safeSourceCount_eq_card_diff]
  simp only [hNoTie, ite_true]
  linarith

/-- Target analogue of `safeSourceRemainingAt_eq_unseen_card`. -/
theorem safeTargetRemainingAt_eq_unseen_card
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    safeTargetRemainingAt hlam0 hlamHalf x0 p0 T sample =
      ((Finset.univ \ (sample.feedbackStateAtElapsed
        hlam0 hlamHalf x0 p0 T).seenTarget).card : ℝ) := by
  classical
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 T
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
  have hcount :
      ((state.seenTarget \ sample.initialSeenTarget x0 p0).card : ℝ) +
          (sample.initialSeenTarget x0 p0).card = state.seenTarget.card := by
    exact_mod_cast hcardNat
  have hseenLe : state.seenTarget.card ≤ n := by
    simpa using state.seenTarget.card_le_univ
  have hcard : ((Finset.univ \ state.seenTarget).card : ℝ) =
      (n : ℝ) - state.seenTarget.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub hseenLe]
  rw [show sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 T = state by rfl]
  rw [hcard]
  unfold safeTargetRemainingAt safeInitialTargetRemainingReal
    initialTargetRemainingReal
  rw [safeTargetCount_eq_card_diff]
  simp only [hNoTie, ite_true]
  linarith

/-- On the actual no-tie boundary, the frozen source pattern is exactly the set of labels that
the boundary snapshot records as unseen. -/
theorem rightSourceInitialPattern_eq_boundaryUnseen
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    rightSourceInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        (x0 + (T : ℝ)) sample =
      Finset.univ \ (revealedSnapshotState
        (sample.revealedSnapshotAtElapsed
          hlam0 hlamHalf x0 p0 T)).seenSource := by
  classical
  let xR := x0 + (T : ℝ)
  obtain ⟨history, href, _hlen⟩ :=
    sample.exists_historyAtCoordinate_of_noFeedbackTies
      hlam0 hlamHalf (le_add_of_nonneg_right T.coe_nonneg) hNoTie
  let state := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have hstate : sample.feedbackStateAtElapsed
      hlam0 hlamHalf x0 p0 T = state := by
    have hx0R : x0 ≤ xR := le_add_of_nonneg_right T.coe_nonneg
    have hendpoint : (⟨xR - x0, sub_nonneg.mpr hx0R⟩ : ℝ≥0) = T := by
      apply NNReal.eq
      change xR - x0 = (T : ℝ)
      dsimp only [xR]
      ring
    have h := HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
      sample hlam0 hlamHalf hx0R history href
    rwa [hendpoint] at h
  have hsnapshotState : revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) = state := by
    simp [revealedSnapshotState, FiniteSample.revealedSnapshotAtElapsed,
      revealedSnapshotFromState, hstate, FeedbackStepState.unpack_pack]
  have hq : actualRightTailFrozenHeight
      (n := n) hlam0 hlamHalf x0 p0 T sample =
        segmentCurve state.x state.p (state.slope lam) xR := by
    rw [actualRightTailFrozenHeight,
      rightBoundaryFrozenHeight_revealedSnapshotAtElapsed
        hlam0 hlamHalf x0 p0 T sample hNoTie,
      rightBoundaryHeight, safeFeedbackHeightAtElapsed,
      ite_eq_left hNoTie,
      sample.feedbackHeightAtElapsed_eq_segmentCurve
        hlam0 hlamHalf x0 p0 T, hstate]
  have hsubset : Finset.univ \ state.seenSource ⊆
      rightSourceInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        xR sample := by
    intro i hi
    have hfuture := href.2.2.1 i (Finset.mem_sdiff.mp hi).2
    simp only [rightSourceInitialPattern, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hq]
    simpa [sourceRawRemainingSetAt, sourceRawRemainingSet,
      FiniteSample.sourcePoint, FiniteSample.sourcePhase,
      FiniteSample.sourceSlope, mul_comm] using hfuture
  have hinitial :
      ((rightSourceInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        xR sample).card : ℝ) =
        rightBoundarySourceRemaining hlam0 hlamHalf x0 p0 T sample := by
    have hsame : rightSourceInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        xR sample =
      rightSourceInitialPattern
        (fun _completed ↦ rightBoundaryFrozenHeight lam xR
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T))
        xR sample := by
      ext i
      simp only [rightSourceInitialPattern, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rfl
    rw [hsame]
    simpa [xR] using
      (rightSourceInitialPattern_card_eq_rightBoundarySourceRemaining
        (n := n) hlam0 hlamHalf x0 p0 T sample hNoTie)
  have hremaining : rightBoundarySourceRemaining
      hlam0 hlamHalf x0 p0 T sample =
        ((Finset.univ \ state.seenSource).card : ℝ) := by
    rw [rightBoundarySourceRemaining,
      safeSourceRemainingAt_eq_unseen_card
        hlam0 hlamHalf x0 p0 T sample hNoTie, hstate]
  have hcard :
      (rightSourceInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        xR sample).card = (Finset.univ \ state.seenSource).card := by
    exact_mod_cast hinitial.trans hremaining
  rw [hsnapshotState]
  exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard])).symm

/-- Target analogue of `rightSourceInitialPattern_eq_boundaryUnseen`. -/
theorem rightTargetInitialPattern_eq_boundaryUnseen
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    rightTargetInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        (x0 + (T : ℝ)) sample =
      Finset.univ \ (revealedSnapshotState
        (sample.revealedSnapshotAtElapsed
          hlam0 hlamHalf x0 p0 T)).seenTarget := by
  classical
  let xR := x0 + (T : ℝ)
  obtain ⟨history, href, _hlen⟩ :=
    sample.exists_historyAtCoordinate_of_noFeedbackTies
      hlam0 hlamHalf (le_add_of_nonneg_right T.coe_nonneg) hNoTie
  let state := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have hstate : sample.feedbackStateAtElapsed
      hlam0 hlamHalf x0 p0 T = state := by
    have hx0R : x0 ≤ xR := le_add_of_nonneg_right T.coe_nonneg
    have hendpoint : (⟨xR - x0, sub_nonneg.mpr hx0R⟩ : ℝ≥0) = T := by
      apply NNReal.eq
      change xR - x0 = (T : ℝ)
      dsimp only [xR]
      ring
    have h := HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
      sample hlam0 hlamHalf hx0R history href
    rwa [hendpoint] at h
  have hsnapshotState : revealedSnapshotState
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) = state := by
    simp [revealedSnapshotState, FiniteSample.revealedSnapshotAtElapsed,
      revealedSnapshotFromState, hstate, FeedbackStepState.unpack_pack]
  have hq : actualRightTailFrozenHeight
      (n := n) hlam0 hlamHalf x0 p0 T sample =
        segmentCurve state.x state.p (state.slope lam) xR := by
    rw [actualRightTailFrozenHeight,
      rightBoundaryFrozenHeight_revealedSnapshotAtElapsed
        hlam0 hlamHalf x0 p0 T sample hNoTie,
      rightBoundaryHeight, safeFeedbackHeightAtElapsed,
      ite_eq_left hNoTie,
      sample.feedbackHeightAtElapsed_eq_segmentCurve
        hlam0 hlamHalf x0 p0 T, hstate]
  have hsubset : Finset.univ \ state.seenTarget ⊆
      rightTargetInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        xR sample := by
    intro j hj
    have hfuture := href.2.2.2 j (Finset.mem_sdiff.mp hj).2
    simp only [rightTargetInitialPattern, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hq]
    simpa [targetRawRemainingSetAt, targetRawRemainingSet,
      FiniteSample.targetPoint, FiniteSample.targetPhase,
      FiniteSample.targetSlope, mul_comm] using hfuture
  have hinitial :
      ((rightTargetInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        xR sample).card : ℝ) =
        rightBoundaryTargetRemaining hlam0 hlamHalf x0 p0 T sample := by
    have hsame : rightTargetInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        xR sample =
      rightTargetInitialPattern
        (fun _completed ↦ rightBoundaryFrozenHeight lam xR
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T))
        xR sample := by
      ext j
      simp only [rightTargetInitialPattern, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rfl
    rw [hsame]
    simpa [xR] using
      (rightTargetInitialPattern_card_eq_rightBoundaryTargetRemaining
        (n := n) hlam0 hlamHalf x0 p0 T sample hNoTie)
  have hremaining : rightBoundaryTargetRemaining
      hlam0 hlamHalf x0 p0 T sample =
        ((Finset.univ \ state.seenTarget).card : ℝ) := by
    rw [rightBoundaryTargetRemaining,
      safeTargetRemainingAt_eq_unseen_card
        hlam0 hlamHalf x0 p0 T sample hNoTie, hstate]
  have hcard :
      (rightTargetInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        xR sample).card = (Finset.univ \ state.seenTarget).card := by
    exact_mod_cast hinitial.trans hremaining
  rw [hsnapshotState]
  exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard])).symm

/-- Post-jump source remaining count equals the strict frozen-height count at the corresponding
coordinate.  This identity is purely finite and does not use a probabilistic premise. -/
theorem rightSourceRemainingAt_eq_strict_count
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) :
    rightSourceRemainingAt q xR t sample =
      ∑ i : Fin n, if xR + (t : ℝ) < sample.sourcePhase i (q sample)
        then 1 else 0 := by
  classical
  let initial := rightSourceInitialPattern q xR sample
  let crossed := Finset.univ.filter fun i : Fin n ↦
    rightSourceEventTime q xR i sample ≤ (t : WithTop ℝ≥0)
  have hcrossedInitial : crossed ⊆ initial := by
    intro i hi
    simp only [crossed, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [initial, rightSourceInitialPattern, Finset.mem_filter,
      Finset.mem_univ, true_and]
    unfold rightSourceEventTime at hi
    split_ifs at hi with hphase
    · exact hphase
    · exact (WithTop.not_top_le_coe t hi).elim
  have hset : initial \ crossed = Finset.univ.filter (fun i : Fin n ↦
      xR + (t : ℝ) < sample.sourcePhase i (q sample)) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      initial, rightSourceInitialPattern, crossed]
    unfold rightSourceEventTime
    by_cases hphase : xR < sample.sourcePhase i (q sample)
    · rw [ite_eq_left hphase]
      have hdiff : 0 ≤ sample.sourcePhase i (q sample) - xR :=
        (sub_pos.mpr hphase).le
      rw [WithTop.coe_le_coe, ← NNReal.coe_le_coe,
        Real.coe_toNNReal _ hdiff]
      constructor
      · intro h
        linarith [h.2]
      · intro h
        exact ⟨hphase, by linarith⟩
    · rw [ite_eq_right hphase]
      simp [hphase]
      linarith [t.coe_nonneg]
  have hcard : initial.card - crossed.card =
      (Finset.univ.filter (fun i : Fin n ↦
        xR + (t : ℝ) < sample.sourcePhase i (q sample))).card := by
    rw [← Finset.card_sdiff_of_subset hcrossedInitial, hset]
  unfold rightSourceRemainingAt rightSourceCount CountingProcess.finiteEventCountTop
  change (initial.card : ℝ) - (crossed.card : ℝ) = _
  rw [← Nat.cast_sub (Finset.card_le_card hcrossedInitial), hcard]
  simp

/-- Target analogue of `rightSourceRemainingAt_eq_strict_count`. -/
theorem rightTargetRemainingAt_eq_strict_count
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) :
    rightTargetRemainingAt q xR t sample =
      ∑ j : Fin n, if xR + (t : ℝ) < sample.targetPhase j (q sample)
        then 1 else 0 := by
  classical
  let initial := rightTargetInitialPattern q xR sample
  let crossed := Finset.univ.filter fun j : Fin n ↦
    rightTargetEventTime q xR j sample ≤ (t : WithTop ℝ≥0)
  have hcrossedInitial : crossed ⊆ initial := by
    intro j hj
    simp only [crossed, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [initial, rightTargetInitialPattern, Finset.mem_filter,
      Finset.mem_univ, true_and]
    unfold rightTargetEventTime at hj
    split_ifs at hj with hphase
    · exact hphase
    · exact (WithTop.not_top_le_coe t hj).elim
  have hset : initial \ crossed = Finset.univ.filter (fun j : Fin n ↦
      xR + (t : ℝ) < sample.targetPhase j (q sample)) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      initial, rightTargetInitialPattern, crossed]
    unfold rightTargetEventTime
    by_cases hphase : xR < sample.targetPhase j (q sample)
    · rw [ite_eq_left hphase]
      have hdiff : 0 ≤ sample.targetPhase j (q sample) - xR :=
        (sub_pos.mpr hphase).le
      rw [WithTop.coe_le_coe, ← NNReal.coe_le_coe,
        Real.coe_toNNReal _ hdiff]
      constructor
      · intro h
        linarith [h.2]
      · intro h
        exact ⟨hphase, by linarith⟩
    · rw [ite_eq_right hphase]
      simp [hphase]
      linarith [t.coe_nonneg]
  have hcard : initial.card - crossed.card =
      (Finset.univ.filter (fun j : Fin n ↦
        xR + (t : ℝ) < sample.targetPhase j (q sample))).card := by
    rw [← Finset.card_sdiff_of_subset hcrossedInitial, hset]
  unfold rightTargetRemainingAt rightTargetCount CountingProcess.finiteEventCountTop
  change (initial.card : ℝ) - (crossed.card : ℝ) = _
  rw [← Nat.cast_sub (Finset.card_le_card hcrossedInitial), hcard]
  simp

/-- At the actual boundary, the source post-jump numerator used by the stopping path is exactly
the snapshot-frozen source count used by the grid event. -/
theorem rightTailFrozenSourceCount_actual_eq_rightSourceRemainingAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    rightTailFrozenSourceCount lam (x0 + (T : ℝ))
        (x0 + (T : ℝ) + (t : ℝ))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample =
      rightSourceRemainingAt
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        (x0 + (T : ℝ)) t sample := by
  classical
  rw [rightSourceRemainingAt_eq_strict_count]
  unfold rightTailFrozenSourceCount rightBoundaryFrozenSourceCount
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hfuture : x0 + (T : ℝ) + (t : ℝ) <
      sample.sourcePhase i
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T sample)
  · have hiInitial : i ∈ rightSourceInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        (x0 + (T : ℝ)) sample := by
      simp only [rightSourceInitialPattern, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact (le_add_of_nonneg_right t.coe_nonneg).trans_lt hfuture
    rw [rightSourceInitialPattern_eq_boundaryUnseen
      hlam0 hlamHalf x0 p0 T sample hNoTie] at hiInitial
    have hiUnseen := (Finset.mem_sdiff.mp hiInitial).2
    have hfutureFrozen : x0 + (T : ℝ) + (t : ℝ) < sample.sourcePhase i
        (rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) := by
      simpa [actualRightTailFrozenHeight] using hfuture
    rw [ite_eq_left ⟨hiUnseen, hfutureFrozen⟩, ite_eq_left hfuture]
  · have hfutureFrozen : ¬x0 + (T : ℝ) + (t : ℝ) < sample.sourcePhase i
        (rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) := by
      simpa [actualRightTailFrozenHeight] using hfuture
    rw [ite_eq_right (fun h ↦ hfutureFrozen h.2), ite_eq_right hfuture]

/-- Target analogue of
`rightTailFrozenSourceCount_actual_eq_rightSourceRemainingAt`. -/
theorem rightTailFrozenTargetCount_actual_eq_rightTargetRemainingAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    rightTailFrozenTargetCount lam (x0 + (T : ℝ))
        (x0 + (T : ℝ) + (t : ℝ))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample =
      rightTargetRemainingAt
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        (x0 + (T : ℝ)) t sample := by
  classical
  rw [rightTargetRemainingAt_eq_strict_count]
  unfold rightTailFrozenTargetCount rightBoundaryFrozenTargetCount
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hfuture : x0 + (T : ℝ) + (t : ℝ) <
      sample.targetPhase j
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T sample)
  · have hjInitial : j ∈ rightTargetInitialPattern
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        (x0 + (T : ℝ)) sample := by
      simp only [rightTargetInitialPattern, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact (le_add_of_nonneg_right t.coe_nonneg).trans_lt hfuture
    rw [rightTargetInitialPattern_eq_boundaryUnseen
      hlam0 hlamHalf x0 p0 T sample hNoTie] at hjInitial
    have hjUnseen := (Finset.mem_sdiff.mp hjInitial).2
    have hfutureFrozen : x0 + (T : ℝ) + (t : ℝ) < sample.targetPhase j
        (rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) := by
      simpa [actualRightTailFrozenHeight] using hfuture
    rw [ite_eq_left ⟨hjUnseen, hfutureFrozen⟩, ite_eq_left hfuture]
  · have hfutureFrozen : ¬x0 + (T : ℝ) + (t : ℝ) < sample.targetPhase j
        (rightBoundaryFrozenHeight lam (x0 + (T : ℝ))
          (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T)) := by
      simpa [actualRightTailFrozenHeight] using hfuture
    rw [ite_eq_right (fun h ↦ hfutureFrozen h.2), ite_eq_right hfuture]

/-- On the interval where the algebraic source area is above the stabilization floor, the source
coordinate of the stopping path is the source rate tested by the frozen grid event. -/
theorem rightTailFrozenSourceRate_actual_eq_postStabilizedRate
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor : ℝ) (T t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (harea : areaFloor ≤ sourceUnclippedRemainingMass n
      (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T sample)
      (x0 + (T : ℝ) + (t : ℝ))) :
    rightTailFrozenSourceRate n lam (x0 + (T : ℝ))
        (x0 + (T : ℝ) + (t : ℝ))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample =
      rightSourcePostStabilizedRate n areaFloor
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        (x0 + (T : ℝ)) t sample := by
  rw [rightTailFrozenSourceRate, rightSourcePostStabilizedRate,
    rightSourceStabilizedArea, rightSourceArea, max_eq_right harea,
    rightTailFrozenSourceCount_actual_eq_rightSourceRemainingAt
      hlam0 hlamHalf x0 p0 T t sample hNoTie]
  rfl

/-- Target analogue of
`rightTailFrozenSourceRate_actual_eq_postStabilizedRate`. -/
theorem rightTailFrozenTargetRate_actual_eq_postStabilizedRate
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor : ℝ) (T t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (harea : areaFloor ≤ targetUnclippedRemainingMass n
      (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T sample)
      (x0 + (T : ℝ) + (t : ℝ))) :
    rightTailFrozenTargetRate n lam (x0 + (T : ℝ))
        (x0 + (T : ℝ) + (t : ℝ))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample =
      rightTargetPostStabilizedRate n areaFloor
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        (x0 + (T : ℝ)) t sample := by
  rw [rightTailFrozenTargetRate, rightTargetPostStabilizedRate,
    rightTargetStabilizedArea, rightTargetArea, max_eq_right harea,
    rightTailFrozenTargetCount_actual_eq_rightTargetRemainingAt
      hlam0 hlamHalf x0 p0 T t sample hNoTie]
  rfl

/-- A strict stopping failure before the elapsed horizon has a rational witness in the frozen
grid failure event.  Source and target stabilization are removed separately by their actual
algebraic area lower bounds. -/
theorem rightTailRateExitTime_lt_horizon_imp_mem_failureSet
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor c C : ℝ) (T H : ℝ≥0)
    (hfloor : 0 < areaFloor) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hSourceArea : ∀ t : ℝ≥0, t < H →
      areaFloor ≤ sourceUnclippedRemainingMass n
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ) + (t : ℝ)))
    (hTargetArea : ∀ t : ℝ≥0, t < H →
      areaFloor ≤ targetUnclippedRemainingMass n
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ) + (t : ℝ)))
    (hExit : rightTailRateExitTime n areaFloor c C
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
        (x0 + (T : ℝ)) H sample < (H : WithTop ℝ≥0)) :
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T, sample) ∈
      rightTailRateFailureSet n lam (x0 + (T : ℝ))
        (x0 + (T : ℝ) + (H : ℝ)) c C := by
  let q := actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T
  let xR := x0 + (T : ℝ)
  have hHit : MeasureTheory.hittingAfter
      (rightTailPostRatePath n areaFloor q xR)
      (rightTailRateBadSet c C) 0 sample < (H : WithTop ℝ≥0) := by
    rw [rightTailRateExitTime, min_lt_iff] at hExit
    exact hExit.resolve_right (lt_irrefl _)
  have hMem : sample ∈ {completed |
      MeasureTheory.hittingAfter
        (rightTailPostRatePath n areaFloor q xR)
        (rightTailRateBadSet c C) 0 completed < (H : WithTop ℝ≥0)} := hHit
  rw [CountingProcess.hittingAfter_zero_lt_set_eq_iUnion_rat_of_rightContinuous
    (rightTailPostRatePath_rightContinuous (n := n) hfloor xR)
    (isOpen_rightTailRateBadSet c C) H] at hMem
  rw [Set.mem_iUnion] at hMem
  obtain ⟨r, hr⟩ := hMem
  by_cases hrH : Real.toNNReal (r : ℝ) < H
  · rw [ite_eq_left hrH] at hr
    let t := Real.toNNReal (r : ℝ)
    change rightTailPostRatePath n areaFloor q xR t sample ∈
      rightTailRateBadSet c C at hr
    have hbad :
        rightSourcePostStabilizedRate n areaFloor q xR t sample ∉ Icc c C ∨
          rightTargetPostStabilizedRate n areaFloor q xR t sample ∉ Icc c C := by
      simpa only [rightTailPostRatePath, rightTailRateBadSet,
        rightTailRateRegion, Set.mem_compl_iff, Set.mem_prod, not_and_or] using hr
    have hsourceArea := hSourceArea t hrH
    have htargetArea := hTargetArea t hrH
    have hfrozen : rightTailFrozenRateBadAt n lam xR c C
        (xR + (t : ℝ))
        (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T) sample := by
      rcases hbad with hsource | htarget
      · exact Or.inl (by
          rw [rightTailFrozenSourceRate_actual_eq_postStabilizedRate
            hlam0 hlamHalf x0 p0 areaFloor T t sample hNoTie hsourceArea]
          exact hsource)
      · exact Or.inr (by
          rw [rightTailFrozenTargetRate_actual_eq_postStabilizedRate
            hlam0 hlamHalf x0 p0 areaFloor T t sample hNoTie htargetArea]
          exact htarget)
    have hcoord : xR + (t : ℝ) < xR + (H : ℝ) := by
      have htReal : (t : ℝ) < (H : ℝ) := by exact_mod_cast hrH
      linarith
    unfold rightTailRateFailureSet
    refine Set.mem_union_right _ ?_
    rw [Set.mem_iUnion]
    refine ⟨r, ?_⟩
    rw [ite_eq_left hcoord]
    exact hfrozen
  · rw [ite_eq_right hrH] at hr
    exact False.elim hr

/-- Actual strict stopping-failure event before the deterministic elapsed horizon. -/
def actualRightTailRateExitBeforeHorizonSet
    (n : ℕ) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor c C : ℝ) (T H : ℝ≥0) : Set (FiniteSample n) :=
  {sample | rightTailRateExitTime n areaFloor c C
    (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T)
    (x0 + (T : ℝ)) H sample < (H : WithTop ℝ≥0)}

/-- The actual strict stopping-failure event is ambient measurable. -/
theorem measurableSet_actualRightTailRateExitBeforeHorizonSet
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor c C : ℝ) (T H : ℝ≥0) (hfloor : 0 < areaFloor) :
    MeasurableSet (actualRightTailRateExitBeforeHorizonSet
      n hlam0 hlamHalf x0 p0 areaFloor c C T H) := by
  let q := actualRightTailFrozenHeight
    (n := n) hlam0 hlamHalf x0 p0 T
  have hq : Measurable q :=
    measurable_actualRightTailFrozenHeight
      (n := n) hlam0 hlamHalf x0 p0 T
  have hstopping : IsStoppingTime (rightTailUsualFiltration q hq
      (x0 + (T : ℝ))) (rightTailRateExitTime n areaFloor c C q
        (x0 + (T : ℝ)) H) :=
    rightTailRateExitTime_isStoppingTime
      (n := n) hq hfloor (x0 + (T : ℝ)) c C H
  have hlt := hstopping.measurableSet_lt H
  have hambient : MeasurableSet
      {sample | rightTailRateExitTime n areaFloor c C q
        (x0 + (T : ℝ)) H sample < (H : WithTop ℝ≥0)} :=
    ((rightTailUsualFiltration q hq (x0 + (T : ℝ))).le H) _ hlt
  simpa [actualRightTailRateExitBeforeHorizonSet, q] using hambient

/-- Pathwise component on which the stabilized stopping denominators agree with the algebraic
source and target areas throughout the strict horizon. -/
def actualRightTailStoppingGeometrySet
    (n : ℕ) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor : ℝ) (T H : ℝ≥0) : Set (FiniteSample n) :=
  {sample | sample.NoFeedbackTies lam x0 p0 ∧
    (∀ t : ℝ≥0, t < H →
      areaFloor ≤ sourceUnclippedRemainingMass n
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ) + (t : ℝ))) ∧
    ∀ t : ℝ≥0, t < H →
      areaFloor ≤ targetUnclippedRemainingMass n
        (actualRightTailFrozenHeight (n := n) hlam0 hlamHalf x0 p0 T sample)
        (x0 + (T : ℝ) + (t : ℝ))}

/-- Completed-sample preimage of the stronger rational grid failure event. -/
def actualRightTailGridFailureSet
    (n : ℕ) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 c C : ℝ) (T H : ℝ≥0) : Set (FiniteSample n) :=
  {sample |
    (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T, sample) ∈
      rightTailRateFailureSet n lam (x0 + (T : ℝ))
        (x0 + (T : ℝ) + (H : ℝ)) c C}

/-- The completed-sample grid failure is the measurable preimage of the joint frozen event. -/
theorem measurableSet_actualRightTailGridFailureSet
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 c C : ℝ) (T H : ℝ≥0) :
    MeasurableSet (actualRightTailGridFailureSet
      n hlam0 hlamHalf x0 p0 c C T H) := by
  have hpair : Measurable fun sample : FiniteSample n ↦
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 T, sample) :=
    (measurable_revealedSnapshotAtElapsed
      (n := n) hlam0 hlamHalf x0 p0 T).prodMk measurable_id
  exact (measurableSet_rightTailRateFailureSet n lam (x0 + (T : ℝ))
    (x0 + (T : ℝ) + (H : ℝ)) c C).preimage hpair

/-- Precise paper-event inclusion: on the no-tie positive-area component, strict stopping before
`xR + H` is contained in the stronger endpoint-plus-rational grid failure event. -/
theorem actualRightTailRateExitBeforeHorizonSet_inter_geometry_subset_gridFailure
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor c C : ℝ) (T H : ℝ≥0) (hfloor : 0 < areaFloor) :
    actualRightTailRateExitBeforeHorizonSet n hlam0 hlamHalf
        x0 p0 areaFloor c C T H ∩
      actualRightTailStoppingGeometrySet n hlam0 hlamHalf
        x0 p0 areaFloor T H ⊆
      actualRightTailGridFailureSet n hlam0 hlamHalf x0 p0 c C T H := by
  intro sample hsample
  exact rightTailRateExitTime_lt_horizon_imp_mem_failureSet
    (n := n) hlam0 hlamHalf x0 p0 areaFloor c C T H hfloor sample
      hsample.2.1 hsample.2.2.1 hsample.2.2.2 hsample.1

/-- The actual self-integrand is exactly the indicator of the completed-sample grid preimage. -/
theorem actualRightTailRateFailure_eq_gridFailureIndicator
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 c C : ℝ) (T H : ℝ≥0) (sample : FiniteSample n) :
    actualRightTailRateFailure n hlam0 hlamHalf x0 p0 T
        (x0 + (T : ℝ) + (H : ℝ)) c C sample =
      (actualRightTailGridFailureSet n hlam0 hlamHalf
        x0 p0 c C T H).indicator 1 sample := by
  rfl

/-- Pointwise paper-event comparison on the stopping geometry component. -/
theorem indicator_actualRightTailRateExitBeforeHorizonSet_le_actual_failure
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor c C : ℝ) (T H : ℝ≥0) (hfloor : 0 < areaFloor)
    (sample : FiniteSample n)
    (hgeometry : sample ∈ actualRightTailStoppingGeometrySet
      n hlam0 hlamHalf x0 p0 areaFloor T H) :
    (actualRightTailRateExitBeforeHorizonSet n hlam0 hlamHalf
        x0 p0 areaFloor c C T H).indicator 1 sample ≤
      actualRightTailRateFailure n hlam0 hlamHalf x0 p0 T
        (x0 + (T : ℝ) + (H : ℝ)) c C sample := by
  rw [actualRightTailRateFailure_eq_gridFailureIndicator]
  by_cases hExit : sample ∈ actualRightTailRateExitBeforeHorizonSet
      n hlam0 hlamHalf x0 p0 areaFloor c C T H
  · have hGrid : sample ∈ actualRightTailGridFailureSet
        n hlam0 hlamHalf x0 p0 c C T H :=
      actualRightTailRateExitBeforeHorizonSet_inter_geometry_subset_gridFailure
        hlam0 hlamHalf x0 p0 areaFloor c C T H hfloor ⟨hExit, hgeometry⟩
    simp [Set.indicator_of_mem hExit, Set.indicator_of_mem hGrid]
  · rw [Set.indicator_of_notMem hExit]
    by_cases hGrid : sample ∈ actualRightTailGridFailureSet
        n hlam0 hlamHalf x0 p0 c C T H
    · rw [Set.indicator_of_mem hGrid]
      norm_num
    · rw [Set.indicator_of_notMem hGrid]

private theorem condExp_le_on_measurableSet_of_indicator_le
    {Ω : Type*} {mΩ m : MeasurableSpace Ω} {μ : @Measure Ω mΩ}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) {G : Set Ω}
    (hG : MeasurableSet[m] G) {f g b : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hlocal : G.indicator f ≤ g)
    (hbound : ∀ᵐ omega ∂μ, omega ∈ G → μ[g | m] omega ≤ b omega) :
    ∀ᵐ omega ∂μ, omega ∈ G → μ[f | m] omega ≤ b omega := by
  have hlocalInt : Integrable (G.indicator f) μ :=
    hf.indicator (hm G hG)
  have hmono : μ[G.indicator f | m] ≤ᵐ[μ] μ[g | m] :=
    condExp_mono hlocalInt hg (Eventually.of_forall hlocal)
  have hpull : μ[G.indicator f | m] =ᵐ[μ] G.indicator (μ[f | m]) :=
    condExp_indicator hf hG
  filter_upwards [hmono, hpull, hbound] with omega hmonoOmega hpullOmega hboundOmega
  intro homegaG
  have hpullAt : μ[G.indicator f | m] omega = μ[f | m] omega := by
    simpa [Set.indicator_of_mem homegaG] using hpullOmega
  calc
    μ[f | m] omega = μ[G.indicator f | m] omega := hpullAt.symm
    _ ≤ μ[g | m] omega := hmonoOmega
    _ ≤ b omega := hboundOmega homegaG

/-- Localized actual `(1.36e)` bound.  On an `F_T`-measurable component `G`, the
strict stopping-failure indicator has conditional expectation bounded by the explicit
source-plus-target polynomial envelope. -/
theorem condExp_actualRightTailRateExitBeforeHorizon_le_epsilon_on_set
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor c C : ℝ) (T H : ℝ≥0) (hT0 : 0 < T)
    (hfloor : 0 < areaFloor) (G : Set (FiniteSample n))
    (hG : MeasurableSet[usualRevealedFiltration (n := n)
      hlam0 hlamHalf x0 p0 T] G)
    (hgeometry : ∀ sample ∈ G, sample ∈ actualRightTailStoppingGeometrySet
      n hlam0 hlamHalf x0 p0 areaFloor T H)
    (hgood : ∀ sample ∈ G, RightTailBoundaryVCGood n lam x0 p0 T
      (x0 + (T : ℝ) + (H : ℝ)) c C sample) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)), sample ∈ G →
      (finiteSampleLaw n : Measure (FiniteSample n))[
        (actualRightTailRateExitBeforeHorizonSet n hlam0 hlamHalf
          x0 p0 areaFloor c C T H).indicator (fun _ ↦ (1 : ℝ)) |
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] sample ≤
      rightTailRateFailureEpsilon
        (rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample)
        (rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample) := by
  let E := actualRightTailRateExitBeforeHorizonSet n hlam0 hlamHalf
    x0 p0 areaFloor c C T H
  let IE : FiniteSample n → ℝ := E.indicator fun _ ↦ 1
  let Y := actualRightTailRateFailure n hlam0 hlamHalf x0 p0 T
    (x0 + (T : ℝ) + (H : ℝ)) c C
  have hm : usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T ≤
      (inferInstance : MeasurableSpace (FiniteSample n)) := by
    exact (usualRevealedFiltration
      (n := n) hlam0 hlamHalf x0 p0).le T
  have hE : @MeasurableSet (FiniteSample n)
      (inferInstance : MeasurableSpace (FiniteSample n)) E := by
    exact measurableSet_actualRightTailRateExitBeforeHorizonSet
      (n := n) hlam0 hlamHalf x0 p0 areaFloor c C T H hfloor
  have hIEint : Integrable IE
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
    exact (integrable_const (1 : ℝ)).indicator hE
  have hYint : Integrable Y
      (finiteSampleLaw n : Measure (FiniteSample n)) := by
    have hGridMeas := measurableSet_actualRightTailGridFailureSet
      (n := n) hlam0 hlamHalf x0 p0 c C T H
    have hGridInt : Integrable
        ((actualRightTailGridFailureSet n hlam0 hlamHalf
          x0 p0 c C T H).indicator fun _ ↦ (1 : ℝ))
        (finiteSampleLaw n : Measure (FiniteSample n)) :=
      (integrable_const (1 : ℝ)).indicator hGridMeas
    have hYeq : Y = (actualRightTailGridFailureSet n hlam0 hlamHalf
        x0 p0 c C T H).indicator fun _ ↦ (1 : ℝ) := by
      funext sample
      exact actualRightTailRateFailure_eq_gridFailureIndicator
        hlam0 hlamHalf x0 p0 c C T H sample
    rw [hYeq]
    exact hGridInt
  have hlocal : G.indicator IE ≤ Y := by
    intro sample
    by_cases hsampleG : sample ∈ G
    · rw [Set.indicator_of_mem hsampleG]
      exact indicator_actualRightTailRateExitBeforeHorizonSet_le_actual_failure
        (n := n) hlam0 hlamHalf x0 p0 areaFloor c C T H hfloor sample
          (hgeometry sample hsampleG)
    · rw [Set.indicator_of_notMem hsampleG]
      dsimp only [Y]
      rw [actualRightTailRateFailure_eq_gridFailureIndicator]
      by_cases hGrid : sample ∈ actualRightTailGridFailureSet
          n hlam0 hlamHalf x0 p0 c C T H <;> simp [hGrid]
  have hxStar : x0 + (T : ℝ) ≤ x0 + (T : ℝ) + (H : ℝ) := by
    linarith [H.coe_nonneg]
  have hgrid := condExp_rightTailRateFailure_le_epsilon_on_boundaryGood
    (n := n) hn hlam0 hlamHalf x0 p0 T hT0
      (x0 + (T : ℝ) + (H : ℝ)) c C hxStar
  have hgridOnG : ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      sample ∈ G →
      (finiteSampleLaw n : Measure (FiniteSample n))[
        Y | usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] sample ≤
        rightTailRateFailureEpsilon
          (rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample)
          (rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample) := by
    filter_upwards [hgrid] with sample hgridSample
    intro hsampleG
    exact hgridSample (hgeometry sample hsampleG).1 (hgood sample hsampleG)
  have hlocalized := condExp_le_on_measurableSet_of_indicator_le
    (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
      hm hG hIEint hYint hlocal hgridOnG
  simpa [E, IE, Y] using hlocalized

/-- Deterministic scaling-envelope form of the localized actual stopping-failure bound. -/
theorem condExp_actualRightTailRateExitBeforeHorizon_le_scalingEnvelope_on_set
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor c C : ℝ) (T H : ℝ≥0) (hT0 : 0 < T)
    (hfloor : 0 < areaFloor) (A density : ℝ)
    (hscale : 1 ≤ density * A * Real.sqrt n) (G : Set (FiniteSample n))
    (hG : MeasurableSet[usualRevealedFiltration (n := n)
      hlam0 hlamHalf x0 p0 T] G)
    (hgeometry : ∀ sample ∈ G, sample ∈ actualRightTailStoppingGeometrySet
      n hlam0 hlamHalf x0 p0 areaFloor T H)
    (hgood : ∀ sample ∈ G, RightTailBoundaryVCGood n lam x0 p0 T
      (x0 + (T : ℝ) + (H : ℝ)) c C sample)
    (hSource : ∀ sample ∈ G, density * A * Real.sqrt n ≤
      rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample)
    (hTarget : ∀ sample ∈ G, density * A * Real.sqrt n ≤
      rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)), sample ∈ G →
      (finiteSampleLaw n : Measure (FiniteSample n))[
        (actualRightTailRateExitBeforeHorizonSet n hlam0 hlamHalf
          x0 p0 areaFloor c C T H).indicator (fun _ ↦ (1 : ℝ)) |
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] sample ≤
      512 * ((density * A * Real.sqrt n)⁻¹) ^ 12 := by
  filter_upwards [condExp_actualRightTailRateExitBeforeHorizon_le_epsilon_on_set
    (n := n) hn hlam0 hlamHalf x0 p0 areaFloor c C T H hT0 hfloor
      G hG hgeometry hgood] with sample hsample
  intro hsampleG
  exact (hsample hsampleG).trans
    (rightTailRateFailureEpsilon_le_scalingEnvelope
      (rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample)
      (rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample)
      n A density hscale (hSource sample hsampleG) (hTarget sample hsampleG))

/-- Paper-ready localized endpoint: the finite-`n` conditional stopping-failure bound comes
with a deterministic envelope that tends to zero. -/
theorem condExp_actualRightTailRateExitBeforeHorizon_le_scalingEnvelope_with_tendsto
    (hn : 0 < n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 areaFloor c C : ℝ) (T H : ℝ≥0) (hT0 : 0 < T)
    (hfloor : 0 < areaFloor) (A density : ℝ)
    (hscale : 1 ≤ density * A * Real.sqrt n) (G : Set (FiniteSample n))
    (hG : MeasurableSet[usualRevealedFiltration (n := n)
      hlam0 hlamHalf x0 p0 T] G)
    (hgeometry : ∀ sample ∈ G, sample ∈ actualRightTailStoppingGeometrySet
      n hlam0 hlamHalf x0 p0 areaFloor T H)
    (hgood : ∀ sample ∈ G, RightTailBoundaryVCGood n lam x0 p0 T
      (x0 + (T : ℝ) + (H : ℝ)) c C sample)
    (hSource : ∀ sample ∈ G, density * A * Real.sqrt n ≤
      rightTailBoundarySourceLabelCount hlam0 hlamHalf x0 p0 T sample)
    (hTarget : ∀ sample ∈ G, density * A * Real.sqrt n ≤
      rightTailBoundaryTargetLabelCount hlam0 hlamHalf x0 p0 T sample) :
    (∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)), sample ∈ G →
      (finiteSampleLaw n : Measure (FiniteSample n))[
        (actualRightTailRateExitBeforeHorizonSet n hlam0 hlamHalf
          x0 p0 areaFloor c C T H).indicator (fun _ ↦ (1 : ℝ)) |
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 T] sample ≤
      512 * ((density * A * Real.sqrt n)⁻¹) ^ 12) ∧
    Tendsto (fun k : ℕ ↦ 512 * ((density * A * Real.sqrt k)⁻¹) ^ 12)
      atTop (nhds 0) := by
  exact ⟨condExp_actualRightTailRateExitBeforeHorizon_le_scalingEnvelope_on_set
    (n := n) hn hlam0 hlamHalf x0 p0 areaFloor c C T H hT0 hfloor
      A density hscale G hG hgeometry hgood hSource hTarget,
    tendsto_rightTailRateFailureScalingEnvelope A density⟩

end FiniteSample

end OTSelector
