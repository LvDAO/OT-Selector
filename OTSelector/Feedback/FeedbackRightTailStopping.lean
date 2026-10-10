import OTSelector.Feedback.FeedbackRightBoundary
import OTSelector.Probability.CountingProcess.ContinuousOpenHitting

/-!
# Actual stopped rate control on a frozen right tail

At a deterministic right boundary the graph height is frozen.  The future source and target
crossings are therefore finite-event counting processes.  Their natural filtration starts by
revealing the boundary height and the two full remaining-label patterns, then reveals the two
future counts.  We take its usual augmentation, define the first failure of a right-continuous
post-jump stabilized rate path, and transfer strict survival to the predictable strict-left rates.

This is a stopping theorem, not a tail-probability theorem.  The latter still needs the
finite-history-section to revealed-filtration conditional-law bridge.
-/

open Filter MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Natural right-tail information -/

/-- Boundary height, full source/target remaining patterns, and attained future counts. -/
abbrev RightTailSnapshot (n : ℕ) :=
  ℝ × ((Finset (Fin n) × Finset (Fin n)) × (ℕ × ℕ))

noncomputable instance instOpensMeasurableRightTailSnapshot :
    OpensMeasurableSpace (RightTailSnapshot n) := by
  let : SecondCountableTopologyEither
      ℝ ((Finset (Fin n) × Finset (Fin n)) × (ℕ × ℕ)) :=
    secondCountableTopologyEither_of_left _ _
  infer_instance

noncomputable instance instBorelSpaceRightTailSnapshot :
    BorelSpace (RightTailSnapshot n) := by
  exact ⟨le_antisymm prod_le_borel_prod OpensMeasurableSpace.borel_le⟩

noncomputable def rightTailSnapshot
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) : RightTailSnapshot n :=
  (q sample,
    ((rightSourceInitialPattern q xR sample, rightTargetInitialPattern q xR sample),
      (rightSourceCount q xR t sample, rightTargetCount q xR t sample)))

theorem measurable_rightTailSnapshot
    {q : FiniteSample n → ℝ} (hq : Measurable q) (xR : ℝ) (t : ℝ≥0) :
    Measurable (rightTailSnapshot q xR t) := by
  exact hq.prodMk
    ((measurable_rightSourceInitialPattern hq xR).prodMk
      (measurable_rightTargetInitialPattern hq xR) |>.prodMk
        ((measurable_rightSourceCount hq xR t).prodMk
          (measurable_rightTargetCount hq xR t)))

noncomputable def rightTailRawFiltration
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)) :=
  Filtration.natural (rightTailSnapshot q xR)
    (fun t ↦ (measurable_rightTailSnapshot hq xR t).stronglyMeasurable)

noncomputable def rightTailUsualFiltration
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)) :=
  usualAugmentation (rightTailRawFiltration q hq xR)
    (finiteSampleLaw n : Measure (FiniteSample n))

theorem rightTailUsualFiltration_isRightContinuous
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    Filtration.IsRightContinuous (rightTailUsualFiltration q hq xR) :=
  usualAugmentation_isRightContinuous (rightTailRawFiltration q hq xR)
    (finiteSampleLaw n : Measure (FiniteSample n))

private theorem rightTailSnapshot_stronglyAdapted_raw
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    StronglyAdapted (rightTailRawFiltration q hq xR) (rightTailSnapshot q xR) :=
  Filtration.stronglyAdapted_natural
    (fun t ↦ (measurable_rightTailSnapshot hq xR t).stronglyMeasurable)

theorem rightTailHeight_stronglyAdapted
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    StronglyAdapted (rightTailUsualFiltration q hq xR) (fun _ ↦ q) := by
  intro t
  have hsnap := rightTailSnapshot_stronglyAdapted_raw q hq xR t
  have hraw : StronglyMeasurable[rightTailRawFiltration q hq xR t] q := by
    exact (measurable_fst.comp hsnap.measurable).stronglyMeasurable
  exact hraw.mono (le_usualAugmentation
    (rightTailRawFiltration q hq xR)
    (finiteSampleLaw n : Measure (FiniteSample n)) t)

theorem rightSourceCount_stronglyAdapted
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    StronglyAdapted (rightTailUsualFiltration q hq xR)
      (fun t sample ↦ (rightSourceCount q xR t sample : ℝ)) := by
  intro t
  have hsnap := rightTailSnapshot_stronglyAdapted_raw q hq xR t
  have hproj : Measurable fun z : RightTailSnapshot n ↦ (z.2.2.1 : ℝ) := by fun_prop
  have hraw : StronglyMeasurable[rightTailRawFiltration q hq xR t]
      (fun sample : FiniteSample n ↦ (rightSourceCount q xR t sample : ℝ)) := by
    exact (hproj.comp hsnap.measurable).stronglyMeasurable
  exact hraw.mono (le_usualAugmentation
    (rightTailRawFiltration q hq xR)
    (finiteSampleLaw n : Measure (FiniteSample n)) t)

theorem rightTargetCount_stronglyAdapted
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    StronglyAdapted (rightTailUsualFiltration q hq xR)
      (fun t sample ↦ (rightTargetCount q xR t sample : ℝ)) := by
  intro t
  have hsnap := rightTailSnapshot_stronglyAdapted_raw q hq xR t
  have hproj : Measurable fun z : RightTailSnapshot n ↦ (z.2.2.2 : ℝ) := by fun_prop
  have hraw : StronglyMeasurable[rightTailRawFiltration q hq xR t]
      (fun sample : FiniteSample n ↦ (rightTargetCount q xR t sample : ℝ)) := by
    exact (hproj.comp hsnap.measurable).stronglyMeasurable
  exact hraw.mono (le_usualAugmentation
    (rightTailRawFiltration q hq xR)
    (finiteSampleLaw n : Measure (FiniteSample n)) t)

private theorem rightSourceInitialCount_stronglyAdapted
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    StronglyAdapted (rightTailUsualFiltration q hq xR)
      (fun _ sample ↦ ((rightSourceInitialPattern q xR sample).card : ℝ)) := by
  intro t
  have hsnap := rightTailSnapshot_stronglyAdapted_raw q hq xR t
  have hproj : Measurable fun z : RightTailSnapshot n ↦ (z.2.1.1.card : ℝ) := by fun_prop
  have hraw : StronglyMeasurable[rightTailRawFiltration q hq xR t]
      (fun sample : FiniteSample n ↦ ((rightSourceInitialPattern q xR sample).card : ℝ)) := by
    exact (hproj.comp hsnap.measurable).stronglyMeasurable
  exact hraw.mono (le_usualAugmentation
    (rightTailRawFiltration q hq xR)
    (finiteSampleLaw n : Measure (FiniteSample n)) t)

private theorem rightTargetInitialCount_stronglyAdapted
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    StronglyAdapted (rightTailUsualFiltration q hq xR)
      (fun _ sample ↦ ((rightTargetInitialPattern q xR sample).card : ℝ)) := by
  intro t
  have hsnap := rightTailSnapshot_stronglyAdapted_raw q hq xR t
  have hproj : Measurable fun z : RightTailSnapshot n ↦ (z.2.1.2.card : ℝ) := by fun_prop
  have hraw : StronglyMeasurable[rightTailRawFiltration q hq xR t]
      (fun sample : FiniteSample n ↦ ((rightTargetInitialPattern q xR sample).card : ℝ)) := by
    exact (hproj.comp hsnap.measurable).stronglyMeasurable
  exact hraw.mono (le_usualAugmentation
    (rightTailRawFiltration q hq xR)
    (finiteSampleLaw n : Measure (FiniteSample n)) t)

/-! ## Post-jump and strict-left rates -/

noncomputable def rightSourceRemainingAt
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) : ℝ :=
  (rightSourceInitialPattern q xR sample).card - rightSourceCount q xR t sample

noncomputable def rightTargetRemainingAt
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) : ℝ :=
  (rightTargetInitialPattern q xR sample).card - rightTargetCount q xR t sample

/-- Remaining labels at the strict-left state used by a predictable rate. -/
noncomputable def rightSourceRemainingBefore
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) : ℝ :=
  (rightSourceInitialPattern q xR sample).card -
    (CountingProcess.countBefore (rightSourceCount q xR) t sample : ℝ)

noncomputable def rightTargetRemainingBefore
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) : ℝ :=
  (rightTargetInitialPattern q xR sample).card -
    (CountingProcess.countBefore (rightTargetCount q xR) t sample : ℝ)

/-- Algebraic source complement area for the frozen-height continuation. -/
noncomputable def rightSourceArea
    (n : ℕ) (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) : ℝ :=
  sourceUnclippedRemainingMass n (q sample) (xR + (t : ℝ))

/-- Algebraic target complement area for the frozen-height continuation. -/
noncomputable def rightTargetArea
    (n : ℕ) (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0)
    (sample : FiniteSample n) : ℝ :=
  targetUnclippedRemainingMass n (q sample) (xR + (t : ℝ))

noncomputable def rightSourceStabilizedArea
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  max areaFloor (rightSourceArea n q xR t sample)

noncomputable def rightTargetStabilizedArea
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  max areaFloor (rightTargetArea n q xR t sample)

noncomputable def rightSourcePostStabilizedRate
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightSourceRemainingAt q xR t sample /
    rightSourceStabilizedArea n areaFloor q xR t sample

noncomputable def rightTargetPostStabilizedRate
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightTargetRemainingAt q xR t sample /
    rightTargetStabilizedArea n areaFloor q xR t sample

/-- Predictable strict-left source rate, with a positive denominator stabilization. -/
noncomputable def rightSourceStrictStabilizedRate
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightSourceRemainingBefore q xR t sample /
    rightSourceStabilizedArea n areaFloor q xR t sample

/-- Predictable strict-left target rate, with a positive denominator stabilization. -/
noncomputable def rightTargetStrictStabilizedRate
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightTargetRemainingBefore q xR t sample /
    rightTargetStabilizedArea n areaFloor q xR t sample

/-- The genuine algebraic strict-left source rate.  It agrees with the stabilized rate whenever
the complement area is at least `areaFloor`. -/
noncomputable def rightSourceStrictRate
    (n : ℕ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightSourceRemainingBefore q xR t sample / rightSourceArea n q xR t sample

noncomputable def rightTargetStrictRate
    (n : ℕ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightTargetRemainingBefore q xR t sample / rightTargetArea n q xR t sample

noncomputable def rightTailPostRatePath
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ × ℝ :=
  (rightSourcePostStabilizedRate n areaFloor q xR t sample,
    rightTargetPostStabilizedRate n areaFloor q xR t sample)

noncomputable def rightTailStrictStabilizedRatePath
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ × ℝ :=
  (rightSourceStrictStabilizedRate n areaFloor q xR t sample,
    rightTargetStrictStabilizedRate n areaFloor q xR t sample)

theorem rightTailPostRatePath_adapted
    {q : FiniteSample n → ℝ} (hq : Measurable q) (areaFloor xR : ℝ) :
    Adapted (rightTailUsualFiltration q hq xR)
      (rightTailPostRatePath n areaFloor q xR) := by
  intro t
  have hqT := rightTailHeight_stronglyAdapted q hq xR t
  have hsInit := rightSourceInitialCount_stronglyAdapted q hq xR t
  have htInit := rightTargetInitialCount_stronglyAdapted q hq xR t
  have hsCount := rightSourceCount_stronglyAdapted q hq xR t
  have htCount := rightTargetCount_stronglyAdapted q hq xR t
  have hqHalf : StronglyMeasurable[rightTailUsualFiltration q hq xR t]
      (fun sample ↦ q sample / 2) :=
    hqT.div stronglyMeasurable_const
  have hsAreaBase : StronglyMeasurable[rightTailUsualFiltration q hq xR t]
      (rightSourceArea n q xR t) := by
    unfold rightSourceArea sourceUnclippedRemainingMass
    exact stronglyMeasurable_const.sub stronglyMeasurable_const |>.add hqHalf
  have hsArea : StronglyMeasurable[rightTailUsualFiltration q hq xR t]
      (rightSourceStabilizedArea n areaFloor q xR t) := by
    unfold rightSourceStabilizedArea
    exact ((continuous_fst.max continuous_snd).measurable.comp
      (stronglyMeasurable_const.prodMk hsAreaBase).measurable).stronglyMeasurable
  have htAreaBase : StronglyMeasurable[rightTailUsualFiltration q hq xR t]
      (rightTargetArea n q xR t) := by
    unfold rightTargetArea targetUnclippedRemainingMass
    exact stronglyMeasurable_const.sub stronglyMeasurable_const |>.sub
      ((hqT.const_mul 3).div stronglyMeasurable_const)
  have htArea : StronglyMeasurable[rightTailUsualFiltration q hq xR t]
      (rightTargetStabilizedArea n areaFloor q xR t) := by
    unfold rightTargetStabilizedArea
    exact ((continuous_fst.max continuous_snd).measurable.comp
      (stronglyMeasurable_const.prodMk htAreaBase).measurable).stronglyMeasurable
  have hsRate := (hsInit.sub hsCount).div hsArea
  have htRate := (htInit.sub htCount).div htArea
  exact (hsRate.prodMk htRate).measurable

theorem rightTailPostRatePath_rightContinuous
    {q : FiniteSample n → ℝ} {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (xR : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s ↦ rightTailPostRatePath n areaFloor q xR s sample) (Ici t) t := by
  have hsCount := CountingProcess.finiteEventCountTop_rightContinuous
    (fun i : Fin n ↦ rightSourceEventTime q xR i) sample t
  have htCount := CountingProcess.finiteEventCountTop_rightContinuous
    (fun j : Fin n ↦ rightTargetEventTime q xR j) sample t
  have hsNum : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ rightSourceRemainingAt q xR s sample) (Ici t) t := by
    exact continuousWithinAt_const.sub hsCount
  have htNum : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ rightTargetRemainingAt q xR s sample) (Ici t) t := by
    exact continuousWithinAt_const.sub htCount
  have hsArea : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ rightSourceStabilizedArea n areaFloor q xR s sample)
      (Ici t) t := by
    unfold rightSourceStabilizedArea rightSourceArea sourceUnclippedRemainingMass
    fun_prop
  have htArea : ContinuousWithinAt
      (fun s : ℝ≥0 ↦ rightTargetStabilizedArea n areaFloor q xR s sample)
      (Ici t) t := by
    unfold rightTargetStabilizedArea rightTargetArea targetUnclippedRemainingMass
    fun_prop
  have hs0 : rightSourceStabilizedArea n areaFloor q xR t sample ≠ 0 :=
    ne_of_gt (hfloor.trans_le (le_max_left _ _))
  have ht0 : rightTargetStabilizedArea n areaFloor q xR t sample ≠ 0 :=
    ne_of_gt (hfloor.trans_le (le_max_left _ _))
  exact (hsNum.div hsArea hs0).prodMk_nhds (htNum.div htArea ht0)

private theorem rightSourcePostRate_tendsto_strict
    {q : FiniteSample n → ℝ} {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (xR : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    Tendsto (fun s ↦ rightSourcePostStabilizedRate n areaFloor q xR s sample)
      (nhdsWithin t (Iio t : Set ℝ≥0))
      (nhds (rightSourceStrictStabilizedRate n areaFloor q xR t sample)) := by
  have hcount : Tendsto
      (fun s ↦ (rightSourceCount q xR s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (CountingProcess.countBefore (rightSourceCount q xR) t sample : ℝ)) := by
    change Tendsto
      (fun s ↦ (CountingProcess.finiteEventCountTop
        (fun i : Fin n ↦ rightSourceEventTime q xR i) s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (CountingProcess.countBefore
        (fun s sample' ↦ CountingProcess.finiteEventCountTop
          (fun i : Fin n ↦ rightSourceEventTime q xR i) s sample')
        t sample : ℝ))
    exact CountingProcess.finiteEventCountTop_tendsto_countBefore_nhdsWithin_Iio
      (fun i : Fin n ↦ rightSourceEventTime q xR i) sample t
  have hnum : Tendsto
      (fun s : ℝ≥0 ↦ ((rightSourceInitialPattern q xR sample).card : ℝ) -
        (rightSourceCount q xR s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (((rightSourceInitialPattern q xR sample).card : ℝ) -
        (CountingProcess.countBefore (rightSourceCount q xR) t sample : ℝ))) :=
    tendsto_const_nhds.sub hcount
  have harea : Tendsto
      (fun s : ℝ≥0 ↦ rightSourceStabilizedArea n areaFloor q xR s sample)
      (nhdsWithin t (Iio t))
      (nhds (rightSourceStabilizedArea n areaFloor q xR t sample)) := by
    exact (show Continuous
        (fun s : ℝ≥0 ↦ rightSourceStabilizedArea n areaFloor q xR s sample) by
      unfold rightSourceStabilizedArea rightSourceArea sourceUnclippedRemainingMass
      fun_prop).continuousAt.mono_left inf_le_left
  have harea0 : rightSourceStabilizedArea n areaFloor q xR t sample ≠ 0 :=
    ne_of_gt (hfloor.trans_le (le_max_left _ _))
  refine Tendsto.congr' (Eventually.of_forall fun s ↦ ?_)
    (hnum.div harea harea0)
  simp only [Pi.div_apply, rightSourcePostStabilizedRate,
    rightSourceRemainingAt]

private theorem rightTargetPostRate_tendsto_strict
    {q : FiniteSample n → ℝ} {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (xR : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    Tendsto (fun s ↦ rightTargetPostStabilizedRate n areaFloor q xR s sample)
      (nhdsWithin t (Iio t : Set ℝ≥0))
      (nhds (rightTargetStrictStabilizedRate n areaFloor q xR t sample)) := by
  have hcount : Tendsto
      (fun s ↦ (rightTargetCount q xR s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (CountingProcess.countBefore (rightTargetCount q xR) t sample : ℝ)) := by
    change Tendsto
      (fun s ↦ (CountingProcess.finiteEventCountTop
        (fun j : Fin n ↦ rightTargetEventTime q xR j) s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (CountingProcess.countBefore
        (fun s sample' ↦ CountingProcess.finiteEventCountTop
          (fun j : Fin n ↦ rightTargetEventTime q xR j) s sample')
        t sample : ℝ))
    exact CountingProcess.finiteEventCountTop_tendsto_countBefore_nhdsWithin_Iio
      (fun j : Fin n ↦ rightTargetEventTime q xR j) sample t
  have hnum : Tendsto
      (fun s : ℝ≥0 ↦ ((rightTargetInitialPattern q xR sample).card : ℝ) -
        (rightTargetCount q xR s sample : ℝ))
      (nhdsWithin t (Iio t))
      (nhds (((rightTargetInitialPattern q xR sample).card : ℝ) -
        (CountingProcess.countBefore (rightTargetCount q xR) t sample : ℝ))) :=
    tendsto_const_nhds.sub hcount
  have harea : Tendsto
      (fun s : ℝ≥0 ↦ rightTargetStabilizedArea n areaFloor q xR s sample)
      (nhdsWithin t (Iio t))
      (nhds (rightTargetStabilizedArea n areaFloor q xR t sample)) := by
    exact (show Continuous
        (fun s : ℝ≥0 ↦ rightTargetStabilizedArea n areaFloor q xR s sample) by
      unfold rightTargetStabilizedArea rightTargetArea targetUnclippedRemainingMass
      fun_prop).continuousAt.mono_left inf_le_left
  have harea0 : rightTargetStabilizedArea n areaFloor q xR t sample ≠ 0 :=
    ne_of_gt (hfloor.trans_le (le_max_left _ _))
  refine Tendsto.congr' (Eventually.of_forall fun s ↦ ?_)
    (hnum.div harea harea0)
  simp only [Pi.div_apply, rightTargetPostStabilizedRate,
    rightTargetRemainingAt]

theorem rightTailPostRatePath_tendsto_strict
    {q : FiniteSample n → ℝ} {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (xR : ℝ) (sample : FiniteSample n) (t : ℝ≥0) :
    Tendsto (fun s ↦ rightTailPostRatePath n areaFloor q xR s sample)
      (nhdsWithin t (Iio t : Set ℝ≥0))
      (nhds (rightTailStrictStabilizedRatePath n areaFloor q xR t sample)) :=
  (rightSourcePostRate_tendsto_strict (n := n) hfloor xR sample t).prodMk_nhds
    (rightTargetPostRate_tendsto_strict (n := n) hfloor xR sample t)

/-! ## First rate failure -/

def rightTailRateRegion (c C : ℝ) : Set (ℝ × ℝ) :=
  Icc c C ×ˢ Icc c C

theorem isClosed_rightTailRateRegion (c C : ℝ) :
    IsClosed (rightTailRateRegion c C) :=
  isClosed_Icc.prod isClosed_Icc

def rightTailRateBadSet (c C : ℝ) : Set (ℝ × ℝ) :=
  (rightTailRateRegion c C)ᶜ

theorem isOpen_rightTailRateBadSet (c C : ℝ) :
    IsOpen (rightTailRateBadSet c C) :=
  (isClosed_rightTailRateRegion c C).isOpen_compl

/-- First post-jump rate failure, capped by the deterministic right-tail horizon. -/
noncomputable def rightTailRateExitTime
    (n : ℕ) (areaFloor c C : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (H : ℝ≥0) : FiniteSample n → WithTop ℝ≥0 := fun sample ↦
  min (MeasureTheory.hittingAfter
    (rightTailPostRatePath n areaFloor q xR) (rightTailRateBadSet c C) 0 sample)
    (H : WithTop ℝ≥0)

theorem rightTailRateExitTime_isStoppingTime
    {q : FiniteSample n → ℝ} (hq : Measurable q) {areaFloor : ℝ}
    (hfloor : 0 < areaFloor) (xR c C : ℝ) (H : ℝ≥0) :
    IsStoppingTime (rightTailUsualFiltration q hq xR)
      (rightTailRateExitTime n areaFloor c C q xR H) := by
  let _ : Filtration.IsRightContinuous (rightTailUsualFiltration q hq xR) :=
    rightTailUsualFiltration_isRightContinuous q hq xR
  have hhit :=
    CountingProcess.MeasureTheory.Adapted.isStoppingTime_hittingAfter_zero_isOpen_of_rightContinuous
      (rightTailPostRatePath_adapted (n := n) hq areaFloor xR)
      (rightTailPostRatePath_rightContinuous (n := n) hfloor xR)
      (isOpen_rightTailRateBadSet c C)
  intro t
  rw [show {sample | rightTailRateExitTime n areaFloor c C q xR H sample ≤
        (t : WithTop ℝ≥0)} =
      {sample | MeasureTheory.hittingAfter
          (rightTailPostRatePath n areaFloor q xR)
          (rightTailRateBadSet c C) 0 sample ≤ (t : WithTop ℝ≥0)} ∪
        {sample | (H : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} by
      ext sample
      simp only [rightTailRateExitTime, min_le_iff, mem_ofPred_eq, mem_union]]
  exact (hhit t).union (MeasurableSet.const ((H : WithTop ℝ≥0) ≤ t))

/-- Strictly before the first post-jump failure, the predictable strict-left stabilized rates
remain in the prescribed compact interval. -/
theorem rightTailStrictStabilizedRatePath_mem_region_of_lt_exit
    {q : FiniteSample n → ℝ} {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (xR c C : ℝ) (H t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      rightTailRateExitTime n areaFloor c C q xR H sample) :
    rightTailStrictStabilizedRatePath n areaFloor q xR t sample ∈
      rightTailRateRegion c C := by
  have htHit : (t : WithTop ℝ≥0) < MeasureTheory.hittingAfter
      (rightTailPostRatePath n areaFloor q xR) (rightTailRateBadSet c C) 0 sample :=
    ht.trans_le (min_le_left _ _)
  by_cases ht0 : t = 0
  · subst t
    have hpost := CountingProcess.not_mem_of_lt_hittingAfter_zero htHit
    have heq : rightTailStrictStabilizedRatePath n areaFloor q xR 0 sample =
        rightTailPostRatePath n areaFloor q xR 0 sample := by
      simp [rightTailStrictStabilizedRatePath, rightTailPostRatePath,
        rightSourceStrictStabilizedRate, rightTargetStrictStabilizedRate,
        rightSourcePostStabilizedRate, rightTargetPostStabilizedRate,
        rightSourceRemainingBefore, rightTargetRemainingBefore,
        rightSourceRemainingAt, rightTargetRemainingAt]
    rw [heq]
    simpa only [rightTailRateBadSet, mem_compl_iff, not_not] using hpost
  · have htpos : 0 < t := lt_of_le_of_ne t.2 (Ne.symm ht0)
    let _ : NeBot (nhdsWithin t (Iio t : Set ℝ≥0)) :=
      nhdsWithin_Iio_neBot' ⟨0, htpos⟩ le_rfl
    apply (isClosed_rightTailRateRegion c C).mem_of_tendsto
      (rightTailPostRatePath_tendsto_strict (n := n) hfloor xR sample t)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsHit : (s : WithTop ℝ≥0) < MeasureTheory.hittingAfter
        (rightTailPostRatePath n areaFloor q xR) (rightTailRateBadSet c C) 0 sample :=
      (WithTop.coe_lt_coe.mpr hs).trans htHit
    have hnot := CountingProcess.not_mem_of_lt_hittingAfter_zero hsHit
    simpa only [rightTailRateBadSet, mem_compl_iff, not_not] using hnot

theorem rightSourceStrictStabilizedRate_eq_rate
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n)
    (harea : areaFloor ≤ rightSourceArea n q xR t sample) :
    rightSourceStrictStabilizedRate n areaFloor q xR t sample =
      rightSourceStrictRate n q xR t sample := by
  simp [rightSourceStrictStabilizedRate, rightSourceStrictRate,
    rightSourceStabilizedArea, max_eq_right harea]

theorem rightTargetStrictStabilizedRate_eq_rate
    (n : ℕ) (areaFloor : ℝ) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n)
    (harea : areaFloor ≤ rightTargetArea n q xR t sample) :
    rightTargetStrictStabilizedRate n areaFloor q xR t sample =
      rightTargetStrictRate n q xR t sample := by
  simp [rightTargetStrictStabilizedRate, rightTargetStrictRate,
    rightTargetStabilizedArea, max_eq_right harea]

/-- Public stopped bound for the genuine strict-left rates, under the deterministic area floor
condition valid on the paper's interval `[x_R,x_*]`. -/
theorem rightTailStrictRates_mem_Icc_of_lt_exit
    {q : FiniteSample n → ℝ} {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (xR c C : ℝ) (H t : ℝ≥0) (sample : FiniteSample n)
    (ht : (t : WithTop ℝ≥0) <
      rightTailRateExitTime n areaFloor c C q xR H sample)
    (hsourceArea : areaFloor ≤ rightSourceArea n q xR t sample)
    (htargetArea : areaFloor ≤ rightTargetArea n q xR t sample) :
    rightSourceStrictRate n q xR t sample ∈ Icc c C ∧
      rightTargetStrictRate n q xR t sample ∈ Icc c C := by
  have hregion := rightTailStrictStabilizedRatePath_mem_region_of_lt_exit
    (n := n) hfloor xR c C H t sample ht
  rw [rightTailRateRegion, mem_prod] at hregion
  rw [← rightSourceStrictStabilizedRate_eq_rate
      n areaFloor q xR t sample hsourceArea,
    ← rightTargetStrictStabilizedRate_eq_rate
      n areaFloor q xR t sample htargetArea]
  exact hregion

end FiniteSample

end OTSelector
