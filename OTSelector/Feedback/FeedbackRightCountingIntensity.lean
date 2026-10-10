import OTSelector.Feedback.FeedbackRightTailStopping
import OTSelector.Feedback.FeedbackRankArrival
import OTSelector.Probability.CountingProcess.FiniteEventThinning
import OTSelector.Probability.CountingProcess.PredictableFiniteSupport

/-!
# Filtration and predictable rates for frozen right-tail counts

The continuation filtration retains all boundary information and adds the attained right-tail
counts.  Rank arrival times are stopping times because their sublevel events are count
thresholds.  No individual future label is revealed merely by observing a count.

The rates below are restricted to a finite horizon and to the region where the physical
complement areas agree with their unclipped formulas and exceed a positive floor.  These
predictability statements are the side conditions for a subsequent compensator identity.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- Rank arrivals only require the attained count to be adapted; individual labels need not be
stopping times in the observation filtration. -/
theorem finiteRankEventTime_isStoppingTime_of_adapted_count
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (ξ : Fin n → Ω → WithTop ℝ≥0) (k : Fin n)
    (hcount : StronglyAdapted F (fun t ω ↦ (finiteEventCountTop ξ t ω : ℝ))) :
    IsStoppingTime F (finiteRankEventTime ξ k) := by
  intro t
  have hmeas : MeasurableSet[F t]
      {ω | (k.val : ℝ) < (finiteEventCountTop ξ t ω : ℝ)} :=
    measurableSet_lt measurable_const (hcount t).measurable
  convert hmeas using 1
  ext ω
  simp only [mem_ofPred_eq, finiteRankEventTime_le_iff_lt_finiteEventCountTop,
    Nat.cast_lt]

omit [MeasurableSpace Ω] in
/-- Sorting event labels preserves the entire attained counting path, including ties. -/
theorem finiteEventCountTop_finiteRankEventTime
    (ξ : Fin n → Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    finiteEventCountTop (finiteRankEventTime ξ) t ω = finiteEventCountTop ξ t ω := by
  unfold finiteEventCountTop finiteRankEventTime
  apply Finset.card_equiv (Tuple.sort (fun i ↦ ξ i ω))
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end CountingProcess

namespace FiniteSample

variable {n : ℕ}

/-- The raw tail filtration retains the full sigma-algebra available at the boundary and
adjoins the natural observations of the frozen-height continuation. -/
noncomputable def rightTailJoinedRawFiltration
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)) :=
  Filtration.const ℝ≥0 (bulk T) (bulk.le T) ⊔ rightTailRawFiltration q hq xR

noncomputable def rightTailJoinedUsualFiltration
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)) :=
  usualAugmentation (rightTailJoinedRawFiltration bulk T q hq xR)
    (finiteSampleLaw n : Measure (FiniteSample n))

theorem boundary_le_rightTailJoinedUsualFiltration
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) (t : ℝ≥0) :
    bulk T ≤ rightTailJoinedUsualFiltration bulk T q hq xR t :=
  (show bulk T ≤ rightTailJoinedRawFiltration bulk T q hq xR t from
    le_sup_left).trans
      (le_usualAugmentation (rightTailJoinedRawFiltration bulk T q hq xR)
        (finiteSampleLaw n : Measure (FiniteSample n)) t)

theorem rightTailSnapshot_stronglyAdapted_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    StronglyAdapted (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightTailSnapshot q xR) := by
  intro t
  have hraw := Filtration.stronglyAdapted_natural
    (fun t ↦ (measurable_rightTailSnapshot hq xR t).stronglyMeasurable) t
  apply hraw.mono
  exact (show rightTailRawFiltration q hq xR t ≤
      rightTailJoinedRawFiltration bulk T q hq xR t from le_sup_right).trans
    (le_usualAugmentation (rightTailJoinedRawFiltration bulk T q hq xR)
      (finiteSampleLaw n : Measure (FiniteSample n)) t)

theorem rightSourceCount_stronglyAdapted_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    StronglyAdapted (rightTailJoinedUsualFiltration bulk T q hq xR)
      (fun t sample ↦ (rightSourceCount q xR t sample : ℝ)) := by
  intro t
  have hproj : Measurable fun z : RightTailSnapshot n ↦ (z.2.2.1 : ℝ) := by fun_prop
  exact (hproj.comp (rightTailSnapshot_stronglyAdapted_joined
    bulk T q hq xR t).measurable).stronglyMeasurable

theorem rightTargetCount_stronglyAdapted_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    StronglyAdapted (rightTailJoinedUsualFiltration bulk T q hq xR)
      (fun t sample ↦ (rightTargetCount q xR t sample : ℝ)) := by
  intro t
  have hproj : Measurable fun z : RightTailSnapshot n ↦ (z.2.2.2 : ℝ) := by fun_prop
  exact (hproj.comp (rightTailSnapshot_stronglyAdapted_joined
    bulk T q hq xR t).measurable).stronglyMeasurable

theorem rightSourceRankEventTime_isStoppingTime_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) (k : Fin n) :
    IsStoppingTime (rightTailJoinedUsualFiltration bulk T q hq xR)
      (CountingProcess.finiteRankEventTime (rightSourceEventTime q xR) k) :=
  CountingProcess.finiteRankEventTime_isStoppingTime_of_adapted_count _ _ _
    (rightSourceCount_stronglyAdapted_joined bulk T q hq xR)

theorem rightTargetRankEventTime_isStoppingTime_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) (k : Fin n) :
    IsStoppingTime (rightTailJoinedUsualFiltration bulk T q hq xR)
      (CountingProcess.finiteRankEventTime (rightTargetEventTime q xR) k) :=
  CountingProcess.finiteRankEventTime_isStoppingTime_of_adapted_count _ _ _
    (rightTargetCount_stronglyAdapted_joined bulk T q hq xR)

/-- The frozen height is predictable from time zero in the joined filtration. -/
theorem rightTailHeight_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0) (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (fun _ ↦ q) := by
  apply CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
  · intro t
    exact (measurable_fst.comp
      (rightTailSnapshot_stronglyAdapted_joined bulk T q hq xR t).measurable).stronglyMeasurable
  · intro sample
    exact continuous_const

theorem rightSourceRemainingBefore_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0) (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightSourceRemainingBefore q xR) := by
  have hinitial : IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (fun _ sample ↦ ((rightSourceInitialPattern q xR sample).card : ℝ)) := by
    apply CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    · intro t
      have hproj : Measurable fun z : RightTailSnapshot n ↦ (z.2.1.1.card : ℝ) := by
        fun_prop
      exact (hproj.comp
        (rightTailSnapshot_stronglyAdapted_joined bulk T q hq xR t).measurable).stronglyMeasurable
    · intro sample
      exact continuous_const
  exact hinitial.sub (CountingProcess.stronglyMeasurable_countBefore
    (rightSourceCount_stronglyAdapted_joined bulk T q hq xR)
    (fun sample _ _ hst ↦ CountingProcess.finiteEventCountTop_mono _ sample hst))

theorem rightTargetRemainingBefore_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0) (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightTargetRemainingBefore q xR) := by
  have hinitial : IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (fun _ sample ↦ ((rightTargetInitialPattern q xR sample).card : ℝ)) := by
    apply CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    · intro t
      have hproj : Measurable fun z : RightTailSnapshot n ↦ (z.2.1.2.card : ℝ) := by
        fun_prop
      exact (hproj.comp
        (rightTailSnapshot_stronglyAdapted_joined bulk T q hq xR t).measurable).stronglyMeasurable
    · intro sample
      exact continuous_const
  exact hinitial.sub (CountingProcess.stronglyMeasurable_countBefore
    (rightTargetCount_stronglyAdapted_joined bulk T q hq xR)
    (fun sample _ _ hst ↦ CountingProcess.finiteEventCountTop_mono _ sample hst))

theorem rightSourceArea_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0) (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightSourceArea n q xR) := by
  have hqpred := rightTailHeight_predictable_joined bulk T q hq xR
  have htime : IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (fun t _ ↦ (t : ℝ)) := by
    apply CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    · exact fun _ ↦ stronglyMeasurable_const
    · exact fun _ ↦ continuous_subtype_val
  exact (stronglyMeasurable_const.sub (stronglyMeasurable_const.add htime)).add
    (hqpred.div stronglyMeasurable_const)

theorem rightTargetArea_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0) (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightTargetArea n q xR) := by
  have hqpred := rightTailHeight_predictable_joined bulk T q hq xR
  have htime : IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (fun t _ ↦ (t : ℝ)) := by
    apply CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    · exact fun _ ↦ stronglyMeasurable_const
    · exact fun _ ↦ continuous_subtype_val
  exact (stronglyMeasurable_const.sub (stronglyMeasurable_const.add htime)).sub
    ((hqpred.const_mul 3).div stronglyMeasurable_const)

theorem rightSourceStrictRate_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0) (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightSourceStrictRate n q xR) :=
  (rightSourceRemainingBefore_predictable_joined bulk T q hq xR).div
    (rightSourceArea_predictable_joined bulk T q hq xR)

theorem rightTargetStrictRate_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T : ℝ≥0) (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightTargetStrictRate n q xR) :=
  (rightTargetRemainingBefore_predictable_joined bulk T q hq xR).div
    (rightTargetArea_predictable_joined bulk T q hq xR)

/-- Endpoint conditions ensuring every source and target mark section is inside the rank strip.
The coordinates are the physical horizontal coordinate and frozen height. -/
def rightTailUnclippedRegion (n : ℕ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Ioo 0 (n : ℝ) ∧ z.1 - z.2 ∈ Ioo 0 (n : ℝ) ∧
    z.1 + z.2 ∈ Ioo 0 (n : ℝ) ∧ z.1 + 2 * z.2 ∈ Ioo 0 (n : ℝ)}

theorem isOpen_rightTailUnclippedRegion (n : ℕ) :
    IsOpen (rightTailUnclippedRegion n) := by
  exact (isOpen_Ioo.preimage continuous_fst).inter
    ((isOpen_Ioo.preimage (continuous_fst.sub continuous_snd)).inter
      ((isOpen_Ioo.preimage (continuous_fst.add continuous_snd)).inter
        (isOpen_Ioo.preimage (continuous_fst.add (continuous_const.mul continuous_snd)))))

theorem sourceBoundary_mem_Ioo_of_rightTailUnclippedRegion
    {x q : ℝ} (h : (x, q) ∈ rightTailUnclippedRegion n) (u : UnitMark) :
    sourceBoundary q x u ∈ Ioo 0 (n : ℝ) := by
  have hcombo := (convex_Ioo (𝕜 := ℝ) (0 : ℝ) (n : ℝ)) h.1 h.2.1
    u.property.1 (sub_nonneg.mpr u.property.2)
    (show (u : ℝ) + (1 - (u : ℝ)) = 1 by ring)
  convert hcombo using 1
  simp only [sourceBoundary, smul_eq_mul]
  ring

theorem targetBoundary_mem_Ioo_of_rightTailUnclippedRegion
    {x q : ℝ} (h : (x, q) ∈ rightTailUnclippedRegion n) (u : UnitMark) :
    targetBoundary q x u ∈ Ioo 0 (n : ℝ) := by
  have hcombo := (convex_Ioo (𝕜 := ℝ) (0 : ℝ) (n : ℝ)) h.2.2.1 h.2.2.2
    (sub_nonneg.mpr u.property.2) u.property.1
    (show (1 - (u : ℝ)) + (u : ℝ) = 1 by ring)
  convert hcombo using 1
  simp only [targetBoundary, smul_eq_mul]
  ring

/-- On the mask's spatial domain the source algebraic area is its physical remaining area,
and the frozen-height sweep speed is exactly one. -/
theorem sourcePhysicalArea_and_speed_of_rightTailUnclippedRegion
    {x q : ℝ} (h : (x, q) ∈ rightTailUnclippedRegion n) :
    sourceTrueRemaining n q x = sourceUnclippedRemainingMass n q x ∧
      sourceSweepSpeed n q x 0 = 1 := by
  have hs := sourceBoundary_mem_Ioo_of_rightTailUnclippedRegion h
  constructor
  · exact sourceTrueRemaining_eq_sourceUnclippedRemainingMass
      (fun u ↦ (hs u).1.le) (fun u ↦ (hs u).2.le)
  · simpa using sourceSweepSpeed_eq_sourceFactor
      (q := 0) (fun u ↦ (hs u).1) (fun u ↦ (hs u).2)

theorem targetPhysicalArea_and_speed_of_rightTailUnclippedRegion
    {x q : ℝ} (h : (x, q) ∈ rightTailUnclippedRegion n) :
    targetTrueRemaining n q x = targetUnclippedRemainingMass n q x ∧
      targetSweepSpeed n q x 0 = 1 := by
  have hs := targetBoundary_mem_Ioo_of_rightTailUnclippedRegion h
  constructor
  · exact targetTrueRemaining_eq_targetUnclippedRemainingMass
      (fun u ↦ (hs u).1.le) (fun u ↦ (hs u).2.le)
  · simpa using targetSweepSpeed_eq_targetFactor
      (q := 0) (fun u ↦ (hs u).1) (fun u ↦ (hs u).2)

/-- The mask is active only on its finite horizon, in the unclipped strip, and when both
physical complement areas are at least the prescribed floor. -/
def rightTailRateAdmissible
    (n : ℕ) (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : Prop :=
  t ∈ Ioc 0 H ∧ (xR + (t : ℝ), q sample) ∈ rightTailUnclippedRegion n ∧
    areaFloor ≤ rightSourceArea n q xR t sample ∧
    areaFloor ≤ rightTargetArea n q xR t sample

noncomputable def rightTailRateMask
    (n : ℕ) (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  if rightTailRateAdmissible n areaFloor H q xR t sample then 1 else 0

theorem rightTailRateMask_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T H : ℝ≥0) (areaFloor : ℝ)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightTailRateMask n areaFloor H q xR) := by
  let F := rightTailJoinedUsualFiltration bulk T q hq xR
  have htimeReal : IsStronglyPredictable F (fun t _ ↦ (t : ℝ)) := by
    apply CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    · exact fun _ ↦ stronglyMeasurable_const
    · exact fun _ ↦ continuous_subtype_val
  have htimeSet : MeasurableSet[F.predictable]
      {z : ℝ≥0 × FiniteSample n | z.1 ∈ Ioc 0 H} := by
    convert htimeReal.measurable (measurableSet_Ioc (a := (0 : ℝ)) (b := (H : ℝ))) using 1
    ext z
    simp [Function.uncurry]
  have hheight := rightTailHeight_predictable_joined bulk T q hq xR
  have hcoords : Measurable[F.predictable]
      (fun z : ℝ≥0 × FiniteSample n ↦ (xR + (z.1 : ℝ), q z.2)) :=
    ((stronglyMeasurable_const.add htimeReal).prodMk hheight).measurable
  have hset : MeasurableSet[F.predictable]
      {z : ℝ≥0 × FiniteSample n | rightTailRateAdmissible n areaFloor H q xR z.1 z.2} :=
    htimeSet.inter
      ((hcoords (isOpen_rightTailUnclippedRegion n).measurableSet).inter
        ((measurableSet_le measurable_const
          (rightSourceArea_predictable_joined bulk T q hq xR).measurable).inter
            (measurableSet_le measurable_const
              (rightTargetArea_predictable_joined bulk T q hq xR).measurable)))
  exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable

/-- Source rate after predictable thinning; the numerator still counts all labels remaining
strictly before the current time, including labels ignored by the mask. -/
noncomputable def rightSourceMaskedRate
    (n : ℕ) (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightTailRateMask n areaFloor H q xR t sample * rightSourceStrictRate n q xR t sample

noncomputable def rightTargetMaskedRate
    (n : ℕ) (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  rightTailRateMask n areaFloor H q xR t sample * rightTargetStrictRate n q xR t sample

theorem rightSourceMaskedRate_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T H : ℝ≥0) (areaFloor : ℝ)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightSourceMaskedRate n areaFloor H q xR) :=
  (rightTailRateMask_predictable_joined bulk T H areaFloor q hq xR).mul
    (rightSourceStrictRate_predictable_joined bulk T q hq xR)

theorem rightTargetMaskedRate_predictable_joined
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T H : ℝ≥0) (areaFloor : ℝ)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    IsStronglyPredictable (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightTargetMaskedRate n areaFloor H q xR) :=
  (rightTailRateMask_predictable_joined bulk T H areaFloor q hq xR).mul
    (rightTargetStrictRate_predictable_joined bulk T q hq xR)

private theorem rightSourceCountBefore_le_initial
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    CountingProcess.countBefore (rightSourceCount q xR) t sample ≤
      (rightSourceInitialPattern q xR sample).card := by
  unfold rightSourceCount
  rw [CountingProcess.countBefore_finiteEventCountTop_eq_card_filter_lt]
  apply Finset.card_le_card
  intro i hi
  have hiTime := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hnot
  simp only [rightSourceEventTime, hnot, ite_false] at hiTime
  exact not_lt_of_ge le_top hiTime

theorem rightSourceRemainingBefore_mem_Icc
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    rightSourceRemainingBefore q xR t sample ∈ Icc 0 (n : ℝ) := by
  have hle : (CountingProcess.countBefore (rightSourceCount q xR) t sample : ℝ) ≤
      (rightSourceInitialPattern q xR sample).card := by
    exact_mod_cast rightSourceCountBefore_le_initial q xR t sample
  have hcard : ((rightSourceInitialPattern q xR sample).card : ℝ) ≤ n := by
    exact_mod_cast (show (rightSourceInitialPattern q xR sample).card ≤ n by
      simpa using Finset.card_le_univ (rightSourceInitialPattern q xR sample))
  have hcount : (0 : ℝ) ≤ CountingProcess.countBefore (rightSourceCount q xR) t sample := by
    positivity
  constructor <;> unfold rightSourceRemainingBefore <;> linarith

theorem rightSourceMaskedRate_nonneg
    {areaFloor : ℝ} (hfloor : 0 < areaFloor) (H : ℝ≥0)
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    0 ≤ rightSourceMaskedRate n areaFloor H q xR t sample := by
  by_cases hadm : rightTailRateAdmissible n areaFloor H q xR t sample
  · have hden : 0 ≤ rightSourceArea n q xR t sample :=
      hfloor.le.trans hadm.2.2.1
    simp only [rightSourceMaskedRate, rightTailRateMask, hadm, ite_true, one_mul,
      rightSourceStrictRate]
    exact div_nonneg (rightSourceRemainingBefore_mem_Icc q xR t sample).1 hden
  · simp [rightSourceMaskedRate, rightTailRateMask, hadm]

theorem rightSourceMaskedRate_le
    {areaFloor : ℝ} (hfloor : 0 < areaFloor) (H : ℝ≥0)
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    rightSourceMaskedRate n areaFloor H q xR t sample ≤ (n : ℝ) / areaFloor := by
  by_cases hadm : rightTailRateAdmissible n areaFloor H q xR t sample
  · have hden : 0 < rightSourceArea n q xR t sample :=
      hfloor.trans_le hadm.2.2.1
    simp only [rightSourceMaskedRate, rightTailRateMask, hadm, ite_true, one_mul,
      rightSourceStrictRate]
    exact (div_le_div_of_nonneg_right
      (rightSourceRemainingBefore_mem_Icc q xR t sample).2 hden.le).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hfloor hadm.2.2.1)
  · simp only [rightSourceMaskedRate, rightTailRateMask, hadm, ite_false, zero_mul]
    positivity

theorem rightSourceMaskedRate_eq_zero_of_horizon_lt
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    {t : ℝ≥0} (ht : H < t) (sample : FiniteSample n) :
    rightSourceMaskedRate n areaFloor H q xR t sample = 0 := by
  have hadm : ¬ rightTailRateAdmissible n areaFloor H q xR t sample :=
    fun h ↦ (not_le.mpr ht) h.1.2
  simp [rightSourceMaskedRate, rightTailRateMask, hadm]

theorem rightSourceMaskedRate_product_integrable
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T H : ℝ≥0) {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    Integrable (Function.uncurry (rightSourceMaskedRate n areaFloor H q xR))
      (CountingProcess.timeMeasure.prod (finiteSampleLaw n : Measure (FiniteSample n))) := by
  apply CountingProcess.integrable_uncurry_of_predictable_bounded_finite_support
    (finiteSampleLaw n : Measure (FiniteSample n))
    (rightTailJoinedUsualFiltration bulk T q hq xR)
    (rightSourceMaskedRate_predictable_joined bulk T H areaFloor q hq xR)
    (rightSourceMaskedRate_nonneg hfloor H q xR)
    (show 0 ≤ (n : ℝ) / areaFloor by positivity)
    (rightSourceMaskedRate_le hfloor H q xR) H
  intro t sample hne
  by_contra ht
  exact hne (rightSourceMaskedRate_eq_zero_of_horizon_lt areaFloor H q xR (lt_of_not_ge ht) sample)

private theorem rightTargetCountBefore_le_initial
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    CountingProcess.countBefore (rightTargetCount q xR) t sample ≤
      (rightTargetInitialPattern q xR sample).card := by
  unfold rightTargetCount
  rw [CountingProcess.countBefore_finiteEventCountTop_eq_card_filter_lt]
  apply Finset.card_le_card
  intro i hi
  have hiTime := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hnot
  simp only [rightTargetEventTime, hnot, ite_false] at hiTime
  exact not_lt_of_ge le_top hiTime

theorem rightTargetRemainingBefore_mem_Icc
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    rightTargetRemainingBefore q xR t sample ∈ Icc 0 (n : ℝ) := by
  have hle : (CountingProcess.countBefore (rightTargetCount q xR) t sample : ℝ) ≤
      (rightTargetInitialPattern q xR sample).card := by
    exact_mod_cast rightTargetCountBefore_le_initial q xR t sample
  have hcard : ((rightTargetInitialPattern q xR sample).card : ℝ) ≤ n := by
    exact_mod_cast (show (rightTargetInitialPattern q xR sample).card ≤ n by
      simpa using Finset.card_le_univ (rightTargetInitialPattern q xR sample))
  have hcount : (0 : ℝ) ≤ CountingProcess.countBefore (rightTargetCount q xR) t sample := by
    positivity
  constructor <;> unfold rightTargetRemainingBefore <;> linarith

theorem rightTargetMaskedRate_nonneg
    {areaFloor : ℝ} (hfloor : 0 < areaFloor) (H : ℝ≥0)
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    0 ≤ rightTargetMaskedRate n areaFloor H q xR t sample := by
  by_cases hadm : rightTailRateAdmissible n areaFloor H q xR t sample
  · have hden : 0 ≤ rightTargetArea n q xR t sample :=
      hfloor.le.trans hadm.2.2.2
    simp only [rightTargetMaskedRate, rightTailRateMask, hadm, ite_true, one_mul,
      rightTargetStrictRate]
    exact div_nonneg (rightTargetRemainingBefore_mem_Icc q xR t sample).1 hden
  · simp [rightTargetMaskedRate, rightTailRateMask, hadm]

theorem rightTargetMaskedRate_le
    {areaFloor : ℝ} (hfloor : 0 < areaFloor) (H : ℝ≥0)
    (q : FiniteSample n → ℝ) (xR : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    rightTargetMaskedRate n areaFloor H q xR t sample ≤ (n : ℝ) / areaFloor := by
  by_cases hadm : rightTailRateAdmissible n areaFloor H q xR t sample
  · have hden : 0 < rightTargetArea n q xR t sample :=
      hfloor.trans_le hadm.2.2.2
    simp only [rightTargetMaskedRate, rightTailRateMask, hadm, ite_true, one_mul,
      rightTargetStrictRate]
    exact (div_le_div_of_nonneg_right
      (rightTargetRemainingBefore_mem_Icc q xR t sample).2 hden.le).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hfloor hadm.2.2.2)
  · simp only [rightTargetMaskedRate, rightTailRateMask, hadm, ite_false, zero_mul]
    positivity

theorem rightTargetMaskedRate_eq_zero_of_horizon_lt
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    {t : ℝ≥0} (ht : H < t) (sample : FiniteSample n) :
    rightTargetMaskedRate n areaFloor H q xR t sample = 0 := by
  have hadm : ¬ rightTailRateAdmissible n areaFloor H q xR t sample :=
    fun h ↦ (not_le.mpr ht) h.1.2
  simp [rightTargetMaskedRate, rightTailRateMask, hadm]

theorem rightTargetMaskedRate_product_integrable
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T H : ℝ≥0) {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) :
    Integrable (Function.uncurry (rightTargetMaskedRate n areaFloor H q xR))
      (CountingProcess.timeMeasure.prod (finiteSampleLaw n : Measure (FiniteSample n))) := by
  apply CountingProcess.integrable_uncurry_of_predictable_bounded_finite_support
    (finiteSampleLaw n : Measure (FiniteSample n))
    (rightTailJoinedUsualFiltration bulk T q hq xR)
    (rightTargetMaskedRate_predictable_joined bulk T H areaFloor q hq xR)
    (rightTargetMaskedRate_nonneg hfloor H q xR)
    (show 0 ≤ (n : ℝ) / areaFloor by positivity)
    (rightTargetMaskedRate_le hfloor H q xR) H
  intro t sample hne
  by_contra ht
  exact hne (rightTargetMaskedRate_eq_zero_of_horizon_lt areaFloor H q xR (lt_of_not_ge ht) sample)

/-- The masked formula is exactly remaining count times physical sweep speed divided by
physical remaining area wherever the predictable mask is active. -/
theorem rightSourceMaskedRate_eq_physical
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) :
    rightSourceMaskedRate n areaFloor H q xR t sample =
      rightTailRateMask n areaFloor H q xR t sample *
        (rightSourceRemainingBefore q xR t sample *
          sourceSweepSpeed n (q sample) (xR + (t : ℝ)) 0 /
            sourceTrueRemaining n (q sample) (xR + (t : ℝ))) := by
  by_cases hadm : rightTailRateAdmissible n areaFloor H q xR t sample
  · obtain ⟨harea, hspeed⟩ := sourcePhysicalArea_and_speed_of_rightTailUnclippedRegion
      hadm.2.1
    rw [harea, hspeed, mul_one]
    rfl
  · simp [rightSourceMaskedRate, rightTailRateMask, hadm]

theorem rightSourceMaskedRate_eq_mask_mul_stabilized
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) :
    rightSourceMaskedRate n areaFloor H q xR t sample =
      rightTailRateMask n areaFloor H q xR t sample *
        rightSourceStrictStabilizedRate n areaFloor q xR t sample := by
  by_cases hadm : rightTailRateAdmissible n areaFloor H q xR t sample
  · rw [rightSourceStrictStabilizedRate_eq_rate n areaFloor q xR t sample hadm.2.2.1]
    rfl
  · simp [rightSourceMaskedRate, rightTailRateMask, hadm]

theorem rightSourceMaskedRate_integrableOn
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T H : ℝ≥0) {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ)
    (R : ℝ≥0) (sample : FiniteSample n) :
    IntegrableOn (fun t ↦ rightSourceMaskedRate n areaFloor H q xR t sample)
      (Ioc (0 : ℝ≥0) R) CountingProcess.timeMeasure := by
  have hambient : StronglyMeasurable[Prod.instMeasurableSpace]
      (Function.uncurry (rightSourceMaskedRate n areaFloor H q xR)) :=
    (rightSourceMaskedRate_predictable_joined bulk T H areaFloor q hq xR).mono
      (CountingProcess.predictable_le_ambient (rightTailJoinedUsualFiltration bulk T q hq xR))
  have hsection := hambient.comp_measurable (measurable_id.prodMk (measurable_const (a := sample)))
  apply Measure.integrableOn_of_bounded (CountingProcess.timeMeasure_Ioc_lt_top 0 R).ne
    hsection.aestronglyMeasurable (M := (n : ℝ) / areaFloor)
  exact ae_of_all _ fun t ↦ by
    change ‖rightSourceMaskedRate n areaFloor H q xR t sample‖ ≤ (n : ℝ) / areaFloor
    rw [Real.norm_eq_abs, abs_of_nonneg (rightSourceMaskedRate_nonneg hfloor H q xR t sample)]
    exact rightSourceMaskedRate_le hfloor H q xR t sample

/-- Thinning is applied to rank arrivals, which are stopping times in the count-observation
filtration, without exposing the identities of unseen future labels. -/
noncomputable def rightSourceMaskedRankEventTime
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ) (k : Fin n) :
    FiniteSample n → WithTop ℝ≥0 :=
  CountingProcess.thinnedEventTime (rightTailRateMask n areaFloor H q xR)
    (CountingProcess.finiteRankEventTime (rightSourceEventTime q xR) k)

theorem rightSourceMaskedRankEventTime_isStoppingTime
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T H : ℝ≥0) (areaFloor : ℝ)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) (k : Fin n) :
    IsStoppingTime (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightSourceMaskedRankEventTime areaFloor H q xR k) :=
  CountingProcess.isStoppingTime_thinnedEventTime_of_predictable
    (rightSourceRankEventTime_isStoppingTime_joined bulk T q hq xR k)
    (rightTailRateMask_predictable_joined bulk T H areaFloor q hq xR)

theorem rightSourceMaskedRankEventTime_eq_top_or_pos
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (k : Fin n) (sample : FiniteSample n) :
    rightSourceMaskedRankEventTime areaFloor H q xR k sample = ⊤ ∨
      (0 : WithTop ℝ≥0) < rightSourceMaskedRankEventTime areaFloor H q xR k sample := by
  apply CountingProcess.thinnedEventTime_eq_top_or_pos
  intro sample
  apply CountingProcess.finiteRankEventTime_eq_top_or_pos
  intro i
  unfold rightSourceEventTime
  split_ifs with h
  · exact Or.inr (WithTop.coe_pos.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr h)))
  · exact Or.inl rfl

/-- The masked formula is exactly remaining count times physical sweep speed divided by
physical remaining area wherever the predictable mask is active. -/
theorem rightTargetMaskedRate_eq_physical
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) :
    rightTargetMaskedRate n areaFloor H q xR t sample =
      rightTailRateMask n areaFloor H q xR t sample *
        (rightTargetRemainingBefore q xR t sample *
          targetSweepSpeed n (q sample) (xR + (t : ℝ)) 0 /
            targetTrueRemaining n (q sample) (xR + (t : ℝ))) := by
  by_cases hadm : rightTailRateAdmissible n areaFloor H q xR t sample
  · obtain ⟨harea, hspeed⟩ := targetPhysicalArea_and_speed_of_rightTailUnclippedRegion
      hadm.2.1
    rw [harea, hspeed, mul_one]
    rfl
  · simp [rightTargetMaskedRate, rightTailRateMask, hadm]

theorem rightTargetMaskedRate_eq_mask_mul_stabilized
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (t : ℝ≥0) (sample : FiniteSample n) :
    rightTargetMaskedRate n areaFloor H q xR t sample =
      rightTailRateMask n areaFloor H q xR t sample *
        rightTargetStrictStabilizedRate n areaFloor q xR t sample := by
  by_cases hadm : rightTailRateAdmissible n areaFloor H q xR t sample
  · rw [rightTargetStrictStabilizedRate_eq_rate n areaFloor q xR t sample hadm.2.2.2]
    rfl
  · simp [rightTargetMaskedRate, rightTailRateMask, hadm]

theorem rightTargetMaskedRate_integrableOn
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T H : ℝ≥0) {areaFloor : ℝ} (hfloor : 0 < areaFloor)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ)
    (R : ℝ≥0) (sample : FiniteSample n) :
    IntegrableOn (fun t ↦ rightTargetMaskedRate n areaFloor H q xR t sample)
      (Ioc (0 : ℝ≥0) R) CountingProcess.timeMeasure := by
  have hambient : StronglyMeasurable[Prod.instMeasurableSpace]
      (Function.uncurry (rightTargetMaskedRate n areaFloor H q xR)) :=
    (rightTargetMaskedRate_predictable_joined bulk T H areaFloor q hq xR).mono
      (CountingProcess.predictable_le_ambient (rightTailJoinedUsualFiltration bulk T q hq xR))
  have hsection := hambient.comp_measurable (measurable_id.prodMk (measurable_const (a := sample)))
  apply Measure.integrableOn_of_bounded (CountingProcess.timeMeasure_Ioc_lt_top 0 R).ne
    hsection.aestronglyMeasurable (M := (n : ℝ) / areaFloor)
  exact ae_of_all _ fun t ↦ by
    change ‖rightTargetMaskedRate n areaFloor H q xR t sample‖ ≤ (n : ℝ) / areaFloor
    rw [Real.norm_eq_abs, abs_of_nonneg (rightTargetMaskedRate_nonneg hfloor H q xR t sample)]
    exact rightTargetMaskedRate_le hfloor H q xR t sample

/-- Thinning is applied to rank arrivals, which are stopping times in the count-observation
filtration, without exposing the identities of unseen future labels. -/
noncomputable def rightTargetMaskedRankEventTime
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ) (k : Fin n) :
    FiniteSample n → WithTop ℝ≥0 :=
  CountingProcess.thinnedEventTime (rightTailRateMask n areaFloor H q xR)
    (CountingProcess.finiteRankEventTime (rightTargetEventTime q xR) k)

theorem rightTargetMaskedRankEventTime_isStoppingTime
    (bulk : Filtration ℝ≥0 (inferInstance : MeasurableSpace (FiniteSample n)))
    (T H : ℝ≥0) (areaFloor : ℝ)
    (q : FiniteSample n → ℝ) (hq : Measurable q) (xR : ℝ) (k : Fin n) :
    IsStoppingTime (rightTailJoinedUsualFiltration bulk T q hq xR)
      (rightTargetMaskedRankEventTime areaFloor H q xR k) :=
  CountingProcess.isStoppingTime_thinnedEventTime_of_predictable
    (rightTargetRankEventTime_isStoppingTime_joined bulk T q hq xR k)
    (rightTailRateMask_predictable_joined bulk T H areaFloor q hq xR)

theorem rightTargetMaskedRankEventTime_eq_top_or_pos
    (areaFloor : ℝ) (H : ℝ≥0) (q : FiniteSample n → ℝ) (xR : ℝ)
    (k : Fin n) (sample : FiniteSample n) :
    rightTargetMaskedRankEventTime areaFloor H q xR k sample = ⊤ ∨
      (0 : WithTop ℝ≥0) < rightTargetMaskedRankEventTime areaFloor H q xR k sample := by
  apply CountingProcess.thinnedEventTime_eq_top_or_pos
  intro sample
  apply CountingProcess.finiteRankEventTime_eq_top_or_pos
  intro i
  unfold rightTargetEventTime
  split_ifs with h
  · exact Or.inr (WithTop.coe_pos.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr h)))
  · exact Or.inl rfl

end FiniteSample
end OTSelector
