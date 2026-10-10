import OTSelector.Feedback.FeedbackPredictableHeight
import OTSelector.Feedback.FeedbackRegularitySurvival
import OTSelector.Feedback.SpacelikeAssembly
import OTSelector.Probability.CountingProcess.ContinuousOpenHitting

/-!
# Actual finite-sample A2 assembly

This file transports the two one-array cut estimates to the distinct source and target arrays of
`finiteSampleLaw`.  The raw global-supremum and endpoint bad sets are not exposed as Borel sets,
so each of the four sets is first replaced by its measurable hull under the corresponding row
law.  Taking the source and target hulls separately is essential: a joint theorem for one rank
array does not control the two different arrays of an actual finite sample.

The final section defines the genuine first open-exit coordinate of the safe feedback height and
assembles the deterministic first-shear-hit trichotomy.  The missing A1 input is represented by
an ordinary measurable current-excursion event, rather than by a bundled placeholder or by an
assumption of A2 survival itself.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal NNReal Topology

namespace OTSelector

open FiniteSample
open RelativeVC

/-! ## Actual source/target row transport -/

theorem finiteSampleLaw_real_preimage_feedbackSourceRankArray
    {n : ℕ} {s : Set (Fin n → ℝ × UnitMark)} (hs : MeasurableSet s) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackSourceRankArray ⁻¹' s) =
      (globalCutRowLaw n).real s := by
  have hmeasure :
      (finiteSampleLaw n : Measure (FiniteSample n))
          (feedbackSourceRankArray ⁻¹' s) =
        (globalCutRowLaw n) s := by
    calc
      (finiteSampleLaw n : Measure (FiniteSample n))
          (feedbackSourceRankArray ⁻¹' s) =
          Measure.map feedbackSourceRankArray
            (finiteSampleLaw n : Measure (FiniteSample n)) s :=
        (Measure.map_apply measurable_feedbackSourceRankArray hs).symm
      _ = (globalCutRowLaw n) s := by
        rw [finiteSampleLaw_map_feedbackSourceRankArray_measure]
        rfl
  exact congrArg ENNReal.toReal hmeasure

theorem finiteSampleLaw_real_preimage_feedbackTargetRankArray
    {n : ℕ} {s : Set (Fin n → ℝ × UnitMark)} (hs : MeasurableSet s) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackTargetRankArray ⁻¹' s) =
      (globalCutRowLaw n).real s := by
  have hmeasure :
      (finiteSampleLaw n : Measure (FiniteSample n))
          (feedbackTargetRankArray ⁻¹' s) =
        (globalCutRowLaw n) s := by
    calc
      (finiteSampleLaw n : Measure (FiniteSample n))
          (feedbackTargetRankArray ⁻¹' s) =
          Measure.map feedbackTargetRankArray
            (finiteSampleLaw n : Measure (FiniteSample n)) s :=
        (Measure.map_apply measurable_feedbackTargetRankArray hs).symm
      _ = (globalCutRowLaw n) s := by
        rw [finiteSampleLaw_map_feedbackTargetRankArray_measure]
        rfl
  exact congrArg ENNReal.toReal hmeasure

/-! ## Measurable actual global-cut events -/

/-- Measurable hull of the source global-supremum excursion. -/
noncomputable def rankSourceGlobalCutBadEventHull (q : ℝ) (n : ℕ) :
    Set (Fin n → ℝ × UnitMark) :=
  toMeasurable (globalCutRowLaw n)
    {points | (q + 32) * Real.sqrt n <
      |globalSourceCutSup (rankStripLaw n : Measure (ℝ × UnitMark)) points|}

/-- Measurable hull of the target global-supremum excursion. -/
noncomputable def rankTargetGlobalCutBadEventHull (q : ℝ) (n : ℕ) :
    Set (Fin n → ℝ × UnitMark) :=
  toMeasurable (globalCutRowLaw n)
    {points | (q + 32) * Real.sqrt n <
      |globalTargetCutSup (rankStripLaw n : Measure (ℝ × UnitMark)) points|}

/-- Either distinct actual rank array violates its corresponding global cut envelope. -/
noncomputable def feedbackA2GlobalCutBadEvent (q : ℝ) (n : ℕ) :
    Set (FiniteSample n) :=
  feedbackSourceRankArray ⁻¹' rankSourceGlobalCutBadEventHull q n ∪
    feedbackTargetRankArray ⁻¹' rankTargetGlobalCutBadEventHull q n

noncomputable def feedbackA2GlobalCutGoodEvent (q : ℝ) (n : ℕ) :
    Set (FiniteSample n) :=
  (feedbackA2GlobalCutBadEvent q n)ᶜ

theorem measurableSet_rankSourceGlobalCutBadEventHull (q : ℝ) (n : ℕ) :
    MeasurableSet (rankSourceGlobalCutBadEventHull q n) :=
  measurableSet_toMeasurable _ _

theorem measurableSet_rankTargetGlobalCutBadEventHull (q : ℝ) (n : ℕ) :
    MeasurableSet (rankTargetGlobalCutBadEventHull q n) :=
  measurableSet_toMeasurable _ _

theorem measurableSet_feedbackA2GlobalCutBadEvent (q : ℝ) (n : ℕ) :
    MeasurableSet (feedbackA2GlobalCutBadEvent q n) := by
  exact ((measurableSet_rankSourceGlobalCutBadEventHull q n).preimage
    measurable_feedbackSourceRankArray).union
      ((measurableSet_rankTargetGlobalCutBadEventHull q n).preimage
        measurable_feedbackTargetRankArray)

theorem measurableSet_feedbackA2GlobalCutGoodEvent (q : ℝ) (n : ℕ) :
    MeasurableSet (feedbackA2GlobalCutGoodEvent q n) :=
  (measurableSet_feedbackA2GlobalCutBadEvent q n).compl

theorem feedbackA2GlobalCutGoodEvent.source_bound
    {q : ℝ} {n : ℕ} {sample : FiniteSample n}
    (hgood : sample ∈ feedbackA2GlobalCutGoodEvent q n) :
    globalSourceCutSup (rankStripLaw n : Measure (ℝ × UnitMark))
        (feedbackSourceRankArray sample) ≤
      (q + 32) * Real.sqrt n := by
  have hnotHull : feedbackSourceRankArray sample ∉
      rankSourceGlobalCutBadEventHull q n := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hnotRaw : feedbackSourceRankArray sample ∉
      {points | (q + 32) * Real.sqrt n <
        |globalSourceCutSup (rankStripLaw n : Measure (ℝ × UnitMark)) points|} := by
    intro hbad
    exact hnotHull (subset_toMeasurable (globalCutRowLaw n) _ hbad)
  have hnonneg := globalSourceCutSup_nonneg
    (rankStripLaw n : Measure (ℝ × UnitMark)) (feedbackSourceRankArray sample)
  change ¬(q + 32) * Real.sqrt n <
    |globalSourceCutSup (rankStripLaw n : Measure (ℝ × UnitMark))
      (feedbackSourceRankArray sample)| at hnotRaw
  rw [abs_of_nonneg hnonneg] at hnotRaw
  exact le_of_not_gt hnotRaw

theorem feedbackA2GlobalCutGoodEvent.target_bound
    {q : ℝ} {n : ℕ} {sample : FiniteSample n}
    (hgood : sample ∈ feedbackA2GlobalCutGoodEvent q n) :
    globalTargetCutSup (rankStripLaw n : Measure (ℝ × UnitMark))
        (feedbackTargetRankArray sample) ≤
      (q + 32) * Real.sqrt n := by
  have hnotHull : feedbackTargetRankArray sample ∉
      rankTargetGlobalCutBadEventHull q n := by
    intro hbad
    exact hgood (Or.inr hbad)
  have hnotRaw : feedbackTargetRankArray sample ∉
      {points | (q + 32) * Real.sqrt n <
        |globalTargetCutSup (rankStripLaw n : Measure (ℝ × UnitMark)) points|} := by
    intro hbad
    exact hnotHull (subset_toMeasurable (globalCutRowLaw n) _ hbad)
  have hnonneg := globalTargetCutSup_nonneg
    (rankStripLaw n : Measure (ℝ × UnitMark)) (feedbackTargetRankArray sample)
  change ¬(q + 32) * Real.sqrt n <
    |globalTargetCutSup (rankStripLaw n : Measure (ℝ × UnitMark))
      (feedbackTargetRankArray sample)| at hnotRaw
  rw [abs_of_nonneg hnonneg] at hnotRaw
  exact le_of_not_gt hnotRaw

/-- Separate source/target transport gives the actual two-array global-cut union bound. -/
theorem finiteSampleLaw_real_feedbackA2GlobalCutBadEvent_le
    {q : ℝ} {n : ℕ} (hn : 0 < n) (hq : 0 < q) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2GlobalCutBadEvent q n) ≤ 18832 / q := by
  let S := rankSourceGlobalCutBadEventHull q n
  let T := rankTargetGlobalCutBadEventHull q n
  have hS : MeasurableSet S := measurableSet_rankSourceGlobalCutBadEventHull q n
  have hT : MeasurableSet T := measurableSet_rankTargetGlobalCutBadEventHull q n
  have hsource :
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackSourceRankArray ⁻¹' S) ≤ 9416 / q := by
    rw [finiteSampleLaw_real_preimage_feedbackSourceRankArray hS]
    dsimp [S, rankSourceGlobalCutBadEventHull]
    change ENNReal.toReal ((globalCutRowLaw n)
      (toMeasurable (globalCutRowLaw n) _)) ≤ _
    rw [measure_toMeasurable]
    exact sourceCut_globalSup_tail_le
      (rankStripLaw n : Measure (ℝ × UnitMark)) hn hq
  have htarget :
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackTargetRankArray ⁻¹' T) ≤ 9416 / q := by
    rw [finiteSampleLaw_real_preimage_feedbackTargetRankArray hT]
    dsimp [T, rankTargetGlobalCutBadEventHull]
    change ENNReal.toReal ((globalCutRowLaw n)
      (toMeasurable (globalCutRowLaw n) _)) ≤ _
    rw [measure_toMeasurable]
    exact targetCut_globalSup_tail_le
      (rankStripLaw n : Measure (ℝ × UnitMark)) hn hq
  have hunion := measureReal_union_le
    (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (feedbackSourceRankArray ⁻¹' S) (feedbackTargetRankArray ⁻¹' T)
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2GlobalCutBadEvent q n) ≤
        (finiteSampleLaw n : Measure (FiniteSample n)).real
            (feedbackSourceRankArray ⁻¹' S) +
          (finiteSampleLaw n : Measure (FiniteSample n)).real
            (feedbackTargetRankArray ⁻¹' T) := by
      simpa [feedbackA2GlobalCutBadEvent, S, T] using hunion
    _ ≤ 9416 / q + 9416 / q := add_le_add hsource htarget
    _ = 18832 / q := by ring

/-! ## Measurable actual endpoint events -/

noncomputable def rankSourceEndpointBadEventHull
    (amplitude q : ℝ) (n : ℕ) : Set (Fin n → ℝ × UnitMark) :=
  toMeasurable (endpointRowLaw n) (sourceEndpointBadEvent amplitude q n)

noncomputable def rankTargetEndpointBadEventHull
    (amplitude q : ℝ) (n : ℕ) : Set (Fin n → ℝ × UnitMark) :=
  toMeasurable (endpointRowLaw n) (targetEndpointBadEvent amplitude q n)

noncomputable def feedbackA2EndpointBadEvent
    (amplitude q : ℝ) (n : ℕ) : Set (FiniteSample n) :=
  feedbackSourceRankArray ⁻¹' rankSourceEndpointBadEventHull amplitude q n ∪
    feedbackTargetRankArray ⁻¹' rankTargetEndpointBadEventHull amplitude q n

noncomputable def feedbackA2EndpointGoodEvent
    (amplitude q : ℝ) (n : ℕ) : Set (FiniteSample n) :=
  (feedbackA2EndpointBadEvent amplitude q n)ᶜ

theorem measurableSet_rankSourceEndpointBadEventHull
    (amplitude q : ℝ) (n : ℕ) :
    MeasurableSet (rankSourceEndpointBadEventHull amplitude q n) :=
  measurableSet_toMeasurable _ _

theorem measurableSet_rankTargetEndpointBadEventHull
    (amplitude q : ℝ) (n : ℕ) :
    MeasurableSet (rankTargetEndpointBadEventHull amplitude q n) :=
  measurableSet_toMeasurable _ _

theorem measurableSet_feedbackA2EndpointBadEvent
    (amplitude q : ℝ) (n : ℕ) :
    MeasurableSet (feedbackA2EndpointBadEvent amplitude q n) := by
  exact ((measurableSet_rankSourceEndpointBadEventHull amplitude q n).preimage
    measurable_feedbackSourceRankArray).union
      ((measurableSet_rankTargetEndpointBadEventHull amplitude q n).preimage
        measurable_feedbackTargetRankArray)

theorem measurableSet_feedbackA2EndpointGoodEvent
    (amplitude q : ℝ) (n : ℕ) :
    MeasurableSet (feedbackA2EndpointGoodEvent amplitude q n) :=
  (measurableSet_feedbackA2EndpointBadEvent amplitude q n).compl

theorem feedbackA2EndpointGoodEvent.source_raw
    {amplitude q : ℝ} {n : ℕ} {sample : FiniteSample n}
    (hgood : sample ∈ feedbackA2EndpointGoodEvent amplitude q n) :
    feedbackSourceRankArray sample ∉ sourceEndpointBadEvent amplitude q n := by
  intro hraw
  exact hgood (Or.inl (subset_toMeasurable (endpointRowLaw n) _ hraw))

theorem feedbackA2EndpointGoodEvent.target_raw
    {amplitude q : ℝ} {n : ℕ} {sample : FiniteSample n}
    (hgood : sample ∈ feedbackA2EndpointGoodEvent amplitude q n) :
    feedbackTargetRankArray sample ∉ targetEndpointBadEvent amplitude q n := by
  intro hraw
  exact hgood (Or.inr (subset_toMeasurable (endpointRowLaw n) _ hraw))

/-- Separate endpoint transport to the two actual arrays. -/
theorem finiteSampleLaw_real_feedbackA2EndpointBadEvent_le
    {amplitude q : ℝ} {n : ℕ}
    (hn : 0 < n) (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2EndpointBadEvent amplitude q n) ≤ 44 / q := by
  let S := rankSourceEndpointBadEventHull amplitude q n
  let T := rankTargetEndpointBadEventHull amplitude q n
  have hS : MeasurableSet S := measurableSet_rankSourceEndpointBadEventHull amplitude q n
  have hT : MeasurableSet T := measurableSet_rankTargetEndpointBadEventHull amplitude q n
  have hsource :
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackSourceRankArray ⁻¹' S) ≤ 22 / q := by
    rw [finiteSampleLaw_real_preimage_feedbackSourceRankArray hS]
    dsimp [S, rankSourceEndpointBadEventHull]
    change ENNReal.toReal ((endpointRowLaw n)
      (toMeasurable (endpointRowLaw n) _)) ≤ _
    rw [measure_toMeasurable]
    exact endpointRowLaw_real_sourceBadEvent_le
      hn hbuffer hfitSource hB hq
  have htarget :
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackTargetRankArray ⁻¹' T) ≤ 22 / q := by
    rw [finiteSampleLaw_real_preimage_feedbackTargetRankArray hT]
    dsimp [T, rankTargetEndpointBadEventHull]
    change ENNReal.toReal ((endpointRowLaw n)
      (toMeasurable (endpointRowLaw n) _)) ≤ _
    rw [measure_toMeasurable]
    exact endpointRowLaw_real_targetBadEvent_le
      hn hbuffer hfitTarget hB hq
  have hunion := measureReal_union_le
    (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (feedbackSourceRankArray ⁻¹' S) (feedbackTargetRankArray ⁻¹' T)
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2EndpointBadEvent amplitude q n) ≤
        (finiteSampleLaw n : Measure (FiniteSample n)).real
            (feedbackSourceRankArray ⁻¹' S) +
          (finiteSampleLaw n : Measure (FiniteSample n)).real
            (feedbackTargetRankArray ⁻¹' T) := by
      simpa [feedbackA2EndpointBadEvent, S, T] using hunion
    _ ≤ 22 / q + 22 / q := add_le_add hsource htarget
    _ = 44 / q := by ring

/-! ## The actual current event and the combined A2 event -/

/-- Raw event that the actual rank current along the safe feedback height exceeds a fixed
threshold before the elapsed horizon. -/
noncomputable def feedbackA2CurrentExcursionRaw
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (currentThreshold : ℝ) : Set (FiniteSample n) :=
  {sample | ∃ t : ℝ≥0, t < T ∧ currentThreshold <
    |feedbackRankDiscrepancy
      (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample)
      (B + (t : ℝ))|}

/-- Measurable hull of the ordinary A1 current-excursion event. -/
noncomputable def feedbackA2CurrentBadEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (currentThreshold : ℝ) : Set (FiniteSample n) :=
  toMeasurable (finiteSampleLaw n : Measure (FiniteSample n))
    (feedbackA2CurrentExcursionRaw
      (n := n) hlam0 hlamHalf B T currentThreshold)

theorem measurableSet_feedbackA2CurrentBadEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) (currentThreshold : ℝ) :
    MeasurableSet (feedbackA2CurrentBadEvent
      (n := n) hlam0 hlamHalf B T currentThreshold) :=
  measurableSet_toMeasurable _ _

theorem feedbackA2CurrentGood_bound
    {n : ℕ} {lam : ℝ} {hlam0 : 0 ≤ lam} {hlamHalf : lam < 1 / 2}
    {B currentThreshold : ℝ} {T : ℝ≥0} {sample : FiniteSample n}
    (hgood : sample ∉ feedbackA2CurrentBadEvent
      hlam0 hlamHalf B T currentThreshold)
    {t : ℝ≥0} (ht : t < T) :
    |feedbackRankDiscrepancy
      (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample)
      (B + (t : ℝ))| ≤ currentThreshold := by
  apply le_of_not_gt
  intro hlarge
  apply hgood
  exact subset_toMeasurable (finiteSampleLaw n : Measure (FiniteSample n)) _
    ⟨t, ht, hlarge⟩

/-- The actual A2 bad event: a global-cut failure, an endpoint failure, or the ordinary A1
current excursion. -/
noncomputable def feedbackA2BadEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (amplitude globalQ endpointQ B : ℝ) (T : ℝ≥0)
    (currentThreshold : ℝ) : Set (FiniteSample n) :=
  feedbackA2GlobalCutBadEvent globalQ n ∪
    (feedbackA2EndpointBadEvent amplitude endpointQ n ∪
      feedbackA2CurrentBadEvent hlam0 hlamHalf B T currentThreshold)

noncomputable def feedbackA2GoodEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (amplitude globalQ endpointQ B : ℝ) (T : ℝ≥0)
    (currentThreshold : ℝ) : Set (FiniteSample n) :=
  (feedbackA2BadEvent hlam0 hlamHalf amplitude globalQ endpointQ B T
    currentThreshold)ᶜ

theorem measurableSet_feedbackA2BadEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (amplitude globalQ endpointQ B : ℝ) (T : ℝ≥0)
    (currentThreshold : ℝ) :
    MeasurableSet (feedbackA2BadEvent
      (n := n) hlam0 hlamHalf amplitude globalQ endpointQ B T currentThreshold) := by
  simpa only [feedbackA2BadEvent] using
    (measurableSet_feedbackA2GlobalCutBadEvent globalQ n).union
      ((measurableSet_feedbackA2EndpointBadEvent amplitude endpointQ n).union
        (measurableSet_feedbackA2CurrentBadEvent
          hlam0 hlamHalf B T currentThreshold))

theorem measurableSet_feedbackA2GoodEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (amplitude globalQ endpointQ B : ℝ) (T : ℝ≥0)
    (currentThreshold : ℝ) :
    MeasurableSet (feedbackA2GoodEvent
      (n := n) hlam0 hlamHalf amplitude globalQ endpointQ B T currentThreshold) :=
  (measurableSet_feedbackA2BadEvent
    hlam0 hlamHalf amplitude globalQ endpointQ B T currentThreshold).compl

/-- The exact union bound leaves only the ordinary A1 current-excursion probability as an input. -/
theorem finiteSampleLaw_real_feedbackA2BadEvent_le
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {amplitude globalQ endpointQ B currentThreshold : ℝ} {T : ℝ≥0}
    (hn : 0 < n) (hglobalQ : 0 < globalQ)
    (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hendpointQ : 1 ≤ endpointQ) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2BadEvent hlam0 hlamHalf amplitude globalQ endpointQ B T
          currentThreshold) ≤
      18832 / globalQ + 44 / endpointQ +
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2CurrentBadEvent
            hlam0 hlamHalf B T currentThreshold) := by
  let G := feedbackA2GlobalCutBadEvent globalQ n
  let E := feedbackA2EndpointBadEvent amplitude endpointQ n
  let K := feedbackA2CurrentBadEvent (n := n) hlam0 hlamHalf B T currentThreshold
  have hGE := measureReal_union_le
    (μ := (finiteSampleLaw n : Measure (FiniteSample n))) E K
  have hAll := measureReal_union_le
    (μ := (finiteSampleLaw n : Measure (FiniteSample n))) G (E ∪ K)
  have hG := finiteSampleLaw_real_feedbackA2GlobalCutBadEvent_le hn hglobalQ
  have hE := finiteSampleLaw_real_feedbackA2EndpointBadEvent_le
    hn hbuffer hfitSource hfitTarget hB hendpointQ
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2BadEvent hlam0 hlamHalf amplitude globalQ endpointQ B T
          currentThreshold) ≤
        (finiteSampleLaw n : Measure (FiniteSample n)).real G +
          (finiteSampleLaw n : Measure (FiniteSample n)).real (E ∪ K) := by
      simpa [feedbackA2BadEvent, G, E, K] using hAll
    _ ≤ (finiteSampleLaw n : Measure (FiniteSample n)).real G +
        ((finiteSampleLaw n : Measure (FiniteSample n)).real E +
          (finiteSampleLaw n : Measure (FiniteSample n)).real K) :=
      add_le_add (le_refl _) hGE
    _ ≤ 18832 / globalQ +
        (44 / endpointQ +
          (finiteSampleLaw n : Measure (FiniteSample n)).real K) := by
      gcongr
    _ = 18832 / globalQ + 44 / endpointQ +
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2CurrentBadEvent
            hlam0 hlamHalf B T currentThreshold) := by
      simp only [K]
      ring

/-! ## Genuine shear exit and the first-hit inclusion -/

def feedbackA2ShearBadSet (B : ℝ) : Set ℝ :=
  {p | B / 8 < |p|}

theorem isOpen_feedbackA2ShearBadSet (B : ℝ) :
    IsOpen (feedbackA2ShearBadSet B) := by
  exact isOpen_lt continuous_const continuous_abs

/-- First elapsed coordinate at which the continuous safe feedback height strictly exceeds the
paper's shear window. -/
noncomputable def safeFeedbackA2ShearExitTime
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) : FiniteSample n → WithTop ℝ≥0 :=
  MeasureTheory.hittingAfter
    (fun t sample ↦ safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample)
    (feedbackA2ShearBadSet B) 0

theorem safeFeedbackA2ShearExitTime_isStoppingTime
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (safeFeedbackA2ShearExitTime (n := n) hlam0 hlamHalf B) := by
  have : Filtration.IsRightContinuous
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0) :=
    usualRevealedFiltration_isRightContinuous
      (n := n) hlam0 hlamHalf B 0
  simpa only [safeFeedbackA2ShearExitTime] using
    CountingProcess.MeasureTheory.Adapted.isStoppingTime_hittingAfter_zero_isOpen
      (safeFeedbackHeightAtElapsed_adapted
        (n := n) hlam0 hlamHalf B 0)
      (fun sample ↦ safeFeedbackHeightAtElapsed_continuous
        hlam0 hlamHalf B 0 sample)
      (isOpen_feedbackA2ShearBadSet B)

/-- Measurable event that the genuine first open shear exit occurs before the horizon. -/
noncomputable def feedbackA2ShearExitBeforeEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) : Set (FiniteSample n) :=
  {sample | safeFeedbackA2ShearExitTime
    (n := n) hlam0 hlamHalf B sample < (T : WithTop ℝ≥0)}

theorem measurableSet_feedbackA2ShearExitBeforeEvent
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) :
    MeasurableSet (feedbackA2ShearExitBeforeEvent
      (n := n) hlam0 hlamHalf B T) := by
  let ℱ := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  have hstop := safeFeedbackA2ShearExitTime_isStoppingTime
    (n := n) hlam0 hlamHalf B
  exact ℱ.le T _ (hstop.measurableSet_lt T)

/-- The paper's closed-window shear-hit event.  It is intentionally kept distinct from the
stopping-time event for the first strict open excursion. -/
noncomputable def feedbackA2ExactShearHitBeforeRaw
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) : Set (FiniteSample n) :=
  {sample | ∃ t ∈ Set.Ico (0 : ℝ≥0) T,
    |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample| = B / 8}

/-- Measurable hull of the exact closed-window hit event.  No stopping-time claim is made for
the raw event. -/
noncomputable def feedbackA2ExactShearHitBeforeHull
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) : Set (FiniteSample n) :=
  toMeasurable (finiteSampleLaw n : Measure (FiniteSample n))
    (feedbackA2ExactShearHitBeforeRaw
      (n := n) hlam0 hlamHalf B T)

theorem measurableSet_feedbackA2ExactShearHitBeforeHull
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (T : ℝ≥0) :
    MeasurableSet (feedbackA2ExactShearHitBeforeHull
      (n := n) hlam0 hlamHalf B T) :=
  measurableSet_toMeasurable _ _

private theorem safeFeedbackHeightAtElapsed_zero_start
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (sample : FiniteSample n) :
    safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 0 sample = 0 := by
  by_cases hgood : sample.NoFeedbackTies lam B 0
  · rw [sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
      hlam0 hlamHalf B 0 0 hgood]
    simpa using sample.feedbackCurve_at_x0 hlam0 hlamHalf B 0
  · simp [safeFeedbackHeightAtElapsed, hgood]

/-- Affine source and target sections remain inside the strip throughout the bulk rectangle at
the exact shear boundary. -/
private theorem feedbackA2_bulk_section_bounds
    {n : ℕ} {B p x : ℝ} (hB : 0 ≤ B)
    (hxLower : B ≤ x) (hxUpper : x ≤ (n : ℝ) - B)
    (hp : |p| = B / 8) :
    ( ∀ u : UnitMark, 0 ≤ x - p * (1 - (u : ℝ))) ∧
    (∀ u : UnitMark, x - p * (1 - (u : ℝ)) ≤ n) ∧
    (∀ v : UnitMark, 0 ≤ x + p * (1 + (v : ℝ))) ∧
    (∀ v : UnitMark, x + p * (1 + (v : ℝ)) ≤ n) := by
  have hB8 : 0 ≤ B / 8 := by positivity
  constructor
  · intro u
    have hu0 : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
    have hu1 : 1 - (u : ℝ) ≤ 1 := by linarith [u.property.1]
    have hterm : |p * (1 - (u : ℝ))| ≤ B / 8 := by
      rw [abs_mul, abs_of_nonneg hu0, hp]
      nlinarith
    nlinarith [le_abs_self (p * (1 - (u : ℝ)))]
  · constructor
    · intro u
      have hu0 : 0 ≤ 1 - (u : ℝ) := sub_nonneg.mpr u.property.2
      have hu1 : 1 - (u : ℝ) ≤ 1 := by linarith [u.property.1]
      have hterm : |p * (1 - (u : ℝ))| ≤ B / 8 := by
        rw [abs_mul, abs_of_nonneg hu0, hp]
        nlinarith
      have hlow := neg_le_of_abs_le hterm
      nlinarith
    · constructor
      · intro v
        have hv0 : 0 ≤ 1 + (v : ℝ) := by linarith [v.property.1]
        have hv2 : 1 + (v : ℝ) ≤ 2 := by linarith [v.property.2]
        have hterm : |p * (1 + (v : ℝ))| ≤ B / 4 := by
          rw [abs_mul, abs_of_nonneg hv0, hp]
          nlinarith
        have hlow := neg_le_of_abs_le hterm
        nlinarith
      · intro v
        have hv0 : 0 ≤ 1 + (v : ℝ) := by linarith [v.property.1]
        have hv2 : 1 + (v : ℝ) ≤ 2 := by linarith [v.property.2]
        have hterm : |p * (1 + (v : ℝ))| ≤ B / 4 := by
          rw [abs_mul, abs_of_nonneg hv0, hp]
          nlinarith
        nlinarith [le_abs_self (p * (1 + (v : ℝ)))]

/-- A genuine first shear exit is forced by an actual global-cut failure or by the ordinary A1
current-excursion event.  The premise on the current threshold is an A1 input; it is not the A2
survival conclusion. -/
theorem feedbackA2ShearExitBefore_subset_globalCut_or_currentBad
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B globalQ currentThreshold : ℝ} {T : ℝ≥0}
    (hn : 0 < n) (hB : 0 < B)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + currentThreshold < B / 4) :
    feedbackA2ShearExitBeforeEvent
        (n := n) hlam0 hlamHalf B T ⊆
      feedbackA2GlobalCutBadEvent globalQ n ∪
        feedbackA2CurrentBadEvent
          hlam0 hlamHalf B T currentThreshold := by
  intro sample hhit
  by_cases hcut : sample ∈ feedbackA2GlobalCutBadEvent globalQ n
  · exact Or.inl hcut
  by_cases hcurrent : sample ∈
      feedbackA2CurrentBadEvent hlam0 hlamHalf B T currentThreshold
  · exact Or.inr hcurrent
  exfalso
  have hwitness : ∃ t ∈ Set.Ico (0 : ℝ≥0) T,
      safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample ∈
        feedbackA2ShearBadSet B := by
    simpa only [feedbackA2ShearExitBeforeEvent, safeFeedbackA2ShearExitTime,
      Set.mem_ofPred_eq] using
        (MeasureTheory.hittingAfter_lt_iff.mp hhit)
  obtain ⟨t, ht, htShear⟩ := hwitness
  let height : ℝ≥0 → ℝ := fun s ↦
    safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 s sample
  have hcont : Continuous height :=
    safeFeedbackHeightAtElapsed_continuous hlam0 hlamHalf B 0 sample
  have hheight0 : height 0 = 0 :=
    safeFeedbackHeightAtElapsed_zero_start hlam0 hlamHalf B sample
  have htarget : B / 8 ∈ Set.Icc |height 0| |height t| := by
    rw [hheight0, abs_zero]
    exact ⟨div_nonneg hB.le (by norm_num), htShear.le⟩
  obtain ⟨s, hs, hsHeight⟩ :=
    (intermediate_value_Icc ht.1 hcont.abs.continuousOn) htarget
  have hsT : s < T := hs.2.trans_lt ht.2
  have hsLower : B ≤ B + (s : ℝ) := by
    exact le_add_of_nonneg_right s.2
  have hsUpper : B + (s : ℝ) ≤ (n : ℝ) - B := by
    have hst : (s : ℝ) < (T : ℝ) := by exact_mod_cast hsT
    linarith
  have hsections := feedbackA2_bulk_section_bounds hB.le hsLower hsUpper hsHeight
  change |height s| = B / 8 at hsHeight
  have hcomponents := first_hit_cut_component_exceeds hn
    (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
    hsections.1 hsections.2.1 hsections.2.2.1 hsections.2.2.2
    (p := height s) (x := B + (s : ℝ)) (hit := B / 4)
    (by
      rw [hsHeight]
      ring)
    (sourceThreshold := (globalQ + 32) * Real.sqrt n)
    (targetThreshold := (globalQ + 32) * Real.sqrt n)
    (currentThreshold := currentThreshold)
    (by nlinarith [hthreshold])
  have hglobalGood : sample ∈ feedbackA2GlobalCutGoodEvent globalQ n := hcut
  have hsourceSup := feedbackA2GlobalCutGoodEvent.source_bound hglobalGood
  have htargetSup := feedbackA2GlobalCutGoodEvent.target_bound hglobalGood
  have hcurrentBound := feedbackA2CurrentGood_bound hcurrent hsT
  rcases hcomponents with hsource | htarget | hK
  · exact (not_lt_of_ge ((abs_sourceCutDefect_le_globalSourceCutSup
      (rankStripLaw n : Measure (ℝ × UnitMark))
      (feedbackSourceRankArray sample) (height s) (B + (s : ℝ))).trans
        hsourceSup)) hsource
  · exact (not_lt_of_ge ((abs_targetCutDefect_le_globalTargetCutSup
      (rankStripLaw n : Measure (ℝ × UnitMark))
      (feedbackTargetRankArray sample) (height s) (B + (s : ℝ))).trans
        htargetSup)) htarget
  · exact (not_lt_of_ge hcurrentBound) hK

/-- The paper's exact boundary-hit event satisfies the same trichotomy, including a tangential
touch that need not enter the strict open bad set. -/
theorem feedbackA2ExactShearHitBeforeRaw_subset_globalCut_or_currentBad
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B globalQ currentThreshold : ℝ} {T : ℝ≥0}
    (hn : 0 < n) (hB : 0 < B)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + currentThreshold < B / 4) :
    feedbackA2ExactShearHitBeforeRaw
        (n := n) hlam0 hlamHalf B T ⊆
      feedbackA2GlobalCutBadEvent globalQ n ∪
        feedbackA2CurrentBadEvent
          hlam0 hlamHalf B T currentThreshold := by
  intro sample hhit
  by_cases hcut : sample ∈ feedbackA2GlobalCutBadEvent globalQ n
  · exact Or.inl hcut
  by_cases hcurrent : sample ∈
      feedbackA2CurrentBadEvent hlam0 hlamHalf B T currentThreshold
  · exact Or.inr hcurrent
  exfalso
  obtain ⟨t, ht, htHeight⟩ := hhit
  have htLower : B ≤ B + (t : ℝ) :=
    le_add_of_nonneg_right t.2
  have htUpper : B + (t : ℝ) ≤ (n : ℝ) - B := by
    have htT : (t : ℝ) < (T : ℝ) := by exact_mod_cast ht.2
    linarith
  have hsections := feedbackA2_bulk_section_bounds hB.le htLower htUpper htHeight
  have hcomponents := first_hit_cut_component_exceeds hn
    (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
    hsections.1 hsections.2.1 hsections.2.2.1 hsections.2.2.2
    (p := safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample)
    (x := B + (t : ℝ)) (hit := B / 4)
    (by rw [htHeight]; ring)
    (sourceThreshold := (globalQ + 32) * Real.sqrt n)
    (targetThreshold := (globalQ + 32) * Real.sqrt n)
    (currentThreshold := currentThreshold)
    (by nlinarith [hthreshold])
  have hglobalGood : sample ∈ feedbackA2GlobalCutGoodEvent globalQ n := hcut
  have hsourceSup := feedbackA2GlobalCutGoodEvent.source_bound hglobalGood
  have htargetSup := feedbackA2GlobalCutGoodEvent.target_bound hglobalGood
  have hcurrentBound := feedbackA2CurrentGood_bound hcurrent ht.2
  rcases hcomponents with hsource | htarget | hK
  · exact (not_lt_of_ge ((abs_sourceCutDefect_le_globalSourceCutSup
      (rankStripLaw n : Measure (ℝ × UnitMark))
      (feedbackSourceRankArray sample)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample)
      (B + (t : ℝ))).trans hsourceSup)) hsource
  · exact (not_lt_of_ge ((abs_targetCutDefect_le_globalTargetCutSup
      (rankStripLaw n : Measure (ℝ × UnitMark))
      (feedbackTargetRankArray sample)
      (safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample)
      (B + (t : ℝ))).trans htargetSup)) htarget
  · exact (not_lt_of_ge hcurrentBound) hK

/-- Avoiding the raw exact-hit event gives the strict closed-window shear bound. -/
theorem abs_safeFeedbackHeightAtElapsed_lt_of_not_exactShearHit
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B : ℝ} (hB : 0 < B) {T : ℝ≥0} {sample : FiniteSample n}
    (hnoHit : sample ∉ feedbackA2ExactShearHitBeforeRaw
      hlam0 hlamHalf B T) {t : ℝ≥0} (ht : t < T) :
    |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample| < B / 8 := by
  by_contra hnot
  have hge : B / 8 ≤
      |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample| :=
    le_of_not_gt hnot
  let height : ℝ≥0 → ℝ := fun s ↦
    safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 s sample
  have hcont : Continuous height :=
    safeFeedbackHeightAtElapsed_continuous hlam0 hlamHalf B 0 sample
  have hheight0 : height 0 = 0 :=
    safeFeedbackHeightAtElapsed_zero_start hlam0 hlamHalf B sample
  have htarget : B / 8 ∈ Set.Icc |height 0| |height t| := by
    rw [hheight0, abs_zero]
    exact ⟨div_nonneg hB.le (by norm_num), hge⟩
  obtain ⟨s, hs, hsHeight⟩ :=
    (intermediate_value_Icc (show (0 : ℝ≥0) ≤ t from bot_le)
      hcont.abs.continuousOn) htarget
  apply hnoHit
  exact ⟨s, ⟨hs.1, hs.2.trans_lt ht⟩, hsHeight⟩

/-- Outer-probability bound for the measurable hull of the paper's exact shear-hit event. -/
theorem finiteSampleLaw_real_feedbackA2ExactShearHitBeforeHull_le
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B globalQ currentThreshold : ℝ} {T : ℝ≥0}
    (hn : 0 < n) (hglobalQ : 0 < globalQ) (hB : 0 < B)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + currentThreshold < B / 4) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2ExactShearHitBeforeHull
          (n := n) hlam0 hlamHalf B T) ≤
      18832 / globalQ +
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2CurrentBadEvent
            hlam0 hlamHalf B T currentThreshold) := by
  let G := feedbackA2GlobalCutBadEvent globalQ n
  let K := feedbackA2CurrentBadEvent (n := n) hlam0 hlamHalf B T currentThreshold
  have hsubset := feedbackA2ExactShearHitBeforeRaw_subset_globalCut_or_currentBad
    hlam0 hlamHalf hn hB hRight hthreshold
  have hraw :
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2ExactShearHitBeforeRaw
            (n := n) hlam0 hlamHalf B T) ≤
        (finiteSampleLaw n : Measure (FiniteSample n)).real (G ∪ K) :=
    measureReal_mono hsubset
      (measure_ne_top (finiteSampleLaw n : Measure (FiniteSample n)) (G ∪ K))
  have hhull :
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2ExactShearHitBeforeHull
            (n := n) hlam0 hlamHalf B T) =
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2ExactShearHitBeforeRaw
            (n := n) hlam0 hlamHalf B T) := by
    change ENNReal.toReal ((finiteSampleLaw n : Measure (FiniteSample n))
      (toMeasurable (finiteSampleLaw n : Measure (FiniteSample n)) _)) = _
    rw [measure_toMeasurable]
    rfl
  have hunion := measureReal_union_le
    (μ := (finiteSampleLaw n : Measure (FiniteSample n))) G K
  have hglobal := finiteSampleLaw_real_feedbackA2GlobalCutBadEvent_le hn hglobalQ
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2ExactShearHitBeforeHull
          (n := n) hlam0 hlamHalf B T) =
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2ExactShearHitBeforeRaw
            (n := n) hlam0 hlamHalf B T) := hhull
    _ ≤ (finiteSampleLaw n : Measure (FiniteSample n)).real (G ∪ K) := hraw
    _ ≤ (finiteSampleLaw n : Measure (FiniteSample n)).real G +
        (finiteSampleLaw n : Measure (FiniteSample n)).real K := hunion
    _ ≤ 18832 / globalQ +
        (finiteSampleLaw n : Measure (FiniteSample n)).real K :=
      add_le_add hglobal (le_refl _)
    _ = 18832 / globalQ +
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2CurrentBadEvent
            hlam0 hlamHalf B T currentThreshold) := by
      rfl

/-- Probability form of the first-hit inclusion.  The second summand is exactly the still-needed
A1 current control; no shear-survival probability is assumed. -/
theorem finiteSampleLaw_real_feedbackA2ShearExitBeforeEvent_le
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {B globalQ currentThreshold : ℝ} {T : ℝ≥0}
    (hn : 0 < n) (hglobalQ : 0 < globalQ) (hB : 0 < B)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + currentThreshold < B / 4) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2ShearExitBeforeEvent
          (n := n) hlam0 hlamHalf B T) ≤
      18832 / globalQ +
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2CurrentBadEvent
            hlam0 hlamHalf B T currentThreshold) := by
  let G := feedbackA2GlobalCutBadEvent globalQ n
  let K := feedbackA2CurrentBadEvent (n := n) hlam0 hlamHalf B T currentThreshold
  have hsubset := feedbackA2ShearExitBefore_subset_globalCut_or_currentBad
    hlam0 hlamHalf hn hB hRight hthreshold
  have hmono :
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2ShearExitBeforeEvent
            (n := n) hlam0 hlamHalf B T) ≤
        (finiteSampleLaw n : Measure (FiniteSample n)).real (G ∪ K) := by
    exact measureReal_mono hsubset
      (measure_ne_top (finiteSampleLaw n : Measure (FiniteSample n)) (G ∪ K))
  have hunion := measureReal_union_le
    (μ := (finiteSampleLaw n : Measure (FiniteSample n))) G K
  have hglobal := finiteSampleLaw_real_feedbackA2GlobalCutBadEvent_le hn hglobalQ
  calc
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2ShearExitBeforeEvent
          (n := n) hlam0 hlamHalf B T) ≤
        (finiteSampleLaw n : Measure (FiniteSample n)).real (G ∪ K) := hmono
    _ ≤ (finiteSampleLaw n : Measure (FiniteSample n)).real G +
        (finiteSampleLaw n : Measure (FiniteSample n)).real K := hunion
    _ ≤ 18832 / globalQ +
        (finiteSampleLaw n : Measure (FiniteSample n)).real K :=
      add_le_add hglobal (le_refl _)
    _ = 18832 / globalQ +
        (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2CurrentBadEvent
            hlam0 hlamHalf B T currentThreshold) := by
      rfl

/-- Final probability combination with an explicit ordinary A1 premise. -/
theorem finiteSampleLaw_real_feedbackA2BadEvent_le_of_current
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {amplitude globalQ endpointQ B currentThreshold currentTail : ℝ} {T : ℝ≥0}
    (hn : 0 < n) (hglobalQ : 0 < globalQ)
    (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hendpointQ : 1 ≤ endpointQ)
    (hcurrent :
      (finiteSampleLaw n : Measure (FiniteSample n)).real
          (feedbackA2CurrentBadEvent
            hlam0 hlamHalf B T currentThreshold) ≤ currentTail) :
    (finiteSampleLaw n : Measure (FiniteSample n)).real
        (feedbackA2BadEvent hlam0 hlamHalf amplitude globalQ endpointQ B T
          currentThreshold) ≤
      18832 / globalQ + 44 / endpointQ + currentTail := by
  exact (finiteSampleLaw_real_feedbackA2BadEvent_le
    hlam0 hlamHalf hn hglobalQ hbuffer hfitSource hfitTarget hB hendpointQ).trans
      (add_le_add (le_refl _) hcurrent)

/-- The combined actual A2 good event directly gives the paper's strict shear survival on the
closed window.  The endpoint component remains part of the combined event, although only the
global-cut and current components are needed for this conclusion. -/
theorem feedbackA2GoodEvent.abs_safeFeedbackHeightAtElapsed_lt
    {n : ℕ} {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    {amplitude globalQ endpointQ B currentThreshold : ℝ} {T : ℝ≥0}
    {sample : FiniteSample n}
    (hn : 0 < n) (hB : 0 < B)
    (hRight : B + (T : ℝ) ≤ (n : ℝ) - B)
    (hthreshold :
      2 * (globalQ + 32) * Real.sqrt n + currentThreshold < B / 4)
    (hgood : sample ∈ feedbackA2GoodEvent
      hlam0 hlamHalf amplitude globalQ endpointQ B T currentThreshold)
    {t : ℝ≥0} (ht : t < T) :
    |safeFeedbackHeightAtElapsed hlam0 hlamHalf B 0 t sample| < B / 8 := by
  have hnotGlobal : sample ∉ feedbackA2GlobalCutBadEvent globalQ n := by
    intro hbad
    exact hgood (Or.inl hbad)
  have hnotCurrent : sample ∉
      feedbackA2CurrentBadEvent hlam0 hlamHalf B T currentThreshold := by
    intro hbad
    exact hgood (Or.inr (Or.inr hbad))
  have hnoExact : sample ∉
      feedbackA2ExactShearHitBeforeRaw hlam0 hlamHalf B T := by
    intro hhit
    have hbad := feedbackA2ExactShearHitBeforeRaw_subset_globalCut_or_currentBad
      hlam0 hlamHalf hn hB hRight hthreshold hhit
    exact hbad.elim hnotGlobal hnotCurrent
  exact abs_safeFeedbackHeightAtElapsed_lt_of_not_exactShearHit
    hlam0 hlamHalf hB hnoExact ht

/-! ## Actual endpoint consequence -/

theorem feedbackA2EndpointGoodEvent.abs_actual_endpoint_height_le
    {amplitude q currentBound : ℝ} {n : ℕ} (hn : 0 < n)
    {sample : FiniteSample n}
    (hbuffer : 0 < endpointBuffer amplitude n)
    (hfitSource : 9 * endpointBuffer amplitude n / 8 ≤ (n : ℝ))
    (hfitTarget : 5 * endpointBuffer amplitude n / 4 ≤ (n : ℝ))
    (hB : 1 ≤ endpointBuffer amplitude n) (hq : 1 ≤ q)
    (hgood : sample ∈ feedbackA2EndpointGoodEvent amplitude q n)
    {p : ℝ} (hp : |p| ≤ endpointBuffer amplitude n / 8)
    (hcurrent :
      |feedbackRankDiscrepancy
        (feedbackSourceRankArray sample) (feedbackTargetRankArray sample) p
        ((n : ℝ) - endpointBuffer amplitude n)| ≤ currentBound) :
    |p| ≤ endpointEnvelopeCoefficient q * endpointScale amplitude n +
      currentBound / 2 := by
  exact abs_endpoint_shear_parameter_le_of_endpoint_good hn
    (feedbackSourceRankArray sample) (feedbackTargetRankArray sample)
    hbuffer hfitSource hfitTarget hB hq hp
    (feedbackA2EndpointGoodEvent.source_raw hgood)
    (feedbackA2EndpointGoodEvent.target_raw hgood) hcurrent

end OTSelector
