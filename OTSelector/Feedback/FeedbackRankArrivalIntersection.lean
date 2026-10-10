import OTSelector.Feedback.FeedbackRankArrival
import OTSelector.Feedback.FeedbackRegularitySurvival

/-!
# Rank arrivals as final-graph intersection order statistics

The safe source and target event times record only labels revealed strictly after the initial
coordinate.  Consequently their `k`-th order statistics correspond to the final intersection
arrays at the shifted indices `initialSeen.card + k`, rather than at `k` itself.  This file makes
that offset explicit, proves the finite and top branches, and exposes the strict source-first and
target-first events at the left rank-arrival stopping sigma algebra.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

namespace CountingProcess

variable {Omega : Type*} {n : ℕ}

/-! ## Generic order and stopping-time helpers -/

/-- A sorted finite tuple is below a threshold exactly when its zero-based rank is smaller than
the number of tuple entries below that threshold. -/
theorem tupleSort_apply_le_iff_lt_card
    {alpha : Type*} [LinearOrder alpha] (values : Fin n → alpha) (k : Fin n) (a : alpha) :
    values (Tuple.sort values k) ≤ a ↔
      k.val < (Finset.univ.filter fun i ↦ values i ≤ a).card := by
  classical
  have hsorted : Monotone (values ∘ Tuple.sort values) := Tuple.monotone_sort values
  have horder := Tuple.lt_card_le_iff_apply_le_of_monotone
    (j := k) (a := a) hsorted
  have hcard :
      (Finset.univ.filter fun i : Fin n ↦ values (Tuple.sort values i) ≤ a).card =
        (Finset.univ.filter fun i : Fin n ↦ values i ≤ a).card := by
    apply Finset.card_equiv (Tuple.sort values)
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simpa only [Function.comp_apply, hcard] using horder.symm

/-- For two stopping times, the strict orientation event is known at their minimum. -/
theorem measurableSet_lt_stopping_time_min
    [MeasurableSpace Omega]
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega)}
    {sigma tau : Omega → WithTop ℝ≥0}
    (hsigma : IsStoppingTime F sigma) (htau : IsStoppingTime F tau) :
    MeasurableSet[(hsigma.min htau).measurableSpace]
      {omega | sigma omega < tau omega} := by
  have hle : MeasurableSet[(hsigma.min htau).measurableSpace]
      {omega | sigma omega ≤ tau omega} :=
    hsigma.measurableSet_stopping_time_le_min htau
  have heq : MeasurableSet[(hsigma.min htau).measurableSpace]
      {omega | sigma omega = tau omega} :=
    hsigma.measurableSet_eq_stopping_time_min htau
  have hset : {omega | sigma omega < tau omega} =
      {omega | sigma omega ≤ tau omega} \ {omega | sigma omega = tau omega} := by
    ext omega
    simp only [mem_ofPred_eq, mem_sdiff]
    exact lt_iff_le_and_ne
  rw [hset]
  exact hle.diff heq

end CountingProcess

namespace FiniteSample

variable {n : ℕ}

/-! ## Counts after the initial coordinate -/

/-- On the no-tie event, adding the initially seen source labels to the safe post-initial source
count recovers the final-graph source intersection count at the current coordinate. -/
theorem safeSourceCount_add_initialSeenSource_card_eq_sourceIntersectionCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    safeSourceCount hlam0 hlamHalf x0 p0 t sample +
        (sample.initialSeenSource x0 p0).card =
      sample.sourceIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (elapsedFeedbackCoordinate x0 t) := by
  classical
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t
  have hsubset : sample.initialSeenSource x0 p0 ⊆ state.seenSource := by
    intro i hi
    apply sample.mem_feedbackState_seenSource_mono lam x0 p0 i (Nat.zero_le _)
    simpa [state, feedbackStateAtElapsed, feedbackState_zero,
      initialFeedbackState] using hi
  have hcard :
      (state.seenSource \ sample.initialSeenSource x0 p0).card +
          (sample.initialSeenSource x0 p0).card = state.seenSource.card := by
    have h := Finset.card_sdiff_add_card state.seenSource
      (sample.initialSeenSource x0 p0)
    rwa [Finset.union_eq_left.mpr hsubset] at h
  rw [safeSourceCount_eq_card_diff]
  simp only [hNoTie, ite_true]
  rw [hcard]
  exact feedbackStateAtElapsed_seenSource_card_eq_sourceIntersectionCount
    sample hlam0 hlamHalf x0 p0 t

/-- On the no-tie event, adding the initially seen target labels to the safe post-initial target
count recovers the final-graph target intersection count at the current coordinate. -/
theorem safeTargetCount_add_initialSeenTarget_card_eq_targetIntersectionCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    safeTargetCount hlam0 hlamHalf x0 p0 t sample +
        (sample.initialSeenTarget x0 p0).card =
      sample.targetIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (elapsedFeedbackCoordinate x0 t) := by
  classical
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t
  have hsubset : sample.initialSeenTarget x0 p0 ⊆ state.seenTarget := by
    intro j hj
    apply sample.mem_feedbackState_seenTarget_mono lam x0 p0 j (Nat.zero_le _)
    simpa [state, feedbackStateAtElapsed, feedbackState_zero,
      initialFeedbackState] using hj
  have hcard :
      (state.seenTarget \ sample.initialSeenTarget x0 p0).card +
          (sample.initialSeenTarget x0 p0).card = state.seenTarget.card := by
    have h := Finset.card_sdiff_add_card state.seenTarget
      (sample.initialSeenTarget x0 p0)
    rwa [Finset.union_eq_left.mpr hsubset] at h
  rw [safeTargetCount_eq_card_diff]
  simp only [hNoTie, ite_true]
  rw [hcard]
  exact feedbackStateAtElapsed_seenTarget_card_eq_targetIntersectionCount
    sample hlam0 hlamHalf x0 p0 t

/-! ## Shifted ranks and final-intersection order statistics -/

/-- The zero-based rank in the full source-intersection array corresponding to a post-initial
source rank. -/
noncomputable def sourceRankIntersectionOffset
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n) : ℕ :=
  (sample.initialSeenSource x0 p0).card + k.val

/-- The zero-based rank in the full target-intersection array corresponding to a post-initial
target rank. -/
noncomputable def targetRankIntersectionOffset
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n) : ℕ :=
  (sample.initialSeenTarget x0 p0).card + k.val

/-- A bounded source offset as an index of the full source-intersection array. -/
noncomputable def sourceRankIntersectionIndex
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (h : sourceRankIntersectionOffset x0 p0 sample k < n) : Fin n :=
  ⟨sourceRankIntersectionOffset x0 p0 sample k, h⟩

/-- A bounded target offset as an index of the full target-intersection array. -/
noncomputable def targetRankIntersectionIndex
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (h : targetRankIntersectionOffset x0 p0 sample k < n) : Fin n :=
  ⟨targetRankIntersectionOffset x0 p0 sample k, h⟩

/-- The `r`-th source intersection of the final feedback graph. -/
noncomputable def sourceIntersectionOrderStatistic
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (r : Fin n) : ℝ :=
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let values := fun i : Fin n ↦ sample.sourceIntersection graph i
  values (Tuple.sort values r)

/-- The `r`-th target intersection of the final feedback graph. -/
noncomputable def targetIntersectionOrderStatistic
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (r : Fin n) : ℝ :=
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let values := fun j : Fin n ↦ sample.targetIntersection graph j
  values (Tuple.sort values r)

/-- Elapsed coordinate of a source-intersection order statistic.  `toNNReal` is harmless for the
shifted post-initial ranks below, which are proved to lie strictly to the right of `x0`. -/
noncomputable def sourceIntersectionOrderStatisticElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (r : Fin n) : ℝ≥0 :=
  Real.toNNReal
    (sourceIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample r - x0)

/-- Elapsed coordinate of a target-intersection order statistic. -/
noncomputable def targetIntersectionOrderStatisticElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (r : Fin n) : ℝ≥0 :=
  Real.toNNReal
    (targetIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample r - x0)

theorem initialSeenSource_card_eq_sourceIntersectionCount_at_initial
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) :
    (sample.initialSeenSource x0 p0).card =
      sample.sourceIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0) x0 := by
  rw [sample.initialSeenSource_eq_sourceIntersection_filter
    hlam0 hlamHalf x0 p0]
  rfl

theorem initialSeenTarget_card_eq_targetIntersectionCount_at_initial
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) :
    (sample.initialSeenTarget x0 p0).card =
      sample.targetIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0) x0 := by
  rw [sample.initialSeenTarget_eq_targetIntersection_filter
    hlam0 hlamHalf x0 p0]
  rfl

/-- Threshold characterization of a source order statistic in elapsed coordinates. -/
theorem sourceIntersectionOrderStatisticElapsed_le_iff_lt_sourceIntersectionCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (r : Fin n) (t : ℝ≥0) :
    sourceIntersectionOrderStatisticElapsed hlam0 hlamHalf x0 p0 sample r ≤ t ↔
      r.val < sample.sourceIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (elapsedFeedbackCoordinate x0 t) := by
  classical
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let values := fun i : Fin n ↦ sample.sourceIntersection graph i
  have hsort := CountingProcess.tupleSort_apply_le_iff_lt_card values r
    (elapsedFeedbackCoordinate x0 t)
  have hcoordinate :
      sourceIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample r ≤
          elapsedFeedbackCoordinate x0 t ↔
        r.val < sample.sourceIntersectionCount graph
          (elapsedFeedbackCoordinate x0 t) := by
    simpa only [sourceIntersectionOrderStatistic, graph, values,
      sourceIntersectionCount] using hsort
  rw [sourceIntersectionOrderStatisticElapsed, Real.toNNReal_le_iff_le_coe]
  calc
    sourceIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample r - x0 ≤ (t : ℝ) ↔
        sourceIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample r ≤
          elapsedFeedbackCoordinate x0 t := by
      simp only [elapsedFeedbackCoordinate]
      constructor <;> intro h <;> linarith
    _ ↔ _ := hcoordinate

/-- Threshold characterization of a target order statistic in elapsed coordinates. -/
theorem targetIntersectionOrderStatisticElapsed_le_iff_lt_targetIntersectionCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (r : Fin n) (t : ℝ≥0) :
    targetIntersectionOrderStatisticElapsed hlam0 hlamHalf x0 p0 sample r ≤ t ↔
      r.val < sample.targetIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (elapsedFeedbackCoordinate x0 t) := by
  classical
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let values := fun j : Fin n ↦ sample.targetIntersection graph j
  have hsort := CountingProcess.tupleSort_apply_le_iff_lt_card values r
    (elapsedFeedbackCoordinate x0 t)
  have hcoordinate :
      targetIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample r ≤
          elapsedFeedbackCoordinate x0 t ↔
        r.val < sample.targetIntersectionCount graph
          (elapsedFeedbackCoordinate x0 t) := by
    simpa only [targetIntersectionOrderStatistic, graph, values,
      targetIntersectionCount] using hsort
  rw [targetIntersectionOrderStatisticElapsed, Real.toNNReal_le_iff_le_coe]
  calc
    targetIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample r - x0 ≤ (t : ℝ) ↔
        targetIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample r ≤
          elapsedFeedbackCoordinate x0 t := by
      simp only [elapsedFeedbackCoordinate]
      constructor <;> intro h <;> linarith
    _ ↔ _ := hcoordinate

/-- The actual source rank-time threshold is the final-intersection count threshold at the shifted
rank. -/
theorem sourceRankEventTime_le_iff_lt_sourceIntersectionCount_offset
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n) (t : ℝ≥0)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≤ (t : WithTop ℝ≥0) ↔
      sourceRankIntersectionOffset x0 p0 sample k <
        sample.sourceIntersectionCount
          (sample.feedbackGraph hlam0 hlamHalf x0 p0)
          (elapsedFeedbackCoordinate x0 t) := by
  rw [sourceRankEventTime_le_iff_lt_safeSourceCount]
  have hcount := safeSourceCount_add_initialSeenSource_card_eq_sourceIntersectionCount
    hlam0 hlamHalf x0 p0 t sample hNoTie
  simp only [sourceRankIntersectionOffset]
  omega

/-- The actual target rank-time threshold is the final-intersection count threshold at the shifted
rank. -/
theorem targetRankEventTime_le_iff_lt_targetIntersectionCount_offset
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n) (t : ℝ≥0)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    targetRankEventTime hlam0 hlamHalf x0 p0 k sample ≤ (t : WithTop ℝ≥0) ↔
      targetRankIntersectionOffset x0 p0 sample k <
        sample.targetIntersectionCount
          (sample.feedbackGraph hlam0 hlamHalf x0 p0)
          (elapsedFeedbackCoordinate x0 t) := by
  rw [targetRankEventTime_le_iff_lt_safeTargetCount]
  have hcount := safeTargetCount_add_initialSeenTarget_card_eq_targetIntersectionCount
    hlam0 hlamHalf x0 p0 t sample hNoTie
  simp only [targetRankIntersectionOffset]
  omega

theorem sourceIntersectionCount_le_card
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 x : ℝ) (sample : FiniteSample n) :
    sample.sourceIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0) x ≤ n := by
  unfold sourceIntersectionCount
  simpa using Finset.card_le_card
    (Finset.filter_subset (fun i : Fin n ↦
      sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤ x)
      Finset.univ)

theorem targetIntersectionCount_le_card
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 x : ℝ) (sample : FiniteSample n) :
    sample.targetIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0) x ≤ n := by
  unfold targetIntersectionCount
  simpa using Finset.card_le_card
    (Finset.filter_subset (fun j : Fin n ↦
      sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j ≤ x)
      Finset.univ)

/-- Every in-bounds shifted source rank lies strictly to the right of the initial coordinate. -/
theorem sourceIntersectionOrderStatistic_gt_initial_of_offset_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hOffset : sourceRankIntersectionOffset x0 p0 sample k < n) :
    x0 < sourceIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample
      (sourceRankIntersectionIndex x0 p0 sample k hOffset) := by
  classical
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let values := fun i : Fin n ↦ sample.sourceIntersection graph i
  let r := sourceRankIntersectionIndex x0 p0 sample k hOffset
  by_contra hnot
  have hle : values (Tuple.sort values r) ≤ x0 := by
    exact le_of_not_gt (by simpa [sourceIntersectionOrderStatistic, graph, values, r] using hnot)
  have hrlt : r.val < (Finset.univ.filter fun i : Fin n ↦ values i ≤ x0).card :=
    (CountingProcess.tupleSort_apply_le_iff_lt_card values r x0).mp hle
  have hinitial := initialSeenSource_card_eq_sourceIntersectionCount_at_initial
    hlam0 hlamHalf x0 p0 sample
  have hcard : (Finset.univ.filter fun i : Fin n ↦ values i ≤ x0).card =
      (sample.initialSeenSource x0 p0).card := by
    rw [hinitial]
    rfl
  rw [hcard] at hrlt
  change sourceRankIntersectionOffset x0 p0 sample k <
    (sample.initialSeenSource x0 p0).card at hrlt
  simp only [sourceRankIntersectionOffset] at hrlt
  omega

/-- Every in-bounds shifted target rank lies strictly to the right of the initial coordinate. -/
theorem targetIntersectionOrderStatistic_gt_initial_of_offset_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hOffset : targetRankIntersectionOffset x0 p0 sample k < n) :
    x0 < targetIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample
      (targetRankIntersectionIndex x0 p0 sample k hOffset) := by
  classical
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let values := fun j : Fin n ↦ sample.targetIntersection graph j
  let r := targetRankIntersectionIndex x0 p0 sample k hOffset
  by_contra hnot
  have hle : values (Tuple.sort values r) ≤ x0 := by
    exact le_of_not_gt (by simpa [targetIntersectionOrderStatistic, graph, values, r] using hnot)
  have hrlt : r.val < (Finset.univ.filter fun j : Fin n ↦ values j ≤ x0).card :=
    (CountingProcess.tupleSort_apply_le_iff_lt_card values r x0).mp hle
  have hinitial := initialSeenTarget_card_eq_targetIntersectionCount_at_initial
    hlam0 hlamHalf x0 p0 sample
  have hcard : (Finset.univ.filter fun j : Fin n ↦ values j ≤ x0).card =
      (sample.initialSeenTarget x0 p0).card := by
    rw [hinitial]
    rfl
  rw [hcard] at hrlt
  change targetRankIntersectionOffset x0 p0 sample k <
    (sample.initialSeenTarget x0 p0).card at hrlt
  simp only [targetRankIntersectionOffset] at hrlt
  omega

/-- An in-bounds source post-initial rank time is exactly the corresponding shifted order
statistic of the final feedback-graph source intersections. -/
theorem sourceRankEventTime_eq_sourceIntersectionOrderStatisticElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hOffset : sourceRankIntersectionOffset x0 p0 sample k < n) :
    sourceRankEventTime hlam0 hlamHalf x0 p0 k sample =
      (sourceIntersectionOrderStatisticElapsed hlam0 hlamHalf x0 p0 sample
        (sourceRankIntersectionIndex x0 p0 sample k hOffset) : WithTop ℝ≥0) := by
  let r := sourceRankIntersectionIndex x0 p0 sample k hOffset
  let elapsed := sourceIntersectionOrderStatisticElapsed
    hlam0 hlamHalf x0 p0 sample r
  have hthreshold : ∀ t : ℝ≥0,
      sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≤ (t : WithTop ℝ≥0) ↔
        elapsed ≤ t := by
    intro t
    calc
      sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≤ (t : WithTop ℝ≥0) ↔
          sourceRankIntersectionOffset x0 p0 sample k <
            sample.sourceIntersectionCount
              (sample.feedbackGraph hlam0 hlamHalf x0 p0)
              (elapsedFeedbackCoordinate x0 t) :=
        sourceRankEventTime_le_iff_lt_sourceIntersectionCount_offset
          hlam0 hlamHalf x0 p0 sample k t hNoTie
      _ ↔ r.val < sample.sourceIntersectionCount
            (sample.feedbackGraph hlam0 hlamHalf x0 p0)
            (elapsedFeedbackCoordinate x0 t) := by
          rfl
      _ ↔ elapsed ≤ t :=
        (sourceIntersectionOrderStatisticElapsed_le_iff_lt_sourceIntersectionCount
          hlam0 hlamHalf x0 p0 sample r t).symm
  have hle : sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≤
      (elapsed : WithTop ℝ≥0) := (hthreshold elapsed).mpr le_rfl
  have hne : sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hle
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hne
  apply le_antisymm hle
  have harrived : sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≤
      (u : WithTop ℝ≥0) := by
    rw [← hu]
  have helapsed : elapsed ≤ u := (hthreshold u).mp harrived
  rw [← hu]
  exact_mod_cast helapsed

/-- An in-bounds target post-initial rank time is exactly the corresponding shifted order
statistic of the final feedback-graph target intersections. -/
theorem targetRankEventTime_eq_targetIntersectionOrderStatisticElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hOffset : targetRankIntersectionOffset x0 p0 sample k < n) :
    targetRankEventTime hlam0 hlamHalf x0 p0 k sample =
      (targetIntersectionOrderStatisticElapsed hlam0 hlamHalf x0 p0 sample
        (targetRankIntersectionIndex x0 p0 sample k hOffset) : WithTop ℝ≥0) := by
  let r := targetRankIntersectionIndex x0 p0 sample k hOffset
  let elapsed := targetIntersectionOrderStatisticElapsed
    hlam0 hlamHalf x0 p0 sample r
  have hthreshold : ∀ t : ℝ≥0,
      targetRankEventTime hlam0 hlamHalf x0 p0 k sample ≤ (t : WithTop ℝ≥0) ↔
        elapsed ≤ t := by
    intro t
    calc
      targetRankEventTime hlam0 hlamHalf x0 p0 k sample ≤ (t : WithTop ℝ≥0) ↔
          targetRankIntersectionOffset x0 p0 sample k <
            sample.targetIntersectionCount
              (sample.feedbackGraph hlam0 hlamHalf x0 p0)
              (elapsedFeedbackCoordinate x0 t) :=
        targetRankEventTime_le_iff_lt_targetIntersectionCount_offset
          hlam0 hlamHalf x0 p0 sample k t hNoTie
      _ ↔ r.val < sample.targetIntersectionCount
            (sample.feedbackGraph hlam0 hlamHalf x0 p0)
            (elapsedFeedbackCoordinate x0 t) := by
          rfl
      _ ↔ elapsed ≤ t :=
        (targetIntersectionOrderStatisticElapsed_le_iff_lt_targetIntersectionCount
          hlam0 hlamHalf x0 p0 sample r t).symm
  have hle : targetRankEventTime hlam0 hlamHalf x0 p0 k sample ≤
      (elapsed : WithTop ℝ≥0) := (hthreshold elapsed).mpr le_rfl
  have hne : targetRankEventTime hlam0 hlamHalf x0 p0 k sample ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hle
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hne
  apply le_antisymm hle
  have harrived : targetRankEventTime hlam0 hlamHalf x0 p0 k sample ≤
      (u : WithTop ℝ≥0) := by
    rw [← hu]
  have helapsed : elapsed ≤ u := (hthreshold u).mp harrived
  rw [← hu]
  exact_mod_cast helapsed

/-- If the shifted source offset is outside the full array, the post-initial source rank never
arrives and uses the top fallback. -/
theorem sourceRankEventTime_eq_top_of_offset_not_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hOffset : ¬ sourceRankIntersectionOffset x0 p0 sample k < n) :
    sourceRankEventTime hlam0 hlamHalf x0 p0 k sample = ⊤ := by
  by_contra hne
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  have harrived : sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≤
      (t : WithTop ℝ≥0) := by
    rw [← ht]
  have hlt := (sourceRankEventTime_le_iff_lt_sourceIntersectionCount_offset
    hlam0 hlamHalf x0 p0 sample k t hNoTie).mp harrived
  have hle := sourceIntersectionCount_le_card hlam0 hlamHalf x0 p0
    (elapsedFeedbackCoordinate x0 t) sample
  omega

/-- If the shifted target offset is outside the full array, the post-initial target rank never
arrives and uses the top fallback. -/
theorem targetRankEventTime_eq_top_of_offset_not_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hOffset : ¬ targetRankIntersectionOffset x0 p0 sample k < n) :
    targetRankEventTime hlam0 hlamHalf x0 p0 k sample = ⊤ := by
  by_contra hne
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  have harrived : targetRankEventTime hlam0 hlamHalf x0 p0 k sample ≤
      (t : WithTop ℝ≥0) := by
    rw [← ht]
  have hlt := (targetRankEventTime_le_iff_lt_targetIntersectionCount_offset
    hlam0 hlamHalf x0 p0 sample k t hNoTie).mp harrived
  have hle := targetIntersectionCount_le_card hlam0 hlamHalf x0 p0
    (elapsedFeedbackCoordinate x0 t) sample
  omega

/-- Under no ties, a source rank arrival is finite exactly when its shifted full-array offset is
in bounds. -/
theorem sourceRankEventTime_ne_top_iff_offset_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≠ ⊤ ↔
      sourceRankIntersectionOffset x0 p0 sample k < n := by
  constructor
  · intro hfinite
    by_contra hOffset
    exact hfinite (sourceRankEventTime_eq_top_of_offset_not_lt
      hlam0 hlamHalf x0 p0 sample k hNoTie hOffset)
  · intro hOffset
    rw [sourceRankEventTime_eq_sourceIntersectionOrderStatisticElapsed
      hlam0 hlamHalf x0 p0 sample k hNoTie hOffset]
    exact WithTop.coe_ne_top

/-- Under no ties, a target rank arrival is finite exactly when its shifted full-array offset is
in bounds. -/
theorem targetRankEventTime_ne_top_iff_offset_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    targetRankEventTime hlam0 hlamHalf x0 p0 k sample ≠ ⊤ ↔
      targetRankIntersectionOffset x0 p0 sample k < n := by
  constructor
  · intro hfinite
    by_contra hOffset
    exact hfinite (targetRankEventTime_eq_top_of_offset_not_lt
      hlam0 hlamHalf x0 p0 sample k hNoTie hOffset)
  · intro hOffset
    rw [targetRankEventTime_eq_targetIntersectionOrderStatisticElapsed
      hlam0 hlamHalf x0 p0 sample k hNoTie hOffset]
    exact WithTop.coe_ne_top

theorem coe_sourceIntersectionOrderStatisticElapsed_of_offset_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hOffset : sourceRankIntersectionOffset x0 p0 sample k < n) :
    (sourceIntersectionOrderStatisticElapsed hlam0 hlamHalf x0 p0 sample
        (sourceRankIntersectionIndex x0 p0 sample k hOffset) : ℝ) =
      sourceIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample
        (sourceRankIntersectionIndex x0 p0 sample k hOffset) - x0 := by
  rw [sourceIntersectionOrderStatisticElapsed]
  exact Real.coe_toNNReal _ (sub_nonneg.mpr
    (sourceIntersectionOrderStatistic_gt_initial_of_offset_lt
      hlam0 hlamHalf x0 p0 sample k hOffset).le)

theorem coe_targetIntersectionOrderStatisticElapsed_of_offset_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hOffset : targetRankIntersectionOffset x0 p0 sample k < n) :
    (targetIntersectionOrderStatisticElapsed hlam0 hlamHalf x0 p0 sample
        (targetRankIntersectionIndex x0 p0 sample k hOffset) : ℝ) =
      targetIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample
        (targetRankIntersectionIndex x0 p0 sample k hOffset) - x0 := by
  rw [targetIntersectionOrderStatisticElapsed]
  exact Real.coe_toNNReal _ (sub_nonneg.mpr
    (targetIntersectionOrderStatistic_gt_initial_of_offset_lt
      hlam0 hlamHalf x0 p0 sample k hOffset).le)

/-- Exact `intersection - x0` form of the finite source rank arrival. -/
theorem sourceRankEventTime_eq_coe_sourceIntersection_sub_initial
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hOffset : sourceRankIntersectionOffset x0 p0 sample k < n) :
    sourceRankEventTime hlam0 hlamHalf x0 p0 k sample =
      WithTop.some (⟨sourceIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample
          (sourceRankIntersectionIndex x0 p0 sample k hOffset) - x0,
        sub_nonneg.mpr
          (sourceIntersectionOrderStatistic_gt_initial_of_offset_lt
            hlam0 hlamHalf x0 p0 sample k hOffset).le⟩ : ℝ≥0) := by
  rw [sourceRankEventTime_eq_sourceIntersectionOrderStatisticElapsed
    hlam0 hlamHalf x0 p0 sample k hNoTie hOffset]
  congr 1
  apply NNReal.eq
  exact coe_sourceIntersectionOrderStatisticElapsed_of_offset_lt
    hlam0 hlamHalf x0 p0 sample k hOffset

/-- Exact `intersection - x0` form of the finite target rank arrival. -/
theorem targetRankEventTime_eq_coe_targetIntersection_sub_initial
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hOffset : targetRankIntersectionOffset x0 p0 sample k < n) :
    targetRankEventTime hlam0 hlamHalf x0 p0 k sample =
      WithTop.some (⟨targetIntersectionOrderStatistic hlam0 hlamHalf x0 p0 sample
          (targetRankIntersectionIndex x0 p0 sample k hOffset) - x0,
        sub_nonneg.mpr
          (targetIntersectionOrderStatistic_gt_initial_of_offset_lt
            hlam0 hlamHalf x0 p0 sample k hOffset).le⟩ : ℝ≥0) := by
  rw [targetRankEventTime_eq_targetIntersectionOrderStatisticElapsed
    hlam0 hlamHalf x0 p0 sample k hNoTie hOffset]
  congr 1
  apply NNReal.eq
  exact coe_targetIntersectionOrderStatisticElapsed_of_offset_lt
    hlam0 hlamHalf x0 p0 sample k hOffset

/-! ## Strict orientation at the left rank-arrival time -/

/-- The source rank arrives strictly before the target rank. -/
def sourceFirstRankEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) : Set (FiniteSample n) :=
  {sample | sourceRankEventTime hlam0 hlamHalf x0 p0 k sample <
    targetRankEventTime hlam0 hlamHalf x0 p0 k sample}

/-- The target rank arrives strictly before the source rank. -/
def targetFirstRankEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) : Set (FiniteSample n) :=
  {sample | targetRankEventTime hlam0 hlamHalf x0 p0 k sample <
    sourceRankEventTime hlam0 hlamHalf x0 p0 k sample}

/-- The two rank arrivals tie; this includes the case in which both offsets are out of bounds and
both rank times use the top fallback. -/
def rankArrivalTieEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) : Set (FiniteSample n) :=
  {sample | sourceRankEventTime hlam0 hlamHalf x0 p0 k sample =
    targetRankEventTime hlam0 hlamHalf x0 p0 k sample}

/-- The source-first event is measurable at the left rank-arrival stopping sigma algebra. -/
theorem measurableSet_sourceFirstRankEvent_at_feedbackRankLeftTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) :
    MeasurableSet[
      (feedbackRankLeftTime_isStoppingTime
        (n := n) hlam0 hlamHalf x0 p0 k).measurableSpace]
      (sourceFirstRankEvent hlam0 hlamHalf x0 p0 k) := by
  let hleft := feedbackRankLeftTime_isStoppingTime
    (n := n) hlam0 hlamHalf x0 p0 k
  let hsource := sourceRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf x0 p0 k
  let htarget := targetRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf x0 p0 k
  have h := CountingProcess.measurableSet_lt_stopping_time_min hsource htarget
  change MeasurableSet[hleft.measurableSpace]
    {sample | sourceRankEventTime hlam0 hlamHalf x0 p0 k sample <
      targetRankEventTime hlam0 hlamHalf x0 p0 k sample}
  have hproof : hleft = hsource.min htarget := Subsingleton.elim _ _
  rw [hproof]
  exact h

/-- The target-first event is measurable at the left rank-arrival stopping sigma algebra. -/
theorem measurableSet_targetFirstRankEvent_at_feedbackRankLeftTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) :
    MeasurableSet[
      (feedbackRankLeftTime_isStoppingTime
        (n := n) hlam0 hlamHalf x0 p0 k).measurableSpace]
      (targetFirstRankEvent hlam0 hlamHalf x0 p0 k) := by
  let hleft := feedbackRankLeftTime_isStoppingTime
    (n := n) hlam0 hlamHalf x0 p0 k
  let hsource := sourceRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf x0 p0 k
  let htarget := targetRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf x0 p0 k
  have h := CountingProcess.measurableSet_lt_stopping_time_min htarget hsource
  have hspace : (htarget.min hsource).measurableSpace =
      (hsource.min htarget).measurableSpace := by
    rw [htarget.measurableSpace_min hsource, hsource.measurableSpace_min htarget,
      inf_comm]
  rw [hspace] at h
  change MeasurableSet[hleft.measurableSpace]
    {sample | targetRankEventTime hlam0 hlamHalf x0 p0 k sample <
      sourceRankEventTime hlam0 hlamHalf x0 p0 k sample}
  have hproof : hleft = hsource.min htarget := Subsingleton.elim _ _
  rw [hproof]
  exact h

/-- The tie event is measurable at the left rank-arrival stopping sigma algebra. -/
theorem measurableSet_rankArrivalTieEvent_at_feedbackRankLeftTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) :
    MeasurableSet[
      (feedbackRankLeftTime_isStoppingTime
        (n := n) hlam0 hlamHalf x0 p0 k).measurableSpace]
      (rankArrivalTieEvent hlam0 hlamHalf x0 p0 k) := by
  let hleft := feedbackRankLeftTime_isStoppingTime
    (n := n) hlam0 hlamHalf x0 p0 k
  let hsource := sourceRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf x0 p0 k
  let htarget := targetRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf x0 p0 k
  have h := hsource.measurableSet_eq_stopping_time_min htarget
  change MeasurableSet[hleft.measurableSpace]
    {sample | sourceRankEventTime hlam0 hlamHalf x0 p0 k sample =
      targetRankEventTime hlam0 hlamHalf x0 p0 k sample}
  have hproof : hleft = hsource.min htarget := Subsingleton.elim _ _
  rw [hproof]
  exact h

theorem sourceFirstRankEvent_disjoint_targetFirstRankEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (k : Fin n) :
    Disjoint (sourceFirstRankEvent hlam0 hlamHalf x0 p0 k)
      (targetFirstRankEvent hlam0 hlamHalf x0 p0 k) := by
  rw [Set.disjoint_left]
  intro sample hsource htarget
  change sourceRankEventTime hlam0 hlamHalf x0 p0 k sample <
    targetRankEventTime hlam0 hlamHalf x0 p0 k sample at hsource
  change targetRankEventTime hlam0 hlamHalf x0 p0 k sample <
    sourceRankEventTime hlam0 hlamHalf x0 p0 k sample at htarget
  exact (not_lt_of_ge hsource.le) htarget

/-- Finite source and target rank arrivals cannot tie. -/
theorem sourceRankEventTime_ne_targetRankEventTime_of_ne_top
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hsource : sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≠ ⊤)
    (htarget : targetRankEventTime hlam0 hlamHalf x0 p0 k sample ≠ ⊤) :
    sourceRankEventTime hlam0 hlamHalf x0 p0 k sample ≠
      targetRankEventTime hlam0 hlamHalf x0 p0 k sample := by
  simpa only [sourceRankEventTime, targetRankEventTime,
    CountingProcess.finiteRankEventTime] using
      (sourceEventTime_ne_targetEventTime hlam0 hlamHalf x0 p0 sample
        (Tuple.sort
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i sample) k)
        (Tuple.sort
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j sample) k)
        hsource htarget)

/-- When both shifted ranks are in bounds, exactly one strict orientation holds. -/
theorem sourceFirstRankEvent_or_targetFirstRankEvent_of_offsets_lt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hsourceOffset : sourceRankIntersectionOffset x0 p0 sample k < n)
    (htargetOffset : targetRankIntersectionOffset x0 p0 sample k < n) :
    sample ∈ sourceFirstRankEvent hlam0 hlamHalf x0 p0 k ∨
      sample ∈ targetFirstRankEvent hlam0 hlamHalf x0 p0 k := by
  have hsource := (sourceRankEventTime_ne_top_iff_offset_lt
    hlam0 hlamHalf x0 p0 sample k hNoTie).mpr hsourceOffset
  have htarget := (targetRankEventTime_ne_top_iff_offset_lt
    hlam0 hlamHalf x0 p0 sample k hNoTie).mpr htargetOffset
  have hne := sourceRankEventTime_ne_targetRankEventTime_of_ne_top
    hlam0 hlamHalf x0 p0 sample k hsource htarget
  simpa only [sourceFirstRankEvent, targetFirstRankEvent, mem_ofPred_eq] using
    (lt_or_gt_of_ne hne)

/-- On the source-first branch, the left rank time is the shifted source-intersection elapsed
coordinate. -/
theorem feedbackRankLeftTime_eq_sourceIntersectionOrderStatisticElapsed_of_sourceFirst
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hsourceOffset : sourceRankIntersectionOffset x0 p0 sample k < n)
    (hsourceFirst : sample ∈ sourceFirstRankEvent hlam0 hlamHalf x0 p0 k) :
    feedbackRankLeftTime hlam0 hlamHalf x0 p0 k sample =
      (sourceIntersectionOrderStatisticElapsed hlam0 hlamHalf x0 p0 sample
        (sourceRankIntersectionIndex x0 p0 sample k hsourceOffset) : WithTop ℝ≥0) := by
  rw [feedbackRankLeftTime_eq_min, min_eq_left hsourceFirst.le]
  exact sourceRankEventTime_eq_sourceIntersectionOrderStatisticElapsed
    hlam0 hlamHalf x0 p0 sample k hNoTie hsourceOffset

/-- On the target-first branch, the left rank time is the shifted target-intersection elapsed
coordinate. -/
theorem feedbackRankLeftTime_eq_targetIntersectionOrderStatisticElapsed_of_targetFirst
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) (k : Fin n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (htargetOffset : targetRankIntersectionOffset x0 p0 sample k < n)
    (htargetFirst : sample ∈ targetFirstRankEvent hlam0 hlamHalf x0 p0 k) :
    feedbackRankLeftTime hlam0 hlamHalf x0 p0 k sample =
      (targetIntersectionOrderStatisticElapsed hlam0 hlamHalf x0 p0 sample
        (targetRankIntersectionIndex x0 p0 sample k htargetOffset) : WithTop ℝ≥0) := by
  rw [feedbackRankLeftTime_eq_min, min_eq_right htargetFirst.le]
  exact targetRankEventTime_eq_targetIntersectionOrderStatisticElapsed
    hlam0 hlamHalf x0 p0 sample k hNoTie htargetOffset

end FiniteSample

end OTSelector
