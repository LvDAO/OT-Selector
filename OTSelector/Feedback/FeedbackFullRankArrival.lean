import OTSelector.Feedback.FeedbackRankArrivalIntersection

/-!
# Full-rank arrivals for the raw feedback recursion

The post-initial event times deliberately omit labels already swept at `(B, 0)`.  For increasing
matching, however, source and target labels must be paired at the same rank of their full arrays.
This file therefore assigns time zero to initially seen labels and otherwise reuses the safe
post-initial event times.  The resulting full-rank arrivals are stopping times and, on the no-tie
event, are exactly the elapsed order statistics of the final raw feedback graph.

This is a bridge for the raw full-recursion graph.  Transport to a stopped-continuation graph is
left to the I4 layer.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Full-label event times -/

/-- A source label already seen at `(B, 0)` arrives at time zero; every other source label uses
the safe post-initial event time. -/
noncomputable def sourceFullEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (i : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  fun sample ↦ if i ∈ sample.initialSeenSource B 0 then 0
    else sourceEventTime hlam0 hlamHalf B 0 i sample

/-- A target label already seen at `(B, 0)` arrives at time zero; every other target label uses
the safe post-initial event time. -/
noncomputable def targetFullEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (j : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  fun sample ↦ if j ∈ sample.initialSeenTarget B 0 then 0
    else targetEventTime hlam0 hlamHalf B 0 j sample

@[simp]
theorem sourceFullEventTime_eq_zero_of_mem_initialSeen
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (i : Fin n) (sample : FiniteSample n)
    (hi : i ∈ sample.initialSeenSource B 0) :
    sourceFullEventTime hlam0 hlamHalf B i sample = 0 := by
  simp [sourceFullEventTime, hi]

@[simp]
theorem targetFullEventTime_eq_zero_of_mem_initialSeen
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (j : Fin n) (sample : FiniteSample n)
    (hj : j ∈ sample.initialSeenTarget B 0) :
    targetFullEventTime hlam0 hlamHalf B j sample = 0 := by
  simp [targetFullEventTime, hj]

@[simp]
theorem sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (i : Fin n) (sample : FiniteSample n)
    (hi : i ∉ sample.initialSeenSource B 0) :
    sourceFullEventTime hlam0 hlamHalf B i sample =
      sourceEventTime hlam0 hlamHalf B 0 i sample := by
  simp [sourceFullEventTime, hi]

@[simp]
theorem targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (j : Fin n) (sample : FiniteSample n)
    (hj : j ∉ sample.initialSeenTarget B 0) :
    targetFullEventTime hlam0 hlamHalf B j sample =
      targetEventTime hlam0 hlamHalf B 0 j sample := by
  simp [targetFullEventTime, hj]

/-- Each full source-label time is a stopping time in the usual revealed filtration. -/
theorem sourceFullEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (i : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (sourceFullEventTime hlam0 hlamHalf B i) := by
  classical
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  let s : Set (FiniteSample n) := {sample | i ∈ sample.initialSeenSource B 0}
  have hs : MeasurableSet[F 0] s :=
    measurableSet_mem_initialSeenSource_usual_zero
      (n := n) hlam0 hlamHalf B 0 i
  have hzero : IsStoppingTime F (fun _ : FiniteSample n ↦ (0 : WithTop ℝ≥0)) :=
    isStoppingTime_const F 0
  have hevent : IsStoppingTime F (sourceEventTime hlam0 hlamHalf B 0 i) :=
    sourceEventTime_isStoppingTime (n := n) hlam0 hlamHalf B 0 i
  have hpiece := hzero.piecewise_of_le hevent
    (i := (0 : ℝ≥0)) (fun _ ↦ bot_le) (fun _ ↦ bot_le) hs
  have heq : s.piecewise (fun _ : FiniteSample n ↦ (0 : WithTop ℝ≥0))
      (sourceEventTime hlam0 hlamHalf B 0 i) =
      sourceFullEventTime hlam0 hlamHalf B i := by
    funext sample
    by_cases hi : i ∈ sample.initialSeenSource B 0
    · have his : sample ∈ s := by simpa [s]
      simp [Set.piecewise, sourceFullEventTime, his, hi]
    · have his : sample ∉ s := by simpa [s]
      simp [Set.piecewise, sourceFullEventTime, his, hi]
  rw [← heq]
  exact hpiece

/-- Each full target-label time is a stopping time in the usual revealed filtration. -/
theorem targetFullEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (j : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (targetFullEventTime hlam0 hlamHalf B j) := by
  classical
  let F := usualRevealedFiltration (n := n) hlam0 hlamHalf B 0
  let s : Set (FiniteSample n) := {sample | j ∈ sample.initialSeenTarget B 0}
  have hs : MeasurableSet[F 0] s :=
    measurableSet_mem_initialSeenTarget_usual_zero
      (n := n) hlam0 hlamHalf B 0 j
  have hzero : IsStoppingTime F (fun _ : FiniteSample n ↦ (0 : WithTop ℝ≥0)) :=
    isStoppingTime_const F 0
  have hevent : IsStoppingTime F (targetEventTime hlam0 hlamHalf B 0 j) :=
    targetEventTime_isStoppingTime (n := n) hlam0 hlamHalf B 0 j
  have hpiece := hzero.piecewise_of_le hevent
    (i := (0 : ℝ≥0)) (fun _ ↦ bot_le) (fun _ ↦ bot_le) hs
  have heq : s.piecewise (fun _ : FiniteSample n ↦ (0 : WithTop ℝ≥0))
      (targetEventTime hlam0 hlamHalf B 0 j) =
      targetFullEventTime hlam0 hlamHalf B j := by
    funext sample
    by_cases hj : j ∈ sample.initialSeenTarget B 0
    · have hjs : sample ∈ s := by simpa [s]
      simp [Set.piecewise, targetFullEventTime, hjs, hj]
    · have hjs : sample ∉ s := by simpa [s]
      simp [Set.piecewise, targetFullEventTime, hjs, hj]
  rw [← heq]
  exact hpiece

/-! ## Full counts -/

/-- Number of full source labels arrived by elapsed time `t`. -/
noncomputable def sourceFullCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (t : ℝ≥0) : FiniteSample n → ℕ :=
  CountingProcess.finiteEventCountTop
    (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i) t

/-- Number of full target labels arrived by elapsed time `t`. -/
noncomputable def targetFullCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (t : ℝ≥0) : FiniteSample n → ℕ :=
  CountingProcess.finiteEventCountTop
    (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j) t

theorem sourceFullCount_eq_initial_card_add_safeSourceCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    sourceFullCount hlam0 hlamHalf B t sample =
      (sample.initialSeenSource B 0).card +
        safeSourceCount hlam0 hlamHalf B 0 t sample := by
  classical
  let initial := sample.initialSeenSource B 0
  let arrived := Finset.univ.filter fun i : Fin n ↦
    sourceEventTime hlam0 hlamHalf B 0 i sample ≤ (t : WithTop ℝ≥0)
  have hdisjoint : Disjoint initial arrived := by
    rw [Finset.disjoint_left]
    intro i hiInitial hiArrived
    have hiTime := (Finset.mem_filter.mp hiArrived).2
    have hiDiff :=
      (sample.sourceEventTime_le_iff_seen_diff hlam0 hlamHalf B 0 i t).mp hiTime
    exact (Finset.mem_sdiff.mp hiDiff.2).2 hiInitial
  have hset :
      Finset.univ.filter (fun i : Fin n ↦
        sourceFullEventTime hlam0 hlamHalf B i sample ≤ (t : WithTop ℝ≥0)) =
        initial ∪ arrived := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hi : i ∈ initial
    · have hi' : i ∈ sample.initialSeenSource B 0 := by simpa [initial] using hi
      simp only [sourceFullEventTime, hi', ite_true]
      constructor
      · intro _
        exact Or.inl hi
      · intro _
        exact (bot_le : (0 : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0))
    · have hi' : i ∉ sample.initialSeenSource B 0 := by simpa [initial] using hi
      simp only [sourceFullEventTime, hi', ite_false, hi, false_or]
      simp only [arrived, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold sourceFullCount CountingProcess.finiteEventCountTop safeSourceCount
  rw [hset, Finset.card_union_of_disjoint hdisjoint]
  rfl

theorem targetFullCount_eq_initial_card_add_safeTargetCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    targetFullCount hlam0 hlamHalf B t sample =
      (sample.initialSeenTarget B 0).card +
        safeTargetCount hlam0 hlamHalf B 0 t sample := by
  classical
  let initial := sample.initialSeenTarget B 0
  let arrived := Finset.univ.filter fun j : Fin n ↦
    targetEventTime hlam0 hlamHalf B 0 j sample ≤ (t : WithTop ℝ≥0)
  have hdisjoint : Disjoint initial arrived := by
    rw [Finset.disjoint_left]
    intro j hjInitial hjArrived
    have hjTime := (Finset.mem_filter.mp hjArrived).2
    have hjDiff :=
      (sample.targetEventTime_le_iff_seen_diff hlam0 hlamHalf B 0 j t).mp hjTime
    exact (Finset.mem_sdiff.mp hjDiff.2).2 hjInitial
  have hset :
      Finset.univ.filter (fun j : Fin n ↦
        targetFullEventTime hlam0 hlamHalf B j sample ≤ (t : WithTop ℝ≥0)) =
        initial ∪ arrived := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    by_cases hj : j ∈ initial
    · have hj' : j ∈ sample.initialSeenTarget B 0 := by simpa [initial] using hj
      simp only [targetFullEventTime, hj', ite_true]
      constructor
      · intro _
        exact Or.inl hj
      · intro _
        exact (bot_le : (0 : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0))
    · have hj' : j ∉ sample.initialSeenTarget B 0 := by simpa [initial] using hj
      simp only [targetFullEventTime, hj', ite_false, hj, false_or]
      simp only [arrived, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold targetFullCount CountingProcess.finiteEventCountTop safeTargetCount
  rw [hset, Finset.card_union_of_disjoint hdisjoint]
  rfl

/-- On the no-tie event, the full source count is the raw final-graph intersection count at
`B + t`. -/
theorem sourceFullCount_eq_sourceIntersectionCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    sourceFullCount hlam0 hlamHalf B t sample =
      sample.sourceIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf B 0)
        (elapsedFeedbackCoordinate B t) := by
  rw [sourceFullCount_eq_initial_card_add_safeSourceCount]
  rw [Nat.add_comm]
  exact safeSourceCount_add_initialSeenSource_card_eq_sourceIntersectionCount
    hlam0 hlamHalf B 0 t sample hNoTie

/-- On the no-tie event, the full target count is the raw final-graph intersection count at
`B + t`. -/
theorem targetFullCount_eq_targetIntersectionCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    targetFullCount hlam0 hlamHalf B t sample =
      sample.targetIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf B 0)
        (elapsedFeedbackCoordinate B t) := by
  rw [targetFullCount_eq_initial_card_add_safeTargetCount]
  rw [Nat.add_comm]
  exact safeTargetCount_add_initialSeenTarget_card_eq_targetIntersectionCount
    hlam0 hlamHalf B 0 t sample hNoTie

theorem sourceFullCount_eq_sourceIntersectionCount_at_B_add
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    sourceFullCount hlam0 hlamHalf B t sample =
      sample.sourceIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf B 0) (B + (t : ℝ)) := by
  simpa only [elapsedFeedbackCoordinate] using
    sourceFullCount_eq_sourceIntersectionCount
      hlam0 hlamHalf B t sample hNoTie

theorem targetFullCount_eq_targetIntersectionCount_at_B_add
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    targetFullCount hlam0 hlamHalf B t sample =
      sample.targetIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf B 0) (B + (t : ℝ)) := by
  simpa only [elapsedFeedbackCoordinate] using
    targetFullCount_eq_targetIntersectionCount
      hlam0 hlamHalf B t sample hNoTie

/-! ## Full-rank stopping times and raw-graph order statistics -/

/-- The `r`-th arrival among all source labels, including labels assigned time zero at `(B, 0)`. -/
noncomputable def sourceFullRankEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  CountingProcess.finiteRankEventTime
    (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i) r

/-- The `r`-th arrival among all target labels, including labels assigned time zero at `(B, 0)`. -/
noncomputable def targetFullRankEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  CountingProcess.finiteRankEventTime
    (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j) r

theorem sourceFullRankEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (sourceFullRankEventTime hlam0 hlamHalf B r) := by
  exact CountingProcess.finiteRankEventTime_isStoppingTime
    (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
    (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i) r
    (fun i ↦ sourceFullEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf B i)

theorem targetFullRankEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (targetFullRankEventTime hlam0 hlamHalf B r) := by
  exact CountingProcess.finiteRankEventTime_isStoppingTime
    (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
    (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j) r
    (fun j ↦ targetFullEventTime_isStoppingTime
      (n := n) hlam0 hlamHalf B j)

theorem sourceFullRankEventTime_le_iff_lt_sourceFullCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (t : ℝ≥0) (sample : FiniteSample n) :
    sourceFullRankEventTime hlam0 hlamHalf B r sample ≤ (t : WithTop ℝ≥0) ↔
      r.val < sourceFullCount hlam0 hlamHalf B t sample := by
  simpa only [sourceFullRankEventTime, sourceFullCount] using
    (CountingProcess.finiteRankEventTime_le_iff_lt_finiteEventCountTop
      (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i) r sample t)

theorem targetFullRankEventTime_le_iff_lt_targetFullCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (t : ℝ≥0) (sample : FiniteSample n) :
    targetFullRankEventTime hlam0 hlamHalf B r sample ≤ (t : WithTop ℝ≥0) ↔
      r.val < targetFullCount hlam0 hlamHalf B t sample := by
  simpa only [targetFullRankEventTime, targetFullCount] using
    (CountingProcess.finiteRankEventTime_le_iff_lt_finiteEventCountTop
      (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j) r sample t)

/-- NoFeedbackTies identifies every full source rank arrival with the corresponding order
statistic of the raw final feedback-graph intersections.  Initial intersections are naturally
compressed to elapsed time zero by `Real.toNNReal`. -/
theorem sourceFullRankEventTime_eq_sourceIntersectionOrderStatisticElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    sourceFullRankEventTime hlam0 hlamHalf B r sample =
      (sourceIntersectionOrderStatisticElapsed hlam0 hlamHalf B 0 sample r :
        WithTop ℝ≥0) := by
  let elapsed := sourceIntersectionOrderStatisticElapsed
    hlam0 hlamHalf B 0 sample r
  have hthreshold : ∀ t : ℝ≥0,
      sourceFullRankEventTime hlam0 hlamHalf B r sample ≤ (t : WithTop ℝ≥0) ↔
        elapsed ≤ t := by
    intro t
    calc
      sourceFullRankEventTime hlam0 hlamHalf B r sample ≤ (t : WithTop ℝ≥0) ↔
          r.val < sourceFullCount hlam0 hlamHalf B t sample :=
        sourceFullRankEventTime_le_iff_lt_sourceFullCount
          hlam0 hlamHalf B r t sample
      _ ↔ r.val < sample.sourceIntersectionCount
            (sample.feedbackGraph hlam0 hlamHalf B 0)
            (elapsedFeedbackCoordinate B t) := by
          rw [sourceFullCount_eq_sourceIntersectionCount
            hlam0 hlamHalf B t sample hNoTie]
      _ ↔ elapsed ≤ t :=
        (sourceIntersectionOrderStatisticElapsed_le_iff_lt_sourceIntersectionCount
          hlam0 hlamHalf B 0 sample r t).symm
  have hle : sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
      (elapsed : WithTop ℝ≥0) := (hthreshold elapsed).mpr le_rfl
  have hne : sourceFullRankEventTime hlam0 hlamHalf B r sample ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hle
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hne
  apply le_antisymm hle
  have harrived : sourceFullRankEventTime hlam0 hlamHalf B r sample ≤
      (u : WithTop ℝ≥0) := by
    rw [← hu]
  have helapsed : elapsed ≤ u := (hthreshold u).mp harrived
  rw [← hu]
  exact_mod_cast helapsed

/-- NoFeedbackTies identifies every full target rank arrival with the corresponding order
statistic of the raw final feedback-graph intersections. -/
theorem targetFullRankEventTime_eq_targetIntersectionOrderStatisticElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    targetFullRankEventTime hlam0 hlamHalf B r sample =
      (targetIntersectionOrderStatisticElapsed hlam0 hlamHalf B 0 sample r :
        WithTop ℝ≥0) := by
  let elapsed := targetIntersectionOrderStatisticElapsed
    hlam0 hlamHalf B 0 sample r
  have hthreshold : ∀ t : ℝ≥0,
      targetFullRankEventTime hlam0 hlamHalf B r sample ≤ (t : WithTop ℝ≥0) ↔
        elapsed ≤ t := by
    intro t
    calc
      targetFullRankEventTime hlam0 hlamHalf B r sample ≤ (t : WithTop ℝ≥0) ↔
          r.val < targetFullCount hlam0 hlamHalf B t sample :=
        targetFullRankEventTime_le_iff_lt_targetFullCount
          hlam0 hlamHalf B r t sample
      _ ↔ r.val < sample.targetIntersectionCount
            (sample.feedbackGraph hlam0 hlamHalf B 0)
            (elapsedFeedbackCoordinate B t) := by
          rw [targetFullCount_eq_targetIntersectionCount
            hlam0 hlamHalf B t sample hNoTie]
      _ ↔ elapsed ≤ t :=
        (targetIntersectionOrderStatisticElapsed_le_iff_lt_targetIntersectionCount
          hlam0 hlamHalf B 0 sample r t).symm
  have hle : targetFullRankEventTime hlam0 hlamHalf B r sample ≤
      (elapsed : WithTop ℝ≥0) := (hthreshold elapsed).mpr le_rfl
  have hne : targetFullRankEventTime hlam0 hlamHalf B r sample ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hle
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hne
  apply le_antisymm hle
  have harrived : targetFullRankEventTime hlam0 hlamHalf B r sample ≤
      (u : WithTop ℝ≥0) := by
    rw [← hu]
  have helapsed : elapsed ≤ u := (hthreshold u).mp harrived
  rw [← hu]
  exact_mod_cast helapsed

/-- Explicit `toNNReal (intersection - B)` form of the source full-rank bridge. -/
theorem sourceFullRankEventTime_eq_toNNReal_sourceIntersection_sub_B
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    sourceFullRankEventTime hlam0 hlamHalf B r sample =
      (Real.toNNReal
        (sourceIntersectionOrderStatistic hlam0 hlamHalf B 0 sample r - B) :
          WithTop ℝ≥0) := by
  simpa only [sourceIntersectionOrderStatisticElapsed] using
    sourceFullRankEventTime_eq_sourceIntersectionOrderStatisticElapsed
      hlam0 hlamHalf B r sample hNoTie

/-- Explicit `toNNReal (intersection - B)` form of the target full-rank bridge. -/
theorem targetFullRankEventTime_eq_toNNReal_targetIntersection_sub_B
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    targetFullRankEventTime hlam0 hlamHalf B r sample =
      (Real.toNNReal
        (targetIntersectionOrderStatistic hlam0 hlamHalf B 0 sample r - B) :
          WithTop ℝ≥0) := by
  simpa only [targetIntersectionOrderStatisticElapsed] using
    targetFullRankEventTime_eq_targetIntersectionOrderStatisticElapsed
      hlam0 hlamHalf B r sample hNoTie

theorem sourceFullRankEventTime_ne_top_of_noFeedbackTies
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    sourceFullRankEventTime hlam0 hlamHalf B r sample ≠ ⊤ := by
  rw [sourceFullRankEventTime_eq_sourceIntersectionOrderStatisticElapsed
    hlam0 hlamHalf B r sample hNoTie]
  exact WithTop.coe_ne_top

theorem targetFullRankEventTime_ne_top_of_noFeedbackTies
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    targetFullRankEventTime hlam0 hlamHalf B r sample ≠ ⊤ := by
  rw [targetFullRankEventTime_eq_targetIntersectionOrderStatisticElapsed
    hlam0 hlamHalf B r sample hNoTie]
  exact WithTop.coe_ne_top

/-! ## Same-rank orientation at the minimum stopping time -/

/-- The first arrival among the source and target full arrays at the same rank `r`. -/
noncomputable def feedbackFullRankLeftTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  fun sample ↦ min
    (sourceFullRankEventTime hlam0 hlamHalf B r sample)
    (targetFullRankEventTime hlam0 hlamHalf B r sample)

@[simp]
theorem feedbackFullRankLeftTime_eq_min
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n) :
    feedbackFullRankLeftTime hlam0 hlamHalf B r sample = min
      (sourceFullRankEventTime hlam0 hlamHalf B r sample)
      (targetFullRankEventTime hlam0 hlamHalf B r sample) :=
  rfl

theorem feedbackFullRankLeftTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
      (feedbackFullRankLeftTime hlam0 hlamHalf B r) := by
  change IsStoppingTime
    (usualRevealedFiltration (n := n) hlam0 hlamHalf B 0)
    (fun sample ↦ min
      (sourceFullRankEventTime hlam0 hlamHalf B r sample)
      (targetFullRankEventTime hlam0 hlamHalf B r sample))
  exact (sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r).min
      (targetFullRankEventTime_isStoppingTime
        (n := n) hlam0 hlamHalf B r)

/-- At full rank `r`, the source arrival is strictly first. -/
def sourceFirstFullRankEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) : Set (FiniteSample n) :=
  {sample | sourceFullRankEventTime hlam0 hlamHalf B r sample <
    targetFullRankEventTime hlam0 hlamHalf B r sample}

/-- At full rank `r`, the target arrival is strictly first. -/
def targetFirstFullRankEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) : Set (FiniteSample n) :=
  {sample | targetFullRankEventTime hlam0 hlamHalf B r sample <
    sourceFullRankEventTime hlam0 hlamHalf B r sample}

/-- Tie of the source and target full-rank arrivals.  Under NoFeedbackTies, this is precisely the
boundary case in which both full-rank times are zero. -/
def fullRankArrivalTieEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) : Set (FiniteSample n) :=
  {sample | sourceFullRankEventTime hlam0 hlamHalf B r sample =
    targetFullRankEventTime hlam0 hlamHalf B r sample}

theorem measurableSet_sourceFirstFullRankEvent_at_leftTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    MeasurableSet[
      (feedbackFullRankLeftTime_isStoppingTime
        (n := n) hlam0 hlamHalf B r).measurableSpace]
      (sourceFirstFullRankEvent hlam0 hlamHalf B r) := by
  let hleft := feedbackFullRankLeftTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let hsource := sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let htarget := targetFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have h := CountingProcess.measurableSet_lt_stopping_time_min hsource htarget
  change MeasurableSet[hleft.measurableSpace]
    {sample | sourceFullRankEventTime hlam0 hlamHalf B r sample <
      targetFullRankEventTime hlam0 hlamHalf B r sample}
  have hproof : hleft = hsource.min htarget := Subsingleton.elim _ _
  rw [hproof]
  exact h

theorem measurableSet_targetFirstFullRankEvent_at_leftTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    MeasurableSet[
      (feedbackFullRankLeftTime_isStoppingTime
        (n := n) hlam0 hlamHalf B r).measurableSpace]
      (targetFirstFullRankEvent hlam0 hlamHalf B r) := by
  let hleft := feedbackFullRankLeftTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let hsource := sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let htarget := targetFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have h := CountingProcess.measurableSet_lt_stopping_time_min htarget hsource
  have hspace : (htarget.min hsource).measurableSpace =
      (hsource.min htarget).measurableSpace := by
    rw [htarget.measurableSpace_min hsource, hsource.measurableSpace_min htarget,
      inf_comm]
  rw [hspace] at h
  change MeasurableSet[hleft.measurableSpace]
    {sample | targetFullRankEventTime hlam0 hlamHalf B r sample <
      sourceFullRankEventTime hlam0 hlamHalf B r sample}
  have hproof : hleft = hsource.min htarget := Subsingleton.elim _ _
  rw [hproof]
  exact h

theorem measurableSet_fullRankArrivalTieEvent_at_leftTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    MeasurableSet[
      (feedbackFullRankLeftTime_isStoppingTime
        (n := n) hlam0 hlamHalf B r).measurableSpace]
      (fullRankArrivalTieEvent hlam0 hlamHalf B r) := by
  let hleft := feedbackFullRankLeftTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let hsource := sourceFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  let htarget := targetFullRankEventTime_isStoppingTime
    (n := n) hlam0 hlamHalf B r
  have h := hsource.measurableSet_eq_stopping_time_min htarget
  change MeasurableSet[hleft.measurableSpace]
    {sample | sourceFullRankEventTime hlam0 hlamHalf B r sample =
      targetFullRankEventTime hlam0 hlamHalf B r sample}
  have hproof : hleft = hsource.min htarget := Subsingleton.elim _ _
  rw [hproof]
  exact h

theorem sourceFirstFullRankEvent_disjoint_targetFirstFullRankEvent
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) :
    Disjoint (sourceFirstFullRankEvent hlam0 hlamHalf B r)
      (targetFirstFullRankEvent hlam0 hlamHalf B r) := by
  rw [Set.disjoint_left]
  intro sample hsource htarget
  change sourceFullRankEventTime hlam0 hlamHalf B r sample <
    targetFullRankEventTime hlam0 hlamHalf B r sample at hsource
  change targetFullRankEventTime hlam0 hlamHalf B r sample <
    sourceFullRankEventTime hlam0 hlamHalf B r sample at htarget
  exact (not_lt_of_ge hsource.le) htarget

theorem sourceFirstFullRankEvent_or_targetFirstFullRankEvent_of_ne
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hne : sourceFullRankEventTime hlam0 hlamHalf B r sample ≠
      targetFullRankEventTime hlam0 hlamHalf B r sample) :
    sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r ∨
      sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r := by
  simpa only [sourceFirstFullRankEvent, targetFirstFullRankEvent, mem_ofPred_eq] using
    (lt_or_gt_of_ne hne)

theorem feedbackFullRankLeftTime_eq_sourceFullRankEventTime_of_sourceFirst
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hsource : sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r) :
    feedbackFullRankLeftTime hlam0 hlamHalf B r sample =
      sourceFullRankEventTime hlam0 hlamHalf B r sample := by
  exact min_eq_left hsource.le

theorem feedbackFullRankLeftTime_eq_targetFullRankEventTime_of_targetFirst
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (htarget : sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r) :
    feedbackFullRankLeftTime hlam0 hlamHalf B r sample =
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
  exact min_eq_right htarget.le

/-- Away from the compressed initial boundary `(0, 0)`, NoFeedbackTies separates the same-rank
source and target full arrivals. -/
theorem sourceFullRankEventTime_ne_targetFullRankEventTime_of_not_both_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hNotBothZero : ¬
      (sourceFullRankEventTime hlam0 hlamHalf B r sample = 0 ∧
        targetFullRankEventTime hlam0 hlamHalf B r sample = 0)) :
    sourceFullRankEventTime hlam0 hlamHalf B r sample ≠
      targetFullRankEventTime hlam0 hlamHalf B r sample := by
  intro heq
  have hsourceZero : sourceFullRankEventTime hlam0 hlamHalf B r sample ≠ 0 := by
    intro hzero
    apply hNotBothZero
    exact ⟨hzero, heq ▸ hzero⟩
  have htargetZero : targetFullRankEventTime hlam0 hlamHalf B r sample ≠ 0 := by
    intro hzero
    apply hsourceZero
    exact heq.trans hzero
  let i := Tuple.sort
    (fun i : Fin n ↦ sourceFullEventTime hlam0 hlamHalf B i sample) r
  let j := Tuple.sort
    (fun j : Fin n ↦ targetFullEventTime hlam0 hlamHalf B j sample) r
  have hsourceSelected :
      sourceFullRankEventTime hlam0 hlamHalf B r sample =
        sourceFullEventTime hlam0 hlamHalf B i sample := by
    rfl
  have htargetSelected :
      targetFullRankEventTime hlam0 hlamHalf B r sample =
        targetFullEventTime hlam0 hlamHalf B j sample := by
    rfl
  have hi : i ∉ sample.initialSeenSource B 0 := by
    intro hi
    apply hsourceZero
    rw [hsourceSelected,
      sourceFullEventTime_eq_zero_of_mem_initialSeen
        hlam0 hlamHalf B i sample hi]
  have hj : j ∉ sample.initialSeenTarget B 0 := by
    intro hj
    apply htargetZero
    rw [htargetSelected,
      targetFullEventTime_eq_zero_of_mem_initialSeen
        hlam0 hlamHalf B j sample hj]
  have hsourceFinite : sourceEventTime hlam0 hlamHalf B 0 i sample ≠ ⊤ := by
    intro htop
    have hfullFinite := sourceFullRankEventTime_ne_top_of_noFeedbackTies
      hlam0 hlamHalf B r sample hNoTie
    apply hfullFinite
    rw [hsourceSelected,
      sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
        hlam0 hlamHalf B i sample hi,
      htop]
  have htargetFinite : targetEventTime hlam0 hlamHalf B 0 j sample ≠ ⊤ := by
    intro htop
    have hfullFinite := targetFullRankEventTime_ne_top_of_noFeedbackTies
      hlam0 hlamHalf B r sample hNoTie
    apply hfullFinite
    rw [htargetSelected,
      targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
        hlam0 hlamHalf B j sample hj,
      htop]
  have hselected : sourceFullEventTime hlam0 hlamHalf B i sample =
      targetFullEventTime hlam0 hlamHalf B j sample := by
    rw [← hsourceSelected, ← htargetSelected]
    exact heq
  have hevent : sourceEventTime hlam0 hlamHalf B 0 i sample =
      targetEventTime hlam0 hlamHalf B 0 j sample := by
    simpa only [sourceFullEventTime_eq_sourceEventTime_of_not_mem_initialSeen
      hlam0 hlamHalf B i sample hi,
      targetFullEventTime_eq_targetEventTime_of_not_mem_initialSeen
        hlam0 hlamHalf B j sample hj] using hselected
  exact (sourceEventTime_ne_targetEventTime
    hlam0 hlamHalf B 0 sample i j hsourceFinite htargetFinite) hevent

/-- Under NoFeedbackTies, equality of same-rank full arrivals is exactly the boundary tie in
which both compressed elapsed times are zero. -/
theorem sourceFullRankEventTime_eq_targetFullRankEventTime_iff_both_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0) :
    sourceFullRankEventTime hlam0 hlamHalf B r sample =
        targetFullRankEventTime hlam0 hlamHalf B r sample ↔
      sourceFullRankEventTime hlam0 hlamHalf B r sample = 0 ∧
        targetFullRankEventTime hlam0 hlamHalf B r sample = 0 := by
  constructor
  · intro heq
    by_contra hNotBothZero
    exact (sourceFullRankEventTime_ne_targetFullRankEventTime_of_not_both_zero
      hlam0 hlamHalf B r sample hNoTie hNotBothZero) heq
  · rintro ⟨hsource, htarget⟩
    exact hsource.trans htarget.symm

/-- Except for the explicit zero-time boundary tie, the same full rank has exactly one strict
orientation. -/
theorem sourceFirstFullRankEvent_or_targetFirstFullRankEvent_of_not_both_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (B : ℝ) (r : Fin n) (sample : FiniteSample n)
    (hNoTie : sample.NoFeedbackTies lam B 0)
    (hNotBothZero : ¬
      (sourceFullRankEventTime hlam0 hlamHalf B r sample = 0 ∧
        targetFullRankEventTime hlam0 hlamHalf B r sample = 0)) :
    sample ∈ sourceFirstFullRankEvent hlam0 hlamHalf B r ∨
      sample ∈ targetFirstFullRankEvent hlam0 hlamHalf B r := by
  exact sourceFirstFullRankEvent_or_targetFirstFullRankEvent_of_ne
    hlam0 hlamHalf B r sample
      (sourceFullRankEventTime_ne_targetFullRankEventTime_of_not_both_zero
        hlam0 hlamHalf B r sample hNoTie hNotBothZero)

end FiniteSample

end OTSelector
