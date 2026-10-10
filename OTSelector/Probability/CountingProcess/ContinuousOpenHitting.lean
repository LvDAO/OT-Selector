import OTSelector.Probability.CountingProcess.StoppingMasks
import Mathlib.Data.NNRat.Encodable
import Mathlib.Probability.Process.HittingTime

/-!
# Continuous open-set hitting times

Mathlib proves the stopping-time property of `hittingAfter` directly only in discrete time.  This
file supplies the continuous-time case needed by the feedback bulk exit.  A continuous path hits
an open set before `t` if and only if it hits it at a nonnegative rationalized time before `t`.
The same countable union identifies the predictable set strictly after the hitting time, and hence
makes the right-closed through-stop mask predictable without a finite-range assumption.
-/

open Filter Set
open scoped Classical NNReal Topology

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω β : Type*}

noncomputable section

private theorem denseRange_rat_toNNReal :
    DenseRange (fun q : ℚ ↦ Real.toNNReal (q : ℝ)) := by
  have hsurj : Function.Surjective Real.toNNReal := by
    intro x
    refine ⟨(x : ℝ), ?_⟩
    exact Real.toNNReal_of_nonneg x.2
  exact hsurj.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal

/-- For continuous paths and an open target, hitting before a deterministic time is detected at
a rationalized nonnegative time. -/
theorem hittingAfter_zero_lt_set_eq_iUnion_rat
    [TopologicalSpace β] {u : ℝ≥0 → Ω → β} {s : Set β}
    (hcont : ∀ ω, Continuous fun t ↦ u t ω) (hs : IsOpen s) (t : ℝ≥0) :
    {ω | MeasureTheory.hittingAfter u s 0 ω < (t : WithTop ℝ≥0)} =
      ⋃ q : ℚ, if Real.toNNReal (q : ℝ) < t then
        {ω | u (Real.toNNReal (q : ℝ)) ω ∈ s} else ∅ := by
  ext ω
  constructor
  · intro hω
    change MeasureTheory.hittingAfter u s 0 ω < (t : WithTop ℝ≥0) at hω
    rw [MeasureTheory.hittingAfter_lt_iff] at hω
    obtain ⟨j, hj, hjs⟩ := hω
    let U : Set ℝ≥0 := (fun r ↦ u r ω) ⁻¹' s ∩ Iio t
    have hUopen : IsOpen U := (hs.preimage (hcont ω)).inter isOpen_Iio
    have hjU : j ∈ U := ⟨hjs, hj.2⟩
    obtain ⟨q, hqU⟩ := denseRange_rat_toNNReal.exists_mem_open hUopen ⟨j, hjU⟩
    change u (Real.toNNReal (q : ℝ)) ω ∈ s ∧ Real.toNNReal (q : ℝ) < t at hqU
    rw [Set.mem_iUnion]
    refine ⟨q, ?_⟩
    rw [ite_eq_left hqU.2]
    exact hqU.1
  · intro hω
    rw [Set.mem_iUnion] at hω
    obtain ⟨q, hq⟩ := hω
    by_cases hqt : Real.toNNReal (q : ℝ) < t
    · rw [ite_eq_left hqt] at hq
      change MeasureTheory.hittingAfter u s 0 ω < (t : WithTop ℝ≥0)
      rw [MeasureTheory.hittingAfter_lt_iff]
      exact ⟨Real.toNNReal (q : ℝ), ⟨bot_le, hqt⟩, hq⟩
    · rw [ite_eq_right hqt] at hq
      exact False.elim hq

/-- Right-continuity is enough to detect an open-set hit before `t` at a rationalized time.
Unlike the continuous-path theorem above, the rational witness is chosen strictly after the
original hit, inside the right neighborhood on which the path remains in the open set. -/
theorem hittingAfter_zero_lt_set_eq_iUnion_rat_of_rightContinuous
    [TopologicalSpace β] {u : ℝ≥0 → Ω → β} {s : Set β}
    (hrc : ∀ ω t, ContinuousWithinAt (fun r ↦ u r ω) (Ici t) t)
    (hs : IsOpen s) (t : ℝ≥0) :
    {ω | MeasureTheory.hittingAfter u s 0 ω < (t : WithTop ℝ≥0)} =
      ⋃ q : ℚ, if Real.toNNReal (q : ℝ) < t then
        {ω | u (Real.toNNReal (q : ℝ)) ω ∈ s} else ∅ := by
  ext ω
  constructor
  · intro hω
    change MeasureTheory.hittingAfter u s 0 ω < (t : WithTop ℝ≥0) at hω
    rw [MeasureTheory.hittingAfter_lt_iff] at hω
    obtain ⟨j, hj, hjs⟩ := hω
    have hpre : (fun r ↦ u r ω) ⁻¹' s ∈ 𝓝[Ici j] j :=
      (hrc ω j).preimage_mem_nhdsWithin (hs.mem_nhds hjs)
    have hpreGT : (fun r ↦ u r ω) ⁻¹' s ∈ 𝓝[>] j :=
      (nhdsWithin_mono j (show Ioi j ⊆ Ici j by
        intro x hx
        change j < x at hx
        change j ≤ x
        exact hx.le)) hpre
    have htGT : Iio t ∈ 𝓝[>] j :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hj.2)
    have hinter : (fun r ↦ u r ω) ⁻¹' s ∩ Iio t ∈ 𝓝[>] j :=
      inter_mem hpreGT htGT
    obtain ⟨r, hjr, hr⟩ :=
      (mem_nhdsGT_iff_exists_Ioo_subset' hj.2).mp hinter
    obtain ⟨q, hq⟩ := denseRange_rat_toNNReal.exists_mem_open
      isOpen_Ioo (nonempty_Ioo.mpr hjr)
    have hq' := hr hq
    rw [Set.mem_iUnion]
    refine ⟨q, ?_⟩
    have hqt : Real.toNNReal (q : ℝ) < t := hq'.2
    rw [ite_eq_left hqt]
    exact hq'.1
  · intro hω
    rw [Set.mem_iUnion] at hω
    obtain ⟨q, hq⟩ := hω
    by_cases hqt : Real.toNNReal (q : ℝ) < t
    · rw [ite_eq_left hqt] at hq
      change MeasureTheory.hittingAfter u s 0 ω < (t : WithTop ℝ≥0)
      rw [MeasureTheory.hittingAfter_lt_iff]
      exact ⟨Real.toNNReal (q : ℝ), ⟨bot_le, hqt⟩, hq⟩
    · rw [ite_eq_right hqt] at hq
      exact False.elim hq

/-- The predictable after-start set of an open hitting time is a countable union of rational
predictable rectangles. -/
theorem afterStartSet_hittingAfter_zero_eq_iUnion_rat
    [TopologicalSpace β] {u : ℝ≥0 → Ω → β} {s : Set β}
    (hcont : ∀ ω, Continuous fun t ↦ u t ω) (hs : IsOpen s) :
    afterStartSet (MeasureTheory.hittingAfter u s 0) =
      ⋃ q : ℚ, Ioi (Real.toNNReal (q : ℝ)) ×ˢ
        {ω | u (Real.toNNReal (q : ℝ)) ω ∈ s} := by
  ext z
  constructor
  · intro hz
    have hz' : z.2 ∈
        {ω | MeasureTheory.hittingAfter u s 0 ω < (z.1 : WithTop ℝ≥0)} := hz
    rw [hittingAfter_zero_lt_set_eq_iUnion_rat hcont hs z.1] at hz'
    rw [Set.mem_iUnion] at hz'
    obtain ⟨q, hq⟩ := hz'
    by_cases hqt : Real.toNNReal (q : ℝ) < z.1
    · rw [ite_eq_left hqt] at hq
      rw [Set.mem_iUnion]
      exact ⟨q, ⟨hqt, hq⟩⟩
    · rw [ite_eq_right hqt] at hq
      exact False.elim hq
  · intro hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨q, hqt, hq⟩ := hz
    change Real.toNNReal (q : ℝ) < z.1 at hqt
    have hz' : z.2 ∈
        {ω | MeasureTheory.hittingAfter u s 0 ω < (z.1 : WithTop ℝ≥0)} := by
      rw [hittingAfter_zero_lt_set_eq_iUnion_rat hcont hs z.1, Set.mem_iUnion]
      refine ⟨q, ?_⟩
      rw [ite_eq_left hqt]
      exact hq
    exact hz'

/-- Right-continuous version of the rational predictable-rectangle representation. -/
theorem afterStartSet_hittingAfter_zero_eq_iUnion_rat_of_rightContinuous
    [TopologicalSpace β] {u : ℝ≥0 → Ω → β} {s : Set β}
    (hrc : ∀ ω t, ContinuousWithinAt (fun r ↦ u r ω) (Ici t) t)
    (hs : IsOpen s) :
    afterStartSet (MeasureTheory.hittingAfter u s 0) =
      ⋃ q : ℚ, Ioi (Real.toNNReal (q : ℝ)) ×ˢ
        {ω | u (Real.toNNReal (q : ℝ)) ω ∈ s} := by
  ext z
  constructor
  · intro hz
    have hz' : z.2 ∈
        {ω | MeasureTheory.hittingAfter u s 0 ω < (z.1 : WithTop ℝ≥0)} := hz
    rw [hittingAfter_zero_lt_set_eq_iUnion_rat_of_rightContinuous hrc hs z.1] at hz'
    rw [Set.mem_iUnion] at hz'
    obtain ⟨q, hq⟩ := hz'
    by_cases hqt : Real.toNNReal (q : ℝ) < z.1
    · rw [ite_eq_left hqt] at hq
      rw [Set.mem_iUnion]
      exact ⟨q, ⟨hqt, hq⟩⟩
    · rw [ite_eq_right hqt] at hq
      exact False.elim hq
  · intro hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨q, hqt, hq⟩ := hz
    change Real.toNNReal (q : ℝ) < z.1 at hqt
    have hz' : z.2 ∈
        {ω | MeasureTheory.hittingAfter u s 0 ω < (z.1 : WithTop ℝ≥0)} := by
      rw [hittingAfter_zero_lt_set_eq_iUnion_rat_of_rightContinuous hrc hs z.1,
        Set.mem_iUnion]
      refine ⟨q, ?_⟩
      rw [ite_eq_left hqt]
      exact hq
    exact hz'

/-- A continuous adapted process has a stopping time when it first reaches an open set. -/
theorem MeasureTheory.Adapted.isStoppingTime_hittingAfter_zero_isOpen
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [ℱ.IsRightContinuous] {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u) (hcont : ∀ ω, Continuous fun t ↦ u t ω) (hs : IsOpen s) :
    IsStoppingTime ℱ (MeasureTheory.hittingAfter u s 0) := by
  apply MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  rw [hittingAfter_zero_lt_set_eq_iUnion_rat hcont hs t]
  refine MeasurableSet.iUnion fun q ↦ ?_
  by_cases hqt : Real.toNNReal (q : ℝ) < t
  · rw [ite_eq_left hqt]
    exact ℱ.mono hqt.le _ ((hu (Real.toNNReal (q : ℝ))) hs.measurableSet)
  · rw [ite_eq_right hqt]
    exact @MeasurableSet.empty Ω (ℱ t)

/-- A right-continuous adapted process first enters an open set at a stopping time. -/
theorem MeasureTheory.Adapted.isStoppingTime_hittingAfter_zero_isOpen_of_rightContinuous
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [ℱ.IsRightContinuous] {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u)
    (hrc : ∀ ω t, ContinuousWithinAt (fun r ↦ u r ω) (Ici t) t)
    (hs : IsOpen s) :
    IsStoppingTime ℱ (MeasureTheory.hittingAfter u s 0) := by
  apply MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  rw [hittingAfter_zero_lt_set_eq_iUnion_rat_of_rightContinuous hrc hs t]
  refine MeasurableSet.iUnion fun q ↦ ?_
  by_cases hqt : Real.toNNReal (q : ℝ) < t
  · rw [ite_eq_left hqt]
    exact ℱ.mono hqt.le _ ((hu (Real.toNNReal (q : ℝ))) hs.measurableSet)
  · rw [ite_eq_right hqt]
    exact @MeasurableSet.empty Ω (ℱ t)

/-- The set strictly after a continuous open-set hitting time is predictable. -/
theorem measurableSet_afterStartSet_hittingAfter_zero_isOpen
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u) (hcont : ∀ ω, Continuous fun t ↦ u t ω) (hs : IsOpen s) :
    MeasurableSet[ℱ.predictable]
      (afterStartSet (MeasureTheory.hittingAfter u s 0)) := by
  rw [afterStartSet_hittingAfter_zero_eq_iUnion_rat hcont hs]
  refine MeasurableSet.iUnion fun q ↦ ?_
  exact measurableSet_predictable_Ioi_prod
    (𝓕 := ℱ) (i := Real.toNNReal (q : ℝ))
    ((hu (Real.toNNReal (q : ℝ))) hs.measurableSet)

/-- For a right-continuous adapted process, the set strictly after its first open-set hit is
predictable. -/
theorem measurableSet_afterStartSet_hittingAfter_zero_isOpen_of_rightContinuous
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u)
    (hrc : ∀ ω t, ContinuousWithinAt (fun r ↦ u r ω) (Ici t) t)
    (hs : IsOpen s) :
    MeasurableSet[ℱ.predictable]
      (afterStartSet (MeasureTheory.hittingAfter u s 0)) := by
  rw [afterStartSet_hittingAfter_zero_eq_iUnion_rat_of_rightContinuous hrc hs]
  refine MeasurableSet.iUnion fun q ↦ ?_
  exact measurableSet_predictable_Ioi_prod
    (𝓕 := ℱ) (i := Real.toNNReal (q : ℝ))
    ((hu (Real.toNNReal (q : ℝ))) hs.measurableSet)

/-- The right-closed stochastic interval through a continuous open-set hitting time is
predictable, without a finite-range assumption on the hitting time. -/
theorem measurableSet_throughStopSet_hittingAfter_zero_isOpen
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u) (hcont : ∀ ω, Continuous fun t ↦ u t ω) (hs : IsOpen s) :
    MeasurableSet[ℱ.predictable]
      (throughStopSet (MeasureTheory.hittingAfter u s 0)) := by
  rw [throughStopSet_eq_compl_afterStartSet]
  exact (measurableSet_afterStartSet_hittingAfter_zero_isOpen hu hcont hs).compl

/-- Right-continuous version of predictability for the right-closed stochastic interval. -/
theorem measurableSet_throughStopSet_hittingAfter_zero_isOpen_of_rightContinuous
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u)
    (hrc : ∀ ω t, ContinuousWithinAt (fun r ↦ u r ω) (Ici t) t)
    (hs : IsOpen s) :
    MeasurableSet[ℱ.predictable]
      (throughStopSet (MeasureTheory.hittingAfter u s 0)) := by
  rw [throughStopSet_eq_compl_afterStartSet]
  exact (measurableSet_afterStartSet_hittingAfter_zero_isOpen_of_rightContinuous
    hu hrc hs).compl

/-- Predictability of the right-closed zero--one mask through an open hitting time. -/
theorem throughStopMask_hittingAfter_zero_predictable
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u) (hcont : ∀ ω, Continuous fun t ↦ u t ω) (hs : IsOpen s) :
    IsStronglyPredictable ℱ
      (throughStopMask (MeasureTheory.hittingAfter u s 0)) := by
  classical
  have hset := measurableSet_throughStopSet_hittingAfter_zero_isOpen hu hcont hs
  change StronglyMeasurable[ℱ.predictable]
    (Function.uncurry (throughStopMask (MeasureTheory.hittingAfter u s 0)))
  have hEq : Function.uncurry
      (throughStopMask (MeasureTheory.hittingAfter u s 0)) =
        (throughStopSet (MeasureTheory.hittingAfter u s 0)).indicator
          (fun _ ↦ (1 : ℝ)) := by
    funext z
    rcases z with ⟨t, ω⟩
    by_cases hz : (t : WithTop ℝ≥0) ≤ MeasureTheory.hittingAfter u s 0 ω
    · change (if (t : WithTop ℝ≥0) ≤ MeasureTheory.hittingAfter u s 0 ω then 1 else 0) =
        if (t, ω) ∈ throughStopSet (MeasureTheory.hittingAfter u s 0) then 1 else 0
      simp only [throughStopSet, Set.mem_ofPred_eq, hz]
    · change (if (t : WithTop ℝ≥0) ≤ MeasureTheory.hittingAfter u s 0 ω then 1 else 0) =
        if (t, ω) ∈ throughStopSet (MeasureTheory.hittingAfter u s 0) then 1 else 0
      simp only [throughStopSet, Set.mem_ofPred_eq, hz]
  rw [hEq]
  exact stronglyMeasurable_const.indicator hset

/-- Predictability of the through-stop mask for a right-continuous open hitting time. -/
theorem throughStopMask_hittingAfter_zero_predictable_of_rightContinuous
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u)
    (hrc : ∀ ω t, ContinuousWithinAt (fun r ↦ u r ω) (Ici t) t)
    (hs : IsOpen s) :
    IsStronglyPredictable ℱ
      (throughStopMask (MeasureTheory.hittingAfter u s 0)) := by
  classical
  have hset :=
    measurableSet_throughStopSet_hittingAfter_zero_isOpen_of_rightContinuous hu hrc hs
  change StronglyMeasurable[ℱ.predictable]
    (Function.uncurry (throughStopMask (MeasureTheory.hittingAfter u s 0)))
  have hEq : Function.uncurry
      (throughStopMask (MeasureTheory.hittingAfter u s 0)) =
        (throughStopSet (MeasureTheory.hittingAfter u s 0)).indicator
          (fun _ ↦ (1 : ℝ)) := by
    funext z
    rcases z with ⟨t, ω⟩
    by_cases hz : (t : WithTop ℝ≥0) ≤ MeasureTheory.hittingAfter u s 0 ω
    · change (if (t : WithTop ℝ≥0) ≤ MeasureTheory.hittingAfter u s 0 ω then 1 else 0) =
        if (t, ω) ∈ throughStopSet (MeasureTheory.hittingAfter u s 0) then 1 else 0
      simp only [throughStopSet, Set.mem_ofPred_eq, hz]
    · change (if (t : WithTop ℝ≥0) ≤ MeasureTheory.hittingAfter u s 0 ω then 1 else 0) =
        if (t, ω) ∈ throughStopSet (MeasureTheory.hittingAfter u s 0) then 1 else 0
      simp only [throughStopSet, Set.mem_ofPred_eq, hz]
  rw [hEq]
  exact stronglyMeasurable_const.indicator hset

/-- The through-stop mask of a continuous open hitting time is a bounded simple predictable
transform even when the hitting time has infinite range. -/
theorem throughStopMask_hittingAfter_zero_boundedSimplePredictable
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u) (hcont : ∀ ω, Continuous fun t ↦ u t ω) (hs : IsOpen s) :
    IsBoundedSimplePredictable ℱ
      (throughStopMask (MeasureTheory.hittingAfter u s 0)) := by
  apply IsBoundedSimplePredictable.of_binary_mask
    (throughStopMask_hittingAfter_zero_predictable hu hcont hs)
  intro t ω
  by_cases h : (t : WithTop ℝ≥0) ≤ MeasureTheory.hittingAfter u s 0 ω
  · exact Or.inr (by simp only [throughStopMask, ite_eq_left h])
  · exact Or.inl (by simp only [throughStopMask, ite_eq_right h])

/-- A right-continuous open hitting time has a bounded simple predictable through-stop mask. -/
theorem throughStopMask_hittingAfter_zero_boundedSimplePredictable_of_rightContinuous
    [MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [OpensMeasurableSpace β] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {u : ℝ≥0 → Ω → β} {s : Set β}
    (hu : Adapted ℱ u)
    (hrc : ∀ ω t, ContinuousWithinAt (fun r ↦ u r ω) (Ici t) t)
    (hs : IsOpen s) :
    IsBoundedSimplePredictable ℱ
      (throughStopMask (MeasureTheory.hittingAfter u s 0)) := by
  apply IsBoundedSimplePredictable.of_binary_mask
    (throughStopMask_hittingAfter_zero_predictable_of_rightContinuous hu hrc hs)
  intro t ω
  by_cases h : (t : WithTop ℝ≥0) ≤ MeasureTheory.hittingAfter u s 0 ω
  · exact Or.inr (by simp only [throughStopMask, ite_eq_left h])
  · exact Or.inl (by simp only [throughStopMask, ite_eq_right h])

/-- Strictly before an open hitting time, the process has not entered the target set. -/
theorem not_mem_of_lt_hittingAfter_zero
    {u : ℝ≥0 → Ω → β} {s : Set β}
    {t : ℝ≥0} {ω : Ω}
    (ht : (t : WithTop ℝ≥0) < MeasureTheory.hittingAfter u s 0 ω) :
    u t ω ∉ s :=
  MeasureTheory.notMem_of_lt_hittingAfter
    (u := u) (s := s) (n := 0) (k := t) ht bot_le

end

end OTSelector.CountingProcess
