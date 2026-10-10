import OTSelector.Limit.FeedbackCellRoots
import OTSelector.Limit.FeedbackCellGeometry
import OTSelector.PointProcess.FiniteMatchingScene
import OTSelector.PointProcess.LocalConfigurationTranslation
import OTSelector.PointProcess.MatchingSceneReroot

/-!
# Actual marked point configurations assembled from the iid return cells

The positive-index jumps up to each first return are placed at the corresponding cell root
plus their physical clock.  Upward jumps form the source configuration and downward jumps the
target configuration.  Events belong to the right-closed cell interval, so a return jump is
included once.  The exceptional invalid paths are mapped to the empty configuration.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators Classical ENNReal

namespace OTSelector.PointProcess

open OTSelector.Limit

noncomputable def indexedConfiguration {X ι : Type*} [MetricSpace X]
    (base : X) (P : ι → Prop) (point : ι → X)
    (h : ∀ n, {i | P i ∧ LocalConfiguration.shellIndex base (point i) = n}.Finite) :
    LocalConfiguration base := fun n ↦
  ∑ i ∈ (h n).toFinset, if hi : LocalConfiguration.shellIndex base (point i) = n then
    {⟨point i, hi⟩} else 0

private theorem sum_map_multiset {Y Z ι : Type*} [AddCommMonoid Z]
    (s : Finset ι) (m : ι → Multiset Y) (f : Y → Z) :
    ((∑ i ∈ s, m i).map f).sum = ∑ i ∈ s, ((m i).map f).sum := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Multiset.map_add]

theorem countingMeasure_indexedConfiguration {X ι : Type*}
    [MetricSpace X] [MeasurableSpace X] [Countable ι]
    (base : X) (P : ι → Prop) (point : ι → X)
    (h : ∀ n, {i | P i ∧ LocalConfiguration.shellIndex base (point i) = n}.Finite) :
    LocalConfiguration.countingMeasure (indexedConfiguration base P point h) =
      Measure.sum (fun i ↦ if P i then Measure.dirac (point i) else 0) := by
  ext s hs
  rw [LocalConfiguration.countingMeasure_apply _ hs, Measure.sum_apply _ hs]
  have hshell (n : ℕ) :
      LocalConfiguration.shellMeasure (indexedConfiguration base P point h) n s =
        ∑' i, if P i ∧ LocalConfiguration.shellIndex base (point i) = n then
          s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (point i) else 0 := by
    rw [LocalConfiguration.shellMeasure_apply _ _ hs]
    simp only [indexedConfiguration, sum_map_multiset]
    rw [tsum_eq_sum (s := (h n).toFinset)]
    · apply Finset.sum_congr rfl
      intro i hi
      have hp := (h n).mem_toFinset.mp hi
      simp [hp.1, hp.2]
    · intro i hi
      have hp : ¬(P i ∧ LocalConfiguration.shellIndex base (point i) = n) := by
        simpa using hi
      simp [hp]
  simp_rw [hshell]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro i
  by_cases hi : P i
  · simp only [hi, true_and, ↓reduceIte]
    rw [tsum_eq_single (LocalConfiguration.shellIndex base (point i))]
    · rw [ite_eq_left rfl, Measure.dirac_apply' _ hs]
      rfl
    · intro n hn
      simp [Ne.symm hn]
  · simp [hi]

/-- Geometry needed to place actual cell events in finite spatial windows. -/
def feedbackCellConfigurationGood (w : FeedbackCellSequence) : Prop :=
  feedbackCellRootsGood w ∧ ∀ j : ℤ,
    (∀ i : ℕ, 0 < (w j (i + 1)).1) ∧ 0 < feedbackMarkedFirstReturnIndex (w j)

theorem measurableSet_feedbackCellConfigurationGood :
    MeasurableSet {w | feedbackCellConfigurationGood w} := by
  unfold feedbackCellConfigurationGood
  simp only [ofPred_and, ofPred_forall]
  refine measurableSet_feedbackCellRootsGood.inter (MeasurableSet.iInter fun j ↦ ?_)
  refine (MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const
    (by fun_prop)).inter ?_
  exact measurableSet_lt measurable_const
    (measurable_feedbackMarkedFirstReturnIndex.comp (measurable_pi_apply j))

theorem feedbackCellBase_configuration_good {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, feedbackCellConfigurationGood w := by
  have hcells : ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam, ∀ j : ℤ,
      (∀ i : ℕ, 0 < (w j (i + 1)).1) ∧ 0 < feedbackMarkedFirstReturnIndex (w j) := by
    rw [ae_all_iff]
    intro j
    exact (feedbackCellBase_eval_measurePreserving hlam0 hlam j).quasiMeasurePreserving.ae
      ((feedbackMarkedTrajectory_waits_positive hlam0 hlam 0).and
        (feedbackMarkedFirstReturnIndex_pos hlam0 hlam))
  filter_upwards [feedbackCellBase_roots_good hlam0 hlam, hcells] with w hw hc
  exact ⟨hw, hc⟩

theorem feedbackCellConfigurationGood.shift {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (k : ℤ) :
    feedbackCellConfigurationGood (IIDShift.shift k w) :=
  ⟨hw.1.shift k, fun j ↦ hw.2 (j + k)⟩

/-- Event label `(j,n)` denotes positive-index jump `n+1` of cell `j`. -/
def feedbackCellEventActive (w : FeedbackCellSequence) (direction : ℤ) (i : ℤ × ℕ) : Prop :=
  feedbackCellConfigurationGood w ∧ i.2 < feedbackMarkedFirstReturnIndex (w i.1) ∧
    (w i.1 (i.2 + 1)).2.2 - (w i.1 i.2).2.2 = direction

/-- The actual physical coordinate and actual sampled mark of a cell jump. -/
noncomputable def feedbackCellEventPoint (w : FeedbackCellSequence) (i : ℤ × ℕ) :
    MatchingPoint :=
  (feedbackCellRoot w i.1 + feedbackCellClock (w i.1) (i.2 + 1), (w i.1 (i.2 + 1)).2.1)

@[fun_prop]
theorem measurable_feedbackCellEventPoint (i : ℤ × ℕ) :
    Measurable (fun w ↦ feedbackCellEventPoint w i) := by
  unfold feedbackCellEventPoint
  fun_prop

theorem measurableSet_feedbackCellEventActive (direction : ℤ) (i : ℤ × ℕ) :
    MeasurableSet {w | feedbackCellEventActive w direction i} := by
  unfold feedbackCellEventActive
  exact measurableSet_feedbackCellConfigurationGood.inter
    ((measurableSet_lt measurable_const
      (measurable_feedbackMarkedFirstReturnIndex.comp (measurable_pi_apply i.1))).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const))

/-- A retained actual event lies in the right-closed interval of its own cell. -/
theorem feedbackCellEventPoint_mem_cell {w : FeedbackCellSequence} {direction : ℤ} {i : ℤ × ℕ}
    (hi : feedbackCellEventActive w direction i) :
    (feedbackCellEventPoint w i).1 ∈
      Ioc (feedbackCellRoot w i.1) (feedbackCellRoot w (i.1 + 1)) := by
  have hc := feedbackCellClock_strictMono (w i.1) (hi.1.2 i.1).1
  have hpos := hc (Nat.succ_pos i.2)
  rw [feedbackCellClock_zero] at hpos
  have hle := hc.monotone (show i.2 + 1 ≤ feedbackMarkedFirstReturnIndex (w i.1) by
    exact Nat.succ_le_of_lt hi.2.1)
  rw [← feedbackCellLength_eq_clock (w i.1) (hi.1.2 i.1).1 (hi.1.2 i.1).2] at hle
  change feedbackCellRoot w i.1 < feedbackCellRoot w i.1 +
    feedbackCellClock (w i.1) (i.2 + 1) ∧
    feedbackCellRoot w i.1 + feedbackCellClock (w i.1) (i.2 + 1) ≤ _
  rw [feedbackCellRoot_add_one]
  constructor <;> linarith

/-- A bounded observation window contains only finitely many retained event labels. -/
theorem finite_feedbackCellEvents_window (w : FeedbackCellSequence) (direction : ℤ) (a b : ℝ) :
    {i : ℤ × ℕ | feedbackCellEventActive w direction i ∧
      (feedbackCellEventPoint w i).1 ∈ Icc a b}.Finite := by
  by_cases hw : feedbackCellConfigurationGood w
  · have hfinite : (⋃ j ∈ Icc (feedbackCellIndex w a - 1) (feedbackCellIndex w b),
        (fun n : ℕ ↦ (j, n)) '' {n | n < feedbackMarkedFirstReturnIndex (w j)}).Finite :=
      (Set.finite_Icc _ _).biUnion fun j _ ↦
        (Set.finite_lt_nat _).image _
    apply hfinite.subset
    rintro ⟨j, n⟩ ⟨hi, hwin⟩
    have hcell := feedbackCellEventPoint_mem_cell hi
    have ha := feedbackCellIndex_bounds hw.1 a
    have hb := feedbackCellIndex_bounds hw.1 b
    have hm := strictMono_feedbackCellRoot hw.1.1
    have hj : j ∈ Icc (feedbackCellIndex w a - 1) (feedbackCellIndex w b) := by
      constructor
      · by_contra h
        have hr := hm (show j + 1 < feedbackCellIndex w a by omega)
        linarith [hcell.2, hwin.1]
      · by_contra h
        have hr := hm.monotone (show feedbackCellIndex w b + 1 ≤ j by omega)
        linarith [hcell.1, hwin.2]
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, ⟨n, hi.2.1, rfl⟩⟩⟩
  · have he : {i : ℤ × ℕ | feedbackCellEventActive w direction i ∧
        (feedbackCellEventPoint w i).1 ∈ Icc a b} = ∅ := by
      ext i
      simp [feedbackCellEventActive, hw]
    rw [he]
    exact finite_empty

private theorem finite_feedbackCellEvents_shell (w : FeedbackCellSequence) (direction : ℤ)
    (n : ℕ) : {i : ℤ × ℕ | feedbackCellEventActive w direction i ∧
      LocalConfiguration.shellIndex matchingPointBase (feedbackCellEventPoint w i) = n}.Finite := by
  apply (finite_feedbackCellEvents_window w direction (-((n : ℝ) + 1)) ((n : ℝ) + 1)).subset
  rintro i ⟨hi, hs⟩
  refine ⟨hi, ?_⟩
  have hd := ((LocalConfiguration.shellIndex_eq_iff matchingPointBase
    (feedbackCellEventPoint w i) n).mp hs).2
  have hdist : |(feedbackCellEventPoint w i).1| ≤
      dist (feedbackCellEventPoint w i) matchingPointBase := by
    simpa only [Prod.dist_eq, matchingPointBase, Real.dist_eq, sub_zero] using
      (le_max_left (dist (feedbackCellEventPoint w i).1 (0 : ℝ))
        (dist (feedbackCellEventPoint w i).2 matchingPointBase.2))
  exact ⟨by linarith [neg_abs_le (feedbackCellEventPoint w i).1],
    by linarith [le_abs_self (feedbackCellEventPoint w i).1]⟩

/-- The marked configuration formed by all jumps of a specified current direction. -/
noncomputable def feedbackConcatenatedPoints (direction : ℤ) (w : FeedbackCellSequence) :
    LocalConfiguration matchingPointBase :=
  indexedConfiguration matchingPointBase (feedbackCellEventActive w direction)
    (feedbackCellEventPoint w) (finite_feedbackCellEvents_shell w direction)

/-- The source configuration uses the actual upward jumps, including each return endpoint once. -/
noncomputable def feedbackConcatenatedSource := feedbackConcatenatedPoints 1

/-- The target configuration uses the actual downward jumps and their actual sampled marks. -/
noncomputable def feedbackConcatenatedTarget := feedbackConcatenatedPoints (-1)

/-- Exact counting measure of the concatenation, retaining multiplicities of all event labels. -/
theorem countingMeasure_feedbackConcatenatedPoints (direction : ℤ) (w : FeedbackCellSequence) :
    LocalConfiguration.countingMeasure (feedbackConcatenatedPoints direction w) =
      Measure.sum (fun i : ℤ × ℕ ↦ if feedbackCellEventActive w direction i then
        Measure.dirac (feedbackCellEventPoint w i) else 0) :=
  countingMeasure_indexedConfiguration _ _ _ _

@[fun_prop]
theorem measurable_feedbackConcatenatedPoints (direction : ℤ) :
    Measurable (feedbackConcatenatedPoints direction) := by
  apply LocalConfiguration.measurable_iff_countingMeasure_comp.mpr
  simp_rw [countingMeasure_feedbackConcatenatedPoints]
  apply Measure.measurable_measure.mpr
  intro s hs
  simp_rw [Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro i
  have hi : Measurable (fun w ↦ if feedbackCellEventActive w direction i then
      Measure.dirac (feedbackCellEventPoint w i) else (0 : Measure MatchingPoint)) :=
    (Measure.measurable_dirac.comp (measurable_feedbackCellEventPoint i)).ite
    (measurableSet_feedbackCellEventActive direction i) measurable_const
  exact (Measure.measurable_coe hs).comp hi

@[fun_prop]
theorem measurable_feedbackConcatenatedSource : Measurable feedbackConcatenatedSource :=
  measurable_feedbackConcatenatedPoints 1

@[fun_prop]
theorem measurable_feedbackConcatenatedTarget : Measurable feedbackConcatenatedTarget :=
  measurable_feedbackConcatenatedPoints (-1)

theorem feedbackCellConfigurationGood_shift_iff (w : FeedbackCellSequence) (k : ℤ) :
    feedbackCellConfigurationGood (IIDShift.shift k w) ↔ feedbackCellConfigurationGood w := by
  constructor
  · intro h
    simpa only [← IIDShift.shift_add, neg_add_cancel, IIDShift.shift_zero] using h.shift (-k)
  · exact fun h ↦ h.shift k

theorem feedbackCellEventActive_shift (w : FeedbackCellSequence) (direction k : ℤ) (i : ℤ × ℕ) :
    feedbackCellEventActive (IIDShift.shift k w) direction i ↔
      feedbackCellEventActive w direction (i.1 + k, i.2) := by
  simp only [feedbackCellEventActive, feedbackCellConfigurationGood_shift_iff, IIDShift.shift]

theorem feedbackCellEventPoint_shift (w : FeedbackCellSequence) (k : ℤ) (i : ℤ × ℕ) :
    feedbackCellEventPoint (IIDShift.shift k w) i =
      Configuration.pointTranslation (-feedbackCellRoot w k)
        (feedbackCellEventPoint w (i.1 + k, i.2)) := by
  simp only [feedbackCellEventPoint, feedbackCellRoot_shift, IIDShift.shift,
    Configuration.pointTranslation_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

/-- Moving any cell to index zero reroots both actual event configurations by its old root. -/
theorem feedbackConcatenatedPoints_shift (direction : ℤ) (w : FeedbackCellSequence) (k : ℤ) :
    feedbackConcatenatedPoints direction (IIDShift.shift k w) =
      LocalConfiguration.reroot (feedbackCellRoot w k) (feedbackConcatenatedPoints direction w) := by
  apply LocalConfiguration.countingMeasure_injective
  rw [LocalConfiguration.countingMeasure_reroot, countingMeasure_feedbackConcatenatedPoints,
    countingMeasure_feedbackConcatenatedPoints,
    Measure.map_sum (Configuration.pointTranslation (-feedbackCellRoot w k)).measurable.aemeasurable]
  let e : (ℤ × ℕ) ≃ (ℤ × ℕ) := (Equiv.addRight k).prodCongr (Equiv.refl ℕ)
  refine Eq.trans ?_ (Measure.sum_comp_equiv e _)
  apply congrArg Measure.sum
  funext i
  change (if feedbackCellEventActive (IIDShift.shift k w) direction i then
      Measure.dirac (feedbackCellEventPoint (IIDShift.shift k w) i) else 0) =
    (if feedbackCellEventActive w direction (i.1 + k, i.2) then
      Measure.dirac (feedbackCellEventPoint w (i.1 + k, i.2)) else 0).map
        (Configuration.pointTranslation (-feedbackCellRoot w k))
  rw [feedbackCellEventPoint_shift]
  by_cases hi : feedbackCellEventActive w direction (i.1 + k, i.2)
  · rw [ite_eq_left ((feedbackCellEventActive_shift w direction k i).mpr hi), ite_eq_left hi,
      Measure.map_dirac' (Configuration.pointTranslation (-feedbackCellRoot w k)).measurable]
  · rw [ite_eq_right (fun h ↦ hi ((feedbackCellEventActive_shift w direction k i).mp h)),
      ite_eq_right hi, Measure.map_zero]

theorem feedbackConcatenatedSource_shift (w : FeedbackCellSequence) (k : ℤ) :
    feedbackConcatenatedSource (IIDShift.shift k w) =
      LocalConfiguration.reroot (feedbackCellRoot w k) (feedbackConcatenatedSource w) :=
  feedbackConcatenatedPoints_shift 1 w k

theorem feedbackConcatenatedTarget_shift (w : FeedbackCellSequence) (k : ℤ) :
    feedbackConcatenatedTarget (IIDShift.shift k w) =
      LocalConfiguration.reroot (feedbackCellRoot w k) (feedbackConcatenatedTarget w) :=
  feedbackConcatenatedPoints_shift (-1) w k

/-- Different right-closed cells share no event, including at their common root. -/
theorem feedbackCellEventPoint_mem_Ioc_roots_iff {w : FeedbackCellSequence} {direction : ℤ}
    {i : ℤ × ℕ} (hi : feedbackCellEventActive w direction i) (k : ℤ) :
    (feedbackCellEventPoint w i).1 ∈
      Ioc (feedbackCellRoot w k) (feedbackCellRoot w (k + 1)) ↔ i.1 = k := by
  have hc := feedbackCellEventPoint_mem_cell hi
  have hm := (strictMono_feedbackCellRoot hi.1.1.1).monotone
  constructor
  · intro hx
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hr := hm (show i.1 + 1 ≤ k by omega)
      linarith [hc.2, hx.1]
    · have hr := hm (show k + 1 ≤ i.1 by omega)
      linarith [hc.1, hx.2]
  · intro h
    simpa only [h] using hc

/-- Counting in an entire cell recovers exactly its retained finite jump count. -/
theorem countingMeasure_feedbackConcatenatedPoints_cell {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (direction k : ℤ) :
    LocalConfiguration.countingMeasure (feedbackConcatenatedPoints direction w)
      (LocalConfiguration.spatialIoc (feedbackCellRoot w k) (feedbackCellRoot w (k + 1))) =
      (((Finset.range (feedbackMarkedFirstReturnIndex (w k))).filter
        (fun n ↦ (w k (n + 1)).2.2 - (w k n).2.2 = direction)).card : ℝ≥0∞) := by
  let s := LocalConfiguration.spatialIoc (feedbackCellRoot w k) (feedbackCellRoot w (k + 1))
  have hs : MeasurableSet s := LocalConfiguration.measurableSet_spatialIoc _ _
  rw [countingMeasure_feedbackConcatenatedPoints, Measure.sum_apply _ hs]
  let t := (Finset.range (feedbackMarkedFirstReturnIndex (w k))).image (fun n ↦ (k, n))
  rw [tsum_eq_sum (s := t)]
  · rw [Finset.sum_image]
    · have hterm (n : ℕ) (hn : n ∈ Finset.range (feedbackMarkedFirstReturnIndex (w k))) :
          (if feedbackCellEventActive w direction (k, n) then
            Measure.dirac (feedbackCellEventPoint w (k, n)) else 0) s =
          if (w k (n + 1)).2.2 - (w k n).2.2 = direction then (1 : ℝ≥0∞) else 0 := by
        by_cases hd : (w k (n + 1)).2.2 - (w k n).2.2 = direction
        · have hi : feedbackCellEventActive w direction (k, n) :=
            ⟨hw, Finset.mem_range.mp hn, hd⟩
          have hp : feedbackCellEventPoint w (k, n) ∈ s :=
            (feedbackCellEventPoint_mem_Ioc_roots_iff hi k).mpr rfl
          simp [hi, hd, Measure.dirac_apply' _ hs, hp]
        · have hi : ¬ feedbackCellEventActive w direction (k, n) := fun h ↦ hd h.2.2
          simp [hi, hd]
      rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
    · intro a ha b hb hab
      exact Prod.mk.inj hab |>.2
  · intro i hi
    by_cases ha : feedbackCellEventActive w direction i
    · rw [ite_eq_left ha, Measure.dirac_apply' _ hs]
      apply Set.indicator_of_notMem
      intro hp
      have hik := (feedbackCellEventPoint_mem_Ioc_roots_iff ha k).mp hp
      apply hi
      exact Finset.mem_image.mpr ⟨i.2, Finset.mem_range.mpr (by simpa [hik] using ha.2.1),
        by ext <;> simp [hik]⟩
    · simp [ha]

theorem spatialCount_feedbackConcatenatedSource_cell {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (k : ℤ) :
    LocalConfiguration.spatialCount (feedbackConcatenatedSource w)
      (feedbackCellRoot w k) (feedbackCellRoot w (k + 1)) =
      ((feedbackCellSourceJumps (w k)).card : ℤ) := by
  have hfilter : (Finset.range (feedbackMarkedFirstReturnIndex (w k))).filter
      (fun n ↦ (w k (n + 1)).2.2 - (w k n).2.2 = 1) = feedbackCellSourceJumps (w k) := by
    ext n
    simp only [feedbackCellSourceJumps, Finset.mem_filter]
    constructor <;> rintro ⟨hn, h⟩ <;> exact ⟨hn, by omega⟩
  simp only [LocalConfiguration.spatialCount, Measure.real, feedbackConcatenatedSource,
    countingMeasure_feedbackConcatenatedPoints_cell hw, hfilter, ENNReal.toReal_natCast,
    Int.floor_natCast]

theorem spatialCount_feedbackConcatenatedTarget_cell {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (k : ℤ) :
    LocalConfiguration.spatialCount (feedbackConcatenatedTarget w)
      (feedbackCellRoot w k) (feedbackCellRoot w (k + 1)) =
      ((feedbackCellTargetJumps (w k)).card : ℤ) := by
  have hfilter : (Finset.range (feedbackMarkedFirstReturnIndex (w k))).filter
      (fun n ↦ (w k (n + 1)).2.2 - (w k n).2.2 = -1) = feedbackCellTargetJumps (w k) := by
    ext n
    simp only [feedbackCellTargetJumps, Finset.mem_filter]
    constructor <;> rintro ⟨hn, h⟩ <;> exact ⟨hn, by omega⟩
  simp only [LocalConfiguration.spatialCount, Measure.real, feedbackConcatenatedTarget,
    countingMeasure_feedbackConcatenatedPoints_cell hw, hfilter, ENNReal.toReal_natCast,
    Int.floor_natCast]

/-- A whole returning cell contributes zero source-minus-target oriented count. -/
theorem orientedCount_feedbackConcatenated_cell_balanced {w : FeedbackCellSequence}
    (hw : feedbackCellConfigurationGood w) (k : ℤ)
    (hbalance : (feedbackCellSourceJumps (w k)).card = (feedbackCellTargetJumps (w k)).card) :
    LocalConfiguration.orientedCount (feedbackConcatenatedSource w)
      (feedbackCellRoot w k) (feedbackCellRoot w (k + 1)) -
    LocalConfiguration.orientedCount (feedbackConcatenatedTarget w)
      (feedbackCellRoot w k) (feedbackCellRoot w (k + 1)) = 0 := by
  have hle := (strictMono_feedbackCellRoot hw.1.1).monotone (show k ≤ k + 1 by omega)
  simp only [LocalConfiguration.orientedCount,
    LocalConfiguration.spatialCount_eq_zero_of_le _ hle, sub_zero,
    spatialCount_feedbackConcatenatedSource_cell hw, spatialCount_feedbackConcatenatedTarget_cell hw,
    hbalance, sub_self]

/-- The actual iid environment satisfies the count identity needed for one-cell rerooting. -/
theorem feedbackCellBase_orientedCount_onecell_zero {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam < 1 / 2) :
    ∀ᵐ w ∂feedbackCellBase lam hlam0 hlam,
      LocalConfiguration.orientedCount (feedbackConcatenatedSource w) 0 (feedbackCellLength (w 0)) -
      LocalConfiguration.orientedCount (feedbackConcatenatedTarget w) 0 (feedbackCellLength (w 0)) = 0 := by
  have hbal := (feedbackCellBase_eval_measurePreserving hlam0 hlam 0).quasiMeasurePreserving.ae
    (feedbackMarkedTrajectory_cell_balanced hlam0 hlam)
  filter_upwards [feedbackCellBase_configuration_good hlam0 hlam, hbal] with w hw hb
  have hroot : feedbackCellRoot w (0 + 1) = feedbackCellLength (w 0) := by
    simpa only [feedbackCellRoot_zero, zero_add] using feedbackCellRoot_add_one w 0
  simpa only [feedbackCellRoot_zero, hroot] using
    orientedCount_feedbackConcatenated_cell_balanced hw 0 hb

end OTSelector.PointProcess
