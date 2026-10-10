import OTSelector.PointProcess.FeedbackCellConfiguration
import OTSelector.PointProcess.CountingKernel

/-!
# The actual return roots as a measurable locally finite configuration

The roots are the signed sums of the actual return-cell lengths.  Their half-open intervals
partition the line almost surely.  The configuration below keeps every root and permits an
arbitrary spatial observation offset; invalid paths have the empty configuration.
-/

open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators Classical ENNReal

namespace OTSelector.Limit

open PointProcess

private theorem finite_feedbackCellRoots_window (w : FeedbackCellSequence) (a b : ℝ) :
    {j : ℤ | feedbackCellRootsGood w ∧ feedbackCellRoot w j ∈ Icc a b}.Finite := by
  by_cases hw : feedbackCellRootsGood w
  · apply (finite_feedbackCellIntervals_inter_Icc hw a b).subset
    intro j hj
    exact ⟨feedbackCellRoot w j,
      ⟨le_rfl, (strictMono_feedbackCellRoot hw.1) (by omega)⟩, hj.2⟩
  · simpa only [hw, false_and, Set.ofPred_false] using (finite_empty : (∅ : Set ℤ).Finite)

private theorem finite_feedbackCellRoots_shell (w : FeedbackCellSequence) (a : ℝ) (n : ℕ) :
    {j : ℤ | feedbackCellRootsGood w ∧
      LocalConfiguration.shellIndex (0 : ℝ) (feedbackCellRoot w j - a) = n}.Finite := by
  apply (finite_feedbackCellRoots_window w (a - ((n : ℝ) + 1)) (a + ((n : ℝ) + 1))).subset
  rintro j ⟨hw, hj⟩
  refine ⟨hw, ?_⟩
  have hd := ((LocalConfiguration.shellIndex_eq_iff (0 : ℝ) _ n).mp hj).2
  simp only [Real.dist_eq, sub_zero] at hd
  have habs := abs_lt.mp hd
  constructor <;> linarith

/-- All actual return roots, viewed from physical position `a`. -/
noncomputable def feedbackReturnConfiguration (w : FeedbackCellSequence) (a : ℝ) :
    LocalConfiguration (0 : ℝ) :=
  indexedConfiguration 0 (fun _ : ℤ ↦ feedbackCellRootsGood w)
    (fun j ↦ feedbackCellRoot w j - a) (finite_feedbackCellRoots_shell w a)

/-- Exact atomic measure of the actual return roots. -/
theorem countingMeasure_feedbackReturnConfiguration (w : FeedbackCellSequence) (a : ℝ) :
    LocalConfiguration.countingMeasure (feedbackReturnConfiguration w a) =
      Measure.sum (fun j : ℤ ↦ if feedbackCellRootsGood w then
        Measure.dirac (feedbackCellRoot w j - a) else 0) :=
  countingMeasure_indexedConfiguration _ _ _ _

theorem countingMeasure_feedbackReturnConfiguration_of_good {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (a : ℝ) :
    LocalConfiguration.countingMeasure (feedbackReturnConfiguration w a) =
      Measure.sum (fun j : ℤ ↦ Measure.dirac (feedbackCellRoot w j - a)) := by
  simp only [countingMeasure_feedbackReturnConfiguration, hw, ↓reduceIte]

/-- Return configurations are jointly measurable in the iid cells and the observation root. -/
theorem measurable_feedbackReturnConfiguration :
    Measurable (fun p : FeedbackCellSequence × ℝ ↦ feedbackReturnConfiguration p.1 p.2) := by
  apply LocalConfiguration.measurable_iff_countingMeasure_comp.mpr
  simp_rw [countingMeasure_feedbackReturnConfiguration]
  apply Measure.measurable_measure.mpr
  intro s hs
  simp_rw [Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro j
  have hm : Measurable (fun p : FeedbackCellSequence × ℝ ↦
      if feedbackCellRootsGood p.1 then Measure.dirac (feedbackCellRoot p.1 j - p.2)
      else (0 : Measure ℝ)) :=
    (Measure.measurable_dirac.comp
      (((measurable_feedbackCellRoot j).comp measurable_fst).sub measurable_snd)).ite
      (measurableSet_feedbackCellRootsGood.preimage measurable_fst) measurable_const
  exact (Measure.measurable_coe hs).comp hm

/-- S-finiteness of the random return counting kernel is supplied by the proved shell code. -/
noncomputable def feedbackReturnCountingKernel : Kernel (FeedbackCellSequence × ℝ) ℝ :=
  LocalConfiguration.randomCountingKernel
    (fun p ↦ feedbackReturnConfiguration p.1 p.2) measurable_feedbackReturnConfiguration

instance : IsSFiniteKernel feedbackReturnCountingKernel := by
  unfold feedbackReturnCountingKernel
  infer_instance

@[simp]
theorem feedbackReturnCountingKernel_apply (p : FeedbackCellSequence × ℝ) :
    feedbackReturnCountingKernel p =
      LocalConfiguration.countingMeasure (feedbackReturnConfiguration p.1 p.2) := rfl

private theorem feedbackCellRootsGood_shift_iff (w : FeedbackCellSequence) (k : ℤ) :
    feedbackCellRootsGood (IIDShift.shift k w) ↔ feedbackCellRootsGood w := by
  constructor
  · intro h
    simpa only [← IIDShift.shift_add, neg_add_cancel, IIDShift.shift_zero] using h.shift (-k)
  · exact fun h ↦ h.shift k

/-- Reindexing the cells leaves the actual spatial return configuration unchanged. -/
theorem feedbackReturnConfiguration_shift (w : FeedbackCellSequence) (k : ℤ) (a : ℝ) :
    feedbackReturnConfiguration (IIDShift.shift k w) (a - feedbackCellRoot w k) =
      feedbackReturnConfiguration w a := by
  apply LocalConfiguration.countingMeasure_injective
  rw [countingMeasure_feedbackReturnConfiguration, countingMeasure_feedbackReturnConfiguration]
  refine Eq.trans ?_ (Measure.sum_comp_equiv (Equiv.addRight k) _)
  apply congrArg Measure.sum
  funext j
  change (if feedbackCellRootsGood (IIDShift.shift k w) then
      Measure.dirac (feedbackCellRoot (IIDShift.shift k w) j - (a - feedbackCellRoot w k))
      else 0) = if feedbackCellRootsGood w then Measure.dirac (feedbackCellRoot w (j + k) - a) else 0
  rw [feedbackCellRootsGood_shift_iff, feedbackCellRoot_shift]
  have h : feedbackCellRoot w (j + k) - feedbackCellRoot w k - (a - feedbackCellRoot w k) =
      feedbackCellRoot w (j + k) - a := by ring
  rw [h]

/-- Moving the observation root translates the actual return counting measure. -/
theorem countingMeasure_feedbackReturnConfiguration_add (w : FeedbackCellSequence) (a b : ℝ) :
    LocalConfiguration.countingMeasure (feedbackReturnConfiguration w (a + b)) =
      (LocalConfiguration.countingMeasure (feedbackReturnConfiguration w a)).map (fun x ↦ x - b) := by
  have hsub : Measurable (fun x : ℝ ↦ x - b) := measurable_id.sub_const b
  rw [countingMeasure_feedbackReturnConfiguration, countingMeasure_feedbackReturnConfiguration,
    Measure.map_sum hsub.aemeasurable]
  apply congrArg Measure.sum
  funext j
  by_cases hw : feedbackCellRootsGood w
  · rw [ite_eq_left hw, ite_eq_left hw, Measure.map_dirac' hsub]
    congr 1
    ring
  · simp only [hw, ↓reduceIte, Measure.map_zero]

/-- The actual root intervals are a disjoint cover of the spatial line. -/
theorem feedbackCellRoot_intervals_partition {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) :
    (⋃ j : ℤ, Ico (feedbackCellRoot w j) (feedbackCellRoot w (j + 1))) = univ ∧
      Pairwise (Disjoint on fun j : ℤ ↦ Ico (feedbackCellRoot w j) (feedbackCellRoot w (j + 1))) := by
  constructor
  · apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr ⟨feedbackCellIndex w x, feedbackCellIndex_bounds hw x⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (feedbackCellRoot_interval_unique hw hi hj)

/-- Nonnegative integration over all actual cells is exactly integration over the line. -/
theorem tsum_lintegral_feedbackCellRoot_intervals {w : FeedbackCellSequence}
    (hw : feedbackCellRootsGood w) (f : ℝ → ℝ≥0∞) :
    (∑' j : ℤ, ∫⁻ x in Ico (feedbackCellRoot w j) (feedbackCellRoot w (j + 1)), f x) =
      ∫⁻ x, f x := by
  rw [← lintegral_iUnion (fun _ ↦ measurableSet_Ico)
    (feedbackCellRoot_intervals_partition hw).2,
    (feedbackCellRoot_intervals_partition hw).1, Measure.restrict_univ]

end OTSelector.Limit
