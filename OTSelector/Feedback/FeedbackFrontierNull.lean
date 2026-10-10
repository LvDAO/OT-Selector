import OTSelector.Feedback.CrossingFibre
import OTSelector.Feedback.ForcedHistory
import OTSelector.Probability.IndependentFiberNull

/-!
# Nullity of fixed affine frontiers

For a fixed affine feedback state, a prescribed source or target label has a strictly monotone
crossing coordinate as a function of its height.  The height coordinate is independent of all
other sample coordinates under `finiteSampleLaw`; hence the equality of that crossing coordinate
with a deterministic frontier is a null event.  The same statement is then obtained for the
finite union of all source and target labels.

The state in this file is fixed.  In particular, no independence claim is made for an adaptive
state depending on the label being varied.  Adaptive event-time nullity requires the separate
forced-history reduction and is intentionally not asserted here.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Fixed-state frontier events -/

/-- The source frontier event for a fixed affine feedback state and deterministic coordinate. -/
def sourceAffineFrontierEvent (lam : ℝ) (state : FeedbackStepState n)
    (i : Fin n) (x : ℝ) : Set (FiniteSample n) :=
  {sample | state.sourceCoordinate sample lam i = x}

/-- The target frontier event for a fixed affine feedback state and deterministic coordinate. -/
def targetAffineFrontierEvent (lam : ℝ) (state : FeedbackStepState n)
    (j : Fin n) (x : ℝ) : Set (FiniteSample n) :=
  {sample | state.targetCoordinate sample lam j = x}

theorem measurableSet_sourceAffineFrontierEvent (lam : ℝ) (state : FeedbackStepState n)
    (i : Fin n) (x : ℝ) :
    MeasurableSet (sourceAffineFrontierEvent lam state i x) := by
  have hcoord : Measurable (fun sample : FiniteSample n ↦
      state.sourceCoordinate sample lam i) := by
    have hpair : Measurable (fun sample : FiniteSample n ↦ (sample, state)) :=
      measurable_id.prodMk measurable_const
    exact (measurable_sourceCoordinate lam i).comp hpair
  change MeasurableSet {sample : FiniteSample n | state.sourceCoordinate sample lam i = x}
  exact hcoord (measurableSet_singleton x)

theorem measurableSet_targetAffineFrontierEvent (lam : ℝ) (state : FeedbackStepState n)
    (j : Fin n) (x : ℝ) :
    MeasurableSet (targetAffineFrontierEvent lam state j x) := by
  have hcoord : Measurable (fun sample : FiniteSample n ↦
      state.targetCoordinate sample lam j) := by
    have hpair : Measurable (fun sample : FiniteSample n ↦ (sample, state)) :=
      measurable_id.prodMk measurable_const
    exact (measurable_targetCoordinate lam j).comp hpair
  change MeasurableSet {sample : FiniteSample n | state.targetCoordinate sample lam j = x}
  exact hcoord (measurableSet_singleton x)

theorem sourceAffineFrontierRestore_fibre_subsingleton
    {lam x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) (i : Fin n)
    (rest : FiniteSample n) :
    ({t : UnitMark |
      state.sourceCoordinate (FiniteSample.coordinateRestore (1, i) rest t) lam i = x}).Subsingleton := by
  have hn : 0 < n := by
    exact Nat.pos_of_ne_zero (by
      intro hn
      exact Fin.elim0 (hn ▸ i))
  intro t₁ ht₁ t₂ ht₂
  have hmark : (FiniteSample.coordinateRestore (1, i) rest t₁).sourceMark i =
      rest.sourceMark i := by
    simpa [FiniteSample.coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq_of_ne (n := n) (1, i) (0, i)
        (by simp) rest t₁)
  have hmark' : (FiniteSample.coordinateRestore (1, i) rest t₂).sourceMark i =
      rest.sourceMark i := by
    simpa [FiniteSample.coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq_of_ne (n := n) (1, i) (0, i)
        (by simp) rest t₂)
  have hslope₁ :
      (FiniteSample.coordinateRestore (1, i) rest t₁).sourceSlope i = rest.sourceSlope i := by
    simp [FiniteSample.sourceSlope, hmark]
  have hslope₂ :
      (FiniteSample.coordinateRestore (1, i) rest t₂).sourceSlope i = rest.sourceSlope i := by
    simp [FiniteSample.sourceSlope, hmark']
  have hheight₁ :
      (FiniteSample.coordinateRestore (1, i) rest t₁).sourceHeight i = t₁ := by
    simpa [FiniteSample.coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq (n := n) (1, i) rest t₁)
  have hheight₂ :
      (FiniteSample.coordinateRestore (1, i) rest t₂).sourceHeight i = t₂ := by
    simpa [FiniteSample.coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq (n := n) (1, i) rest t₂)
  have hcross₁ :
      state.sourceCoordinate (FiniteSample.coordinateRestore (1, i) rest t₁) lam i =
        sourceNatHeightCrossing n state.x state.p (state.slope lam)
          (rest.sourceSlope i) (t₁ : ℝ) := by
    simp [FeedbackStepState.sourceCoordinate, sourceNatHeightCrossing, hslope₁, hheight₁]
  have hcross₂ :
      state.sourceCoordinate (FiniteSample.coordinateRestore (1, i) rest t₂) lam i =
        sourceNatHeightCrossing n state.x state.p (state.slope lam)
          (rest.sourceSlope i) (t₂ : ℝ) := by
    simp [FeedbackStepState.sourceCoordinate, sourceNatHeightCrossing, hslope₂, hheight₂]
  have ha := rest.sourceSlope_mem i
  have hfiber := state.sourceHeightCrossing_unit_fibre_subsingleton
    (lam := lam) hlam0 hlamHalf ha.1 ha.2 hn x
  have ht₁' :
      sourceNatHeightCrossing n state.x state.p (state.slope lam)
          (rest.sourceSlope i) (t₁ : ℝ) = x := by
    change state.sourceCoordinate (FiniteSample.coordinateRestore (1, i) rest t₁) lam i = x
      at ht₁
    rw [hcross₁] at ht₁
    exact ht₁
  have ht₂' :
      sourceNatHeightCrossing n state.x state.p (state.slope lam)
          (rest.sourceSlope i) (t₂ : ℝ) = x := by
    change state.sourceCoordinate (FiniteSample.coordinateRestore (1, i) rest t₂) lam i = x
      at ht₂
    rw [hcross₂] at ht₂
    exact ht₂
  exact hfiber ht₁' ht₂'

theorem targetAffineFrontierRestore_fibre_subsingleton
    {lam x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) (j : Fin n)
    (rest : FiniteSample n) :
    ({t : UnitMark |
      state.targetCoordinate (FiniteSample.coordinateRestore (3, j) rest t) lam j = x}).Subsingleton := by
  have hn : 0 < n := by
    exact Nat.pos_of_ne_zero (by
      intro hn
      exact Fin.elim0 (hn ▸ j))
  intro t₁ ht₁ t₂ ht₂
  have hmark₁ : (FiniteSample.coordinateRestore (3, j) rest t₁).targetMark j =
      rest.targetMark j := by
    simpa [FiniteSample.coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq_of_ne (n := n) (3, j) (2, j)
        (by simp) rest t₁)
  have hmark₂ : (FiniteSample.coordinateRestore (3, j) rest t₂).targetMark j =
      rest.targetMark j := by
    simpa [FiniteSample.coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq_of_ne (n := n) (3, j) (2, j)
        (by simp) rest t₂)
  have hslope₁ :
      (FiniteSample.coordinateRestore (3, j) rest t₁).targetSlope j = rest.targetSlope j := by
    simp [FiniteSample.targetSlope, hmark₁]
  have hslope₂ :
      (FiniteSample.coordinateRestore (3, j) rest t₂).targetSlope j = rest.targetSlope j := by
    simp [FiniteSample.targetSlope, hmark₂]
  have hheight₁ :
      (FiniteSample.coordinateRestore (3, j) rest t₁).targetHeight j = t₁ := by
    simpa [FiniteSample.coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq (n := n) (3, j) rest t₁)
  have hheight₂ :
      (FiniteSample.coordinateRestore (3, j) rest t₂).targetHeight j = t₂ := by
    simpa [FiniteSample.coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq (n := n) (3, j) rest t₂)
  have hcross₁ :
      state.targetCoordinate (FiniteSample.coordinateRestore (3, j) rest t₁) lam j =
        targetNatHeightCrossing n state.x state.p (state.slope lam)
          (rest.targetSlope j) (t₁ : ℝ) := by
    simp [FeedbackStepState.targetCoordinate, targetNatHeightCrossing, hslope₁, hheight₁]
  have hcross₂ :
      state.targetCoordinate (FiniteSample.coordinateRestore (3, j) rest t₂) lam j =
        targetNatHeightCrossing n state.x state.p (state.slope lam)
          (rest.targetSlope j) (t₂ : ℝ) := by
    simp [FeedbackStepState.targetCoordinate, targetNatHeightCrossing, hslope₂, hheight₂]
  have hb := rest.targetSlope_mem j
  have hfiber := state.targetHeightCrossing_unit_fibre_subsingleton
    (lam := lam) hlam0 hlamHalf hb.1 hb.2 hn x
  have ht₁' :
      targetNatHeightCrossing n state.x state.p (state.slope lam)
          (rest.targetSlope j) (t₁ : ℝ) = x := by
    change state.targetCoordinate (FiniteSample.coordinateRestore (3, j) rest t₁) lam j = x
      at ht₁
    rw [hcross₁] at ht₁
    exact ht₁
  have ht₂' :
      targetNatHeightCrossing n state.x state.p (state.slope lam)
          (rest.targetSlope j) (t₂ : ℝ) = x := by
    change state.targetCoordinate (FiniteSample.coordinateRestore (3, j) rest t₂) lam j = x
      at ht₂
    rw [hcross₂] at ht₂
    exact ht₂
  exact hfiber ht₁' ht₂'

/-! ## Product-law nullity -/

set_option maxHeartbeats 800000 in
theorem measure_sourceAffineFrontierEvent_eq_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) (i : Fin n) (x : ℝ) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        (sourceAffineFrontierEvent lam state i x) = 0 := by
  let p : FiniteSample.CoordinateIndex n := (1, i)
  let s : Set (FiniteSample n × UnitMark) :=
    {pair | state.sourceCoordinate (FiniteSample.coordinateRestore p pair.1 pair.2) lam i = x}
  have hs : MeasurableSet s := by
    have hsample : Measurable (fun pair : FiniteSample n × UnitMark ↦
        FiniteSample.coordinateRestore p pair.1 pair.2) := by
      simpa [p] using (measurable_coordinateRestore (n := n) (1, i))
    have hpair : Measurable (fun pair : FiniteSample n × UnitMark ↦
        (FiniteSample.coordinateRestore p pair.1 pair.2, state)) :=
      hsample.prodMk measurable_const
    have hcoord : Measurable (fun pair : FiniteSample n × UnitMark ↦
        state.sourceCoordinate (FiniteSample.coordinateRestore p pair.1 pair.2) lam i) :=
      (measurable_sourceCoordinate lam i).comp hpair
    exact hcoord (measurableSet_singleton x)
  have hnull : (finiteSampleLaw n : Measure (FiniteSample n))
      ((fun sample ↦ (FiniteSample.coordinateLeaveOneOut p sample,
        FiniteSample.coordinate p sample)) ⁻¹' s) = 0 := by
    let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
      change NullSingletonClass (volume : Measure UnitMark)
      infer_instance
    apply measure_pair_mem_eq_zero_of_indepFun_of_finite_fibres
      (ν := (unitUniform : Measure UnitMark))
      (measurable_coordinateLeaveOneOut p) (measurable_coordinate p)
      (coordinateLeaveOneOut_indepFun_coordinate p)
    · exact congrArg ProbabilityMeasure.toMeasure (coordinate_marginal p)
    · exact hs
    · intro rest
      exact (sourceAffineFrontierRestore_fibre_subsingleton
        (x := x) hlam0 hlamHalf state i rest).finite
  have hset : sourceAffineFrontierEvent lam state i x =
      (fun sample ↦ (FiniteSample.coordinateLeaveOneOut p sample,
        FiniteSample.coordinate p sample)) ⁻¹' s := by
    ext sample
    change state.sourceCoordinate sample lam i = x ↔
      state.sourceCoordinate
        (FiniteSample.coordinateRestore p (FiniteSample.coordinateLeaveOneOut p sample)
          (FiniteSample.coordinate p sample)) lam i = x
    rw [FiniteSample.coordinateRestore_coordinateLeaveOneOut]
  rw [hset]
  exact hnull

set_option maxHeartbeats 800000 in
theorem measure_targetAffineFrontierEvent_eq_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) (j : Fin n) (x : ℝ) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        (targetAffineFrontierEvent lam state j x) = 0 := by
  let p : FiniteSample.CoordinateIndex n := (3, j)
  let s : Set (FiniteSample n × UnitMark) :=
    {pair | state.targetCoordinate (FiniteSample.coordinateRestore p pair.1 pair.2) lam j = x}
  have hs : MeasurableSet s := by
    have hsample : Measurable (fun pair : FiniteSample n × UnitMark ↦
        FiniteSample.coordinateRestore p pair.1 pair.2) := by
      simpa [p] using (measurable_coordinateRestore (n := n) (3, j))
    have hpair : Measurable (fun pair : FiniteSample n × UnitMark ↦
        (FiniteSample.coordinateRestore p pair.1 pair.2, state)) :=
      hsample.prodMk measurable_const
    have hcoord : Measurable (fun pair : FiniteSample n × UnitMark ↦
        state.targetCoordinate (FiniteSample.coordinateRestore p pair.1 pair.2) lam j) :=
      (measurable_targetCoordinate lam j).comp hpair
    exact hcoord (measurableSet_singleton x)
  have hnull : (finiteSampleLaw n : Measure (FiniteSample n))
      ((fun sample ↦ (FiniteSample.coordinateLeaveOneOut p sample,
        FiniteSample.coordinate p sample)) ⁻¹' s) = 0 := by
    let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
      change NullSingletonClass (volume : Measure UnitMark)
      infer_instance
    apply measure_pair_mem_eq_zero_of_indepFun_of_finite_fibres
      (ν := (unitUniform : Measure UnitMark))
      (measurable_coordinateLeaveOneOut p) (measurable_coordinate p)
      (coordinateLeaveOneOut_indepFun_coordinate p)
    · exact congrArg ProbabilityMeasure.toMeasure (coordinate_marginal p)
    · exact hs
    · intro rest
      exact (targetAffineFrontierRestore_fibre_subsingleton
        (x := x) hlam0 hlamHalf state j rest).finite
  have hset : targetAffineFrontierEvent lam state j x =
      (fun sample ↦ (FiniteSample.coordinateLeaveOneOut p sample,
        FiniteSample.coordinate p sample)) ⁻¹' s := by
    ext sample
    change state.targetCoordinate sample lam j = x ↔
      state.targetCoordinate
        (FiniteSample.coordinateRestore p (FiniteSample.coordinateLeaveOneOut p sample)
          (FiniteSample.coordinate p sample)) lam j = x
    rw [FiniteSample.coordinateRestore_coordinateLeaveOneOut]
  rw [hset]
  exact hnull

/-! ## Finite source/target union -/

/-- The event that some source or target label has affine crossing coordinate `x`. -/
def anyAffineFrontierEvent (lam : ℝ) (state : FeedbackStepState n)
    (x : ℝ) : Set (FiniteSample n) :=
  {sample | (∃ i : Fin n, state.sourceCoordinate sample lam i = x) ∨
    ∃ j : Fin n, state.targetCoordinate sample lam j = x}

theorem measurableSet_anyAffineFrontierEvent (lam : ℝ) (state : FeedbackStepState n)
    (x : ℝ) : MeasurableSet (anyAffineFrontierEvent lam state x) := by
  rw [show anyAffineFrontierEvent lam state x =
      (⋃ i : Fin n, sourceAffineFrontierEvent lam state i x) ∪
        ⋃ j : Fin n, targetAffineFrontierEvent lam state j x by
    ext sample
    simp [anyAffineFrontierEvent, sourceAffineFrontierEvent, targetAffineFrontierEvent]]
  exact (MeasurableSet.iUnion fun i ↦ measurableSet_sourceAffineFrontierEvent lam state i x).union
    (MeasurableSet.iUnion fun j ↦ measurableSet_targetAffineFrontierEvent lam state j x)

theorem measure_anyAffineFrontierEvent_eq_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) (x : ℝ) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        (anyAffineFrontierEvent lam state x) = 0 := by
  rw [show anyAffineFrontierEvent lam state x =
      (⋃ i : Fin n, sourceAffineFrontierEvent lam state i x) ∪
        ⋃ j : Fin n, targetAffineFrontierEvent lam state j x by
    ext sample
    simp [anyAffineFrontierEvent, sourceAffineFrontierEvent, targetAffineFrontierEvent]]
  rw [measure_union_null]
  · rw [measure_iUnion_null_iff]
    intro i
    exact measure_sourceAffineFrontierEvent_eq_zero hlam0 hlamHalf state i x
  · rw [measure_iUnion_null_iff]
    intro j
    exact measure_targetAffineFrontierEvent_eq_zero hlam0 hlamHalf state j x

end FiniteSample

end OTSelector
