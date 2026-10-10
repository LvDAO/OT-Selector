import OTSelector.Feedback.CrossingFibre
import OTSelector.Feedback.ForcedHistory
import OTSelector.Feedback.NoTieBranch
import OTSelector.Probability.IndependentFiberNull

/-!
# Nullity of a fixed forced-history crossing tie

For a fixed initial pattern and a fixed forced history, the scheduled state only uses the
coordinates of labels in that history.  If a label has not appeared, restoring its height changes
only its own crossing coordinate.  Strict monotonicity in that height and the atomless product law
therefore make equality with any distinct label a null event.

This is the probability half of the no-tie argument.  The deterministic reduction from an actual
first tie to one of these fixed branch events is kept in `NoTieBranch.lean`.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

private theorem forcedLabelStep_coordinateRestore_eq_of_ne
    (rest : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (selected next : FeedbackLabel n) (t : UnitMark) (hne : next ≠ selected) :
    state.forcedLabelStep
        (coordinateRestore (labelHeightCoordinate selected) rest t) lam next =
      state.forcedLabelStep rest lam next := by
  have hcoord := labelCoordinate_coordinateRestore_eq_of_ne
    rest lam state selected next t hne
  cases next <;>
    simp only [FeedbackStepState.forcedLabelStep, hcoord]

private theorem scheduledState_coordinateRestore_eq
    (rest : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (selected : FeedbackLabel n)
    (t : UnitMark) (hselected : selected ∉ history) :
    scheduledState (coordinateRestore (labelHeightCoordinate selected) rest t)
        lam x0 p0 sourcePattern targetPattern history =
      scheduledState rest lam x0 p0 sourcePattern targetPattern history := by
  have hfrom : ∀ (state : FeedbackStepState n) (xs : List (FeedbackLabel n)),
      selected ∉ xs →
        scheduledStateFrom
            (coordinateRestore (labelHeightCoordinate selected) rest t) lam state xs =
          scheduledStateFrom rest lam state xs := by
    intro state xs
    induction xs generalizing state with
    | nil => intro; rfl
    | cons next tail ih =>
        intro hnot
        have hnext : next ≠ selected := by
          intro h
          exact hnot (by simp [h])
        have htail : selected ∉ tail := by
          intro h
          exact hnot (by simp [h])
        simp only [scheduledStateFrom]
        rw [forcedLabelStep_coordinateRestore_eq_of_ne rest lam state selected next t hnext]
        exact ih (state := state.forcedLabelStep rest lam next) htail
  exact hfrom (forcedInitialState x0 p0 sourcePattern targetPattern) history hselected

/-- Reconstruct a sample from an arbitrary remaining sample and the selected height coordinate. -/
private def restoredForLabel (label : FeedbackLabel n)
    (pair : FiniteSample n × UnitMark) : FiniteSample n :=
  coordinateRestore (labelHeightCoordinate label) pair.1 pair.2

private theorem measurable_restoredForLabel (label : FeedbackLabel n) :
    Measurable (restoredForLabel label : FiniteSample n × UnitMark → FiniteSample n) :=
  measurable_coordinateRestore (labelHeightCoordinate label)

/-- Product-space equality event for two labels at one fixed scheduled state. -/
private def scheduledLabelTieSet (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (selected other : FeedbackLabel n) :
    Set (FiniteSample n × UnitMark) :=
  {pair |
    let sample := restoredForLabel selected pair
    let state := scheduledState sample lam x0 p0 sourcePattern targetPattern history
    state.labelCoordinate sample lam selected = state.labelCoordinate sample lam other}

set_option maxHeartbeats 800000 in
private theorem measurableSet_scheduledLabelTieSet
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (selected other : FeedbackLabel n) :
    MeasurableSet
      (scheduledLabelTieSet lam x0 p0 sourcePattern targetPattern history selected other) := by
  let sampleFun : FiniteSample n × UnitMark → FiniteSample n := restoredForLabel selected
  let stateFun : FiniteSample n × UnitMark → FeedbackStepState n := fun pair ↦
    scheduledState (sampleFun pair) lam x0 p0 sourcePattern targetPattern history
  have hsample : Measurable sampleFun := measurable_restoredForLabel selected
  have hstate : Measurable stateFun :=
    (measurable_scheduledState lam x0 p0 sourcePattern targetPattern history).comp hsample
  have hpair : Measurable fun pair : FiniteSample n × UnitMark ↦
      (sampleFun pair, stateFun pair) := hsample.prodMk hstate
  have heq := measurableSet_eq_fun
    ((FeedbackStepState.measurable_labelCoordinate lam selected).comp hpair)
    ((FeedbackStepState.measurable_labelCoordinate lam other).comp hpair)
  simpa only [scheduledLabelTieSet, sampleFun, stateFun, Function.comp_apply] using heq

private theorem sourceLabelCoordinate_restoredForLabel
    (rest : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (i : Fin n) (t : UnitMark) :
    state.labelCoordinate (restoredForLabel (Sum.inl i) (rest, t)) lam (Sum.inl i) =
      sourceNatHeightCrossing n state.x state.p (state.slope lam)
        (rest.sourceSlope i) (t : ℝ) := by
  have hmark := coordinateRestore_coordinate_eq_of_ne (n := n) (1, i) (0, i)
    (by simp) rest t
  have hmark' :
      (coordinateRestore (1, i) rest t).sourceMark i = rest.sourceMark i := by
    simpa [coordinate, FiniteSample.toFourArrays] using hmark
  have hslope :
      (coordinateRestore (1, i) rest t).sourceSlope i = rest.sourceSlope i := by
    simp [FiniteSample.sourceSlope, hmark']
  have hheight :
      (coordinateRestore (1, i) rest t).sourceHeight i = t := by
    simpa [coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq (n := n) (1, i) rest t)
  simp [restoredForLabel, FeedbackStepState.labelCoordinate,
    FeedbackStepState.sourceCoordinate, sourceNatHeightCrossing, hslope, hheight]

private theorem targetLabelCoordinate_restoredForLabel
    (rest : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (j : Fin n) (t : UnitMark) :
    state.labelCoordinate (restoredForLabel (Sum.inr j) (rest, t)) lam (Sum.inr j) =
      targetNatHeightCrossing n state.x state.p (state.slope lam)
        (rest.targetSlope j) (t : ℝ) := by
  have hmark := coordinateRestore_coordinate_eq_of_ne (n := n) (3, j) (2, j)
    (by simp) rest t
  have hmark' :
      (coordinateRestore (3, j) rest t).targetMark j = rest.targetMark j := by
    simpa [coordinate, FiniteSample.toFourArrays] using hmark
  have hslope :
      (coordinateRestore (3, j) rest t).targetSlope j = rest.targetSlope j := by
    simp [FiniteSample.targetSlope, hmark']
  have hheight :
      (coordinateRestore (3, j) rest t).targetHeight j = t := by
    simpa [coordinate, FiniteSample.toFourArrays] using
      (coordinateRestore_coordinate_eq (n := n) (3, j) rest t)
  simp [restoredForLabel, FeedbackStepState.labelCoordinate,
    FeedbackStepState.targetCoordinate, targetNatHeightCrossing, hslope, hheight]

private theorem scheduledLabelTieSet_fibre_subsingleton
    {lam x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (selected other : FeedbackLabel n)
    (hselected : selected ∉ history) (hne : other ≠ selected) (rest : FiniteSample n) :
    (Prod.mk rest ⁻¹'
      scheduledLabelTieSet lam x0 p0 sourcePattern targetPattern history selected other
    ).Subsingleton := by
  have hn : 0 < n := by
    cases selected with
    | inl i => exact Nat.pos_of_ne_zero (by intro h; exact Fin.elim0 (h ▸ i))
    | inr j => exact Nat.pos_of_ne_zero (by intro h; exact Fin.elim0 (h ▸ j))
  let state := scheduledState rest lam x0 p0 sourcePattern targetPattern history
  intro t₁ ht₁ t₂ ht₂
  have hstate₁ :
      scheduledState (restoredForLabel selected (rest, t₁))
          lam x0 p0 sourcePattern targetPattern history = state := by
    exact scheduledState_coordinateRestore_eq rest lam x0 p0 sourcePattern targetPattern
      history selected t₁ hselected
  have hstate₂ :
      scheduledState (restoredForLabel selected (rest, t₂))
          lam x0 p0 sourcePattern targetPattern history = state := by
    exact scheduledState_coordinateRestore_eq rest lam x0 p0 sourcePattern targetPattern
      history selected t₂ hselected
  have hother₁ :
      state.labelCoordinate (restoredForLabel selected (rest, t₁)) lam other =
        state.labelCoordinate rest lam other := by
    exact labelCoordinate_coordinateRestore_eq_of_ne rest lam state selected other t₁ hne
  have hother₂ :
      state.labelCoordinate (restoredForLabel selected (rest, t₂)) lam other =
        state.labelCoordinate rest lam other := by
    exact labelCoordinate_coordinateRestore_eq_of_ne rest lam state selected other t₂ hne
  change
    (scheduledState (restoredForLabel selected (rest, t₁))
        lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          (restoredForLabel selected (rest, t₁)) lam selected =
      (scheduledState (restoredForLabel selected (rest, t₁))
        lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          (restoredForLabel selected (rest, t₁)) lam other at ht₁
  change
    (scheduledState (restoredForLabel selected (rest, t₂))
        lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          (restoredForLabel selected (rest, t₂)) lam selected =
      (scheduledState (restoredForLabel selected (rest, t₂))
        lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          (restoredForLabel selected (rest, t₂)) lam other at ht₂
  rw [hstate₁, hother₁] at ht₁
  rw [hstate₂, hother₂] at ht₂
  cases selected with
  | inl i =>
      have ha := rest.sourceSlope_mem i
      apply Subtype.ext
      apply (state.sourceHeightCrossing_strictMono hlam0 hlamHalf ha.1 ha.2 hn).injective
      rw [← sourceLabelCoordinate_restoredForLabel rest lam state i t₁,
        ← sourceLabelCoordinate_restoredForLabel rest lam state i t₂]
      exact ht₁.trans ht₂.symm
  | inr j =>
      have hb := rest.targetSlope_mem j
      apply Subtype.ext
      apply (state.targetHeightCrossing_strictMono hlam0 hlamHalf hb.1 hb.2 hn).injective
      rw [← targetLabelCoordinate_restoredForLabel rest lam state j t₁,
        ← targetLabelCoordinate_restoredForLabel rest lam state j t₂]
      exact ht₁.trans ht₂.symm

/-- At a fixed forced history, equality of the crossing coordinates of an unused label and a
distinct label has probability zero under the canonical finite product law. -/
theorem measure_scheduledLabelTie_eq_zero
    {lam x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (selected other : FeedbackLabel n)
    (hselected : selected ∉ history) (hne : other ≠ selected) :
    (finiteSampleLaw n : Measure (FiniteSample n))
        {sample |
          let state := scheduledState sample lam x0 p0 sourcePattern targetPattern history
          state.labelCoordinate sample lam selected = state.labelCoordinate sample lam other} = 0 := by
  let p := labelHeightCoordinate selected
  let s := scheduledLabelTieSet lam x0 p0 sourcePattern targetPattern history selected other
  let _ : NullSingletonClass (unitUniform : Measure UnitMark) := by
    change NullSingletonClass (volume : Measure UnitMark)
    infer_instance
  have hnull : (finiteSampleLaw n : Measure (FiniteSample n))
      ((fun sample ↦ (coordinateLeaveOneOut p sample, coordinate p sample)) ⁻¹' s) = 0 := by
    apply measure_pair_mem_eq_zero_of_indepFun_of_finite_fibres
      (ν := (unitUniform : Measure UnitMark))
      (measurable_coordinateLeaveOneOut p) (measurable_coordinate p)
      (coordinateLeaveOneOut_indepFun_coordinate p)
    · exact congrArg ProbabilityMeasure.toMeasure (coordinate_marginal p)
    · exact measurableSet_scheduledLabelTieSet lam x0 p0 sourcePattern targetPattern
        history selected other
    · intro rest
      exact (scheduledLabelTieSet_fibre_subsingleton hlam0 hlamHalf sourcePattern
        targetPattern history selected other hselected hne rest).finite
  have hset :
      {sample : FiniteSample n |
          let state := scheduledState sample lam x0 p0 sourcePattern targetPattern history
          state.labelCoordinate sample lam selected = state.labelCoordinate sample lam other} =
        (fun sample ↦ (coordinateLeaveOneOut p sample, coordinate p sample)) ⁻¹' s := by
    ext sample
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, s, scheduledLabelTieSet,
      restoredForLabel, p]
    rw [coordinateRestore_coordinateLeaveOneOut]
  rw [hset]
  exact hnull

/-- Simultaneously, almost every sample avoids every fixed forced-history equality whose selected
label has not appeared in the history. -/
theorem ae_all_scheduledLabelCoordinates_ne
    {lam x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      ∀ sourcePattern targetPattern : Finset (Fin n),
        ∀ history : List (FeedbackLabel n), ∀ selected other : FeedbackLabel n,
          selected ∉ history → other ≠ selected →
            let state := scheduledState sample lam x0 p0 sourcePattern targetPattern history
            state.labelCoordinate sample lam selected ≠ state.labelCoordinate sample lam other := by
  apply ae_all_iff.2
  intro sourcePattern
  apply ae_all_iff.2
  intro targetPattern
  apply ae_all_iff.2
  intro history
  apply ae_all_iff.2
  intro selected
  apply ae_all_iff.2
  intro other
  by_cases hselected : selected ∈ history
  · filter_upwards [] with sample
    intro hnot
    exact False.elim (hnot hselected)
  · by_cases hne : other = selected
    · filter_upwards [] with sample
      intro _ hother
      exact False.elim (hother hne)
    · have hzero := measure_scheduledLabelTie_eq_zero
        (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf
        sourcePattern targetPattern history selected other
        hselected hne
      have hneae := measure_eq_zero_iff_ae_notMem.mp hzero
      exact hneae.mono fun sample hsample _ _ ↦ hsample

/-- Under `0 ≤ lam < 1/2`, the canonical finite product sample has no simultaneous feedback
crossings almost surely.  This closes the finite-dimensional no-tie step without using the later
adaptive deferred-decision theorem. -/
theorem finiteSampleLaw_noFeedbackTies_ae
    {lam x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      sample.NoFeedbackTies lam x0 p0 := by
  filter_upwards [ae_all_scheduledLabelCoordinates_ne
    (n := n) (x0 := x0) (p0 := p0) hlam0 hlamHalf] with sample hsample
  by_contra hbad
  obtain ⟨sourcePattern, targetPattern, history, selected, other, _, _, hselected,
    hne, _, hcoord⟩ := sample.exists_noTieBranch_of_not_NoFeedbackTies hbad
  exact (hsample sourcePattern targetPattern history selected other
    hselected hne.symm) hcoord

/-- The measurable feedback-tie event has zero probability under the finite product law. -/
theorem measure_feedbackTieEvent_eq_zero
    {lam x0 p0 : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | ¬sample.NoFeedbackTies lam x0 p0} = 0 := by
  exact measure_eq_zero_iff_ae_notMem.mpr
    ((finiteSampleLaw_noFeedbackTies_ae (n := n) (x0 := x0) (p0 := p0)
      hlam0 hlamHalf).mono fun sample hsample hmem ↦ hmem hsample)

end FiniteSample

end OTSelector
