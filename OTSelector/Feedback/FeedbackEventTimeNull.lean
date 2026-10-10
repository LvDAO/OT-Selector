import OTSelector.Feedback.FeedbackFrontierNull
import OTSelector.Feedback.FiniteHistoryBefore
import OTSelector.Feedback.FiniteHistoryPartition
import OTSelector.Feedback.NoTieNull

/-!
# Nullity of deterministic feedback event times

An actual finite feedback knot at a deterministic coordinate is reduced to a finite forced-history
prefix and the next label.  Once that prefix is fixed, its scheduled state uses only labels already
in the history.  Restoring the next label's height therefore leaves the state unchanged, while its
affine crossing coordinate has a singleton height fibre.  The canonical finite product law then
makes every fixed prefix/frontier event null.

Initial labels are not counted as jumps: the final theorem assumes `x₀ < x` and uses only knot
indices `1, ..., 2n`, exactly as `FiniteSample.NoFeedbackEventAt` does.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## A fixed forced-history frontier -/

/-- Equality of the next prescribed label's affine coordinate with a deterministic frontier. -/
def scheduledLabelFrontierEvent (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (label : FeedbackLabel n) (x : ℝ) :
    Set (FiniteSample n) :=
  {sample |
    let state := scheduledState sample lam x0 p0 sourcePattern targetPattern history
    state.labelCoordinate sample lam label = x}

theorem measurableSet_scheduledLabelFrontierEvent
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (label : FeedbackLabel n) (x : ℝ) :
    MeasurableSet
      (scheduledLabelFrontierEvent lam x0 p0 sourcePattern targetPattern history label x) := by
  let state : FiniteSample n → FeedbackStepState n := fun sample ↦
    scheduledState sample lam x0 p0 sourcePattern targetPattern history
  have hstate : Measurable state := by
    simpa [state] using measurable_scheduledState
      (n := n) lam x0 p0 sourcePattern targetPattern history
  have hpair : Measurable fun sample : FiniteSample n ↦ (sample, state sample) :=
    measurable_id.prodMk hstate
  have hcoord : Measurable fun sample : FiniteSample n ↦
      (state sample).labelCoordinate sample lam label :=
    (FeedbackStepState.measurable_labelCoordinate lam label).comp hpair
  change MeasurableSet {sample : FiniteSample n |
    (state sample).labelCoordinate sample lam label = x}
  exact hcoord (measurableSet_singleton x)

private theorem forcedLabelStep_coordinateRestore_eq_of_ne
    (rest : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (selected next : FeedbackLabel n) (t : UnitMark) (hne : next ≠ selected) :
    state.forcedLabelStep
        (coordinateRestore (labelHeightCoordinate selected) rest t) lam next =
      state.forcedLabelStep rest lam next := by
  have hcoord := labelCoordinate_coordinateRestore_eq_of_ne
    rest lam state selected next t hne
  cases next <;> simp only [FeedbackStepState.forcedLabelStep, hcoord]

/-- A forced scheduled state does not use the restored height of a label absent from its history. -/
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

private def scheduledLabelFrontierProductSet (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (label : FeedbackLabel n) (x : ℝ) :
    Set (FiniteSample n × UnitMark) :=
  {pair |
    let sample := coordinateRestore (labelHeightCoordinate label) pair.1 pair.2
    let state := scheduledState sample lam x0 p0 sourcePattern targetPattern history
    state.labelCoordinate sample lam label = x}

set_option maxHeartbeats 800000 in
private theorem measurableSet_scheduledLabelFrontierProductSet
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (label : FeedbackLabel n) (x : ℝ) :
    MeasurableSet
      (scheduledLabelFrontierProductSet lam x0 p0 sourcePattern targetPattern history label x) := by
  let sample : FiniteSample n × UnitMark → FiniteSample n := fun pair ↦
    coordinateRestore (labelHeightCoordinate label) pair.1 pair.2
  let state : FiniteSample n × UnitMark → FeedbackStepState n := fun pair ↦
    scheduledState (sample pair) lam x0 p0 sourcePattern targetPattern history
  have hsample : Measurable sample := by
    simpa [sample] using measurable_coordinateRestore (labelHeightCoordinate label)
  have hstate : Measurable state :=
    (measurable_scheduledState lam x0 p0 sourcePattern targetPattern history).comp hsample
  have hpair : Measurable fun pair : FiniteSample n × UnitMark ↦
      (sample pair, state pair) := hsample.prodMk hstate
  have hcoord : Measurable fun pair : FiniteSample n × UnitMark ↦
      (state pair).labelCoordinate (sample pair) lam label :=
    (FeedbackStepState.measurable_labelCoordinate lam label).comp hpair
  change MeasurableSet {pair : FiniteSample n × UnitMark |
    (state pair).labelCoordinate (sample pair) lam label = x}
  exact hcoord (measurableSet_singleton x)

private theorem scheduledLabelFrontierProductSet_fibre_subsingleton
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlabel : label ∉ history) (rest : FiniteSample n) :
    (Prod.mk rest ⁻¹'
      scheduledLabelFrontierProductSet lam x0 p0 sourcePattern targetPattern history label x
    ).Subsingleton := by
  let state := scheduledState rest lam x0 p0 sourcePattern targetPattern history
  intro t₁ ht₁ t₂ ht₂
  have hstate₁ :
      scheduledState (coordinateRestore (labelHeightCoordinate label) rest t₁)
          lam x0 p0 sourcePattern targetPattern history = state := by
    exact scheduledState_coordinateRestore_eq rest lam x0 p0 sourcePattern targetPattern
      history label t₁ hlabel
  have hstate₂ :
      scheduledState (coordinateRestore (labelHeightCoordinate label) rest t₂)
          lam x0 p0 sourcePattern targetPattern history = state := by
    exact scheduledState_coordinateRestore_eq rest lam x0 p0 sourcePattern targetPattern
      history label t₂ hlabel
  cases label with
  | inl i =>
      have hstate₁' :
          scheduledState (coordinateRestore (1, i) rest t₁)
              lam x0 p0 sourcePattern targetPattern history = state := by
        simpa only [labelHeightCoordinate_inl] using hstate₁
      have hstate₂' :
          scheduledState (coordinateRestore (1, i) rest t₂)
              lam x0 p0 sourcePattern targetPattern history = state := by
        simpa only [labelHeightCoordinate_inl] using hstate₂
      change
        (scheduledState (coordinateRestore (1, i) rest t₁) lam x0 p0 sourcePattern
          targetPattern history).sourceCoordinate (coordinateRestore (1, i) rest t₁) lam i = x
        at ht₁
      change
        (scheduledState (coordinateRestore (1, i) rest t₂) lam x0 p0 sourcePattern
          targetPattern history).sourceCoordinate (coordinateRestore (1, i) rest t₂) lam i = x
        at ht₂
      rw [hstate₁'] at ht₁
      rw [hstate₂'] at ht₂
      exact (sourceAffineFrontierRestore_fibre_subsingleton
        (x := x) hlam0 hlamHalf state i rest) ht₁ ht₂
  | inr j =>
      have hstate₁' :
          scheduledState (coordinateRestore (3, j) rest t₁)
              lam x0 p0 sourcePattern targetPattern history = state := by
        simpa only [labelHeightCoordinate_inr] using hstate₁
      have hstate₂' :
          scheduledState (coordinateRestore (3, j) rest t₂)
              lam x0 p0 sourcePattern targetPattern history = state := by
        simpa only [labelHeightCoordinate_inr] using hstate₂
      change
        (scheduledState (coordinateRestore (3, j) rest t₁) lam x0 p0 sourcePattern
          targetPattern history).targetCoordinate (coordinateRestore (3, j) rest t₁) lam j = x
        at ht₁
      change
        (scheduledState (coordinateRestore (3, j) rest t₂) lam x0 p0 sourcePattern
          targetPattern history).targetCoordinate (coordinateRestore (3, j) rest t₂) lam j = x
        at ht₂
      rw [hstate₁'] at ht₁
      rw [hstate₂'] at ht₂
      exact (targetAffineFrontierRestore_fibre_subsingleton
        (x := x) hlam0 hlamHalf state j rest) ht₁ ht₂

set_option maxHeartbeats 1000000 in
/-- A fixed forced-history prefix followed by a label absent from that prefix cannot hit a
deterministic affine frontier with positive probability. -/
theorem measure_scheduledLabelFrontierEvent_eq_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (label : FeedbackLabel n)
    (hlabel : label ∉ history) (x : ℝ) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      (scheduledLabelFrontierEvent lam x0 p0 sourcePattern targetPattern history label x) = 0 := by
  let p := labelHeightCoordinate label
  let s := scheduledLabelFrontierProductSet
    lam x0 p0 sourcePattern targetPattern history label x
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
    · exact measurableSet_scheduledLabelFrontierProductSet
        lam x0 p0 sourcePattern targetPattern history label x
    · intro rest
      exact (scheduledLabelFrontierProductSet_fibre_subsingleton
        (x := x) hlam0 hlamHalf sourcePattern targetPattern history label hlabel rest).finite
  have hset :
      scheduledLabelFrontierEvent lam x0 p0 sourcePattern targetPattern history label x =
        (fun sample ↦ (coordinateLeaveOneOut p sample, coordinate p sample)) ⁻¹' s := by
    ext sample
    change
      (scheduledState sample lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          sample lam label = x ↔
        (scheduledState
            (coordinateRestore p (coordinateLeaveOneOut p sample) (coordinate p sample))
            lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          (coordinateRestore p (coordinateLeaveOneOut p sample) (coordinate p sample))
          lam label = x
    rw [coordinateRestore_coordinateLeaveOneOut]
  rw [hset]
  exact hnull

/-! ## The finite union of all admissible forced prefixes -/

/-- All fixed forced-history frontier events whose next label is absent from the prefix. -/
noncomputable def forcedHistoryFrontierUnion (lam x0 p0 x : ℝ) : Set (FiniteSample n) := by
  classical
  exact ⋃ index : HistoryCellIndex n, ⋃ label : FeedbackLabel n,
      if label ∉ index.history then
        scheduledLabelFrontierEvent lam x0 p0 index.sourcePattern index.targetPattern
          index.history label x
      else ∅

theorem measure_forcedHistoryFrontierUnion_eq_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 x : ℝ) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      (forcedHistoryFrontierUnion lam x0 p0 x) = 0 := by
  classical
  unfold forcedHistoryFrontierUnion
  rw [measure_iUnion_null_iff]
  intro index
  rw [measure_iUnion_null_iff]
  intro label
  by_cases hlabel : label ∉ index.history
  · simp only [hlabel]
    exact measure_scheduledLabelFrontierEvent_eq_zero
      hlam0 hlamHalf x0 p0 index.sourcePattern index.targetPattern index.history label hlabel x
  · simp [hlabel]

/-! ## Reduction of an actual knot to a forced prefix -/

set_option linter.unusedVariables false in
theorem exists_scheduledLabelFrontier_of_not_noFeedbackEventAt_of_noFeedbackTies
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hEvent : ¬ sample.NoFeedbackEventAt lam x0 p0 x) :
    ∃ (sourcePattern targetPattern : Finset (Fin n))
      (history : List (FeedbackLabel n)) (label : FeedbackLabel n),
      history.length < 2 * n ∧ label ∉ history ∧
        sample ∈ scheduledLabelFrontierEvent
          lam x0 p0 sourcePattern targetPattern history label x := by
  classical
  rw [NoFeedbackEventAt] at hEvent
  push Not at hEvent
  obtain ⟨eventIndex, hindexPos, hindexBound, hindexKnot⟩ := hEvent
  have hex : ∃ m : ℕ, sample.feedbackKnot lam x0 p0 m = x :=
    ⟨eventIndex, hindexKnot⟩
  let m := Nat.find hex
  have hmKnot : sample.feedbackKnot lam x0 p0 m = x := Nat.find_spec hex
  have hmBound : m ≤ 2 * n :=
    (Nat.find_min' hex hindexKnot).trans hindexBound
  have hmNeZero : m ≠ 0 := by
    intro hm0
    have hx0eq : x0 = x := by
      simpa [m, hm0, feedbackKnot, feedbackState_zero, initialFeedbackState] using hmKnot
    exact ne_of_lt hx0x hx0eq
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmNeZero
  have hkFind : Nat.find hex = k + 1 := by
    simpa [m] using hk
  rw [hk] at hmKnot hmBound
  have hkBound : k < 2 * n := by omega
  have hkKnotNe : sample.feedbackKnot lam x0 p0 k ≠ x := by
    apply Nat.find_min hex
    rw [hkFind]
    exact Nat.lt_succ_self k
  have hkCandidates :
      ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty := by
    by_contra hnone
    have hempty : (feedbackState sample lam x0 p0 k).candidates sample lam = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hstate := sample.feedbackState_succ_eq_of_candidates_eq_empty
      lam x0 p0 k hempty
    have hknotEq : sample.feedbackKnot lam x0 p0 (k + 1) =
        sample.feedbackKnot lam x0 p0 k := by
      simpa only [feedbackKnot] using congrArg FeedbackStepState.x hstate
    exact hkKnotNe (hknotEq ▸ hmKnot)
  have hactive : ∀ r < k,
      ((feedbackState sample lam x0 p0 r).candidates sample lam).Nonempty := by
    intro r hr
    by_contra hnone
    have hempty : (feedbackState sample lam x0 p0 r).candidates sample lam = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hstate : feedbackState sample lam x0 p0 k =
        feedbackState sample lam x0 p0 r := by
      simpa [Nat.add_sub_of_le (Nat.le_of_lt hr)] using
        sample.feedbackState_eq_of_candidates_eq_empty lam x0 p0 r hempty (k - r)
    have hkempty : (feedbackState sample lam x0 p0 k).candidates sample lam = ∅ := by
      rw [hstate]
      exact hempty
    exact hkCandidates.ne_empty hkempty
  have hprior : ∀ r < k,
      ((feedbackState sample lam x0 p0 r).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 r).newTarget sample lam).card ≤ 1 := by
    intro r hr
    exact hNoTie r (hr.trans hkBound)
  let sourcePattern := sample.initialSeenSource x0 p0
  let targetPattern := sample.initialSeenTarget x0 p0
  have hinit : sample.initialFeedbackState x0 p0 =
      forcedInitialState x0 p0 sourcePattern targetPattern := by
    simp [sourcePattern, targetPattern, initialFeedbackState, initialFeedbackCurrent,
      forcedInitialState]
  obtain ⟨history, hlen, hreal, hstate⟩ :=
    sample.exists_forced_history_of_prior_active lam x0 p0 sourcePattern targetPattern
      hinit k hactive hprior
  have hcount :
      ((feedbackState sample lam x0 p0 k).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 k).newTarget sample lam).card = 1 :=
    sample.new_label_count_eq_one_of_noFeedbackTies hNoTie hkBound hkCandidates
  obtain ⟨label, hlabelStep⟩ := sample.exists_labelStepRealizes_of_card_sum_eq_one
    lam (feedbackState sample lam x0 p0 k) hcount
  have hlabelMem : label ∈
      newLabelSet sample lam (feedbackState sample lam x0 p0 k) := by
    cases label with
    | inl i =>
        rw [mem_newLabelSet_iff]
        rw [hlabelStep.1]
        simp
    | inr j =>
        rw [mem_newLabelSet_iff]
        rw [hlabelStep.2]
        simp
  have hlabelNot : label ∉ history :=
    sample.label_not_mem_history_of_mem_newLabelSet lam x0 p0 sourcePattern targetPattern
      history (feedbackState sample lam x0 p0 k) hstate hlabelMem
  have hcoordNext := sample.labelCoordinate_eq_next_of_mem_newLabelSet lam
    (feedbackState sample lam x0 p0 k) hlabelMem
  have hnextX :
      (feedbackState sample lam x0 p0 k).nextCoordinate sample lam = x := by
    simpa only [feedbackKnot, feedbackState_succ, FeedbackStepState.step] using hmKnot
  have hfrontier :
      (scheduledState sample lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          sample lam label = x := by
    rw [← hstate]
    exact hcoordNext.trans hnextX
  refine ⟨sourcePattern, targetPattern, history, label, ?_, hlabelNot, ?_⟩
  · simpa [hlen] using hkBound
  · exact hfrontier

theorem mem_forcedHistoryFrontierUnion_of_not_noFeedbackEventAt_of_noFeedbackTies
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hEvent : ¬ sample.NoFeedbackEventAt lam x0 p0 x) :
    sample ∈ forcedHistoryFrontierUnion lam x0 p0 x := by
  obtain ⟨sourcePattern, targetPattern, history, label, hlen, hlabel, hfrontier⟩ :=
    sample.exists_scheduledLabelFrontier_of_not_noFeedbackEventAt_of_noFeedbackTies
      hlam0 hlamHalf hx0x hNoTie hEvent
  let index : HistoryCellIndex n :=
    { sourcePattern := sourcePattern
      targetPattern := targetPattern
      history := history
      history_length_le := hlen.le }
  classical
  unfold forcedHistoryFrontierUnion
  refine Set.mem_iUnion.mpr ⟨index, ?_⟩
  refine Set.mem_iUnion.mpr ⟨label, ?_⟩
  simpa [index, hlabel] using hfrontier

/-! ## Actual deterministic event-time nullity -/

/-- With probability one, no non-initial finite feedback knot lies at a fixed deterministic
coordinate strictly to the right of `x₀`. -/
theorem measure_not_noFeedbackEventAt_eq_zero
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 < x) :
    (finiteSampleLaw n : Measure (FiniteSample n))
      {sample | ¬ sample.NoFeedbackEventAt lam x0 p0 x} = 0 := by
  have hsubset : {sample : FiniteSample n | ¬ sample.NoFeedbackEventAt lam x0 p0 x} ⊆
      {sample | ¬ sample.NoFeedbackTies lam x0 p0} ∪
        forcedHistoryFrontierUnion lam x0 p0 x := by
    intro sample hEvent
    by_cases hNoTie : sample.NoFeedbackTies lam x0 p0
    · exact Or.inr (sample.mem_forcedHistoryFrontierUnion_of_not_noFeedbackEventAt_of_noFeedbackTies
        hlam0 hlamHalf hx0x hNoTie hEvent)
    · exact Or.inl hNoTie
  apply measure_mono_null hsubset
  rw [measure_union_null]
  · exact measure_feedbackTieEvent_eq_zero (n := n) (x0 := x0) (p0 := p0)
      hlam0 hlamHalf
  · exact measure_forcedHistoryFrontierUnion_eq_zero hlam0 hlamHalf x0 p0 x

/-- Almost-sure endpoint convention: actual finite feedback events avoid every fixed
deterministic coordinate `x > x₀`. -/
theorem noFeedbackEventAt_ae
    {lam x0 p0 x : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hx0x : x0 < x) :
    ∀ᵐ sample ∂(finiteSampleLaw n : Measure (FiniteSample n)),
      sample.NoFeedbackEventAt lam x0 p0 x := by
  have hae := measure_eq_zero_iff_ae_notMem.mp
    (measure_not_noFeedbackEventAt_eq_zero (n := n) (p0 := p0) hlam0 hlamHalf hx0x)
  exact hae.mono fun sample hsample ↦ by
    simpa only [Set.mem_ofPred_eq, not_not] using hsample

end FiniteSample

end OTSelector
