import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import OTSelector.Basic.FiniteSampleLeaveOneOut
import OTSelector.Feedback.FeedbackRecursion
import OTSelector.Feedback.StateMeasurable

/-!
# Deterministic forced feedback histories

This file provides the finite, branchwise recursion used in the no-tie argument.  A forced
history records the labels that are processed, rather than recomputing the minimum over all
remaining candidates.  The construction is deterministic and contains no probabilistic claim.
-/

open MeasureTheory Set

namespace OTSelector

/-- A feedback label is either a source or a target index. -/
abbrev FeedbackLabel (n : ℕ) := Fin n ⊕ Fin n

namespace FeedbackStepState

variable {n : ℕ}

/-- The candidate coordinate attached to a source or target label. -/
noncomputable def labelCoordinate (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (label : FeedbackLabel n) : ℝ :=
  match label with
  | Sum.inl i => state.sourceCoordinate sample lam i
  | Sum.inr j => state.targetCoordinate sample lam j

@[simp] theorem labelCoordinate_inl (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (i : Fin n) :
    state.labelCoordinate sample lam (Sum.inl i) = state.sourceCoordinate sample lam i :=
  rfl

@[simp] theorem labelCoordinate_inr (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (j : Fin n) :
    state.labelCoordinate sample lam (Sum.inr j) = state.targetCoordinate sample lam j :=
  rfl

/-- Process exactly one prescribed label on the current affine segment. -/
noncomputable def forcedLabelStep (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (label : FeedbackLabel n) : FeedbackStepState n :=
  match label with
  | Sum.inl i =>
      { x := state.labelCoordinate sample lam label
        p := segmentCurve state.x state.p (state.slope lam)
          (state.labelCoordinate sample lam label)
        current := state.current + 1
        seenSource := insert i state.seenSource
        seenTarget := state.seenTarget }
  | Sum.inr j =>
      { x := state.labelCoordinate sample lam label
        p := segmentCurve state.x state.p (state.slope lam)
          (state.labelCoordinate sample lam label)
        current := state.current - 1
        seenSource := state.seenSource
        seenTarget := insert j state.seenTarget }

@[simp] theorem forcedLabelStep_inl (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (i : Fin n) :
    state.forcedLabelStep sample lam (Sum.inl i) =
      { x := state.sourceCoordinate sample lam i
        p := segmentCurve state.x state.p (state.slope lam)
          (state.sourceCoordinate sample lam i)
        current := state.current + 1
        seenSource := insert i state.seenSource
        seenTarget := state.seenTarget } :=
  rfl

@[simp] theorem forcedLabelStep_inr (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (j : Fin n) :
    state.forcedLabelStep sample lam (Sum.inr j) =
      { x := state.targetCoordinate sample lam j
        p := segmentCurve state.x state.p (state.slope lam)
          (state.targetCoordinate sample lam j)
        current := state.current - 1
        seenSource := state.seenSource
        seenTarget := insert j state.seenTarget } :=
  rfl

/-- Measurability of the selected coordinate for a fixed feedback label. -/
@[fun_prop]
theorem measurable_labelCoordinate (lam : ℝ) (label : FeedbackLabel n) :
    Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      labelCoordinate pair.1 lam pair.2 label := by
  cases label with
  | inl i =>
      exact FiniteSample.measurable_sourceCoordinate lam i
  | inr j =>
      exact FiniteSample.measurable_targetCoordinate lam j

@[fun_prop]
theorem measurable_forcedLabelStep (lam : ℝ) (label : FeedbackLabel n) :
    Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
      pair.2.forcedLabelStep pair.1 lam label := by
  cases label with
  | inl i =>
      have hcoord : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          pair.2.labelCoordinate pair.1 lam (Sum.inl i) :=
        measurable_labelCoordinate lam (Sum.inl i)
      have hx : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.x :=
        FeedbackStepState.measurable_x.comp measurable_snd
      have hp : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.p :=
        FeedbackStepState.measurable_p.comp measurable_snd
      have hslope : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          pair.2.slope lam :=
        (FeedbackStepState.measurable_slope lam).comp measurable_snd
      have hsegment : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          segmentCurve pair.2.x pair.2.p (pair.2.slope lam)
            (pair.2.labelCoordinate pair.1 lam (Sum.inl i)) := by
        simp only [segmentCurve]
        exact hp.add (hslope.mul (hcoord.sub hx))
      have hcurrent : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          pair.2.current + (1 : ℤ) :=
        (FeedbackStepState.measurable_current.comp measurable_snd).add measurable_const
      have hseenSource : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          insert i pair.2.seenSource := by
        apply FiniteSample.measurable_finset_of_mem
        intro k
        by_cases hki : k = i
        · simp [hki]
        · have hmem : MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
              k ∈ pair.2.seenSource} := FiniteSample.measurableSet_mem_seenSource k
          simpa [Finset.mem_insert, hki] using hmem
      have hseenTarget : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          pair.2.seenTarget := FeedbackStepState.measurable_seenTarget.comp measurable_snd
      have hpack : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          FeedbackStepState.pack (pair.2.forcedLabelStep pair.1 lam (Sum.inl i)) := by
        simp only [FeedbackStepState.forcedLabelStep, FeedbackStepState.pack,
          FeedbackStepState.labelCoordinate]
        exact hcoord.prodMk <| hsegment.prodMk <| hcurrent.prodMk <|
          hseenSource.prodMk hseenTarget
      have hcomp := FeedbackStepState.measurable_unpack.comp hpack
      simpa [Function.comp_def, FeedbackStepState.unpack_pack] using hcomp
  | inr j =>
      have hcoord : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          pair.2.labelCoordinate pair.1 lam (Sum.inr j) :=
        measurable_labelCoordinate lam (Sum.inr j)
      have hx : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.x :=
        FeedbackStepState.measurable_x.comp measurable_snd
      have hp : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦ pair.2.p :=
        FeedbackStepState.measurable_p.comp measurable_snd
      have hslope : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          pair.2.slope lam :=
        (FeedbackStepState.measurable_slope lam).comp measurable_snd
      have hsegment : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          segmentCurve pair.2.x pair.2.p (pair.2.slope lam)
            (pair.2.labelCoordinate pair.1 lam (Sum.inr j)) := by
        simp only [segmentCurve]
        exact hp.add (hslope.mul (hcoord.sub hx))
      have hcurrent : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          pair.2.current - (1 : ℤ) :=
        (FeedbackStepState.measurable_current.comp measurable_snd).sub measurable_const
      have hseenSource : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          pair.2.seenSource := FeedbackStepState.measurable_seenSource.comp measurable_snd
      have hseenTarget : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          insert j pair.2.seenTarget := by
        apply FiniteSample.measurable_finset_of_mem
        intro k
        by_cases hkj : k = j
        · simp [hkj]
        · have hmem : MeasurableSet {pair : FiniteSample n × FeedbackStepState n |
              k ∈ pair.2.seenTarget} := FiniteSample.measurableSet_mem_seenTarget k
          simpa [Finset.mem_insert, hkj] using hmem
      have hpack : Measurable fun pair : FiniteSample n × FeedbackStepState n ↦
          FeedbackStepState.pack (pair.2.forcedLabelStep pair.1 lam (Sum.inr j)) := by
        simp only [FeedbackStepState.forcedLabelStep, FeedbackStepState.pack,
          FeedbackStepState.labelCoordinate]
        exact hcoord.prodMk <| hsegment.prodMk <| hcurrent.prodMk <|
          hseenSource.prodMk hseenTarget
      have hcomp := FeedbackStepState.measurable_unpack.comp hpack
      simpa [Function.comp_def, FeedbackStepState.unpack_pack] using hcomp

end FeedbackStepState

namespace FiniteSample

variable {n : ℕ}

/-- The scalar coordinate occupied by the height of a prescribed feedback label. -/
def labelHeightCoordinate : FeedbackLabel n → CoordinateIndex n
  | Sum.inl i => (1, i)
  | Sum.inr j => (3, j)

@[simp] theorem labelHeightCoordinate_inl (i : Fin n) :
    labelHeightCoordinate (Sum.inl i : FeedbackLabel n) = (1, i) :=
  rfl

@[simp] theorem labelHeightCoordinate_inr (j : Fin n) :
    labelHeightCoordinate (Sum.inr j : FeedbackLabel n) = (3, j) :=
  rfl

/-- A deterministic initial state with prescribed seen-label patterns. -/
def forcedInitialState (x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n)) :
    FeedbackStepState n :=
  { x := x0
    p := p0
    current := (sourcePattern.card : ℤ) - targetPattern.card
    seenSource := sourcePattern
    seenTarget := targetPattern }

/-- Process a prescribed list from a given deterministic state. -/
noncomputable def scheduledStateFrom (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : List (FeedbackLabel n) → FeedbackStepState n
  | [] => state
  | label :: history =>
      scheduledStateFrom sample lam (state.forcedLabelStep sample lam label) history

/-- State obtained by processing a prescribed list of labels from a fixed pattern. -/
noncomputable def scheduledState (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) : FeedbackStepState n :=
  scheduledStateFrom sample lam (forcedInitialState x0 p0 sourcePattern targetPattern) history

/-- Source labels appearing in a prescribed history. -/
def sourceHistorySet : List (FeedbackLabel n) → Finset (Fin n)
  | [] => ∅
  | Sum.inl i :: history => insert i (sourceHistorySet history)
  | Sum.inr _ :: history => sourceHistorySet history

/-- Target labels appearing in a prescribed history. -/
def targetHistorySet : List (FeedbackLabel n) → Finset (Fin n)
  | [] => ∅
  | Sum.inl _ :: history => targetHistorySet history
  | Sum.inr j :: history => insert j (targetHistorySet history)

@[simp] theorem sourceHistorySet_nil :
    sourceHistorySet ([] : List (FeedbackLabel n)) = ∅ :=
  rfl

@[simp] theorem targetHistorySet_nil :
    targetHistorySet ([] : List (FeedbackLabel n)) = ∅ :=
  rfl

theorem mem_sourceHistorySet_of_mem (history : List (FeedbackLabel n)) (i : Fin n)
    (h : Sum.inl i ∈ history) : i ∈ sourceHistorySet history := by
  induction history with
  | nil => simp at h
  | cons label history ih =>
      cases label with
      | inl k =>
          simp only [List.mem_cons] at h
          simp only [sourceHistorySet, Finset.mem_insert]
          rcases h with h | h
          · have hik : i = k := Sum.inl.inj h
            subst k
            simp
          · exact Or.inr (ih h)
      | inr j =>
          simp only [List.mem_cons] at h
          exact ih (by simpa using h)

theorem mem_targetHistorySet_of_mem (history : List (FeedbackLabel n)) (j : Fin n)
    (h : Sum.inr j ∈ history) : j ∈ targetHistorySet history := by
  induction history with
  | nil => simp at h
  | cons label history ih =>
      cases label with
      | inl i =>
          simp only [List.mem_cons] at h
          exact ih (by simpa using h)
      | inr k =>
          simp only [List.mem_cons] at h
          simp only [targetHistorySet, Finset.mem_insert]
          rcases h with h | h
          · have hjk : j = k := Sum.inr.inj h
            subst k
            simp
          · exact Or.inr (ih h)

theorem scheduledStateFrom_seenSource (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (history : List (FeedbackLabel n)) :
    (scheduledStateFrom sample lam state history).seenSource =
      state.seenSource ∪ sourceHistorySet history := by
  induction history generalizing state with
  | nil => simp [scheduledStateFrom, sourceHistorySet]
  | cons label history ih =>
      cases label with
      | inl i =>
          simp only [scheduledStateFrom, sourceHistorySet,
            FeedbackStepState.forcedLabelStep]
          rw [ih]
          simp
      | inr j =>
          simp only [scheduledStateFrom, sourceHistorySet,
            FeedbackStepState.forcedLabelStep]
          rw [ih]

theorem scheduledStateFrom_seenTarget (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (history : List (FeedbackLabel n)) :
    (scheduledStateFrom sample lam state history).seenTarget =
      state.seenTarget ∪ targetHistorySet history := by
  induction history generalizing state with
  | nil => simp [scheduledStateFrom, targetHistorySet]
  | cons label history ih =>
      cases label with
      | inl i =>
          simp only [scheduledStateFrom, targetHistorySet,
            FeedbackStepState.forcedLabelStep]
          rw [ih]
      | inr j =>
          simp only [scheduledStateFrom, targetHistorySet,
            FeedbackStepState.forcedLabelStep]
          rw [ih]
          simp

theorem scheduledState_seenSource (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    (scheduledState sample lam x0 p0 sourcePattern targetPattern history).seenSource =
      sourcePattern ∪ sourceHistorySet history := by
  simpa [scheduledState, forcedInitialState] using
    scheduledStateFrom_seenSource sample lam
      (forcedInitialState x0 p0 sourcePattern targetPattern) history

theorem scheduledState_seenTarget (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    (scheduledState sample lam x0 p0 sourcePattern targetPattern history).seenTarget =
      targetPattern ∪ targetHistorySet history := by
  simpa [scheduledState, forcedInitialState] using
    scheduledStateFrom_seenTarget sample lam
      (forcedInitialState x0 p0 sourcePattern targetPattern) history

theorem scheduledState_mem_seenSource_of_mem_history
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (i : Fin n)
    (h : Sum.inl i ∈ history) :
    i ∈ (scheduledState sample lam x0 p0 sourcePattern targetPattern history).seenSource := by
  rw [scheduledState_seenSource]
  exact Finset.mem_union_right _ (mem_sourceHistorySet_of_mem history i h)

theorem scheduledState_mem_seenTarget_of_mem_history
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (j : Fin n)
    (h : Sum.inr j ∈ history) :
    j ∈ (scheduledState sample lam x0 p0 sourcePattern targetPattern history).seenTarget := by
  rw [scheduledState_seenTarget]
  exact Finset.mem_union_right _ (mem_targetHistorySet_of_mem history j h)

theorem measurable_scheduledStateFrom (lam : ℝ)
    (stateFun : FiniteSample n → FeedbackStepState n)
    (hstate : Measurable stateFun) (history : List (FeedbackLabel n)) :
    Measurable fun sample : FiniteSample n ↦
      scheduledStateFrom sample lam (stateFun sample) history := by
  induction history generalizing stateFun with
  | nil =>
      simpa [scheduledStateFrom] using hstate
  | cons label history ih =>
      let next : FiniteSample n → FeedbackStepState n :=
        fun sample ↦ (stateFun sample).forcedLabelStep sample lam label
      have hpair : Measurable fun sample : FiniteSample n ↦
          (sample, stateFun sample) := measurable_id.prodMk hstate
      have hnext : Measurable next := by
        exact (FeedbackStepState.measurable_forcedLabelStep lam label).comp hpair
      have htail := ih (stateFun := next) hnext
      simpa [scheduledStateFrom, next, Function.comp_def] using htail

@[fun_prop]
theorem measurable_scheduledState (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) :
    Measurable fun sample : FiniteSample n ↦
      scheduledState sample lam x0 p0 sourcePattern targetPattern history := by
  unfold scheduledState
  exact measurable_scheduledStateFrom lam
    (fun _ : FiniteSample n ↦ forcedInitialState x0 p0 sourcePattern targetPattern)
    measurable_const history

@[simp] theorem scheduledState_nil (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n)) :
    scheduledState sample lam x0 p0 sourcePattern targetPattern [] =
      forcedInitialState x0 p0 sourcePattern targetPattern :=
  rfl

@[simp] theorem scheduledState_cons (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n)) (label : FeedbackLabel n)
    (history : List (FeedbackLabel n)) :
    scheduledState sample lam x0 p0 sourcePattern targetPattern (label :: history) =
      scheduledStateFrom sample lam
        ((forcedInitialState x0 p0 sourcePattern targetPattern).forcedLabelStep
          sample lam label) history :=
  rfl

@[simp] theorem scheduledState_append_singleton (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n)) (history : List (FeedbackLabel n))
    (label : FeedbackLabel n) :
    scheduledState sample lam x0 p0 sourcePattern targetPattern (history ++ [label]) =
      (scheduledState sample lam x0 p0 sourcePattern targetPattern history).forcedLabelStep
        sample lam label :=
  by
    have hfrom : ∀ (state : FeedbackStepState n) (history : List (FeedbackLabel n)),
        scheduledStateFrom sample lam state (history ++ [label]) =
          (scheduledStateFrom sample lam state history).forcedLabelStep sample lam label := by
      intro state history
      induction history generalizing state with
      | nil => rfl
      | cons head tail ih =>
          exact ih (state := state.forcedLabelStep sample lam head)
    exact hfrom (forcedInitialState x0 p0 sourcePattern targetPattern) history

/-! ## Realization of a prescribed branch -/

/-- The ordinary step processes exactly the prescribed label in one of the two singleton cases. -/
def labelStepRealizes (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) (label : FeedbackLabel n) : Prop :=
  match label with
  | Sum.inl i =>
      state.newSource sample lam = {i} ∧ state.newTarget sample lam = ∅
  | Sum.inr j =>
      state.newSource sample lam = ∅ ∧ state.newTarget sample lam = {j}

/-- A list of labels is a valid forced branch when each next label is selected by the ordinary
step from the state reached by the preceding labels. -/
def ForcedHistoryRealizes (sample : FiniteSample n) (lam : ℝ)
    (state : FeedbackStepState n) : List (FeedbackLabel n) → Prop
  | [] => True
  | label :: history =>
      labelStepRealizes sample lam state label ∧
        ForcedHistoryRealizes sample lam
          (state.forcedLabelStep sample lam label) history

/-- The two singleton cases in which the ordinary minimum step is exactly a forced step. -/
theorem step_eq_forcedLabelStep_of_source_singleton
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n)
    (hsource : state.newSource sample lam = {i})
    (htarget : state.newTarget sample lam = ∅) :
    state.step sample lam = state.forcedLabelStep sample lam (Sum.inl i) := by
  classical
  have hi : i ∈ state.newSource sample lam := by simp [hsource]
  have hcoord : state.sourceCoordinate sample lam i = state.nextCoordinate sample lam := by
    exact (Finset.mem_filter.mp (show i ∈
      (Finset.univ \ state.seenSource).filter
        (fun k ↦ state.sourceCoordinate sample lam k = state.nextCoordinate sample lam) by
          simpa only [FeedbackStepState.newSource, hsource] using hi)).2
  cases state with
  | mk x p current seenSource seenTarget =>
    simp [FeedbackStepState.step, FeedbackStepState.forcedLabelStep,
    FeedbackStepState.labelCoordinate, hsource, htarget, hcoord]

theorem step_eq_forcedLabelStep_of_target_singleton
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n)
    (hsource : state.newSource sample lam = ∅)
    (htarget : state.newTarget sample lam = {j}) :
    state.step sample lam = state.forcedLabelStep sample lam (Sum.inr j) := by
  classical
  have hj : j ∈ state.newTarget sample lam := by simp [htarget]
  have hcoord : state.targetCoordinate sample lam j = state.nextCoordinate sample lam := by
    exact (Finset.mem_filter.mp (show j ∈
      (Finset.univ \ state.seenTarget).filter
        (fun k ↦ state.targetCoordinate sample lam k = state.nextCoordinate sample lam) by
          simpa only [FeedbackStepState.newTarget, htarget] using hj)).2
  cases state with
  | mk x p current seenSource seenTarget =>
    simp [FeedbackStepState.step, FeedbackStepState.forcedLabelStep,
    FeedbackStepState.labelCoordinate, hsource, htarget, hcoord]

private theorem feedbackState_eq_scheduledStateFrom_of_history
    (sample : FiniteSample n) (lam x0 p0 : ℝ) (m : ℕ)
    (state : FeedbackStepState n)
    (hstate : feedbackState sample lam x0 p0 m = state)
    (history : List (FeedbackLabel n))
    (hgood : ForcedHistoryRealizes sample lam state history) :
    feedbackState sample lam x0 p0 (m + history.length) =
      scheduledStateFrom sample lam state history := by
  induction history generalizing m state with
  | nil =>
      simpa [scheduledStateFrom] using hstate
  | cons label history ih =>
      have hreal : labelStepRealizes sample lam state label := hgood.1
      have htail : ForcedHistoryRealizes sample lam
          (state.forcedLabelStep sample lam label) history := hgood.2
      have hstep : state.step sample lam =
          state.forcedLabelStep sample lam label := by
        cases label with
        | inl i =>
            exact step_eq_forcedLabelStep_of_source_singleton sample lam state i
              hreal.1 hreal.2
        | inr j =>
            exact step_eq_forcedLabelStep_of_target_singleton sample lam state j
              hreal.1 hreal.2
      have hstate' : feedbackState sample lam x0 p0 (m + 1) =
          state.forcedLabelStep sample lam label := by
        rw [feedbackState_succ]
        rw [hstate, hstep]
      have hrec := ih (m := m + 1)
        (state := state.forcedLabelStep sample lam label) hstate' htail
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        scheduledStateFrom] using hrec

theorem feedbackState_eq_scheduledState_of_history
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hinit : sample.initialFeedbackState x0 p0 =
      forcedInitialState x0 p0 sourcePattern targetPattern)
    (hgood : ForcedHistoryRealizes sample lam
      (forcedInitialState x0 p0 sourcePattern targetPattern) history) :
    feedbackState sample lam x0 p0 history.length =
      scheduledState sample lam x0 p0 sourcePattern targetPattern history := by
  have hrec := feedbackState_eq_scheduledStateFrom_of_history sample lam x0 p0 0
    (forcedInitialState x0 p0 sourcePattern targetPattern)
    (by simp [hinit]) history hgood
  simpa [scheduledState, scheduledStateFrom] using hrec

/-! ## Leave-one-out invariance -/

theorem sourceHeightLeaveOneOut_sourceHeight_eq_of_ne (sample : FiniteSample n)
    (i k : Fin n) (hki : k ≠ i) :
    (sourceHeightLeaveOneOut i sample).sourceHeight k = sample.sourceHeight k := by
  simpa [sourceHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using
    (coordinateLeaveOneOut_coordinate_eq_of_ne (n := n) (1, i) (1, k)
      (by simpa using hki) sample)

theorem targetHeightLeaveOneOut_targetHeight_eq_of_ne (sample : FiniteSample n)
    (i k : Fin n) (hki : k ≠ i) :
    (targetHeightLeaveOneOut i sample).targetHeight k = sample.targetHeight k := by
  simpa [targetHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using
    (coordinateLeaveOneOut_coordinate_eq_of_ne (n := n) (3, i) (3, k)
      (by simpa using hki) sample)

theorem sourceHeightLeaveOneOut_sourceCoordinate_eq_of_ne (sample : FiniteSample n)
    (lam : ℝ) (state : FeedbackStepState n) (i k : Fin n) (hki : k ≠ i) :
    state.sourceCoordinate (sourceHeightLeaveOneOut i sample) lam k =
      state.sourceCoordinate sample lam k := by
  have hh := sourceHeightLeaveOneOut_sourceHeight_eq_of_ne sample i k hki
  have hm := coordinateLeaveOneOut_coordinate_eq_of_ne (n := n) (1, i) (0, k)
    (by simp) sample
  have hm' : (sourceHeightLeaveOneOut i sample).sourceMark k = sample.sourceMark k := by
    simpa [sourceHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using hm
  have hs : (sourceHeightLeaveOneOut i sample).sourceSlope k = sample.sourceSlope k := by
    simp [FiniteSample.sourceSlope, hm']
  simp only [FeedbackStepState.sourceCoordinate, FeedbackStepState.slope,
    sourceHeightLeaveOneOut_sourceHeight_eq_of_ne sample i k hki, hs]

theorem targetHeightLeaveOneOut_targetCoordinate_eq_of_ne (sample : FiniteSample n)
    (lam : ℝ) (state : FeedbackStepState n) (i j : Fin n) (hji : j ≠ i) :
    state.targetCoordinate (targetHeightLeaveOneOut i sample) lam j =
      state.targetCoordinate sample lam j := by
  have hh := targetHeightLeaveOneOut_targetHeight_eq_of_ne sample i j hji
  have hm := coordinateLeaveOneOut_coordinate_eq_of_ne (n := n) (3, i) (2, j)
    (by simp) sample
  have hm' : (targetHeightLeaveOneOut i sample).targetMark j = sample.targetMark j := by
    simpa [targetHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using hm
  have hs : (targetHeightLeaveOneOut i sample).targetSlope j = sample.targetSlope j := by
    simp [FiniteSample.targetSlope, hm']
  simp only [FeedbackStepState.targetCoordinate, FeedbackStepState.slope, hh, hs]

theorem sourceHeightLeaveOneOut_targetCoordinate_eq (sample : FiniteSample n)
    (lam : ℝ) (state : FeedbackStepState n) (i j : Fin n) :
    state.targetCoordinate (sourceHeightLeaveOneOut i sample) lam j =
      state.targetCoordinate sample lam j := by
  have hh := coordinateLeaveOneOut_coordinate_eq_of_ne (n := n) (1, i) (3, j)
    (by simp) sample
  have hm := coordinateLeaveOneOut_coordinate_eq_of_ne (n := n) (1, i) (2, j)
    (by simp) sample
  have hh' : (sourceHeightLeaveOneOut i sample).targetHeight j = sample.targetHeight j := by
    simpa [sourceHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using hh
  have hm' : (sourceHeightLeaveOneOut i sample).targetMark j = sample.targetMark j := by
    simpa [sourceHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using hm
  have hs : (sourceHeightLeaveOneOut i sample).targetSlope j = sample.targetSlope j := by
    simp [FiniteSample.targetSlope, hm']
  simp only [FeedbackStepState.targetCoordinate, FeedbackStepState.slope, hh', hs]

theorem targetHeightLeaveOneOut_sourceCoordinate_eq (sample : FiniteSample n)
    (lam : ℝ) (state : FeedbackStepState n) (i k : Fin n) :
    state.sourceCoordinate (targetHeightLeaveOneOut i sample) lam k =
      state.sourceCoordinate sample lam k := by
  have hh := coordinateLeaveOneOut_coordinate_eq_of_ne (n := n) (3, i) (1, k)
    (by simp) sample
  have hm := coordinateLeaveOneOut_coordinate_eq_of_ne (n := n) (3, i) (0, k)
    (by simp) sample
  have hh' : (targetHeightLeaveOneOut i sample).sourceHeight k = sample.sourceHeight k := by
    simpa [targetHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using hh
  have hm' : (targetHeightLeaveOneOut i sample).sourceMark k = sample.sourceMark k := by
    simpa [targetHeightLeaveOneOut, coordinate, Function.comp_def, FiniteSample.toFourArrays] using hm
  have hs : (targetHeightLeaveOneOut i sample).sourceSlope k = sample.sourceSlope k := by
    simp [FiniteSample.sourceSlope, hm']
  simp only [FeedbackStepState.sourceCoordinate, FeedbackStepState.slope, hh', hs]

theorem labelCoordinate_coordinateRestore_eq_of_ne (rest : FiniteSample n)
    (lam : ℝ) (state : FeedbackStepState n) (label other : FeedbackLabel n)
    (t : UnitMark) (hother : other ≠ label) :
    state.labelCoordinate (coordinateRestore (labelHeightCoordinate label) rest t) lam other =
      state.labelCoordinate rest lam other := by
  cases label with
  | inl i =>
      cases other with
      | inl k =>
          have hki : k ≠ i := by
            intro h
            apply hother
            simp [h]
          have hh := coordinateRestore_coordinate_eq_of_ne (n := n) (1, i) (1, k)
            (by simpa using hki) rest t
          have hm := coordinateRestore_coordinate_eq_of_ne (n := n) (1, i) (0, k)
            (by simp) rest t
          have hh' :
              (coordinateRestore (1, i) rest t).sourceHeight k = rest.sourceHeight k := by
            simpa [coordinate, coordinateRestore, FiniteSample.toFourArrays] using hh
          have hm' :
              (coordinateRestore (1, i) rest t).sourceMark k = rest.sourceMark k := by
            simpa [coordinate, coordinateRestore, FiniteSample.toFourArrays] using hm
          have hs :
              (coordinateRestore (1, i) rest t).sourceSlope k = rest.sourceSlope k := by
            simp [FiniteSample.sourceSlope, hm']
          simp only [labelHeightCoordinate, FeedbackStepState.labelCoordinate,
            FeedbackStepState.sourceCoordinate, FeedbackStepState.slope, hh', hs]
      | inr j =>
          have hh := coordinateRestore_coordinate_eq_of_ne (n := n) (1, i) (3, j)
            (by simp) rest t
          have hm := coordinateRestore_coordinate_eq_of_ne (n := n) (1, i) (2, j)
            (by simp) rest t
          have hh' :
              (coordinateRestore (1, i) rest t).targetHeight j = rest.targetHeight j := by
            simpa [coordinate, coordinateRestore, FiniteSample.toFourArrays] using hh
          have hm' :
              (coordinateRestore (1, i) rest t).targetMark j = rest.targetMark j := by
            simpa [coordinate, coordinateRestore, FiniteSample.toFourArrays] using hm
          have hs :
              (coordinateRestore (1, i) rest t).targetSlope j = rest.targetSlope j := by
            simp [FiniteSample.targetSlope, hm']
          simp only [labelHeightCoordinate, FeedbackStepState.labelCoordinate,
            FeedbackStepState.targetCoordinate, FeedbackStepState.slope, hh', hs]
  | inr j =>
      cases other with
      | inl k =>
          have hh := coordinateRestore_coordinate_eq_of_ne (n := n) (3, j) (1, k)
            (by simp) rest t
          have hm := coordinateRestore_coordinate_eq_of_ne (n := n) (3, j) (0, k)
            (by simp) rest t
          have hh' :
              (coordinateRestore (3, j) rest t).sourceHeight k = rest.sourceHeight k := by
            simpa [coordinate, coordinateRestore, FiniteSample.toFourArrays] using hh
          have hm' :
              (coordinateRestore (3, j) rest t).sourceMark k = rest.sourceMark k := by
            simpa [coordinate, coordinateRestore, FiniteSample.toFourArrays] using hm
          have hs :
              (coordinateRestore (3, j) rest t).sourceSlope k = rest.sourceSlope k := by
            simp [FiniteSample.sourceSlope, hm']
          simp only [labelHeightCoordinate, FeedbackStepState.labelCoordinate,
            FeedbackStepState.sourceCoordinate, FeedbackStepState.slope, hh', hs]
      | inr k =>
          have hkj : k ≠ j := by
            intro h
            apply hother
            simp [h]
          have hh := coordinateRestore_coordinate_eq_of_ne (n := n) (3, j) (3, k)
            (by simpa using hkj) rest t
          have hm := coordinateRestore_coordinate_eq_of_ne (n := n) (3, j) (2, k)
            (by simp) rest t
          have hh' :
              (coordinateRestore (3, j) rest t).targetHeight k = rest.targetHeight k := by
            simpa [coordinate, coordinateRestore, FiniteSample.toFourArrays] using hh
          have hm' :
              (coordinateRestore (3, j) rest t).targetMark k = rest.targetMark k := by
            simpa [coordinate, coordinateRestore, FiniteSample.toFourArrays] using hm
          have hs :
              (coordinateRestore (3, j) rest t).targetSlope k = rest.targetSlope k := by
            simp [FiniteSample.targetSlope, hm']
          simp only [labelHeightCoordinate, FeedbackStepState.labelCoordinate,
            FeedbackStepState.targetCoordinate, FeedbackStepState.slope, hh', hs]

theorem forcedLabelStep_sourceHeightLeaveOneOut_eq_of_ne (sample : FiniteSample n)
    (lam : ℝ) (state : FeedbackStepState n) (i : Fin n) (label : FeedbackLabel n)
    (hlabel : label ≠ Sum.inl i) :
    state.forcedLabelStep (sourceHeightLeaveOneOut i sample) lam label =
      state.forcedLabelStep sample lam label := by
  cases label with
  | inl k =>
      have hki : k ≠ i := by
        intro h
        apply hlabel
        simp [h]
      simp [FeedbackStepState.forcedLabelStep, FeedbackStepState.labelCoordinate,
        sourceHeightLeaveOneOut_sourceCoordinate_eq_of_ne sample lam state i k hki]
  | inr j =>
      simp [FeedbackStepState.forcedLabelStep, FeedbackStepState.labelCoordinate,
        sourceHeightLeaveOneOut_targetCoordinate_eq sample lam state i j]

theorem forcedLabelStep_targetHeightLeaveOneOut_eq_of_ne (sample : FiniteSample n)
    (lam : ℝ) (state : FeedbackStepState n) (i : Fin n) (label : FeedbackLabel n)
    (hlabel : label ≠ Sum.inr i) :
    state.forcedLabelStep (targetHeightLeaveOneOut i sample) lam label =
      state.forcedLabelStep sample lam label := by
  cases label with
  | inl k =>
      simp [FeedbackStepState.forcedLabelStep, FeedbackStepState.labelCoordinate,
        targetHeightLeaveOneOut_sourceCoordinate_eq sample lam state i k]
  | inr j =>
      have hji : j ≠ i := by
        intro h
        apply hlabel
        simp [h]
      simp [FeedbackStepState.forcedLabelStep, FeedbackStepState.labelCoordinate,
        targetHeightLeaveOneOut_targetCoordinate_eq_of_ne sample lam state i j hji]

theorem scheduledState_sourceHeightLeaveOneOut_eq (sample : FiniteSample n)
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (i : Fin n)
    (hlabel : Sum.inl i ∉ history) :
    scheduledState (sourceHeightLeaveOneOut i sample) lam x0 p0
        sourcePattern targetPattern history =
      scheduledState sample lam x0 p0 sourcePattern targetPattern history := by
  have hfrom : ∀ (state : FeedbackStepState n) (xs : List (FeedbackLabel n)),
      Sum.inl i ∉ xs →
        scheduledStateFrom (sourceHeightLeaveOneOut i sample) lam state xs =
          scheduledStateFrom sample lam state xs := by
    intro state xs
    induction xs generalizing state with
    | nil => intro; rfl
    | cons label tail ih =>
        intro hnot
        have hhead : label ≠ Sum.inl i := by
          intro heq
          apply hnot
          simp [heq]
        have htail : Sum.inl i ∉ tail := by
          intro hmem
          apply hnot
          simp [hmem]
        simp only [scheduledStateFrom]
        rw [forcedLabelStep_sourceHeightLeaveOneOut_eq_of_ne sample lam state i label hhead]
        exact ih (state := state.forcedLabelStep sample lam label) htail
  exact hfrom (forcedInitialState x0 p0 sourcePattern targetPattern) history hlabel

theorem scheduledState_targetHeightLeaveOneOut_eq (sample : FiniteSample n)
    (lam x0 p0 : ℝ) (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (i : Fin n)
    (hlabel : Sum.inr i ∉ history) :
    scheduledState (targetHeightLeaveOneOut i sample) lam x0 p0
        sourcePattern targetPattern history =
      scheduledState sample lam x0 p0 sourcePattern targetPattern history := by
  have hfrom : ∀ (state : FeedbackStepState n) (xs : List (FeedbackLabel n)),
      Sum.inr i ∉ xs →
        scheduledStateFrom (targetHeightLeaveOneOut i sample) lam state xs =
          scheduledStateFrom sample lam state xs := by
    intro state xs
    induction xs generalizing state with
    | nil => intro; rfl
    | cons label tail ih =>
        intro hnot
        have hhead : label ≠ Sum.inr i := by
          intro heq
          apply hnot
          simp [heq]
        have htail : Sum.inr i ∉ tail := by
          intro hmem
          apply hnot
          simp [hmem]
        simp only [scheduledStateFrom]
        rw [forcedLabelStep_targetHeightLeaveOneOut_eq_of_ne sample lam state i label hhead]
        exact ih (state := state.forcedLabelStep sample lam label) htail
  exact hfrom (forcedInitialState x0 p0 sourcePattern targetPattern) history hlabel

end FiniteSample

end OTSelector
