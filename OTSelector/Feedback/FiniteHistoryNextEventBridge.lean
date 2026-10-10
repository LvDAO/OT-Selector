import OTSelector.Feedback.FiniteHistoryNextEvent
import OTSelector.Feedback.FiniteHistoryProductSection
import OTSelector.Feedback.NoTieBranch

/-!
# Canonical merge and strict next-label selection

This file is the deterministic bridge between the fixed-state next-event set and the ordinary
feedback step.  It contains no probability or compensator statement.  On a canonical
seen/unseen merge, the fixed-state crossing of an unseen point is exactly the corresponding
terminal label coordinate; consequently the strict-minimum condition is equivalent to a
singleton `newLabelSet`.
-/

open Set

namespace OTSelector

variable {n : ℕ}

/-! ## Pointwise crossing coordinates of the canonical merge -/

private theorem feedbackUnseenMerge_sourcePoint_eq'
    (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (i : Fin n) (hi : (Sum.inl i : FeedbackLabel n) ∉ S) :
    (finiteSampleSeenUnseenMerge S seen unseen).sourcePoint i =
      unseen ⟨Sum.inl i, by simp [feedbackUnseenFinset, hi]⟩ := by
  have htuple := congrFun
    (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen)
    (⟨Sum.inl i, by simp [feedbackUnseenFinset, hi]⟩ : feedbackUnseenFinset S)
  simpa [feedbackUnseenTuple, feedbackLabelTuple] using htuple

private theorem feedbackUnseenMerge_targetPoint_eq'
    (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (j : Fin n) (hj : (Sum.inr j : FeedbackLabel n) ∉ S) :
    (finiteSampleSeenUnseenMerge S seen unseen).targetPoint j =
      unseen ⟨Sum.inr j, by simp [feedbackUnseenFinset, hj]⟩ := by
  have htuple := congrFun
    (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen)
    (⟨Sum.inr j, by simp [feedbackUnseenFinset, hj]⟩ : feedbackUnseenFinset S)
  simpa [feedbackUnseenTuple, feedbackLabelTuple] using htuple

private theorem feedbackLabelFixedStateCrossing_finiteSampleSeenUnseenMerge_eq
    (state : FeedbackStepState n) (_sample : FiniteSample n)
    (lam : ℝ) (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (label : feedbackUnseenFinset S) :
    feedbackLabelFixedStateCrossing n lam state label (unseen label) =
      state.labelCoordinate (finiteSampleSeenUnseenMerge S seen unseen) lam
        (label : FeedbackLabel n) := by
  rcases label with ⟨label, hlabel⟩
  cases label with
  | inl i =>
      have hpoint :
          (finiteSampleSeenUnseenMerge S seen unseen).sourcePoint i =
            unseen ⟨Sum.inl i, hlabel⟩ := by
        have htuple := congrFun
          (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen)
          (⟨Sum.inl i, hlabel⟩ : feedbackUnseenFinset S)
        simpa [feedbackUnseenTuple, feedbackLabelTuple] using htuple
      rw [← hpoint]
      rfl
  | inr j =>
      have hpoint :
          (finiteSampleSeenUnseenMerge S seen unseen).targetPoint j =
            unseen ⟨Sum.inr j, hlabel⟩ := by
        have htuple := congrFun
          (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen)
          (⟨Sum.inr j, hlabel⟩ : feedbackUnseenFinset S)
        simpa [feedbackUnseenTuple, feedbackLabelTuple] using htuple
      rw [← hpoint]
      rfl

/-! ## Strict minima and singleton new-label sets -/

private theorem newLabelSet_eq_singleton_iff_strict_min
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (label : feedbackUnseenFinset S) :
    FiniteSample.newLabelSet sample lam state = {(label : FeedbackLabel n)} ↔
      ∀ other : feedbackUnseenFinset S, other ≠ label →
        state.labelCoordinate sample lam (label : FeedbackLabel n) <
          state.labelCoordinate sample lam (other : FeedbackLabel n) := by
  classical
  constructor
  · intro hsingleton
    have hselected : (label : FeedbackLabel n) ∈
        FiniteSample.newLabelSet sample lam state := by
      rw [hsingleton]
      simp
    have hselectedNext := FiniteSample.labelCoordinate_eq_next_of_mem_newLabelSet
      sample lam state hselected
    have hnext_le_source (i : Fin n) (hi : i ∉ state.seenSource) :
        state.nextCoordinate sample lam ≤ state.sourceCoordinate sample lam i := by
      have hiDiff : i ∈ Finset.univ \ state.seenSource := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      have hiCandidate : state.sourceCoordinate sample lam i ∈
          state.sourceCandidates sample lam := by
        exact Finset.mem_image.mpr ⟨i, hiDiff, rfl⟩
      have hcandidates : (state.candidates sample lam).Nonempty :=
        ⟨state.sourceCoordinate sample lam i,
          Finset.mem_union_left _ hiCandidate⟩
      rw [FeedbackStepState.nextCoordinate, dite_eq_left hcandidates]
      exact Finset.min'_le _ _ (Finset.mem_union_left _ hiCandidate)
    have hnext_le_target (j : Fin n) (hj : j ∉ state.seenTarget) :
        state.nextCoordinate sample lam ≤ state.targetCoordinate sample lam j := by
      have hjDiff : j ∈ Finset.univ \ state.seenTarget := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
      have hjCandidate : state.targetCoordinate sample lam j ∈
          state.targetCandidates sample lam := by
        exact Finset.mem_image.mpr ⟨j, hjDiff, rfl⟩
      have hcandidates : (state.candidates sample lam).Nonempty :=
        ⟨state.targetCoordinate sample lam j,
          Finset.mem_union_right _ hjCandidate⟩
      rw [FeedbackStepState.nextCoordinate, dite_eq_left hcandidates]
      exact Finset.min'_le _ _ (Finset.mem_union_right _ hjCandidate)
    intro other hne
    have hstrict : state.nextCoordinate sample lam ≠
        state.labelCoordinate sample lam (other : FeedbackLabel n) := by
      intro heq
      have hotherNew : (other : FeedbackLabel n) ∈
          FiniteSample.newLabelSet sample lam state := by
        rcases other with ⟨other, hotherS⟩
        cases other with
        | inl i =>
            have hi : i ∉ state.seenSource := by
              intro hiSeen
              have hiS : (Sum.inl i : FeedbackLabel n) ∉ S := by
                simpa [feedbackUnseenFinset] using hotherS
              exact hiS ((hsource i).mpr hiSeen)
            rw [FiniteSample.mem_newLabelSet_iff]
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
            simpa [FeedbackStepState.labelCoordinate] using heq.symm
        | inr j =>
            have hj : j ∉ state.seenTarget := by
              intro hjSeen
              have hjS : (Sum.inr j : FeedbackLabel n) ∉ S := by
                simpa [feedbackUnseenFinset] using hotherS
              exact hjS ((htarget j).mpr hjSeen)
            rw [FiniteSample.mem_newLabelSet_iff]
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩, ?_⟩
            simpa [FeedbackStepState.labelCoordinate] using heq.symm
      have hotherSingleton : (other : FeedbackLabel n) ∈
          ({(label : FeedbackLabel n)} : Finset (FeedbackLabel n)) := by
        simpa [hsingleton] using hotherNew
      have hlabels : (other : FeedbackLabel n) = (label : FeedbackLabel n) :=
        Finset.mem_singleton.mp hotherSingleton
      exact hne (Subtype.ext hlabels)
    have hle : state.nextCoordinate sample lam ≤
        state.labelCoordinate sample lam (other : FeedbackLabel n) := by
      rcases other with ⟨other, hotherS⟩
      cases other with
      | inl i =>
          have hi : i ∉ state.seenSource := by
            intro hiSeen
            have hiS : (Sum.inl i : FeedbackLabel n) ∉ S := by
              simpa [feedbackUnseenFinset] using hotherS
            exact hiS ((hsource i).mpr hiSeen)
          simpa [FeedbackStepState.labelCoordinate] using hnext_le_source i hi
      | inr j =>
          have hj : j ∉ state.seenTarget := by
            intro hjSeen
            have hjS : (Sum.inr j : FeedbackLabel n) ∉ S := by
              simpa [feedbackUnseenFinset] using hotherS
            exact hjS ((htarget j).mpr hjSeen)
          simpa [FeedbackStepState.labelCoordinate] using hnext_le_target j hj
    calc
      state.labelCoordinate sample lam (label : FeedbackLabel n) =
          state.nextCoordinate sample lam := hselectedNext
      _ < state.labelCoordinate sample lam (other : FeedbackLabel n) :=
        lt_of_le_of_ne hle hstrict
  · intro hstrict
    cases label with
    | mk label hlabel =>
        cases label with
        | inl i =>
            have hi : i ∉ state.seenSource := by
              intro hiSeen
              exact (by
                have hiS : (Sum.inl i : FeedbackLabel n) ∉ S := by
                  simpa [feedbackUnseenFinset] using hlabel
                exact hiS ((hsource i).mpr hiSeen))
            have hsource' : ∀ k, k ∉ state.seenSource → k ≠ i →
                state.sourceCoordinate sample lam i <
                  state.sourceCoordinate sample lam k := by
              intro k hk hki
              have hkS : (Sum.inl k : FeedbackLabel n) ∉ S := by
                intro hkMem
                exact hk ((hsource k).mp hkMem)
              have hkU : (Sum.inl k : FeedbackLabel n) ∈ feedbackUnseenFinset S := by
                simpa [feedbackUnseenFinset] using hkS
              have hiU : (Sum.inl i : FeedbackLabel n) ∈ feedbackUnseenFinset S := by
                simpa [feedbackUnseenFinset] using hlabel
              have hne : (⟨Sum.inl k, hkU⟩ : feedbackUnseenFinset S) ≠
                  (⟨Sum.inl i, hiU⟩ : feedbackUnseenFinset S) := by
                intro heq
                have hsum : (Sum.inl k : FeedbackLabel n) = Sum.inl i :=
                  congrArg (fun z : feedbackUnseenFinset S =>
                    (z : FeedbackLabel n)) heq
                exact hki (Sum.inl.inj hsum)
              have hlt := hstrict ⟨Sum.inl k, hkU⟩ hne
              simpa [FeedbackStepState.labelCoordinate] using hlt
            have htarget' : ∀ j, j ∉ state.seenTarget →
                state.sourceCoordinate sample lam i <
                  state.targetCoordinate sample lam j := by
              intro j hj
              have hjS : (Sum.inr j : FeedbackLabel n) ∉ S := by
                intro hjMem
                exact hj ((htarget j).mp hjMem)
              have hjU : (Sum.inr j : FeedbackLabel n) ∈ feedbackUnseenFinset S := by
                simpa [feedbackUnseenFinset] using hjS
              have hiU : (Sum.inl i : FeedbackLabel n) ∈ feedbackUnseenFinset S := by
                simpa [feedbackUnseenFinset] using hlabel
              have hne : (⟨Sum.inr j, hjU⟩ : feedbackUnseenFinset S) ≠
                  (⟨Sum.inl i, hiU⟩ : feedbackUnseenFinset S) := by
                intro heq
                have := congrArg (fun z : feedbackUnseenFinset S =>
                  (z : FeedbackLabel n)) heq
                simp at this
              have hlt := hstrict ⟨Sum.inr j, hjU⟩ hne
              simpa [FeedbackStepState.labelCoordinate] using hlt
            have hreal := FeedbackStepState.labelStepRealizes_of_source_unique_min
              sample lam state i hi hsource' htarget'
            simp [FiniteSample.newLabelSet, hreal.1, hreal.2]
        | inr j =>
            have hj : j ∉ state.seenTarget := by
              intro hjSeen
              exact (by
                have hjS : (Sum.inr j : FeedbackLabel n) ∉ S := by
                  simpa [feedbackUnseenFinset] using hlabel
                exact hjS ((htarget j).mpr hjSeen))
            have hsource' : ∀ k, k ∉ state.seenSource →
                state.targetCoordinate sample lam j <
                  state.sourceCoordinate sample lam k := by
              intro k hk
              have hkS : (Sum.inl k : FeedbackLabel n) ∉ S := by
                intro hkMem
                exact hk ((hsource k).mp hkMem)
              have hkU : (Sum.inl k : FeedbackLabel n) ∈ feedbackUnseenFinset S := by
                simpa [feedbackUnseenFinset] using hkS
              have hjU : (Sum.inr j : FeedbackLabel n) ∈ feedbackUnseenFinset S := by
                simpa [feedbackUnseenFinset] using hlabel
              have hne : (⟨Sum.inl k, hkU⟩ : feedbackUnseenFinset S) ≠
                  (⟨Sum.inr j, hjU⟩ : feedbackUnseenFinset S) := by
                intro heq
                have := congrArg (fun z : feedbackUnseenFinset S =>
                  (z : FeedbackLabel n)) heq
                simp at this
              have hlt := hstrict ⟨Sum.inl k, hkU⟩ hne
              simpa [FeedbackStepState.labelCoordinate] using hlt
            have htarget' : ∀ l, l ∉ state.seenTarget → l ≠ j →
                state.targetCoordinate sample lam j <
                  state.targetCoordinate sample lam l := by
              intro l hl hlj
              have hlS : (Sum.inr l : FeedbackLabel n) ∉ S := by
                intro hlMem
                exact hl ((htarget l).mp hlMem)
              have hlU : (Sum.inr l : FeedbackLabel n) ∈ feedbackUnseenFinset S := by
                simpa [feedbackUnseenFinset] using hlS
              have hjU : (Sum.inr j : FeedbackLabel n) ∈ feedbackUnseenFinset S := by
                simpa [feedbackUnseenFinset] using hlabel
              have hne : (⟨Sum.inr l, hlU⟩ : feedbackUnseenFinset S) ≠
                  (⟨Sum.inr j, hjU⟩ : feedbackUnseenFinset S) := by
                intro heq
                have hsum : (Sum.inr l : FeedbackLabel n) = Sum.inr j :=
                  congrArg (fun z : feedbackUnseenFinset S =>
                    (z : FeedbackLabel n)) heq
                exact hlj (Sum.inr.inj hsum)
              have hlt := hstrict ⟨Sum.inr l, hlU⟩ hne
              simpa [FeedbackStepState.labelCoordinate] using hlt
            have hreal := FeedbackStepState.labelStepRealizes_of_target_unique_min
              sample lam state j hj hsource' htarget'
            simp [FiniteSample.newLabelSet, hreal.1, hreal.2]

private theorem newLabelSet_eq_inl_singleton_iff
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n) :
    FiniteSample.newLabelSet sample lam state = {Sum.inl i} ↔
      state.newSource sample lam = {i} ∧ state.newTarget sample lam = ∅ := by
  classical
  constructor
  · intro h
    constructor
    · ext k
      constructor
      · intro hk
        have hmem : (Sum.inl k : FeedbackLabel n) ∈
            FiniteSample.newLabelSet sample lam state := by
          rw [FiniteSample.mem_newLabelSet_iff]
          exact hk
        rw [h] at hmem
        simpa using hmem
      · intro hk
        have hki : k = i := Finset.mem_singleton.mp hk
        subst k
        have hmem : (Sum.inl i : FeedbackLabel n) ∈
            FiniteSample.newLabelSet sample lam state := by
          rw [h]
          simp
        exact (FiniteSample.mem_newLabelSet_iff sample lam state (Sum.inl i)).mp hmem
    · ext j
      constructor
      · intro hj
        have hmem : (Sum.inr j : FeedbackLabel n) ∈
            FiniteSample.newLabelSet sample lam state := by
          rw [FiniteSample.mem_newLabelSet_iff]
          exact hj
        rw [h] at hmem
        simp at hmem
      · intro hj
        simp at hj
  · rintro ⟨hsource, htarget⟩
    simp [FiniteSample.newLabelSet, hsource, htarget]

private theorem newLabelSet_eq_inr_singleton_iff
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n) :
    FiniteSample.newLabelSet sample lam state = {Sum.inr j} ↔
      state.newSource sample lam = ∅ ∧ state.newTarget sample lam = {j} := by
  classical
  constructor
  · intro h
    constructor
    · ext i
      constructor
      · intro hi
        have hmem : (Sum.inl i : FeedbackLabel n) ∈
            FiniteSample.newLabelSet sample lam state := by
          rw [FiniteSample.mem_newLabelSet_iff]
          exact hi
        rw [h] at hmem
        simp at hmem
      · intro hi
        simp at hi
    · ext k
      constructor
      · intro hk
        have hmem : (Sum.inr k : FeedbackLabel n) ∈
            FiniteSample.newLabelSet sample lam state := by
          rw [FiniteSample.mem_newLabelSet_iff]
          exact hk
        rw [h] at hmem
        simpa using hmem
      · intro hk
        have hkj : k = j := Finset.mem_singleton.mp hk
        subst k
        have hmem : (Sum.inr j : FeedbackLabel n) ∈
            FiniteSample.newLabelSet sample lam state := by
          rw [h]
          simp
        exact (FiniteSample.mem_newLabelSet_iff sample lam state (Sum.inr j)).mp hmem
  · rintro ⟨hsource, htarget⟩
    simp [FiniteSample.newLabelSet, hsource, htarget]

/-! ## Fixed-terminal bridge -/

set_option linter.unusedVariables false in
theorem feedbackNextEventSet_finiteSampleSeenUnseenMerge_iff
    (state : FeedbackStepState n) (sample : FiniteSample n)
    (lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (label : feedbackUnseenFinset S) (hst : s ≤ t) :
    unseen ∈ feedbackNextEventSet lam state s t S label ↔
      state.labelCoordinate (finiteSampleSeenUnseenMerge S seen unseen) lam
          (label : FeedbackLabel n) ∈ Ioc s t ∧
        FiniteSample.newLabelSet (finiteSampleSeenUnseenMerge S seen unseen) lam state =
          {(label : FeedbackLabel n)} := by
  have hcross := feedbackLabelFixedStateCrossing_finiteSampleSeenUnseenMerge_eq
    state (finiteSampleSeenUnseenMerge S seen unseen) lam S seen unseen label
  rw [mem_feedbackNextEventSet_iff_remaining state lam s t S label unseen
    hlam0 hlamHalf hst]
  have hcrossIoc :
      feedbackLabelFixedStateCrossing n lam state label (unseen label) ∈ Ioc s t ↔
        state.labelCoordinate (finiteSampleSeenUnseenMerge S seen unseen) lam
            (label : FeedbackLabel n) ∈ Ioc s t := by
    rw [hcross]
  constructor
  · rintro ⟨hslab, hrest⟩
    refine ⟨hcrossIoc.mp ((mem_feedbackLabelRemainingSetAt_sdiff_iff_crossing_Ioc
      state lam s t label (unseen label) hlam0 hlamHalf hst).mp hslab), ?_⟩
    apply (newLabelSet_eq_singleton_iff_strict_min
      (finiteSampleSeenUnseenMerge S seen unseen) lam state S hsource htarget label).2
    intro other hne
    have hlt := hrest other hne
    have hltCross := (mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
      state lam (other : FeedbackLabel n) (unseen other)
        (feedbackLabelFixedStateCrossing n lam state label (unseen label))
        hlam0 hlamHalf).mp hlt
    have hltCoord :
        state.labelCoordinate (finiteSampleSeenUnseenMerge S seen unseen) lam
            (label : FeedbackLabel n) <
          state.labelCoordinate (finiteSampleSeenUnseenMerge S seen unseen) lam
            (other : FeedbackLabel n) := by
      rw [← feedbackLabelFixedStateCrossing_finiteSampleSeenUnseenMerge_eq
        state (finiteSampleSeenUnseenMerge S seen unseen) lam S seen unseen label]
      rw [← feedbackLabelFixedStateCrossing_finiteSampleSeenUnseenMerge_eq
        state (finiteSampleSeenUnseenMerge S seen unseen) lam S seen unseen other]
      exact hltCross
    exact hltCoord
  · rintro ⟨hcoord, hsingleton⟩
    have hstrict := (newLabelSet_eq_singleton_iff_strict_min
      (finiteSampleSeenUnseenMerge S seen unseen) lam state S hsource htarget label).1
      hsingleton
    refine ⟨?_, ?_⟩
    · exact (mem_feedbackLabelRemainingSetAt_sdiff_iff_crossing_Ioc
        state lam s t label (unseen label) hlam0 hlamHalf hst).mpr
        (hcrossIoc.mpr hcoord)
    · intro other hne
      have hlt := hstrict other hne
      have hltCross :
          feedbackLabelFixedStateCrossing n lam state label (unseen label) <
            feedbackLabelFixedStateCrossing n lam state other (unseen other) := by
        rw [feedbackLabelFixedStateCrossing_finiteSampleSeenUnseenMerge_eq
          state (finiteSampleSeenUnseenMerge S seen unseen) lam S seen unseen label]
        rw [feedbackLabelFixedStateCrossing_finiteSampleSeenUnseenMerge_eq
          state (finiteSampleSeenUnseenMerge S seen unseen) lam S seen unseen other]
        exact hlt
      exact (mem_feedbackLabelRemainingSetAt_iff_lt_fixedStateCrossing
          state lam (other : FeedbackLabel n) (unseen other)
            (feedbackLabelFixedStateCrossing n lam state label (unseen label))
            hlam0 hlamHalf).mpr hltCross

set_option linter.unusedVariables false in
theorem feedbackNextEventSet_finiteSampleSeenUnseenMerge_source_iff
    (state : FeedbackStepState n) (sample : FiniteSample n)
    (lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (label : feedbackUnseenFinset S) (i : Fin n)
    (hlabel : (label : FeedbackLabel n) = Sum.inl i) (hst : s ≤ t) :
    unseen ∈ feedbackNextEventSet lam state s t S label ↔
      state.sourceCoordinate (finiteSampleSeenUnseenMerge S seen unseen) lam i ∈ Ioc s t ∧
      state.newSource (finiteSampleSeenUnseenMerge S seen unseen) lam = {i} ∧
      state.newTarget (finiteSampleSeenUnseenMerge S seen unseen) lam = ∅ := by
  have hgeneric := feedbackNextEventSet_finiteSampleSeenUnseenMerge_iff
    state (finiteSampleSeenUnseenMerge S seen unseen) lam s t S hlam0 hlamHalf
      hsource htarget seen unseen label hst
  have hset := newLabelSet_eq_inl_singleton_iff
    (finiteSampleSeenUnseenMerge S seen unseen) lam state i
  constructor
  · intro h
    have hg := hgeneric.mp h
    have hcoord : state.sourceCoordinate
        (finiteSampleSeenUnseenMerge S seen unseen) lam i ∈ Ioc s t := by
      simpa [FeedbackStepState.labelCoordinate, hlabel] using hg.1
    have hnew : FiniteSample.newLabelSet
        (finiteSampleSeenUnseenMerge S seen unseen) lam state = {Sum.inl i} := by
      simpa [hlabel] using hg.2
    exact ⟨hcoord, hset.mp hnew |>.1, hset.mp hnew |>.2⟩
  · rintro ⟨hcoord, hsourceNew, htargetNew⟩
    apply hgeneric.mpr
    have hnew : FiniteSample.newLabelSet
        (finiteSampleSeenUnseenMerge S seen unseen) lam state = {Sum.inl i} :=
      hset.mpr ⟨hsourceNew, htargetNew⟩
    refine ⟨?_, ?_⟩
    simpa [FeedbackStepState.labelCoordinate, hlabel] using hcoord
    simpa [hlabel] using hnew

set_option linter.unusedVariables false in
theorem feedbackNextEventSet_finiteSampleSeenUnseenMerge_target_iff
    (state : FeedbackStepState n) (sample : FiniteSample n)
    (lam s t : ℝ) (S : Finset (FeedbackLabel n))
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hsource : ∀ i : Fin n,
      (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n,
      (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight)
    (label : feedbackUnseenFinset S) (j : Fin n)
    (hlabel : (label : FeedbackLabel n) = Sum.inr j) (hst : s ≤ t) :
    unseen ∈ feedbackNextEventSet lam state s t S label ↔
      state.targetCoordinate (finiteSampleSeenUnseenMerge S seen unseen) lam j ∈ Ioc s t ∧
      state.newSource (finiteSampleSeenUnseenMerge S seen unseen) lam = ∅ ∧
      state.newTarget (finiteSampleSeenUnseenMerge S seen unseen) lam = {j} := by
  have hgeneric := feedbackNextEventSet_finiteSampleSeenUnseenMerge_iff
    state (finiteSampleSeenUnseenMerge S seen unseen) lam s t S hlam0 hlamHalf
      hsource htarget seen unseen label hst
  have hset := newLabelSet_eq_inr_singleton_iff
    (finiteSampleSeenUnseenMerge S seen unseen) lam state j
  constructor
  · intro h
    have hg := hgeneric.mp h
    have hcoord : state.targetCoordinate
        (finiteSampleSeenUnseenMerge S seen unseen) lam j ∈ Ioc s t := by
      simpa [FeedbackStepState.labelCoordinate, hlabel] using hg.1
    have hnew : FiniteSample.newLabelSet
        (finiteSampleSeenUnseenMerge S seen unseen) lam state = {Sum.inr j} := by
      simpa [hlabel] using hg.2
    exact ⟨hcoord, hset.mp hnew |>.1, hset.mp hnew |>.2⟩
  · rintro ⟨hcoord, hsourceNew, htargetNew⟩
    apply hgeneric.mpr
    have hnew : FiniteSample.newLabelSet
        (finiteSampleSeenUnseenMerge S seen unseen) lam state = {Sum.inr j} :=
      hset.mpr ⟨hsourceNew, htargetNew⟩
    refine ⟨?_, ?_⟩
    simpa [FeedbackStepState.labelCoordinate, hlabel] using hcoord
    simpa [hlabel] using hnew

/-! ## Realized-history specialization and source/target corollaries -/

set_option linter.unusedVariables false in
theorem historyBranch_feedbackNextEventSet_finiteSampleSeenUnseenMerge_iff
    (reference : FiniteSample n) {lam x0 p0 s t : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (unseen : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (label : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history)) (hst : s ≤ t) :
    unseen ∈ feedbackNextEventSet lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s t
        (feedbackTerminalLabelSet sourcePattern targetPattern history) label ↔
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).labelCoordinate
          (finiteSampleSeenUnseenMerge
            (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen) lam
          (label : FeedbackLabel n) ∈ Ioc s t ∧
        FiniteSample.newLabelSet
            (finiteSampleSeenUnseenMerge
              (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen) lam
            (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) =
          {(label : FeedbackLabel n)} := by
  exact feedbackNextEventSet_finiteSampleSeenUnseenMerge_iff
    (state := reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
    (sample := finiteSampleSeenUnseenMerge
      (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
    (lam := lam) (s := s) (t := t)
    (S := feedbackTerminalLabelSet sourcePattern targetPattern history)
    (hlam0 := hlam0) (hlamHalf := hlamHalf)
    (hsource := fun i ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 sourcePattern targetPattern history i)
    (htarget := fun j ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 sourcePattern targetPattern history j)
    (seen := seen) (unseen := unseen) (label := label) hst

set_option linter.unusedVariables false in
theorem historyBranch_feedbackNextEventSet_source_iff
    (reference : FiniteSample n) {lam x0 p0 s t : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (unseen : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (label : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history))
    (i : Fin n) (hlabel : (label : FeedbackLabel n) = Sum.inl i)
    (hst : s ≤ t) :
    unseen ∈ feedbackNextEventSet lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s t
        (feedbackTerminalLabelSet sourcePattern targetPattern history) label ↔
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).sourceCoordinate
          (finiteSampleSeenUnseenMerge
            (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen) lam i ∈ Ioc s t ∧
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).newSource
          (finiteSampleSeenUnseenMerge
            (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen) lam = {i} ∧
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).newTarget
          (finiteSampleSeenUnseenMerge
            (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen) lam = ∅ := by
  exact feedbackNextEventSet_finiteSampleSeenUnseenMerge_source_iff
    (state := reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
    (sample := finiteSampleSeenUnseenMerge
      (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
    (lam := lam) (s := s) (t := t)
    (S := feedbackTerminalLabelSet sourcePattern targetPattern history)
    (hlam0 := hlam0) (hlamHalf := hlamHalf)
    (hsource := fun k ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 sourcePattern targetPattern history k)
    (htarget := fun k ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 sourcePattern targetPattern history k)
    (seen := seen) (unseen := unseen) (label := label) (i := i) hlabel hst

set_option linter.unusedVariables false in
theorem historyBranch_feedbackNextEventSet_target_iff
    (reference : FiniteSample n) {lam x0 p0 s t : ℝ}
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (href : HistoryBranch reference lam x0 p0 sourcePattern targetPattern history)
    (seen : feedbackTerminalLabelSet sourcePattern targetPattern history → MarkedHeight)
    (unseen : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history) → MarkedHeight)
    (hseen : seen = feedbackSeenTuple
      (feedbackTerminalLabelSet sourcePattern targetPattern history) reference)
    (label : feedbackUnseenFinset
      (feedbackTerminalLabelSet sourcePattern targetPattern history))
    (j : Fin n) (hlabel : (label : FeedbackLabel n) = Sum.inr j)
    (hst : s ≤ t) :
    unseen ∈ feedbackNextEventSet lam
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history) s t
        (feedbackTerminalLabelSet sourcePattern targetPattern history) label ↔
      (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).targetCoordinate
          (finiteSampleSeenUnseenMerge
            (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen) lam j ∈ Ioc s t ∧
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).newSource
          (finiteSampleSeenUnseenMerge
            (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen) lam = ∅ ∧
        (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).newTarget
          (finiteSampleSeenUnseenMerge
            (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen) lam = {j} := by
  exact feedbackNextEventSet_finiteSampleSeenUnseenMerge_target_iff
    (state := reference.scheduledState lam x0 p0 sourcePattern targetPattern history)
    (sample := finiteSampleSeenUnseenMerge
      (feedbackTerminalLabelSet sourcePattern targetPattern history) seen unseen)
    (lam := lam) (s := s) (t := t)
    (S := feedbackTerminalLabelSet sourcePattern targetPattern history)
    (hlam0 := hlam0) (hlamHalf := hlamHalf)
    (hsource := fun k ↦ mem_feedbackTerminalLabelSet_inl_iff_seenSource
      reference lam x0 p0 sourcePattern targetPattern history k)
    (htarget := fun k ↦ mem_feedbackTerminalLabelSet_inr_iff_seenTarget
      reference lam x0 p0 sourcePattern targetPattern history k)
    (seen := seen) (unseen := unseen) (label := label) (j := j) hlabel hst

end OTSelector
