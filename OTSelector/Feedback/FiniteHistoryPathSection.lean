import OTSelector.Feedback.FiniteHistorySnapshotSection

/-!
# Revealed snapshot paths on a finite-history coordinate cell

This file proves the deterministic pathwise factorization on one fixed coordinate cell.  The
argument only uses branch realization, equality of the points exposed by the terminal history,
and the strict remaining-region condition in the two cells.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

private theorem forcedHistoryRealizes_take
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n)
    (history : List (FeedbackLabel n))
    (hgood : FiniteSample.ForcedHistoryRealizes sample lam state history) :
    ∀ m ≤ history.length,
      FiniteSample.ForcedHistoryRealizes sample lam state (history.take m) := by
  induction history generalizing state with
  | nil =>
      intro m hm
      simp at hm
      simp [FiniteSample.ForcedHistoryRealizes]
  | cons label history ih =>
      intro m hm
      cases m with
      | zero =>
          exact trivial
      | succ m =>
          have hm' : m ≤ history.length := by
            simp only [List.length_cons] at hm
            omega
          have htail := ih (state := state.forcedLabelStep sample lam label)
            hgood.2 m hm'
          change FiniteSample.labelStepRealizes sample lam state label ∧
            FiniteSample.ForcedHistoryRealizes sample lam
              (state.forcedLabelStep sample lam label) (history.take m)
          exact ⟨hgood.1, htail⟩

private theorem history_points_eq_of_feedbackSeenTuple_eq
    (reference sample : FiniteSample n)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    ∀ label, label ∈ history →
      feedbackLabelPoint label reference = feedbackLabelPoint label sample := by
  intro label hlabel
  have hlabelS : label ∈ feedbackTerminalLabelSet sourcePattern targetPattern history := by
    cases label with
    | inl i =>
        simp only [mem_feedbackTerminalLabelSet_inl]
        exact Finset.mem_union_right _
          (FiniteSample.mem_sourceHistorySet_of_mem history i hlabel)
    | inr j =>
        simp only [mem_feedbackTerminalLabelSet_inr]
        exact Finset.mem_union_right _
          (FiniteSample.mem_targetHistorySet_of_mem history j hlabel)
  have hpoint := congrFun htuple ⟨label, hlabelS⟩
  simpa [feedbackSeenTuple, feedbackLabelTuple] using hpoint

private theorem scheduledState_eq_of_history_take_points_eq
    (reference sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (m : ℕ) (_hm : m ≤ history.length)
    (hpoints : ∀ label, label ∈ history →
      feedbackLabelPoint label reference = feedbackLabelPoint label sample) :
    reference.scheduledState lam x0 p0 sourcePattern targetPattern (history.take m) =
      sample.scheduledState lam x0 p0 sourcePattern targetPattern (history.take m) := by
  apply FiniteSample.scheduledState_eq_of_history_points_eq
  intro label hlabel
  exact hpoints label (List.mem_of_mem_take hlabel)

private theorem feedbackState_eq_of_history_take
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (m : ℕ)
    (hinit : sample.initialFeedbackState x0 p0 =
      FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern)
    (hgood : FiniteSample.ForcedHistoryRealizes
      sample lam (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern) history)
    (hm : m ≤ history.length) :
    sample.feedbackState lam x0 p0 m =
      sample.scheduledState lam x0 p0 sourcePattern targetPattern (history.take m) := by
  have htake := forcedHistoryRealizes_take sample lam
    (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern) history hgood m hm
  have hstate := FiniteSample.feedbackState_eq_scheduledState_of_history sample lam x0 p0
    sourcePattern targetPattern (history.take m) hinit htake
  have htake_len : (history.take m).length = m := by
    simp [List.length_take, Nat.min_eq_left hm]
  simpa [htake_len] using hstate

private theorem sourceHistorySet_take_subset
    (history : List (FeedbackLabel n)) (m : ℕ) :
    FiniteSample.sourceHistorySet (history.take m) ⊆
      FiniteSample.sourceHistorySet history := by
  induction history generalizing m with
  | nil => simp
  | cons label history ih =>
      cases m with
      | zero => simp
      | succ m =>
          cases label with
          | inl i =>
              simp only [List.take_succ_cons, FiniteSample.sourceHistorySet]
              intro k hk
              simp only [Finset.mem_insert] at hk ⊢
              rcases hk with rfl | hk
              · simp
              · exact Or.inr ((ih m) hk)
          | inr j =>
              simp only [List.take_succ_cons, FiniteSample.sourceHistorySet]
              exact ih m

private theorem targetHistorySet_take_subset
    (history : List (FeedbackLabel n)) (m : ℕ) :
    FiniteSample.targetHistorySet (history.take m) ⊆
      FiniteSample.targetHistorySet history := by
  induction history generalizing m with
  | nil => simp
  | cons label history ih =>
      cases m with
      | zero => simp
      | succ m =>
          cases label with
          | inl i =>
              simp only [List.take_succ_cons, FiniteSample.targetHistorySet]
              exact ih m
          | inr j =>
              simp only [List.take_succ_cons, FiniteSample.targetHistorySet]
              intro k hk
              simp only [Finset.mem_insert] at hk ⊢
              rcases hk with rfl | hk
              · simp
              · exact Or.inr ((ih m) hk)

private theorem feedbackState_seenSource_subset_of_history_take
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (m : ℕ) (_hm : m ≤ history.length)
  (hstate : sample.feedbackState lam x0 p0 m =
      sample.scheduledState lam x0 p0 sourcePattern targetPattern (history.take m)) :
    ∀ i, i ∈ (sample.feedbackState lam x0 p0 m).seenSource →
      i ∈ (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource := by
  intro i hi
  rw [hstate] at hi
  simp only [FiniteSample.scheduledState_seenSource] at hi ⊢
  simp only [Finset.mem_union] at hi ⊢
  rcases hi with hi | hi
  · exact Or.inl hi
  · right
    exact sourceHistorySet_take_subset history m hi

private theorem feedbackState_seenTarget_subset_of_history_take
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (m : ℕ) (_hm : m ≤ history.length)
    (hstate : sample.feedbackState lam x0 p0 m =
      sample.scheduledState lam x0 p0 sourcePattern targetPattern (history.take m)) :
    ∀ j, j ∈ (sample.feedbackState lam x0 p0 m).seenTarget →
      j ∈ (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget := by
  intro j hj
  rw [hstate] at hj
  simp only [FiniteSample.scheduledState_seenTarget] at hj ⊢
  simp only [Finset.mem_union] at hj ⊢
  rcases hj with hj | hj
  · exact Or.inl hj
  · right
    exact targetHistorySet_take_subset history m hj

private theorem maskedSourceArray_eq_of_seen_subset
    (reference sample : FiniteSample n) (state : FeedbackStepState n)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hseen : ∀ i, i ∈ state.seenSource →
      i ∈ (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    FiniteSample.maskedSourceArray reference state =
      FiniteSample.maskedSourceArray sample state := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  funext i
  by_cases hi : i ∈ state.seenSource
  · have hiT := hseen i hi
    have hiS : (Sum.inl i : FeedbackLabel n) ∈ S := by
      exact (mem_feedbackTerminalLabelSet_inl_iff_seenSource
        reference lam x0 p0 sourcePattern targetPattern history i).2 hiT
    have hpoint := congrFun htuple (⟨Sum.inl i, hiS⟩ : S)
    simpa [S, FiniteSample.maskedSourceArray, FiniteSample.maskedSourcePoint,
      hi, feedbackSeenTuple, feedbackLabelTuple, feedbackLabelPoint] using hpoint
  · simp [FiniteSample.maskedSourceArray, FiniteSample.maskedSourcePoint, hi]

private theorem maskedTargetArray_eq_of_seen_subset
    (reference sample : FiniteSample n) (state : FeedbackStepState n)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hseen : ∀ j, j ∈ state.seenTarget →
      j ∈ (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    FiniteSample.maskedTargetArray reference state =
      FiniteSample.maskedTargetArray sample state := by
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  funext j
  by_cases hj : j ∈ state.seenTarget
  · have hjT := hseen j hj
    have hjS : (Sum.inr j : FeedbackLabel n) ∈ S := by
      exact (mem_feedbackTerminalLabelSet_inr_iff_seenTarget
        reference lam x0 p0 sourcePattern targetPattern history j).2 hjT
    have hpoint := congrFun htuple (⟨Sum.inr j, hjS⟩ : S)
    simpa [S, FiniteSample.maskedTargetArray, FiniteSample.maskedTargetPoint,
      hj, feedbackSeenTuple, feedbackLabelTuple, feedbackLabelPoint] using hpoint
  · simp [FiniteSample.maskedTargetArray, FiniteSample.maskedTargetPoint, hj]

private theorem nextCoordinate_gt_of_liesInStateRemainingAt
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (state : FeedbackStepState n) {x y : ℝ} (hyx : y ≤ x)
    (hremaining : LiesInStateRemainingAt lam state x sample)
    (hcand : (state.candidates sample lam).Nonempty) :
    y < state.nextCoordinate sample lam := by
  have hsource_gt : ∀ i, i ∉ state.seenSource →
      x < state.sourceCoordinate sample lam i := by
    intro i hi
    have hi_mem := hremaining.1 i hi
    have hi_line : x <
        (n : ℝ) * (sample.sourceHeight i : ℝ) + sample.sourceSlope i *
          segmentCurve state.x state.p (state.slope lam) x := by
      simpa [sourceRawRemainingSetAt, sourceRawRemainingSet, FiniteSample.sourcePoint,
        FiniteSample.sourceSlope, FeedbackStepState.slope, mul_comm] using hi_mem
    have ha := sample.sourceSlope_mem i
    have hcross := (x_lt_sourceSegmentCrossing_iff ha.1 ha.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2 hi_line
    simpa only [FeedbackStepState.sourceCoordinate, FeedbackStepState.slope] using hcross
  have htarget_gt : ∀ j, j ∉ state.seenTarget →
      x < state.targetCoordinate sample lam j := by
    intro j hj
    have hj_mem := hremaining.2 j hj
    have hj_line : x <
        (n : ℝ) * (sample.targetHeight j : ℝ) - sample.targetSlope j *
          segmentCurve state.x state.p (state.slope lam) x := by
      simpa [targetRawRemainingSetAt, targetRawRemainingSet, FiniteSample.targetPoint,
        FiniteSample.targetSlope, FeedbackStepState.slope, mul_comm] using hj_mem
    have hb := sample.targetSlope_mem j
    have hcross := (x_lt_targetSegmentCrossing_iff hb.1 hb.2
      (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2 hj_line
    simpa only [FeedbackStepState.targetCoordinate, FeedbackStepState.slope] using hcross
  have hnext_mem := state.nextCoordinate_mem_candidates sample lam hcand
  rw [FeedbackStepState.candidates] at hnext_mem
  simp only [Finset.mem_union] at hnext_mem
  rcases hnext_mem with hsource | htarget
  · rw [FeedbackStepState.sourceCandidates] at hsource
    obtain ⟨i, hi, hcoord⟩ := Finset.mem_image.mp hsource
    have hnotseen : i ∉ state.seenSource := (Finset.mem_sdiff.mp hi).2
    have hxnext : x < state.nextCoordinate sample lam := by
      exact hcoord ▸ hsource_gt i hnotseen
    exact hyx.trans_lt hxnext
  · rw [FeedbackStepState.targetCandidates] at htarget
    obtain ⟨j, hj, hcoord⟩ := Finset.mem_image.mp htarget
    have hnottseen : j ∉ state.seenTarget := (Finset.mem_sdiff.mp hj).2
    have hxnext : x < state.nextCoordinate sample lam := by
      exact hcoord ▸ htarget_gt j hnottseen
    exact hyx.trans_lt hxnext

private theorem revealedSnapshotFromState_eq_of_seen_subset
    (reference sample : FiniteSample n) (stateReference stateSample : FeedbackStepState n)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hstate : stateReference = stateSample)
    (hsource : ∀ i, i ∈ stateReference.seenSource →
      i ∈ (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).seenSource)
    (htarget : ∀ j, j ∈ stateReference.seenTarget →
      j ∈ (reference.scheduledState lam x0 p0 sourcePattern targetPattern history).seenTarget)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    FiniteSample.revealedSnapshotFromState reference stateReference =
      FiniteSample.revealedSnapshotFromState sample stateSample := by
  have hsourceArray := maskedSourceArray_eq_of_seen_subset reference sample stateReference
    sourcePattern targetPattern history hsource htuple
  have htargetArray := maskedTargetArray_eq_of_seen_subset reference sample stateReference
    sourcePattern targetPattern history htarget htuple
  have hsourceArray' := hsourceArray
  have htargetArray' := htargetArray
  rw [hstate] at hsourceArray' htargetArray'
  simp only [FiniteSample.revealedSnapshotFromState]
  rw [hstate]
  rw [hsourceArray', htargetArray']

private theorem feedbackStateAtElapsed_eq_scheduledState_of_historyAtCoordinate_of_terminal_le
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hcell : HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x)
    (u : ℝ≥0) (hu : u ≤ ⟨x - x0, sub_nonneg.mpr hx0x⟩)
    (hterminal :
      (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x ≤
        x0 + (u : ℝ)) :
    sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u =
      sample.scheduledState lam x0 p0 sourcePattern targetPattern history := by
  classical
  let terminal := sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hinit : sample.initialFeedbackState x0 p0 =
      FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern := hcell.1.1
  have hgood : FiniteSample.ForcedHistoryRealizes sample lam
      (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern) history := hcell.1.2
  have hstate : sample.feedbackState lam x0 p0 history.length = terminal := by
    have h := FiniteSample.feedbackState_eq_scheduledState_of_history sample lam x0 p0
      sourcePattern targetPattern history hinit hgood
    simpa [terminal] using h
  have hlen : history.length ≤ 2 * n := hgood.length_le_two_mul
  have hyx : x0 + (u : ℝ) ≤ x := by
    have hu' : (u : ℝ) ≤ x - x0 := by
      have h := NNReal.coe_le_coe.mp hu
      change (u : ℝ) ≤ x - x0 at h
      exact h
    linarith
  have htermKnot : sample.feedbackKnot lam x0 p0 history.length = terminal.x := by
    simpa [FiniteSample.feedbackKnot, terminal] using congrArg FeedbackStepState.x hstate
  have hleft_real : sample.feedbackKnot lam x0 p0 history.length - x0 ≤ (u : ℝ) := by
    rw [htermKnot]
    linarith
  have hleft : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 history.length ≤ u := by
    apply NNReal.coe_le_coe.mp
    simpa only [FiniteSample.coe_elapsedFeedbackKnot] using hleft_real
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 u
  have hI_mem : I ∈ sample.elapsedIndexSet hlam0 hlamHalf x0 p0 u := by
    simpa [I] using sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 u
  have hI_ge : history.length ≤ I.val := by
    let J : Fin (2 * n + 1) := ⟨history.length, by omega⟩
    have hJ_mem : J ∈ sample.elapsedIndexSet hlam0 hlamHalf x0 p0 u := by
      simp only [FiniteSample.elapsedIndexSet, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa only [J] using hleft
    have hset_nonempty :
        (sample.elapsedIndexSet hlam0 hlamHalf x0 p0 u).Nonempty := by
      exact ⟨0, sample.zero_mem_elapsedIndexSet hlam0 hlamHalf x0 p0 u⟩
    have hle := FiniteSample.le_maxFinsetIndex ⟨0, by omega⟩ hset_nonempty hJ_mem
    exact hle
  by_cases hcand :
      ((sample.feedbackState lam x0 p0 history.length).candidates sample lam).Nonempty
  · have hremaining : LiesInStateRemainingAt lam
        (sample.feedbackState lam x0 p0 history.length) x sample := by
      rw [hstate]
      exact hcell.2.2
    have hnext : x0 + (u : ℝ) <
        (sample.feedbackState lam x0 p0 history.length).nextCoordinate sample lam := by
      exact nextCoordinate_gt_of_liesInStateRemainingAt sample hlam0 hlamHalf _ hyx
        hremaining hcand
    have hstep : sample.feedbackKnot lam x0 p0 (history.length + 1) =
        (sample.feedbackState lam x0 p0 history.length).nextCoordinate sample lam := by
      simp only [FiniteSample.feedbackKnot, FiniteSample.feedbackState_succ,
        FeedbackStepState.step]
    have hnext_knot : x0 + (u : ℝ) <
        sample.feedbackKnot lam x0 p0 (history.length + 1) := by
      rw [hstep]
      exact hnext
    have hI_le : I.val ≤ history.length := by
      by_contra hnot
      have hgt : history.length < I.val := Nat.lt_of_not_ge hnot
      have hsucc : history.length + 1 ≤ I.val := by omega
      have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0 hsucc
      have hK : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 I.val ≤ u := by
        simpa only [FiniteSample.elapsedIndexSet, Finset.mem_filter,
          Finset.mem_univ, true_and] using hI_mem
      have hKreal :
          (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 I.val : ℝ) ≤ (u : ℝ) :=
        NNReal.coe_le_coe.mpr hK
      have hKsub : sample.feedbackKnot lam x0 p0 I.val - x0 ≤ (u : ℝ) := by
        simpa only [FiniteSample.coe_elapsedFeedbackKnot] using hKreal
      have hnext_le : sample.feedbackKnot lam x0 p0 (history.length + 1) ≤
          sample.feedbackKnot lam x0 p0 I.val := hmono
      linarith
    have hI_eq : I.val = history.length := Nat.le_antisymm hI_le hI_ge
    rw [FiniteSample.feedbackStateAtElapsed]
    have hI_eq' :
        (sample.elapsedIndex hlam0 hlamHalf x0 p0 u).val = history.length := by
      simpa [I] using hI_eq
    rw [hI_eq']
    exact hstate
  · have hcand_empty :
        (sample.feedbackState lam x0 p0 history.length).candidates sample lam = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcand
    have hstate_idx : sample.feedbackState lam x0 p0 I.val =
        sample.feedbackState lam x0 p0 history.length := by
      have hstable := sample.feedbackState_eq_of_candidates_eq_empty lam x0 p0
        history.length hcand_empty (I.val - history.length)
      simpa [Nat.add_sub_of_le hI_ge] using hstable
    rw [FiniteSample.feedbackStateAtElapsed]
    have hstate_idx' :
        sample.feedbackState lam x0 p0
            (sample.elapsedIndex hlam0 hlamHalf x0 p0 u).val =
          sample.feedbackState lam x0 p0 history.length := by
      simpa [I] using hstate_idx
    rw [hstate_idx', hstate]

/-! ## Path equality on one coordinate cell -/

theorem revealedSnapshotAtElapsed_eq_of_historyAtCoordinate_of_le
    (reference sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history x)
    (hsample : HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample)
    (u : ℝ≥0) (hu : u ≤ ⟨x - x0, sub_nonneg.mpr hx0x⟩) :
    reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 u =
      sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 u := by
  classical
  let endpoint : ℝ≥0 := ⟨x - x0, sub_nonneg.mpr hx0x⟩
  have hu_real : (u : ℝ) ≤ x - x0 := by
    have h := NNReal.coe_le_coe.mp hu
    change (u : ℝ) ≤ x - x0 at h
    exact h
  let y : ℝ := x0 + (u : ℝ)
  have hy0 : x0 ≤ y := by
    dsimp [y]
    exact le_add_of_nonneg_right u.coe_nonneg
  have hyx : y ≤ x := by
    dsimp [y]
    linarith
  let terminalReference :=
    reference.scheduledState lam x0 p0 sourcePattern targetPattern history
  let terminalSample :=
    sample.scheduledState lam x0 p0 sourcePattern targetPattern history
  have hrefInit : reference.initialFeedbackState x0 p0 =
      FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern := href.1.1
  have hsampleInit : sample.initialFeedbackState x0 p0 =
      FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern := hsample.1.1
  have hrefGood : FiniteSample.ForcedHistoryRealizes reference lam
      (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern) history := href.1.2
  have hsampleGood : FiniteSample.ForcedHistoryRealizes sample lam
      (FiniteSample.forcedInitialState x0 p0 sourcePattern targetPattern) history := hsample.1.2
  have hpoints : ∀ label, label ∈ history →
      feedbackLabelPoint label reference = feedbackLabelPoint label sample :=
    history_points_eq_of_feedbackSeenTuple_eq reference sample sourcePattern targetPattern history
      htuple
  have hrefState : ∀ m ≤ history.length,
      reference.feedbackState lam x0 p0 m =
        reference.scheduledState lam x0 p0 sourcePattern targetPattern (history.take m) := by
    intro m hm
    exact feedbackState_eq_of_history_take reference lam x0 p0 sourcePattern targetPattern
      history m hrefInit hrefGood hm
  have hsampleState : ∀ m ≤ history.length,
      sample.feedbackState lam x0 p0 m =
        sample.scheduledState lam x0 p0 sourcePattern targetPattern (history.take m) := by
    intro m hm
    exact feedbackState_eq_of_history_take sample lam x0 p0 sourcePattern targetPattern
      history m hsampleInit hsampleGood hm
  have hprefixEq : ∀ m ≤ history.length,
      reference.scheduledState lam x0 p0 sourcePattern targetPattern (history.take m) =
        sample.scheduledState lam x0 p0 sourcePattern targetPattern (history.take m) := by
    intro m hm
    exact scheduledState_eq_of_history_take_points_eq reference sample lam x0 p0
      sourcePattern targetPattern history m hm hpoints
  have hfeedbackEq : ∀ m ≤ history.length,
      reference.feedbackState lam x0 p0 m = sample.feedbackState lam x0 p0 m := by
    intro m hm
    exact (hrefState m hm).trans ((hprefixEq m hm).trans (hsampleState m hm).symm)
  have hknotEq : ∀ m ≤ history.length,
      reference.feedbackKnot lam x0 p0 m = sample.feedbackKnot lam x0 p0 m := by
    intro m hm
    simpa [FiniteSample.feedbackKnot] using
      congrArg FeedbackStepState.x (hfeedbackEq m hm)
  have hterminalEq : terminalReference = terminalSample := by
    dsimp [terminalReference, terminalSample]
    simpa using scheduledState_eq_of_history_take_points_eq reference sample lam x0 p0
      sourcePattern targetPattern history history.length le_rfl hpoints
  have htermKnotReference : reference.feedbackKnot lam x0 p0 history.length =
      terminalReference.x := by
    have hstate := hrefState history.length le_rfl
    simpa [FiniteSample.feedbackKnot, terminalReference] using
      congrArg FeedbackStepState.x hstate
  have htermKnotSample : sample.feedbackKnot lam x0 p0 history.length =
      terminalSample.x := by
    have hstate := hsampleState history.length le_rfl
    simpa [FiniteSample.feedbackKnot, terminalSample] using
      congrArg FeedbackStepState.x hstate
  have hlen : history.length ≤ 2 * n := hrefGood.length_le_two_mul
  have hterminal_ge_x0 : x0 ≤ terminalReference.x := by
    have h := reference.feedbackKnot_ge_x0 hlam0 hlamHalf x0 p0 history.length
    rw [htermKnotReference] at h
    exact h
  have hterminalSample_ge_x0 : x0 ≤ terminalSample.x := by
    have h := sample.feedbackKnot_ge_x0 hlam0 hlamHalf x0 p0 history.length
    rw [htermKnotSample] at h
    exact h
  by_cases hyterm : y < terminalReference.x
  · have hytermSample : y < terminalSample.x := by
      have hxy := congrArg FeedbackStepState.x hterminalEq
      simpa [hxy] using hyterm
    have hnotReference : ∀ k : Fin (2 * n + 1), history.length ≤ k.val →
        k ∉ reference.elapsedIndexSet hlam0 hlamHalf x0 p0 u := by
      intro k hk hmem
      have hK : reference.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k.val ≤ u := by
        simpa only [FiniteSample.elapsedIndexSet, Finset.mem_filter,
          Finset.mem_univ, true_and] using hmem
      have hKreal :
          (reference.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k.val : ℝ) ≤ (u : ℝ) :=
        NNReal.coe_le_coe.mpr hK
      have hKsub : reference.feedbackKnot lam x0 p0 k.val - x0 ≤ (u : ℝ) := by
        simpa only [FiniteSample.coe_elapsedFeedbackKnot] using hKreal
      have hterm_le : terminalReference.x ≤ reference.feedbackKnot lam x0 p0 k.val := by
        rw [← htermKnotReference]
        exact reference.feedbackState_x_mono hlam0 hlamHalf x0 p0 hk
      have hylt : y < reference.feedbackKnot lam x0 p0 k.val :=
        hyterm.trans_le hterm_le
      linarith
    have hnotSample : ∀ k : Fin (2 * n + 1), history.length ≤ k.val →
        k ∉ sample.elapsedIndexSet hlam0 hlamHalf x0 p0 u := by
      intro k hk hmem
      have hK : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k.val ≤ u := by
        simpa only [FiniteSample.elapsedIndexSet, Finset.mem_filter,
          Finset.mem_univ, true_and] using hmem
      have hKreal :
          (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k.val : ℝ) ≤ (u : ℝ) :=
        NNReal.coe_le_coe.mpr hK
      have hKsub : sample.feedbackKnot lam x0 p0 k.val - x0 ≤ (u : ℝ) := by
        simpa only [FiniteSample.coe_elapsedFeedbackKnot] using hKreal
      have hterm_le : terminalSample.x ≤ sample.feedbackKnot lam x0 p0 k.val := by
        rw [← htermKnotSample]
        exact sample.feedbackState_x_mono hlam0 hlamHalf x0 p0 hk
      have hylt : y < sample.feedbackKnot lam x0 p0 k.val :=
        hytermSample.trans_le hterm_le
      linarith
    have hsetEq :
        reference.elapsedIndexSet hlam0 hlamHalf x0 p0 u =
          sample.elapsedIndexSet hlam0 hlamHalf x0 p0 u := by
      ext k
      by_cases hk : k.val < history.length
      · have hk_le : k.val ≤ history.length := Nat.le_of_lt hk
        have hK : reference.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k.val =
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k.val := by
          apply NNReal.eq
          simpa only [FiniteSample.coe_elapsedFeedbackKnot] using
            congrArg (fun z : ℝ ↦ z - x0) (hknotEq k.val hk_le)
        simp only [FiniteSample.elapsedIndexSet, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rw [hK]
      · have hk_ge : history.length ≤ k.val := Nat.le_of_not_gt hk
        exact iff_of_false (hnotReference k hk_ge) (hnotSample k hk_ge)
    let IReference := reference.elapsedIndex hlam0 hlamHalf x0 p0 u
    let ISample := sample.elapsedIndex hlam0 hlamHalf x0 p0 u
    have hIeq : IReference = ISample := by
      dsimp [IReference, ISample, FiniteSample.elapsedIndex]
      rw [hsetEq]
    have hIReference_lt : IReference.val < history.length := by
      by_contra hnot
      have hmem := reference.elapsedIndex_mem hlam0 hlamHalf x0 p0 u
      exact (hnotReference IReference (Nat.le_of_not_gt hnot)) hmem
    have hISample_lt : ISample.val < history.length := by
      by_contra hnot
      have hmem := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 u
      exact (hnotSample ISample (Nat.le_of_not_gt hnot)) hmem
    have hstateAt : reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u =
        sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u := by
      change reference.feedbackState lam x0 p0 IReference.val =
        sample.feedbackState lam x0 p0 ISample.val
      rw [hIeq]
      exact hfeedbackEq ISample.val (Nat.le_of_lt hISample_lt)
    have hsourceAt : ∀ i,
        i ∈ (reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u).seenSource →
          i ∈ terminalReference.seenSource := by
      intro i hi
      have hi' : i ∈ (reference.feedbackState lam x0 p0 IReference.val).seenSource := by
        simpa [FiniteSample.feedbackStateAtElapsed, IReference] using hi
      have hsub := feedbackState_seenSource_subset_of_history_take reference lam x0 p0
        sourcePattern targetPattern history IReference.val
        (Nat.le_of_lt hIReference_lt) (hrefState IReference.val
          (Nat.le_of_lt hIReference_lt)) i hi'
      simpa [terminalReference] using hsub
    have htargetAt : ∀ j,
        j ∈ (reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u).seenTarget →
          j ∈ terminalReference.seenTarget := by
      intro j hj
      have hj' : j ∈ (reference.feedbackState lam x0 p0 IReference.val).seenTarget := by
        simpa [FiniteSample.feedbackStateAtElapsed, IReference] using hj
      have hsub := feedbackState_seenTarget_subset_of_history_take reference lam x0 p0
        sourcePattern targetPattern history IReference.val
        (Nat.le_of_lt hIReference_lt) (hrefState IReference.val
          (Nat.le_of_lt hIReference_lt)) j hj'
      simpa [terminalReference] using hsub
    simpa [FiniteSample.revealedSnapshotAtElapsed] using
      revealedSnapshotFromState_eq_of_seen_subset reference sample
        (reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u)
        (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u)
        sourcePattern targetPattern history hstateAt hsourceAt htargetAt htuple
  · have hterminal_le_y : terminalReference.x ≤ y := le_of_not_gt hyterm
    have hterminalSample_le_y : terminalSample.x ≤ y := by
      have hxy := congrArg FeedbackStepState.x hterminalEq
      calc
        terminalSample.x = terminalReference.x := hxy.symm
        _ ≤ y := hterminal_le_y
    have hrefAt :=
      feedbackStateAtElapsed_eq_scheduledState_of_historyAtCoordinate_of_terminal_le
        reference hlam0 hlamHalf hx0x sourcePattern targetPattern history href u hu (by
          simpa [terminalReference, y] using hterminal_le_y)
    have hsampleAt :=
      feedbackStateAtElapsed_eq_scheduledState_of_historyAtCoordinate_of_terminal_le
        sample hlam0 hlamHalf hx0x sourcePattern targetPattern history hsample u hu (by
          simpa [terminalSample, y] using hterminalSample_le_y)
    have hstateAt : reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u =
        sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u := by
      calc
        reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u = terminalReference := by
          simpa [terminalReference] using hrefAt
        _ = terminalSample := hterminalEq
        _ = sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u := by
          simpa [terminalSample] using hsampleAt.symm
    have hsourceAt : ∀ i,
        i ∈ (reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u).seenSource →
          i ∈ terminalReference.seenSource := by
      intro i hi
      have hi' := hi
      rw [hrefAt] at hi'
      simpa [terminalReference] using hi'
    have htargetAt : ∀ j,
        j ∈ (reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u).seenTarget →
          j ∈ terminalReference.seenTarget := by
      intro j hj
      have hj' := hj
      rw [hrefAt] at hj'
      simpa [terminalReference] using hj'
    simpa [FiniteSample.revealedSnapshotAtElapsed] using
      revealedSnapshotFromState_eq_of_seen_subset reference sample
        (reference.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u)
        (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 u)
        sourcePattern targetPattern history hstateAt hsourceAt htargetAt htuple

/-! The same factorization as an equality of paths on the elapsed interval. -/

theorem revealedSnapshotAtElapsed_path_eq_of_historyAtCoordinate
    (reference sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    {sourcePattern targetPattern : Finset (Fin n)}
    {history : List (FeedbackLabel n)}
    (href : HistoryAtCoordinate reference lam x0 p0 sourcePattern targetPattern history x)
    (hsample : HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x)
    (htuple :
      feedbackSeenTuple (feedbackTerminalLabelSet sourcePattern targetPattern history) reference =
        feedbackSeenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample) :
    (fun u : Set.Iic (⟨x - x0, sub_nonneg.mpr hx0x⟩ : ℝ≥0) ↦
      reference.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 u.1) =
      (fun u : Set.Iic (⟨x - x0, sub_nonneg.mpr hx0x⟩ : ℝ≥0) ↦
        sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 u.1) := by
  funext u
  exact revealedSnapshotAtElapsed_eq_of_historyAtCoordinate_of_le reference sample
    hlam0 hlamHalf hx0x href hsample htuple u.1 u.2

end OTSelector
