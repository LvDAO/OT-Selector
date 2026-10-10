import OTSelector.Feedback.FiniteHistoryBefore
import OTSelector.Feedback.FeedbackPredictableRate

/-!
# Strict-cell counting and state identities

This file supplies the pathwise bridge from a strict history cell to the predictable
left limits.  `HistoryBeforeCoordinate` carries the no-tie condition as part of the
ordinary strict-cell proposition, so the identities below need no separate certificate.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

namespace FiniteSample

private theorem historyBefore_terminal_data
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    let terminal := sample.scheduledState lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
    sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ = terminal ∧
      sample.feedbackState lam x0 p0 history.length = terminal ∧
      sample.feedbackKnot lam x0 p0 history.length = terminal.x ∧
      terminal.x < x := by
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have hAt := HistoryBeforeCoordinate.feedbackStateAtElapsed_eq_scheduledState
    sample hlam0 hlamHalf hx0x hbefore
  change (HistoryBranch sample lam x0 p0 (sample.initialSeenSource x0 p0)
      (sample.initialSeenTarget x0 p0) history ∧
      terminal.x < x ∧
      (∀ i, i ∉ terminal.seenSource →
        x < terminal.sourceCoordinate sample lam i) ∧
      (∀ j, j ∉ terminal.seenTarget →
        x < terminal.targetCoordinate sample lam j)) ∧ _ at hbefore
  have hbase := hbefore.1
  have hbranch : HistoryBranch sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history :=
    hbase.1
  have hstate := FiniteSample.feedbackState_eq_scheduledState_of_history sample lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
    hbranch.1 hbranch.2
  have htermKnot : sample.feedbackKnot lam x0 p0 history.length = terminal.x := by
    simpa [FiniteSample.feedbackKnot, terminal] using
      congrArg FeedbackStepState.x hstate
  have hterminal_lt : terminal.x < x := hbase.2.1
  exact ⟨by simpa [terminal] using hAt, by simpa [terminal] using hstate,
    htermKnot, hterminal_lt⟩

private theorem elapsedTerminal_lt_elapsedCoordinate
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 history.length <
      ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ := by
  obtain ⟨_, _, htermKnot, hterminal_lt⟩ := historyBefore_terminal_data
    sample hlam0 hlamHalf hx0x hbefore
  apply NNReal.coe_lt_coe.mp
  change sample.feedbackKnot lam x0 p0 history.length - x0 < x - x0
  rw [htermKnot]
  linarith

theorem countBefore_safeSourceCount_eq_terminal_sdiff_card
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    CountingProcess.countBefore
      (safeSourceCount hlam0 hlamHalf x0 p0)
      ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ sample =
      ((sample.scheduledState lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history).seenSource \
        sample.initialSeenSource x0 p0).card := by
  classical
  let t : ℝ≥0 := ⟨x - x0, sub_nonneg.mpr hx0x.le⟩
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have hNoTie : sample.NoFeedbackTies lam x0 p0 := hbefore.2
  obtain ⟨hAt, hstate, htermKnot, hterminal_lt⟩ := historyBefore_terminal_data
    sample hlam0 hlamHalf hx0x hbefore
  let tTerminal := sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 history.length
  have htermTime : tTerminal < t := by
    exact elapsedTerminal_lt_elapsedCoordinate sample hlam0 hlamHalf hx0x hbefore
  have hAtTerminal : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 tTerminal = terminal := by
    calc
      sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 tTerminal =
          sample.feedbackState lam x0 p0 history.length := by
            simpa [tTerminal] using
              (sample.feedbackStateAtElapsed_at_elapsedFeedbackKnot hlam0 hlamHalf x0 p0
                (hbefore.1.1.2.length_le_two_mul))
      _ = terminal := hstate
  have hfilter :
      (Finset.univ.filter (fun i : Fin n ↦
        sourceEventTime hlam0 hlamHalf x0 p0 i sample < (t : WithTop ℝ≥0))) =
        terminal.seenSource \ sample.initialSeenSource x0 p0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · intro hi
      have hle := (sample.sourceEventTime_le_iff_seen_diff hlam0 hlamHalf x0 p0 i t).1
        (le_of_lt hi)
      have hi' := hle.2
      simpa [hAt, terminal, t] using hi'
    · intro hi
      have hiTerminal : i ∈
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 tTerminal).seenSource \
            sample.initialSeenSource x0 p0 := by
        simpa [hAtTerminal, terminal] using hi
      have hleTerminal :=
        (sample.sourceEventTime_le_iff_seen_diff hlam0 hlamHalf x0 p0 i tTerminal).2
          ⟨hNoTie, hiTerminal⟩
      exact lt_of_le_of_lt hleTerminal (WithTop.coe_lt_coe.mpr htermTime)
  unfold safeSourceCount
  change CountingProcess.countBefore
      (fun s ω' ↦ CountingProcess.finiteEventCountTop
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s ω')
      t sample = _
  exact
    (CountingProcess.countBefore_finiteEventCountTop_eq_card_filter_lt
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) sample t).trans
      (congrArg Finset.card hfilter)

theorem countBefore_safeTargetCount_eq_terminal_sdiff_card
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    CountingProcess.countBefore
      (safeTargetCount hlam0 hlamHalf x0 p0)
      ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ sample =
      ((sample.scheduledState lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history).seenTarget \
        sample.initialSeenTarget x0 p0).card := by
  classical
  let t : ℝ≥0 := ⟨x - x0, sub_nonneg.mpr hx0x.le⟩
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have hNoTie : sample.NoFeedbackTies lam x0 p0 := hbefore.2
  obtain ⟨hAt, hstate, htermKnot, hterminal_lt⟩ := historyBefore_terminal_data
    sample hlam0 hlamHalf hx0x hbefore
  let tTerminal := sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 history.length
  have htermTime : tTerminal < t := by
    exact elapsedTerminal_lt_elapsedCoordinate sample hlam0 hlamHalf hx0x hbefore
  have hAtTerminal : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 tTerminal = terminal := by
    calc
      sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 tTerminal =
          sample.feedbackState lam x0 p0 history.length := by
            simpa [tTerminal] using
              (sample.feedbackStateAtElapsed_at_elapsedFeedbackKnot hlam0 hlamHalf x0 p0
                (hbefore.1.1.2.length_le_two_mul))
      _ = terminal := hstate
  have hfilter :
      (Finset.univ.filter (fun j : Fin n ↦
        targetEventTime hlam0 hlamHalf x0 p0 j sample < (t : WithTop ℝ≥0))) =
        terminal.seenTarget \ sample.initialSeenTarget x0 p0 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · intro hj
      have hle := (sample.targetEventTime_le_iff_seen_diff hlam0 hlamHalf x0 p0 j t).1
        (le_of_lt hj)
      have hj' := hle.2
      simpa [hAt, terminal, t] using hj'
    · intro hj
      have hjTerminal : j ∈
          (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 tTerminal).seenTarget \
            sample.initialSeenTarget x0 p0 := by
        simpa [hAtTerminal, terminal] using hj
      have hleTerminal :=
        (sample.targetEventTime_le_iff_seen_diff hlam0 hlamHalf x0 p0 j tTerminal).2
          ⟨hNoTie, hjTerminal⟩
      exact lt_of_le_of_lt hleTerminal (WithTop.coe_lt_coe.mpr htermTime)
  unfold safeTargetCount
  change CountingProcess.countBefore
      (fun s ω' ↦ CountingProcess.finiteEventCountTop
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s ω')
      t sample = _
  exact
    (CountingProcess.countBefore_finiteEventCountTop_eq_card_filter_lt
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) sample t).trans
      (congrArg Finset.card hfilter)

theorem safeSourceRemainingBefore_eq_n_sub_terminal_seenSource_card
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    safeSourceRemainingBefore hlam0 hlamHalf x0 p0
      ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ sample =
      (n : ℝ) -
        ((sample.scheduledState lam x0 p0
          (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history).seenSource.card : ℝ) := by
  classical
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have hNoTie : sample.NoFeedbackTies lam x0 p0 := hbefore.2
  have hsubset : sample.initialSeenSource x0 p0 ⊆ terminal.seenSource := by
    rw [scheduledState_seenSource]
    exact Finset.subset_union_left
  have hcard := Finset.card_sdiff_add_card terminal.seenSource
    (sample.initialSeenSource x0 p0)
  rw [Finset.union_eq_left.mpr hsubset] at hcard
  have hcardReal :
      ((terminal.seenSource \ sample.initialSeenSource x0 p0).card : ℝ) +
          (sample.initialSeenSource x0 p0).card =
        (terminal.seenSource.card : ℝ) := by
    exact_mod_cast hcard
  have hcount := countBefore_safeSourceCount_eq_terminal_sdiff_card
    sample hlam0 hlamHalf hx0x hbefore
  unfold safeSourceRemainingBefore safeInitialSourceRemainingReal
    initialSourceRemainingReal
  simp only [hNoTie, ↓reduceIte]
  rw [hcount]
  change (n : ℝ) - (sample.initialSeenSource x0 p0).card -
      ((terminal.seenSource \ sample.initialSeenSource x0 p0).card : ℝ) =
    (n : ℝ) - (terminal.seenSource.card : ℝ)
  linarith

theorem safeTargetRemainingBefore_eq_n_sub_terminal_seenTarget_card
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    safeTargetRemainingBefore hlam0 hlamHalf x0 p0
      ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ sample =
      (n : ℝ) -
        ((sample.scheduledState lam x0 p0
          (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history).seenTarget.card : ℝ) := by
  classical
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have hNoTie : sample.NoFeedbackTies lam x0 p0 := hbefore.2
  have hsubset : sample.initialSeenTarget x0 p0 ⊆ terminal.seenTarget := by
    rw [scheduledState_seenTarget]
    exact Finset.subset_union_left
  have hcard := Finset.card_sdiff_add_card terminal.seenTarget
    (sample.initialSeenTarget x0 p0)
  rw [Finset.union_eq_left.mpr hsubset] at hcard
  have hcardReal :
      ((terminal.seenTarget \ sample.initialSeenTarget x0 p0).card : ℝ) +
          (sample.initialSeenTarget x0 p0).card =
        (terminal.seenTarget.card : ℝ) := by
    exact_mod_cast hcard
  have hcount := countBefore_safeTargetCount_eq_terminal_sdiff_card
    sample hlam0 hlamHalf hx0x hbefore
  unfold safeTargetRemainingBefore safeInitialTargetRemainingReal
    initialTargetRemainingReal
  simp only [hNoTie, ↓reduceIte]
  rw [hcount]
  change (n : ℝ) - (sample.initialSeenTarget x0 p0).card -
      ((terminal.seenTarget \ sample.initialSeenTarget x0 p0).card : ℝ) =
    (n : ℝ) - (terminal.seenTarget.card : ℝ)
  linarith

theorem safePreCurrentAt_eq_terminal_current
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    safePreCurrentAt hlam0 hlamHalf x0 p0
      ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ sample =
      (sample.scheduledState lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history).current := by
  classical
  let terminal := sample.scheduledState lam x0 p0
    (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history
  have hNoTie : sample.NoFeedbackTies lam x0 p0 := hbefore.2
  obtain ⟨_, hstate, _, _⟩ := historyBefore_terminal_data
    sample hlam0 hlamHalf hx0x hbefore
  have hsource := countBefore_safeSourceCount_eq_terminal_sdiff_card
    sample hlam0 hlamHalf hx0x hbefore
  have htarget := countBefore_safeTargetCount_eq_terminal_sdiff_card
    sample hlam0 hlamHalf hx0x hbefore
  have hsubsetSource : sample.initialSeenSource x0 p0 ⊆ terminal.seenSource := by
    rw [scheduledState_seenSource]
    exact Finset.subset_union_left
  have hsubsetTarget : sample.initialSeenTarget x0 p0 ⊆ terminal.seenTarget := by
    rw [scheduledState_seenTarget]
    exact Finset.subset_union_left
  have hcardSource := Finset.card_sdiff_add_card terminal.seenSource
    (sample.initialSeenSource x0 p0)
  rw [Finset.union_eq_left.mpr hsubsetSource] at hcardSource
  have hcardTarget := Finset.card_sdiff_add_card terminal.seenTarget
    (sample.initialSeenTarget x0 p0)
  rw [Finset.union_eq_left.mpr hsubsetTarget] at hcardTarget
  have hsource_int :
      (terminal.seenSource.card : ℤ) =
        (sample.initialSeenSource x0 p0).card +
          (terminal.seenSource \ sample.initialSeenSource x0 p0).card := by
    have hcast :
        (terminal.seenSource.card : ℤ) =
          (terminal.seenSource \ sample.initialSeenSource x0 p0).card +
            (sample.initialSeenSource x0 p0).card := by
      exact_mod_cast hcardSource.symm
    omega
  have htarget_int :
      (terminal.seenTarget.card : ℤ) =
        (sample.initialSeenTarget x0 p0).card +
          (terminal.seenTarget \ sample.initialSeenTarget x0 p0).card := by
    have hcast :
        (terminal.seenTarget.card : ℤ) =
          (terminal.seenTarget \ sample.initialSeenTarget x0 p0).card +
            (sample.initialSeenTarget x0 p0).card := by
      exact_mod_cast hcardTarget.symm
    omega
  have hterminal_current : terminal.current =
      (terminal.seenSource.card : ℤ) - terminal.seenTarget.card := by
    have h := sample.feedbackState_current_eq_card_sub lam x0 p0 history.length
    rw [hstate] at h
    exact h
  simp only [safePreCurrentAt, CountingProcess.leftCurrentOfCounts,
    safeK0, hNoTie, ↓reduceIte]
  rw [hsource, htarget]
  change sample.initialFeedbackCurrent x0 p0 +
      (terminal.seenSource \ sample.initialSeenSource x0 p0).card -
      (terminal.seenTarget \ sample.initialSeenTarget x0 p0).card = terminal.current
  simp only [initialFeedbackCurrent]
  rw [hterminal_current]
  omega

theorem safePreFeedbackSlope_eq_terminal_slope
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 < x)
    {history : List (FeedbackLabel n)}
    (hbefore : HistoryBeforeCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    safePreFeedbackSlope hlam0 hlamHalf x0 p0
      ⟨x - x0, sub_nonneg.mpr hx0x.le⟩ sample =
      (sample.scheduledState lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history).slope lam := by
  have hcurrent := safePreCurrentAt_eq_terminal_current
    sample hlam0 hlamHalf hx0x hbefore
  have hcast := congrArg (fun k : ℤ ↦ feedbackSlope lam (k : ℝ)) hcurrent
  simpa [safePreFeedbackSlope, FeedbackStepState.slope] using hcast

end FiniteSample

end OTSelector
