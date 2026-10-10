import OTSelector.Feedback.FiniteHistoryAt
import OTSelector.Feedback.NoTieBranch
import OTSelector.Feedback.RevealedHistory

/-!
# Deterministic coverage of finite feedback history cells

For a no-tie finite sample, the event recursion has a finite forced history at every
deterministic coordinate.  This file contains the finite combinatorial construction and the
strict remaining-region argument; it contains no probabilistic statement.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

namespace FiniteSample

/-! ## Forced histories with only prior activity -/

/--
Construct the first `m` singleton steps when every step strictly before `m` is active.

The strict inequality in `hactive` is intentional: in the successor case the `m`-th step is
obtained from the successor hypothesis, while the induction hypothesis only needs the prior
steps.  In particular, the zero-length case never has to choose a label.
-/
theorem exists_forced_history_of_prior_active
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (hinit : sample.initialFeedbackState x0 p0 =
      forcedInitialState x0 p0 sourcePattern targetPattern)
    (m : ℕ)
    (hactive : ∀ k < m,
      ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty)
    (hprior : ∀ k < m,
      ((feedbackState sample lam x0 p0 k).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 k).newTarget sample lam).card ≤ 1) :
    ∃ history : List (FeedbackLabel n),
      history.length = m ∧
      ForcedHistoryRealizes sample lam
        (forcedInitialState x0 p0 sourcePattern targetPattern) history ∧
      feedbackState sample lam x0 p0 m =
        scheduledState sample lam x0 p0 sourcePattern targetPattern history := by
  induction m with
  | zero =>
      refine ⟨[], rfl, trivial, ?_⟩
      simpa [feedbackState_zero, scheduledState, scheduledStateFrom] using hinit
  | succ m ih =>
      have hactive' : ∀ k < m,
          ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty := by
        intro k hk
        exact hactive k (lt_trans hk (Nat.lt_succ_self m))
      have hprior' : ∀ k < m,
          ((feedbackState sample lam x0 p0 k).newSource sample lam).card +
            ((feedbackState sample lam x0 p0 k).newTarget sample lam).card ≤ 1 := by
        intro k hk
        exact hprior k (lt_trans hk (Nat.lt_succ_self m))
      obtain ⟨history, hlen, hgood, hstate⟩ := ih hactive' hprior'
      have hcount :
          ((feedbackState sample lam x0 p0 m).newSource sample lam).card +
            ((feedbackState sample lam x0 p0 m).newTarget sample lam).card = 1 := by
        have hpos := sample.new_label_count_pos_of_candidates_nonempty lam
          (feedbackState sample lam x0 p0 m) (hactive m (Nat.lt_succ_self m))
        have hup := hprior m (Nat.lt_succ_self m)
        omega
      obtain ⟨label, hlabel⟩ := sample.exists_labelStepRealizes_of_card_sum_eq_one
        lam (feedbackState sample lam x0 p0 m) hcount
      have hlabel' : labelStepRealizes sample lam
          (scheduledState sample lam x0 p0 sourcePattern targetPattern history) label := by
        rw [← hstate]
        exact hlabel
      have hgood' : ForcedHistoryRealizes sample lam
          (forcedInitialState x0 p0 sourcePattern targetPattern) (history ++ [label]) := by
        apply ForcedHistoryRealizes.append_singleton sample lam
          (forcedInitialState x0 p0 sourcePattern targetPattern) history label hgood
        simpa [scheduledState] using hlabel'
      have hstate' := feedbackState_eq_scheduledState_of_history sample lam x0 p0
        sourcePattern targetPattern (history ++ [label]) hinit hgood'
      refine ⟨history ++ [label], by simp [hlen], hgood', ?_⟩
      simpa [Nat.succ_eq_add_one, hlen] using hstate'

/-! ## The next knot after an elapsed index -/

/-- The coordinate after the elapsed index is strictly beyond the observed elapsed coordinate. -/
theorem elapsedIndex_next_knot_gt_of_val_lt
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0)
    (hm : (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val < 2 * n) :
    x0 + (t : ℝ) <
      sample.feedbackKnot lam x0 p0 ((sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val + 1) := by
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 t
  let J : Fin (2 * n + 1) := ⟨I.val + 1, by omega⟩
  by_contra hnot
  have hJ_le : sample.feedbackKnot lam x0 p0 J.val - x0 ≤ (t : ℝ) := by
    have hnot' : ¬ x0 + (t : ℝ) < sample.feedbackKnot lam x0 p0 J.val := by
      simpa [I, J] using hnot
    have hle' : sample.feedbackKnot lam x0 p0 J.val ≤ x0 + (t : ℝ) :=
      le_of_not_gt hnot'
    linarith
  have hJ_mem : J ∈ sample.elapsedIndexSet hlam0 hlamHalf x0 p0 t := by
    simp only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
    apply NNReal.coe_le_coe.mp
    simpa only [coe_elapsedFeedbackKnot] using hJ_le
  have hset_nonempty :
      (sample.elapsedIndexSet hlam0 hlamHalf x0 p0 t).Nonempty := by
    exact ⟨0, sample.zero_mem_elapsedIndexSet hlam0 hlamHalf x0 p0 t⟩
  have hle : J ≤ I := by
    exact le_maxFinsetIndex ⟨0, by omega⟩ hset_nonempty hJ_mem
  have hval : J.val ≤ I.val := hle
  dsimp [J] at hval
  omega

/-! ## Coverage at a deterministic coordinate -/

/--
Every no-tie finite recursion has a realized history cell at every coordinate to the right of
the initial knot.  The returned history is bounded by the `2 * n` label horizon.
-/
theorem exists_historyAtCoordinate_of_noFeedbackTies
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    (hNoTie : sample.NoFeedbackTies lam x0 p0) :
    ∃ history : List (FeedbackLabel n),
      HistoryAtCoordinate sample lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x ∧
      history.length ≤ 2 * n := by
  classical
  let sourcePattern := sample.initialSeenSource x0 p0
  let targetPattern := sample.initialSeenTarget x0 p0
  have hinit : sample.initialFeedbackState x0 p0 =
      forcedInitialState x0 p0 sourcePattern targetPattern := by
    simp [sourcePattern, targetPattern, initialFeedbackState, initialFeedbackCurrent,
      forcedInitialState]
  let t : ℝ≥0 := ⟨x - x0, sub_nonneg.mpr hx0x⟩
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 t
  let m := I.val
  have hm_le : m ≤ 2 * n := by
    dsimp [m, I]
    omega
  have hI_mem : I ∈ sample.elapsedIndexSet hlam0 hlamHalf x0 p0 t := by
    simpa [I] using sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
  have hI_elapsed : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 I.val ≤ t := by
    simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hI_mem
  have hI_coe :
      (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 I.val : ℝ) ≤ (t : ℝ) :=
    NNReal.coe_le_coe.mpr hI_elapsed
  have hm_knot : sample.feedbackKnot lam x0 p0 m ≤ x := by
    have hsub : sample.feedbackKnot lam x0 p0 I.val - x0 ≤ (t : ℝ) := by
      simpa only [coe_elapsedFeedbackKnot] using hI_coe
    have ht : (t : ℝ) = x - x0 := by
      rfl
    rw [ht] at hsub
    have hsub' : sample.feedbackKnot lam x0 p0 m - x0 ≤ x - x0 := by
      simpa [m] using hsub
    linarith
  have hq_exists : ∃ k, (feedbackState sample lam x0 p0 k).candidates sample lam = ∅ := by
    exact ⟨2 * n, sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0⟩
  let q := Nat.find hq_exists
  have hq_empty :
      (feedbackState sample lam x0 p0 q).candidates sample lam = ∅ :=
    Nat.find_spec hq_exists
  have hq_le : q ≤ 2 * n := by
    exact Nat.find_min' hq_exists
      (sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0)
  have hq_active : ∀ k < q,
      ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty := by
    intro k hk
    by_contra hnone
    exact (Nat.find_min hq_exists hk)
      (Finset.not_nonempty_iff_eq_empty.mp hnone)
  have hq_prior : ∀ k < q,
      ((feedbackState sample lam x0 p0 k).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 k).newTarget sample lam).card ≤ 1 := by
    intro k hk
    apply hNoTie k
    exact lt_of_lt_of_le hk hq_le
  obtain ⟨historyQ, hQlen, hQgood, hQstate⟩ :=
    sample.exists_forced_history_of_prior_active lam x0 p0 sourcePattern targetPattern
      hinit q hq_active hq_prior
  have hQbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern historyQ :=
    ⟨hinit, hQgood⟩
  by_cases hq_m : q ≤ m
  · have hqm_knot : sample.feedbackKnot lam x0 p0 q ≤
        sample.feedbackKnot lam x0 p0 m :=
      sample.feedbackState_x_mono hlam0 hlamHalf x0 p0 hq_m
    have hQtermx :
        (scheduledState sample lam x0 p0 sourcePattern targetPattern historyQ).x ≤ x := by
      rw [← hQstate]
      exact (by simpa only [feedbackKnot] using hqm_knot.trans hm_knot)
    have hQall :
        (feedbackState sample lam x0 p0 q).seenSource = Finset.univ ∧
          (feedbackState sample lam x0 p0 q).seenTarget = Finset.univ :=
      (FeedbackStepState.candidates_eq_empty_iff sample lam
        (feedbackState sample lam x0 p0 q)).mp hq_empty
    have hQremaining :
        LiesInStateRemainingAt lam
          (scheduledState sample lam x0 p0 sourcePattern targetPattern historyQ) x sample := by
      rw [← hQstate]
      constructor
      · intro i hi
        exact False.elim (hi (by rw [hQall.1]; exact Finset.mem_univ i))
      · intro j hj
        exact False.elim (hj (by rw [hQall.2]; exact Finset.mem_univ j))
    have hQat : HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern historyQ x := by
      change HistoryBranch sample lam x0 p0 sourcePattern targetPattern historyQ ∧
        (scheduledState sample lam x0 p0 sourcePattern targetPattern historyQ).x ≤ x ∧
          LiesInStateRemainingAt lam
            (scheduledState sample lam x0 p0 sourcePattern targetPattern historyQ) x sample
      exact ⟨hQbranch, hQtermx, hQremaining⟩
    refine ⟨historyQ, ?_, ?_⟩
    · simpa [sourcePattern, targetPattern] using hQat
    · exact hQgood.length_le_two_mul
  · have hm_q : m < q := Nat.lt_of_not_ge hq_m
    have hm_active : ∀ k < m,
        ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty := by
      intro k hk
      exact hq_active k (lt_trans hk hm_q)
    have hm_prior : ∀ k < m,
        ((feedbackState sample lam x0 p0 k).newSource sample lam).card +
          ((feedbackState sample lam x0 p0 k).newTarget sample lam).card ≤ 1 := by
      intro k hk
      apply hNoTie k
      exact lt_of_lt_of_le (lt_trans hk hm_q) hq_le
    obtain ⟨historyM, hMlen, hMgood, hMstate⟩ :=
      sample.exists_forced_history_of_prior_active lam x0 p0 sourcePattern targetPattern
        hinit m hm_active hm_prior
    have hMbranch : HistoryBranch sample lam x0 p0 sourcePattern targetPattern historyM :=
      ⟨hinit, hMgood⟩
    have hm_lt_horizon : m < 2 * n := lt_of_lt_of_le hm_q hq_le
    have hnext0 := sample.elapsedIndex_next_knot_gt_of_val_lt hlam0 hlamHalf x0 p0 t (by
      simpa [m, I] using hm_lt_horizon)
    have hnext : x < sample.feedbackKnot lam x0 p0 (m + 1) := by
      have hnext' : x0 + (t : ℝ) < sample.feedbackKnot lam x0 p0 (m + 1) := by
        simpa [m, I] using hnext0
      change x0 + (x - x0) < sample.feedbackKnot lam x0 p0 (m + 1) at hnext'
      linarith
    have hMtermx :
        (scheduledState sample lam x0 p0 sourcePattern targetPattern historyM).x ≤ x := by
      rw [← hMstate]
      simpa only [feedbackKnot] using hm_knot
    have hMremaining :
        LiesInStateRemainingAt lam
          (scheduledState sample lam x0 p0 sourcePattern targetPattern historyM) x sample := by
      rw [← hMstate]
      constructor
      · intro i hi
        have hcoord_mem :
            (feedbackState sample lam x0 p0 m).sourceCoordinate sample lam i ∈
              (feedbackState sample lam x0 p0 m).candidates sample lam := by
          rw [FeedbackStepState.candidates]
          simp only [Finset.mem_union]
          left
          exact Finset.mem_image.mpr ⟨i,
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
        have hmin :
            (feedbackState sample lam x0 p0 m).nextCoordinate sample lam ≤
              (feedbackState sample lam x0 p0 m).sourceCoordinate sample lam i := by
          rw [FeedbackStepState.nextCoordinate, dite_eq_left (hq_active m hm_q)]
          exact Finset.min'_le _ _ hcoord_mem
        have hstep :
            sample.feedbackKnot lam x0 p0 (m + 1) =
              (feedbackState sample lam x0 p0 m).nextCoordinate sample lam := by
          simp only [feedbackKnot, feedbackState_succ, FeedbackStepState.step]
        have hcross : x <
            (feedbackState sample lam x0 p0 m).sourceCoordinate sample lam i := by
          rw [hstep] at hnext
          exact hnext.trans_le hmin
        have hcross' : x < sourceSegmentCrossing
            (feedbackState sample lam x0 p0 m).x
            (feedbackState sample lam x0 p0 m).p
            ((feedbackState sample lam x0 p0 m).slope lam)
            ((n : ℝ) * (sample.sourceHeight i : ℝ)) (sample.sourceSlope i) := by
          simpa only [FeedbackStepState.sourceCoordinate] using hcross
        have ha := sample.sourceSlope_mem i
        have hphase := (x_lt_sourceSegmentCrossing_iff ha.1 ha.2
          (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).1 hcross'
        simpa [sourceRawRemainingSetAt, sourceRawRemainingSet, FiniteSample.sourcePoint,
          FiniteSample.sourceSlope, FeedbackStepState.slope, mul_comm] using hphase
      · intro j hj
        have hcoord_mem :
            (feedbackState sample lam x0 p0 m).targetCoordinate sample lam j ∈
              (feedbackState sample lam x0 p0 m).candidates sample lam := by
          rw [FeedbackStepState.candidates]
          simp only [Finset.mem_union]
          right
          exact Finset.mem_image.mpr ⟨j,
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩
        have hmin :
            (feedbackState sample lam x0 p0 m).nextCoordinate sample lam ≤
              (feedbackState sample lam x0 p0 m).targetCoordinate sample lam j := by
          rw [FeedbackStepState.nextCoordinate, dite_eq_left (hq_active m hm_q)]
          exact Finset.min'_le _ _ hcoord_mem
        have hstep :
            sample.feedbackKnot lam x0 p0 (m + 1) =
              (feedbackState sample lam x0 p0 m).nextCoordinate sample lam := by
          simp only [feedbackKnot, feedbackState_succ, FeedbackStepState.step]
        have hcross : x <
            (feedbackState sample lam x0 p0 m).targetCoordinate sample lam j := by
          rw [hstep] at hnext
          exact hnext.trans_le hmin
        have hcross' : x < targetSegmentCrossing
            (feedbackState sample lam x0 p0 m).x
            (feedbackState sample lam x0 p0 m).p
            ((feedbackState sample lam x0 p0 m).slope lam)
            ((n : ℝ) * (sample.targetHeight j : ℝ)) (sample.targetSlope j) := by
          simpa only [FeedbackStepState.targetCoordinate] using hcross
        have hb := sample.targetSlope_mem j
        have hphase := (x_lt_targetSegmentCrossing_iff hb.1 hb.2
          (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).1 hcross'
        simpa [targetRawRemainingSetAt, targetRawRemainingSet, FiniteSample.targetPoint,
          FiniteSample.targetSlope, FeedbackStepState.slope, mul_comm] using hphase
    have hMat : HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern historyM x := by
      change HistoryBranch sample lam x0 p0 sourcePattern targetPattern historyM ∧
        (scheduledState sample lam x0 p0 sourcePattern targetPattern historyM).x ≤ x ∧
          LiesInStateRemainingAt lam
            (scheduledState sample lam x0 p0 sourcePattern targetPattern historyM) x sample
      exact ⟨hMbranch, hMtermx, hMremaining⟩
    refine ⟨historyM, ?_, ?_⟩
    · simpa [sourcePattern, targetPattern] using hMat
    · exact hMgood.length_le_two_mul

/-! ## The elapsed state represented by a covered cell -/

namespace HistoryAtCoordinate

/-- A covered coordinate cell carries the same state as the elapsed recursive snapshot. -/
theorem feedbackStateAtElapsed_eq_scheduledState
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    (history : List (FeedbackLabel n))
    (hcell : HistoryAtCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x⟩ =
      sample.scheduledState lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history := by
  classical
  let sourcePattern := sample.initialSeenSource x0 p0
  let targetPattern := sample.initialSeenTarget x0 p0
  let t : ℝ≥0 := ⟨x - x0, sub_nonneg.mpr hx0x⟩
  have hcell' : HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history x := by
    simpa [sourcePattern, targetPattern] using hcell
  change HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      (scheduledState sample lam x0 p0 sourcePattern targetPattern history).x ≤ x ∧
        LiesInStateRemainingAt lam
          (scheduledState sample lam x0 p0 sourcePattern targetPattern history) x sample at hcell'
  have hbranch := hcell'.1
  have hstate : feedbackState sample lam x0 p0 history.length =
      scheduledState sample lam x0 p0 sourcePattern targetPattern history :=
    feedbackState_eq_scheduledState_of_history sample lam x0 p0
      sourcePattern targetPattern history hbranch.1 hbranch.2
  have hlen_le : history.length ≤ 2 * n := hbranch.2.length_le_two_mul
  have hleft_real : sample.feedbackKnot lam x0 p0 history.length - x0 ≤ (t : ℝ) := by
    have hterm : sample.feedbackKnot lam x0 p0 history.length ≤ x := by
      rw [feedbackKnot, hstate]
      exact hcell'.2.1
    have ht : (t : ℝ) = x - x0 := by rfl
    rw [ht]
    linarith
  have hleft : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 history.length ≤ t := by
    apply NNReal.coe_le_coe.mp
    simpa only [coe_elapsedFeedbackKnot] using hleft_real
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 t
  have hI_mem : I ∈ sample.elapsedIndexSet hlam0 hlamHalf x0 p0 t := by
    simpa [I] using sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
  have hI_ge : history.length ≤ I.val := by
    let J : Fin (2 * n + 1) := ⟨history.length, by omega⟩
    have hJ_mem : J ∈ sample.elapsedIndexSet hlam0 hlamHalf x0 p0 t := by
      simp only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [J] using hleft
    have hset_nonempty :
        (sample.elapsedIndexSet hlam0 hlamHalf x0 p0 t).Nonempty := by
      exact ⟨0, sample.zero_mem_elapsedIndexSet hlam0 hlamHalf x0 p0 t⟩
    have hle : J ≤ I := le_maxFinsetIndex ⟨0, by omega⟩ hset_nonempty hJ_mem
    exact hle
  by_cases hcand :
      ((feedbackState sample lam x0 p0 history.length).candidates sample lam).Nonempty
  · have hlen_lt : history.length < 2 * n := by
      exact lt_of_not_ge (fun hEq => by
        have hall :
            (feedbackState sample lam x0 p0 history.length).seenSource = Finset.univ ∧
              (feedbackState sample lam x0 p0 history.length).seenTarget = Finset.univ := by
          have hdone := sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0
          have hstable := sample.feedbackState_stable_after_two_mul lam x0 p0
            (history.length - 2 * n)
          have hstate_done :
              feedbackState sample lam x0 p0 (2 * n) =
                feedbackState sample lam x0 p0 history.length := by
            rw [← hstable]
            simp [hEq]
          rw [← hstate_done]
          exact (FeedbackStepState.candidates_eq_empty_iff sample lam _).mp hdone
        exact hcand.ne_empty ((FeedbackStepState.candidates_eq_empty_iff sample lam _).mpr hall)
        )
    have hremainingR :
        LiesInStateRemainingAt lam
          (feedbackState sample lam x0 p0 history.length) x sample := by
      rw [hstate]
      exact hcell'.2.2
    have hsource_gt : ∀ i, i ∉
        (feedbackState sample lam x0 p0 history.length).seenSource →
          x < (feedbackState sample lam x0 p0 history.length).sourceCoordinate sample lam i := by
      intro i hi
      have hi_mem := hremainingR.1 i hi
      have hi_line : x <
          (n : ℝ) * (sample.sourceHeight i : ℝ) +
            sample.sourceSlope i *
              segmentCurve
                (feedbackState sample lam x0 p0 history.length).x
                (feedbackState sample lam x0 p0 history.length).p
                ((feedbackState sample lam x0 p0 history.length).slope lam) x := by
        rw [hstate] at hi
        simpa [sourceRawRemainingSetAt, sourceRawRemainingSet, FiniteSample.sourcePoint,
          FiniteSample.sourceSlope, FeedbackStepState.slope, mul_comm] using hi_mem
      have ha := sample.sourceSlope_mem i
      have hcross := (x_lt_sourceSegmentCrossing_iff ha.1 ha.2
        (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2 hi_line
      simpa only [FeedbackStepState.sourceCoordinate, FeedbackStepState.slope] using hcross
    have htarget_gt : ∀ j, j ∉
        (feedbackState sample lam x0 p0 history.length).seenTarget →
          x < (feedbackState sample lam x0 p0 history.length).targetCoordinate sample lam j := by
      intro j hj
      have hj_mem := hremainingR.2 j hj
      have hj_line : x <
          (n : ℝ) * (sample.targetHeight j : ℝ) -
            sample.targetSlope j *
              segmentCurve
                (feedbackState sample lam x0 p0 history.length).x
                (feedbackState sample lam x0 p0 history.length).p
                ((feedbackState sample lam x0 p0 history.length).slope lam) x := by
        rw [hstate] at hj
        simpa [targetRawRemainingSetAt, targetRawRemainingSet, FiniteSample.targetPoint,
          FiniteSample.targetSlope, FeedbackStepState.slope, mul_comm] using hj_mem
      have hb := sample.targetSlope_mem j
      have hcross := (x_lt_targetSegmentCrossing_iff hb.1 hb.2
        (abs_feedbackSlope_le hlam0) hlam0 hlamHalf).2 hj_line
      simpa only [FeedbackStepState.targetCoordinate, FeedbackStepState.slope] using hcross
    have hnext_gt : x <
        (feedbackState sample lam x0 p0 history.length).nextCoordinate sample lam := by
      have hnext_mem := (feedbackState sample lam x0 p0 history.length).nextCoordinate_mem_candidates
        sample lam hcand
      rw [FeedbackStepState.candidates] at hnext_mem
      simp only [Finset.mem_union] at hnext_mem
      rcases hnext_mem with hsource | htarget
      · rw [FeedbackStepState.sourceCandidates] at hsource
        obtain ⟨i, hi, hcoord⟩ := Finset.mem_image.mp hsource
        exact hcoord ▸ hsource_gt i (Finset.mem_sdiff.mp hi).2
      · rw [FeedbackStepState.targetCandidates] at htarget
        obtain ⟨j, hj, hcoord⟩ := Finset.mem_image.mp htarget
        exact hcoord ▸ htarget_gt j (Finset.mem_sdiff.mp hj).2
    have hstep : sample.feedbackKnot lam x0 p0 (history.length + 1) =
        (feedbackState sample lam x0 p0 history.length).nextCoordinate sample lam := by
      simp only [feedbackKnot, feedbackState_succ, FeedbackStepState.step]
    have hright_real : (t : ℝ) <
        sample.feedbackKnot lam x0 p0 (history.length + 1) - x0 := by
      have hterm : x < sample.feedbackKnot lam x0 p0 (history.length + 1) := by
        rw [hstep]
        exact hnext_gt
      have ht : (t : ℝ) = x - x0 := by rfl
      rw [ht]
      linarith
    have hright : t <
        sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (history.length + 1) := by
      apply NNReal.coe_lt_coe.mp
      simpa only [coe_elapsedFeedbackKnot] using hright_real
    have hidx := sample.elapsedIndex_eq_of_mem_interval hlam0 hlamHalf x0 p0
      hlen_lt hleft hright
    have hidx' : I.val = history.length := by
      simpa [I] using hidx
    have hfinal : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t =
        sample.scheduledState lam x0 p0 sourcePattern targetPattern history := by
      rw [feedbackStateAtElapsed]
      have hidx'' :
          (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val = history.length := by
        simpa [I] using hidx'
      rw [hidx'']
      exact hstate
    simpa [t, sourcePattern, targetPattern] using hfinal
  · have hstate_idx :
        feedbackState sample lam x0 p0 I.val =
          feedbackState sample lam x0 p0 history.length := by
      have hcand_empty :
          (feedbackState sample lam x0 p0 history.length).candidates sample lam = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hcand
      have hstable := sample.feedbackState_eq_of_candidates_eq_empty lam x0 p0
        history.length hcand_empty (I.val - history.length)
      simpa [Nat.add_sub_of_le hI_ge] using hstable
    have hfinal : sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t =
        sample.scheduledState lam x0 p0 sourcePattern targetPattern history := by
      rw [feedbackStateAtElapsed]
      have hstate_idx' :
          feedbackState sample lam x0 p0
              (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val =
            feedbackState sample lam x0 p0 history.length := by
        simpa [I] using hstate_idx
      rw [hstate_idx', hstate]
    simpa [t, sourcePattern, targetPattern] using hfinal

end HistoryAtCoordinate

end FiniteSample

namespace HistoryAtCoordinate

/-- Root-namespace entry point for the elapsed-state bridge. -/
theorem feedbackStateAtElapsed_eq_scheduledState
    (sample : FiniteSample n) {lam x0 p0 x : ℝ}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2) (hx0x : x0 ≤ x)
    (history : List (FeedbackLabel n))
    (hcell : HistoryAtCoordinate sample lam x0 p0
      (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history x) :
    sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0
        ⟨x - x0, sub_nonneg.mpr hx0x⟩ =
      sample.scheduledState lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history := by
  exact FiniteSample.HistoryAtCoordinate.feedbackStateAtElapsed_eq_scheduledState
    sample hlam0 hlamHalf hx0x history hcell

end HistoryAtCoordinate

end OTSelector
