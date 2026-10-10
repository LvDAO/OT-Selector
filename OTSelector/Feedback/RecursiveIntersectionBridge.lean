import OTSelector.Feedback.FeedbackCurve
import OTSelector.Feedback.CrossingCounts

/-!
# Recursive feedback knots and global intersection coordinates

This file is the deterministic bridge between the event recursion and the unique global
intersections of the feedback graph.  It does not use a no-tie hypothesis: simultaneous labels are
absorbed by the `newSource`/`newTarget` filters at one knot.
-/

open Set

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-! ## The recursive curve on one interval -/

@[simp] theorem feedbackCurve_at_x0
    {lam : ℝ} (_hlam0 : 0 ≤ lam) (_hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    feedbackCurve sample lam x0 p0 x0 = p0 := by
  simp [feedbackCurve]

theorem feedbackCurveAux_eq_segment_on_interval
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n) {x : ℝ}
    (hleft : feedbackKnot sample lam x0 p0 m < x)
    (hright : x ≤ feedbackKnot sample lam x0 p0 (m + 1)) :
    feedbackCurve sample lam x0 p0 x =
      segmentCurve (feedbackKnot sample lam x0 p0 m)
        (feedbackKnotValue sample lam x0 p0 m)
        ((feedbackState sample lam x0 p0 m).slope lam) x := by
  have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
  have hskip : ∀ r ≤ m,
      feedbackCurveAux sample lam x0 p0 (2 * n) 0 x =
        feedbackCurveAux sample lam x0 p0 (2 * n) r x := by
    intro r hr
    induction r with
    | zero => rfl
    | succ r ihr =>
        have hrs : r + 1 ≤ m := by omega
        have hk : feedbackKnot sample lam x0 p0 (r + 1) ≤
            feedbackKnot sample lam x0 p0 m :=
          hmono (by omega)
        have hxnext :
            ¬x ≤ feedbackKnot sample lam x0 p0 (r + 1) := by
          exact not_le_of_gt (lt_of_le_of_lt hk hleft)
        calc
          feedbackCurveAux sample lam x0 p0 (2 * n) 0 x =
          feedbackCurveAux sample lam x0 p0 (2 * n) r x := ihr (by omega)
          _ = feedbackCurveAux sample lam x0 p0 (2 * n) (r + 1) x := by
            rw [feedbackCurveAux, dite_eq_left (by omega), ite_eq_right hxnext]
  have hx0 : x0 < x := by
    have hk0 : feedbackKnot sample lam x0 p0 0 ≤
        feedbackKnot sample lam x0 p0 m := hmono (Nat.zero_le m)
    simpa only [feedbackKnot_zero] using lt_of_le_of_lt hk0 hleft
  rw [feedbackCurve, ite_eq_right (not_le_of_gt hx0), hskip m (le_rfl)]
  rw [feedbackCurveAux, dite_eq_left hm, ite_eq_left hright]

theorem feedbackCurve_eq_feedbackKnotValue_at_knot
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m ≤ 2 * n) :
    feedbackCurve sample lam x0 p0 (feedbackKnot sample lam x0 p0 m) =
      feedbackKnotValue sample lam x0 p0 m := by
  induction m with
  | zero => exact sample.feedbackCurve_at_x0 hlam0 hlamHalf x0 p0
  | succ m ih =>
      have hmH : m ≤ 2 * n := by omega
      have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
      have hkm : feedbackKnot sample lam x0 p0 m ≤
          feedbackKnot sample lam x0 p0 (m + 1) :=
        hmono (Nat.le_succ m)
      by_cases hstrict : feedbackKnot sample lam x0 p0 m <
          feedbackKnot sample lam x0 p0 (m + 1)
      · have hseg := sample.feedbackCurveAux_eq_segment_on_interval
          hlam0 hlamHalf x0 p0 (by omega) hstrict le_rfl
        rw [hseg, sample.feedbackKnot_value_consistency]
      · have heq : feedbackKnot sample lam x0 p0 (m + 1) =
            feedbackKnot sample lam x0 p0 m := le_antisymm
          (le_of_not_gt hstrict) hkm
        rw [heq]
        have hp : feedbackKnotValue sample lam x0 p0 (m + 1) =
            feedbackKnotValue sample lam x0 p0 m := by
          rw [sample.feedbackKnotValue_succ]
          simp [heq, segmentCurve]
        rw [hp]
        exact ih hmH

theorem feedbackCurve_eq_segment_on_closed_interval
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n) {x : ℝ}
    (hleft : feedbackKnot sample lam x0 p0 m ≤ x)
    (hright : x ≤ feedbackKnot sample lam x0 p0 (m + 1)) :
    feedbackCurve sample lam x0 p0 x =
      segmentCurve (feedbackKnot sample lam x0 p0 m)
        (feedbackKnotValue sample lam x0 p0 m)
        ((feedbackState sample lam x0 p0 m).slope lam) x := by
  by_cases heq : x = feedbackKnot sample lam x0 p0 m
  · subst x
    rw [sample.feedbackCurve_eq_feedbackKnotValue_at_knot hlam0 hlamHalf x0 p0
      (le_of_lt hm)]
    simp [segmentCurve]
  · exact sample.feedbackCurveAux_eq_segment_on_interval hlam0 hlamHalf x0 p0 hm
      (lt_of_le_of_ne hleft (Ne.symm heq)) hright

/-! ## Initial filters and one-step event membership -/

theorem initialSeenSource_eq_sourceIntersection_filter
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    sample.initialSeenSource x0 p0 =
      Finset.univ.filter fun i ↦
        sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤ x0 := by
  classical
  ext i
  simp only [initialSeenSource, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [sourceIntersection_le_iff]
  have hg : (sample.feedbackGraph hlam0 hlamHalf x0 p0).curve x0 = p0 := by
    change feedbackCurve sample lam x0 p0 x0 = p0
    exact sample.feedbackCurve_at_x0 hlam0 hlamHalf x0 p0
  simp [sourcePhase, hg]

theorem initialSeenTarget_eq_targetIntersection_filter
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    sample.initialSeenTarget x0 p0 =
      Finset.univ.filter fun j ↦
        sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j ≤ x0 := by
  classical
  ext j
  simp only [initialSeenTarget, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [targetIntersection_le_iff]
  have hg : (sample.feedbackGraph hlam0 hlamHalf x0 p0).curve x0 = p0 := by
    change feedbackCurve sample lam x0 p0 x0 = p0
    exact sample.feedbackCurve_at_x0 hlam0 hlamHalf x0 p0
  simp [targetPhase, hg]

theorem sourceIntersection_le_iff_mem_newSource_of_seen_filter
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n)
    (hseen : (feedbackState sample lam x0 p0 m).seenSource =
      Finset.univ.filter fun i ↦
        sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤
          feedbackKnot sample lam x0 p0 m)
    (i : Fin n) :
    i ∉ (feedbackState sample lam x0 p0 m).seenSource →
      (sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤
          feedbackKnot sample lam x0 p0 (m + 1) ↔
        i ∈ (feedbackState sample lam x0 p0 m).newSource sample lam) := by
  intro hi
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let state := feedbackState sample lam x0 p0 m
  let k := feedbackKnot sample lam x0 p0 m
  let k' := feedbackKnot sample lam x0 p0 (m + 1)
  have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
  have hk : k ≤ k' := hmono (Nat.le_succ m)
  have hi_gt : k < sample.sourceIntersection graph i := by
    have hnot : ¬ sample.sourceIntersection graph i ≤ k := by
      intro hle
      have hle' : sample.sourceIntersection graph i ≤ k := by
        simpa [graph, k] using hle
      apply hi
      rw [hseen]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle'⟩
    exact lt_of_not_ge hnot
  by_cases hcand : (state.candidates sample lam).Nonempty
  ·
    constructor
    · intro hinter
      have hxi : sample.sourceIntersection graph i ≤ k' := hinter
      have hcurve : feedbackCurve sample lam x0 p0
          (sample.sourceIntersection graph i) =
          segmentCurve k (feedbackKnotValue sample lam x0 p0 m)
            (state.slope lam) (sample.sourceIntersection graph i) := by
        apply sample.feedbackCurve_eq_segment_on_closed_interval
          hlam0 hlamHalf x0 p0 hm
        · exact hi_gt.le
        · exact hxi
      have hspec := sample.sourceIntersection_spec graph i
      have hphase : sample.sourcePhase i
          (segmentCurve k (feedbackKnotValue sample lam x0 p0 m)
            (state.slope lam) (sample.sourceIntersection graph i)) =
          sample.sourceIntersection graph i := by
        rw [← hcurve]
        exact hspec
      have hcross : sample.sourceIntersection graph i =
          state.sourceCoordinate sample lam i := by
        apply sourceSegmentCrossing_unique
          (sample.sourceSlope_mem i).1 (sample.sourceSlope_mem i).2
          (by simpa [FeedbackStepState.slope] using
            (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
          hlam0 hlamHalf
        simpa [FeedbackStepState.sourceCoordinate, sourcePhase, k, state,
          feedbackKnot, feedbackKnotValue] using hphase
      have hcoord : state.sourceCoordinate sample lam i = k' := by
        rw [← hcross]
        have hle : sample.sourceIntersection graph i ≤ k' := hinter
        have hnew : sample.sourceIntersection graph i = k' := by
          have hnotle : ¬ sample.sourceIntersection graph i < k' := by
            intro hlt
            have hlt' : sample.sourceIntersection graph i < k' := hlt
            have hcoord' : sample.sourceIntersection graph i =
                state.sourceCoordinate sample lam i := hcross
            have hcandidate : state.sourceCoordinate sample lam i ∈
                state.candidates sample lam := by
              change state.sourceCoordinate sample lam i ∈
                state.sourceCandidates sample lam ∪ state.targetCandidates sample lam
              exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,
                Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
            have hnextle0 : state.nextCoordinate sample lam ≤
                state.sourceCoordinate sample lam i := by
              rw [FeedbackStepState.nextCoordinate, dite_eq_left hcand]
              exact Finset.min'_le _ _ hcandidate
            have hnextle : k' ≤ state.sourceCoordinate sample lam i := by
              simpa [k', state, feedbackKnot, feedbackState_succ,
                FeedbackStepState.step] using hnextle0
            rw [← hcoord'] at hnextle
            exact (not_lt_of_ge hnextle) hlt'
          exact le_antisymm hle (le_of_not_gt hnotle)
        exact hnew
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩,
        hcoord⟩
    · intro hnew
      have hcoord : state.sourceCoordinate sample lam i = k' :=
        (Finset.mem_filter.mp hnew).2
      have hintersect : sample.sourcePhase i
          (feedbackCurve sample lam x0 p0 k') = k' := by
        dsimp [k']
        rw [sample.feedbackCurve_eq_segment_on_closed_interval hlam0 hlamHalf
          x0 p0 (m := m) (x := feedbackKnot sample lam x0 p0 (m + 1)) hm
          (sample.feedbackState_x_mono hlam0 hlamHalf x0 p0 (Nat.le_succ m)) le_rfl]
        have hcross := sourceSegmentCrossing_intersects
          (x0 := state.x) (p0 := state.p) (q := state.slope lam)
          (t := (n : ℝ) * (sample.sourceHeight i : ℝ))
          (a := sample.sourceSlope i)
          (sample.sourceSlope_mem i).1 (sample.sourceSlope_mem i).2
          (by simpa [FeedbackStepState.slope] using
            (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
          hlam0 hlamHalf
        have hcross' : sample.sourcePhase i
            (segmentCurve state.x state.p (state.slope lam) k') = k' := by
          rw [← hcoord]
          simpa [FeedbackStepState.sourceCoordinate, sourcePhase] using hcross
        have hkx : k' = (feedbackState sample lam x0 p0 (m + 1)).x := rfl
        rw [hkx] at hcross'
        exact hcross'
      have huniq := sample.sourceIntersection_unique graph i
        (x := k') (by simpa [graph] using hintersect)
      have hle : sample.sourceIntersection graph i ≤ k' := huniq.symm.le
      have hk' : k' = feedbackKnot sample lam x0 p0 (m + 1) := rfl
      rw [hk'] at hle
      simpa [graph] using hle
  · have hzero : state.candidates sample lam = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcand
    have hkeq : k' = k := by
      unfold k' k feedbackKnot
      rw [feedbackState_succ]
      exact congrArg FeedbackStepState.x
        (FeedbackStepState.step_eq_of_candidates_eq_empty sample lam state hzero)
    constructor
    · intro hinter
      have hinter' : sample.sourceIntersection graph i ≤ k' := by
        simpa [graph, k'] using hinter
      rw [hkeq] at hinter'
      have hle : sample.sourceIntersection graph i ≤ k := by
        simpa [k] using hinter'
      exact (False.elim ((not_lt_of_ge hle) hi_gt))
    · intro hnew
      have hzero' : state.newSource sample lam = ∅ := by
        rw [FeedbackStepState.newSource]
        have hall := (FeedbackStepState.candidates_eq_empty_iff sample lam state).mp hzero
        simp [hall.1]
      rw [hzero'] at hnew
      nomatch hnew

theorem targetIntersection_le_iff_mem_newTarget_of_seen_filter
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n)
    (hseen : (feedbackState sample lam x0 p0 m).seenTarget =
      Finset.univ.filter fun j ↦
        sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j ≤
          feedbackKnot sample lam x0 p0 m)
    (j : Fin n) :
    j ∉ (feedbackState sample lam x0 p0 m).seenTarget →
      (sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j ≤
          feedbackKnot sample lam x0 p0 (m + 1) ↔
        j ∈ (feedbackState sample lam x0 p0 m).newTarget sample lam) := by
  intro hj
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let state := feedbackState sample lam x0 p0 m
  let k := feedbackKnot sample lam x0 p0 m
  let k' := feedbackKnot sample lam x0 p0 (m + 1)
  have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
  have hk : k ≤ k' := hmono (Nat.le_succ m)
  have hj_gt : k < sample.targetIntersection graph j := by
    have hnot : ¬ sample.targetIntersection graph j ≤ k := by
      intro hle
      have hle' : sample.targetIntersection graph j ≤ k := by
        simpa [graph, k] using hle
      apply hj
      rw [hseen]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle'⟩
    exact lt_of_not_ge hnot
  by_cases hcand : (state.candidates sample lam).Nonempty
  ·
    constructor
    · intro hinter
      have hcurve : feedbackCurve sample lam x0 p0
          (sample.targetIntersection graph j) =
          segmentCurve k (feedbackKnotValue sample lam x0 p0 m)
            (state.slope lam) (sample.targetIntersection graph j) := by
        apply sample.feedbackCurve_eq_segment_on_closed_interval
          hlam0 hlamHalf x0 p0 hm
        · exact hj_gt.le
        · exact hinter
      have hspec := sample.targetIntersection_spec graph j
      have hphase : sample.targetPhase j
          (segmentCurve k (feedbackKnotValue sample lam x0 p0 m)
            (state.slope lam) (sample.targetIntersection graph j)) =
          sample.targetIntersection graph j := by
        rw [← hcurve]
        exact hspec
      have hcross : sample.targetIntersection graph j =
          state.targetCoordinate sample lam j := by
        apply targetSegmentCrossing_unique
          (sample.targetSlope_mem j).1 (sample.targetSlope_mem j).2
          (by simpa [FeedbackStepState.slope] using
            (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
          hlam0 hlamHalf
        simpa [FeedbackStepState.targetCoordinate, targetPhase, k, state,
          feedbackKnot, feedbackKnotValue] using hphase
      have hcoord : state.targetCoordinate sample lam j = k' := by
        rw [← hcross]
        have hnotlt : ¬ sample.targetIntersection graph j < k' := by
          intro hlt
          have hcandidate : state.targetCoordinate sample lam j ∈
              state.candidates sample lam := by
            change state.targetCoordinate sample lam j ∈
              state.sourceCandidates sample lam ∪ state.targetCandidates sample lam
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩)
          have hnextle0 : state.nextCoordinate sample lam ≤
              state.targetCoordinate sample lam j := by
            rw [FeedbackStepState.nextCoordinate, dite_eq_left hcand]
            exact Finset.min'_le _ _ hcandidate
          have hnextle : k' ≤ state.targetCoordinate sample lam j := by
            simpa [k', state, feedbackKnot, feedbackState_succ,
              FeedbackStepState.step] using hnextle0
          rw [← hcross] at hnextle
          exact (not_lt_of_ge hnextle) hlt
        exact le_antisymm hinter (le_of_not_gt hnotlt)
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩,
        hcoord⟩
    · intro hnew
      have hcoord : state.targetCoordinate sample lam j = k' :=
        (Finset.mem_filter.mp hnew).2
      have hintersect : sample.targetPhase j
          (feedbackCurve sample lam x0 p0 k') = k' := by
        dsimp [k']
        rw [sample.feedbackCurve_eq_segment_on_closed_interval hlam0 hlamHalf
          x0 p0 (m := m) (x := feedbackKnot sample lam x0 p0 (m + 1)) hm
          (sample.feedbackState_x_mono hlam0 hlamHalf x0 p0 (Nat.le_succ m)) le_rfl]
        have hcross := targetSegmentCrossing_intersects
          (x0 := state.x) (p0 := state.p) (q := state.slope lam)
          (s := (n : ℝ) * (sample.targetHeight j : ℝ))
          (b := sample.targetSlope j)
          (sample.targetSlope_mem j).1 (sample.targetSlope_mem j).2
          (by simpa [FeedbackStepState.slope] using
            (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
          hlam0 hlamHalf
        have hcross' : sample.targetPhase j
            (segmentCurve state.x state.p (state.slope lam) k') = k' := by
          rw [← hcoord]
          simpa [FeedbackStepState.targetCoordinate, targetPhase] using hcross
        have hkx : k' = (feedbackState sample lam x0 p0 (m + 1)).x := rfl
        rw [hkx] at hcross'
        exact hcross'
      have huniq := sample.targetIntersection_unique graph j
        (x := k') (by simpa [graph] using hintersect)
      have hle : sample.targetIntersection graph j ≤ k' := huniq.symm.le
      have hk' : k' = feedbackKnot sample lam x0 p0 (m + 1) := rfl
      rw [hk'] at hle
      simpa [graph] using hle
  · have hzero : state.candidates sample lam = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcand
    have hkeq : k' = k := by
      unfold k' k feedbackKnot
      rw [feedbackState_succ]
      exact congrArg FeedbackStepState.x
        (FeedbackStepState.step_eq_of_candidates_eq_empty sample lam state hzero)
    constructor
    · intro hinter
      have hinter' : sample.targetIntersection graph j ≤ k' := by
        simpa [graph, k'] using hinter
      rw [hkeq] at hinter'
      have hle : sample.targetIntersection graph j ≤ k := by
        simpa [k] using hinter'
      exact (False.elim ((not_lt_of_ge hle) hj_gt))
    · intro hnew
      have hzero' : state.newTarget sample lam = ∅ := by
        rw [FeedbackStepState.newTarget]
        have hall := (FeedbackStepState.candidates_eq_empty_iff sample lam state).mp hzero
        simp [hall.2]
      rw [hzero'] at hnew
      nomatch hnew

theorem mem_newSource_iff_unseen_and_sourceIntersection_eq_next
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n)
    (hseen : (feedbackState sample lam x0 p0 m).seenSource =
      Finset.univ.filter fun i ↦
        sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤
          feedbackKnot sample lam x0 p0 m)
    (i : Fin n) :
    i ∈ (feedbackState sample lam x0 p0 m).newSource sample lam ↔
      i ∉ (feedbackState sample lam x0 p0 m).seenSource ∧
        sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i =
          feedbackKnot sample lam x0 p0 (m + 1) := by
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let state := feedbackState sample lam x0 p0 m
  have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
  constructor
  · intro hnew
    have hnew' : i ∈ (Finset.univ \ state.seenSource).filter
        (fun k ↦ state.sourceCoordinate sample lam k = state.nextCoordinate sample lam) := by
      simpa only [FeedbackStepState.newSource] using hnew
    have hi : i ∉ state.seenSource :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hnew').1).2
    have hcoord : state.sourceCoordinate sample lam i =
        feedbackKnot sample lam x0 p0 (m + 1) := by
      have hnext : state.nextCoordinate sample lam =
          feedbackKnot sample lam x0 p0 (m + 1) := by
        rfl
      rw [← hnext]
      exact (Finset.mem_filter.mp hnew').2
    have hcross := sourceSegmentCrossing_intersects
      (x0 := state.x) (p0 := state.p) (q := state.slope lam)
      (t := (n : ℝ) * (sample.sourceHeight i : ℝ))
      (a := sample.sourceSlope i)
      (sample.sourceSlope_mem i).1 (sample.sourceSlope_mem i).2
      (by simpa [FeedbackStepState.slope] using
        (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
      hlam0 hlamHalf
    have hcross' : sample.sourcePhase i
        (segmentCurve state.x state.p (state.slope lam)
          (feedbackKnot sample lam x0 p0 (m + 1))) =
        feedbackKnot sample lam x0 p0 (m + 1) := by
      rw [← hcoord]
      simpa [FeedbackStepState.sourceCoordinate, sourcePhase] using hcross
    have hintersect : sample.sourcePhase i
        (feedbackCurve sample lam x0 p0
          (feedbackKnot sample lam x0 p0 (m + 1))) =
        feedbackKnot sample lam x0 p0 (m + 1) := by
      rw [sample.feedbackCurve_eq_segment_on_closed_interval hlam0 hlamHalf
        x0 p0 (m := m) (x := feedbackKnot sample lam x0 p0 (m + 1)) hm
        (hmono (Nat.le_succ m)) le_rfl]
      simpa [state, feedbackKnot, feedbackKnotValue] using hcross'
    have huniq := sample.sourceIntersection_unique graph i
      (x := feedbackKnot sample lam x0 p0 (m + 1))
      (by simpa [graph] using hintersect)
    refine ⟨?_, ?_⟩
    · simpa [state] using hi
    · exact huniq.symm
  · rintro ⟨hi, hinter⟩
    have hi' : i ∉ state.seenSource := by simpa [state] using hi
    have hle : sample.sourceIntersection graph i ≤
        feedbackKnot sample lam x0 p0 (m + 1) := by
      simpa [graph] using hinter.le
    exact (sample.sourceIntersection_le_iff_mem_newSource_of_seen_filter
      hlam0 hlamHalf x0 p0 hm hseen i hi').mp hle

theorem mem_newTarget_iff_unseen_and_targetIntersection_eq_next
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n)
    (hseen : (feedbackState sample lam x0 p0 m).seenTarget =
      Finset.univ.filter fun j ↦
        sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j ≤
          feedbackKnot sample lam x0 p0 m)
    (j : Fin n) :
    j ∈ (feedbackState sample lam x0 p0 m).newTarget sample lam ↔
      j ∉ (feedbackState sample lam x0 p0 m).seenTarget ∧
        sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j =
          feedbackKnot sample lam x0 p0 (m + 1) := by
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let state := feedbackState sample lam x0 p0 m
  have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
  constructor
  · intro hnew
    have hnew' : j ∈ (Finset.univ \ state.seenTarget).filter
        (fun k ↦ state.targetCoordinate sample lam k = state.nextCoordinate sample lam) := by
      simpa only [FeedbackStepState.newTarget] using hnew
    have hj : j ∉ state.seenTarget :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hnew').1).2
    have hcoord : state.targetCoordinate sample lam j =
        feedbackKnot sample lam x0 p0 (m + 1) := by
      have hnext : state.nextCoordinate sample lam =
          feedbackKnot sample lam x0 p0 (m + 1) := by
        rfl
      rw [← hnext]
      exact (Finset.mem_filter.mp hnew').2
    have hcross := targetSegmentCrossing_intersects
      (x0 := state.x) (p0 := state.p) (q := state.slope lam)
      (s := (n : ℝ) * (sample.targetHeight j : ℝ))
      (b := sample.targetSlope j)
      (sample.targetSlope_mem j).1 (sample.targetSlope_mem j).2
      (by simpa [FeedbackStepState.slope] using
        (abs_feedbackSlope_le (lam := lam) (k := (state.current : ℝ)) hlam0))
      hlam0 hlamHalf
    have hcross' : sample.targetPhase j
        (segmentCurve state.x state.p (state.slope lam)
          (feedbackKnot sample lam x0 p0 (m + 1))) =
        feedbackKnot sample lam x0 p0 (m + 1) := by
      rw [← hcoord]
      simpa [FeedbackStepState.targetCoordinate, targetPhase] using hcross
    have hintersect : sample.targetPhase j
        (feedbackCurve sample lam x0 p0
          (feedbackKnot sample lam x0 p0 (m + 1))) =
        feedbackKnot sample lam x0 p0 (m + 1) := by
      rw [sample.feedbackCurve_eq_segment_on_closed_interval hlam0 hlamHalf
        x0 p0 (m := m) (x := feedbackKnot sample lam x0 p0 (m + 1)) hm
        (hmono (Nat.le_succ m)) le_rfl]
      simpa [state, feedbackKnot, feedbackKnotValue] using hcross'
    have huniq := sample.targetIntersection_unique graph j
      (x := feedbackKnot sample lam x0 p0 (m + 1))
      (by simpa [graph] using hintersect)
    refine ⟨?_, ?_⟩
    · simpa [state] using hj
    · exact huniq.symm
  · rintro ⟨hj, hinter⟩
    have hj' : j ∉ state.seenTarget := by simpa [state] using hj
    have hle : sample.targetIntersection graph j ≤
        feedbackKnot sample lam x0 p0 (m + 1) := by
      simpa [graph] using hinter.le
    exact (sample.targetIntersection_le_iff_mem_newTarget_of_seen_filter
      hlam0 hlamHalf x0 p0 hm hseen j hj').mp hle

/-! ## Seen sets, counts, and current at the recursive knots -/

theorem feedbackState_seenSource_eq_sourceIntersection_filter
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m ≤ 2 * n) :
    (feedbackState sample lam x0 p0 m).seenSource =
      Finset.univ.filter fun i ↦
        sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤
          feedbackKnot sample lam x0 p0 m := by
  induction m with
  | zero =>
      simpa [feedbackState_zero, initialFeedbackState] using
        sample.initialSeenSource_eq_sourceIntersection_filter hlam0 hlamHalf x0 p0
  | succ m ih =>
      have hmH : m < 2 * n := by omega
      have hsource := sample.sourceIntersection_le_iff_mem_newSource_of_seen_filter
        hlam0 hlamHalf x0 p0 hmH (ih (by omega))
      ext i
      rw [feedbackState_succ, FeedbackStepState.step]
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hseen : i ∈ (feedbackState sample lam x0 p0 m).seenSource
      · have hnew : i ∉ (feedbackState sample lam x0 p0 m).newSource sample lam := by
          exact fun hi => (Finset.disjoint_left.mp
            (FeedbackStepState.newSource_disjoint_seenSource sample lam _)) hi hseen
        have hprev : i ∈ Finset.univ.filter fun k ↦
            sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) k ≤
              feedbackKnot sample lam x0 p0 m := by
          rw [← ih (by omega)]
          exact hseen
        have hle : sample.sourceIntersection
            (sample.feedbackGraph hlam0 hlamHalf x0 p0) i ≤
              feedbackKnot sample lam x0 p0 m :=
          (Finset.mem_filter.mp hprev).2
        constructor
        · intro _
          simpa [Nat.succ_eq_add_one] using
            (le_trans hle (sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
              (Nat.le_succ m)))
        · intro _
          simp [hseen]
      · have hiff := hsource i hseen
        constructor
        · intro hmem
          have hnew : i ∈ (feedbackState sample lam x0 p0 m).newSource sample lam := by
            simpa [hseen] using hmem
          exact hiff.mpr hnew
        · intro hle
          have hnew : i ∈ (feedbackState sample lam x0 p0 m).newSource sample lam :=
            hiff.mp hle
          simp [hseen, hnew]

theorem feedbackState_seenTarget_eq_targetIntersection_filter
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m ≤ 2 * n) :
    (feedbackState sample lam x0 p0 m).seenTarget =
      Finset.univ.filter fun j ↦
        sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j ≤
          feedbackKnot sample lam x0 p0 m := by
  induction m with
  | zero =>
      simpa [feedbackState_zero, initialFeedbackState] using
        sample.initialSeenTarget_eq_targetIntersection_filter hlam0 hlamHalf x0 p0
  | succ m ih =>
      have hmH : m < 2 * n := by omega
      have htarget := sample.targetIntersection_le_iff_mem_newTarget_of_seen_filter
        hlam0 hlamHalf x0 p0 hmH (ih (by omega))
      ext j
      rw [feedbackState_succ, FeedbackStepState.step]
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hseen : j ∈ (feedbackState sample lam x0 p0 m).seenTarget
      · have hnew : j ∉ (feedbackState sample lam x0 p0 m).newTarget sample lam := by
          exact fun hj => (Finset.disjoint_left.mp
            (FeedbackStepState.newTarget_disjoint_seenTarget sample lam _)) hj hseen
        have hprev : j ∈ Finset.univ.filter fun k ↦
            sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) k ≤
              feedbackKnot sample lam x0 p0 m := by
          rw [← ih (by omega)]
          exact hseen
        have hle : sample.targetIntersection
            (sample.feedbackGraph hlam0 hlamHalf x0 p0) j ≤
              feedbackKnot sample lam x0 p0 m :=
          (Finset.mem_filter.mp hprev).2
        constructor
        · intro _
          simpa [Nat.succ_eq_add_one] using
            (le_trans hle (sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
              (Nat.le_succ m)))
        · intro _
          simp [hseen]
      · have hiff := htarget j hseen
        constructor
        · intro hmem
          have hnew : j ∈ (feedbackState sample lam x0 p0 m).newTarget sample lam := by
            simpa [hseen] using hmem
          exact hiff.mpr hnew
        · intro hle
          have hnew : j ∈ (feedbackState sample lam x0 p0 m).newTarget sample lam :=
            hiff.mp hle
          simp [hseen, hnew]

/-- At an actual recursive step, the newly absorbed source labels are exactly the previously
unseen labels whose global graph intersection is the next knot. -/
theorem mem_newSource_iff_unseen_and_sourceIntersection_eq_next_at_step
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n) (i : Fin n) :
    i ∈ (feedbackState sample lam x0 p0 m).newSource sample lam ↔
      i ∉ (feedbackState sample lam x0 p0 m).seenSource ∧
        sample.sourceIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) i =
          feedbackKnot sample lam x0 p0 (m + 1) := by
  exact sample.mem_newSource_iff_unseen_and_sourceIntersection_eq_next
    hlam0 hlamHalf x0 p0 hm
      (sample.feedbackState_seenSource_eq_sourceIntersection_filter
        hlam0 hlamHalf x0 p0 (le_of_lt hm)) i

/-- At an actual recursive step, the newly absorbed target labels are exactly the previously
unseen labels whose global graph intersection is the next knot. -/
theorem mem_newTarget_iff_unseen_and_targetIntersection_eq_next_at_step
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n) (j : Fin n) :
    j ∈ (feedbackState sample lam x0 p0 m).newTarget sample lam ↔
      j ∉ (feedbackState sample lam x0 p0 m).seenTarget ∧
        sample.targetIntersection (sample.feedbackGraph hlam0 hlamHalf x0 p0) j =
          feedbackKnot sample lam x0 p0 (m + 1) := by
  exact sample.mem_newTarget_iff_unseen_and_targetIntersection_eq_next
    hlam0 hlamHalf x0 p0 hm
      (sample.feedbackState_seenTarget_eq_targetIntersection_filter
        hlam0 hlamHalf x0 p0 (le_of_lt hm)) j

theorem sourceIntersectionCount_eq_seenSource_card_of_knot_le_of_lt_next
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n) {x : ℝ}
    (hleft : feedbackKnot sample lam x0 p0 m ≤ x)
    (hright : x < feedbackKnot sample lam x0 p0 (m + 1)) :
    sample.sourceIntersectionCount (sample.feedbackGraph hlam0 hlamHalf x0 p0) x =
      (feedbackState sample lam x0 p0 m).seenSource.card := by
  classical
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let state := feedbackState sample lam x0 p0 m
  have hseen := sample.feedbackState_seenSource_eq_sourceIntersection_filter
    hlam0 hlamHalf x0 p0 (le_of_lt hm)
  have hfilter : Finset.univ.filter (fun i ↦ sample.sourceIntersection graph i ≤ x) =
      state.seenSource := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ state.seenSource
    · have hleK : sample.sourceIntersection graph i ≤
          feedbackKnot sample lam x0 p0 m := by
        have hi' : i ∈ Finset.univ.filter
            (fun k ↦ sample.sourceIntersection graph k ≤
              feedbackKnot sample lam x0 p0 m) := by
          rw [← hseen]
          simpa [state] using hi
        exact (Finset.mem_filter.mp hi').2
      have hleX : sample.sourceIntersection graph i ≤ x := hleK.trans hleft
      constructor
      · intro _
        exact hi
      · intro _
        exact hleX
    · constructor
      · intro hleX
        have hleNext : sample.sourceIntersection graph i ≤
            feedbackKnot sample lam x0 p0 (m + 1) :=
          hleX.trans (le_of_lt hright)
        have hnew := (sample.sourceIntersection_le_iff_mem_newSource_of_seen_filter
          hlam0 hlamHalf x0 p0 hm hseen i (by simpa [state] using hi)).mp hleNext
        have heq := (sample.mem_newSource_iff_unseen_and_sourceIntersection_eq_next
          hlam0 hlamHalf x0 p0 hm hseen i).mp hnew
        have hnext_le_x : feedbackKnot sample lam x0 p0 (m + 1) ≤ x := by
          rw [← heq.2]
          exact hleX
        exact False.elim ((not_le_of_gt hright) hnext_le_x)
      · intro hi'
        exact False.elim (hi (by simpa [state] using hi'))
  change (Finset.card (Finset.univ.filter
    (fun i ↦ sample.sourceIntersection graph i ≤ x))) = state.seenSource.card
  rw [hfilter]

theorem targetIntersectionCount_eq_seenTarget_card_of_knot_le_of_lt_next
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m < 2 * n) {x : ℝ}
    (hleft : feedbackKnot sample lam x0 p0 m ≤ x)
    (hright : x < feedbackKnot sample lam x0 p0 (m + 1)) :
    sample.targetIntersectionCount (sample.feedbackGraph hlam0 hlamHalf x0 p0) x =
      (feedbackState sample lam x0 p0 m).seenTarget.card := by
  classical
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let state := feedbackState sample lam x0 p0 m
  have hseen := sample.feedbackState_seenTarget_eq_targetIntersection_filter
    hlam0 hlamHalf x0 p0 (le_of_lt hm)
  have hfilter : Finset.univ.filter (fun j ↦ sample.targetIntersection graph j ≤ x) =
      state.seenTarget := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j ∈ state.seenTarget
    · have hleK : sample.targetIntersection graph j ≤
          feedbackKnot sample lam x0 p0 m := by
        have hj' : j ∈ Finset.univ.filter
            (fun k ↦ sample.targetIntersection graph k ≤
              feedbackKnot sample lam x0 p0 m) := by
          rw [← hseen]
          simpa [state] using hj
        exact (Finset.mem_filter.mp hj').2
      have hleX : sample.targetIntersection graph j ≤ x := hleK.trans hleft
      constructor
      · intro _
        exact hj
      · intro _
        exact hleX
    · constructor
      · intro hleX
        have hleNext : sample.targetIntersection graph j ≤
            feedbackKnot sample lam x0 p0 (m + 1) :=
          hleX.trans (le_of_lt hright)
        have hnew := (sample.targetIntersection_le_iff_mem_newTarget_of_seen_filter
          hlam0 hlamHalf x0 p0 hm hseen j (by simpa [state] using hj)).mp hleNext
        have heq := (sample.mem_newTarget_iff_unseen_and_targetIntersection_eq_next
          hlam0 hlamHalf x0 p0 hm hseen j).mp hnew
        have hnext_le_x : feedbackKnot sample lam x0 p0 (m + 1) ≤ x := by
          rw [← heq.2]
          exact hleX
        exact False.elim ((not_le_of_gt hright) hnext_le_x)
      · intro hj'
        exact False.elim (hj (by simpa [state] using hj'))
  change (Finset.card (Finset.univ.filter
    (fun j ↦ sample.targetIntersection graph j ≤ x))) = state.seenTarget.card
  rw [hfilter]

theorem sourceIntersectionCount_eq_terminal_seenSource_card_of_ge_terminal
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {x : ℝ}
    (hge : feedbackKnot sample lam x0 p0 (2 * n) ≤ x) :
    sample.sourceIntersectionCount (sample.feedbackGraph hlam0 hlamHalf x0 p0) x =
      (feedbackState sample lam x0 p0 (2 * n)).seenSource.card := by
  classical
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let state := feedbackState sample lam x0 p0 (2 * n)
  have hterminal : state.seenSource = Finset.univ := by
    exact (FeedbackStepState.candidates_eq_empty_iff sample lam state).mp
      (sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0) |>.1
  have hseen := sample.feedbackState_seenSource_eq_sourceIntersection_filter
    hlam0 hlamHalf x0 p0 (le_rfl : 2 * n ≤ 2 * n)
  have hall : ∀ i : Fin n, sample.sourceIntersection graph i ≤
      feedbackKnot sample lam x0 p0 (2 * n) := by
    intro i
    have hi : i ∈ state.seenSource := by rw [hterminal]; simp
    have hi' : i ∈ Finset.univ.filter
        (fun k ↦ sample.sourceIntersection graph k ≤
          feedbackKnot sample lam x0 p0 (2 * n)) := by
      rw [← hseen]
      simpa [state] using hi
    exact (Finset.mem_filter.mp hi').2
  have hfilter : Finset.univ.filter (fun i ↦ sample.sourceIntersection graph i ≤ x) =
      Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact (hall i).trans hge
  change (Finset.card (Finset.univ.filter
    (fun i ↦ sample.sourceIntersection graph i ≤ x))) = state.seenSource.card
  rw [hfilter, hterminal]

theorem targetIntersectionCount_eq_terminal_seenTarget_card_of_ge_terminal
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {x : ℝ}
    (hge : feedbackKnot sample lam x0 p0 (2 * n) ≤ x) :
    sample.targetIntersectionCount (sample.feedbackGraph hlam0 hlamHalf x0 p0) x =
      (feedbackState sample lam x0 p0 (2 * n)).seenTarget.card := by
  classical
  let graph := sample.feedbackGraph hlam0 hlamHalf x0 p0
  let state := feedbackState sample lam x0 p0 (2 * n)
  have hterminal : state.seenTarget = Finset.univ := by
    exact (FeedbackStepState.candidates_eq_empty_iff sample lam state).mp
      (sample.feedbackState_candidates_eq_empty_two_mul lam x0 p0) |>.2
  have hseen := sample.feedbackState_seenTarget_eq_targetIntersection_filter
    hlam0 hlamHalf x0 p0 (le_rfl : 2 * n ≤ 2 * n)
  have hall : ∀ j : Fin n, sample.targetIntersection graph j ≤
      feedbackKnot sample lam x0 p0 (2 * n) := by
    intro j
    have hj : j ∈ state.seenTarget := by rw [hterminal]; simp
    have hj' : j ∈ Finset.univ.filter
        (fun k ↦ sample.targetIntersection graph k ≤
          feedbackKnot sample lam x0 p0 (2 * n)) := by
      rw [← hseen]
      simpa [state] using hj
    exact (Finset.mem_filter.mp hj').2
  have hfilter : Finset.univ.filter (fun j ↦ sample.targetIntersection graph j ≤ x) =
      Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact (hall j).trans hge
  change (Finset.card (Finset.univ.filter
    (fun j ↦ sample.targetIntersection graph j ≤ x))) = state.seenTarget.card
  rw [hfilter, hterminal]

theorem feedbackState_seenSource_card_eq_sourceIntersectionCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m ≤ 2 * n) :
    ((feedbackState sample lam x0 p0 m).seenSource.card : ℕ) =
      sample.sourceIntersectionCount (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (feedbackKnot sample lam x0 p0 m) := by
  rw [sample.feedbackState_seenSource_eq_sourceIntersection_filter hlam0 hlamHalf x0 p0 hm]
  rfl

theorem feedbackState_seenTarget_card_eq_targetIntersectionCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m ≤ 2 * n) :
    ((feedbackState sample lam x0 p0 m).seenTarget.card : ℕ) =
      sample.targetIntersectionCount (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (feedbackKnot sample lam x0 p0 m) := by
  rw [sample.feedbackState_seenTarget_eq_targetIntersection_filter hlam0 hlamHalf x0 p0 hm]
  rfl

theorem feedbackState_current_eq_intersectionCount_sub
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} (hm : m ≤ 2 * n) :
    (feedbackState sample lam x0 p0 m).current =
      (sample.sourceIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (feedbackKnot sample lam x0 p0 m) : ℤ) -
      sample.targetIntersectionCount
        (sample.feedbackGraph hlam0 hlamHalf x0 p0)
        (feedbackKnot sample lam x0 p0 m) := by
  rw [sample.feedbackState_current_eq_card_sub,
    sample.feedbackState_seenSource_card_eq_sourceIntersectionCount hlam0 hlamHalf x0 p0 hm,
    sample.feedbackState_seenTarget_card_eq_targetIntersectionCount hlam0 hlamHalf x0 p0 hm]

end FiniteSample

end OTSelector
