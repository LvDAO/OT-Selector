import OTSelector.Feedback.FiniteHistoryCoverage
import OTSelector.Feedback.RevealedCounting

/-!
# The elapsed feedback graph height

The elapsed state is a post-jump state.  This file first identifies the affine segment selected by
that state with the deterministic feedback curve, and then adds the null tie fallback needed for a
process adapted to the revealed filtration.
-/

open MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## Deterministic terminal tail -/

theorem feedbackCurveAux_eq_terminal_value_of_ge_terminal_knot
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {x : ℝ}
  (hx : feedbackKnot sample lam x0 p0 (2 * n) ≤ x) :
    feedbackCurveAux sample lam x0 p0 (2 * n) 0 x =
      feedbackKnotValue sample lam x0 p0 (2 * n) := by
  by_cases hxeq : x = feedbackKnot sample lam x0 p0 (2 * n)
  · subst x
    by_cases hterminal : feedbackKnot sample lam x0 p0 (2 * n) ≤ x0
    · have hterminal_eq : feedbackKnot sample lam x0 p0 (2 * n) = x0 := by
        apply le_antisymm hterminal
        exact sample.feedbackKnot_ge_x0 hlam0 hlamHalf x0 p0 (2 * n)
      have hp : p0 = feedbackKnotValue sample lam x0 p0 (2 * n) := by
        calc
          p0 = feedbackCurve sample lam x0 p0 x0 :=
            (sample.feedbackCurve_at_x0 hlam0 hlamHalf x0 p0).symm
          _ = feedbackCurve sample lam x0 p0
              (feedbackKnot sample lam x0 p0 (2 * n)) := by rw [hterminal_eq]
          _ = feedbackKnotValue sample lam x0 p0 (2 * n) :=
            sample.feedbackCurve_eq_feedbackKnotValue_at_knot
              hlam0 hlamHalf x0 p0 (show 2 * n ≤ 2 * n by omega)
      rw [hterminal_eq]
      exact (sample.feedbackCurveAux_zero_at_x0 hlam0 hlamHalf x0 p0).trans hp
    · have hcurve := sample.feedbackCurve_eq_feedbackKnotValue_at_knot
        hlam0 hlamHalf x0 p0 (show 2 * n ≤ 2 * n by omega)
      have haux : feedbackCurve sample lam x0 p0
          (feedbackKnot sample lam x0 p0 (2 * n)) =
          feedbackCurveAux sample lam x0 p0 (2 * n) 0
            (feedbackKnot sample lam x0 p0 (2 * n)) := by
        rw [feedbackCurve, ite_eq_right hterminal]
      exact haux ▸ hcurve
  · have hxgt : feedbackKnot sample lam x0 p0 (2 * n) < x :=
      lt_of_le_of_ne hx (Ne.symm hxeq)
    have haux : ∀ m ≤ 2 * n,
        feedbackCurveAux sample lam x0 p0 (2 * n) m x =
          feedbackKnotValue sample lam x0 p0 (2 * n) := by
      intro m hm
      induction hdiff : 2 * n - m using Nat.strong_induction_on generalizing m with
      | h d ih =>
          by_cases hmH : m < 2 * n
          · have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
            have hk : feedbackKnot sample lam x0 p0 (m + 1) ≤
                feedbackKnot sample lam x0 p0 (2 * n) := hmono (by omega)
            have hnot : ¬x ≤ feedbackKnot sample lam x0 p0 (m + 1) :=
              not_le_of_gt (lt_of_le_of_lt hk hxgt)
            rw [feedbackCurveAux, dite_eq_left hmH, ite_eq_right hnot]
            exact ih (2 * n - (m + 1)) (by omega) (m + 1) (by omega) rfl
          · have hmH' : m = 2 * n := by omega
            subst m
            rw [feedbackCurveAux, dite_eq_right (by omega)]
    exact haux 0 (by omega)

theorem feedbackCurve_eq_terminal_value_of_ge_terminal_knot
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {x : ℝ}
    (hx : feedbackKnot sample lam x0 p0 (2 * n) ≤ x) :
    feedbackCurve sample lam x0 p0 x =
      feedbackKnotValue sample lam x0 p0 (2 * n) := by
  have hx0 : x0 ≤ x := by
    have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
    have hzero : x0 ≤ feedbackKnot sample lam x0 p0 (2 * n) := by
      simpa only [feedbackKnot_zero] using hmono (Nat.zero_le (2 * n))
    exact hzero.trans hx
  by_cases hxx0 : x ≤ x0
  · have hxeq : x = x0 := le_antisymm hxx0 hx0
    subst x
    have hterminal : feedbackKnot sample lam x0 p0 (2 * n) = x0 := by
      apply le_antisymm
      · exact hx
      · exact sample.feedbackKnot_ge_x0 hlam0 hlamHalf x0 p0 (2 * n)
    have hp : p0 = feedbackKnotValue sample lam x0 p0 (2 * n) := by
      calc
        p0 = feedbackCurve sample lam x0 p0 x0 :=
          (sample.feedbackCurve_at_x0 hlam0 hlamHalf x0 p0).symm
        _ = feedbackCurve sample lam x0 p0
            (feedbackKnot sample lam x0 p0 (2 * n)) := by rw [hterminal]
        _ = feedbackKnotValue sample lam x0 p0 (2 * n) :=
          sample.feedbackCurve_eq_feedbackKnotValue_at_knot
            hlam0 hlamHalf x0 p0 (show 2 * n ≤ 2 * n by omega)
    exact (sample.feedbackCurve_at_x0 hlam0 hlamHalf x0 p0).trans hp
  · rw [feedbackCurve, ite_eq_right hxx0]
    exact sample.feedbackCurveAux_eq_terminal_value_of_ge_terminal_knot
      hlam0 hlamHalf x0 p0 hx

/-! ## Elapsed height and its deterministic identification -/

noncomputable def feedbackHeightAtElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  let state := sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t
  let m := (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val
  if m < 2 * n then
    segmentCurve state.x state.p (state.slope lam) (x0 + (t : ℝ))
  else state.p

theorem feedbackHeightAtElapsed_eq_feedbackCurve
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
      feedbackCurve sample lam x0 p0 (x0 + (t : ℝ)) := by
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 t
  have hmem := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
  by_cases hm : I.val < 2 * n
  · have hleftNN : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 I.val ≤ t := by
      simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
    have hleft : feedbackKnot sample lam x0 p0 I.val ≤ x0 + (t : ℝ) := by
      have hleft' := NNReal.coe_le_coe.mp hleftNN
      change sample.feedbackKnot lam x0 p0 I.val - x0 ≤ (t : ℝ) at hleft'
      linarith
    have hright : x0 + (t : ℝ) <
        feedbackKnot sample lam x0 p0 (I.val + 1) :=
      sample.elapsedIndex_next_knot_gt_of_val_lt hlam0 hlamHalf x0 p0 t hm
    have hseg := sample.feedbackCurve_eq_segment_on_closed_interval
      hlam0 hlamHalf x0 p0 hm hleft (le_of_lt hright)
    change (if I.val < 2 * n then
      segmentCurve (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).x
        (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).p
        ((sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).slope lam)
        (x0 + (t : ℝ))
      else (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).p) = _
    rw [ite_eq_left hm]
    rw [show sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t =
        feedbackState sample lam x0 p0 I.val by rfl]
    exact hseg.symm
  · have hmle : I.val ≤ 2 * n := by omega
    have hmeq : I.val = 2 * n := by omega
    have hmem_le := hmem
    simp only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem_le
    have hmeq' : (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val = 2 * n := by
      simpa [I] using hmeq
    have hmem' : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (2 * n) ≤ t := by
      simpa [hmeq'] using hmem_le
    have hstate := sample.feedbackStateAtElapsed_eq_terminal_of_terminal_le
      hlam0 hlamHalf x0 p0 hmem'
    have hcurve := sample.feedbackCurve_eq_terminal_value_of_ge_terminal_knot
      hlam0 hlamHalf x0 p0 (show feedbackKnot sample lam x0 p0 (2 * n) ≤
        x0 + (t : ℝ) by
          have hcoe := NNReal.coe_le_coe.mp hmem'
          change sample.feedbackKnot lam x0 p0 (2 * n) - x0 ≤ (t : ℝ) at hcoe
          linarith)
    change (if I.val < 2 * n then
      segmentCurve (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).x
        (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).p
        ((sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).slope lam)
        (x0 + (t : ℝ))
      else (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).p) = _
    rw [ite_eq_right hm, hstate]
    exact hcurve.symm

theorem feedbackHeightAtElapsed_eq_segmentCurve
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) :
    feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
      segmentCurve
        (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).x
        (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).p
        ((sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).slope lam)
        (x0 + (t : ℝ)) := by
  let I := sample.elapsedIndex hlam0 hlamHalf x0 p0 t
  by_cases hm : I.val < 2 * n
  · change (if I.val < 2 * n then _ else _) = _
    rw [ite_eq_left hm]
  · have hmeq : I.val = 2 * n := by omega
    have hmem := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
    have hmem_le := hmem
    simp only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem_le
    have hmeq' : (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val = 2 * n := by
      simpa [I] using hmeq
    have hmem' : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (2 * n) ≤ t := by
      simpa [hmeq'] using hmem_le
    have hstate := sample.feedbackStateAtElapsed_eq_terminal_of_terminal_le
      hlam0 hlamHalf x0 p0 hmem'
    change (if I.val < 2 * n then _ else _) = _
    rw [ite_eq_right hm, hstate, sample.feedbackState_terminal_slope]
    simp [segmentCurve]

/-! ## The safe branch -/

noncomputable def safeFeedbackHeightAtElapsed
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n) : ℝ :=
  if sample.NoFeedbackTies lam x0 p0 then
    feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample else p0

theorem safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (sample : FiniteSample n)
    (hgood : sample.NoFeedbackTies lam x0 p0) :
    safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample =
      feedbackCurve sample lam x0 p0 (x0 + (t : ℝ)) := by
  simp [safeFeedbackHeightAtElapsed, hgood,
    sample.feedbackHeightAtElapsed_eq_feedbackCurve hlam0 hlamHalf x0 p0 t]

theorem measurable_feedbackHeightAtElapsed_raw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) :
    Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun sample : FiniteSample n ↦
        feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) := by
  have hsnap := stronglyAdapted_rawRevealedSnapshot
    (n := n) hlam0 hlamHalf x0 p0
  let stateOfSnapshot : RevealedSnapshot n → FeedbackStepState n := fun z ↦
    FeedbackStepState.unpack z.1
  have hstate : Measurable stateOfSnapshot := by
    exact FeedbackStepState.measurable_unpack.comp measurable_fst
  have hheight : Measurable (fun z : RevealedSnapshot n ↦
      segmentCurve (stateOfSnapshot z).x (stateOfSnapshot z).p
        ((stateOfSnapshot z).slope lam) (x0 + (t : ℝ))) := by
    have hx : Measurable (fun z : RevealedSnapshot n ↦ (stateOfSnapshot z).x) :=
      FeedbackStepState.measurable_x.comp hstate
    have hp : Measurable (fun z : RevealedSnapshot n ↦ (stateOfSnapshot z).p) :=
      FeedbackStepState.measurable_p.comp hstate
    have hslope : Measurable (fun z : RevealedSnapshot n ↦
        (stateOfSnapshot z).slope lam) :=
      (FeedbackStepState.measurable_slope lam).comp hstate
    have harg : Measurable (fun z : RevealedSnapshot n ↦
        x0 + (t : ℝ) - (stateOfSnapshot z).x) :=
      (measurable_const : Measurable
        (fun _ : RevealedSnapshot n ↦ x0 + (t : ℝ))).sub hx
    change Measurable (fun z : RevealedSnapshot n ↦
      (stateOfSnapshot z).p + (stateOfSnapshot z).slope lam *
        (x0 + (t : ℝ) - (stateOfSnapshot z).x))
    exact hp.add (hslope.mul harg)
  have hcomp : Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun sample : FiniteSample n ↦
        segmentCurve
          (stateOfSnapshot
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t)).x
          (stateOfSnapshot
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t)).p
          ((stateOfSnapshot
            (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t)).slope lam)
          (x0 + (t : ℝ))) :=
    hheight.comp (hsnap t).measurable
  convert hcomp using 1
  funext sample
  have hstate_unpack : stateOfSnapshot
      (sample.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t) =
      sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t := by
    rfl
  rw [sample.feedbackHeightAtElapsed_eq_segmentCurve hlam0 hlamHalf x0 p0 t,
    hstate_unpack]

theorem measurable_safeFeedbackHeightAtElapsed_usual
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) :
    Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun sample : FiniteSample n ↦
        safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) := by
  have hraw := measurable_feedbackHeightAtElapsed_raw
    (n := n) hlam0 hlamHalf x0 p0 t
  have hheight : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
    (fun sample : FiniteSample n ↦
        feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) :=
    fun s hs ↦ (rawRevealedFiltration_le_usual
      (n := n) hlam0 hlamHalf x0 p0 t) _ (hraw hs)
  have hgood0 := measurableSet_feedbackGoodEvent_usual_zero
    (n := n) hlam0 hlamHalf x0 p0
  have hgood : MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (feedbackGoodEvent (n := n) lam x0 p0) :=
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).mono bot_le _ hgood0
  have hsafe : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun sample : FiniteSample n ↦
        if sample.NoFeedbackTies lam x0 p0 then
          feedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample else p0) := by
    apply Measurable.ite
    · simpa only [feedbackGoodEvent] using hgood
    · exact hheight
    · exact measurable_const
  simpa only [safeFeedbackHeightAtElapsed] using hsafe

theorem safeFeedbackHeightAtElapsed_stronglyAdapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) := by
  intro t
  exact (measurable_safeFeedbackHeightAtElapsed_usual
    (n := n) hlam0 hlamHalf x0 p0 t).stronglyMeasurable

theorem safeFeedbackHeightAtElapsed_adapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    Adapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) := by
  exact (safeFeedbackHeightAtElapsed_stronglyAdapted
    (n := n) hlam0 hlamHalf x0 p0).adapted

theorem safeFeedbackHeightAtElapsed_continuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (sample : FiniteSample n) :
    Continuous (fun t : ℝ≥0 ↦
      safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) := by
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · have hfun : (fun t : ℝ≥0 ↦
        safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) =
      (fun t : ℝ≥0 ↦ feedbackCurve sample lam x0 p0 (x0 + (t : ℝ))) := by
      funext t
      exact sample.safeFeedbackHeightAtElapsed_eq_feedbackCurve_of_good
        hlam0 hlamHalf x0 p0 t hgood
    rw [hfun]
    exact (sample.feedbackCurve_continuous hlam0 hlamHalf x0 p0).comp
      (continuous_const.add continuous_subtype_val)
  · have hfun : (fun t : ℝ≥0 ↦
        safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) =
      (fun _ : ℝ≥0 ↦ p0) := by
      funext t
      simp [safeFeedbackHeightAtElapsed, hgood]
    rw [hfun]
    exact continuous_const

theorem safeFeedbackHeightAtElapsed_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t sample ↦ safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0 t sample) :=
  CountingProcess.MeasureTheory.IsStronglyPredictable.of_continuous_adapted
    (fun t ↦ (measurable_safeFeedbackHeightAtElapsed_usual
      (n := n) hlam0 hlamHalf x0 p0 t).stronglyMeasurable)
    (fun sample ↦ safeFeedbackHeightAtElapsed_continuous
      hlam0 hlamHalf x0 p0 sample)

end FiniteSample

end OTSelector
