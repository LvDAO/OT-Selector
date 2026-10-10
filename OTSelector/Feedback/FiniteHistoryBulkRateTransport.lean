import OTSelector.Feedback.FiniteHistoryBulkAllLabel
import OTSelector.Feedback.FiniteHistoryBulkInterval
import OTSelector.Feedback.FiniteHistoryBulkRateBound
import OTSelector.Feedback.FiniteHistoryBulkRateCell
import OTSelector.Feedback.FiniteHistoryCoordinateJointMeasurable
import OTSelector.Feedback.AdaptiveDeferredDecision

/-!
# Transport of a fixed-history bulk rate to the finite-sample law

The nested seen/time/unseen integral supplied by the next-event calculation is rewritten as a
time/sample integral of the actual safe bulk rate.  The proof keeps the continuously valued seen
tuple as an outer integration variable, uses Fubini only after a uniform bulk bound has established
integrability, and replaces the right-continuous history cell by its strict version only almost
everywhere.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace OTSelector

variable {n : ℕ}

private noncomputable def historyNestedRateMassOf
    (stateRate : FeedbackStepState n → ℝ → ℝ)
    (width lam x0 p0 s t : ℝ)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (E : Set (FiniteSample n)) : ℝ :=
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  ∫ seen, ∫ y in Ioc (feedbackBranchBulkStart width lam
      (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) s)
      (feedbackBranchBulkStop width lam
        (feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen) t),
    ∫ unseen,
      {unseen : feedbackUnseenFinset S → MarkedHeight |
        HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
            lam x0 p0 sourcePattern targetPattern history y ∧
          finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
        (fun _ ↦ stateRate
          (feedbackScheduledStateOfSeen lam x0 p0
            sourcePattern targetPattern history seen) y) unseen
      ∂(feedbackUnseenTupleLaw S) ∂volume
    ∂(feedbackTupleLaw S)

set_option maxHeartbeats 1000000 in
private theorem historyNestedRateMassOf_eq_strictSafeRate
    {width lam x0 p0 s t : ℝ}
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hhistory : history.length ≤ 2 * n)
    (E : Set (FiniteSample n)) (hE : MeasurableSet E)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hwidth : 0 < width) (hx0s : x0 ≤ s)
    (stateRate : FeedbackStepState n → ℝ → ℝ)
    (hstateRate : Measurable fun pair : FeedbackStepState n × ℝ ↦
      stateRate pair.1 pair.2)
    (hstateRateBulk : ∀ (state : FeedbackStepState n) (y : ℝ),
      feedbackBulkRegion n width y
          (segmentCurve state.x state.p (state.slope lam) y) →
        stateRate state y ∈ Icc 0 (feedbackBulkRateCap n width))
    (safeRate : ℝ≥0 → FiniteSample n → ℝ)
    (hsafeRateBulk : ∀ (sample : FiniteSample n) (y : ℝ), x0 < y →
      HistoryBeforeCoordinate sample lam x0 p0
          sourcePattern targetPattern history y →
      ∀ (u : ℝ≥0), FiniteSample.elapsedFeedbackCoordinate x0 u = y →
        feedbackBulkRegion n width y
          (segmentCurve
            (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x
            (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).p
            ((sample.scheduledState lam x0 p0
              sourcePattern targetPattern history).slope lam) y) →
        safeRate u sample = stateRate
          (sample.scheduledState lam x0 p0 sourcePattern targetPattern history) y)
    (hsafeRateNotBulk : ∀ (sample : FiniteSample n) (y : ℝ), x0 < y →
      HistoryBeforeCoordinate sample lam x0 p0
          sourcePattern targetPattern history y →
      ∀ (u : ℝ≥0), FiniteSample.elapsedFeedbackCoordinate x0 u = y →
        ¬ feedbackBulkRegion n width y
          (segmentCurve
            (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).x
            (sample.scheduledState lam x0 p0 sourcePattern targetPattern history).p
            ((sample.scheduledState lam x0 p0
              sourcePattern targetPattern history).slope lam) y) →
        safeRate u sample = 0) :
    historyNestedRateMassOf stateRate width lam x0 p0 s t
        sourcePattern targetPattern history E =
      ∫ y in Ioc s t, ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0
              sourcePattern targetPattern history y ∧ sample ∈ E}.indicator
          (fun _ ↦ safeRate (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume := by
  classical
  let S := feedbackTerminalLabelSet sourcePattern targetPattern history
  let seenLaw := feedbackTupleLaw S
  let unseenLaw := feedbackUnseenTupleLaw S
  let timeLaw := volume.restrict (Ioc s t)
  let state : (S → MarkedHeight) → FeedbackStepState n := fun seen ↦
    feedbackScheduledStateOfSeen lam x0 p0 sourcePattern targetPattern history seen
  let merge : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) → FiniteSample n := fun z ↦
    finiteSampleSeenUnseenMerge S z.1.1 z.2
  let rateSet : Set (((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight)) :=
    {z |
      HistoryAtCoordinate (merge z) lam x0 p0 sourcePattern targetPattern history z.1.2 ∧
        merge z ∈ E ∧
        feedbackBulkRegion n width z.1.2
          (segmentCurve (state z.1.1).x (state z.1.1).p
            ((state z.1.1).slope lam) z.1.2) ∧
        (state z.1.1).x < z.1.2}
  let H : (((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight)) → ℝ := fun z ↦
    rateSet.indicator (fun _ ↦ stateRate (state z.1.1) z.1.2) z
  let G : (S → MarkedHeight) × ℝ → ℝ := fun z ↦
    ∫ unseen, H (z, unseen) ∂unseenLaw
  let : IsProbabilityMeasure seenLaw := by
    dsimp [seenLaw, feedbackTupleLaw]
    infer_instance
  let : IsProbabilityMeasure unseenLaw := by
    dsimp [unseenLaw, feedbackUnseenTupleLaw]
    infer_instance
  let : IsFiniteMeasure timeLaw := by
    dsimp [timeLaw]
    infer_instance
  have hseen : Measurable fun z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ z.1.1 :=
    measurable_fst.comp measurable_fst
  have hy : Measurable fun z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ z.1.2 :=
    measurable_snd.comp measurable_fst
  have hunseen : Measurable fun z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ z.2 := measurable_snd
  have hstate : Measurable fun z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ state z.1.1 := by
    exact (measurable_feedbackScheduledStateOfSeen lam x0 p0
      sourcePattern targetPattern history).comp hseen
  have hmerge : Measurable merge := by
    exact (measurable_finiteSampleSeenUnseenMerge S).comp (hseen.prodMk hunseen)
  have hyMerge : Measurable fun z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ (z.1.2, merge z) :=
    hy.prodMk hmerge
  have hhistoryAt : MeasurableSet {z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) |
      HistoryAtCoordinate (merge z) lam x0 p0
        sourcePattern targetPattern history z.1.2} := by
    simpa only [Set.preimage_ofPred_eq] using
      (measurableSet_historyAtCoordinate_joint (n := n)
        lam x0 p0 sourcePattern targetPattern history).preimage hyMerge
  have hcurve : Measurable fun z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦
      segmentCurve (state z.1.1).x (state z.1.1).p
        ((state z.1.1).slope lam) z.1.2 := by
    simp only [segmentCurve]
    exact (FeedbackStepState.measurable_p.comp hstate).add
      ((FeedbackStepState.measurable_slope lam).comp hstate |>.mul
        (hy.sub (FeedbackStepState.measurable_x.comp hstate)))
  have hbulk : MeasurableSet {z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) |
      feedbackBulkRegion n width z.1.2
        (segmentCurve (state z.1.1).x (state z.1.1).p
          ((state z.1.1).slope lam) z.1.2)} :=
    (feedbackBulkRegion_measurableSet n width).preimage (hy.prodMk hcurve)
  have hstatex : Measurable fun z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦ (state z.1.1).x :=
    FeedbackStepState.measurable_x.comp hstate
  have hrateSet : MeasurableSet rateSet := by
    change MeasurableSet
      ({z | HistoryAtCoordinate (merge z) lam x0 p0
          sourcePattern targetPattern history z.1.2} ∩
        ({z | merge z ∈ E} ∩
          ({z | feedbackBulkRegion n width z.1.2
            (segmentCurve (state z.1.1).x (state z.1.1).p
              ((state z.1.1).slope lam) z.1.2)} ∩
            {z | (state z.1.1).x < z.1.2})))
    exact hhistoryAt.inter ((hE.preimage hmerge).inter
      (hbulk.inter (measurableSet_lt hstatex hy)))
  have hrate : Measurable fun z : ((S → MarkedHeight) × ℝ) ×
      (feedbackUnseenFinset S → MarkedHeight) ↦
      stateRate (state z.1.1) z.1.2 :=
    hstateRate.comp (hstate.prodMk hy)
  have hHmeas : Measurable H := hrate.indicator hrateSet
  have hHint : Integrable H ((seenLaw.prod timeLaw).prod unseenLaw) := by
    apply Integrable.of_bound hHmeas.aestronglyMeasurable (feedbackBulkRateCap n width)
    exact Filter.Eventually.of_forall fun z ↦ by
      by_cases hz : z ∈ rateSet
      · rw [show H z = stateRate (state z.1.1) z.1.2 by
          simp [H, hz]]
        have hb := hstateRateBulk (state z.1.1) z.1.2 hz.2.2.1
        simpa [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
      · simp [H, hz, feedbackBulkRateCap_nonneg]
  have hGint : Integrable G (seenLaw.prod timeLaw) := by
    simpa [G] using hHint.integral_prod_left
  have hbranchToG :
      historyNestedRateMassOf stateRate width lam x0 p0 s t
          sourcePattern targetPattern history E =
        ∫ seen, ∫ y, G (seen, y) ∂timeLaw ∂seenLaw := by
    simp only [historyNestedRateMassOf, S, seenLaw, timeLaw]
    apply integral_congr_ae
    filter_upwards [] with seen
    let terminal := state seen
    let old : ℝ → ℝ := fun y ↦
      ∫ unseen,
        {unseen : feedbackUnseenFinset S → MarkedHeight |
          HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
              lam x0 p0 sourcePattern targetPattern history y ∧
            finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
          (fun _ ↦ stateRate terminal y) unseen ∂unseenLaw
    let slab : Set ℝ :=
      ({y | feedbackBulkRegion n width y
        (segmentCurve terminal.x terminal.p (terminal.slope lam) y)} ∩ Ioc s t) ∩
          Ioi terminal.x
    have hslab : MeasurableSet slab := by
      have hcurveTerminal : Measurable fun y : ℝ ↦
          segmentCurve terminal.x terminal.p (terminal.slope lam) y := by
        simp only [segmentCurve]
        fun_prop
      exact ((feedbackBulkRegion_measurableSet n width).preimage
        (measurable_id.prodMk hcurveTerminal)).inter measurableSet_Ioc |>.inter
          measurableSet_Ioi
    have hsets := feedbackBulk_inter_Ioc_inter_Ioi_state_ae_eq_Ioc_branchBulk
      width lam terminal s t hwidth
    calc
      (∫ y in Ioc (feedbackBranchBulkStart width lam terminal s)
          (feedbackBranchBulkStop width lam terminal t), old y ∂volume) =
          ∫ y in slab, old y ∂volume :=
        setIntegral_congr_set hsets.symm
      _ = ∫ y in Ioc s t, G (seen, y) ∂volume := by
        rw [← integral_indicator hslab, ← integral_indicator measurableSet_Ioc]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y ↦ by
          by_cases hyIoc : y ∈ Ioc s t
          · rw [Set.indicator_of_mem hyIoc]
            by_cases hyBulk : feedbackBulkRegion n width y
                (segmentCurve terminal.x terminal.p (terminal.slope lam) y)
            · by_cases hyState : terminal.x < y
              · have hySlab : y ∈ slab := ⟨⟨hyBulk, hyIoc⟩, hyState⟩
                rw [Set.indicator_of_mem hySlab]
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun unseen ↦ by
                  change
                    {unseen : feedbackUnseenFinset S → MarkedHeight |
                      HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                          lam x0 p0 sourcePattern targetPattern history y ∧
                        finiteSampleSeenUnseenMerge S seen unseen ∈ E}.indicator
                        (fun _ ↦ stateRate terminal y) unseen =
                      H ((seen, y), unseen)
                  let C : Set (feedbackUnseenFinset S → MarkedHeight) :=
                    {unseen |
                      HistoryAtCoordinate (finiteSampleSeenUnseenMerge S seen unseen)
                          lam x0 p0 sourcePattern targetPattern history y ∧
                        finiteSampleSeenUnseenMerge S seen unseen ∈ E}
                  change C.indicator (fun _ ↦ stateRate terminal y) unseen =
                    H ((seen, y), unseen)
                  by_cases hc : HistoryAtCoordinate
                      (finiteSampleSeenUnseenMerge S seen unseen) lam x0 p0
                        sourcePattern targetPattern history y ∧
                    finiteSampleSeenUnseenMerge S seen unseen ∈ E
                  · have hz : ((seen, y), unseen) ∈ rateSet := by
                      exact ⟨hc.1, hc.2, hyBulk, hyState⟩
                    have hcC : unseen ∈ C := hc
                    rw [Set.indicator_of_mem hcC]
                    simp only [H, Set.indicator_of_mem hz]
                    rfl
                  · have hz : ((seen, y), unseen) ∉ rateSet := by
                      intro hz
                      exact hc ⟨hz.1, hz.2.1⟩
                    have hcC : unseen ∉ C := hc
                    rw [Set.indicator_of_notMem hcC]
                    simp only [H, Set.indicator_of_notMem hz]
              · have hyNotSlab : y ∉ slab := by simp [slab, hyState]
                rw [Set.indicator_of_notMem hyNotSlab]
                simp [G, H, rateSet, state, terminal, hyState]
            · have hyNotSlab : y ∉ slab := by simp [slab, hyBulk]
              rw [Set.indicator_of_notMem hyNotSlab]
              simp [G, H, rateSet, state, terminal, hyBulk]
          · have hyNotSlab : y ∉ slab := by simp [slab, hyIoc]
            simp [hyIoc, hyNotSlab]
  have hswap :
      (∫ seen, ∫ y, G (seen, y) ∂timeLaw ∂seenLaw) =
        ∫ y, ∫ seen, G (seen, y) ∂seenLaw ∂timeLaw := by
    exact integral_integral_swap hGint
  have hfixed : ∀ y ∈ Ioc s t,
      (∫ seen, G (seen, y) ∂seenLaw) =
        ∫ sample,
          {sample : FiniteSample n |
            HistoryBeforeCoordinate sample lam x0 p0
                sourcePattern targetPattern history y ∧ sample ∈ E}.indicator
            (fun _ ↦ safeRate (Real.toNNReal (y - x0)) sample) sample
          ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
    intro y hyIoc
    have hx0y : x0 < y := hx0s.trans_lt hyIoc.1
    let F : (S → MarkedHeight) ×
        (feedbackUnseenFinset S → MarkedHeight) → ℝ := fun parts ↦
      let terminal := state parts.1
      {parts |
        finiteSampleSeenUnseenMerge S parts.1 parts.2 ∈ E ∧
          feedbackBulkRegion n width y
            (segmentCurve terminal.x terminal.p (terminal.slope lam) y) ∧
          terminal.x < y}.indicator
        (fun _ ↦ stateRate terminal y) parts
    have hFmeas : Measurable F := by
      have hseen' : Measurable fun parts : (S → MarkedHeight) ×
          (feedbackUnseenFinset S → MarkedHeight) ↦ parts.1 := measurable_fst
      have hunseen' : Measurable fun parts : (S → MarkedHeight) ×
          (feedbackUnseenFinset S → MarkedHeight) ↦ parts.2 := measurable_snd
      have hstate' : Measurable fun parts : (S → MarkedHeight) ×
          (feedbackUnseenFinset S → MarkedHeight) ↦ state parts.1 :=
        (measurable_feedbackScheduledStateOfSeen lam x0 p0
          sourcePattern targetPattern history).comp hseen'
      have hmerge' : Measurable fun parts : (S → MarkedHeight) ×
          (feedbackUnseenFinset S → MarkedHeight) ↦
          finiteSampleSeenUnseenMerge S parts.1 parts.2 :=
        (measurable_finiteSampleSeenUnseenMerge S).comp (hseen'.prodMk hunseen')
      have hcurve' : Measurable fun parts : (S → MarkedHeight) ×
          (feedbackUnseenFinset S → MarkedHeight) ↦
          segmentCurve (state parts.1).x (state parts.1).p
            ((state parts.1).slope lam) y := by
        simp only [segmentCurve]
        exact (FeedbackStepState.measurable_p.comp hstate').add
          ((FeedbackStepState.measurable_slope lam).comp hstate' |>.mul
            (measurable_const.sub (FeedbackStepState.measurable_x.comp hstate')))
      have hbulk' : MeasurableSet {parts : (S → MarkedHeight) ×
          (feedbackUnseenFinset S → MarkedHeight) |
          feedbackBulkRegion n width y
            (segmentCurve (state parts.1).x (state parts.1).p
              ((state parts.1).slope lam) y)} :=
        (feedbackBulkRegion_measurableSet n width).preimage
          (measurable_const.prodMk hcurve')
      have hset' : MeasurableSet {parts : (S → MarkedHeight) ×
          (feedbackUnseenFinset S → MarkedHeight) |
          finiteSampleSeenUnseenMerge S parts.1 parts.2 ∈ E ∧
            feedbackBulkRegion n width y
              (segmentCurve (state parts.1).x (state parts.1).p
                ((state parts.1).slope lam) y) ∧
            (state parts.1).x < y} :=
        (hE.preimage hmerge').inter (hbulk'.inter
          (measurableSet_lt (FeedbackStepState.measurable_x.comp hstate') measurable_const))
      exact (hstateRate.comp (hstate'.prodMk measurable_const)).indicator hset'
    have hFint : Integrable F (seenLaw.prod unseenLaw) := by
      apply Integrable.of_bound hFmeas.aestronglyMeasurable
        (feedbackBulkRateCap n width)
      exact Filter.Eventually.of_forall fun parts ↦ by
        by_cases hp : finiteSampleSeenUnseenMerge S parts.1 parts.2 ∈ E ∧
            feedbackBulkRegion n width y
              (segmentCurve (state parts.1).x (state parts.1).p
                ((state parts.1).slope lam) y) ∧
            (state parts.1).x < y
        · rw [show F parts = stateRate (state parts.1) y by simp [F, hp]]
          have hb := hstateRateBulk (state parts.1) y hp.2.1
          simpa [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
        · simp [F, hp, feedbackBulkRateCap_nonneg]
    have htransport := integral_historyAtCoordinate_eq_iterated
      lam x0 p0 sourcePattern targetPattern history y hFint
    have hGiter :
        (∫ seen, G (seen, y) ∂seenLaw) =
          ∫ seen, ∫ unseen,
            (historyAtCoordinateProductSet lam x0 p0
              sourcePattern targetPattern history y).indicator F (seen, unseen)
              ∂unseenLaw ∂seenLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun seen ↦ by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun unseen ↦ by
          change H ((seen, y), unseen) =
            (historyAtCoordinateProductSet lam x0 p0
              sourcePattern targetPattern history y).indicator F (seen, unseen)
          let C : Set ((S → MarkedHeight) ×
              (feedbackUnseenFinset S → MarkedHeight)) :=
            {parts |
              finiteSampleSeenUnseenMerge S parts.1 parts.2 ∈ E ∧
                feedbackBulkRegion n width y
                  (segmentCurve (state parts.1).x (state parts.1).p
                    ((state parts.1).slope lam) y) ∧
                (state parts.1).x < y}
          by_cases hc : HistoryAtCoordinate
              (finiteSampleSeenUnseenMerge S seen unseen) lam x0 p0
                sourcePattern targetPattern history y
          · have hprod : (seen, unseen) ∈ historyAtCoordinateProductSet
                lam x0 p0 sourcePattern targetPattern history y := by
              simpa [historyAtCoordinateProductSet, S] using hc
            by_cases hp : finiteSampleSeenUnseenMerge S seen unseen ∈ E ∧
                feedbackBulkRegion n width y
                  (segmentCurve (state seen).x (state seen).p
                    ((state seen).slope lam) y) ∧
                (state seen).x < y
            · have hz : ((seen, y), unseen) ∈ rateSet :=
                ⟨hc, hp.1, hp.2.1, hp.2.2⟩
              rw [Set.indicator_of_mem hprod]
              simp only [H, Set.indicator_of_mem hz]
              change stateRate (state seen) y =
                C.indicator (fun _ ↦ stateRate (state seen) y) (seen, unseen)
              have hpC : (seen, unseen) ∈ C := hp
              rw [Set.indicator_of_mem hpC]
            · have hz : ((seen, y), unseen) ∉ rateSet := by
                intro hz
                exact hp ⟨hz.2.1, hz.2.2.1, hz.2.2.2⟩
              rw [Set.indicator_of_mem hprod]
              simp only [H, Set.indicator_of_notMem hz]
              change (0 : ℝ) =
                C.indicator (fun _ ↦ stateRate (state seen) y) (seen, unseen)
              have hpC : (seen, unseen) ∉ C := hp
              rw [Set.indicator_of_notMem hpC]
          · have hprod : (seen, unseen) ∉ historyAtCoordinateProductSet
                lam x0 p0 sourcePattern targetPattern history y := by
              simpa [historyAtCoordinateProductSet, S] using hc
            have hz : ((seen, y), unseen) ∉ rateSet := by
              intro hz
              exact hc hz.1
            simp only [H, Set.indicator_of_notMem hz,
              Set.indicator_of_notMem hprod]
    have hseenToSample :
        (∫ seen, G (seen, y) ∂seenLaw) =
          ∫ sample,
            {sample : FiniteSample n |
              HistoryAtCoordinate sample lam x0 p0
                  sourcePattern targetPattern history y ∧
                sample ∈ E ∧
                feedbackBulkRegion n width y
                  (segmentCurve
                    (sample.scheduledState lam x0 p0
                      sourcePattern targetPattern history).x
                    (sample.scheduledState lam x0 p0
                      sourcePattern targetPattern history).p
                    ((sample.scheduledState lam x0 p0
                      sourcePattern targetPattern history).slope lam) y) ∧
                (sample.scheduledState lam x0 p0
                  sourcePattern targetPattern history).x < y}.indicator
              (fun _ ↦ stateRate
                (sample.scheduledState lam x0 p0
                  sourcePattern targetPattern history) y) sample
            ∂(finiteSampleLaw n : Measure (FiniteSample n)) := by
      rw [hGiter]
      change _ = ∫ sample,
        {sample : FiniteSample n |
          HistoryAtCoordinate sample lam x0 p0 sourcePattern targetPattern history y ∧
            sample ∈ E ∧
            feedbackBulkRegion n width y
              (segmentCurve
                (sample.scheduledState lam x0 p0
                  sourcePattern targetPattern history).x
                (sample.scheduledState lam x0 p0
                  sourcePattern targetPattern history).p
                ((sample.scheduledState lam x0 p0
                  sourcePattern targetPattern history).slope lam) y) ∧
            (sample.scheduledState lam x0 p0
              sourcePattern targetPattern history).x < y}.indicator
          (fun _ ↦ stateRate
            (sample.scheduledState lam x0 p0
              sourcePattern targetPattern history) y) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n))
      rw [← htransport]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun sample ↦ by
        have hs := scheduledState_eq_feedbackScheduledStateOfSeen_feedbackSeenTuple
          sample lam x0 p0 sourcePattern targetPattern history
        let A : Set (FiniteSample n) :=
          {sample | HistoryAtCoordinate sample lam x0 p0
            sourcePattern targetPattern history y}
        let B : Set (FiniteSample n) :=
          {sample |
            HistoryAtCoordinate sample lam x0 p0
                sourcePattern targetPattern history y ∧
              sample ∈ E ∧
              feedbackBulkRegion n width y
                (segmentCurve
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history).x
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history).p
                  ((sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history).slope lam) y) ∧
              (sample.scheduledState lam x0 p0
                sourcePattern targetPattern history).x < y}
        let parts :=
          (feedbackSeenTuple S sample, feedbackUnseenTuple S sample)
        let C : Set ((S → MarkedHeight) ×
            (feedbackUnseenFinset S → MarkedHeight)) :=
          {parts |
            finiteSampleSeenUnseenMerge S parts.1 parts.2 ∈ E ∧
              feedbackBulkRegion n width y
                (segmentCurve (state parts.1).x (state parts.1).p
                  ((state parts.1).slope lam) y) ∧
              (state parts.1).x < y}
        change A.indicator (fun _ ↦ F parts) sample =
          B.indicator (fun _ ↦ stateRate
            (sample.scheduledState lam x0 p0
              sourcePattern targetPattern history) y) sample
        by_cases hc : HistoryAtCoordinate sample lam x0 p0
            sourcePattern targetPattern history y
        · by_cases hp : sample ∈ E ∧
              feedbackBulkRegion n width y
                (segmentCurve
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history).x
                  (sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history).p
                  ((sample.scheduledState lam x0 p0
                    sourcePattern targetPattern history).slope lam) y) ∧
              (sample.scheduledState lam x0 p0
                sourcePattern targetPattern history).x < y
          · have hA : sample ∈ A := hc
            have hB : sample ∈ B := ⟨hc, hp⟩
            have hC : parts ∈ C := by
              simpa [parts, C, state, S, hs] using hp
            rw [Set.indicator_of_mem hA, Set.indicator_of_mem hB]
            change C.indicator (fun _ ↦ stateRate (state parts.1) y) parts =
              stateRate (sample.scheduledState lam x0 p0
                sourcePattern targetPattern history) y
            rw [Set.indicator_of_mem hC]
            simpa [parts, state, S] using
              congrArg (fun q : FeedbackStepState n ↦ stateRate q y) hs.symm
          · have hA : sample ∈ A := hc
            have hB : sample ∉ B := by
              intro hB
              exact hp hB.2
            have hC : parts ∉ C := by
              intro hC
              apply hp
              simpa [parts, C, state, S, hs] using hC
            rw [Set.indicator_of_mem hA, Set.indicator_of_notMem hB]
            change C.indicator (fun _ ↦ stateRate (state parts.1) y) parts = 0
            rw [Set.indicator_of_notMem hC]
        · have hA : sample ∉ A := hc
          have hB : sample ∉ B := by
            intro hB
            exact hc hB.1
          rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB]
    rw [hseenToSample]
    let index : HistoryCellIndex n :=
      { sourcePattern := sourcePattern
        targetPattern := targetPattern
        history := history
        history_length_le := hhistory }
    have hcell := historyBeforeCell_ae_eq_historyCell
      (p0 := p0) index hlam0 hlamHalf hx0y
    apply integral_congr_ae
    filter_upwards [hcell] with sample hsampleCell
    have hcellIff :
        HistoryBeforeCoordinate sample lam x0 p0
            sourcePattern targetPattern history y ↔
          HistoryAtCoordinate sample lam x0 p0
            sourcePattern targetPattern history y := by
      change HistoryBeforeCoordinate sample lam x0 p0
          sourcePattern targetPattern history y =
        HistoryAtCoordinate sample lam x0 p0
          sourcePattern targetPattern history y at hsampleCell
      exact Iff.of_eq hsampleCell
    by_cases hbefore : HistoryBeforeCoordinate sample lam x0 p0
        sourcePattern targetPattern history y
    · have hat : HistoryAtCoordinate sample lam x0 p0
          sourcePattern targetPattern history y := hcellIff.mp hbefore
      have hterminalLt : (sample.scheduledState lam x0 p0
          sourcePattern targetPattern history).x < y := hbefore.1.2.1
      by_cases hsampleE : sample ∈ E
      · by_cases hsampleBulk : feedbackBulkRegion n width y
          (segmentCurve
            (sample.scheduledState lam x0 p0
              sourcePattern targetPattern history).x
            (sample.scheduledState lam x0 p0
              sourcePattern targetPattern history).p
            ((sample.scheduledState lam x0 p0
              sourcePattern targetPattern history).slope lam) y)
        · have hu : FiniteSample.elapsedFeedbackCoordinate x0
              (Real.toNNReal (y - x0)) = y := by
            change x0 + max (y - x0) 0 = y
            rw [max_eq_left (sub_nonneg.mpr hx0y.le)]
            ring
          have hsafe := hsafeRateBulk sample y hx0y hbefore
            (Real.toNNReal (y - x0)) hu hsampleBulk
          simp [hat, hbefore, hsampleE, hsampleBulk, hterminalLt, hsafe]
        · have hu : FiniteSample.elapsedFeedbackCoordinate x0
              (Real.toNNReal (y - x0)) = y := by
            change x0 + max (y - x0) 0 = y
            rw [max_eq_left (sub_nonneg.mpr hx0y.le)]
            ring
          have hsafe := hsafeRateNotBulk sample y hx0y hbefore
            (Real.toNNReal (y - x0)) hu hsampleBulk
          simp [hat, hbefore, hsampleE, hsampleBulk, hsafe]
      · simp [hbefore, hsampleE]
    · have hnotAt : ¬ HistoryAtCoordinate sample lam x0 p0
          sourcePattern targetPattern history y := fun h ↦ hbefore (hcellIff.mpr h)
      simp [hbefore, hnotAt]
  calc
    historyNestedRateMassOf stateRate width lam x0 p0 s t
        sourcePattern targetPattern history E =
        ∫ seen, ∫ y, G (seen, y) ∂timeLaw ∂seenLaw := hbranchToG
    _ = ∫ y, ∫ seen, G (seen, y) ∂seenLaw ∂timeLaw := hswap
    _ = ∫ y in Ioc s t, ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0
              sourcePattern targetPattern history y ∧ sample ∈ E}.indicator
          (fun _ ↦ safeRate (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y hy
      exact hfixed y hy

/-- A fixed source history's nested affine rate mass is the time/sample integral of the actual
safe source bulk rate on its strict pre-jump cell. -/
theorem sourceHistoryNestedRateMass_eq_strictSafeRate
    {width lam x0 p0 s t : ℝ}
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hhistory : history.length ≤ 2 * n)
    (E : Set (FiniteSample n)) (hE : MeasurableSet E)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hwidth : 0 < width) (hx0s : x0 ≤ s) :
    sourceHistoryNestedRateMass width lam x0 p0 s t
        sourcePattern targetPattern history E =
      ∫ y in Ioc s t, ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0
              sourcePattern targetPattern history y ∧ sample ∈ E}.indicator
          (fun _ ↦ safeSourceBulkRate hlam0 hlamHalf width x0 p0
            (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume := by
  simpa [sourceHistoryNestedRateMass, historyNestedRateMassOf] using
    historyNestedRateMassOf_eq_strictSafeRate
      sourcePattern targetPattern history hhistory E hE hlam0 hlamHalf hwidth hx0s
      (fun state y ↦ FeedbackStepState.sourceUnclippedStateRateAt lam state y)
      (measurable_sourceUnclippedStateRateAt_joint lam)
      (fun state y hbulk ↦
        sourceUnclippedStateRateAt_mem_Icc_of_bulk state hlam0 hlamHalf hwidth hbulk)
      (fun u sample ↦ safeSourceBulkRate hlam0 hlamHalf width x0 p0 u sample)
      (fun sample y hxy hbefore u hu hbulk ↦
        safeSourceBulkRate_eq_sourceUnclippedStateRateAt_of_historyBeforeCoordinate_stateBulk
          sample hlam0 hlamHalf hwidth hxy hbefore u hu hbulk)
      (fun sample y hxy hbefore u hu hnotBulk ↦
        safeSourceBulkRate_eq_zero_of_historyBeforeCoordinate_not_stateBulk
          sample hlam0 hlamHalf hxy hbefore u hu hnotBulk)

/-- Target analogue of `sourceHistoryNestedRateMass_eq_strictSafeRate`. -/
theorem targetHistoryNestedRateMass_eq_strictSafeRate
    {width lam x0 p0 s t : ℝ}
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n))
    (hhistory : history.length ≤ 2 * n)
    (E : Set (FiniteSample n)) (hE : MeasurableSet E)
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hwidth : 0 < width) (hx0s : x0 ≤ s) :
    targetHistoryNestedRateMass width lam x0 p0 s t
        sourcePattern targetPattern history E =
      ∫ y in Ioc s t, ∫ sample,
        {sample : FiniteSample n |
          HistoryBeforeCoordinate sample lam x0 p0
              sourcePattern targetPattern history y ∧ sample ∈ E}.indicator
          (fun _ ↦ safeTargetBulkRate hlam0 hlamHalf width x0 p0
            (Real.toNNReal (y - x0)) sample) sample
        ∂(finiteSampleLaw n : Measure (FiniteSample n)) ∂volume := by
  simpa [targetHistoryNestedRateMass, historyNestedRateMassOf] using
    historyNestedRateMassOf_eq_strictSafeRate
      sourcePattern targetPattern history hhistory E hE hlam0 hlamHalf hwidth hx0s
      (fun state y ↦ FeedbackStepState.targetUnclippedStateRateAt lam state y)
      (measurable_targetUnclippedStateRateAt_joint lam)
      (fun state y hbulk ↦
        targetUnclippedStateRateAt_mem_Icc_of_bulk state hlam0 hlamHalf hwidth hbulk)
      (fun u sample ↦ safeTargetBulkRate hlam0 hlamHalf width x0 p0 u sample)
      (fun sample y hxy hbefore u hu hbulk ↦
        safeTargetBulkRate_eq_targetUnclippedStateRateAt_of_historyBeforeCoordinate_stateBulk
          sample hlam0 hlamHalf hwidth hxy hbefore u hu hbulk)
      (fun sample y hxy hbefore u hu hnotBulk ↦
        safeTargetBulkRate_eq_zero_of_historyBeforeCoordinate_not_stateBulk
          sample hlam0 hlamHalf hxy hbefore u hu hnotBulk)

end OTSelector
