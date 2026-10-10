import OTSelector.Feedback.FiniteEventBulkGlobalBranchSum
import OTSelector.Feedback.FiniteHistoryBulkAllLabelMeasurable

/-!
# Integrated finite bulk-count increments

The pathwise history-cell decomposition of a thinned count can be integrated under the
canonical finite-sample law.  The only null-set input is the already established almost-sure
no-feedback-tie statement.  The right-hand side is the finite sum of the real masses of the
measurable history and next-label events; no compensator conclusion is asserted here.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace OTSelector

variable {n : ℕ}

open CountingProcess FiniteSample

private lemma setIntegral_indicator_one_eq_measureReal_inter
    {μ : Measure (FiniteSample n)} {E A : Set (FiniteSample n)}
    (hA : MeasurableSet A) :
    (∫ sample in E, A.indicator (fun _ ↦ (1 : ℝ)) sample ∂μ) =
      μ.real (E ∩ A) := by
  rw [setIntegral_indicator hA, setIntegral_const]
  simp [smul_eq_mul]

private lemma source_bulk_cell_event_integral
    {lam B x0 p0 r : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxr : x0 ≤ r)
    (E : Set (FiniteSample n))
    (_hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (i : Fin n) :
    (∫ sample in E,
      ({sample : FiniteSample n |
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
          feedbackUnseenTuple
              (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet sourcePattern targetPattern history) (Sum.inl i)}).indicator
        (fun _ ↦ (1 : ℝ)) sample ∂(finiteSampleLaw n)) =
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample : FiniteSample n |
          HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
            feedbackUnseenTuple
                (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∈
              feedbackBulkNextEventSetOfLabel B lam
                (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
                (x0 + (s : ℝ)) (x0 + (t : ℝ))
                (feedbackTerminalLabelSet sourcePattern targetPattern history) (Sum.inl i) ∧
            sample ∈ E} := by
  let A : Set (FiniteSample n) := {sample : FiniteSample n |
    HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      feedbackUnseenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∈
        feedbackBulkNextEventSetOfLabel B lam
          (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
          (x0 + (s : ℝ)) (x0 + (t : ℝ))
          (feedbackTerminalLabelSet sourcePattern targetPattern history) (Sum.inl i)}
  have hA : MeasurableSet A := by
    simpa [A] using
      (measurableSet_finiteSample_sourceBulk_history_allLabel_event
        (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0) (r := r)
        (s := (x0 + (s : ℝ))) (t := (x0 + (t : ℝ)))
        hlam0 hlamHalf sourcePattern targetPattern history hxr
        (Set.univ : Set (FiniteSample n)) MeasurableSet.univ i)
  have hmass := setIntegral_indicator_one_eq_measureReal_inter
    (n := n) (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (E := E) (A := A) hA
  rw [show E ∩ A = A ∩ E by exact Set.inter_comm _ _] at hmass
  have hset :
      {sample : FiniteSample n |
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
          feedbackUnseenTuple
              (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet sourcePattern targetPattern history) (Sum.inl i) ∧
      sample ∈ E} = A ∩ E := by
    ext sample
    simp [A, and_assoc, and_left_comm, and_comm]
  rw [hset]
  simpa [A] using hmass

private lemma target_bulk_cell_event_integral
    {lam B x0 p0 r : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxr : x0 ≤ r)
    (E : Set (FiniteSample n))
    (_hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (sourcePattern targetPattern : Finset (Fin n))
    (history : List (FeedbackLabel n)) (j : Fin n) :
    (∫ sample in E,
      ({sample : FiniteSample n |
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
          feedbackUnseenTuple
              (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet sourcePattern targetPattern history) (Sum.inr j)}).indicator
        (fun _ ↦ (1 : ℝ)) sample ∂(finiteSampleLaw n)) =
      (finiteSampleLaw n : Measure (FiniteSample n)).real
        {sample : FiniteSample n |
          HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
            feedbackUnseenTuple
                (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∈
              feedbackBulkNextEventSetOfLabel B lam
                (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
                (x0 + (s : ℝ)) (x0 + (t : ℝ))
                (feedbackTerminalLabelSet sourcePattern targetPattern history) (Sum.inr j) ∧
            sample ∈ E} := by
  let A : Set (FiniteSample n) := {sample : FiniteSample n |
    HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
      feedbackUnseenTuple
          (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∈
        feedbackBulkNextEventSetOfLabel B lam
          (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
          (x0 + (s : ℝ)) (x0 + (t : ℝ))
          (feedbackTerminalLabelSet sourcePattern targetPattern history) (Sum.inr j)}
  have hA : MeasurableSet A := by
    simpa [A] using
      (measurableSet_finiteSample_targetBulk_history_allLabel_event
        (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0) (r := r)
        (s := (x0 + (s : ℝ))) (t := (x0 + (t : ℝ)))
        hlam0 hlamHalf sourcePattern targetPattern history hxr
        (Set.univ : Set (FiniteSample n)) MeasurableSet.univ j)
  have hmass := setIntegral_indicator_one_eq_measureReal_inter
    (n := n) (μ := (finiteSampleLaw n : Measure (FiniteSample n)))
    (E := E) (A := A) hA
  rw [show E ∩ A = A ∩ E by exact Set.inter_comm _ _] at hmass
  have hset :
      {sample : FiniteSample n |
        HistoryBranch sample lam x0 p0 sourcePattern targetPattern history ∧
          feedbackUnseenTuple
              (feedbackTerminalLabelSet sourcePattern targetPattern history) sample ∈
            feedbackBulkNextEventSetOfLabel B lam
              (sample.scheduledState lam x0 p0 sourcePattern targetPattern history)
              (x0 + (s : ℝ)) (x0 + (t : ℝ))
              (feedbackTerminalLabelSet sourcePattern targetPattern history) (Sum.inr j) ∧
      sample ∈ E} = A ∩ E := by
    ext sample
    simp [A, and_assoc, and_left_comm, and_comm]
  rw [hset]
  simpa [A] using hmass

theorem finiteEventCountThinned_source_sub_setIntegral_eq_historyCellIndex_nextLabel_real_sum
    {lam B x0 p0 r : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxr : x0 ≤ r)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hst : s ≤ t) :
    (∫ sample in E,
      (((finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample -
        finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample : ℕ) : ℝ))
        ∂(finiteSampleLaw n)) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∑ i : Fin n,
            (finiteSampleLaw n : Measure (FiniteSample n)).real
              {sample : FiniteSample n |
                HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                    index.history ∧
                  feedbackUnseenTuple
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) sample ∈
                    feedbackBulkNextEventSetOfLabel B lam
                      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                        index.history)
                      (x0 + (s : ℝ)) (x0 + (t : ℝ))
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) (Sum.inl i) ∧
                  sample ∈ E}
        else 0 := by
  classical
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  have hpath : ∀ᵐ sample ∂(μ.restrict E),
      (((finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample -
        finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample : ℕ) : ℝ)) =
        ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∑ i : Fin n,
              ({sample : FiniteSample n |
                HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                    index.history ∧
                  feedbackUnseenTuple
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) sample ∈
                    feedbackBulkNextEventSetOfLabel B lam
                      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                        index.history)
                      (x0 + (s : ℝ)) (x0 + (t : ℝ))
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) (Sum.inl i)}).indicator
                (fun _ ↦ (1 : ℝ)) sample
          else 0 := by
    filter_upwards [ae_restrict_of_ae
      (finiteSampleLaw_noFeedbackTies_ae (n := n) (x0 := x0) (p0 := p0)
        hlam0 hlamHalf)] with sample hgood
    have hnat := finiteEventCountThinned_source_sub_eq_historyCellIndex_nextLabel_sum
      (B := B) sample hlam0 hlamHalf hgood hst
    have hreal := congrArg (fun z : ℕ ↦ (z : ℝ)) hnat
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hreal
    convert hreal using 1
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro index hi
    by_cases hlen : index.history.length = m.val
    · by_cases hbranch :
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
      · simp [hlen, hbranch, Set.indicator]
      · simp [hlen, hbranch, Set.indicator]
    · simp [hlen]
  have hint :
      (∫ sample in E,
        (((finiteEventCountThinned
            (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample -
          finiteEventCountThinned
            (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample : ℕ) : ℝ))
          ∂μ) =
      ∫ sample in E,
        (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∑ i : Fin n,
              ({sample : FiniteSample n |
                HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                    index.history ∧
                  feedbackUnseenTuple
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) sample ∈
                    feedbackBulkNextEventSetOfLabel B lam
                      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                        index.history)
                      (x0 + (s : ℝ)) (x0 + (t : ℝ))
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) (Sum.inl i)}).indicator
                (fun _ ↦ (1 : ℝ)) sample
          else 0) ∂μ := by
    exact integral_congr_ae hpath
  rw [hint]
  have hcellint : ∀ m : Fin (2 * n), ∀ index : HistoryCellIndex n,
      Integrable (fun sample : FiniteSample n ↦
        if index.history.length = m.val then
          ∑ i : Fin n,
            ({sample : FiniteSample n |
              HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                  index.history ∧
                feedbackUnseenTuple
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) sample ∈
                  feedbackBulkNextEventSetOfLabel B lam
                    (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                      index.history)
                    (x0 + (s : ℝ)) (x0 + (t : ℝ))
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) (Sum.inl i)}).indicator
              (fun _ ↦ (1 : ℝ)) sample
        else 0) (μ.restrict E) := by
    intro m index
    by_cases hlen : index.history.length = m.val
    · simp only [ite_eq_left hlen]
      refine integrable_finsetSum (μ := μ.restrict E)
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun i sample ↦
          ({sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                index.history ∧
              feedbackUnseenTuple
                  (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                    index.history) sample ∈
                feedbackBulkNextEventSetOfLabel B lam
                  (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                    index.history)
                  (x0 + (s : ℝ)) (x0 + (t : ℝ))
                  (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                    index.history) (Sum.inl i)}).indicator
            (fun _ ↦ (1 : ℝ)) sample) ?_
      intro i hi
      exact ((integrable_const (1 : ℝ)).indicator
        (by
          simpa using
            (measurableSet_finiteSample_sourceBulk_history_allLabel_event
              (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0) (r := r)
              (s := (x0 + (s : ℝ))) (t := (x0 + (t : ℝ)))
              hlam0 hlamHalf index.sourcePattern index.targetPattern index.history hxr
              (Set.univ : Set (FiniteSample n)) MeasurableSet.univ i)))
    · simp only [ite_eq_right hlen]
      exact integrable_zero (FiniteSample n) ℝ (μ.restrict E)
  have hsum_m := integral_finsetSum (μ := μ.restrict E)
    (s := (Finset.univ : Finset (Fin (2 * n))))
    (fun m hm ↦ by
      refine integrable_finsetSum (μ := μ.restrict E)
        (s := (Finset.univ : Finset (HistoryCellIndex n)))
        (f := fun index sample ↦
          if index.history.length = m.val then
            ∑ i : Fin n,
              ({sample : FiniteSample n |
                HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                    index.history ∧
                  feedbackUnseenTuple
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) sample ∈
                    feedbackBulkNextEventSetOfLabel B lam
                      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                        index.history)
                      (x0 + (s : ℝ)) (x0 + (t : ℝ))
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) (Sum.inl i)}).indicator
                (fun _ ↦ (1 : ℝ)) sample
          else 0) ?_
      intro index hi
      exact hcellint m index)
  rw [hsum_m]
  apply Finset.sum_congr rfl
  intro m hm
  have hsum_index := integral_finsetSum (μ := μ.restrict E)
    (s := (Finset.univ : Finset (HistoryCellIndex n)))
    (fun index hi ↦ hcellint m index)
  rw [hsum_index]
  apply Finset.sum_congr rfl
  intro index hi
  by_cases hlen : index.history.length = m.val
  · simp only [ite_eq_left hlen]
    have hsum_label := integral_finsetSum (μ := μ.restrict E)
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun i sample ↦
        ({sample : FiniteSample n |
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history ∧
            feedbackUnseenTuple
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
                sample ∈
              feedbackBulkNextEventSetOfLabel B lam
                (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                  index.history)
                (x0 + (s : ℝ)) (x0 + (t : ℝ))
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
                (Sum.inl i)}).indicator (fun _ ↦ (1 : ℝ)) sample)
      (fun i hi ↦ by
        exact (integrable_const (1 : ℝ)).indicator (by
          simpa using
            (measurableSet_finiteSample_sourceBulk_history_allLabel_event
              (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0) (r := r)
              (s := (x0 + (s : ℝ))) (t := (x0 + (t : ℝ)))
              hlam0 hlamHalf index.sourcePattern index.targetPattern index.history hxr
              (Set.univ : Set (FiniteSample n)) MeasurableSet.univ i)))
    rw [hsum_label]
    apply Finset.sum_congr rfl
    intro i hi
    exact source_bulk_cell_event_integral hlam0 hlamHalf hxr E hE
      index.sourcePattern index.targetPattern index.history i
  · simp only [ite_eq_right hlen]
    simp

theorem finiteEventCountThinned_target_sub_setIntegral_eq_historyCellIndex_nextLabel_real_sum
    {lam B x0 p0 r : ℝ} {s t : ℝ≥0}
    (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (hxr : x0 ≤ r)
    (E : Set (FiniteSample n))
    (hE : MeasurableSet[
      FiniteSample.rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0
        ⟨r - x0, sub_nonneg.mpr hxr⟩] E)
    (hst : s ≤ t) :
    (∫ sample in E,
      (((finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample -
        finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample : ℕ) : ℝ))
        ∂(finiteSampleLaw n)) =
      ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
        if index.history.length = m.val then
          ∑ j : Fin n,
            (finiteSampleLaw n : Measure (FiniteSample n)).real
              {sample : FiniteSample n |
                HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                    index.history ∧
                  feedbackUnseenTuple
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) sample ∈
                    feedbackBulkNextEventSetOfLabel B lam
                      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                        index.history)
                      (x0 + (s : ℝ)) (x0 + (t : ℝ))
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) (Sum.inr j) ∧
                  sample ∈ E}
        else 0 := by
  classical
  let μ : Measure (FiniteSample n) := finiteSampleLaw n
  have hpath : ∀ᵐ sample ∂(μ.restrict E),
      (((finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample -
        finiteEventCountThinned
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample : ℕ) : ℝ)) =
        ∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∑ j : Fin n,
              ({sample : FiniteSample n |
                HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                    index.history ∧
                  feedbackUnseenTuple
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) sample ∈
                    feedbackBulkNextEventSetOfLabel B lam
                      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                        index.history)
                      (x0 + (s : ℝ)) (x0 + (t : ℝ))
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) (Sum.inr j)}).indicator
                (fun _ ↦ (1 : ℝ)) sample
          else 0 := by
    filter_upwards [ae_restrict_of_ae
      (finiteSampleLaw_noFeedbackTies_ae (n := n) (x0 := x0) (p0 := p0)
        hlam0 hlamHalf)] with sample hgood
    have hnat := finiteEventCountThinned_target_sub_eq_historyCellIndex_nextLabel_sum
      (B := B) sample hlam0 hlamHalf hgood hst
    have hreal := congrArg (fun z : ℕ ↦ (z : ℝ)) hnat
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hreal
    convert hreal using 1
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro index hi
    by_cases hlen : index.history.length = m.val
    · by_cases hbranch :
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history
      · simp [hlen, hbranch, Set.indicator]
      · simp [hlen, hbranch, Set.indicator]
    · simp [hlen]
  have hint :
      (∫ sample in E,
        (((finiteEventCountThinned
            (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample -
          finiteEventCountThinned
            (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample : ℕ) : ℝ))
          ∂μ) =
      ∫ sample in E,
        (∑ m : Fin (2 * n), ∑ index : HistoryCellIndex n,
          if index.history.length = m.val then
            ∑ j : Fin n,
              ({sample : FiniteSample n |
                HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                    index.history ∧
                  feedbackUnseenTuple
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) sample ∈
                    feedbackBulkNextEventSetOfLabel B lam
                      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                        index.history)
                      (x0 + (s : ℝ)) (x0 + (t : ℝ))
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) (Sum.inr j)}).indicator
                (fun _ ↦ (1 : ℝ)) sample
          else 0) ∂μ := by
    exact integral_congr_ae hpath
  rw [hint]
  have hcellint : ∀ m : Fin (2 * n), ∀ index : HistoryCellIndex n,
      Integrable (fun sample : FiniteSample n ↦
        if index.history.length = m.val then
          ∑ j : Fin n,
            ({sample : FiniteSample n |
              HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                  index.history ∧
                feedbackUnseenTuple
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) sample ∈
                  feedbackBulkNextEventSetOfLabel B lam
                    (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                      index.history)
                    (x0 + (s : ℝ)) (x0 + (t : ℝ))
                    (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                      index.history) (Sum.inr j)}).indicator
              (fun _ ↦ (1 : ℝ)) sample
        else 0) (μ.restrict E) := by
    intro m index
    by_cases hlen : index.history.length = m.val
    · simp only [ite_eq_left hlen]
      refine integrable_finsetSum (μ := μ.restrict E)
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun j sample ↦
          ({sample : FiniteSample n |
            HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                index.history ∧
              feedbackUnseenTuple
                  (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                    index.history) sample ∈
                feedbackBulkNextEventSetOfLabel B lam
                  (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                    index.history)
                  (x0 + (s : ℝ)) (x0 + (t : ℝ))
                  (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                    index.history) (Sum.inr j)}).indicator
            (fun _ ↦ (1 : ℝ)) sample) ?_
      intro j hj
      exact ((integrable_const (1 : ℝ)).indicator
        (by
          simpa using
            (measurableSet_finiteSample_targetBulk_history_allLabel_event
              (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0) (r := r)
              (s := (x0 + (s : ℝ))) (t := (x0 + (t : ℝ)))
              hlam0 hlamHalf index.sourcePattern index.targetPattern index.history hxr
              (Set.univ : Set (FiniteSample n)) MeasurableSet.univ j)))
    · simp only [ite_eq_right hlen]
      exact integrable_zero (FiniteSample n) ℝ (μ.restrict E)
  have hsum_m := integral_finsetSum (μ := μ.restrict E)
    (s := (Finset.univ : Finset (Fin (2 * n))))
    (fun m hm ↦ by
      refine integrable_finsetSum (μ := μ.restrict E)
        (s := (Finset.univ : Finset (HistoryCellIndex n)))
        (f := fun index sample ↦
          if index.history.length = m.val then
            ∑ j : Fin n,
              ({sample : FiniteSample n |
                HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern
                    index.history ∧
                  feedbackUnseenTuple
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) sample ∈
                    feedbackBulkNextEventSetOfLabel B lam
                      (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                        index.history)
                      (x0 + (s : ℝ)) (x0 + (t : ℝ))
                      (feedbackTerminalLabelSet index.sourcePattern index.targetPattern
                        index.history) (Sum.inr j)}).indicator
                (fun _ ↦ (1 : ℝ)) sample
          else 0) ?_
      intro index hi
      exact hcellint m index)
  rw [hsum_m]
  apply Finset.sum_congr rfl
  intro m hm
  have hsum_index := integral_finsetSum (μ := μ.restrict E)
    (s := (Finset.univ : Finset (HistoryCellIndex n)))
    (fun index hi ↦ hcellint m index)
  rw [hsum_index]
  apply Finset.sum_congr rfl
  intro index hi
  by_cases hlen : index.history.length = m.val
  · simp only [ite_eq_left hlen]
    have hsum_label := integral_finsetSum (μ := μ.restrict E)
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun j sample ↦
        ({sample : FiniteSample n |
          HistoryBranch sample lam x0 p0 index.sourcePattern index.targetPattern index.history ∧
            feedbackUnseenTuple
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
                sample ∈
              feedbackBulkNextEventSetOfLabel B lam
                (sample.scheduledState lam x0 p0 index.sourcePattern index.targetPattern
                  index.history)
                (x0 + (s : ℝ)) (x0 + (t : ℝ))
                (feedbackTerminalLabelSet index.sourcePattern index.targetPattern index.history)
                (Sum.inr j)}).indicator (fun _ ↦ (1 : ℝ)) sample)
      (fun j hj ↦ by
        exact (integrable_const (1 : ℝ)).indicator (by
          simpa using
            (measurableSet_finiteSample_targetBulk_history_allLabel_event
              (n := n) (width := B) (lam := lam) (x0 := x0) (p0 := p0) (r := r)
              (s := (x0 + (s : ℝ))) (t := (x0 + (t : ℝ)))
              hlam0 hlamHalf index.sourcePattern index.targetPattern index.history hxr
              (Set.univ : Set (FiniteSample n)) MeasurableSet.univ j)))
    rw [hsum_label]
    apply Finset.sum_congr rfl
    intro j hj
    exact target_bulk_cell_event_integral hlam0 hlamHalf hxr E hE
      index.sourcePattern index.targetPattern index.history j
  · simp only [ite_eq_right hlen]
    simp

end OTSelector
