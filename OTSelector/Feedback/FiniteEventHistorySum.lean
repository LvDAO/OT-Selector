import OTSelector.Feedback.RevealedCounting
import OTSelector.Feedback.FiniteHistoryCoverage

/-!
# Finite event-history sums

This file contains only deterministic finite bookkeeping.  A label which is inserted into a
feedback state's `newSource` (respectively `newTarget`) set cannot be inserted again at a later
step, because the seen sets are monotone.  Consequently an interval indicator for an event time
can be rewritten as a finite sum over feedback knots.  The no-tie hypothesis is used only for the
safe event-time fallback and for the corresponding count identities.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ}

/-! ## The finite branch behind an active no-tie step -/

theorem exists_historyBranch_of_noFeedbackTies_of_active
    (sample : FiniteSample n) (lam x0 p0 : ℝ)
    {m : ℕ} (hm : m < 2 * n)
    (hNoTie : sample.NoFeedbackTies lam x0 p0)
    (hactive : ((feedbackState sample lam x0 p0 m).candidates sample lam).Nonempty) :
    ∃ history : List (FeedbackLabel n),
      history.length = m ∧
      HistoryBranch sample lam x0 p0
        (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history ∧
      feedbackState sample lam x0 p0 m =
        sample.scheduledState lam x0 p0
          (sample.initialSeenSource x0 p0) (sample.initialSeenTarget x0 p0) history := by
  classical
  let sourcePattern := sample.initialSeenSource x0 p0
  let targetPattern := sample.initialSeenTarget x0 p0
  have hinit : sample.initialFeedbackState x0 p0 =
      forcedInitialState x0 p0 sourcePattern targetPattern := by
    simp [sourcePattern, targetPattern, initialFeedbackState, initialFeedbackCurrent,
      forcedInitialState]
  have hactive_prior : ∀ k < m,
      ((feedbackState sample lam x0 p0 k).candidates sample lam).Nonempty := by
    intro k hk
    by_contra hnonempty
    have hzero : (feedbackState sample lam x0 p0 k).candidates sample lam = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hstate : feedbackState sample lam x0 p0 m =
        feedbackState sample lam x0 p0 k := by
      simpa [Nat.add_sub_of_le (Nat.le_of_lt hk)] using
        sample.feedbackState_eq_of_candidates_eq_empty lam x0 p0 k hzero (m - k)
    have hzero_m : (feedbackState sample lam x0 p0 m).candidates sample lam = ∅ := by
      rw [hstate]
      exact hzero
    rw [hzero_m] at hactive
    exact Finset.not_nonempty_empty hactive
  have hprior : ∀ k < m,
      ((feedbackState sample lam x0 p0 k).newSource sample lam).card +
        ((feedbackState sample lam x0 p0 k).newTarget sample lam).card ≤ 1 := by
    intro k hk
    exact hNoTie k (lt_trans hk hm)
  obtain ⟨history, hlen, hforced, hstate⟩ :=
    sample.exists_forced_history_of_prior_active lam x0 p0 sourcePattern targetPattern
      hinit m hactive_prior hprior
  refine ⟨history, hlen, ?_, ?_⟩
  · exact ⟨hinit, hforced⟩
  · simpa [sourcePattern, targetPattern] using hstate

/-! ## A label is inserted at most once -/

theorem newSource_step_unique
    (sample : FiniteSample n) (lam x0 p0 : ℝ) (i : Fin n)
    {m r : Fin (2 * n)}
    (hm : i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam)
    (hr : i ∈ (feedbackState sample lam x0 p0 r.val).newSource sample lam) :
    m = r := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hmr | hrm
  · have hseen : i ∈ (feedbackState sample lam x0 p0 (m.val + 1)).seenSource :=
      (sample.mem_feedbackState_seenSource_iff lam x0 p0 i (m.val + 1)).mpr
        (Or.inr ⟨m.val, by omega, hm⟩)
    have hseen' : i ∈ (feedbackState sample lam x0 p0 r.val).seenSource :=
      sample.mem_feedbackState_seenSource_mono lam x0 p0 i
        (Nat.succ_le_of_lt hmr) hseen
    exact (Finset.disjoint_left.mp
      (FeedbackStepState.newSource_disjoint_seenSource sample lam
        (feedbackState sample lam x0 p0 r.val))) hr hseen'
  · have hseen : i ∈ (feedbackState sample lam x0 p0 (r.val + 1)).seenSource :=
      (sample.mem_feedbackState_seenSource_iff lam x0 p0 i (r.val + 1)).mpr
        (Or.inr ⟨r.val, by omega, hr⟩)
    have hseen' : i ∈ (feedbackState sample lam x0 p0 m.val).seenSource :=
      sample.mem_feedbackState_seenSource_mono lam x0 p0 i
        (Nat.succ_le_of_lt hrm) hseen
    exact (Finset.disjoint_left.mp
      (FeedbackStepState.newSource_disjoint_seenSource sample lam
        (feedbackState sample lam x0 p0 m.val))) hm hseen'

theorem newTarget_step_unique
    (sample : FiniteSample n) (lam x0 p0 : ℝ) (j : Fin n)
    {m r : Fin (2 * n)}
    (hm : j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam)
    (hr : j ∈ (feedbackState sample lam x0 p0 r.val).newTarget sample lam) :
    m = r := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hmr | hrm
  · have hseen : j ∈ (feedbackState sample lam x0 p0 (m.val + 1)).seenTarget :=
      (sample.mem_feedbackState_seenTarget_iff lam x0 p0 j (m.val + 1)).mpr
        (Or.inr ⟨m.val, by omega, hm⟩)
    have hseen' : j ∈ (feedbackState sample lam x0 p0 r.val).seenTarget :=
      sample.mem_feedbackState_seenTarget_mono lam x0 p0 j
        (Nat.succ_le_of_lt hmr) hseen
    exact (Finset.disjoint_left.mp
      (FeedbackStepState.newTarget_disjoint_seenTarget sample lam
        (feedbackState sample lam x0 p0 r.val))) hr hseen'
  · have hseen : j ∈ (feedbackState sample lam x0 p0 (r.val + 1)).seenTarget :=
      (sample.mem_feedbackState_seenTarget_iff lam x0 p0 j (r.val + 1)).mpr
        (Or.inr ⟨r.val, by omega, hr⟩)
    have hseen' : j ∈ (feedbackState sample lam x0 p0 m.val).seenTarget :=
      sample.mem_feedbackState_seenTarget_mono lam x0 p0 j
        (Nat.succ_le_of_lt hrm) hseen
    exact (Finset.disjoint_left.mp
      (FeedbackStepState.newTarget_disjoint_seenTarget sample lam
        (feedbackState sample lam x0 p0 m.val))) hm hseen'

/-! ## Event-time interval characterizations -/

set_option linter.unusedVariables false in
theorem sourceEventTime_mem_Ioc_iff_exists_newSource_knot_mem_Ioc
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    (i : Fin n) {s t : ℝ≥0} (hst : s ≤ t) :
    sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ↔
      ∃ m : Fin (2 * n),
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t := by
  constructor
  · intro h
    have ht := (sample.sourceEventTime_le_iff_exists hlam0 hlamHalf x0 p0 i t).1 h.2
    rcases ht with ⟨_, ⟨m, hm, hmt⟩⟩
    have hms : s < sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) := by
      apply lt_of_not_ge
      intro hle
      have hes := (sample.sourceEventTime_le_iff_exists hlam0 hlamHalf x0 p0 i s).2
        ⟨hgood, ⟨m, hm, hle⟩⟩
      exact (not_lt_of_ge hes) h.1
    exact ⟨m, hm, hms, hmt⟩
  · rintro ⟨m, hm, hms, hmt⟩
    have hmt' := (sample.sourceEventTime_le_iff_exists hlam0 hlamHalf x0 p0 i t).2
      ⟨hgood, ⟨m, hm, hmt⟩⟩
    have hnot : ¬ sourceEventTime hlam0 hlamHalf x0 p0 i sample ≤ (s : WithTop ℝ≥0) := by
      intro hs
      rcases (sample.sourceEventTime_le_iff_exists hlam0 hlamHalf x0 p0 i s).1 hs with
        ⟨_, ⟨r, hr, hrs⟩⟩
      have hmr : r = m := sample.newSource_step_unique lam x0 p0 i hr hm
      rw [hmr] at hrs
      exact (not_lt_of_ge hrs) hms
    exact ⟨lt_of_not_ge hnot, hmt'⟩

set_option linter.unusedVariables false in
theorem targetEventTime_mem_Ioc_iff_exists_newTarget_knot_mem_Ioc
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    (j : Fin n) {s t : ℝ≥0} (hst : s ≤ t) :
    targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ↔
      ∃ m : Fin (2 * n),
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t := by
  constructor
  · intro h
    have ht := (sample.targetEventTime_le_iff_exists hlam0 hlamHalf x0 p0 j t).1 h.2
    rcases ht with ⟨_, ⟨m, hm, hmt⟩⟩
    have hms : s < sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) := by
      apply lt_of_not_ge
      intro hle
      have hes := (sample.targetEventTime_le_iff_exists hlam0 hlamHalf x0 p0 j s).2
        ⟨hgood, ⟨m, hm, hle⟩⟩
      exact (not_lt_of_ge hes) h.1
    exact ⟨m, hm, hms, hmt⟩
  · rintro ⟨m, hm, hms, hmt⟩
    have hmt' := (sample.targetEventTime_le_iff_exists hlam0 hlamHalf x0 p0 j t).2
      ⟨hgood, ⟨m, hm, hmt⟩⟩
    have hnot : ¬ targetEventTime hlam0 hlamHalf x0 p0 j sample ≤ (s : WithTop ℝ≥0) := by
      intro hs
      rcases (sample.targetEventTime_le_iff_exists hlam0 hlamHalf x0 p0 j s).1 hs with
        ⟨_, ⟨r, hr, hrs⟩⟩
      have hmr : r = m := sample.newTarget_step_unique lam x0 p0 j hr hm
      rw [hmr] at hrs
      exact (not_lt_of_ge hrs) hms
    exact ⟨lt_of_not_ge hnot, hmt'⟩

/-! ## Per-label finite sums -/

theorem sourceEventTime_indicator_eq_sum_newSource
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    (i : Fin n) {s t : ℝ≥0} (hst : s ≤ t) {R : Type*}
    [AddCommMonoidWithOne R] :
    (if sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : R) else 0) =
      ∑ m : Fin (2 * n), if
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then (1 : R) else 0 := by
  classical
  let P : Fin (2 * n) → Prop := fun m ↦
    i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
  have hiff : sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
      Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ↔ ∃ m, P m := by
    simpa [P] using sample.sourceEventTime_mem_Ioc_iff_exists_newSource_knot_mem_Ioc
      hlam0 hlamHalf x0 p0 hgood i hst
  have hfilter_nonempty :
      (Finset.univ.filter P).Nonempty ↔
        sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
    constructor
    · rintro ⟨m, hm⟩
      exact hiff.mpr ⟨m, (Finset.mem_filter.mp hm).2⟩
    · intro h
      rcases hiff.mp h with ⟨m, hm⟩
      exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
  have hcard_le : (Finset.univ.filter P).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro m hm r hr
    exact sample.newSource_step_unique lam x0 p0 i
      (Finset.mem_filter.mp hm).2.1 (Finset.mem_filter.mp hr).2.1
  have hsum_card :
      (∑ m : Fin (2 * n), if P m then (1 : R) else 0) =
        ((Finset.univ.filter P).card : R) := by
    simpa using (Finset.sum_boole (R := R) P
      (Finset.univ : Finset (Fin (2 * n))))
  by_cases h : sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
      Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)
  · have hne : (Finset.univ.filter P).Nonempty := hfilter_nonempty.mpr h
    have hcard : (Finset.univ.filter P).card = 1 := by
      have hpos := Finset.card_pos.mpr hne
      omega
    rw [ite_eq_left h, hsum_card, hcard]
    simp
  · have hempty : Finset.univ.filter P = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (hfilter_nonempty.not.mpr h)
    rw [ite_eq_right h, hsum_card, hempty]
    simp

theorem targetEventTime_indicator_eq_sum_newTarget
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    (j : Fin n) {s t : ℝ≥0} (hst : s ≤ t) {R : Type*}
    [AddCommMonoidWithOne R] :
    (if targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : R) else 0) =
      ∑ m : Fin (2 * n), if
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then (1 : R) else 0 := by
  classical
  let P : Fin (2 * n) → Prop := fun m ↦
    j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
  have hiff : targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
      Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ↔ ∃ m, P m := by
    simpa [P] using sample.targetEventTime_mem_Ioc_iff_exists_newTarget_knot_mem_Ioc
      hlam0 hlamHalf x0 p0 hgood j hst
  have hfilter_nonempty :
      (Finset.univ.filter P).Nonempty ↔
        targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
    constructor
    · rintro ⟨m, hm⟩
      exact hiff.mpr ⟨m, (Finset.mem_filter.mp hm).2⟩
    · intro h
      rcases hiff.mp h with ⟨m, hm⟩
      exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
  have hcard_le : (Finset.univ.filter P).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro m hm r hr
    exact sample.newTarget_step_unique lam x0 p0 j
      (Finset.mem_filter.mp hm).2.1 (Finset.mem_filter.mp hr).2.1
  have hsum_card :
      (∑ m : Fin (2 * n), if P m then (1 : R) else 0) =
        ((Finset.univ.filter P).card : R) := by
    simpa using (Finset.sum_boole (R := R) P
      (Finset.univ : Finset (Fin (2 * n))))
  by_cases h : targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
      Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)
  · have hne : (Finset.univ.filter P).Nonempty := hfilter_nonempty.mpr h
    have hcard : (Finset.univ.filter P).card = 1 := by
      have hpos := Finset.card_pos.mpr hne
      omega
    rw [ite_eq_left h, hsum_card, hcard]
    simp
  · have hempty : Finset.univ.filter P = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (hfilter_nonempty.not.mpr h)
    rw [ite_eq_right h, hsum_card, hempty]
    simp

/-! ## Weighted source/target sums -/

theorem sourceEventTime_weighted_interval_eq_sum_newSource
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    (w : Fin n → ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    ∑ i : Fin n, w i * (if sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) =
      ∑ m : Fin (2 * n), ∑ i : Fin n, w i * (if
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then (1 : ℝ) else 0) := by
  classical
  calc
    ∑ i : Fin n, w i * (if sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) =
        ∑ i : Fin n, ∑ m : Fin (2 * n), w i * (if
          i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
          then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      rw [sample.sourceEventTime_indicator_eq_sum_newSource hlam0 hlamHalf
        x0 p0 hgood i hst]
    _ = ∑ m : Fin (2 * n), ∑ i : Fin n, w i * (if
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then (1 : ℝ) else 0) := by
      exact Finset.sum_comm

theorem targetEventTime_weighted_interval_eq_sum_newTarget
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    (w : Fin n → ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    ∑ j : Fin n, w j * (if targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) =
      ∑ m : Fin (2 * n), ∑ j : Fin n, w j * (if
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then (1 : ℝ) else 0) := by
  classical
  calc
    ∑ j : Fin n, w j * (if targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) =
        ∑ j : Fin n, ∑ m : Fin (2 * n), w j * (if
          j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
          then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
      rw [sample.targetEventTime_indicator_eq_sum_newTarget hlam0 hlamHalf
        x0 p0 hgood j hst]
    _ = ∑ m : Fin (2 * n), ∑ j : Fin n, w j * (if
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then (1 : ℝ) else 0) := by
      exact Finset.sum_comm

/-! ## Count/cardinality corollaries -/

theorem finiteEventCountTop_sub_eq_card_filter_Ioc
    {Ω : Type*} {m : ℕ} (ξ : Fin m → Ω → WithTop ℝ≥0)
    (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω) :
    CountingProcess.finiteEventCountTop ξ t ω -
        CountingProcess.finiteEventCountTop ξ s ω =
      (Finset.univ.filter (fun i : Fin m ↦
        ξ i ω ∈ Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))).card := by
  classical
  let A : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ ξ i ω ≤ (t : WithTop ℝ≥0))
  let B : Finset (Fin m) := Finset.univ.filter
    (fun i ↦ ξ i ω ≤ (s : WithTop ℝ≥0))
  have hsub : B ⊆ A := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hi).2.trans (WithTop.coe_le_coe.mpr hst)⟩
  have hdiff : A \ B = Finset.univ.filter (fun i : Fin m ↦
      ξ i ω ∈ Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := by
    ext i
    simp only [A, B, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_Ioc]
    constructor
    · rintro ⟨hit, hnot⟩
      exact ⟨lt_of_not_ge hnot, hit⟩
    · rintro ⟨his, hit⟩
      exact ⟨hit, not_le_of_gt his⟩
  change A.card - B.card = _
  rw [← Finset.card_sdiff_of_subset hsub, hdiff]

theorem sourceEventTime_card_interval_eq_sum_newSource_card
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (Finset.univ.filter (fun i : Fin n ↦
      sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))).card =
      ∑ m : Fin (2 * n), if
        sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t then
          ((feedbackState sample lam x0 p0 m.val).newSource sample lam).card else 0 := by
  classical
  have hsum_card :
      (Finset.univ.filter (fun i : Fin n ↦
        sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))).card =
        ∑ i : Fin n, if sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then 1 else 0 := by
    symm
    simpa using (Finset.sum_boole (R := ℕ)
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) (Finset.univ : Finset (Fin n)))
  calc
    _ = ∑ i : Fin n, if sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then 1 else 0 := hsum_card
    _ = ∑ i : Fin n, ∑ m : Fin (2 * n), if
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sample.sourceEventTime_indicator_eq_sum_newSource hlam0 hlamHalf
        x0 p0 hgood i hst
    _ = ∑ m : Fin (2 * n), ∑ i : Fin n, if
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then 1 else 0 := by
      exact Finset.sum_comm
    _ = ∑ m : Fin (2 * n), if
        sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t then
          ((feedbackState sample lam x0 p0 m.val).newSource sample lam).card else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hk : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
      · simp [hk]
      · simp [hk]

theorem targetEventTime_card_interval_eq_sum_newTarget_card
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (hgood : sample.NoFeedbackTies lam x0 p0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (Finset.univ.filter (fun j : Fin n ↦
      targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))).card =
      ∑ m : Fin (2 * n), if
        sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t then
          ((feedbackState sample lam x0 p0 m.val).newTarget sample lam).card else 0 := by
  classical
  have hsum_card :
      (Finset.univ.filter (fun j : Fin n ↦
        targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))).card =
        ∑ j : Fin n, if targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then 1 else 0 := by
    symm
    simpa using (Finset.sum_boole (R := ℕ)
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)) (Finset.univ : Finset (Fin n)))
  calc
    _ = ∑ j : Fin n, if targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then 1 else 0 := hsum_card
    _ = ∑ j : Fin n, ∑ m : Fin (2 * n), if
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sample.targetEventTime_indicator_eq_sum_newTarget hlam0 hlamHalf
        x0 p0 hgood j hst
    _ = ∑ m : Fin (2 * n), ∑ j : Fin n, if
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
        then 1 else 0 := by
      exact Finset.sum_comm
    _ = ∑ m : Fin (2 * n), if
        sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t then
          ((feedbackState sample lam x0 p0 m.val).newTarget sample lam).card else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hk : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
      · simp [hk]
      · simp [hk]

/-! ## Safe tie-fallback indicators and count increments -/

theorem safeSourceEventTime_indicator_eq_if_sum_newSource
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (i : Fin n)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (if sourceEventTime hlam0 hlamHalf x0 p0 i sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) =
      if sample.NoFeedbackTies lam x0 p0 then
        ∑ m : Fin (2 * n), if
          i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
          then (1 : ℝ) else 0
      else 0 := by
  classical
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · simpa [hgood] using sample.sourceEventTime_indicator_eq_sum_newSource
      hlam0 hlamHalf x0 p0 hgood i hst
  · have htop : sourceEventTime hlam0 hlamHalf x0 p0 i sample = ⊤ := by
      simp [sourceEventTime, hgood]
    rw [htop]
    have htop_not : (⊤ : WithTop ℝ≥0) ∉ Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
      intro hmem
      exact WithTop.not_top_le_coe t hmem.2
    rw [ite_eq_right htop_not, ite_eq_right hgood]

theorem safeTargetEventTime_indicator_eq_if_sum_newTarget
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) (j : Fin n)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (if targetEventTime hlam0 hlamHalf x0 p0 j sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : ℝ) else 0) =
      if sample.NoFeedbackTies lam x0 p0 then
        ∑ m : Fin (2 * n), if
          j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t
          then (1 : ℝ) else 0
      else 0 := by
  classical
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · simpa [hgood] using sample.targetEventTime_indicator_eq_sum_newTarget
      hlam0 hlamHalf x0 p0 hgood j hst
  · have htop : targetEventTime hlam0 hlamHalf x0 p0 j sample = ⊤ := by
      simp [targetEventTime, hgood]
    rw [htop]
    have htop_not : (⊤ : WithTop ℝ≥0) ∉ Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) := by
      intro hmem
      exact WithTop.not_top_le_coe t hmem.2
    rw [ite_eq_right htop_not, ite_eq_right hgood]

theorem safeSourceCount_interval_eq_if_knot_sum
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    safeSourceCount hlam0 hlamHalf x0 p0 t sample -
        safeSourceCount hlam0 hlamHalf x0 p0 s sample =
      if sample.NoFeedbackTies lam x0 p0 then
        ∑ m : Fin (2 * n), if
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t then
            ((feedbackState sample lam x0 p0 m.val).newSource sample lam).card else 0
      else 0 := by
  classical
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · have hcount := finiteEventCountTop_sub_eq_card_filter_Ioc
      (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s t hst sample
    rw [show safeSourceCount hlam0 hlamHalf x0 p0 t sample =
        CountingProcess.finiteEventCountTop
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample by rfl,
      show safeSourceCount hlam0 hlamHalf x0 p0 s sample =
        CountingProcess.finiteEventCountTop
          (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample by rfl]
    rw [hcount]
    simpa [hgood] using sample.sourceEventTime_card_interval_eq_sum_newSource_card
      hlam0 hlamHalf x0 p0 hgood hst
  · have htop : ∀ i : Fin n, sourceEventTime hlam0 hlamHalf x0 p0 i sample = ⊤ := by
      intro i
      simp [sourceEventTime, hgood]
    simp only [safeSourceCount, CountingProcess.finiteEventCountTop]
    have hzero_t : (Finset.univ.filter (fun i : Fin n ↦
        sourceEventTime hlam0 hlamHalf x0 p0 i sample ≤ (t : WithTop ℝ≥0))) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [htop i]
      constructor
      · intro hle
        exact False.elim (WithTop.not_top_le_coe t hle)
      · intro hi
        simp at hi
    have hzero_s : (Finset.univ.filter (fun i : Fin n ↦
        sourceEventTime hlam0 hlamHalf x0 p0 i sample ≤ (s : WithTop ℝ≥0))) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [htop i]
      constructor
      · intro hle
        exact False.elim (WithTop.not_top_le_coe s hle)
      · intro hi
        simp at hi
    rw [hzero_t, hzero_s]
    simp [hgood]

theorem safeTargetCount_interval_eq_if_knot_sum
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    safeTargetCount hlam0 hlamHalf x0 p0 t sample -
        safeTargetCount hlam0 hlamHalf x0 p0 s sample =
      if sample.NoFeedbackTies lam x0 p0 then
        ∑ m : Fin (2 * n), if
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t then
            ((feedbackState sample lam x0 p0 m.val).newTarget sample lam).card else 0
      else 0 := by
  classical
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · have hcount := finiteEventCountTop_sub_eq_card_filter_Ioc
      (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s t hst sample
    rw [show safeTargetCount hlam0 hlamHalf x0 p0 t sample =
        CountingProcess.finiteEventCountTop
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample by rfl,
      show safeTargetCount hlam0 hlamHalf x0 p0 s sample =
        CountingProcess.finiteEventCountTop
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample by rfl]
    rw [hcount]
    simpa [hgood] using sample.targetEventTime_card_interval_eq_sum_newTarget_card
      hlam0 hlamHalf x0 p0 hgood hst
  · have htop : ∀ j : Fin n, targetEventTime hlam0 hlamHalf x0 p0 j sample = ⊤ := by
      intro j
      simp [targetEventTime, hgood]
    simp only [safeTargetCount, CountingProcess.finiteEventCountTop]
    have hzero_t : (Finset.univ.filter (fun j : Fin n ↦
        targetEventTime hlam0 hlamHalf x0 p0 j sample ≤ (t : WithTop ℝ≥0))) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [htop j]
      constructor
      · intro hle
        exact False.elim (WithTop.not_top_le_coe t hle)
      · intro hi
        simp at hi
    have hzero_s : (Finset.univ.filter (fun j : Fin n ↦
        targetEventTime hlam0 hlamHalf x0 p0 j sample ≤ (s : WithTop ℝ≥0))) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [htop j]
      constructor
      · intro hle
        exact False.elim (WithTop.not_top_le_coe s hle)
      · intro hi
        simp at hi
    rw [hzero_t, hzero_s]
    simp [hgood]

end FiniteSample

end OTSelector
