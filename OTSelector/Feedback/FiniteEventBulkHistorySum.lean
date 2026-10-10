import OTSelector.Feedback.FiniteEventHistorySum
import OTSelector.Feedback.FeedbackBulkMask
import OTSelector.Probability.CountingProcess.FiniteEventThinning

/-!
# Bulk-masked finite event-history sums

This file identifies the predictable bulk mask at a revealed event knot and then rewrites the
corresponding thinned event indicators and finite count increments as sums over the recursive
feedback steps.  All statements are pathwise; no probabilistic interface is introduced here.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal Topology

namespace OTSelector

open CountingProcess

namespace FiniteSample

variable {n : ℕ}

/-! ## The unique knot of a newly seen label -/

theorem sourceEventTime_eq_elapsedFeedbackKnot_of_newSource
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0) (i : Fin n)
    {m : Fin (2 * n)}
    (hm : i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam) :
    sourceEventTime hlam0 hlamHalf x0 p0 i sample =
      (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) :
        WithTop ℝ≥0) := by
  classical
  have hmS : m ∈ sample.sourceEventSet lam x0 p0 i := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
  have hS : (sample.sourceEventSet lam x0 p0 i).Nonempty := ⟨m, hmS⟩
  have hset : sample.sourceEventSet lam x0 p0 i = {m} := by
    ext r
    constructor
    · intro hr
      have hrnew := (Finset.mem_filter.mp hr).2
      have hmr : r = m := sample.newSource_step_unique lam x0 p0 i hrnew hm
      simp [hmr]
    · intro hr
      have hmr : r = m := Finset.mem_singleton.mp hr
      simpa [hmr] using hmS
  simp [sourceEventTime, hgood, sourceEventTimeRaw, hset]
  rfl

theorem targetEventTime_eq_elapsedFeedbackKnot_of_newTarget
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0) (j : Fin n)
    {m : Fin (2 * n)}
    (hm : j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam) :
    targetEventTime hlam0 hlamHalf x0 p0 j sample =
      (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) :
        WithTop ℝ≥0) := by
  classical
  have hmS : m ∈ sample.targetEventSet lam x0 p0 j := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
  have hS : (sample.targetEventSet lam x0 p0 j).Nonempty := ⟨m, hmS⟩
  have hset : sample.targetEventSet lam x0 p0 j = {m} := by
    ext r
    constructor
    · intro hr
      have hrnew := (Finset.mem_filter.mp hr).2
      have hmr : r = m := sample.newTarget_step_unique lam x0 p0 j hrnew hm
      simp [hmr]
    · intro hr
      have hmr : r = m := Finset.mem_singleton.mp hr
      simpa [hmr] using hmS
  simp [targetEventTime, hgood, targetEventTimeRaw, hset]
  rfl

/-! ## The safe height at an elapsed knot -/

theorem safeFeedbackHeightAtElapsed_at_elapsedFeedbackKnot_of_noFeedbackTies
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0) (k : ℕ) (hk : k ≤ 2 * n) :
    safeFeedbackHeightAtElapsed hlam0 hlamHalf x0 p0
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k) sample =
      feedbackKnotValue sample lam x0 p0 k := by
  simp only [safeFeedbackHeightAtElapsed, hgood]
  rw [sample.feedbackHeightAtElapsed_eq_feedbackCurve hlam0 hlamHalf x0 p0]
  rw [show x0 + (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 k : ℝ) =
      sample.feedbackKnot lam x0 p0 k by
        simp only [FiniteSample.coe_elapsedFeedbackKnot]
        ring]
  exact sample.feedbackCurve_eq_feedbackKnotValue_at_knot hlam0 hlamHalf x0 p0 hk

/-! ## Acceptance is exactly the bulk condition at an active knot -/

theorem eventAccepted_safeFeedbackBulkMask_source_of_newSource
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0) (i : Fin n)
    {m : Fin (2 * n)}
    (hm : i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam) :
    eventAccepted
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ↔
      feedbackBulkRegion n B
        (sample.feedbackKnot lam x0 p0 (m.val + 1))
        (feedbackKnotValue sample lam x0 p0 (m.val + 1)) := by
  have htime := sample.sourceEventTime_eq_elapsedFeedbackKnot_of_newSource
    hlam0 hlamHalf x0 p0 hgood i hm
  have hk : m.val + 1 ≤ 2 * n := by omega
  have hstop : stoppedValue
      (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (sourceEventTime hlam0 hlamHalf x0 p0 i) sample =
      safeFeedbackBulkMask hlam0 hlamHalf B x0 p0
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1)) sample := by
    simp only [stoppedValue, htime]
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  constructor
  · intro hacc
    have hmask : safeFeedbackBulkMask hlam0 hlamHalf B x0 p0
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1)) sample ≠ 0 := by
      rw [← hstop]
      exact hacc.2
    simpa [safeFeedbackBulkMask,
      sample.safeFeedbackHeightAtElapsed_at_elapsedFeedbackKnot_of_noFeedbackTies
        hlam0 hlamHalf x0 p0 hgood (m.val + 1) hk,
      elapsedFeedbackCoordinate, FiniteSample.coe_elapsedFeedbackKnot] using hmask
  · intro hbulk
    have hfinite : sourceEventTime hlam0 hlamHalf x0 p0 i sample ≠ ⊤ := by
      rw [htime]
      exact WithTop.coe_ne_top
    refine ⟨hfinite, ?_⟩
    rw [hstop]
    simpa [safeFeedbackBulkMask,
      sample.safeFeedbackHeightAtElapsed_at_elapsedFeedbackKnot_of_noFeedbackTies
        hlam0 hlamHalf x0 p0 hgood (m.val + 1) hk,
      elapsedFeedbackCoordinate, FiniteSample.coe_elapsedFeedbackKnot] using hbulk

theorem eventAccepted_safeFeedbackBulkMask_target_of_newTarget
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0) (j : Fin n)
    {m : Fin (2 * n)}
    (hm : j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam) :
    eventAccepted
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (targetEventTime hlam0 hlamHalf x0 p0 j) sample ↔
      feedbackBulkRegion n B
        (sample.feedbackKnot lam x0 p0 (m.val + 1))
        (feedbackKnotValue sample lam x0 p0 (m.val + 1)) := by
  have htime := sample.targetEventTime_eq_elapsedFeedbackKnot_of_newTarget
    hlam0 hlamHalf x0 p0 hgood j hm
  have hk : m.val + 1 ≤ 2 * n := by omega
  have hstop : stoppedValue
      (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (targetEventTime hlam0 hlamHalf x0 p0 j) sample =
      safeFeedbackBulkMask hlam0 hlamHalf B x0 p0
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1)) sample := by
    simp only [stoppedValue, htime]
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  constructor
  · intro hacc
    have hmask' : safeFeedbackBulkMask hlam0 hlamHalf B x0 p0
        (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1)) sample ≠ 0 := by
      rw [← hstop]
      exact hacc.2
    simpa [safeFeedbackBulkMask,
      sample.safeFeedbackHeightAtElapsed_at_elapsedFeedbackKnot_of_noFeedbackTies
        hlam0 hlamHalf x0 p0 hgood (m.val + 1) hk,
      elapsedFeedbackCoordinate, FiniteSample.coe_elapsedFeedbackKnot] using hmask'
  · intro hbulk
    have hfinite : targetEventTime hlam0 hlamHalf x0 p0 j sample ≠ ⊤ := by
      rw [htime]
      exact WithTop.coe_ne_top
    refine ⟨hfinite, ?_⟩
    rw [hstop]
    simpa [safeFeedbackBulkMask,
      sample.safeFeedbackHeightAtElapsed_at_elapsedFeedbackKnot_of_noFeedbackTies
        hlam0 hlamHalf x0 p0 hgood (m.val + 1) hk,
      elapsedFeedbackCoordinate, FiniteSample.coe_elapsedFeedbackKnot] using hbulk

/-! ## Source and target interval predicates for the thinned times -/

theorem thinnedSourceEventTime_mem_Ioc_iff_exists_newSource_bulk
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0) (i : Fin n)
    {s t : ℝ≥0} (hst : s ≤ t) :
    thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ↔
      ∃ m : Fin (2 * n),
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1)) := by
  constructor
  · intro hthin
    have hle := (thinnedEventTime_le_iff sample t).mp hthin.2
    rcases hle with ⟨hacc, _⟩
    rw [thinnedEventTime_of_accepted hacc] at hthin
    rcases (sample.sourceEventTime_mem_Ioc_iff_exists_newSource_knot_mem_Ioc
      hlam0 hlamHalf x0 p0 hgood i hst).mp hthin with ⟨m, hm, hk⟩
    have hbulk := (sample.eventAccepted_safeFeedbackBulkMask_source_of_newSource
      hlam0 hlamHalf B x0 p0 hgood i hm).mp hacc
    exact ⟨m, hm, hk, hbulk⟩
  · rintro ⟨m, hm, hk, hbulk⟩
    have hsource := (sample.sourceEventTime_mem_Ioc_iff_exists_newSource_knot_mem_Ioc
      hlam0 hlamHalf x0 p0 hgood i hst).mpr ⟨m, hm, hk⟩
    have hacc := (sample.eventAccepted_safeFeedbackBulkMask_source_of_newSource
      hlam0 hlamHalf B x0 p0 hgood i hm).mpr hbulk
    rw [thinnedEventTime_of_accepted hacc]
    exact hsource

theorem thinnedTargetEventTime_mem_Ioc_iff_exists_newTarget_bulk
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0) (j : Fin n)
    {s t : ℝ≥0} (hst : s ≤ t) :
    thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (targetEventTime hlam0 hlamHalf x0 p0 j) sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ↔
      ∃ m : Fin (2 * n),
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1)) := by
  constructor
  · intro hthin
    have hle := (thinnedEventTime_le_iff sample t).mp hthin.2
    rcases hle with ⟨hacc, _⟩
    rw [thinnedEventTime_of_accepted hacc] at hthin
    rcases (sample.targetEventTime_mem_Ioc_iff_exists_newTarget_knot_mem_Ioc
      hlam0 hlamHalf x0 p0 hgood j hst).mp hthin with ⟨m, hm, hk⟩
    have hbulk := (sample.eventAccepted_safeFeedbackBulkMask_target_of_newTarget
      hlam0 hlamHalf B x0 p0 hgood j hm).mp hacc
    exact ⟨m, hm, hk, hbulk⟩
  · rintro ⟨m, hm, hk, hbulk⟩
    have htarget := (sample.targetEventTime_mem_Ioc_iff_exists_newTarget_knot_mem_Ioc
      hlam0 hlamHalf x0 p0 hgood j hst).mpr ⟨m, hm, hk⟩
    have hacc := (sample.eventAccepted_safeFeedbackBulkMask_target_of_newTarget
      hlam0 hlamHalf B x0 p0 hgood j hm).mpr hbulk
    rw [thinnedEventTime_of_accepted hacc]
    exact htarget

theorem thinnedSourceEventTime_indicator_eq_sum_newSource_bulk
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0) (i : Fin n)
    {s t : ℝ≥0} (hst : s ≤ t) {R : Type*}
    [AddCommMonoidWithOne R] :
    (if thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : R) else 0) =
      ∑ m : Fin (2 * n), if
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1))
        then (1 : R) else 0 := by
  let P : Fin (2 * n) → Prop := fun m ↦
    i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
      feedbackBulkRegion n B
        (sample.feedbackKnot lam x0 p0 (m.val + 1))
        (feedbackKnotValue sample lam x0 p0 (m.val + 1))
  have hiff :
      thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ↔ ∃ m, P m := by
    simpa [P] using sample.thinnedSourceEventTime_mem_Ioc_iff_exists_newSource_bulk
      hlam0 hlamHalf B x0 p0 hgood i hst
  have huniq : ∀ m r, P m → P r → m = r := by
    intro m r hm hr
    exact sample.newSource_step_unique lam x0 p0 i hm.1 hr.1
  calc
    (if thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : R) else 0) =
        (if ∃ m, P m then (1 : R) else 0) := by
      by_cases h : thinnedEventTime
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)
      · have hex : ∃ m, P m := hiff.mp h
        rw [ite_eq_left h, ite_eq_left hex]
      · have hnex : ¬∃ m, P m := by
          intro hex
          exact h (hiff.mpr hex)
        rw [ite_eq_right h, ite_eq_right hnex]
    _ = (Finset.univ.filter P).card := by
      by_cases h : ∃ m, P m
      · have hne : (Finset.univ.filter P).Nonempty := by
          rcases h with ⟨m, hm⟩
          exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
        have hle : (Finset.univ.filter P).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro m hm r hr
          exact huniq m r (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hr).2
        have hcard : (Finset.univ.filter P).card = 1 := by
          have hpos := Finset.card_pos.mpr hne
          omega
        simp [h, hcard]
      · have hempty : Finset.univ.filter P = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          rcases hne with ⟨m, hm⟩
          exact h ⟨m, (Finset.mem_filter.mp hm).2⟩
        simp [h, hempty]
    _ = ∑ m : Fin (2 * n), if P m then (1 : R) else 0 := by
      symm
      simpa using (Finset.sum_boole (R := R) P
        (Finset.univ : Finset (Fin (2 * n))))
    _ = ∑ m : Fin (2 * n), if
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1))
        then (1 : R) else 0 := by rfl

theorem thinnedTargetEventTime_indicator_eq_sum_newTarget_bulk
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0) (j : Fin n)
    {s t : ℝ≥0} (hst : s ≤ t) {R : Type*}
    [AddCommMonoidWithOne R] :
    (if thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (targetEventTime hlam0 hlamHalf x0 p0 j) sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : R) else 0) =
      ∑ m : Fin (2 * n), if
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1))
        then (1 : R) else 0 := by
  let P : Fin (2 * n) → Prop := fun m ↦
    j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
      feedbackBulkRegion n B
        (sample.feedbackKnot lam x0 p0 (m.val + 1))
        (feedbackKnotValue sample lam x0 p0 (m.val + 1))
  have hiff :
      thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (targetEventTime hlam0 hlamHalf x0 p0 j) sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) ↔ ∃ m, P m := by
    simpa [P] using sample.thinnedTargetEventTime_mem_Ioc_iff_exists_newTarget_bulk
      hlam0 hlamHalf B x0 p0 hgood j hst
  have huniq : ∀ m r, P m → P r → m = r := by
    intro m r hm hr
    exact sample.newTarget_step_unique lam x0 p0 j hm.1 hr.1
  calc
    (if thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (targetEventTime hlam0 hlamHalf x0 p0 j) sample ∈
        Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then (1 : R) else 0) =
        (if ∃ m, P m then (1 : R) else 0) := by
      by_cases h : thinnedEventTime
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (targetEventTime hlam0 hlamHalf x0 p0 j) sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0)
      · have hex : ∃ m, P m := hiff.mp h
        rw [ite_eq_left h, ite_eq_left hex]
      · have hnex : ¬∃ m, P m := by
          intro hex
          exact h (hiff.mpr hex)
        rw [ite_eq_right h, ite_eq_right hnex]
    _ = (Finset.univ.filter P).card := by
      by_cases h : ∃ m, P m
      · have hne : (Finset.univ.filter P).Nonempty := by
          rcases h with ⟨m, hm⟩
          exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩
        have hle : (Finset.univ.filter P).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro m hm r hr
          exact huniq m r (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hr).2
        have hcard : (Finset.univ.filter P).card = 1 := by
          have hpos := Finset.card_pos.mpr hne
          omega
        simp [h, hcard]
      · have hempty : Finset.univ.filter P = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          rcases hne with ⟨m, hm⟩
          exact h ⟨m, (Finset.mem_filter.mp hm).2⟩
        simp [h, hempty]
    _ = ∑ m : Fin (2 * n), if P m then (1 : R) else 0 := by
      symm
      simpa using (Finset.sum_boole (R := R) P
        (Finset.univ : Finset (Fin (2 * n))))
    _ = ∑ m : Fin (2 * n), if
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1))
        then (1 : R) else 0 := by rfl

/-! ## Count increments -/

theorem finiteEventCountThinned_source_sub_eq_sum_newSource_bulk_card
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t sample -
      finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) s sample =
      ∑ m : Fin (2 * n),
        (Finset.univ.filter (fun i : Fin n ↦
          i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card := by
  classical
  have hcount := finiteEventCountTop_sub_eq_card_filter_Ioc
    (fun i : Fin n ↦ thinnedEventTime
      (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (sourceEventTime hlam0 hlamHalf x0 p0 i)) s t hst sample
  change finiteEventCountTop
      (fun i : Fin n ↦ thinnedEventTime
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (sourceEventTime hlam0 hlamHalf x0 p0 i)) t sample -
    finiteEventCountTop
      (fun i : Fin n ↦ thinnedEventTime
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (sourceEventTime hlam0 hlamHalf x0 p0 i)) s sample = _
  rw [hcount]
  calc
    (Finset.univ.filter (fun i : Fin n ↦
        thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))).card =
        ∑ i : Fin n, if
          thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ∈
            Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then 1 else 0 := by
      symm
      exact Finset.sum_boole (R := ℕ)
        (fun i : Fin n ↦ thinnedEventTime
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (sourceEventTime hlam0 hlamHalf x0 p0 i) sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))
        (Finset.univ : Finset (Fin n))
    _ = ∑ i : Fin n, ∑ m : Fin (2 * n), if
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1))
        then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sample.thinnedSourceEventTime_indicator_eq_sum_newSource_bulk
        hlam0 hlamHalf B x0 p0 hgood i hst
    _ = ∑ m : Fin (2 * n), ∑ i : Fin n, if
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1))
        then 1 else 0 := by
      exact Finset.sum_comm
    _ = ∑ m : Fin (2 * n),
        (Finset.univ.filter (fun i : Fin n ↦
          i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_boole (R := ℕ)
        (fun i : Fin n ↦
          i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))
        (Finset.univ : Finset (Fin n))

theorem finiteEventCountThinned_target_sub_eq_sum_newTarget_bulk_card
    (sample : FiniteSample n) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlamHalf : lam < 1 / 2) (B x0 p0 : ℝ)
    (hgood : sample.NoFeedbackTies lam x0 p0)
    {s t : ℝ≥0} (hst : s ≤ t) :
    finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t sample -
      finiteEventCountThinned
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) s sample =
      ∑ m : Fin (2 * n),
        (Finset.univ.filter (fun j : Fin n ↦
          j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card := by
  classical
  have hcount := finiteEventCountTop_sub_eq_card_filter_Ioc
    (fun j : Fin n ↦ thinnedEventTime
      (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
      (targetEventTime hlam0 hlamHalf x0 p0 j)) s t hst sample
  change finiteEventCountTop
      (fun j : Fin n ↦ thinnedEventTime
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (targetEventTime hlam0 hlamHalf x0 p0 j)) t sample -
    finiteEventCountTop
      (fun j : Fin n ↦ thinnedEventTime
        (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
        (targetEventTime hlam0 hlamHalf x0 p0 j)) s sample = _
  rw [hcount]
  calc
    (Finset.univ.filter (fun j : Fin n ↦
        thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (targetEventTime hlam0 hlamHalf x0 p0 j) sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))).card =
        ∑ j : Fin n, if
          thinnedEventTime (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
            (targetEventTime hlam0 hlamHalf x0 p0 j) sample ∈
            Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0) then 1 else 0 := by
      symm
      simpa using (Finset.sum_boole (R := ℕ)
        (fun j : Fin n ↦ thinnedEventTime
          (safeFeedbackBulkMask hlam0 hlamHalf B x0 p0)
          (targetEventTime hlam0 hlamHalf x0 p0 j) sample ∈
          Ioc (s : WithTop ℝ≥0) (t : WithTop ℝ≥0))
        (Finset.univ : Finset (Fin n)))
    _ = ∑ j : Fin n, ∑ m : Fin (2 * n), if
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1))
        then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sample.thinnedTargetEventTime_indicator_eq_sum_newTarget_bulk
        hlam0 hlamHalf B x0 p0 hgood j hst
    _ = ∑ m : Fin (2 * n), ∑ j : Fin n, if
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
          feedbackBulkRegion n B
            (sample.feedbackKnot lam x0 p0 (m.val + 1))
            (feedbackKnotValue sample lam x0 p0 (m.val + 1))
        then 1 else 0 := by
      exact Finset.sum_comm
    _ = ∑ m : Fin (2 * n),
        (Finset.univ.filter (fun j : Fin n ↦
          j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))).card := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_boole (R := ℕ)
        (fun j : Fin n ↦
          j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ∈ Ioc s t ∧
            feedbackBulkRegion n B
              (sample.feedbackKnot lam x0 p0 (m.val + 1))
              (feedbackKnotValue sample lam x0 p0 (m.val + 1)))
        (Finset.univ : Finset (Fin n))

end FiniteSample

end OTSelector
