import OTSelector.Feedback.RevealedHistory
import OTSelector.Feedback.MarkedPredictable
import OTSelector.Probability.CountingProcess.FiniteEventCountTop

/-!
# Safe post-initial revealed counts

The recursive feedback state records the labels already swept at each knot.  This file turns the
finite post-initial part of that recursion into top-valued event times and finite counting paths.
The top fallback is used on the terminal null tie event; it therefore contributes no finite-time
jumps and does not require putting the good event in the raw filtration.
-/

open MeasureTheory Set
open scoped Classical NNReal Topology

namespace OTSelector

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-! ## First post-initial event labels -/

noncomputable def sourceEventSet
    (lam x0 p0 : ℝ) (i : Fin n) : Finset (Fin (2 * n)) :=
  Finset.univ.filter fun m ↦
    i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam

noncomputable def targetEventSet
    (lam x0 p0 : ℝ) (j : Fin n) : Finset (Fin (2 * n)) :=
  Finset.univ.filter fun m ↦
    j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam

noncomputable def sourceEventTimeRaw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) : WithTop ℝ≥0 :=
  if h : (sample.sourceEventSet lam x0 p0 i).Nonempty then
    (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0
      (((sample.sourceEventSet lam x0 p0 i).min' h).val + 1) : WithTop ℝ≥0)
  else ⊤

noncomputable def targetEventTimeRaw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) : WithTop ℝ≥0 :=
  if h : (sample.targetEventSet lam x0 p0 j).Nonempty then
    (sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0
      (((sample.targetEventSet lam x0 p0 j).min' h).val + 1) : WithTop ℝ≥0)
  else ⊤

/-- The safe source event time; ties are sent to the top fallback. -/
noncomputable def sourceEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  fun ω ↦ if ω.NoFeedbackTies lam x0 p0 then
    sourceEventTimeRaw ω hlam0 hlamHalf x0 p0 i else ⊤

/-- The safe target event time; ties are sent to the top fallback. -/
noncomputable def targetEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) : FiniteSample n → WithTop ℝ≥0 :=
  fun ω ↦ if ω.NoFeedbackTies lam x0 p0 then
    targetEventTimeRaw ω hlam0 hlamHalf x0 p0 j else ⊤

theorem sourceEventTimeRaw_eq_top_iff
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) :
    sample.sourceEventTimeRaw hlam0 hlamHalf x0 p0 i = ⊤ ↔
      (sample.sourceEventSet lam x0 p0 i).Nonempty = False := by
  classical
  by_cases h : (sample.sourceEventSet lam x0 p0 i).Nonempty
  · rw [sourceEventTimeRaw, dite_eq_left h]
    constructor
    · intro htop
      exact False.elim (WithTop.coe_ne_top htop)
    · intro hfalse
      simp [h] at hfalse
  · simp [sourceEventTimeRaw, h]

theorem targetEventTimeRaw_eq_top_iff
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) :
    sample.targetEventTimeRaw hlam0 hlamHalf x0 p0 j = ⊤ ↔
      (sample.targetEventSet lam x0 p0 j).Nonempty = False := by
  classical
  by_cases h : (sample.targetEventSet lam x0 p0 j).Nonempty
  · rw [targetEventTimeRaw, dite_eq_left h]
    constructor
    · intro htop
      exact False.elim (WithTop.coe_ne_top htop)
    · intro hfalse
      simp [h] at hfalse
  · simp [targetEventTimeRaw, h]

theorem sourceEventTimeRaw_le_iff_exists
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) (t : ℝ≥0) :
    sample.sourceEventTimeRaw hlam0 hlamHalf x0 p0 i ≤ (t : WithTop ℝ≥0) ↔
      ∃ m : Fin (2 * n),
        i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ≤ t := by
  classical
  let S := sample.sourceEventSet lam x0 p0 i
  by_cases hS : S.Nonempty
  · rw [sourceEventTimeRaw, dite_eq_left hS]
    constructor
    · intro hle
      let m := S.min' hS
      refine ⟨m, ?_, ?_⟩
      · exact (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
      · exact_mod_cast hle
    · rintro ⟨m, hm, hmt⟩
      have hmS : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
      have hmin : (S.min' hS).val ≤ m.val := Finset.min'_le S m hmS
      have hmono := sample.elapsedFeedbackKnot_mono hlam0 hlamHalf x0 p0
        (Nat.add_le_add_right hmin 1)
      have hle : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0
          ((S.min' hS).val + 1) ≤ t := hmono.trans hmt
      exact_mod_cast hle
  · rw [sourceEventTimeRaw, dite_eq_right hS]
    constructor
    · intro htop
      exact False.elim (WithTop.not_top_le_coe t htop)
    · rintro ⟨m, hm, _⟩
      have : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
      exact False.elim (hS ⟨m, this⟩)

theorem targetEventTimeRaw_le_iff_exists
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) (t : ℝ≥0) :
    sample.targetEventTimeRaw hlam0 hlamHalf x0 p0 j ≤ (t : WithTop ℝ≥0) ↔
      ∃ m : Fin (2 * n),
        j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
          sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ≤ t := by
  classical
  let S := sample.targetEventSet lam x0 p0 j
  by_cases hS : S.Nonempty
  · rw [targetEventTimeRaw, dite_eq_left hS]
    constructor
    · intro hle
      let m := S.min' hS
      refine ⟨m, ?_, ?_⟩
      · exact (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
      · exact_mod_cast hle
    · rintro ⟨m, hm, hmt⟩
      have hmS : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
      have hmin : (S.min' hS).val ≤ m.val := Finset.min'_le S m hmS
      have hmono := sample.elapsedFeedbackKnot_mono hlam0 hlamHalf x0 p0
        (Nat.add_le_add_right hmin 1)
      have hle : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0
          ((S.min' hS).val + 1) ≤ t := hmono.trans hmt
      exact_mod_cast hle
  · rw [targetEventTimeRaw, dite_eq_right hS]
    constructor
    · intro htop
      exact False.elim (WithTop.not_top_le_coe t htop)
    · rintro ⟨m, hm, _⟩
      have : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
      exact False.elim (hS ⟨m, this⟩)

theorem sourceEventTime_le_iff_exists
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) (t : ℝ≥0) :
    sourceEventTime hlam0 hlamHalf x0 p0 i sample ≤ (t : WithTop ℝ≥0) ↔
      sample.NoFeedbackTies lam x0 p0 ∧
        ∃ m : Fin (2 * n),
          i ∈ (feedbackState sample lam x0 p0 m.val).newSource sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ≤ t := by
  classical
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · simp only [sourceEventTime, hgood, ↓reduceIte]
    rw [sourceEventTimeRaw_le_iff_exists]
    simp
  · have htop : sourceEventTime hlam0 hlamHalf x0 p0 i sample = ⊤ := by
      simp [sourceEventTime, hgood]
    rw [htop]
    constructor
    · intro h
      exact False.elim (WithTop.not_top_le_coe t h)
    · intro h
      exact False.elim (hgood h.1)

theorem targetEventTime_le_iff_exists
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) (t : ℝ≥0) :
    targetEventTime hlam0 hlamHalf x0 p0 j sample ≤ (t : WithTop ℝ≥0) ↔
      sample.NoFeedbackTies lam x0 p0 ∧
        ∃ m : Fin (2 * n),
          j ∈ (feedbackState sample lam x0 p0 m.val).newTarget sample lam ∧
            sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) ≤ t := by
  classical
  by_cases hgood : sample.NoFeedbackTies lam x0 p0
  · simp only [targetEventTime, hgood, ↓reduceIte]
    rw [targetEventTimeRaw_le_iff_exists]
    simp
  · have htop : targetEventTime hlam0 hlamHalf x0 p0 j sample = ⊤ := by
      simp [targetEventTime, hgood]
    rw [htop]
    constructor
    · intro h
      exact False.elim (WithTop.not_top_le_coe t h)
    · intro h
      exact False.elim (hgood h.1)

/-! ## Seen-set induction and the state-at-time equivalence -/

theorem mem_feedbackState_seenSource_iff
    (lam x0 p0 : ℝ) (i : Fin n) (m : ℕ) :
    i ∈ (feedbackState sample lam x0 p0 m).seenSource ↔
      i ∈ sample.initialSeenSource x0 p0 ∨
        ∃ k < m, i ∈ (feedbackState sample lam x0 p0 k).newSource sample lam := by
  induction m with
  | zero => simp [feedbackState, initialFeedbackState]
  | succ m ih =>
      rw [feedbackState_succ]
      constructor
      · intro hi
        simp only [FeedbackStepState.step, Finset.mem_union] at hi
        rcases hi with hi | hi
        · exact Or.imp_right (fun ⟨k, hk, hknew⟩ ↦
            ⟨k, Nat.lt_trans hk (Nat.lt_succ_self _), hknew⟩) (ih.mp hi)
        · exact Or.inr ⟨m, Nat.lt_succ_self _, hi⟩
      · rintro (hi | ⟨k, hk, hi⟩)
        · exact Finset.mem_union_left _ (ih.mpr (Or.inl hi))
        · by_cases hkm : k < m
          · exact Finset.mem_union_left _ (ih.mpr (Or.inr ⟨k, hkm, hi⟩))
          · have hkeq : k = m := Nat.eq_of_lt_succ_of_not_lt hk hkm
            subst hkeq
            exact Finset.mem_union_right _ hi

theorem mem_feedbackState_seenTarget_iff
    (lam x0 p0 : ℝ) (j : Fin n) (m : ℕ) :
    j ∈ (feedbackState sample lam x0 p0 m).seenTarget ↔
      j ∈ sample.initialSeenTarget x0 p0 ∨
        ∃ k < m, j ∈ (feedbackState sample lam x0 p0 k).newTarget sample lam := by
  induction m with
  | zero => simp [feedbackState, initialFeedbackState]
  | succ m ih =>
      rw [feedbackState_succ]
      constructor
      · intro hj
        simp only [FeedbackStepState.step, Finset.mem_union] at hj
        rcases hj with hj | hj
        · exact Or.imp_right (fun ⟨k, hk, hknew⟩ ↦
            ⟨k, Nat.lt_trans hk (Nat.lt_succ_self _), hknew⟩) (ih.mp hj)
        · exact Or.inr ⟨m, Nat.lt_succ_self _, hj⟩
      · rintro (hj | ⟨k, hk, hj⟩)
        · exact Finset.mem_union_left _ (ih.mpr (Or.inl hj))
        · by_cases hkm : k < m
          · exact Finset.mem_union_left _ (ih.mpr (Or.inr ⟨k, hkm, hj⟩))
          · have hkeq : k = m := Nat.eq_of_lt_succ_of_not_lt hk hkm
            subst hkeq
            exact Finset.mem_union_right _ hj

theorem mem_feedbackState_seenSource_mono
    (lam x0 p0 : ℝ) (i : Fin n) {m r : ℕ} (hmr : m ≤ r)
    (hi : i ∈ (feedbackState sample lam x0 p0 m).seenSource) :
    i ∈ (feedbackState sample lam x0 p0 r).seenSource := by
  revert hi
  induction hmr with
  | refl =>
      intro hi
      exact hi
  | @step r hmr ih =>
      intro hi
      rw [feedbackState_succ]
      exact Finset.mem_union_left _ (ih hi)

theorem mem_feedbackState_seenTarget_mono
    (lam x0 p0 : ℝ) (j : Fin n) {m r : ℕ} (hmr : m ≤ r)
    (hj : j ∈ (feedbackState sample lam x0 p0 m).seenTarget) :
    j ∈ (feedbackState sample lam x0 p0 r).seenTarget := by
  revert hj
  induction hmr with
  | refl =>
      intro hj
      exact hj
  | @step r hmr ih =>
      intro hj
      rw [feedbackState_succ]
      exact Finset.mem_union_left _ (ih hj)

theorem sourceEventTime_le_iff_seen_diff
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) (t : ℝ≥0) :
    sourceEventTime hlam0 hlamHalf x0 p0 i sample ≤ (t : WithTop ℝ≥0) ↔
      sample.NoFeedbackTies lam x0 p0 ∧
        i ∈ (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
          sample.initialSeenSource x0 p0 := by
  classical
  rw [sample.sourceEventTime_le_iff_exists hlam0 hlamHalf x0 p0 i t]
  constructor
  · rintro ⟨hgood, ⟨m, hm, hmt⟩⟩
    have hI : (⟨m.val + 1, by omega⟩ : Fin (2 * n + 1)) ∈
        sample.elapsedIndexSet hlam0 hlamHalf x0 p0 t := by
      simp only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmt
    have hleI : (⟨m.val + 1, by omega⟩ : Fin (2 * n + 1)) ≤
        sample.elapsedIndex hlam0 hlamHalf x0 p0 t :=
      le_maxFinsetIndex ⟨0, by omega⟩
        ⟨0, sample.zero_mem_elapsedIndexSet hlam0 hlamHalf x0 p0 t⟩ hI
    have hseen : i ∈ (feedbackState sample lam x0 p0 (m.val + 1)).seenSource := by
      exact (sample.mem_feedbackState_seenSource_iff lam x0 p0 i (m.val + 1)).mpr
        (Or.inr ⟨m.val, by omega, hm⟩)
    have hseen_idx : i ∈ (feedbackState sample lam x0 p0
        (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val).seenSource :=
      sample.mem_feedbackState_seenSource_mono lam x0 p0 i (show m.val + 1 ≤
        (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val by exact hleI) hseen
    have hseen' : i ∈
        (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource := by
      change i ∈ (feedbackState sample lam x0 p0
        (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val).seenSource
      exact hseen_idx
    exact ⟨hgood, Finset.mem_sdiff.mpr ⟨hseen', by
      intro hi0
      have hi0_seen : i ∈ (feedbackState sample lam x0 p0 m.val).seenSource := by
        apply sample.mem_feedbackState_seenSource_mono lam x0 p0 i (Nat.zero_le _)
        simpa [feedbackState_zero, initialFeedbackState] using hi0
      exact (Finset.disjoint_left.mp
        (FeedbackStepState.newSource_disjoint_seenSource sample lam
          (feedbackState sample lam x0 p0 m.val))) hm hi0_seen⟩⟩
  · rintro ⟨hgood, hi⟩
    rw [Finset.mem_sdiff] at hi
    have hiSeenAt : i ∈ (feedbackState sample lam x0 p0
        (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val).seenSource := by
      change i ∈ (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource
      exact hi.1
    have hidx := sample.mem_feedbackState_seenSource_iff lam x0 p0 i
      (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val
    rcases hidx.mp hiSeenAt with hi0 | ⟨m, hm, hmnew⟩
    · exact False.elim (hi.2 hi0)
    · have hmfin : m < 2 * n := by omega
      let M : Fin (2 * n) := ⟨m, hmfin⟩
      have hMtime : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m + 1) ≤ t := by
        have hmem := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
        have hle : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0
            (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val ≤ t := by
          simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
        have hsucc : m + 1 ≤ (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val :=
          Nat.succ_le_of_lt hm
        have hmono := sample.elapsedFeedbackKnot_mono hlam0 hlamHalf x0 p0 hsucc
        exact hmono.trans hle
      exact ⟨hgood, ⟨M, hmnew, hMtime⟩⟩

theorem targetEventTime_le_iff_seen_diff
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) (t : ℝ≥0) :
    targetEventTime hlam0 hlamHalf x0 p0 j sample ≤ (t : WithTop ℝ≥0) ↔
      sample.NoFeedbackTies lam x0 p0 ∧
        j ∈ (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
          sample.initialSeenTarget x0 p0 := by
  classical
  rw [sample.targetEventTime_le_iff_exists hlam0 hlamHalf x0 p0 j t]
  constructor
  · rintro ⟨hgood, ⟨m, hm, hmt⟩⟩
    have hI : (⟨m.val + 1, by omega⟩ : Fin (2 * n + 1)) ∈
        sample.elapsedIndexSet hlam0 hlamHalf x0 p0 t := by
      simp only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmt
    have hleI : (⟨m.val + 1, by omega⟩ : Fin (2 * n + 1)) ≤
        sample.elapsedIndex hlam0 hlamHalf x0 p0 t :=
      le_maxFinsetIndex ⟨0, by omega⟩
        ⟨0, sample.zero_mem_elapsedIndexSet hlam0 hlamHalf x0 p0 t⟩ hI
    have hseen : j ∈ (feedbackState sample lam x0 p0 (m.val + 1)).seenTarget := by
      exact (sample.mem_feedbackState_seenTarget_iff lam x0 p0 j (m.val + 1)).mpr
        (Or.inr ⟨m.val, by omega, hm⟩)
    have hseen' : j ∈ (feedbackState sample lam x0 p0
        (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val).seenTarget := by
      exact sample.mem_feedbackState_seenTarget_mono lam x0 p0 j (show m.val + 1 ≤
        (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val by exact hleI) hseen
    exact ⟨hgood, Finset.mem_sdiff.mpr ⟨hseen', by
      intro hi0
      have hj0_seen : j ∈ (feedbackState sample lam x0 p0 m.val).seenTarget := by
        apply sample.mem_feedbackState_seenTarget_mono lam x0 p0 j (Nat.zero_le _)
        simpa [feedbackState_zero, initialFeedbackState] using hi0
      exact (Finset.disjoint_left.mp
        (FeedbackStepState.newTarget_disjoint_seenTarget sample lam
          (feedbackState sample lam x0 p0 m.val))) hm hj0_seen⟩⟩
  · rintro ⟨hgood, hi⟩
    rw [Finset.mem_sdiff] at hi
    have hiSeenAt : j ∈ (feedbackState sample lam x0 p0
        (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val).seenTarget := by
      change j ∈ (sample.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget
      exact hi.1
    rcases (sample.mem_feedbackState_seenTarget_iff lam x0 p0 j
      (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val).mp hiSeenAt with hi0 | ⟨m, hm, hmnew⟩
    · exact False.elim (hi.2 hi0)
    · have hmfin : m < 2 * n := by omega
      let M : Fin (2 * n) := ⟨m, hmfin⟩
      have hMtime : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m + 1) ≤ t := by
        have hmem := sample.elapsedIndex_mem hlam0 hlamHalf x0 p0 t
        have hle : sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0
            (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val ≤ t := by
          simpa only [elapsedIndexSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
        have hsucc : m + 1 ≤ (sample.elapsedIndex hlam0 hlamHalf x0 p0 t).val :=
          Nat.succ_le_of_lt hm
        have hmono := sample.elapsedFeedbackKnot_mono hlam0 hlamHalf x0 p0 hsucc
        exact hmono.trans hle
      exact ⟨hgood, ⟨M, hmnew, hMtime⟩⟩

/-! ## Safe counts and the current identity -/

noncomputable def safeSourceCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) : FiniteSample n → ℕ :=
  CountingProcess.finiteEventCountTop
    (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t

noncomputable def safeTargetCount
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) : FiniteSample n → ℕ :=
  CountingProcess.finiteEventCountTop
    (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t

theorem safeSourceCount_eq_card_diff
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (ω : FiniteSample n) :
    safeSourceCount hlam0 hlamHalf x0 p0 t ω =
      if ω.NoFeedbackTies lam x0 p0 then
        ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
          ω.initialSeenSource x0 p0).card
      else 0 := by
  classical
  by_cases hgood : ω.NoFeedbackTies lam x0 p0
  · have hset : (Finset.univ.filter (fun i : Fin n ↦
        sourceEventTime hlam0 hlamHalf x0 p0 i ω ≤ (t : WithTop ℝ≥0))) =
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
          ω.initialSeenSource x0 p0 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [sourceEventTime_le_iff_seen_diff]
      simp [hgood]
    unfold safeSourceCount CountingProcess.finiteEventCountTop
    rw [hset]
    simp [hgood]
  · have hset : (Finset.univ.filter (fun i : Fin n ↦
        sourceEventTime hlam0 hlamHalf x0 p0 i ω ≤ (t : WithTop ℝ≥0))) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have htop : sourceEventTime hlam0 hlamHalf x0 p0 i ω = ⊤ := by
        simp [sourceEventTime, hgood]
      rw [htop]
      constructor
      · intro hle
        exact False.elim (WithTop.not_top_le_coe t hle)
      · intro hi
        simp at hi
    unfold safeSourceCount CountingProcess.finiteEventCountTop
    rw [hset]
    simp [hgood]

theorem safeTargetCount_eq_card_diff
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (ω : FiniteSample n) :
    safeTargetCount hlam0 hlamHalf x0 p0 t ω =
      if ω.NoFeedbackTies lam x0 p0 then
        ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
          ω.initialSeenTarget x0 p0).card
      else 0 := by
  classical
  by_cases hgood : ω.NoFeedbackTies lam x0 p0
  · have hset : (Finset.univ.filter (fun j : Fin n ↦
        targetEventTime hlam0 hlamHalf x0 p0 j ω ≤ (t : WithTop ℝ≥0))) =
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
          ω.initialSeenTarget x0 p0 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [targetEventTime_le_iff_seen_diff]
      simp [hgood]
    unfold safeTargetCount CountingProcess.finiteEventCountTop
    rw [hset]
    simp [hgood]
  · have hset : (Finset.univ.filter (fun j : Fin n ↦
        targetEventTime hlam0 hlamHalf x0 p0 j ω ≤ (t : WithTop ℝ≥0))) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have htop : targetEventTime hlam0 hlamHalf x0 p0 j ω = ⊤ := by
        simp [targetEventTime, hgood]
      rw [htop]
      constructor
      · intro hle
        exact False.elim (WithTop.not_top_le_coe t hle)
      · intro hi
        simp at hi
    unfold safeTargetCount CountingProcess.finiteEventCountTop
    rw [hset]
    simp [hgood]

noncomputable def safeK0
    (lam x0 p0 : ℝ) : FiniteSample n → ℤ :=
  fun ω ↦ if ω.NoFeedbackTies lam x0 p0 then ω.initialFeedbackCurrent x0 p0 else 0

noncomputable def safeCurrentAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) : FiniteSample n → ℤ :=
  fun ω ↦ if ω.NoFeedbackTies lam x0 p0 then
    (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).current else 0

theorem safeCurrentAt_eq_K0_add_counts
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (ω : FiniteSample n) :
    safeCurrentAt hlam0 hlamHalf x0 p0 t ω =
      safeK0 lam x0 p0 ω +
        (safeSourceCount hlam0 hlamHalf x0 p0 t ω : ℤ) -
        safeTargetCount hlam0 hlamHalf x0 p0 t ω := by
  classical
  by_cases hgood : ω.NoFeedbackTies lam x0 p0
  · have hsource_subset : ω.initialSeenSource x0 p0 ⊆
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource := by
      intro i hi
      change i ∈ (feedbackState ω lam x0 p0
        (ω.elapsedIndex hlam0 hlamHalf x0 p0 t).val).seenSource
      apply ω.mem_feedbackState_seenSource_mono lam x0 p0 i (Nat.zero_le _)
      simpa [feedbackState_zero, initialFeedbackState] using hi
    have htarget_subset : ω.initialSeenTarget x0 p0 ⊆
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget := by
      intro j hj
      change j ∈ (feedbackState ω lam x0 p0
        (ω.elapsedIndex hlam0 hlamHalf x0 p0 t).val).seenTarget
      apply ω.mem_feedbackState_seenTarget_mono lam x0 p0 j (Nat.zero_le _)
      simpa [feedbackState_zero, initialFeedbackState] using hj
    have hsource_card :
        ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
          ω.initialSeenSource x0 p0).card +
          (ω.initialSeenSource x0 p0).card =
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource.card := by
      have hcard := Finset.card_sdiff_add_card
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource
        (ω.initialSeenSource x0 p0)
      rw [Finset.union_eq_left.mpr hsource_subset] at hcard
      exact hcard
    have htarget_card :
        ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
          ω.initialSeenTarget x0 p0).card +
          (ω.initialSeenTarget x0 p0).card =
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget.card := by
      have hcard := Finset.card_sdiff_add_card
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget
        (ω.initialSeenTarget x0 p0)
      rw [Finset.union_eq_left.mpr htarget_subset] at hcard
      exact hcard
    simp only [safeCurrentAt, safeK0, hgood, ↓reduceIte]
    rw [safeSourceCount_eq_card_diff, safeTargetCount_eq_card_diff]
    simp only [hgood, ↓reduceIte]
    change (feedbackState ω lam x0 p0
      (ω.elapsedIndex hlam0 hlamHalf x0 p0 t).val).current = _
    rw [feedbackState_current_eq_card_sub]
    have hsource_int :
        ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource.card : ℤ) =
          (ω.initialSeenSource x0 p0).card +
            ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
              ω.initialSeenSource x0 p0).card := by
      have hcast :
          ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource.card : ℤ) =
            ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
              ω.initialSeenSource x0 p0).card +
              (ω.initialSeenSource x0 p0).card := by
        exact_mod_cast hsource_card.symm
      omega
    have htarget_int :
        ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget.card : ℤ) =
          (ω.initialSeenTarget x0 p0).card +
            ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
              ω.initialSeenTarget x0 p0).card := by
      have hcast :
          ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget.card : ℤ) =
            ((ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
              ω.initialSeenTarget x0 p0).card +
              (ω.initialSeenTarget x0 p0).card := by
        exact_mod_cast htarget_card.symm
      omega
    simp only [feedbackStateAtElapsed] at hsource_int htarget_int
    simp only [initialFeedbackCurrent]
    simp only [feedbackStateAtElapsed]
    omega
  · simp [safeCurrentAt, safeK0, hgood, safeSourceCount_eq_card_diff,
      safeTargetCount_eq_card_diff]

/-! ## Raw snapshot projections -/

theorem measurable_seenSourceAtElapsed_raw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (_i : Fin n) :
    Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun ω : FiniteSample n ↦
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource) := by
  have hsnap := stronglyAdapted_rawRevealedSnapshot
    (n := n) hlam0 hlamHalf x0 p0
  have hseen : Measurable (fun z : RevealedSnapshot n ↦
      (FeedbackStepState.unpack z.1).seenSource) :=
    FeedbackStepState.measurable_seenSource.comp
      (FeedbackStepState.measurable_unpack.comp measurable_fst)
  have hcomp : Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun ω : FiniteSample n ↦
        (FeedbackStepState.unpack
          ((ω.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t).1)).seenSource) :=
    hseen.comp (hsnap t).measurable
  simpa [revealedSnapshotAtElapsed, revealedSnapshotFromState] using hcomp

theorem measurable_seenTargetAtElapsed_raw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) :
    Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun ω : FiniteSample n ↦
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget) := by
  have hsnap := stronglyAdapted_rawRevealedSnapshot
    (n := n) hlam0 hlamHalf x0 p0
  have hseen : Measurable (fun z : RevealedSnapshot n ↦
      (FeedbackStepState.unpack z.1).seenTarget) :=
    FeedbackStepState.measurable_seenTarget.comp
      (FeedbackStepState.measurable_unpack.comp measurable_fst)
  have hcomp : Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun ω : FiniteSample n ↦
        (FeedbackStepState.unpack
          ((ω.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t).1)).seenTarget) :=
    hseen.comp (hsnap t).measurable
  simpa [revealedSnapshotAtElapsed, revealedSnapshotFromState] using hcomp

theorem measurable_currentAtElapsed_raw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) :
    Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun ω : FiniteSample n ↦
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).current) := by
  have hsnap := stronglyAdapted_rawRevealedSnapshot
    (n := n) hlam0 hlamHalf x0 p0
  have hcurrent : Measurable (fun z : RevealedSnapshot n ↦
      (FeedbackStepState.unpack z.1).current) :=
    FeedbackStepState.measurable_current.comp
      (FeedbackStepState.measurable_unpack.comp measurable_fst)
  have hcomp : Measurable[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (fun ω : FiniteSample n ↦
        (FeedbackStepState.unpack
          ((ω.revealedSnapshotAtElapsed hlam0 hlamHalf x0 p0 t).1)).current) :=
    hcurrent.comp (hsnap t).measurable
  simpa [revealedSnapshotAtElapsed, revealedSnapshotFromState] using hcomp

theorem measurableSet_mem_seenSourceAtElapsed_raw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (i : Fin n) :
    MeasurableSet[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      {ω : FiniteSample n |
        i ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource} :=
  (measurable_seenSourceAtElapsed_raw (n := n) hlam0 hlamHalf x0 p0 t i)
    (measurableSet_mem_finset i)

theorem measurableSet_mem_seenTargetAtElapsed_raw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (j : Fin n) :
    MeasurableSet[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      {ω : FiniteSample n |
        j ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget} :=
  (measurable_seenTargetAtElapsed_raw (n := n) hlam0 hlamHalf x0 p0 t)
    (measurableSet_mem_finset j)

theorem measurableSet_mem_initialSeenSource_raw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) :
    MeasurableSet[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      {ω : FiniteSample n | i ∈ ω.initialSeenSource x0 p0} := by
  have hstate := measurableSet_mem_seenSourceAtElapsed_raw
    (n := n) hlam0 hlamHalf x0 p0 0 i
  have hzero (ω : FiniteSample n) :
      ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 0 =
        ω.initialFeedbackState x0 p0 := by
    simpa using
      (ω.feedbackStateAtElapsed_at_elapsedFeedbackKnot hlam0 hlamHalf x0 p0
        (show 0 ≤ 2 * n by omega))
  convert hstate using 1
  ext ω
  change i ∈ ω.initialSeenSource x0 p0 ↔
    i ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 0).seenSource
  rw [hzero]
  rfl

theorem measurableSet_mem_initialSeenTarget_raw
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) :
    MeasurableSet[
      rawRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      {ω : FiniteSample n | j ∈ ω.initialSeenTarget x0 p0} := by
  have hstate := measurableSet_mem_seenTargetAtElapsed_raw
    (n := n) hlam0 hlamHalf x0 p0 0 j
  have hzero (ω : FiniteSample n) :
      ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 0 =
        ω.initialFeedbackState x0 p0 := by
    simpa using
      (ω.feedbackStateAtElapsed_at_elapsedFeedbackKnot hlam0 hlamHalf x0 p0
        (show 0 ≤ 2 * n by omega))
  convert hstate using 1
  ext ω
  change j ∈ ω.initialSeenTarget x0 p0 ↔
    j ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 0).seenTarget
  rw [hzero]
  rfl

theorem measurableSet_mem_seenSourceAtElapsed_usual
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (i : Fin n) :
    MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      {ω : FiniteSample n |
        i ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource} :=
  (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf x0 p0 t) _
    (measurableSet_mem_seenSourceAtElapsed_raw
      (n := n) hlam0 hlamHalf x0 p0 t i)

theorem measurableSet_mem_seenTargetAtElapsed_usual
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (j : Fin n) :
    MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      {ω : FiniteSample n |
        j ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget} :=
  (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf x0 p0 t) _
    (measurableSet_mem_seenTargetAtElapsed_raw
      (n := n) hlam0 hlamHalf x0 p0 t j)

theorem measurableSet_mem_initialSeenSource_usual_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) :
    MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      {ω : FiniteSample n | i ∈ ω.initialSeenSource x0 p0} :=
  (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf x0 p0 0) _
    (measurableSet_mem_initialSeenSource_raw
      (n := n) hlam0 hlamHalf x0 p0 i)

theorem measurableSet_mem_initialSeenTarget_usual_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) :
    MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      {ω : FiniteSample n | j ∈ ω.initialSeenTarget x0 p0} :=
  (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf x0 p0 0) _
    (measurableSet_mem_initialSeenTarget_raw
      (n := n) hlam0 hlamHalf x0 p0 j)

theorem measurableSet_mem_initialSeenSource_usual
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (i : Fin n) :
    MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      {ω : FiniteSample n | i ∈ ω.initialSeenSource x0 p0} :=
  (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).mono bot_le _
    (measurableSet_mem_initialSeenSource_usual_zero
      (n := n) hlam0 hlamHalf x0 p0 i)

theorem measurableSet_mem_initialSeenTarget_usual
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (j : Fin n) :
    MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      {ω : FiniteSample n | j ∈ ω.initialSeenTarget x0 p0} :=
  (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).mono bot_le _
    (measurableSet_mem_initialSeenTarget_usual_zero
      (n := n) hlam0 hlamHalf x0 p0 j)

theorem sourceEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (i : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (sourceEventTime hlam0 hlamHalf x0 p0 i) := by
  intro t
  have hgood : MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (feedbackGoodEvent (n := n) lam x0 p0) :=
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).mono bot_le _
      (measurableSet_feedbackGoodEvent_usual_zero
        (n := n) hlam0 hlamHalf x0 p0)
  have hseen := measurableSet_mem_seenSourceAtElapsed_usual
    (n := n) hlam0 hlamHalf x0 p0 t i
  have hinitial := measurableSet_mem_initialSeenSource_usual
    (n := n) hlam0 hlamHalf x0 p0 t i
  have hdiff : MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      {ω : FiniteSample n |
        i ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
          ω.initialSeenSource x0 p0} := by
    rw [show {ω : FiniteSample n |
        i ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
          ω.initialSeenSource x0 p0} =
      {ω | i ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource} ∩
        {ω | i ∉ ω.initialSeenSource x0 p0} by
      ext ω
      simp]
    exact hseen.inter hinitial.compl
  rw [show {ω : FiniteSample n |
      sourceEventTime hlam0 hlamHalf x0 p0 i ω ≤ (t : WithTop ℝ≥0)} =
      feedbackGoodEvent (n := n) lam x0 p0 ∩
        {ω : FiniteSample n |
          i ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenSource \
            ω.initialSeenSource x0 p0} by
    ext ω
    simp only [feedbackGoodEvent, mem_ofPred_eq, mem_inter_iff]
    exact ω.sourceEventTime_le_iff_seen_diff hlam0 hlamHalf x0 p0 i t]
  exact hgood.inter hdiff

theorem targetEventTime_isStoppingTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (j : Fin n) :
    IsStoppingTime
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (targetEventTime hlam0 hlamHalf x0 p0 j) := by
  intro t
  have hgood : MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (feedbackGoodEvent (n := n) lam x0 p0) :=
    (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0).mono bot_le _
      (measurableSet_feedbackGoodEvent_usual_zero
        (n := n) hlam0 hlamHalf x0 p0)
  have hseen := measurableSet_mem_seenTargetAtElapsed_usual
    (n := n) hlam0 hlamHalf x0 p0 t j
  have hinitial := measurableSet_mem_initialSeenTarget_usual
    (n := n) hlam0 hlamHalf x0 p0 t j
  have hdiff : MeasurableSet[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      {ω : FiniteSample n |
        j ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
          ω.initialSeenTarget x0 p0} := by
    rw [show {ω : FiniteSample n |
        j ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
          ω.initialSeenTarget x0 p0} =
      {ω | j ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget} ∩
        {ω | j ∉ ω.initialSeenTarget x0 p0} by
      ext ω
      simp]
    exact hseen.inter hinitial.compl
  rw [show {ω : FiniteSample n |
      targetEventTime hlam0 hlamHalf x0 p0 j ω ≤ (t : WithTop ℝ≥0)} =
      feedbackGoodEvent (n := n) lam x0 p0 ∩
        {ω : FiniteSample n |
          j ∈ (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 t).seenTarget \
            ω.initialSeenTarget x0 p0} by
    ext ω
    simp only [feedbackGoodEvent, mem_ofPred_eq, mem_inter_iff]
    exact ω.targetEventTime_le_iff_seen_diff hlam0 hlamHalf x0 p0 j t]
  exact hgood.inter hdiff

/-! ## Path properties of the event times and counts -/

theorem candidates_nonempty_of_mem_newSource
    (lam : ℝ) (state : FeedbackStepState n) (i : Fin n)
    (hi : i ∈ state.newSource sample lam) :
    (state.candidates sample lam).Nonempty := by
  by_contra h
  have hzero : state.candidates sample lam = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  have hall := (state.candidates_eq_empty_iff sample lam).mp hzero
  have : state.newSource sample lam = ∅ := by
    simp [FeedbackStepState.newSource, hall.1]
  rw [this] at hi
  simp at hi

theorem candidates_nonempty_of_mem_newTarget
    (lam : ℝ) (state : FeedbackStepState n) (j : Fin n)
    (hj : j ∈ state.newTarget sample lam) :
    (state.candidates sample lam).Nonempty := by
  by_contra h
  have hzero : state.candidates sample lam = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  have hall := (state.candidates_eq_empty_iff sample lam).mp hzero
  have : state.newTarget sample lam = ∅ := by
    simp [FeedbackStepState.newTarget, hall.2]
  rw [this] at hj
  simp at hj

theorem elapsedFeedbackKnot_pos_of_mem_newSource
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} {i : Fin n}
    (hi : i ∈ (feedbackState sample lam x0 p0 m).newSource sample lam) :
    0 < sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m + 1) := by
  have hcand := sample.candidates_nonempty_of_mem_newSource lam
    (feedbackState sample lam x0 p0 m) i hi
  have hstrict := sample.feedbackState_x_strictMono_step hlam0 hlamHalf x0 p0 m hcand
  have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0 (Nat.zero_le m)
  have hx : x0 < sample.feedbackKnot lam x0 p0 (m + 1) := by
    have hmono' : x0 ≤ sample.feedbackKnot lam x0 p0 m := by
      simpa [feedbackKnot, feedbackState_zero, initialFeedbackState] using hmono
    have hstrict' : sample.feedbackKnot lam x0 p0 m <
        sample.feedbackKnot lam x0 p0 (m + 1) := by
      simpa [feedbackKnot] using hstrict
    exact hmono'.trans_lt hstrict'
  apply NNReal.coe_pos.mp
  simpa only [coe_elapsedFeedbackKnot] using (sub_pos.mpr hx)

theorem elapsedFeedbackKnot_pos_of_mem_newTarget
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m : ℕ} {j : Fin n}
    (hj : j ∈ (feedbackState sample lam x0 p0 m).newTarget sample lam) :
    0 < sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m + 1) := by
  have hcand := sample.candidates_nonempty_of_mem_newTarget lam
    (feedbackState sample lam x0 p0 m) j hj
  have hstrict := sample.feedbackState_x_strictMono_step hlam0 hlamHalf x0 p0 m hcand
  have hmono := sample.feedbackState_x_mono hlam0 hlamHalf x0 p0 (Nat.zero_le m)
  have hx : x0 < sample.feedbackKnot lam x0 p0 (m + 1) := by
    have hmono' : x0 ≤ sample.feedbackKnot lam x0 p0 m := by
      simpa [feedbackKnot, feedbackState_zero, initialFeedbackState] using hmono
    have hstrict' : sample.feedbackKnot lam x0 p0 m <
        sample.feedbackKnot lam x0 p0 (m + 1) := by
      simpa [feedbackKnot] using hstrict
    exact hmono'.trans_lt hstrict'
  apply NNReal.coe_pos.mp
  simpa only [coe_elapsedFeedbackKnot] using (sub_pos.mpr hx)

theorem sourceEventTime_eq_top_or_pos
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) (i : Fin n) :
    sourceEventTime hlam0 hlamHalf x0 p0 i ω = ⊤ ∨
      (0 : WithTop ℝ≥0) < sourceEventTime hlam0 hlamHalf x0 p0 i ω := by
  classical
  by_cases hgood : ω.NoFeedbackTies lam x0 p0
  · by_cases hS : (ω.sourceEventSet lam x0 p0 i).Nonempty
    · right
      simp only [sourceEventTime, hgood, ↓reduceIte, sourceEventTimeRaw, dite_eq_left hS]
      exact_mod_cast ω.elapsedFeedbackKnot_pos_of_mem_newSource hlam0 hlamHalf x0 p0
        (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
    · left
      simp [sourceEventTime, hgood, sourceEventTimeRaw, hS]
  · left
    simp [sourceEventTime, hgood]

theorem targetEventTime_eq_top_or_pos
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) (j : Fin n) :
    targetEventTime hlam0 hlamHalf x0 p0 j ω = ⊤ ∨
      (0 : WithTop ℝ≥0) < targetEventTime hlam0 hlamHalf x0 p0 j ω := by
  classical
  by_cases hgood : ω.NoFeedbackTies lam x0 p0
  · by_cases hS : (ω.targetEventSet lam x0 p0 j).Nonempty
    · right
      simp only [targetEventTime, hgood, ↓reduceIte,
        targetEventTimeRaw, dite_eq_left hS]
      exact_mod_cast ω.elapsedFeedbackKnot_pos_of_mem_newTarget hlam0 hlamHalf x0 p0
        (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
    · left
      simp [targetEventTime, hgood, targetEventTimeRaw, hS]
  · left
    simp [targetEventTime, hgood]

theorem elapsedFeedbackKnot_strict_of_newSource_steps
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m r : ℕ} (hmr : m < r) {i j : Fin n}
    (_hi : i ∈ (feedbackState sample lam x0 p0 m).newSource sample lam)
    (hj : j ∈ (feedbackState sample lam x0 p0 r).newSource sample lam) :
    sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m + 1) <
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (r + 1) := by
  have hcand := sample.candidates_nonempty_of_mem_newSource lam
    (feedbackState sample lam x0 p0 r) j hj
  have hstrict := sample.feedbackState_x_strictMono_step hlam0 hlamHalf x0 p0 r hcand
  have hmono : sample.feedbackKnot lam x0 p0 (m + 1) ≤
      sample.feedbackKnot lam x0 p0 r :=
    sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
      (Nat.succ_le_of_lt hmr)
  have hx : sample.feedbackKnot lam x0 p0 (m + 1) <
      sample.feedbackKnot lam x0 p0 (r + 1) := by
    have hstrict' : sample.feedbackKnot lam x0 p0 r <
        sample.feedbackKnot lam x0 p0 (r + 1) := by
      simpa [feedbackKnot] using hstrict
    exact hmono.trans_lt hstrict'
  apply NNReal.coe_lt_coe.mp
  simpa only [coe_elapsedFeedbackKnot] using (sub_lt_sub_right hx x0)

theorem elapsedFeedbackKnot_strict_of_newTarget_steps
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) {m r : ℕ} (hmr : m < r) {i j : Fin n}
    (_hi : i ∈ (feedbackState sample lam x0 p0 m).newTarget sample lam)
    (hj : j ∈ (feedbackState sample lam x0 p0 r).newTarget sample lam) :
    sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m + 1) <
      sample.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (r + 1) := by
  have hcand := sample.candidates_nonempty_of_mem_newTarget lam
    (feedbackState sample lam x0 p0 r) j hj
  have hstrict := sample.feedbackState_x_strictMono_step hlam0 hlamHalf x0 p0 r hcand
  have hmono : sample.feedbackKnot lam x0 p0 (m + 1) ≤
      sample.feedbackKnot lam x0 p0 r :=
    sample.feedbackState_x_mono hlam0 hlamHalf x0 p0
      (Nat.succ_le_of_lt hmr)
  have hx : sample.feedbackKnot lam x0 p0 (m + 1) <
      sample.feedbackKnot lam x0 p0 (r + 1) := by
    have hstrict' : sample.feedbackKnot lam x0 p0 r <
        sample.feedbackKnot lam x0 p0 (r + 1) := by
      simpa [feedbackKnot] using hstrict
    exact hmono.trans_lt hstrict'
  apply NNReal.coe_lt_coe.mp
  simpa only [coe_elapsedFeedbackKnot] using (sub_lt_sub_right hx x0)

theorem sourceEventTime_injOn_of_noFeedbackTies
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) (hgood : ω.NoFeedbackTies lam x0 p0) :
    ∀ i j : Fin n,
      sourceEventTime hlam0 hlamHalf x0 p0 i ω ≠ ⊤ →
      sourceEventTime hlam0 hlamHalf x0 p0 j ω ≠ ⊤ →
      sourceEventTime hlam0 hlamHalf x0 p0 i ω =
        sourceEventTime hlam0 hlamHalf x0 p0 j ω → i = j := by
  classical
  intro i j hif hjf heq
  have hSi : (ω.sourceEventSet lam x0 p0 i).Nonempty := by
    by_contra h
    apply hif
    simp [sourceEventTime, hgood, sourceEventTimeRaw, h]
  have hSj : (ω.sourceEventSet lam x0 p0 j).Nonempty := by
    by_contra h
    apply hjf
    simp [sourceEventTime, hgood, sourceEventTimeRaw, h]
  let m := (ω.sourceEventSet lam x0 p0 i).min' hSi
  let r := (ω.sourceEventSet lam x0 p0 j).min' hSj
  have hmi : i ∈ (feedbackState ω lam x0 p0 m.val).newSource ω lam :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hSi)).2
  have hmj : j ∈ (feedbackState ω lam x0 p0 r.val).newSource ω lam :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hSj)).2
  have htime : ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) =
      ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (r.val + 1) := by
    have heq' := heq
    simp only [sourceEventTime, hgood, ↓reduceIte, sourceEventTimeRaw,
      dite_eq_left hSi, dite_eq_left hSj] at heq'
    exact WithTop.coe_injective heq'
  by_cases hmr : m.val = r.val
  · have hcard :
        ((feedbackState ω lam x0 p0 m.val).newSource ω lam).card ≤ 1 := by
      have hsum := hgood m.val (by omega)
      omega
    exact (Finset.card_le_one.mp hcard) i hmi j (by simpa [hmr] using hmj)
  · rcases lt_or_gt_of_ne hmr with hlt | hgt
    · have hlt_time := ω.elapsedFeedbackKnot_strict_of_newSource_steps
        hlam0 hlamHalf x0 p0 hlt hmi hmj
      exact False.elim ((ne_of_lt hlt_time) htime)
    · have hlt_time := ω.elapsedFeedbackKnot_strict_of_newSource_steps
        hlam0 hlamHalf x0 p0 hgt hmj hmi
      exact False.elim ((ne_of_lt hlt_time) htime.symm)

theorem targetEventTime_injOn_of_noFeedbackTies
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) (hgood : ω.NoFeedbackTies lam x0 p0) :
    ∀ i j : Fin n,
      targetEventTime hlam0 hlamHalf x0 p0 i ω ≠ ⊤ →
      targetEventTime hlam0 hlamHalf x0 p0 j ω ≠ ⊤ →
      targetEventTime hlam0 hlamHalf x0 p0 i ω =
        targetEventTime hlam0 hlamHalf x0 p0 j ω → i = j := by
  classical
  intro i j hif hjf heq
  have hSi : (ω.targetEventSet lam x0 p0 i).Nonempty := by
    by_contra h
    apply hif
    simp [targetEventTime, hgood, targetEventTimeRaw, h]
  have hSj : (ω.targetEventSet lam x0 p0 j).Nonempty := by
    by_contra h
    apply hjf
    simp [targetEventTime, hgood, targetEventTimeRaw, h]
  let m := (ω.targetEventSet lam x0 p0 i).min' hSi
  let r := (ω.targetEventSet lam x0 p0 j).min' hSj
  have hmi : i ∈ (feedbackState ω lam x0 p0 m.val).newTarget ω lam :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hSi)).2
  have hmj : j ∈ (feedbackState ω lam x0 p0 r.val).newTarget ω lam :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hSj)).2
  have htime : ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) =
      ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (r.val + 1) := by
    have heq' := heq
    simp only [targetEventTime, hgood, ↓reduceIte, targetEventTimeRaw,
      dite_eq_left hSi, dite_eq_left hSj] at heq'
    exact WithTop.coe_injective heq'
  by_cases hmr : m.val = r.val
  · have hcard :
        ((feedbackState ω lam x0 p0 m.val).newTarget ω lam).card ≤ 1 := by
      have hsum := hgood m.val (by omega)
      omega
    exact (Finset.card_le_one.mp hcard) i hmi j (by simpa [hmr] using hmj)
  · rcases lt_or_gt_of_ne hmr with hlt | hgt
    · have hlt_time := ω.elapsedFeedbackKnot_strict_of_newTarget_steps
        hlam0 hlamHalf x0 p0 hlt hmi hmj
      exact False.elim ((ne_of_lt hlt_time) htime)
    · have hlt_time := ω.elapsedFeedbackKnot_strict_of_newTarget_steps
        hlam0 hlamHalf x0 p0 hgt hmj hmi
      exact False.elim ((ne_of_lt hlt_time) htime.symm)

theorem safeSourceCount_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) :
    safeSourceCount hlam0 hlamHalf x0 p0 0 ω = 0 := by
  apply CountingProcess.finiteEventCountTop_zero
  intro i
  exact ω.sourceEventTime_eq_top_or_pos hlam0 hlamHalf x0 p0 i

theorem safeTargetCount_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) :
    safeTargetCount hlam0 hlamHalf x0 p0 0 ω = 0 := by
  apply CountingProcess.finiteEventCountTop_zero
  intro j
  exact ω.targetEventTime_eq_top_or_pos hlam0 hlamHalf x0 p0 j

theorem safeSourceCount_mono
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) {s t : ℝ≥0} (hst : s ≤ t) :
    safeSourceCount hlam0 hlamHalf x0 p0 s ω ≤
      safeSourceCount hlam0 hlamHalf x0 p0 t ω :=
  CountingProcess.finiteEventCountTop_mono
    (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) ω hst

theorem safeTargetCount_mono
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) {s t : ℝ≥0} (hst : s ≤ t) :
    safeTargetCount hlam0 hlamHalf x0 p0 s ω ≤
      safeTargetCount hlam0 hlamHalf x0 p0 t ω :=
  CountingProcess.finiteEventCountTop_mono
    (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) ω hst

theorem safeSourceCount_rightContinuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s ↦ (safeSourceCount hlam0 hlamHalf x0 p0 s ω : ℝ)) (Ici t) t :=
  CountingProcess.finiteEventCountTop_rightContinuous
    (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) ω t

theorem safeTargetCount_rightContinuous
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s ↦ (safeTargetCount hlam0 hlamHalf x0 p0 s ω : ℝ)) (Ici t) t :=
  CountingProcess.finiteEventCountTop_rightContinuous
    (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) ω t

/-! ## Adapted counts and simple counting processes -/

theorem safeSourceCount_stronglyAdapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t ω ↦ (safeSourceCount hlam0 hlamHalf x0 p0 t ω : ℝ)) := by
  intro t
  let f : Fin n → FiniteSample n → ℝ := fun i ω ↦
    if sourceEventTime hlam0 hlamHalf x0 p0 i ω ≤ (t : WithTop ℝ≥0)
    then 1 else 0
  have hsum : StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (∑ i : Fin n, f i) := by
    apply Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin n)) (f := f)
    intro i hi
    have hmeas : Measurable[
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
        (fun ω : FiniteSample n ↦ f i ω) := by
      simp only [f]
      exact Measurable.ite
        ((sourceEventTime_isStoppingTime (n := n) hlam0 hlamHalf x0 p0 i) t)
        measurable_const measurable_const
    exact hmeas.stronglyMeasurable
  convert hsum using 1
  · funext ω
    simpa [f, safeSourceCount] using
      (CountingProcess.finiteEventCountTop_cast_eq_sum
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t ω)

theorem safeTargetCount_stronglyAdapted
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    StronglyAdapted
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t ω ↦ (safeTargetCount hlam0 hlamHalf x0 p0 t ω : ℝ)) := by
  intro t
  let f : Fin n → FiniteSample n → ℝ := fun j ω ↦
    if targetEventTime hlam0 hlamHalf x0 p0 j ω ≤ (t : WithTop ℝ≥0)
    then 1 else 0
  have hsum : StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
      (∑ j : Fin n, f j) := by
    apply Finset.stronglyMeasurable_sum (Finset.univ : Finset (Fin n)) (f := f)
    intro j hj
    have hmeas : Measurable[
        usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 t]
        (fun ω : FiniteSample n ↦ f j ω) := by
      simp only [f]
      exact Measurable.ite
        ((targetEventTime_isStoppingTime (n := n) hlam0 hlamHalf x0 p0 j) t)
        measurable_const measurable_const
    exact hmeas.stronglyMeasurable
  convert hsum using 1
  · funext ω
    simpa [f, safeTargetCount] using
      (CountingProcess.finiteEventCountTop_cast_eq_sum
        (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t ω)

theorem sourceEventTime_injective
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    ∀ (ω : FiniteSample n) (i j : Fin n),
      sourceEventTime hlam0 hlamHalf x0 p0 i ω ≠ ⊤ →
      sourceEventTime hlam0 hlamHalf x0 p0 j ω ≠ ⊤ →
      sourceEventTime hlam0 hlamHalf x0 p0 i ω =
        sourceEventTime hlam0 hlamHalf x0 p0 j ω → i = j := by
  intro ω i j hif hjf heq
  by_cases hgood : ω.NoFeedbackTies lam x0 p0
  · exact sourceEventTime_injOn_of_noFeedbackTies
      (n := n) hlam0 hlamHalf x0 p0 ω hgood i j hif hjf heq
  · have htop : sourceEventTime hlam0 hlamHalf x0 p0 i ω = ⊤ := by
      simp [sourceEventTime, hgood]
    exact False.elim (hif htop)

theorem targetEventTime_injective
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    ∀ (ω : FiniteSample n) (i j : Fin n),
      targetEventTime hlam0 hlamHalf x0 p0 i ω ≠ ⊤ →
      targetEventTime hlam0 hlamHalf x0 p0 j ω ≠ ⊤ →
      targetEventTime hlam0 hlamHalf x0 p0 i ω =
        targetEventTime hlam0 hlamHalf x0 p0 j ω → i = j := by
  intro ω i j hif hjf heq
  by_cases hgood : ω.NoFeedbackTies lam x0 p0
  · exact targetEventTime_injOn_of_noFeedbackTies
      (n := n) hlam0 hlamHalf x0 p0 ω hgood i j hif hjf heq
  · have htop : targetEventTime hlam0 hlamHalf x0 p0 i ω = ⊤ := by
      simp [targetEventTime, hgood]
    exact False.elim (hif htop)

theorem safeSourceCount_isSimpleCountingProcess
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    CountingProcess.IsSimpleCountingProcess
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t ω ↦ safeSourceCount hlam0 hlamHalf x0 p0 t ω) := by
  apply CountingProcess.IsSimpleCountingProcess.of_finiteEventCountTop
    (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i)
  · intro ω i
    exact sourceEventTime_eq_top_or_pos (n := n) hlam0 hlamHalf x0 p0 ω i
  · intro ω i j hif hjf heq
    exact sourceEventTime_injective hlam0 hlamHalf x0 p0 ω i j hif hjf heq
  · exact safeSourceCount_stronglyAdapted hlam0 hlamHalf x0 p0

theorem safeTargetCount_isSimpleCountingProcess
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    CountingProcess.IsSimpleCountingProcess
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t ω ↦ safeTargetCount hlam0 hlamHalf x0 p0 t ω) := by
  apply CountingProcess.IsSimpleCountingProcess.of_finiteEventCountTop
    (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j)
  · intro ω j
    exact targetEventTime_eq_top_or_pos (n := n) hlam0 hlamHalf x0 p0 ω j
  · intro ω i j hif hjf heq
    exact targetEventTime_injective hlam0 hlamHalf x0 p0 ω i j hif hjf heq
  · exact safeTargetCount_stronglyAdapted hlam0 hlamHalf x0 p0

/-! ## Cross-colour jump separation -/

theorem sourceEventTime_ne_targetEventTime
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (ω : FiniteSample n) (i j : Fin n) :
    sourceEventTime hlam0 hlamHalf x0 p0 i ω ≠ ⊤ →
    targetEventTime hlam0 hlamHalf x0 p0 j ω ≠ ⊤ →
    sourceEventTime hlam0 hlamHalf x0 p0 i ω ≠
      targetEventTime hlam0 hlamHalf x0 p0 j ω := by
  intro hif hjf heq
  by_cases hgood : ω.NoFeedbackTies lam x0 p0
  · have hSi : (ω.sourceEventSet lam x0 p0 i).Nonempty := by
      by_contra h
      apply hif
      simp [sourceEventTime, hgood, sourceEventTimeRaw, h]
    have hSj : (ω.targetEventSet lam x0 p0 j).Nonempty := by
      by_contra h
      apply hjf
      simp [targetEventTime, hgood, targetEventTimeRaw, h]
    let m := (ω.sourceEventSet lam x0 p0 i).min' hSi
    let r := (ω.targetEventSet lam x0 p0 j).min' hSj
    have hmi : i ∈ (feedbackState ω lam x0 p0 m.val).newSource ω lam :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hSi)).2
    have hmj : j ∈ (feedbackState ω lam x0 p0 r.val).newTarget ω lam :=
      (Finset.mem_filter.mp (Finset.min'_mem _ hSj)).2
    have htime : ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) =
        ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (r.val + 1) := by
      have heq' := heq
      simp only [sourceEventTime, targetEventTime, hgood, ↓reduceIte,
        sourceEventTimeRaw, targetEventTimeRaw, dite_eq_left hSi, dite_eq_left hSj] at heq'
      exact WithTop.coe_injective heq'
    by_cases hmr : m.val = r.val
    · have hmj' : j ∈ (feedbackState ω lam x0 p0 m.val).newTarget ω lam := by
        simpa [hmr] using hmj
      have hsource_pos :
          0 < ((feedbackState ω lam x0 p0 m.val).newSource ω lam).card :=
        Finset.card_pos.mpr ⟨i, hmi⟩
      have htarget_pos :
          0 < ((feedbackState ω lam x0 p0 m.val).newTarget ω lam).card :=
        Finset.card_pos.mpr ⟨j, hmj'⟩
      have hsum := hgood m.val (by omega)
      omega
    · rcases lt_or_gt_of_ne hmr with hlt | hgt
      · have hcand := candidates_nonempty_of_mem_newTarget
          (sample := ω) lam (feedbackState ω lam x0 p0 r.val) j hmj
        have hstrict := ω.feedbackState_x_strictMono_step
          hlam0 hlamHalf x0 p0 r.val hcand
        have hmono : ω.feedbackKnot lam x0 p0 (m.val + 1) ≤
            ω.feedbackKnot lam x0 p0 r.val :=
          ω.feedbackState_x_mono hlam0 hlamHalf x0 p0
            (Nat.succ_le_of_lt hlt)
        have hltKnot : ω.feedbackKnot lam x0 p0 (m.val + 1) <
            ω.feedbackKnot lam x0 p0 (r.val + 1) := by
          have hstrict' : ω.feedbackKnot lam x0 p0 r.val <
              ω.feedbackKnot lam x0 p0 (r.val + 1) := by
            simpa [feedbackKnot] using hstrict
          exact hmono.trans_lt hstrict'
        have hltTime : ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) <
            ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (r.val + 1) := by
          apply NNReal.coe_lt_coe.mp
          simpa only [coe_elapsedFeedbackKnot] using
            (sub_lt_sub_right hltKnot x0)
        exact False.elim ((ne_of_lt hltTime) htime)
      · have hcand := candidates_nonempty_of_mem_newSource
          (sample := ω) lam (feedbackState ω lam x0 p0 m.val) i hmi
        have hstrict := ω.feedbackState_x_strictMono_step
          hlam0 hlamHalf x0 p0 m.val hcand
        have hmono : ω.feedbackKnot lam x0 p0 (r.val + 1) ≤
            ω.feedbackKnot lam x0 p0 m.val :=
          ω.feedbackState_x_mono hlam0 hlamHalf x0 p0
            (Nat.succ_le_of_lt hgt)
        have hltKnot : ω.feedbackKnot lam x0 p0 (r.val + 1) <
            ω.feedbackKnot lam x0 p0 (m.val + 1) := by
          have hstrict' : ω.feedbackKnot lam x0 p0 m.val <
              ω.feedbackKnot lam x0 p0 (m.val + 1) := by
            simpa [feedbackKnot] using hstrict
          exact hmono.trans_lt hstrict'
        have hltTime : ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (r.val + 1) <
            ω.elapsedFeedbackKnot hlam0 hlamHalf x0 p0 (m.val + 1) := by
          apply NNReal.coe_lt_coe.mp
          simpa only [coe_elapsedFeedbackKnot] using
            (sub_lt_sub_right hltKnot x0)
        exact False.elim ((ne_of_lt hltTime) htime.symm)
  · have htop : sourceEventTime hlam0 hlamHalf x0 p0 i ω = ⊤ := by
      simp [sourceEventTime, hgood]
    exact False.elim (hif htop)

theorem safeCounts_noSimultaneousJumpsOn
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (T : ℝ≥0) :
    CountingProcess.NoSimultaneousJumpsOn
      (safeSourceCount (n := n) hlam0 hlamHalf x0 p0)
      (safeTargetCount (n := n) hlam0 hlamHalf x0 p0) T := by
  intro ω k l hk hl
  change CountingProcess.jumpTime
      (fun t ω' ↦ CountingProcess.finiteEventCountTop
        (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i) t ω') k ω ≠
      CountingProcess.jumpTime
        (fun t ω' ↦ CountingProcess.finiteEventCountTop
          (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j) t ω') l ω
  exact CountingProcess.finiteEventCountTop_cross_jumpTime_ne
    (fun i : Fin n ↦ sourceEventTime hlam0 hlamHalf x0 p0 i)
    (fun j : Fin n ↦ targetEventTime hlam0 hlamHalf x0 p0 j)
    (fun ω i j hif hjf ↦
      sourceEventTime_ne_targetEventTime hlam0 hlamHalf x0 p0 ω i j hif hjf)
    ω hk hl

theorem safeCurrentAt_eq_currentOfCounts
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) (ω : FiniteSample n) :
    safeCurrentAt hlam0 hlamHalf x0 p0 t ω =
      CountingProcess.currentOfCounts (safeK0 lam x0 p0)
        (safeSourceCount hlam0 hlamHalf x0 p0)
        (safeTargetCount hlam0 hlamHalf x0 p0) t ω := by
  simpa [CountingProcess.currentOfCounts] using
    (safeCurrentAt_eq_K0_add_counts hlam0 hlamHalf x0 p0 t ω)

/-! ## Safe initial state and predictable pre-jump transforms -/

theorem safeK0_stronglyMeasurable_usual_zero
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    StronglyMeasurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ (safeK0 lam x0 p0 ω : ℝ)) := by
  have hcurrentRaw := measurable_currentAtElapsed_raw
    (n := n) hlam0 hlamHalf x0 p0 0
  have hcurrent : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦
        (ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 0).current) :=
    fun s hs ↦
      (rawRevealedFiltration_le_usual (n := n) hlam0 hlamHalf x0 p0 0) _
        (hcurrentRaw hs)
  have hzero (ω : FiniteSample n) :
      ω.feedbackStateAtElapsed hlam0 hlamHalf x0 p0 0 =
        ω.initialFeedbackState x0 p0 := by
    simpa using
      (ω.feedbackStateAtElapsed_at_elapsedFeedbackKnot hlam0 hlamHalf x0 p0
        (show 0 ≤ 2 * n by omega))
  have hinitial : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ ω.initialFeedbackCurrent x0 p0) := by
    convert hcurrent using 1
    funext ω
    rw [hzero]
    rfl
  have hinitialReal : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦ (ω.initialFeedbackCurrent x0 p0 : ℝ)) :=
    (continuous_of_discreteTopology
      (f := fun k : ℤ ↦ (k : ℝ))).measurable.comp hinitial
  have hgood := measurableSet_feedbackGoodEvent_usual_zero
    (n := n) hlam0 hlamHalf x0 p0
  have hsafe : Measurable[
      usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0 0]
      (fun ω : FiniteSample n ↦
        if ω.NoFeedbackTies lam x0 p0 then
          (ω.initialFeedbackCurrent x0 p0 : ℝ) else 0) :=
    Measurable.ite hgood hinitialReal measurable_const
  simpa [safeK0] using hsafe.stronglyMeasurable

noncomputable def safePreCurrentAt
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) (t : ℝ≥0) : FiniteSample n → ℤ :=
  CountingProcess.leftCurrentOfCounts (safeK0 lam x0 p0)
    (safeSourceCount hlam0 hlamHalf x0 p0)
    (safeTargetCount hlam0 hlamHalf x0 p0) t

theorem safePreCurrentAt_cast_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t ω ↦ (safePreCurrentAt hlam0 hlamHalf x0 p0 t ω : ℝ)) := by
  exact CountingProcess.leftCurrentOfCounts_cast_predictable
    (safeSourceCount_isSimpleCountingProcess hlam0 hlamHalf x0 p0)
    (safeTargetCount_isSimpleCountingProcess hlam0 hlamHalf x0 p0)
    (safeK0_stronglyMeasurable_usual_zero hlam0 hlamHalf x0 p0)

theorem safeFeedbackSlope_predictable
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamHalf : lam < 1 / 2)
    (x0 p0 : ℝ) :
    IsStronglyPredictable
      (usualRevealedFiltration (n := n) hlam0 hlamHalf x0 p0)
      (fun t ω ↦ feedbackSlope lam
        (safePreCurrentAt hlam0 hlamHalf x0 p0 t ω : ℝ)) := by
  exact CountingProcess.leftCurrentOfCounts_comp_predictable
    (safeSourceCount_isSimpleCountingProcess hlam0 hlamHalf x0 p0)
    (safeTargetCount_isSimpleCountingProcess hlam0 hlamHalf x0 p0)
    (safeK0_stronglyMeasurable_usual_zero hlam0 hlamHalf x0 p0)
    (fun k : ℤ ↦ feedbackSlope lam (k : ℝ))

end FiniteSample

end OTSelector
