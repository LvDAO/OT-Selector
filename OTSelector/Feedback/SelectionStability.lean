import OTSelector.Feedback.ForcedHistory

/-!
# Deterministic stability of a strict next-coordinate selection

The hypotheses below are purely finite and deterministic: one unseen label is strictly below every
other candidate.  Consequently it is the unique label exposed by the ordinary feedback step.
-/

namespace OTSelector

namespace FeedbackStepState

variable {n : ℕ}

private theorem nextCoordinate_eq_sourceCoordinate_of_strict_min
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n)
    (hi : i ∉ state.seenSource)
    (hsource : ∀ k, k ∉ state.seenSource → k ≠ i →
      state.sourceCoordinate sample lam i < state.sourceCoordinate sample lam k)
    (htarget : ∀ j, j ∉ state.seenTarget →
      state.sourceCoordinate sample lam i < state.targetCoordinate sample lam j) :
    state.nextCoordinate sample lam = state.sourceCoordinate sample lam i := by
  classical
  have hiDiff : i ∈ Finset.univ \ state.seenSource := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
  have hiSource : state.sourceCoordinate sample lam i ∈
      state.sourceCandidates sample lam := by
    exact Finset.mem_image.mpr ⟨i, hiDiff, rfl⟩
  have hiCandidate : state.sourceCoordinate sample lam i ∈
      state.candidates sample lam := by
    exact Finset.mem_union_left _ hiSource
  have hcandidates : (state.candidates sample lam).Nonempty :=
    ⟨state.sourceCoordinate sample lam i, hiCandidate⟩
  have hle : ∀ z ∈ state.candidates sample lam,
      state.sourceCoordinate sample lam i ≤ z := by
    intro z hz
    rw [candidates, Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp hz
      by_cases hki : k = i
      · subst k
        exact le_of_eq hkz
      · have hlt := hsource k (Finset.mem_sdiff.mp hk).2 hki
        exact hlt.le.trans_eq hkz
    · obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp hz
      have hlt := htarget j (Finset.mem_sdiff.mp hj).2
      exact hlt.le.trans_eq hjz
  apply le_antisymm
  · rw [nextCoordinate, dite_eq_left hcandidates]
    exact Finset.min'_le _ _ hiCandidate
  · rw [nextCoordinate, dite_eq_left hcandidates]
    exact hle _ (Finset.min'_mem _ hcandidates)

private theorem nextCoordinate_eq_targetCoordinate_of_strict_min
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n)
    (hj : j ∉ state.seenTarget)
    (hsource : ∀ k, k ∉ state.seenSource →
      state.targetCoordinate sample lam j < state.sourceCoordinate sample lam k)
    (htarget : ∀ l, l ∉ state.seenTarget → l ≠ j →
      state.targetCoordinate sample lam j < state.targetCoordinate sample lam l) :
    state.nextCoordinate sample lam = state.targetCoordinate sample lam j := by
  classical
  have hjDiff : j ∈ Finset.univ \ state.seenTarget := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
  have hjTarget : state.targetCoordinate sample lam j ∈
      state.targetCandidates sample lam := by
    exact Finset.mem_image.mpr ⟨j, hjDiff, rfl⟩
  have hjCandidate : state.targetCoordinate sample lam j ∈
      state.candidates sample lam := by
    exact Finset.mem_union_right _ hjTarget
  have hcandidates : (state.candidates sample lam).Nonempty :=
    ⟨state.targetCoordinate sample lam j, hjCandidate⟩
  have hle : ∀ z ∈ state.candidates sample lam,
      state.targetCoordinate sample lam j ≤ z := by
    intro z hz
    rw [candidates, Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨k, hk, hkz⟩ := Finset.mem_image.mp hz
      have hlt := hsource k (Finset.mem_sdiff.mp hk).2
      exact hlt.le.trans_eq hkz
    · obtain ⟨l, hl, hlz⟩ := Finset.mem_image.mp hz
      by_cases hlj : l = j
      · subst l
        exact le_of_eq hlz
      · have hlt := htarget l (Finset.mem_sdiff.mp hl).2 hlj
        exact hlt.le.trans_eq hlz
  apply le_antisymm
  · rw [nextCoordinate, dite_eq_left hcandidates]
    exact Finset.min'_le _ _ hjCandidate
  · rw [nextCoordinate, dite_eq_left hcandidates]
    exact hle _ (Finset.min'_mem _ hcandidates)

private theorem nextCoordinate_le_sourceCoordinate
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (k : Fin n)
    (hk : k ∉ state.seenSource) :
    state.nextCoordinate sample lam ≤ state.sourceCoordinate sample lam k := by
  classical
  have hkDiff : k ∈ Finset.univ \ state.seenSource := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩
  have hkSource : state.sourceCoordinate sample lam k ∈
      state.sourceCandidates sample lam := by
    exact Finset.mem_image.mpr ⟨k, hkDiff, rfl⟩
  have hkCandidate : state.sourceCoordinate sample lam k ∈
      state.candidates sample lam := by
    exact Finset.mem_union_left _ hkSource
  have hcandidates : (state.candidates sample lam).Nonempty :=
    ⟨state.sourceCoordinate sample lam k, hkCandidate⟩
  rw [nextCoordinate, dite_eq_left hcandidates]
  exact Finset.min'_le _ _ hkCandidate

private theorem nextCoordinate_le_targetCoordinate
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n)
    (hj : j ∉ state.seenTarget) :
    state.nextCoordinate sample lam ≤ state.targetCoordinate sample lam j := by
  classical
  have hjDiff : j ∈ Finset.univ \ state.seenTarget := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩
  have hjTarget : state.targetCoordinate sample lam j ∈
      state.targetCandidates sample lam := by
    exact Finset.mem_image.mpr ⟨j, hjDiff, rfl⟩
  have hjCandidate : state.targetCoordinate sample lam j ∈
      state.candidates sample lam := by
    exact Finset.mem_union_right _ hjTarget
  have hcandidates : (state.candidates sample lam).Nonempty :=
    ⟨state.targetCoordinate sample lam j, hjCandidate⟩
  rw [nextCoordinate, dite_eq_left hcandidates]
  exact Finset.min'_le _ _ hjCandidate

/-- A source coordinate that is strictly below every other unseen candidate is selected alone. -/
theorem labelStepRealizes_of_source_unique_min
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n)
    (hi : i ∉ state.seenSource)
    (hsource : ∀ k, k ∉ state.seenSource → k ≠ i →
      state.sourceCoordinate sample lam i < state.sourceCoordinate sample lam k)
    (htarget : ∀ j, j ∉ state.seenTarget →
      state.sourceCoordinate sample lam i < state.targetCoordinate sample lam j) :
    FiniteSample.labelStepRealizes sample lam state (Sum.inl i) := by
  classical
  have hnext := nextCoordinate_eq_sourceCoordinate_of_strict_min sample lam state i hi
    hsource htarget
  have hsource_eq : state.newSource sample lam = {i} := by
    ext k
    constructor
    · intro hk
      have hkFilter := Finset.mem_filter.mp hk
      have hkSeen : k ∉ state.seenSource := Finset.mem_sdiff.mp hkFilter.1 |>.2
      have hkEq := hkFilter.2
      by_cases hki : k = i
      · exact Finset.mem_singleton.mpr hki
      · have hlt := hsource k hkSeen hki
        have heq : state.sourceCoordinate sample lam k =
            state.sourceCoordinate sample lam i := hkEq.trans hnext
        exact False.elim ((ne_of_lt hlt) (heq.symm))
    · intro hk
      have hki : k = i := Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩, hnext.symm⟩
  have htarget_eq : state.newTarget sample lam = ∅ := by
    ext j
    constructor
    · intro hj
      have hjFilter := Finset.mem_filter.mp hj
      have hjSeen : j ∉ state.seenTarget := Finset.mem_sdiff.mp hjFilter.1 |>.2
      have hjEq := hjFilter.2
      have hlt := htarget j hjSeen
      have heq : state.sourceCoordinate sample lam i =
          state.targetCoordinate sample lam j := hnext.symm.trans hjEq.symm
      exact False.elim ((ne_of_lt hlt) heq)
    · intro hj
      simp at hj
  exact ⟨hsource_eq, htarget_eq⟩

/-- A target coordinate that is strictly below every other unseen candidate is selected alone. -/
theorem labelStepRealizes_of_target_unique_min
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j : Fin n)
    (hj : j ∉ state.seenTarget)
    (hsource : ∀ k, k ∉ state.seenSource →
      state.targetCoordinate sample lam j < state.sourceCoordinate sample lam k)
    (htarget : ∀ l, l ∉ state.seenTarget → l ≠ j →
      state.targetCoordinate sample lam j < state.targetCoordinate sample lam l) :
    FiniteSample.labelStepRealizes sample lam state (Sum.inr j) := by
  classical
  have hnext := nextCoordinate_eq_targetCoordinate_of_strict_min sample lam state j hj
    hsource htarget
  have hsource_eq : state.newSource sample lam = ∅ := by
    ext k
    constructor
    · intro hk
      have hkFilter := Finset.mem_filter.mp hk
      have hkSeen : k ∉ state.seenSource := Finset.mem_sdiff.mp hkFilter.1 |>.2
      have hkEq := hkFilter.2
      have hlt := hsource k hkSeen
      have heq : state.targetCoordinate sample lam j =
          state.sourceCoordinate sample lam k := hnext.symm.trans hkEq.symm
      exact False.elim ((ne_of_lt hlt) heq)
    · intro hk
      simp at hk
  have htarget_eq : state.newTarget sample lam = {j} := by
    ext l
    constructor
    · intro hl
      have hlFilter := Finset.mem_filter.mp hl
      have hlSeen : l ∉ state.seenTarget := Finset.mem_sdiff.mp hlFilter.1 |>.2
      have hlEq := hlFilter.2
      by_cases hlj : l = j
      · exact Finset.mem_singleton.mpr hlj
      · have hlt := htarget l hlSeen hlj
        have heq : state.targetCoordinate sample lam l =
            state.targetCoordinate sample lam j := hlEq.trans hnext
        exact False.elim ((ne_of_lt hlt) heq.symm)
    · intro hl
      have hlj : l = j := Finset.mem_singleton.mp hl
      subst l
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩, hnext.symm⟩
  exact ⟨hsource_eq, htarget_eq⟩

/-- A realized source singleton is strictly below every other unseen source coordinate. -/
theorem labelStepRealizes_source_lt_source_of_ne
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i k : Fin n)
    (hreal : FiniteSample.labelStepRealizes sample lam state (Sum.inl i))
    (hk : k ∉ state.seenSource) (hki : k ≠ i) :
    state.sourceCoordinate sample lam i < state.sourceCoordinate sample lam k := by
  classical
  have hiNew : i ∈ state.newSource sample lam := by
    rw [hreal.1]
    simp
  have hiFilter := Finset.mem_filter.mp hiNew
  have hselected : state.sourceCoordinate sample lam i =
      state.nextCoordinate sample lam := hiFilter.2
  have hle := nextCoordinate_le_sourceCoordinate sample lam state k hk
  have hle' : state.sourceCoordinate sample lam i ≤
      state.sourceCoordinate sample lam k := by
    calc
      state.sourceCoordinate sample lam i = state.nextCoordinate sample lam := hselected
      _ ≤ state.sourceCoordinate sample lam k := hle
  have hne : state.sourceCoordinate sample lam i ≠
      state.sourceCoordinate sample lam k := by
    intro heq
    have hkNew : k ∈ state.newSource sample lam := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩, ?_⟩
      calc
        state.sourceCoordinate sample lam k = state.sourceCoordinate sample lam i := heq.symm
        _ = state.nextCoordinate sample lam := hselected
    have hkSingleton : k ∈ ({i} : Finset (Fin n)) := by
      rw [← hreal.1]
      exact hkNew
    exact hki (Finset.mem_singleton.mp hkSingleton)
  exact lt_of_le_of_ne hle' hne

/-- A realized source singleton is strictly below every unseen target coordinate. -/
theorem labelStepRealizes_source_lt_target
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (i : Fin n)
    (hreal : FiniteSample.labelStepRealizes sample lam state (Sum.inl i))
    (j : Fin n) (hj : j ∉ state.seenTarget) :
    state.sourceCoordinate sample lam i < state.targetCoordinate sample lam j := by
  classical
  have hiNew : i ∈ state.newSource sample lam := by
    rw [hreal.1]
    simp
  have hiFilter := Finset.mem_filter.mp hiNew
  have hselected : state.sourceCoordinate sample lam i =
      state.nextCoordinate sample lam := hiFilter.2
  have hle := nextCoordinate_le_targetCoordinate sample lam state j hj
  have hle' : state.sourceCoordinate sample lam i ≤
      state.targetCoordinate sample lam j := by
    calc
      state.sourceCoordinate sample lam i = state.nextCoordinate sample lam := hselected
      _ ≤ state.targetCoordinate sample lam j := hle
  have hne : state.sourceCoordinate sample lam i ≠
      state.targetCoordinate sample lam j := by
    intro heq
    have hjNew : j ∈ state.newTarget sample lam := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩, ?_⟩
      calc
        state.targetCoordinate sample lam j = state.sourceCoordinate sample lam i := heq.symm
        _ = state.nextCoordinate sample lam := hselected
    rw [hreal.2] at hjNew
    simp at hjNew
  exact lt_of_le_of_ne hle' hne

/-- A realized target singleton is strictly below every unseen source coordinate. -/
theorem labelStepRealizes_target_lt_source
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j k : Fin n)
    (hreal : FiniteSample.labelStepRealizes sample lam state (Sum.inr j))
    (hk : k ∉ state.seenSource) :
    state.targetCoordinate sample lam j < state.sourceCoordinate sample lam k := by
  classical
  have hjNew : j ∈ state.newTarget sample lam := by
    rw [hreal.2]
    simp
  have hjFilter := Finset.mem_filter.mp hjNew
  have hselected : state.targetCoordinate sample lam j =
      state.nextCoordinate sample lam := hjFilter.2
  have hle := nextCoordinate_le_sourceCoordinate sample lam state k hk
  have hle' : state.targetCoordinate sample lam j ≤
      state.sourceCoordinate sample lam k := by
    calc
      state.targetCoordinate sample lam j = state.nextCoordinate sample lam := hselected
      _ ≤ state.sourceCoordinate sample lam k := hle
  have hne : state.targetCoordinate sample lam j ≠
      state.sourceCoordinate sample lam k := by
    intro heq
    have hkNew : k ∈ state.newSource sample lam := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩, ?_⟩
      calc
        state.sourceCoordinate sample lam k = state.targetCoordinate sample lam j := heq.symm
        _ = state.nextCoordinate sample lam := hselected
    rw [hreal.1] at hkNew
    simp at hkNew
  exact lt_of_le_of_ne hle' hne

/-- A realized target singleton is strictly below every other unseen target coordinate. -/
theorem labelStepRealizes_target_lt_target_of_ne
    (sample : FiniteSample n) (lam : ℝ) (state : FeedbackStepState n) (j l : Fin n)
    (hreal : FiniteSample.labelStepRealizes sample lam state (Sum.inr j))
    (hl : l ∉ state.seenTarget) (hlj : l ≠ j) :
    state.targetCoordinate sample lam j < state.targetCoordinate sample lam l := by
  classical
  have hjNew : j ∈ state.newTarget sample lam := by
    rw [hreal.2]
    simp
  have hjFilter := Finset.mem_filter.mp hjNew
  have hselected : state.targetCoordinate sample lam j =
      state.nextCoordinate sample lam := hjFilter.2
  have hle := nextCoordinate_le_targetCoordinate sample lam state l hl
  have hle' : state.targetCoordinate sample lam j ≤
      state.targetCoordinate sample lam l := by
    calc
      state.targetCoordinate sample lam j = state.nextCoordinate sample lam := hselected
      _ ≤ state.targetCoordinate sample lam l := hle
  have hne : state.targetCoordinate sample lam j ≠
      state.targetCoordinate sample lam l := by
    intro heq
    have hlNew : l ∈ state.newTarget sample lam := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hl⟩, ?_⟩
      calc
        state.targetCoordinate sample lam l = state.targetCoordinate sample lam j := heq.symm
        _ = state.nextCoordinate sample lam := hselected
    have hlSingleton : l ∈ ({j} : Finset (Fin n)) := by
      rw [← hreal.2]
      exact hlNew
    exact hlj (Finset.mem_singleton.mp hlSingleton)
  exact lt_of_le_of_ne hle' hne

end FeedbackStepState

end OTSelector
