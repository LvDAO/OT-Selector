import OTSelector.Feedback.FeedbackRightIntensityRawRectangleBoundary

/-!
# Frozen-count observations on completed boundary snapshots

These identities connect actual snapshot completion to the independent unseen-coordinate
counts.  They preserve the two aggregate histories used in the raw rectangle proof.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal Topology

namespace OTSelector.RightTail

variable {n : ℕ}

theorem sum_unseenSourceGroup (S : Finset (FeedbackLabel n)) (f : FeedbackLabel n → ℝ) :
    (∑ label ∈ unseenSourceGroup S, f (label : FeedbackLabel n)) =
      ∑ i : Fin n, if (Sum.inl i : FeedbackLabel n) ∉ S then f (Sum.inl i) else 0 := by
  calc
    _ = ∑ label : feedbackUnseenFinset S,
        if (label : FeedbackLabel n).isLeft then f label else 0 := by
      rw [unseenSourceGroup, Finset.sum_filter]
    _ = ∑ label ∈ feedbackUnseenFinset S, if label.isLeft then f label else 0 :=
      Finset.sum_coe_sort (feedbackUnseenFinset S)
        (fun label : FeedbackLabel n ↦ if label.isLeft then f label else 0)
    _ = ∑ label : FeedbackLabel n,
        if label ∉ S then (if label.isLeft then f label else 0) else 0 := by
      have hset : feedbackUnseenFinset S =
          Finset.univ.filter (fun label : FeedbackLabel n ↦ label ∉ S) := by
        ext label
        simp [feedbackUnseenFinset]
      rw [hset, Finset.sum_filter]
    _ = _ := by rw [Fintype.sum_sum_type]; simp

theorem sum_unseenTargetGroup (S : Finset (FeedbackLabel n)) (f : FeedbackLabel n → ℝ) :
    (∑ label ∈ (unseenSourceGroup S)ᶜ, f (label : FeedbackLabel n)) =
      ∑ j : Fin n, if (Sum.inr j : FeedbackLabel n) ∉ S then f (Sum.inr j) else 0 := by
  have hgroup : (unseenSourceGroup S)ᶜ =
      Finset.univ.filter (fun label : feedbackUnseenFinset S ↦
        ¬ (label : FeedbackLabel n).isLeft) := by
    ext label
    simp [unseenSourceGroup]
  calc
    _ = ∑ label : feedbackUnseenFinset S,
        if ¬ (label : FeedbackLabel n).isLeft then f label else 0 := by
      rw [hgroup, Finset.sum_filter]
    _ = ∑ label ∈ feedbackUnseenFinset S, if ¬ label.isLeft then f label else 0 :=
      Finset.sum_coe_sort (feedbackUnseenFinset S)
        (fun label : FeedbackLabel n ↦ if ¬ label.isLeft then f label else 0)
    _ = ∑ label : FeedbackLabel n,
        if label ∉ S then (if ¬ label.isLeft then f label else 0) else 0 := by
      have hset : feedbackUnseenFinset S =
          Finset.univ.filter (fun label : FeedbackLabel n ↦ label ∉ S) := by
        ext label
        simp [feedbackUnseenFinset]
      rw [hset, Finset.sum_filter]
    _ = _ := by rw [Fintype.sum_sum_type]; simp

/-- The frozen phase of each unseen coordinate is its phase in the completed sample. -/
theorem fixedPhase_unseen_eq_mergePhase (q : ℝ) (S : Finset (FeedbackLabel n))
    (seen : S → MarkedHeight) (unseen : feedbackUnseenFinset S → MarkedHeight)
    (label : feedbackUnseenFinset S) :
    fixedPhase n q (unseenSourceGroup S) label (unseen label) =
      match (label : FeedbackLabel n) with
      | Sum.inl i => (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i q
      | Sum.inr j => (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j q := by
  have hpoint := congrFun (feedbackUnseenTuple_finiteSampleSeenUnseenMerge S seen unseen) label
  rcases label with ⟨label, hlabel⟩
  cases label with
  | inl i =>
      have hsource : (finiteSampleSeenUnseenMerge S seen unseen).sourcePoint i =
          unseen ⟨Sum.inl i, hlabel⟩ := by
        simpa [feedbackUnseenTuple, feedbackLabelTuple, feedbackLabelPoint] using hpoint
      simp only [fixedPhase, unseenSourceGroup, Finset.mem_filter, Finset.mem_univ,
        Sum.isLeft_inl, and_self]
      unfold sourcePhase FiniteSample.sourcePhase FiniteSample.sourceSlope
      rw [← hsource]
      simp [FiniteSample.sourcePoint, mul_comm]
  | inr j =>
      have htarget : (finiteSampleSeenUnseenMerge S seen unseen).targetPoint j =
          unseen ⟨Sum.inr j, hlabel⟩ := by
        simpa [feedbackUnseenTuple, feedbackLabelTuple, feedbackLabelPoint] using hpoint
      simp only [fixedPhase, unseenSourceGroup, Finset.mem_filter, Finset.mem_univ,
        Sum.isLeft_inr, Bool.false_eq_true, and_false]
      unfold targetPhase FiniteSample.targetPhase FiniteSample.targetSlope
      rw [← htarget]
      simp [FiniteSample.targetPoint, mul_comm]

theorem sourceRemaining_merge_eq_card_sub_count
    (lam xR y : ℝ) (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    FiniteSample.rightBoundaryFrozenSourceCount lam xR y
        (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) =
      ((unseenSourceGroup S).card : ℝ) -
        count (fixedPhase n (segmentCurve state.x state.p (state.slope lam) xR)
          (unseenSourceGroup S)) (unseenSourceGroup S) y unseen := by
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let phase : FeedbackLabel n → ℝ := fun label ↦ match label with
    | Sum.inl i => (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i q
    | Sum.inr j => (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j q
  have hsum := sum_unseenSourceGroup S (fun label ↦ if y < phase label then 1 else 0)
  have hphase : ∀ label : feedbackUnseenFinset S,
      fixedPhase n q (unseenSourceGroup S) label (unseen label) = phase label :=
    fixedPhase_unseen_eq_mergePhase q S seen unseen
  calc
    _ = ∑ label ∈ unseenSourceGroup S, if y < phase label then 1 else 0 := by
      rw [hsum]
      change (∑ i : Fin n, if i ∉ state.seenSource ∧
        y < (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i q then 1 else 0) = _
      apply Finset.sum_congr rfl
      intro i hi
      simp only [phase, hsource, ite_and]
    _ = ∑ label ∈ unseenSourceGroup S,
        ((1 : ℝ) - if fixedPhase n q (unseenSourceGroup S) label (unseen label) ≤ y
          then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro label hlabel
      rw [hphase]
      by_cases h : phase label ≤ y <;> simp [h, not_lt.mpr, lt_of_not_ge]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, count, q]

theorem targetRemaining_merge_eq_card_sub_count
    (lam xR y : ℝ) (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (htarget : ∀ j : Fin n, (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    (unseen : feedbackUnseenFinset S → MarkedHeight) :
    FiniteSample.rightBoundaryFrozenTargetCount lam xR y
        (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) =
      (((unseenSourceGroup S)ᶜ).card : ℝ) -
        count (fixedPhase n (segmentCurve state.x state.p (state.slope lam) xR)
          (unseenSourceGroup S)) (unseenSourceGroup S)ᶜ y unseen := by
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let phase : FeedbackLabel n → ℝ := fun label ↦ match label with
    | Sum.inl i => (finiteSampleSeenUnseenMerge S seen unseen).sourcePhase i q
    | Sum.inr j => (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j q
  have hsum := sum_unseenTargetGroup S (fun label ↦ if y < phase label then 1 else 0)
  have hphase : ∀ label : feedbackUnseenFinset S,
      fixedPhase n q (unseenSourceGroup S) label (unseen label) = phase label :=
    fixedPhase_unseen_eq_mergePhase q S seen unseen
  calc
    _ = ∑ label ∈ (unseenSourceGroup S)ᶜ, if y < phase label then 1 else 0 := by
      rw [hsum]
      change (∑ j : Fin n, if j ∉ state.seenTarget ∧
        y < (finiteSampleSeenUnseenMerge S seen unseen).targetPhase j q then 1 else 0) = _
      apply Finset.sum_congr rfl
      intro j hj
      simp only [phase, htarget, ite_and]
    _ = ∑ label ∈ (unseenSourceGroup S)ᶜ,
        ((1 : ℝ) - if fixedPhase n q (unseenSourceGroup S) label (unseen label) ≤ y
          then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro label hlabel
      rw [hphase]
      by_cases h : phase label ≤ y <;> simp [h, not_lt.mpr, lt_of_not_ge]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, count, q]

/-- Replacing strict-left counts by attained counts changes only finitely many path times. -/
theorem integral_remainingBefore_eq_remainingAt {A ι : Type*} [Fintype ι]
    (X : ι → A → ℝ) (J : Finset ι) (a : ℝ → ℝ) (s t : ℝ) (ω : ι → A) :
    (∫ u in Ioc s t, ((J.card : ℝ) - countBefore X J u ω) / a u) =
      ∫ u in Ioc s t, ((J.card : ℝ) - count X J u ω) / a u := by
  have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ Set.range (fun i : ι ↦ X i (ω i)) :=
    measure_eq_zero_iff_ae_notMem.mp ((Set.finite_range _).measure_zero volume)
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hae] with u hu
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hne : X i (ω i) ≠ u := fun h ↦ hu ⟨i, h⟩
  have hiff : X i (ω i) < u ↔ X i (ω i) ≤ u :=
    ⟨le_of_lt, fun h ↦ lt_of_le_of_ne h hne⟩
  exact if_congr hiff rfl rfl

/-- Frozen remaining-count history, with its boundary kept as an explicit observable input. -/
noncomputable def frozenRemainingHistory (lam xR s : ℝ)
    (boundary : FiniteSample.RevealedSnapshot n) (completed : FiniteSample n) :
    Iic s → ℝ × ℝ := fun u ↦
  (FiniteSample.rightBoundaryFrozenSourceCount lam xR u.1 boundary completed,
    FiniteSample.rightBoundaryFrozenTargetCount lam xR u.1 boundary completed)

theorem measurable_frozenRemainingHistory (lam xR s : ℝ) :
    Measurable fun p : FiniteSample.RevealedSnapshot n × FiniteSample n ↦
      frozenRemainingHistory lam xR s p.1 p.2 := by
  unfold frozenRemainingHistory
  rw [measurable_pi_iff]
  intro u
  have hmap : Measurable fun p : FiniteSample.RevealedSnapshot n × FiniteSample n ↦
      (u.1, p) := measurable_const.prodMk measurable_id
  apply Measurable.prodMk
  · have h := (FiniteSample.measurable_rightBoundaryFrozenSourceCount (n := n) lam xR).comp hmap
    convert h using 1
    rfl
  · have h := (FiniteSample.measurable_rightBoundaryFrozenTargetCount (n := n) lam xR).comp hmap
    convert h using 1
    rfl

/-- Every measurable frozen-future history cylinder has a raw-measurable unseen-coordinate
section.  The constant boundary information is retained as a parameter. -/
theorem measurableSet_frozenRemainingHistory_section
    (lam xR s : ℝ) (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n, (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    {C : Set (Iic s → ℝ × ℝ)} (hC : MeasurableSet C) :
    MeasurableSet[rawFiltration
      (fixedPhase n (segmentCurve state.x state.p (state.slope lam) xR) (unseenSourceGroup S))
      (measurable_fixedPhase n _ _) (unseenSourceGroup S) s]
      {unseen | frozenRemainingHistory lam xR s (sample.revealedSnapshotFromState state)
        (finiteSampleSeenUnseenMerge S seen unseen) ∈ C} := by
  let X := fixedPhase n (segmentCurve state.x state.p (state.slope lam) xR) (unseenSourceGroup S)
  let J := unseenSourceGroup S
  have hcount := Filtration.stronglyAdapted_natural
    (fun u ↦ ((measurable_count X (measurable_fixedPhase n _ _) J u).prodMk
      (measurable_count X (measurable_fixedPhase n _ _) Jᶜ u)).stronglyMeasurable)
  have hpath : @Measurable _ _ (rawFiltration X (measurable_fixedPhase n _ _) J s)
      (inferInstance : MeasurableSpace (Iic s → ℝ × ℝ))
      (fun unseen ↦ frozenRemainingHistory lam xR s (sample.revealedSnapshotFromState state)
        (finiteSampleSeenUnseenMerge S seen unseen)) := by
    let : MeasurableSpace (feedbackUnseenFinset S → MarkedHeight) :=
      rawFiltration X (measurable_fixedPhase n _ _) J s
    rw [measurable_pi_iff]
    intro u
    have hu := ((hcount u).mono ((rawFiltration X (measurable_fixedPhase n _ _) J).mono u.2)).measurable
    have hsourceCount : Measurable fun unseen ↦ (J.card : ℝ) - count X J u unseen :=
      measurable_const.sub (measurable_fst.comp hu)
    have htargetCount : Measurable fun unseen ↦ ((Jᶜ).card : ℝ) - count X Jᶜ u unseen :=
      measurable_const.sub (measurable_snd.comp hu)
    convert hsourceCount.prodMk htargetCount using 1
    funext unseen
    exact Prod.ext (sourceRemaining_merge_eq_card_sub_count lam xR u state S
      hsource sample seen unseen) (targetRemaining_merge_eq_card_sub_count lam xR u state S
      htarget sample seen unseen)
  exact hpath hC

/-- Source crossings in a physical interval, computed from the frozen remaining counts. -/
noncomputable def frozenSourceWindow (lam xR s t : ℝ)
    (boundary : FiniteSample.RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  FiniteSample.rightBoundaryFrozenSourceCount lam xR s boundary completed -
    FiniteSample.rightBoundaryFrozenSourceCount lam xR t boundary completed

/-- A globally bounded area-floor extension of the physical source hazard integral.  On the
unclipped strip above the floor, its denominator is exactly the physical remaining area. -/
noncomputable def frozenSourceHazardIntegral (areaFloor lam xR s t : ℝ)
    (boundary : FiniteSample.RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  ∫ u in Ioc s t,
    FiniteSample.rightBoundaryFrozenSourceCount lam xR u boundary completed /
      max areaFloor (sourceUnclippedRemainingMass n
        (FiniteSample.rightBoundaryFrozenHeight lam xR boundary) u)

theorem source_frozenHistory_normalized_rawRectangle
    (hn : 0 < n) (lam xR areaFloor : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n, (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    {s t : ℝ} (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t,
      (u, segmentCurve state.x state.p (state.slope lam) xR) ∈
        FiniteSample.rightTailUnclippedRegion n)
    (hfloor : areaFloor ≤ sourceUnclippedRemainingMass n
      (segmentCurve state.x state.p (state.slope lam) xR) t)
    {C : Set (Iic s → ℝ × ℝ)} (hC : MeasurableSet C) :
    normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
      (feedbackUnseenRectangularSetAt lam state xR S)
      (fun unseen ↦ if frozenRemainingHistory lam xR s (sample.revealedSnapshotFromState state)
          (finiteSampleSeenUnseenMerge S seen unseen) ∈ C
        then frozenSourceWindow lam xR s t (sample.revealedSnapshotFromState state)
          (finiteSampleSeenUnseenMerge S seen unseen) else 0) =
      normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
        (feedbackUnseenRectangularSetAt lam state xR S)
        (fun unseen ↦ if frozenRemainingHistory lam xR s (sample.revealedSnapshotFromState state)
            (finiteSampleSeenUnseenMerge S seen unseen) ∈ C
          then frozenSourceHazardIntegral areaFloor lam xR s t (sample.revealedSnapshotFromState state)
            (finiteSampleSeenUnseenMerge S seen unseen) else 0) := by
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let J := unseenSourceGroup S
  let X := fixedPhase n q J
  let E : Set (feedbackUnseenFinset S → MarkedHeight) :=
    {unseen | frozenRemainingHistory lam xR s (sample.revealedSnapshotFromState state)
      (finiteSampleSeenUnseenMerge S seen unseen) ∈ C}
  have hE := measurableSet_frozenRemainingHistory_section lam xR s state S
    hsource htarget sample seen hC
  have hbase := history_source_normalized_rawRectangle hn lam xR state S hRs hst hstrip hE
  have hwindow : ∀ unseen, frozenSourceWindow lam xR s t
      (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) =
        count X J t unseen - count X J s unseen := by
    intro unseen
    unfold frozenSourceWindow
    rw [sourceRemaining_merge_eq_card_sub_count lam xR s state S hsource sample seen unseen,
      sourceRemaining_merge_eq_card_sub_count lam xR t state S hsource sample seen unseen]
    change ((J.card : ℝ) - count X J s unseen) - (J.card - count X J t unseen) = _
    ring
  have hintegral : ∀ unseen, (∫ u in Ioc s t,
      ((J.card : ℝ) - countBefore X J u unseen) / sourceUnclippedRemainingMass n q u) =
        frozenSourceHazardIntegral areaFloor lam xR s t
          (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) := by
    intro unseen
    rw [integral_remainingBefore_eq_remainingAt]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have harea : areaFloor ≤ sourceUnclippedRemainingMass n q u := by
      unfold sourceUnclippedRemainingMass at hfloor ⊢
      dsimp [q]
      linarith [hu.2]
    have hq : FiniteSample.rightBoundaryFrozenHeight lam xR
        (sample.revealedSnapshotFromState state) = q := rfl
    dsimp only
    rw [sourceRemaining_merge_eq_card_sub_count lam xR u state S hsource sample seen unseen,
      hq, max_eq_right harea]
  have hleft : (fun unseen ↦ if frozenRemainingHistory lam xR s
      (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) ∈ C
      then frozenSourceWindow lam xR s t (sample.revealedSnapshotFromState state)
        (finiteSampleSeenUnseenMerge S seen unseen) else 0) =
        E.indicator (fun unseen ↦ count X J t unseen - count X J s unseen) := by
    funext unseen
    rw [hwindow]
    rfl
  have hright : E.indicator (fun unseen ↦ ∫ u in Ioc s t,
      ((J.card : ℝ) - countBefore X J u unseen) / sourceUnclippedRemainingMass n q u) =
      (fun unseen ↦ if frozenRemainingHistory lam xR s
        (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) ∈ C
        then frozenSourceHazardIntegral areaFloor lam xR s t
          (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) else 0) := by
    funext unseen
    change (if unseen ∈ E then _ else 0) = _
    dsimp only
    rw [hintegral]
    rfl
  rw [hleft]
  exact hbase.trans (congrArg
    (normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
      (feedbackUnseenRectangularSetAt lam state xR S)) hright)

/-- Target crossings in a physical interval, computed from the frozen remaining counts. -/
noncomputable def frozenTargetWindow (lam xR s t : ℝ)
    (boundary : FiniteSample.RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  FiniteSample.rightBoundaryFrozenTargetCount lam xR s boundary completed -
    FiniteSample.rightBoundaryFrozenTargetCount lam xR t boundary completed

/-- A globally bounded area-floor extension of the physical target hazard integral.  On the
unclipped strip above the floor, its denominator is exactly the physical remaining area. -/
noncomputable def frozenTargetHazardIntegral (areaFloor lam xR s t : ℝ)
    (boundary : FiniteSample.RevealedSnapshot n) (completed : FiniteSample n) : ℝ :=
  ∫ u in Ioc s t,
    FiniteSample.rightBoundaryFrozenTargetCount lam xR u boundary completed /
      max areaFloor (targetUnclippedRemainingMass n
        (FiniteSample.rightBoundaryFrozenHeight lam xR boundary) u)

theorem target_frozenHistory_normalized_rawRectangle
    (hn : 0 < n) (lam xR areaFloor : ℝ) (state : FeedbackStepState n)
    (S : Finset (FeedbackLabel n))
    (hsource : ∀ i : Fin n, (Sum.inl i : FeedbackLabel n) ∈ S ↔ i ∈ state.seenSource)
    (htarget : ∀ j : Fin n, (Sum.inr j : FeedbackLabel n) ∈ S ↔ j ∈ state.seenTarget)
    (sample : FiniteSample n) (seen : S → MarkedHeight)
    {s t : ℝ} (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t,
      (u, segmentCurve state.x state.p (state.slope lam) xR) ∈
        FiniteSample.rightTailUnclippedRegion n)
    (hfloor : areaFloor ≤ targetUnclippedRemainingMass n
      (segmentCurve state.x state.p (state.slope lam) xR) t)
    {C : Set (Iic s → ℝ × ℝ)} (hC : MeasurableSet C) :
    normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
      (feedbackUnseenRectangularSetAt lam state xR S)
      (fun unseen ↦ if frozenRemainingHistory lam xR s (sample.revealedSnapshotFromState state)
          (finiteSampleSeenUnseenMerge S seen unseen) ∈ C
        then frozenTargetWindow lam xR s t (sample.revealedSnapshotFromState state)
          (finiteSampleSeenUnseenMerge S seen unseen) else 0) =
      normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
        (feedbackUnseenRectangularSetAt lam state xR S)
        (fun unseen ↦ if frozenRemainingHistory lam xR s (sample.revealedSnapshotFromState state)
            (finiteSampleSeenUnseenMerge S seen unseen) ∈ C
          then frozenTargetHazardIntegral areaFloor lam xR s t (sample.revealedSnapshotFromState state)
            (finiteSampleSeenUnseenMerge S seen unseen) else 0) := by
  let q := segmentCurve state.x state.p (state.slope lam) xR
  let J := unseenSourceGroup S
  let X := fixedPhase n q J
  let E : Set (feedbackUnseenFinset S → MarkedHeight) :=
    {unseen | frozenRemainingHistory lam xR s (sample.revealedSnapshotFromState state)
      (finiteSampleSeenUnseenMerge S seen unseen) ∈ C}
  have hE := measurableSet_frozenRemainingHistory_section lam xR s state S
    hsource htarget sample seen hC
  have hbase := history_target_normalized_rawRectangle hn lam xR state S hRs hst hstrip hE
  have hwindow : ∀ unseen, frozenTargetWindow lam xR s t
      (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) =
        count X Jᶜ t unseen - count X Jᶜ s unseen := by
    intro unseen
    unfold frozenTargetWindow
    rw [targetRemaining_merge_eq_card_sub_count lam xR s state S htarget sample seen unseen,
      targetRemaining_merge_eq_card_sub_count lam xR t state S htarget sample seen unseen]
    change (((Jᶜ).card : ℝ) - count X Jᶜ s unseen) - ((Jᶜ).card - count X Jᶜ t unseen) = _
    ring
  have hintegral : ∀ unseen, (∫ u in Ioc s t,
      (((Jᶜ).card : ℝ) - countBefore X Jᶜ u unseen) / targetUnclippedRemainingMass n q u) =
        frozenTargetHazardIntegral areaFloor lam xR s t
          (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) := by
    intro unseen
    rw [integral_remainingBefore_eq_remainingAt]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have harea : areaFloor ≤ targetUnclippedRemainingMass n q u := by
      unfold targetUnclippedRemainingMass at hfloor ⊢
      dsimp [q]
      linarith [hu.2]
    have hq : FiniteSample.rightBoundaryFrozenHeight lam xR
        (sample.revealedSnapshotFromState state) = q := rfl
    dsimp only
    rw [targetRemaining_merge_eq_card_sub_count lam xR u state S htarget sample seen unseen,
      hq, max_eq_right harea]
  have hleft : (fun unseen ↦ if frozenRemainingHistory lam xR s
      (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) ∈ C
      then frozenTargetWindow lam xR s t (sample.revealedSnapshotFromState state)
        (finiteSampleSeenUnseenMerge S seen unseen) else 0) =
        E.indicator (fun unseen ↦ count X Jᶜ t unseen - count X Jᶜ s unseen) := by
    funext unseen
    rw [hwindow]
    rfl
  have hright : E.indicator (fun unseen ↦ ∫ u in Ioc s t,
      (((Jᶜ).card : ℝ) - countBefore X Jᶜ u unseen) / targetUnclippedRemainingMass n q u) =
      (fun unseen ↦ if frozenRemainingHistory lam xR s
        (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) ∈ C
        then frozenTargetHazardIntegral areaFloor lam xR s t
          (sample.revealedSnapshotFromState state) (finiteSampleSeenUnseenMerge S seen unseen) else 0) := by
    funext unseen
    change (if unseen ∈ E then _ else 0) = _
    dsimp only
    rw [hintegral]
    rfl
  rw [hleft]
  exact hbase.trans (congrArg
    (normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
      (feedbackUnseenRectangularSetAt lam state xR S)) hright)

end OTSelector.RightTail
