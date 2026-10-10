import OTSelector.Feedback.FeedbackRightIntensityRawRectangle

/-!
# Coordinate transport for frozen-tail compensation

The unseen labels in a revealed snapshot form a finite subtype.  The raw-rectangle theorem is
transported along a coordinate equivalence so that it can be applied to that actual tuple law.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal Topology

namespace OTSelector.RightTail

variable {A ι κ : Type*} [MeasurableSpace A] [Fintype ι] [Fintype κ]

theorem rawFiltration_congr [DecidableEq κ] {X Y : κ → A → ℝ}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (h : X = Y) (J : Finset κ) : rawFiltration X hX J = rawFiltration Y hY J := by
  subst Y
  rfl

omit [Fintype ι] [Fintype κ] in
theorem count_reindex (e : ι ≃ κ) (X : κ → A → ℝ) (J : Finset κ)
    (t : ℝ) (ω : ι → A) :
    count X J t (MeasurableEquiv.piCongrLeft (fun _ : κ ↦ A) e ω) =
      count (fun i ↦ X (e i)) (J.map e.symm.toEmbedding) t ω := by
  unfold count
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
  have hcoord := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ ↦ A) e ω (e.symm j)
  simpa only [Equiv.apply_symm_apply] using congrArg
    (fun z : A ↦ if X j z ≤ t then (1 : ℝ) else 0) hcoord

omit [Fintype ι] [Fintype κ] in
theorem countBefore_reindex (e : ι ≃ κ) (X : κ → A → ℝ) (J : Finset κ)
    (t : ℝ) (ω : ι → A) :
    countBefore X J t (MeasurableEquiv.piCongrLeft (fun _ : κ ↦ A) e ω) =
      countBefore (fun i ↦ X (e i)) (J.map e.symm.toEmbedding) t ω := by
  unfold countBefore
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
  have hcoord := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ ↦ A) e ω (e.symm j)
  simpa only [Equiv.apply_symm_apply] using congrArg
    (fun z : A ↦ if X j z < t then (1 : ℝ) else 0) hcoord

theorem map_compl_equiv [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (J : Finset κ) :
    Jᶜ.map e.symm.toEmbedding = (J.map e.symm.toEmbedding)ᶜ := by
  ext i
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, Finset.mem_compl]
  constructor
  · rintro ⟨j, hj, rfl⟩ ⟨k, hk, hkj⟩
    exact hj (e.symm.injective hkj ▸ hk)
  · intro hi
    refine ⟨e i, ?_, e.symm_apply_apply i⟩
    intro hmem
    exact hi ⟨e i, hmem, e.symm_apply_apply i⟩

theorem rawEvent_reindex [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (X : κ → A → ℝ)
    (hX : ∀ i, Measurable (X i)) (J : Finset κ) {s : ℝ}
    {E : Set (κ → A)} (hE : MeasurableSet[rawFiltration X hX J s] E) :
    MeasurableSet[rawFiltration (fun i ↦ X (e i)) (fun i ↦ hX (e i))
      (J.map e.symm.toEmbedding) s]
      ((MeasurableEquiv.piCongrLeft (fun _ : κ ↦ A) e) ⁻¹' E) := by
  rw [rawFiltration, Filtration.natural_eq_comap] at hE ⊢
  obtain ⟨D, hD, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hE
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨D, hD, ?_⟩
  ext ω
  simp only [Set.mem_preimage]
  apply iff_of_eq
  congr 1
  funext u
  exact Prod.ext (count_reindex e X J u.1 ω).symm
    (by simpa only [map_compl_equiv] using (count_reindex e X Jᶜ u.1 ω).symm)

theorem setIntegral_reindex (e : ι ≃ κ) (P : κ → Measure A)
    [∀ i, SigmaFinite (P i)] {E : Set (κ → A)} (hE : MeasurableSet E)
    (f : (κ → A) → ℝ) :
    (∫ ω in E, f ω ∂Measure.pi P) =
      ∫ ω in (MeasurableEquiv.piCongrLeft (fun _ : κ ↦ A) e) ⁻¹' E,
        f (MeasurableEquiv.piCongrLeft (fun _ : κ ↦ A) e ω)
          ∂Measure.pi (fun i ↦ P (e i)) := by
  have hpres := measurePreserving_piCongrLeft (α := fun _ : κ ↦ A) P e
  rw [← integral_indicator hE,
    ← integral_indicator ((MeasurableEquiv.piCongrLeft (fun _ : κ ↦ A) e).measurable hE),
    ← hpres.integral_comp' (E.indicator f)]
  rfl

/-- The independent-lifetime raw rectangle works directly on any finite label subtype. -/
theorem count_rawRectangle_fintype
    [DecidableEq κ]
    (P : κ → Measure A) [∀ i, IsProbabilityMeasure (P i)]
    (X : κ → A → ℝ) (hX : ∀ i, Measurable (X i))
    (J L : Finset κ) {K D s t : ℝ} (hst : s ≤ t)
    (hfloor : 0 < K - t) (hD : D ≠ 0)
    (hsurvival : ∀ i ∈ L, ∀ u ∈ Icc s t,
      (P i).real {x | u < X i x} = (K - u) / D)
    {E : Set (κ → A)} (hE : MeasurableSet[rawFiltration X hX J s] E) :
    (∫ ω in E, count X L t ω - count X L s ω ∂Measure.pi P) =
      ∫ ω in E, ∫ u in Ioc s t,
        ((L.card : ℝ) - countBefore X L u ω) / (K - u) ∂volume ∂Measure.pi P := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hEambient : MeasurableSet E := (rawFiltration X hX J).le s E hE
  conv_lhs => rw [setIntegral_reindex e P hEambient]
  conv_rhs => rw [setIntegral_reindex e P hEambient]
  simp_rw [count_reindex, countBefore_reindex]
  have hbase := count_rawRectangle_remainingBefore (fun i ↦ P (e i))
    (fun i ↦ X (e i)) (fun i ↦ hX (e i))
    (J.map e.symm.toEmbedding) (L.map e.symm.toEmbedding) hst hfloor hD
    (fun i hi ↦ by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      simpa only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply] using hsurvival j hj)
    (rawEvent_reindex e X hX J hE)
  simpa only [Finset.card_map] using hbase

omit [MeasurableSpace A] [Fintype ι] [Fintype κ] in
theorem mem_map_symm_equiv (e : ι ≃ κ) (J : Finset κ) (i : ι) :
    i ∈ J.map e.symm.toEmbedding ↔ e i ∈ J := by
  constructor
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simpa using hj
  · intro hi
    exact Finset.mem_map.mpr ⟨e i, hi, e.symm_apply_apply i⟩

omit [MeasurableSpace A] [Fintype ι] [Fintype κ] in
theorem fixedPhase_reindex (e : ι ≃ κ) (n : ℕ) (q : ℝ) (J : Finset κ) (i : ι) :
    fixedPhase n q J (e i) = fixedPhase n q (J.map e.symm.toEmbedding) i := by
  simp only [fixedPhase, mem_map_symm_equiv]

omit [MeasurableSpace A] [Fintype ι] [Fintype κ] in
theorem fixedLaw_reindex (e : ι ≃ κ) (n : ℕ) (q xR : ℝ) (J : Finset κ) (i : ι) :
    fixedLaw n q xR J (e i) = fixedLaw n q xR (J.map e.symm.toEmbedding) i := by
  simp only [fixedLaw, mem_map_symm_equiv]

omit [MeasurableSpace A] in
/-- The concrete fixed-boundary source formula on an arbitrary finite unseen-label subtype. -/
theorem fixedBoundary_source_rawRectangle_fintype
    [DecidableEq κ] {n : ℕ} (hn : 0 < n) {q xR s t : ℝ} (J : Finset κ)
    (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t, (u, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    {E : Set (κ → MarkedHeight)}
    (hE : MeasurableSet[rawFiltration (fixedPhase n q J)
      (measurable_fixedPhase n q J) J s] E) :
    (∫ ω in E, count (fixedPhase n q J) J t ω - count (fixedPhase n q J) J s ω
      ∂Measure.pi (fixedLaw n q xR J)) =
      ∫ ω in E, ∫ u in Ioc s t,
        ((J.card : ℝ) - countBefore (fixedPhase n q J) J u ω) /
          sourceUnclippedRemainingMass n q u ∂volume ∂Measure.pi (fixedLaw n q xR J) := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let : ∀ i, IsProbabilityMeasure (fixedLaw n q xR J i) :=
    fixedLaw_isProbabilityMeasure hn J (hstrip xR ⟨le_rfl, hRs.trans hst⟩)
  have hEambient : MeasurableSet E :=
    (rawFiltration (fixedPhase n q J) (measurable_fixedPhase n q J) J).le s E hE
  have hE' := rawEvent_reindex e (fixedPhase n q J) (measurable_fixedPhase n q J) J hE
  have hphase : (fun i ↦ fixedPhase n q J (e i)) =
      fixedPhase n q (J.map e.symm.toEmbedding) :=
    funext (fixedPhase_reindex e n q J)
  rw [rawFiltration_congr _ (measurable_fixedPhase n q (J.map e.symm.toEmbedding))
    hphase] at hE'
  conv_lhs => rw [setIntegral_reindex e (fixedLaw n q xR J) hEambient]
  conv_rhs => rw [setIntegral_reindex e (fixedLaw n q xR J) hEambient]
  simp_rw [count_reindex, countBefore_reindex, fixedPhase_reindex, fixedLaw_reindex]
  simpa only [Finset.card_map] using fixedBoundary_source_rawRectangle hn
    (J.map e.symm.toEmbedding) hRs hst hstrip hE'

omit [MeasurableSpace A] in
/-- The concrete target formula on the same unseen-label subtype and two-count history. -/
theorem fixedBoundary_target_rawRectangle_fintype
    [DecidableEq κ] {n : ℕ} (hn : 0 < n) {q xR s t : ℝ} (J : Finset κ)
    (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t, (u, q) ∈ FiniteSample.rightTailUnclippedRegion n)
    {E : Set (κ → MarkedHeight)}
    (hE : MeasurableSet[rawFiltration (fixedPhase n q J)
      (measurable_fixedPhase n q J) J s] E) :
    (∫ ω in E, count (fixedPhase n q J) Jᶜ t ω - count (fixedPhase n q J) Jᶜ s ω
      ∂Measure.pi (fixedLaw n q xR J)) =
      ∫ ω in E, ∫ u in Ioc s t,
        (((Jᶜ).card : ℝ) - countBefore (fixedPhase n q J) Jᶜ u ω) /
          targetUnclippedRemainingMass n q u ∂volume ∂Measure.pi (fixedLaw n q xR J) := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let : ∀ i, IsProbabilityMeasure (fixedLaw n q xR J i) :=
    fixedLaw_isProbabilityMeasure hn J (hstrip xR ⟨le_rfl, hRs.trans hst⟩)
  have hEambient : MeasurableSet E :=
    (rawFiltration (fixedPhase n q J) (measurable_fixedPhase n q J) J).le s E hE
  have hE' := rawEvent_reindex e (fixedPhase n q J) (measurable_fixedPhase n q J) J hE
  have hphase : (fun i ↦ fixedPhase n q J (e i)) =
      fixedPhase n q (J.map e.symm.toEmbedding) :=
    funext (fixedPhase_reindex e n q J)
  rw [rawFiltration_congr _ (measurable_fixedPhase n q (J.map e.symm.toEmbedding))
    hphase] at hE'
  conv_lhs => rw [setIntegral_reindex e (fixedLaw n q xR J) hEambient]
  conv_rhs => rw [setIntegral_reindex e (fixedLaw n q xR J) hEambient]
  simp_rw [count_reindex, countBefore_reindex, fixedPhase_reindex, fixedLaw_reindex,
    map_compl_equiv]
  have hcard : ((J.map e.symm.toEmbedding)ᶜ).card = Jᶜ.card := by
    rw [← map_compl_equiv, Finset.card_map]
  simpa only [hcard] using fixedBoundary_target_rawRectangle hn
    (J.map e.symm.toEmbedding) hRs hst hstrip hE'

/-- The source partition of the actual dependent unseen-label tuple. -/
noncomputable def unseenSourceGroup {n : ℕ} (S : Finset (FeedbackLabel n)) :
    Finset (feedbackUnseenFinset S) :=
  Finset.univ.filter fun label ↦ (label : FeedbackLabel n).isLeft

theorem historyFactorLaw_eq_fixedLaw {n : ℕ} (lam xR : ℝ)
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (label : feedbackUnseenFinset S) :
    FiniteSample.rightBoundaryHistoryFactorLaw lam xR state (label : FeedbackLabel n) =
      fixedLaw n (segmentCurve state.x state.p (state.slope lam) xR) xR
        (unseenSourceGroup S) label := by
  rcases label with ⟨label, hlabel⟩
  cases label <;>
    simp [FiniteSample.rightBoundaryHistoryFactorLaw, fixedLaw, unseenSourceGroup,
      feedbackLabelRemainingSetAt, sourceRawRemainingSetAt, targetRawRemainingSetAt]

/-- The normalized actual unseen rectangle has exactly the conditional product law used by
the frozen-tail compensator, with positivity supplied by the physical unclipped strip. -/
theorem conditioned_unseenTupleLaw_eq_fixedLaw {n : ℕ} (hn : 0 < n) (lam xR : ℝ)
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hR : (xR, segmentCurve state.x state.p (state.slope lam) xR) ∈
      FiniteSample.rightTailUnclippedRegion n) :
    (feedbackUnseenTupleLaw S)[|feedbackUnseenRectangularSetAt lam state xR S] =
      Measure.pi (fixedLaw n (segmentCurve state.x state.p (state.slope lam) xR) xR
        (unseenSourceGroup S)) := by
  have hpositive : ∀ label : feedbackUnseenFinset S,
      (unitSquareUniform : Measure MarkedHeight)
        (feedbackLabelRemainingSetAt lam state xR (label : FeedbackLabel n)) ≠ 0 := by
    intro label
    let : IsProbabilityMeasure
        ((unitSquareUniform : Measure MarkedHeight)[|
          feedbackLabelRemainingSetAt lam state xR (label : FeedbackLabel n)]) := by
      change IsProbabilityMeasure (FiniteSample.rightBoundaryHistoryFactorLaw lam xR state _)
      rw [historyFactorLaw_eq_fixedLaw]
      exact fixedLaw_isProbabilityMeasure hn (unseenSourceGroup S) hR label
    intro hzero
    exact (IsProbabilityMeasure.ne_zero _ ) (cond_eq_zero_of_meas_eq_zero hzero)
  rw [feedbackUnseenTupleLaw, feedbackUnseenRectangularSetAt,
    Probability.cond_univ_pi_eq_pi_cond unitSquareUniform _
      (fun label : feedbackUnseenFinset S ↦
        measurableSet_feedbackLabelRemainingSetAt lam state xR label) hpositive]
  congr 1
  funext label
  exact historyFactorLaw_eq_fixedLaw lam xR state S label

theorem normalized_unseen_eq_integral_fixedLaw {n : ℕ} (hn : 0 < n) (lam xR : ℝ)
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    (hR : (xR, segmentCurve state.x state.p (state.slope lam) xR) ∈
      FiniteSample.rightTailUnclippedRegion n)
    (f : (feedbackUnseenFinset S → MarkedHeight) → ℝ) :
    normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
      (feedbackUnseenRectangularSetAt lam state xR S) f =
      ∫ unseen, f unseen
        ∂Measure.pi (fixedLaw n (segmentCurve state.x state.p (state.slope lam) xR) xR
          (unseenSourceGroup S)) := by
  rw [← integral_cond_eq_normalizedRestrictionIntegral,
    conditioned_unseenTupleLaw_eq_fixedLaw hn lam xR state S hR]

/-- Source rectangle compensation on the actual dependent unseen tuple, in exactly the
normalized-section form consumed by the full-history boundary conditional-law theorem. -/
theorem history_source_normalized_rawRectangle {n : ℕ} (hn : 0 < n) (lam xR : ℝ)
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    {s t : ℝ} (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t,
      (u, segmentCurve state.x state.p (state.slope lam) xR) ∈
        FiniteSample.rightTailUnclippedRegion n)
    {E : Set (feedbackUnseenFinset S → MarkedHeight)}
    (hE : MeasurableSet[rawFiltration
      (fixedPhase n (segmentCurve state.x state.p (state.slope lam) xR) (unseenSourceGroup S))
      (measurable_fixedPhase n _ _) (unseenSourceGroup S) s] E) :
    let q := segmentCurve state.x state.p (state.slope lam) xR
    let J := unseenSourceGroup S
    normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
      (feedbackUnseenRectangularSetAt lam state xR S)
      (E.indicator (fun ω ↦ count (fixedPhase n q J) J t ω -
        count (fixedPhase n q J) J s ω)) =
      normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
        (feedbackUnseenRectangularSetAt lam state xR S)
        (E.indicator (fun ω ↦ ∫ u in Ioc s t,
          ((J.card : ℝ) - countBefore (fixedPhase n q J) J u ω) /
            sourceUnclippedRemainingMass n q u)) := by
  dsimp only
  have hR := hstrip xR ⟨le_rfl, hRs.trans hst⟩
  have hEambient : MeasurableSet E := (rawFiltration _ _ _).le s E hE
  rw [normalized_unseen_eq_integral_fixedLaw hn lam xR state S hR,
    normalized_unseen_eq_integral_fixedLaw hn lam xR state S hR,
    integral_indicator hEambient, integral_indicator hEambient]
  exact fixedBoundary_source_rawRectangle_fintype hn (unseenSourceGroup S) hRs hst hstrip hE

/-- Target analogue on the same actual dependent unseen tuple. -/
theorem history_target_normalized_rawRectangle {n : ℕ} (hn : 0 < n) (lam xR : ℝ)
    (state : FeedbackStepState n) (S : Finset (FeedbackLabel n))
    {s t : ℝ} (hRs : xR ≤ s) (hst : s ≤ t)
    (hstrip : ∀ u ∈ Icc xR t,
      (u, segmentCurve state.x state.p (state.slope lam) xR) ∈
        FiniteSample.rightTailUnclippedRegion n)
    {E : Set (feedbackUnseenFinset S → MarkedHeight)}
    (hE : MeasurableSet[rawFiltration
      (fixedPhase n (segmentCurve state.x state.p (state.slope lam) xR) (unseenSourceGroup S))
      (measurable_fixedPhase n _ _) (unseenSourceGroup S) s] E) :
    let q := segmentCurve state.x state.p (state.slope lam) xR
    let J := unseenSourceGroup S
    normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
      (feedbackUnseenRectangularSetAt lam state xR S)
      (E.indicator (fun ω ↦ count (fixedPhase n q J) Jᶜ t ω -
        count (fixedPhase n q J) Jᶜ s ω)) =
      normalizedRestrictionIntegral (feedbackUnseenTupleLaw S)
        (feedbackUnseenRectangularSetAt lam state xR S)
        (E.indicator (fun ω ↦ ∫ u in Ioc s t,
          (((Jᶜ).card : ℝ) - countBefore (fixedPhase n q J) Jᶜ u ω) /
            targetUnclippedRemainingMass n q u)) := by
  dsimp only
  have hR := hstrip xR ⟨le_rfl, hRs.trans hst⟩
  have hEambient : MeasurableSet E := (rawFiltration _ _ _).le s E hE
  rw [normalized_unseen_eq_integral_fixedLaw hn lam xR state S hR,
    normalized_unseen_eq_integral_fixedLaw hn lam xR state S hR,
    integral_indicator hEambient, integral_indicator hEambient]
  exact fixedBoundary_target_rawRectangle_fintype hn (unseenSourceGroup S) hRs hst hstrip hE

end OTSelector.RightTail
