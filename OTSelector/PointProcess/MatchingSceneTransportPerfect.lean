import OTSelector.PointProcess.MatchingSceneTransport
import OTSelector.PointProcess.MatchingSceneProbability

/-!
# Compact partner events for limits of actual matching laws

A source atom in an open observation window cannot lose all partners from a fixed compact
partner window in a vague limit. The resulting closed event is suited to the quantitative
root-averaged escape bounds of the original finite assignments.
-/

open MeasureTheory Set Function Filter Topology
open scoped BigOperators Classical ENNReal

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

namespace OTSelector.PointProcess.MatchingScene

noncomputable local instance transportPerfectPointTopology : TopologicalSpace (LocalConfiguration matchingPointBase) :=
  LocalConfiguration.vagueTopology matchingPointBase
noncomputable local instance transportPerfectEdgeTopology : TopologicalSpace
    (LocalConfiguration (matchingPointBase, matchingPointBase)) :=
  LocalConfiguration.vagueTopology (matchingPointBase, matchingPointBase)

/-- Actual source atoms inside the open observation interval retain a partner in `K`. -/
def HasSourcePartnersIn (U K : Set MatchingPoint) (scene : MatchingScene) : Prop :=
  ∀ x ∈ U, LocalConfiguration.multiplicity scene.source x ≠ 0 →
    ∃ y ∈ K, LocalConfiguration.multiplicity scene.edges (x, y) ≠ 0

private theorem exists_pos_lt_finset {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ δ > 0, ∀ i ∈ s, δ < r i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih
    refine ⟨min δ (r i / 2), lt_min hδ (half_pos (hr i)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans_lt (by linarith [hr j])
    · exact (min_le_left _ _).trans_lt (hbound j hj)

private theorem isClosed_hasPartnersIn
    (vertices : MatchingScene → LocalConfiguration matchingPointBase) (hv : Continuous vertices)
    (edge : MatchingPoint → MatchingPoint → MatchingPoint × MatchingPoint)
    (hdist : ∀ x y x' y', dist (edge x y) (edge x' y') = max (dist x x') (dist y y'))
    {U K : Set MatchingPoint} (hU : IsOpen U) (hK : IsCompact K) :
    IsClosed {scene | ∀ x ∈ U, LocalConfiguration.multiplicity (vertices scene) x ≠ 0 →
      ∃ y ∈ K, LocalConfiguration.multiplicity scene.edges (edge x y) ≠ 0} := by
  apply isClosed_iff_forall_filter.mpr
  intro limit l hl hset hlim
  let : NeBot l := hl
  have hsc : Tendsto vertices l (𝓝 (vertices limit)) :=
    (hv.tendsto limit).mono_left hlim
  have hed : Tendsto (fun scene : MatchingScene ↦ scene.edges) l (𝓝 limit.edges) :=
    (continuous_edges.tendsto limit).mono_left hlim
  have hev : ∀ᶠ scene in l, ∀ x ∈ U, LocalConfiguration.multiplicity (vertices scene) x ≠ 0 →
      ∃ y ∈ K, LocalConfiguration.multiplicity scene.edges (edge x y) ≠ 0 :=
    Filter.le_principal_iff.mp hset
  intro x hx hxatom
  by_contra hn
  have hzero (y : K) : LocalConfiguration.multiplicity limit.edges (edge x y.val) = 0 := by
    by_contra h
    exact hn ⟨y.val, y.property, h⟩
  choose r hr hlocal using (fun y : K ↦
    LocalConfiguration.eventually_no_atom_near_of_tendsto hed (hzero y))
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun y : K ↦ Metric.ball y.val (r y))
    (fun _ ↦ Metric.isOpen_ball) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (hr ⟨y, hy⟩)⟩)
  obtain ⟨δ, hδ, hδr⟩ := exists_pos_lt_finset s r hr
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hnear := LocalConfiguration.eventually_exists_atom_near_of_tendsto hsc hxatom
    (lt_min hδ hε)
  have hnone : ∀ᶠ scene in l, ∀ y ∈ s, ∀ e,
      dist e (edge x y.val) < r y → LocalConfiguration.multiplicity scene.edges e = 0 :=
    (eventually_all_finset s).mpr (fun y _ ↦ hlocal y)
  have hfalse : ∀ᶠ scene in l, False := by
    filter_upwards [hev, hnear, hnone] with scene hscene hpoint hempty
    obtain ⟨x', hx'near, hx'atom⟩ := hpoint
    have hx'U : x' ∈ U := hεU ((lt_min_iff.mp hx'near).2)
    obtain ⟨y', hy'K, hy'edge⟩ := hscene x' hx'U hx'atom
    obtain ⟨y, hy, hy'near⟩ := mem_iUnion₂.mp (hs hy'K)
    apply hy'edge
    apply hempty y hy (edge x' y')
    rw [hdist]
    exact max_lt ((lt_min_iff.mp hx'near).1.trans (hδr y hy)) hy'near
  exact hfalse.exists.elim (fun _ h ↦ h)

/-- Compactness of the partner window makes the actual no-loss condition closed for the genuine
vague topology. This proof works with arbitrary convergent filters, without metrizability. -/
theorem isClosed_hasSourcePartnersIn {U K : Set MatchingPoint}
    (hU : IsOpen U) (hK : IsCompact K) : IsClosed {scene | HasSourcePartnersIn U K scene} :=
  isClosed_hasPartnersIn source continuous_source Prod.mk (fun _ _ _ _ ↦ Prod.dist_eq) hU hK

/-- Actual target atoms inside the open observation interval retain a source partner in `K`. -/
def HasTargetPartnersIn (U K : Set MatchingPoint) (scene : MatchingScene) : Prop :=
  ∀ y ∈ U, LocalConfiguration.multiplicity scene.target y ≠ 0 →
    ∃ x ∈ K, LocalConfiguration.multiplicity scene.edges (x, y) ≠ 0

theorem isClosed_hasTargetPartnersIn {U K : Set MatchingPoint}
    (hU : IsOpen U) (hK : IsCompact K) : IsClosed {scene | HasTargetPartnersIn U K scene} :=
  isClosed_hasPartnersIn target continuous_target (fun y x ↦ (x, y))
    (fun _ _ _ _ ↦ by rw [Prod.dist_eq, max_comm]) hU hK

/-- Open spatial source window and closed bounded target window, with all original marks. -/
def HasBoundedSourcePartners (A B : ℝ) (scene : MatchingScene) : Prop :=
  HasSourcePartnersIn {x | |x.1| < A} {y | |y.1| ≤ B} scene

theorem isClosed_hasBoundedSourcePartners (A B : ℝ) :
    IsClosed {scene | HasBoundedSourcePartners A B scene} :=
  isClosed_hasSourcePartnersIn (isOpen_lt continuous_fst.abs continuous_const)
    (isCompact_partnerWindow B)

/-- The corresponding actual target partner event. -/
def HasBoundedTargetPartners (A B : ℝ) (scene : MatchingScene) : Prop :=
  HasTargetPartnersIn {y | |y.1| < A} {x | |x.1| ≤ B} scene

theorem isClosed_hasBoundedTargetPartners (A B : ℝ) :
    IsClosed {scene | HasBoundedTargetPartners A B scene} :=
  isClosed_hasTargetPartnersIn (isOpen_lt continuous_fst.abs continuous_const)
    (isCompact_partnerWindow B)

end OTSelector.PointProcess.MatchingScene

namespace OTSelector.FiniteSample

open PointProcess
variable {n : ℕ} {lam : ℝ}

/-- If the actual source partner condition fails, at least one original assigned edge is long. -/
theorem one_le_sourceRootLongEdgeCount_of_not_hasBoundedSourcePartners
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    (A R z : ℝ)
    (hbad : ¬ MatchingScene.HasBoundedSourcePartners A (A + R)
      (sample.rootedMatchingScene graph σ z)) :
    1 ≤ FiniteMatching.sourceRootLongEdgeCount
      (sample.sourceIntersection graph) (sample.targetIntersection graph) σ A R z := by
  change ¬ (∀ x, |x.1| < A →
    LocalConfiguration.multiplicity (LocalConfiguration.ofTuple matchingPointBase
      (sample.rootedSourcePoint graph z)) x ≠ 0 →
    ∃ y, |y.1| ≤ A + R ∧ LocalConfiguration.multiplicity
      (sample.rootedMatchingScene graph σ z).edges (x, y) ≠ 0) at hbad
  push Not at hbad
  obtain ⟨x, hx, hxatom, hnone⟩ := hbad
  obtain ⟨i, rfl⟩ := (LocalConfiguration.multiplicity_ofTuple_ne_zero_iff _ _).mp hxatom
  have hedge : LocalConfiguration.multiplicity (sample.rootedMatchingScene graph σ z).edges
      (sample.rootedSourcePoint graph z i, sample.rootedTargetPoint graph z (σ i)) ≠ 0 := by
    exact (LocalConfiguration.multiplicity_ofTuple_ne_zero_iff _ _).mpr ⟨i, rfl⟩
  have ht : A + R < |(sample.rootedTargetPoint graph z (σ i)).1| := by
    by_contra h
    exact hedge (hnone _ (le_of_not_gt h))
  have hd : R < |sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i| := by
    have htri := abs_add_le (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i)
      (sample.sourceIntersection graph i - z)
    rw [sub_add_sub_cancel] at htri
    change |sample.sourceIntersection graph i - z| < A at hx
    change A + R < |sample.targetIntersection graph (σ i) - z| at ht
    linarith
  change 1 ≤ (Finset.univ.filter fun i ↦
    |sample.sourceIntersection graph i - z| ≤ A ∧
    R < |sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i|).card
  apply Nat.one_le_iff_ne_zero.mpr
  apply Finset.card_ne_zero.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.le, hd⟩⟩

/-- A fixed finite sample loses a bounded source partner on at most its actual quadratic-energy
root budget. This is an unconditional spatial-root estimate for that concrete sample. -/
theorem measure_not_hasBoundedSourcePartners_le
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    {a b A R : ℝ} (hab : a < b) (hA : 0 ≤ A) (hR : 0 < R) :
    sample.rootedMatchingSceneLaw graph σ a b
      {scene | ¬ MatchingScene.HasBoundedSourcePartners A (A + R) scene} ≤
      ENNReal.ofReal ((2 * A / R ^ 2 / (b - a)) *
        ∑ i, (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2) := by
  let f : ℝ → ℝ := fun z ↦ (FiniteMatching.sourceRootLongEdgeCount
    (sample.sourceIntersection graph) (sample.targetIntersection graph) σ A R z : ℝ)
  have hi : Integrable f := FiniteMatching.integrable_rootWindowTailCount _ _ _ _
  have hir : Integrable f (Probability.spatialRootLaw a b) := by
    simp only [Probability.spatialRootLaw, ProbabilityTheory.cond, Real.volume_Ioc]
    exact hi.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr
      ((ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'))
  have hs : MeasurableSet {scene | ¬ MatchingScene.HasBoundedSourcePartners A (A + R) scene} :=
    (MatchingScene.isClosed_hasBoundedSourcePartners A (A + R)).measurableSet.compl
  rw [rootedMatchingSceneLaw, Measure.map_apply (sample.measurable_rootedMatchingScene graph σ) hs]
  apply le_trans (meas_le_lintegral₀ hir.aestronglyMeasurable.aemeasurable.ennreal_ofReal ?_)
  · rw [← ofReal_integral_eq_lintegral_ofReal hir (ae_of_all _ fun z ↦ Nat.cast_nonneg _),
      Probability.integral_spatialRootLaw hab.le, intervalIntegral.integral_of_le hab.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (b - a)⁻¹ * ((2 * A / R ^ 2) *
          ∑ i, (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (FiniteMatching.setIntegral_sourceRootLongEdgeCount_le _ _ σ _ hA hR)
          (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
      _ = _ := by ring
  · intro z hz
    have h := sample.one_le_sourceRootLongEdgeCount_of_not_hasBoundedSourcePartners graph σ A R z hz
    dsimp only [f]
    rw [ENNReal.ofReal_natCast]
    exact_mod_cast h

/-- The target-side failure uses the actual inverse-assigned source partner. -/
theorem one_le_targetRootLongEdgeCount_of_not_hasBoundedTargetPartners
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    (A R z : ℝ)
    (hbad : ¬ MatchingScene.HasBoundedTargetPartners A (A + R)
      (sample.rootedMatchingScene graph σ z)) :
    1 ≤ FiniteMatching.targetRootLongEdgeCount
      (sample.sourceIntersection graph) (sample.targetIntersection graph) σ A R z := by
  change ¬ (∀ y, |y.1| < A →
    LocalConfiguration.multiplicity (LocalConfiguration.ofTuple matchingPointBase
      (sample.rootedTargetPoint graph z)) y ≠ 0 →
    ∃ x, |x.1| ≤ A + R ∧ LocalConfiguration.multiplicity
      (sample.rootedMatchingScene graph σ z).edges (x, y) ≠ 0) at hbad
  push Not at hbad
  obtain ⟨y, hy, hyatom, hnone⟩ := hbad
  obtain ⟨i, rfl⟩ := (LocalConfiguration.multiplicity_ofTuple_ne_zero_iff _ _).mp hyatom
  have hedge : LocalConfiguration.multiplicity (sample.rootedMatchingScene graph σ z).edges
      (sample.rootedSourcePoint graph z (σ.symm i), sample.rootedTargetPoint graph z i) ≠ 0 := by
    apply (LocalConfiguration.multiplicity_ofTuple_ne_zero_iff _ _).mpr
    exact ⟨σ.symm i, by simp⟩
  have hs : A + R < |(sample.rootedSourcePoint graph z (σ.symm i)).1| := by
    by_contra h
    exact hedge (hnone _ (le_of_not_gt h))
  have hd : R < |sample.targetIntersection graph i - sample.sourceIntersection graph (σ.symm i)| := by
    have htri := abs_add_le (sample.sourceIntersection graph (σ.symm i) - sample.targetIntersection graph i)
      (sample.targetIntersection graph i - z)
    rw [sub_add_sub_cancel, abs_sub_comm (sample.sourceIntersection graph (σ.symm i))
      (sample.targetIntersection graph i)] at htri
    change |sample.targetIntersection graph i - z| < A at hy
    change A + R < |sample.sourceIntersection graph (σ.symm i) - z| at hs
    linarith
  change 1 ≤ (Finset.univ.filter fun i ↦
    |sample.targetIntersection graph i - z| ≤ A ∧
    R < |sample.targetIntersection graph i - sample.sourceIntersection graph (σ.symm i)|).card
  apply Nat.one_le_iff_ne_zero.mpr
  apply Finset.card_ne_zero.mpr
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.le, hd⟩⟩

/-- Target partner escape has the same actual forward-indexed quadratic-energy budget. -/
theorem measure_not_hasBoundedTargetPartners_le
    (sample : FiniteSample n) (graph : FeedbackGraph lam) (σ : Assignment n)
    {a b A R : ℝ} (hab : a < b) (hA : 0 ≤ A) (hR : 0 < R) :
    sample.rootedMatchingSceneLaw graph σ a b
      {scene | ¬ MatchingScene.HasBoundedTargetPartners A (A + R) scene} ≤
      ENNReal.ofReal ((2 * A / R ^ 2 / (b - a)) *
        ∑ i, (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2) := by
  let f : ℝ → ℝ := fun z ↦ (FiniteMatching.targetRootLongEdgeCount
    (sample.sourceIntersection graph) (sample.targetIntersection graph) σ A R z : ℝ)
  have hi : Integrable f := FiniteMatching.integrable_rootWindowTailCount _ _ _ _
  have hir : Integrable f (Probability.spatialRootLaw a b) := by
    simp only [Probability.spatialRootLaw, ProbabilityTheory.cond, Real.volume_Ioc]
    exact hi.integrableOn.smul_measure (ENNReal.inv_ne_top.mpr
      ((ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'))
  have hs : MeasurableSet {scene | ¬ MatchingScene.HasBoundedTargetPartners A (A + R) scene} :=
    (MatchingScene.isClosed_hasBoundedTargetPartners A (A + R)).measurableSet.compl
  rw [rootedMatchingSceneLaw, Measure.map_apply (sample.measurable_rootedMatchingScene graph σ) hs]
  apply le_trans (meas_le_lintegral₀ hir.aestronglyMeasurable.aemeasurable.ennreal_ofReal ?_)
  · rw [← ofReal_integral_eq_lintegral_ofReal hir (ae_of_all _ fun z ↦ Nat.cast_nonneg _),
      Probability.integral_spatialRootLaw hab.le, intervalIntegral.integral_of_le hab.le]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (b - a)⁻¹ * ((2 * A / R ^ 2) *
          ∑ i, (sample.targetIntersection graph (σ i) - sample.sourceIntersection graph i) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (FiniteMatching.setIntegral_targetRootLongEdgeCount_le _ _ σ _ hA hR)
          (inv_nonneg.mpr (sub_nonneg.mpr hab.le))
      _ = _ := by ring
  · intro z hz
    have h := sample.one_le_targetRootLongEdgeCount_of_not_hasBoundedTargetPartners graph σ A R z hz
    dsimp only [f]
    rw [ENNReal.ofReal_natCast]
    exact_mod_cast h

end OTSelector.FiniteSample

namespace OTSelector.PointProcess.MatchingScene

/-- Quantitative complement form of closed Portmanteau for tight actual scene laws. -/
theorem measure_compl_closed_le_of_tendsto_of_tight
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene)))
    {F : Set MatchingScene} (hF : IsClosed F) {E : ℝ≥0∞}
    (hE : ∀ᶠ k in atTop, (μ k : Measure MatchingScene) Fᶜ ≤ E) :
    (ν : Measure MatchingScene) Fᶜ ≤ E := by
  have hlo : ∀ᶠ k in atTop, 1 - E ≤ (μ k : Measure MatchingScene) F := by
    filter_upwards [hE] with k hk
    rw [measure_compl hF.measurableSet (measure_ne_top _ _), measure_univ] at hk
    exact tsub_le_iff_left.mpr (tsub_le_iff_right.mp hk)
  have hlim := limsup_measure_closed_le_of_tendsto_of_tight μ hμ htight hF
  have h : 1 - E ≤ (ν : Measure MatchingScene) F :=
    (Filter.le_limsup_of_frequently_le hlo.frequently).trans hlim
  rw [measure_compl hF.measurableSet (measure_ne_top _ _), measure_univ]
  exact tsub_le_iff_right.mpr (tsub_le_iff_left.mp h)

/-- Closed endpoint test domination is preserved almost surely by actual finite scene laws. -/
theorem ae_hasEndpointTestDomination_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene))) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), HasEndpointTestDomination scene := by
  rw [ae_iff]
  apply le_antisymm _ zero_le
  apply measure_compl_closed_le_of_tendsto_of_tight hμ htight isClosed_hasEndpointTestDomination
  apply Eventually.of_forall
  intro k
  rw [hlaw k, FiniteSample.rootedMatchingSceneLaw, Measure.map_apply
    ((sample k).measurable_rootedMatchingScene (graph k) (assignment k))
    isClosed_hasEndpointTestDomination.measurableSet.compl]
  have hempty : (sample k).rootedMatchingScene (graph k) (assignment k) ⁻¹'
      {scene | HasEndpointTestDomination scene}ᶜ = ∅ := by
    ext z
    simp only [mem_preimage, mem_compl_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_not_intro (hasEndpointTestDomination_rootedMatchingScene (sample k) (graph k) (assignment k) z)
  rw [hempty, measure_empty]

/-- The finite-sample partner escape bound passes to a genuine weak limit law. -/
theorem measure_not_hasBoundedSourcePartners_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene))) {C : ℝ}
    (henergy : ∀ᶠ k in atTop, (∑ i,
      ((sample k).targetIntersection (graph k) (assignment k i) -
        (sample k).sourceIntersection (graph k) i) ^ 2) ≤ C * (b k - a k))
    {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R) :
    (ν : Measure MatchingScene) {scene | ¬ HasBoundedSourcePartners A (A + R) scene} ≤
      ENNReal.ofReal (2 * A * C / R ^ 2) := by
  apply measure_compl_closed_le_of_tendsto_of_tight hμ htight
    (isClosed_hasBoundedSourcePartners A (A + R))
  filter_upwards [henergy] with k hk
  rw [hlaw k]
  apply ((sample k).measure_not_hasBoundedSourcePartners_le
    (graph k) (assignment k) (hab k) hA hR).trans
  apply ENNReal.ofReal_le_ofReal
  have hlen : 0 < b k - a k := sub_pos.mpr (hab k)
  calc
    _ ≤ (2 * A / R ^ 2 / (b k - a k)) * (C * (b k - a k)) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by field_simp [ne_of_gt hlen]

/-- The same quantitative retention holds at target vertices. -/
theorem measure_not_hasBoundedTargetPartners_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene))) {C : ℝ}
    (henergy : ∀ᶠ k in atTop, (∑ i,
      ((sample k).targetIntersection (graph k) (assignment k i) -
        (sample k).sourceIntersection (graph k) i) ^ 2) ≤ C * (b k - a k))
    {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R) :
    (ν : Measure MatchingScene) {scene | ¬ HasBoundedTargetPartners A (A + R) scene} ≤
      ENNReal.ofReal (2 * A * C / R ^ 2) := by
  apply measure_compl_closed_le_of_tendsto_of_tight hμ htight
    (isClosed_hasBoundedTargetPartners A (A + R))
  filter_upwards [henergy] with k hk
  rw [hlaw k]
  apply ((sample k).measure_not_hasBoundedTargetPartners_le
    (graph k) (assignment k) (hab k) hA hR).trans
  apply ENNReal.ofReal_le_ofReal
  have hlen : 0 < b k - a k := sub_pos.mpr (hab k)
  calc
    _ ≤ (2 * A / R ^ 2 / (b k - a k)) * (C * (b k - a k)) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by field_simp [ne_of_gt hlen]

private theorem ae_exists_nat_of_quadratic_compl_bound (P : Measure MatchingScene)
    (p : ℕ → MatchingScene → Prop) (M : ℝ)
    (hbound : ∀ n : ℕ, P {scene | ¬ p n scene} ≤ ENNReal.ofReal (M / ((n : ℝ) + 1) ^ 2)) :
    ∀ᵐ scene ∂P, ∃ n : ℕ, p n scene := by
  rw [ae_iff]
  apply le_antisymm _ zero_le
  have hden : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) ^ 2) atTop atTop := by
    have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hnat
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (M / ((n : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ ↦ M / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hr
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  apply Eventually.of_forall
  intro n
  apply (measure_mono ?_).trans (hbound n)
  intro scene hscene
  exact fun h ↦ hscene ⟨n, h⟩

/-- Endpoint domination and simple endpoint configurations identify a genuine partial matching. -/
theorem isSimplePartialMatching_of_hasEndpointTestDomination {scene : MatchingScene}
    (hdom : HasEndpointTestDomination scene)
    (hsource : ∀ x, LocalConfiguration.multiplicity scene.source x ≤ 1)
    (htarget : ∀ x, LocalConfiguration.multiplicity scene.target x ≤ 1) :
    IsSimplePartialMatching scene := by
  have hp₁ (e f : MatchingPoint × MatchingPoint) : dist e.1 f.1 ≤ dist e f := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hp₂ (e f : MatchingPoint × MatchingPoint) : dist e.2 f.2 ≤ dist e f := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have hms := LocalConfiguration.multiplicity_le_of_projectedTestDomination hp₁ hdom.1
  have hmt := LocalConfiguration.multiplicity_le_of_projectedTestDomination hp₂ hdom.2
  refine ⟨fun e ↦ (hms e).trans (hsource e.1), ?_,
    LocalConfiguration.injOn_of_projectedTestDomination hp₁ hdom.1 hsource,
    LocalConfiguration.injOn_of_projectedTestDomination hp₂ hdom.2 htarget⟩
  intro e he
  constructor
  · exact fun hz ↦ he (Nat.eq_zero_of_le_zero (hz ▸ hms e))
  · exact fun hz ↦ he (Nat.eq_zero_of_le_zero (hz ▸ hmt e))

/-- A tight weak limit of the actual finite rooted laws is almost surely a simple perfect
matching when its endpoint configurations are simple and the concrete samples have uniformly
bounded energy per root-interval length. Partner retention is proved from the actual finite
quadratic-energy tail, rather than assumed as a limiting property. -/
theorem ae_isSimplePerfectMatching_of_rootedMatchingSceneLaw_tendsto
    {N : ℕ → ℕ} {lam : ℝ} (sample : ∀ k, FiniteSample (N k))
    (graph : ℕ → FeedbackGraph lam) (assignment : ∀ k, Assignment (N k))
    (a b : ℕ → ℝ) (hab : ∀ k, a k < b k)
    {μ : ℕ → ProbabilityMeasure MatchingScene} {ν : ProbabilityMeasure MatchingScene}
    (hlaw : ∀ k, (μ k : Measure MatchingScene) =
      (sample k).rootedMatchingSceneLaw (graph k) (assignment k) (a k) (b k))
    (hμ : Tendsto μ atTop (𝓝 ν))
    (htight : IsTightMeasureSet (range fun n ↦ (μ n : Measure MatchingScene))) {C : ℝ}
    (henergy : ∀ᶠ k in atTop, (∑ i,
      ((sample k).targetIntersection (graph k) (assignment k i) -
        (sample k).sourceIntersection (graph k) i) ^ 2) ≤ C * (b k - a k))
    (hsimple : ∀ᵐ scene ∂(ν : Measure MatchingScene),
      (∀ x, LocalConfiguration.multiplicity scene.source x ≤ 1) ∧
      (∀ x, LocalConfiguration.multiplicity scene.target x ≤ 1)) :
    ∀ᵐ scene ∂(ν : Measure MatchingScene), IsSimplePerfectMatching scene := by
  have hs (A : ℕ) : ∀ᵐ scene ∂(ν : Measure MatchingScene), ∃ r : ℕ,
      HasBoundedSourcePartners A ((A : ℝ) + ((r : ℝ) + 1)) scene := by
    apply ae_exists_nat_of_quadratic_compl_bound _ _ (2 * A * C)
    intro r
    exact measure_not_hasBoundedSourcePartners_of_rootedMatchingSceneLaw_tendsto
      sample graph assignment a b hab hlaw hμ htight henergy (Nat.cast_nonneg A)
      (by positivity : (0 : ℝ) < (r : ℝ) + 1)
  have ht (A : ℕ) : ∀ᵐ scene ∂(ν : Measure MatchingScene), ∃ r : ℕ,
      HasBoundedTargetPartners A ((A : ℝ) + ((r : ℝ) + 1)) scene := by
    apply ae_exists_nat_of_quadratic_compl_bound _ _ (2 * A * C)
    intro r
    exact measure_not_hasBoundedTargetPartners_of_rootedMatchingSceneLaw_tendsto
      sample graph assignment a b hab hlaw hμ htight henergy (Nat.cast_nonneg A)
      (by positivity : (0 : ℝ) < (r : ℝ) + 1)
  filter_upwards [ae_all_iff.mpr hs, ae_all_iff.mpr ht, hsimple,
    ae_hasEndpointTestDomination_of_rootedMatchingSceneLaw_tendsto
      sample graph assignment a b hlaw hμ htight] with scene hsource htarget hsimple hdom
  refine ⟨isSimplePartialMatching_of_hasEndpointTestDomination hdom hsimple.1 hsimple.2, ?_, ?_⟩
  · intro x hx
    obtain ⟨A, hA⟩ := exists_nat_gt |x.1|
    obtain ⟨r, hr⟩ := hsource A
    obtain ⟨y, _, hy⟩ := hr x hA hx
    exact ⟨y, hy⟩
  · intro y hy
    obtain ⟨A, hA⟩ := exists_nat_gt |y.1|
    obtain ⟨r, hr⟩ := htarget A
    obtain ⟨x, _, hx⟩ := hr y hA hy
    exact ⟨x, hx⟩

end OTSelector.PointProcess.MatchingScene
