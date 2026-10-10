import OTSelector.Probability.CountingProcess.GridStopping

/-!
# Finite-range stopping masks

This module records the predictable masks needed for a finite stopping grid.  The start mask is
`1_{σ < t}` and the stop mask is `1_{t ≤ τ}`, so their product represents the stochastic interval
`(σ, τ]`.  Finite range is used through the atom decomposition of the stopping coordinate.

The strict mask `1_{t < τ}` is deliberately not used here: a general continuous-time stopping
time need not be predictable, and finite range alone does not repair that endpoint issue.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Sets and masks -/

/-- The predictable set corresponding to the time interval after a stopping coordinate. -/
def afterStartSet (σ : Ω → WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  {z | σ z.2 < (z.1 : WithTop ℝ≥0)}

/-- One finite-range atom of `afterStartSet`; the top atom contributes nothing. -/
def afterStartAtom (σ : Ω → WithTop ℝ≥0) (s : WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  match s with
  | ⊤ => ∅
  | (s : ℝ≥0) => Set.Ioi s ×ˢ {ω | σ ω = (s : WithTop ℝ≥0)}

/-- The right-closed stop set used for the interval `(σ, τ]`. -/
def throughStopSet (τ : Ω → WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  {z | (z.1 : WithTop ℝ≥0) ≤ τ z.2}

/-- The stochastic interval `(σ, τ]` on the time-coordinate product. -/
def stochasticIntervalSet (σ τ : Ω → WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  afterStartSet σ ∩ throughStopSet τ

/-- Indicator of the after-start predictable set. -/
noncomputable def afterStartMask (σ : Ω → WithTop ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) then 1 else 0

/-- Indicator of the right-closed through-stop set. -/
noncomputable def throughStopMask (τ : Ω → WithTop ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then 1 else 0

/-- Indicator of the stochastic interval `(σ, τ]`. -/
noncomputable def stochasticIntervalMask (σ τ : Ω → WithTop ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then 1 else 0

/-! ## Finite-range atom decomposition and predictable sets -/

omit [MeasurableSpace Ω] in
theorem afterStartSet_eq_atoms {σ : Ω → WithTop ℝ≥0} :
    afterStartSet σ = ⋃ s ∈ Set.range σ, afterStartAtom σ s := by
  ext z
  constructor
  · intro hz
    change σ z.2 < (z.1 : WithTop ℝ≥0) at hz
    cases hsigma : σ z.2 with
    | top =>
      rw [hsigma] at hz
      exact False.elim ((WithTop.not_top_lt (z.1 : WithTop ℝ≥0)) hz)
    | coe s =>
      rw [hsigma] at hz
      have hst : s < z.1 := by exact_mod_cast hz
      have hs : (s : WithTop ℝ≥0) ∈ Set.range σ := ⟨z.2, hsigma⟩
      rw [Set.mem_iUnion]
      refine ⟨(s : WithTop ℝ≥0), ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨hs, ?_⟩
      change s < z.1 ∧ σ z.2 = (s : WithTop ℝ≥0)
      exact ⟨hst, hsigma⟩
  · rw [Set.mem_iUnion]
    rintro ⟨s, hs⟩
    rw [Set.mem_iUnion] at hs
    rcases hs with ⟨_, hz⟩
    cases s with
    | top =>
      change z ∈ (∅ : Set (ℝ≥0 × Ω)) at hz
      exact hz.elim
    | coe s =>
      change z ∈ Set.Ioi s ×ˢ {ω | σ ω = (s : WithTop ℝ≥0)} at hz
      change σ z.2 < (z.1 : WithTop ℝ≥0)
      rw [hz.2]
      exact_mod_cast hz.1

omit [MeasurableSpace Ω] in
theorem measurableSet_afterStartSet {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hσ_range : (Set.range σ).Finite) :
    MeasurableSet[ℱ.predictable] (afterStartSet σ) := by
  rw [afterStartSet_eq_atoms]
  exact MeasurableSet.biUnion hσ_range.countable fun s hs ↦ by
    cases s with
    | top => simp [afterStartAtom]
    | coe s =>
      exact measurableSet_predictable_Ioi_prod (𝓕 := ℱ) (i := s)
        (hσ.measurableSet_eq_le le_rfl)

omit [MeasurableSpace Ω] in
theorem throughStopSet_eq_compl_afterStartSet (τ : Ω → WithTop ℝ≥0) :
    throughStopSet τ = (afterStartSet τ)ᶜ := by
  ext z
  change ((z.1 : WithTop ℝ≥0) ≤ τ z.2) ↔ ¬τ z.2 < (z.1 : WithTop ℝ≥0)
  constructor
  · exact fun h ↦ not_lt_of_ge h
  · exact fun h ↦ le_of_not_gt h

omit [MeasurableSpace Ω] in
theorem measurableSet_throughStopSet {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (hτ_range : (Set.range τ).Finite) :
    MeasurableSet[ℱ.predictable] (throughStopSet τ) := by
  rw [throughStopSet_eq_compl_afterStartSet]
  exact (measurableSet_afterStartSet hτ hτ_range).compl

omit [MeasurableSpace Ω] in
theorem measurableSet_stochasticIntervalSet {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    MeasurableSet[ℱ.predictable] (stochasticIntervalSet σ τ) :=
  (measurableSet_afterStartSet hσ hσ_range).inter
    (measurableSet_throughStopSet hτ hτ_range)

/-! ## Strong predictability of the masks -/

omit [MeasurableSpace Ω] in
theorem afterStartMask_predictable {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hσ_range : (Set.range σ).Finite) :
    IsStronglyPredictable ℱ (afterStartMask σ) := by
  classical
  have hset := measurableSet_afterStartSet hσ hσ_range
  change StronglyMeasurable[ℱ.predictable] (Function.uncurry (afterStartMask σ))
  have hEq : Function.uncurry (afterStartMask σ) =
      (afterStartSet σ).indicator (fun _ ↦ (1 : ℝ)) := by
    funext z
    rcases z with ⟨t, ω⟩
    by_cases hz : σ ω < (t : WithTop ℝ≥0)
    · change (if σ ω < (t : WithTop ℝ≥0) then 1 else 0) =
        if (t, ω) ∈ afterStartSet σ then 1 else 0
      simp only [afterStartSet, Set.mem_ofPred_eq, hz, ite_true]
    · change (if σ ω < (t : WithTop ℝ≥0) then 1 else 0) =
        if (t, ω) ∈ afterStartSet σ then 1 else 0
      simp only [afterStartSet, Set.mem_ofPred_eq, hz, ite_false]
  rw [hEq]
  exact stronglyMeasurable_const.indicator hset

omit [MeasurableSpace Ω] in
theorem throughStopMask_predictable {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (hτ_range : (Set.range τ).Finite) :
    IsStronglyPredictable ℱ (throughStopMask τ) := by
  classical
  have hset := measurableSet_throughStopSet hτ hτ_range
  change StronglyMeasurable[ℱ.predictable] (Function.uncurry (throughStopMask τ))
  have hEq : Function.uncurry (throughStopMask τ) =
      (throughStopSet τ).indicator (fun _ ↦ (1 : ℝ)) := by
    funext z
    rcases z with ⟨t, ω⟩
    by_cases hz : (t : WithTop ℝ≥0) ≤ τ ω
    · change (if (t : WithTop ℝ≥0) ≤ τ ω then 1 else 0) =
        if (t, ω) ∈ throughStopSet τ then 1 else 0
      simp only [throughStopSet, Set.mem_ofPred_eq, hz, ite_true]
    · change (if (t : WithTop ℝ≥0) ≤ τ ω then 1 else 0) =
        if (t, ω) ∈ throughStopSet τ then 1 else 0
      simp only [throughStopSet, Set.mem_ofPred_eq, hz, ite_false]
  rw [hEq]
  exact stronglyMeasurable_const.indicator hset

omit [MeasurableSpace Ω] in
theorem stochasticIntervalMask_predictable {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    IsStronglyPredictable ℱ (stochasticIntervalMask σ τ) := by
  classical
  have hset := measurableSet_stochasticIntervalSet hσ hτ hσ_range hτ_range
  change StronglyMeasurable[ℱ.predictable] (Function.uncurry (stochasticIntervalMask σ τ))
  have hEq : Function.uncurry (stochasticIntervalMask σ τ) =
      (stochasticIntervalSet σ τ).indicator (fun _ ↦ (1 : ℝ)) := by
    funext z
    rcases z with ⟨t, ω⟩
    by_cases hz : σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω
    · change (if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then 1 else 0) =
        if (t, ω) ∈ stochasticIntervalSet σ τ then 1 else 0
      simp only [stochasticIntervalSet, Set.mem_inter_iff, afterStartSet, throughStopSet,
        Set.mem_ofPred_eq, hz]
    · change (if σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω then 1 else 0) =
        if (t, ω) ∈ stochasticIntervalSet σ τ then 1 else 0
      simp only [stochasticIntervalSet, Set.mem_inter_iff, afterStartSet, throughStopSet,
        Set.mem_ofPred_eq, hz, ite_false]
  rw [hEq]
  exact stronglyMeasurable_const.indicator hset

/-! ## Finite range and bounded-simple closure -/

theorem IsBoundedSimplePredictable.of_binary_mask
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : IsStronglyPredictable ℱ M)
    (hM01 : ∀ t ω, M t ω = 0 ∨ M t ω = 1) :
    IsBoundedSimplePredictable ℱ M := by
  refine ⟨hM, ?_, 1, by positivity, ?_⟩
  · refine (Set.finite_singleton (0 : ℝ)).insert 1 |>.subset ?_
    rintro y ⟨⟨t, ω⟩, rfl⟩
    rcases hM01 t ω with h0 | h1
    · simp [h0]
    · simp [h1]
  · intro t ω
    rcases hM01 t ω with h0 | h1
    · simp [h0]
    · simp [h1]

omit [MeasurableSpace Ω] in
theorem afterStartMask_boundedSimplePredictable {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hσ_range : (Set.range σ).Finite) :
    IsBoundedSimplePredictable ℱ (afterStartMask σ) := by
  apply IsBoundedSimplePredictable.of_binary_mask (afterStartMask_predictable hσ hσ_range)
  intro t ω
  by_cases h : σ ω < (t : WithTop ℝ≥0)
  · exact Or.inr (ite_eq_left h)
  · exact Or.inl (ite_eq_right h)

omit [MeasurableSpace Ω] in
theorem throughStopMask_boundedSimplePredictable {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (hτ_range : (Set.range τ).Finite) :
    IsBoundedSimplePredictable ℱ (throughStopMask τ) := by
  apply IsBoundedSimplePredictable.of_binary_mask (throughStopMask_predictable hτ hτ_range)
  intro t ω
  by_cases h : (t : WithTop ℝ≥0) ≤ τ ω
  · exact Or.inr (ite_eq_left h)
  · exact Or.inl (ite_eq_right h)

omit [MeasurableSpace Ω] in
theorem stochasticIntervalMask_boundedSimplePredictable {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    IsBoundedSimplePredictable ℱ (stochasticIntervalMask σ τ) := by
  apply IsBoundedSimplePredictable.of_binary_mask
    (stochasticIntervalMask_predictable hσ hτ hσ_range hτ_range)
  intro t ω
  by_cases h : σ ω < (t : WithTop ℝ≥0) ∧ (t : WithTop ℝ≥0) ≤ τ ω
  · exact Or.inr (ite_eq_left h)
  · exact Or.inl (ite_eq_right h)

omit [MeasurableSpace Ω] in
theorem IsBoundedSimplePredictable.mul_afterStartMask
    {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {σ : Ω → WithTop ℝ≥0} {H : ℝ≥0 → Ω → ℝ}
    (hσ : IsStoppingTime ℱ σ) (hσ_range : (Set.range σ).Finite)
    (hH : IsBoundedSimplePredictable ℱ H) :
    IsBoundedSimplePredictable ℱ (fun t ω ↦ afterStartMask σ t ω * H t ω) :=
  (afterStartMask_boundedSimplePredictable hσ hσ_range).mul_process hH

omit [MeasurableSpace Ω] in
theorem IsBoundedSimplePredictable.mul_throughStopMask
    {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {τ : Ω → WithTop ℝ≥0} {H : ℝ≥0 → Ω → ℝ}
    (hτ : IsStoppingTime ℱ τ) (hτ_range : (Set.range τ).Finite)
    (hH : IsBoundedSimplePredictable ℱ H) :
    IsBoundedSimplePredictable ℱ (fun t ω ↦ throughStopMask τ t ω * H t ω) :=
  (throughStopMask_boundedSimplePredictable hτ hτ_range).mul_process hH

omit [MeasurableSpace Ω] in
theorem IsBoundedSimplePredictable.mul_stochasticIntervalMask
    {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    {σ τ : Ω → WithTop ℝ≥0} {H : ℝ≥0 → Ω → ℝ}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite)
    (hH : IsBoundedSimplePredictable ℱ H) :
    IsBoundedSimplePredictable ℱ
      (fun t ω ↦ stochasticIntervalMask σ τ t ω * H t ω) :=
  (stochasticIntervalMask_boundedSimplePredictable hσ hτ hσ_range hτ_range).mul_process hH

/-! ## Stopping-time algebra and finite-range/bound closure -/

omit [MeasurableSpace Ω] in
theorem finiteRange_min {σ τ : Ω → WithTop ℝ≥0}
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    (Set.range (fun ω ↦ min (σ ω) (τ ω))).Finite := by
  refine (hσ_range.prod hτ_range).image
      (fun p : WithTop ℝ≥0 × WithTop ℝ≥0 ↦ min p.1 p.2) |>.subset ?_
  rintro x ⟨ω, rfl⟩
  exact ⟨(σ ω, τ ω), ⟨⟨ω, rfl⟩, ⟨ω, rfl⟩⟩, rfl⟩

omit [MeasurableSpace Ω] in
theorem finiteRange_max {σ τ : Ω → WithTop ℝ≥0}
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    (Set.range (fun ω ↦ max (σ ω) (τ ω))).Finite := by
  refine (hσ_range.prod hτ_range).image
      (fun p : WithTop ℝ≥0 × WithTop ℝ≥0 ↦ max p.1 p.2) |>.subset ?_
  rintro x ⟨ω, rfl⟩
  exact ⟨(σ ω, τ ω), ⟨⟨ω, rfl⟩, ⟨ω, rfl⟩⟩, rfl⟩

omit [MeasurableSpace Ω] in
theorem finiteRange_min_const {σ : Ω → WithTop ℝ≥0}
    (hσ_range : (Set.range σ).Finite) (c : ℝ≥0) :
    (Set.range (fun ω ↦ min (σ ω) (c : WithTop ℝ≥0))).Finite := by
  refine (hσ_range.image (fun s : WithTop ℝ≥0 ↦ min s c)).subset ?_
  rintro x ⟨ω, rfl⟩
  exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩

omit [MeasurableSpace Ω] in
theorem finiteRange_max_const {σ : Ω → WithTop ℝ≥0}
    (hσ_range : (Set.range σ).Finite) (c : ℝ≥0) :
    (Set.range (fun ω ↦ max (σ ω) (c : WithTop ℝ≥0))).Finite := by
  refine (hσ_range.image (fun s : WithTop ℝ≥0 ↦ max s c)).subset ?_
  rintro x ⟨ω, rfl⟩
  exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩

omit [MeasurableSpace Ω] in
theorem finiteRange_add_const {σ : Ω → WithTop ℝ≥0}
    (hσ_range : (Set.range σ).Finite) (c : ℝ≥0) :
    (Set.range (fun ω ↦ σ ω + (c : WithTop ℝ≥0))).Finite := by
  refine (hσ_range.image (fun s : WithTop ℝ≥0 ↦ s + (c : WithTop ℝ≥0))).subset ?_
  rintro x ⟨ω, rfl⟩
  exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩

omit [MeasurableSpace Ω] in
theorem finiteRange_coe {σ : Ω → ℝ≥0} (hσ_range : (Set.range σ).Finite) :
    (Set.range (fun ω ↦ (σ ω : WithTop ℝ≥0))).Finite := by
  refine (hσ_range.image (fun s : ℝ≥0 ↦ (s : WithTop ℝ≥0))).subset ?_
  rintro x ⟨ω, rfl⟩
  exact ⟨σ ω, ⟨ω, rfl⟩, rfl⟩

omit [MeasurableSpace Ω] in
theorem upperBound_min {σ τ : Ω → WithTop ℝ≥0} {B : WithTop ℝ≥0}
    (hσ : ∀ ω, σ ω ≤ B) (hτ : ∀ ω, τ ω ≤ B) :
    ∀ ω, min (σ ω) (τ ω) ≤ B :=
  fun ω ↦ by
    rw [← min_self B]
    exact min_le_min (hσ ω) (hτ ω)

omit [MeasurableSpace Ω] in
theorem upperBound_max {σ τ : Ω → WithTop ℝ≥0} {B : WithTop ℝ≥0}
    (hσ : ∀ ω, σ ω ≤ B) (hτ : ∀ ω, τ ω ≤ B) :
    ∀ ω, max (σ ω) (τ ω) ≤ B :=
  fun ω ↦ max_le (hσ ω) (hτ ω)

omit [MeasurableSpace Ω] in
theorem upperBound_min_const {σ : Ω → WithTop ℝ≥0} {B : WithTop ℝ≥0}
    (hσ : ∀ ω, σ ω ≤ B) (c : ℝ≥0) :
    ∀ ω, min (σ ω) (c : WithTop ℝ≥0) ≤ max B c :=
  fun ω ↦ (min_le_left _ _).trans (le_max_of_le_left (hσ ω))

omit [MeasurableSpace Ω] in
theorem upperBound_max_const {σ : Ω → WithTop ℝ≥0} {B : WithTop ℝ≥0}
    (hσ : ∀ ω, σ ω ≤ B) (c : ℝ≥0) :
    ∀ ω, max (σ ω) (c : WithTop ℝ≥0) ≤ max B c :=
  fun ω ↦ max_le (le_max_of_le_left (hσ ω)) (le_max_of_le_right le_rfl)

omit [MeasurableSpace Ω] in
theorem upperBound_add_const {σ : Ω → WithTop ℝ≥0} {B : WithTop ℝ≥0}
    (hσ : ∀ ω, σ ω ≤ B) (c : ℝ≥0) :
    ∀ ω, σ ω + (c : WithTop ℝ≥0) ≤ B + c :=
  fun ω ↦ add_le_add_left (hσ ω) (c : WithTop ℝ≥0)

omit [MeasurableSpace Ω] in
theorem IsStoppingTime.min_finiteRange {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    IsStoppingTime ℱ (fun ω ↦ min (σ ω) (τ ω)) ∧
      (Set.range (fun ω ↦ min (σ ω) (τ ω))).Finite :=
  ⟨hσ.min hτ, finiteRange_min hσ_range hτ_range⟩

omit [MeasurableSpace Ω] in
theorem IsStoppingTime.max_finiteRange {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hσ_range : (Set.range σ).Finite) (hτ_range : (Set.range τ).Finite) :
    IsStoppingTime ℱ (fun ω ↦ max (σ ω) (τ ω)) ∧
      (Set.range (fun ω ↦ max (σ ω) (τ ω))).Finite :=
  ⟨hσ.max hτ, finiteRange_max hσ_range hτ_range⟩

omit [MeasurableSpace Ω] in
theorem IsStoppingTime.min_const_finiteRange {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hσ_range : (Set.range σ).Finite) (c : ℝ≥0) :
    IsStoppingTime ℱ (fun ω ↦ min (σ ω) (c : WithTop ℝ≥0)) ∧
      (Set.range (fun ω ↦ min (σ ω) (c : WithTop ℝ≥0))).Finite :=
  ⟨hσ.min_const c, finiteRange_min_const hσ_range c⟩

omit [MeasurableSpace Ω] in
theorem IsStoppingTime.max_const_finiteRange {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ) (hσ_range : (Set.range σ).Finite) (c : ℝ≥0) :
    IsStoppingTime ℱ (fun ω ↦ max (σ ω) (c : WithTop ℝ≥0)) ∧
      (Set.range (fun ω ↦ max (σ ω) (c : WithTop ℝ≥0))).Finite :=
  ⟨hσ.max_const c, finiteRange_max_const hσ_range c⟩

omit [MeasurableSpace Ω] in
theorem IsStoppingTime.add_const_finiteRange {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (hτ_range : (Set.range τ).Finite) (c : ℝ≥0) :
    IsStoppingTime ℱ (fun ω ↦ τ ω + (c : WithTop ℝ≥0)) ∧
      (Set.range (fun ω ↦ τ ω + (c : WithTop ℝ≥0))).Finite := by
  refine ⟨?_, finiteRange_add_const hτ_range c⟩
  intro j
  let addConstAtom : WithTop ℝ≥0 → Set Ω := fun s ↦
    {ω | τ ω = s ∧ s + (c : WithTop ℝ≥0) ≤ (j : WithTop ℝ≥0)}
  have hset : {ω | τ ω + (c : WithTop ℝ≥0) ≤ (j : WithTop ℝ≥0)} =
      ⋃ s ∈ Set.range τ, addConstAtom s := by
    ext ω
    constructor
    · intro hω
      rw [Set.mem_iUnion]
      refine ⟨τ ω, ?_⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨ω, rfl⟩, rfl, hω⟩
    · rw [Set.mem_iUnion]
      rintro ⟨s, hs⟩
      rw [Set.mem_iUnion] at hs
      rcases hs with ⟨_, hs⟩
      change τ ω + (c : WithTop ℝ≥0) ≤ (j : WithTop ℝ≥0)
      rw [hs.1]
      exact hs.2
  rw [hset]
  exact MeasurableSet.biUnion hτ_range.countable fun s hs ↦ by
    by_cases hsc : s + (c : WithTop ℝ≥0) ≤ (j : WithTop ℝ≥0)
    · have hsj : s ≤ (j : WithTop ℝ≥0) :=
        (le_add_of_nonneg_right
          (show (0 : WithTop ℝ≥0) ≤ (c : WithTop ℝ≥0) by positivity)).trans hsc
      have hsne : s ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hsj
      lift s to ℝ≥0 using hsne with s hscoe
      have hEq : addConstAtom (s : WithTop ℝ≥0) =
          {ω | τ ω = (s : WithTop ℝ≥0)} := by
        ext ω
        change (τ ω = (s : WithTop ℝ≥0) ∧
          (s : WithTop ℝ≥0) + c ≤ j) ↔ τ ω = (s : WithTop ℝ≥0)
        exact and_iff_left hsc
      rw [hEq]
      exact hτ.measurableSet_eq_le (WithTop.coe_le_coe.mp hsj)
    · have hEq : addConstAtom s = (∅ : Set Ω) := by
        ext ω
        change (τ ω = s ∧ s + (c : WithTop ℝ≥0) ≤ j) ↔ False
        exact ⟨fun h ↦ hsc h.2, False.elim⟩
      rw [hEq]
      exact @MeasurableSet.empty Ω (ℱ j)

omit [MeasurableSpace Ω] in
theorem IsStoppingTime.coe_add_const_finiteRange {m : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 m} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    (hσ_range : (Set.range σ).Finite) (c : ℝ≥0) :
    IsStoppingTime ℱ (fun ω ↦ ((σ ω + c : ℝ≥0) : WithTop ℝ≥0)) ∧
      (Set.range (fun ω ↦ ((σ ω + c : ℝ≥0) : WithTop ℝ≥0))).Finite := by
  exact IsStoppingTime.add_const_finiteRange hσ (finiteRange_coe hσ_range) c

end OTSelector.CountingProcess
