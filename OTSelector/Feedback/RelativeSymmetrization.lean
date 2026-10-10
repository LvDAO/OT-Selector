import OTSelector.Feedback.RelativeVC
import LeanPool.FormalLearningTheory.Complexity.BorelAnalyticBridge

/-!
# Relative VC symmetrization by pairwise exchangeability

This module connects the variance-sensitive restriction-pattern bounds to an actual iid double
sample.  It uses the pairwise swap action from the lean-pool symmetrization architecture, while
retaining the realized disagreement count in the Rademacher exponent.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace OTSelector.RelativeVC

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Disagreement set of a Boolean hypothesis and target concept. -/
def errorSet (h c : Concept Ω Bool) : Set Ω := {x | h x ≠ c x}

omit [MeasurableSpace Ω] in
@[simp] theorem indicatorReal_errorSet (h c : Concept Ω Bool) (x : Ω) :
    indicatorReal (errorSet h c) x = zeroOneLoss Bool (h x) (c x) := by
  by_cases hx : h x = c x
  · simp [indicatorReal, errorSet, zeroOneLoss, hx]
  · simp [indicatorReal, errorSet, zeroOneLoss, hx]

theorem measurableSet_errorSet {h c : Concept Ω Bool} (hh : Measurable h)
    (hc : Measurable c) : MeasurableSet (errorSet h c) :=
  (measurableSet_eq_fun hh hc).compl

/-- Swap the two observations in pair `i` when the corresponding sign is true. -/
def pairSwap {m : ℕ} (σ : SignVector m) (z : Fin m → Ω × Ω) : Fin m → Ω × Ω :=
  fun i ↦ if σ i then (z i).swap else z i

/-- List the first coordinates followed by the second coordinates of a paired sample. -/
def mergedPairSample {m : ℕ} (z : Fin m → Ω × Ω) : Fin (2 * m) → Ω :=
  fun j ↦ if h : j.val < m then (z ⟨j.val, by omega⟩).1
    else (z ⟨j.val - m, by omega⟩).2

/-- The signed coefficient attached to a binary restriction pattern and one sample pair. -/
noncomputable def pairPatternCoeff {m : ℕ} (p : Fin (2 * m) → Bool) (i : Fin m) : ℝ :=
  -((if p (⟨i.val + m, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0) -
    (if p (⟨i.val, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0))

/-- Number of positive labels in a binary pattern, grouped according to the sample pairs. -/
noncomputable def pairPatternMass {m : ℕ} (p : Fin (2 * m) → Bool) : ℝ :=
  ∑ i : Fin m,
    ((if p (⟨i.val, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0) +
      (if p (⟨i.val + m, by omega⟩ : Fin (2 * m)) then (1 : ℝ) else 0))

/-- Unnormalized empirical error difference between the second and first samples. -/
noncomputable def pairGap {m : ℕ} (h c : Concept Ω Bool) (z : Fin m → Ω × Ω) : ℝ :=
  (∑ i : Fin m, zeroOneLoss Bool (h (z i).2) (c (z i).2)) -
    ∑ i : Fin m, zeroOneLoss Bool (h (z i).1) (c (z i).1)

/-- Total number of errors across both halves of a paired sample. -/
noncomputable def pairErrorMass {m : ℕ} (h c : Concept Ω Bool)
    (z : Fin m → Ω × Ω) : ℝ :=
  ∑ i : Fin m,
    (zeroOneLoss Bool (h (z i).1) (c (z i).1) +
      zeroOneLoss Bool (h (z i).2) (c (z i).2))

/-- Unnormalized error count of one sample. -/
noncomputable def sampleErrorSum {m : ℕ} (h c : Concept Ω Bool) (xs : Fin m → Ω) : ℝ :=
  ∑ i : Fin m, zeroOneLoss Bool (h (xs i)) (c (xs i))

/-- Unnormalized centered error count. -/
noncomputable def centeredErrorSum (P : Measure Ω) {m : ℕ}
    (h c : Concept Ω Bool) (xs : Fin m → Ω) : ℝ :=
  sampleErrorSum h c xs - (m : ℝ) * P.real (errorSet h c)

theorem measurable_pairSwap {m : ℕ} (σ : SignVector m) :
    Measurable (pairSwap (Ω := Ω) σ) := by
  apply measurable_pi_lambda
  intro i
  by_cases hσi : σ i
  · simp only [pairSwap, hσi, ↓reduceIte]
    exact (measurable_pi_apply i |>.snd).prod (measurable_pi_apply i |>.fst)
  · simp only [pairSwap, hσi]
    exact measurable_pi_apply i

/-- Pairwise swaps preserve a finite iid product of identical pair laws. -/
theorem measurePreserving_pairSwap
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ} (σ : SignVector m) :
    MeasurePreserving (pairSwap σ)
      (Measure.pi (fun _ : Fin m ↦ P.prod P))
      (Measure.pi (fun _ : Fin m ↦ P.prod P)) := by
  let fσ : Fin m → (Ω × Ω) → (Ω × Ω) := fun i ↦ if σ i then Prod.swap else id
  have hpoint : pairSwap σ = fun z i ↦ fσ i (z i) := by
    funext z i
    simp only [pairSwap, fσ]
    split <;> simp
  refine ⟨measurable_pairSwap σ, ?_⟩
  rw [hpoint]
  rw [Measure.pi_map_pi (fun i ↦ by
    simp only [fσ]
    split
    · exact measurable_swap.aemeasurable
    · exact measurable_id.aemeasurable)]
  congr 1
  funext i
  simp only [fσ]
  split
  · exact Measure.prod_swap (μ := P) (ν := P)
  · exact Measure.map_id

/-- The coefficient variance is at most the total number of positive labels in the pattern. -/
theorem pairPatternCoeff_sq_sum_le_mass {m : ℕ} (p : Fin (2 * m) → Bool) :
    ∑ i : Fin m, pairPatternCoeff p i ^ 2 ≤ pairPatternMass p := by
  apply Finset.sum_le_sum
  intro i _
  simp only [pairPatternCoeff]
  split <;> split <;> norm_num

omit [MeasurableSpace Ω] in
/-- Pairwise swapping converts the empirical gap into the Rademacher signed sum of the realized
restriction pattern. -/
theorem pairGap_pairSwap_eq_rademacher {m : ℕ} (h c : Concept Ω Bool)
    (z : Fin m → Ω × Ω) (σ : SignVector m) :
    pairGap h c (pairSwap σ z) =
      ∑ i : Fin m,
        pairPatternCoeff
          (fun j ↦ decide (h (mergedPairSample z j) ≠ c (mergedPairSample z j))) i *
          boolToSign (σ i) := by
  rw [pairGap, ← Finset.sum_sub_distrib]
  congr 1
  ext i
  simp only [pairSwap, pairPatternCoeff, mergedPairSample]
  have hi_lt : i.val < m := i.isLt
  have hi_plus_ge : ¬(i.val + m < m) := by omega
  have him : i.val + m - m = i.val := by omega
  simp only [hi_lt, ↓reduceDIte, hi_plus_ge, him]
  rcases Bool.eq_false_or_eq_true (σ i) with hσi | hσi <;> simp only [hσi]
  · simp only [boolToSign, zeroOneLoss]
    rcases Bool.eq_false_or_eq_true (h (z i).2 == c (z i).2) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (h (z i).1 == c (z i).1) with h1 | h1 <;>
    simp [Ne]
  · simp only [boolToSign, Prod.swap, zeroOneLoss]
    rcases Bool.eq_false_or_eq_true (h (z i).2 == c (z i).2) with h2 | h2 <;>
    rcases Bool.eq_false_or_eq_true (h (z i).1 == c (z i).1) with h1 | h1 <;>
    simp [Ne]

omit [MeasurableSpace Ω] in
/-- The total error mass is invariant under pairwise swaps. -/
theorem pairErrorMass_pairSwap {m : ℕ} (h c : Concept Ω Bool)
    (z : Fin m → Ω × Ω) (σ : SignVector m) :
    pairErrorMass h c (pairSwap σ z) = pairErrorMass h c z := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hσi : σ i
  · simp [pairSwap, hσi, add_comm]
  · simp [pairSwap, hσi]

omit [MeasurableSpace Ω] in
/-- The pattern mass of a realized hypothesis is exactly its total double-sample error count. -/
theorem pairPatternMass_realized {m : ℕ} (h c : Concept Ω Bool)
    (z : Fin m → Ω × Ω) :
    pairPatternMass
      (fun j ↦ decide (h (mergedPairSample z j) ≠ c (mergedPairSample z j))) =
      pairErrorMass h c z := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [mergedPairSample]
  have hi_lt : i.val < m := i.isLt
  have hi_plus_ge : ¬(i.val + m < m) := by omega
  have him : i.val + m - m = i.val := by omega
  simp only [hi_lt, ↓reduceDIte, hi_plus_ge, him, zeroOneLoss]
  rcases Bool.eq_false_or_eq_true (h (z i).1 == c (z i).1) with h1 | h1 <;>
  rcases Bool.eq_false_or_eq_true (h (z i).2 == c (z i).2) with h2 | h2 <;>
  simp [Ne]

/-- The unnormalized pair gap is `√m` times the difference of the two centered empirical
processes. -/
theorem pairGap_zip_eq_sqrt_mul_empiricalProcess_sub
    (P : Measure Ω) {m : ℕ} (hm : 0 < m) (h c : Concept Ω Bool)
    (xs xs' : Fin m → Ω) :
    pairGap h c (fun i ↦ (xs i, xs' i)) =
      Real.sqrt m *
        (EmpiricalProcess.empiricalProcess P m xs' (indicatorReal (errorSet h c)) -
          EmpiricalProcess.empiricalProcess P m xs (indicatorReal (errorSet h c))) := by
  simp only [pairGap, indicatorReal_errorSet,
    EmpiricalProcess.empiricalProcess, EmpiricalProcess.empiricalAverage]
  have hm_real : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsqrt_sq : (Real.sqrt m) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg m)
  field_simp
  rw [hsqrt_sq]
  ring

/-- Decomposition of an unnormalized error count into its population mean and centered empirical
process. -/
theorem sampleErrorSum_eq_true_add_empiricalProcess
    (P : Measure Ω) {m : ℕ} (hm : 0 < m) (h c : Concept Ω Bool)
    (hs : MeasurableSet (errorSet h c)) (xs : Fin m → Ω) :
    sampleErrorSum h c xs =
      (m : ℝ) * P.real (errorSet h c) + Real.sqrt m *
        EmpiricalProcess.empiricalProcess P m xs (indicatorReal (errorSet h c)) := by
  simp only [sampleErrorSum, ← indicatorReal_errorSet,
    EmpiricalProcess.empiricalProcess, EmpiricalProcess.empiricalAverage]
  rw [show ∫ x, indicatorReal (errorSet h c) x ∂P = P.real (errorSet h c) by
    simpa [indicatorReal] using integral_indicator_one (μ := P) hs]
  have hm_real : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsqrt_sq : (Real.sqrt m) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg m)
  field_simp
  rw [hsqrt_sq]
  ring

theorem centeredErrorSum_eq_sqrt_mul_empiricalProcess
    (P : Measure Ω) {m : ℕ} (hm : 0 < m) (h c : Concept Ω Bool)
    (hs : MeasurableSet (errorSet h c)) (xs : Fin m → Ω) :
    centeredErrorSum P h c xs = Real.sqrt m *
      EmpiricalProcess.empiricalProcess P m xs (indicatorReal (errorSet h c)) := by
  rw [centeredErrorSum, sampleErrorSum_eq_true_add_empiricalProcess P hm h c hs xs]
  ring

/-- Generic ghost-sample reduction at success probability one half.  No measurability of the
possibly uncountable union `A` or `B` is assumed: the proof uses the completed measurable hull of
`B`, exactly as in lean-pool's symmetrization framework. -/
theorem ghost_half_symmetrization
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) (B : Set (α × α))
    (hghost : ∀ x ∈ A, ∃ G : Set α,
      (1 : ENNReal) / 2 ≤ μ G ∧ G ⊆ Prod.mk x ⁻¹' B) :
    μ A ≤ 2 * (μ.prod μ) B := by
  suffices hhalf : (1 : ENNReal) / 2 * μ A ≤ (μ.prod μ) B by
    have htwo : μ A ≤ 2 * ((1 : ENNReal) / 2 * μ A) := by
      rw [← mul_assoc, show (2 : ENNReal) * (1 / 2) = 1 from by
        simp [ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0)
          (by exact ENNReal.ofNat_ne_top)]]
      simp
    exact htwo.trans (mul_le_mul_right hhalf 2)
  let B' := toMeasurable (μ.prod μ) B
  have hB'_meas : MeasurableSet B' := measurableSet_toMeasurable _ _
  let f : α → ENNReal := fun x ↦ μ (Prod.mk x ⁻¹' B')
  have hf_meas : Measurable f := measurable_measure_prodMk_left hB'_meas
  have hcond : ∀ x ∈ A, (1 : ENNReal) / 2 ≤ f x := by
    intro x hx
    obtain ⟨G, hGhalf, hGsub⟩ := hghost x hx
    exact hGhalf.trans (measure_mono
      (hGsub.trans (Set.preimage_mono (subset_toMeasurable _ _))))
  have hmarkov : (1 : ENNReal) / 2 * μ {x | (1 : ENNReal) / 2 ≤ f x} ≤
      ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral hf_meas _
  have hprod : (μ.prod μ) B' = ∫⁻ x, μ (Prod.mk x ⁻¹' B') ∂μ :=
    Measure.prod_apply hB'_meas
  calc
    (1 : ENNReal) / 2 * μ A
        ≤ (1 : ENNReal) / 2 * μ {x | (1 : ENNReal) / 2 ≤ f x} := by
          apply mul_le_mul_right
          exact measure_mono hcond
    _ ≤ ∫⁻ x, f x ∂μ := hmarkov
    _ = (μ.prod μ) B' := hprod.symm
    _ = (μ.prod μ) B := measure_toMeasurable B

/-- A probability event of mass at most one half has a complement of mass at least one half. -/
theorem half_le_measure_compl_of_measure_le_half
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (H : Set α) (hH : μ H ≤ (1 : ENNReal) / 2) :
    (1 : ENNReal) / 2 ≤ μ Hᶜ := by
  have htotal : 1 ≤ μ H + μ Hᶜ := by
    have h := measure_union_le (μ := μ) H Hᶜ
    rwa [Set.union_compl_self, measure_univ] at h
  have hH_ne_top : μ H ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hH.trans (by norm_num))
  calc
    (1 : ENNReal) / 2 = 1 - 1 / 2 := by norm_num
    _ ≤ 1 - μ H := tsub_le_tsub_left hH 1
    _ ≤ (μ H + μ Hᶜ) - μ H := tsub_le_tsub_right htotal (μ H)
    _ = μ Hᶜ := ENNReal.add_sub_cancel_left hH_ne_top

/-- The variance-localized double-sample event used by relative VC symmetrization. -/
noncomputable def relativeDoubleSampleEvent {m : ℕ}
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (u varianceCap : ℝ) :
    Set (Fin m → Ω × Ω) :=
  {z | ∃ h ∈ C,
    u ≤ |pairGap h c z| ∧ pairErrorMass h c z ≤ varianceCap}

/-- The same localized double-sample event in the usual product-of-samples representation. -/
noncomputable def relativeDoubleSampleEventProd {m : ℕ}
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (u varianceCap : ℝ) :
    Set ((Fin m → Ω) × (Fin m → Ω)) :=
  {p | ∃ h ∈ C,
    u ≤ |(∑ i : Fin m, zeroOneLoss Bool (h (p.2 i)) (c (p.2 i))) -
      ∑ i : Fin m, zeroOneLoss Bool (h (p.1 i)) (c (p.1 i))| ∧
    (∑ i : Fin m,
      (zeroOneLoss Bool (h (p.1 i)) (c (p.1 i)) +
        zeroOneLoss Bool (h (p.2 i)) (c (p.2 i)))) ≤ varianceCap}

/-- Parameter-space witness set whose projection is a localized relative double-sample event. -/
noncomputable def relativeParamWitnessSet
    {Θ : Type*} (e : Θ → Concept Ω Bool) (c : Concept Ω Bool)
    (m : ℕ) (u varianceCap : ℝ) : Set (Θ × GhostPairs Ω m) :=
  {q | u ≤ |(∑ i : Fin m, zeroOneLoss Bool (e q.1 (q.2.2 i)) (c (q.2.2 i))) -
      ∑ i : Fin m, zeroOneLoss Bool (e q.1 (q.2.1 i)) (c (q.2.1 i))| ∧
    (∑ i : Fin m,
      (zeroOneLoss Bool (e q.1 (q.2.1 i)) (c (q.2.1 i)) +
        zeroOneLoss Bool (e q.1 (q.2.2 i)) (c (q.2.2 i)))) ≤ varianceCap}

private theorem parameterizedSampleErrorSum_measurable
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept Ω Bool)
    (he : Measurable (fun p : Θ × Ω ↦ e p.1 p.2))
    (c : Concept Ω Bool) (hc : Measurable c) (m : ℕ)
    (sel : GhostPairs Ω m → (Fin m → Ω)) (hsel : Measurable sel) :
    Measurable fun q : Θ × GhostPairs Ω m ↦
      ∑ i : Fin m, zeroOneLoss Bool (e q.1 (sel q.2 i)) (c (sel q.2 i)) := by
  apply Finset.measurable_sum
  intro i _
  simp only [zeroOneLoss]
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (he.comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp (hsel.comp measurable_snd))))
      (hc.comp ((measurable_pi_apply i).comp (hsel.comp measurable_snd)))
  · exact measurable_const
  · exact measurable_const

theorem relativeParamWitnessSet_measurable
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept Ω Bool)
    (he : Measurable (fun p : Θ × Ω ↦ e p.1 p.2))
    (c : Concept Ω Bool) (hc : Measurable c)
    (m : ℕ) (u varianceCap : ℝ) :
    MeasurableSet (relativeParamWitnessSet e c m u varianceCap) := by
  let first : GhostPairs Ω m → (Fin m → Ω) := Prod.fst
  let second : GhostPairs Ω m → (Fin m → Ω) := Prod.snd
  have hfirst : Measurable first := measurable_fst
  have hsecond : Measurable second := measurable_snd
  have hmFirst := parameterizedSampleErrorSum_measurable e he c hc m first hfirst
  have hmSecond := parameterizedSampleErrorSum_measurable e he c hc m second hsecond
  have hmGapAbs : Measurable fun q : Θ × GhostPairs Ω m ↦
      |(∑ i : Fin m, zeroOneLoss Bool (e q.1 (q.2.2 i)) (c (q.2.2 i))) -
        ∑ i : Fin m, zeroOneLoss Bool (e q.1 (q.2.1 i)) (c (q.2.1 i))| := by
    simpa only [first, second, Pi.sub_apply, Real.norm_eq_abs] using
      (hmSecond.sub hmFirst).norm
  have hmMass' : Measurable fun q : Θ × GhostPairs Ω m ↦
      (∑ i : Fin m, zeroOneLoss Bool (e q.1 (q.2.1 i)) (c (q.2.1 i))) +
        ∑ i : Fin m, zeroOneLoss Bool (e q.1 (q.2.2 i)) (c (q.2.2 i)) := by
    exact hmFirst.add hmSecond
  have hmMass : Measurable fun q : Θ × GhostPairs Ω m ↦
      ∑ i : Fin m,
        (zeroOneLoss Bool (e q.1 (q.2.1 i)) (c (q.2.1 i)) +
          zeroOneLoss Bool (e q.1 (q.2.2 i)) (c (q.2.2 i))) := by
    simpa only [Finset.sum_add_distrib] using hmMass'
  unfold relativeParamWitnessSet
  exact (measurableSet_le measurable_const hmGapAbs).inter
    (measurableSet_le hmMass measurable_const)

/-- Borel parameterization discharges the localized double-sample measurability condition through
the lean-pool analytic-set bridge. -/
theorem relativeDoubleSampleEventProd_nullMeasurable_of_borelParam
    [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept Ω Bool)
    (he : Measurable (fun p : Θ × Ω ↦ e p.1 p.2))
    (c : Concept Ω Bool) (hc : Measurable c)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (u varianceCap : ℝ) :
    NullMeasurableSet
      (relativeDoubleSampleEventProd (Set.range e) c u varianceCap)
      ((Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P))) := by
  let W := relativeParamWitnessSet e c m u varianceCap
  have hW : MeasurableSet W := relativeParamWitnessSet_measurable e he c hc m u varianceCap
  have : SecondCountableTopology
      (Set.range (Prod.snd : Θ × GhostPairs Ω m → GhostPairs Ω m)) := inferInstance
  have hanalytic : AnalyticSet (Prod.snd '' W) := hW.analyticSet_image measurable_snd
  have hevent : Prod.snd '' W =
      relativeDoubleSampleEventProd (Set.range e) c u varianceCap := by
    ext p
    simp only [W, relativeParamWitnessSet, relativeDoubleSampleEventProd,
      Set.mem_image, Set.mem_ofPred_eq, Prod.exists, Set.mem_range]
    constructor
    · rintro ⟨θ, p1, p2, hp, heq⟩
      have hpEq : (p1, p2) = p :=
        Prod.ext (congrArg Prod.fst heq) (congrArg Prod.snd heq)
      subst hpEq
      exact ⟨e θ, ⟨θ, rfl⟩, hp⟩
    · rintro ⟨_, ⟨θ, rfl⟩, hp⟩
      exact ⟨θ, p.1, p.2, hp, rfl⟩
  rw [← hevent]
  exact analyticSet_nullMeasurableSet_ghostPairs hanalytic P

theorem arrowProd_preimage_relativeDoubleSampleEventProd {m : ℕ}
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool) (u varianceCap : ℝ) :
    (MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin m)) ⁻¹'
        relativeDoubleSampleEventProd C c u varianceCap =
      relativeDoubleSampleEvent C c u varianceCap := by
  ext z
  simp only [relativeDoubleSampleEventProd, relativeDoubleSampleEvent,
    Set.mem_preimage, Set.mem_ofPred_eq, pairGap, pairErrorMass,
    MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]

/-- Actual double-sample relative-VC bound.  Pairwise exchangeability, restriction-pattern
counting, and the realized quadratic-variation estimate are all discharged in the proof. -/
theorem doubleSample_relative_vc_bound [Infinite Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (m : ℕ) (u varianceCap : ℝ) (hu : 0 < u) (hvarianceCap : 0 < varianceCap)
    (hnull : NullMeasurableSet (relativeDoubleSampleEvent C c u varianceCap)
      (Measure.pi (fun _ : Fin m ↦ P.prod P))) :
    Measure.pi (fun _ : Fin m ↦ P.prod P)
        (relativeDoubleSampleEvent C c u varianceCap) ≤
      ENNReal.ofReal
        (2 * (GrowthFunction Ω C (2 * m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * varianceCap))) := by
  classical
  let ν := Measure.pi (fun _ : Fin m ↦ P.prod P)
  let S : Set (Fin m → Ω × Ω) :=
    relativeDoubleSampleEvent (m := m) C c u varianceCap
  let bound : ℝ := 2 * (GrowthFunction Ω C (2 * m) : ℝ) *
    Real.exp (-(u ^ 2) / (2 * varianceCap))
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    positivity
  have hper_z : ∀ z : Fin m → Ω × Ω,
      ((Finset.univ.filter (fun σ : SignVector m ↦ pairSwap σ z ∈ S)).card : ℝ) ≤
        bound * (Fintype.card (SignVector m) : ℝ) := by
    intro z
    let merged := mergedPairSample z
    let patterns := restrictionPatterns C c (2 * m) merged
    let shellPatterns := patterns.filter (fun p ↦ pairPatternMass p ≤ varianceCap)
    let coeff : (Fin (2 * m) → Bool) → Fin m → ℝ := pairPatternCoeff
    have hvar_le : ∀ p ∈ shellPatterns, ∑ i, coeff p i ^ 2 ≤ varianceCap := by
      intro p hp
      have hpMass : pairPatternMass p ≤ varianceCap := (Finset.mem_filter.mp hp).2
      exact (pairPatternCoeff_sq_sum_le_mass p).trans hpMass
    have hrad := rademacher_finitePattern_tail_card_of_variance_le
      shellPatterns coeff hu hvarianceCap hvar_le
    have hsubset :
        Finset.univ.filter (fun σ : SignVector m ↦ pairSwap σ z ∈ S) ⊆
          Finset.univ.filter (fun σ : SignVector m ↦
            ∃ p ∈ shellPatterns,
              u ≤ |∑ i, coeff p i * boolToSign (σ i)|) := by
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      change pairSwap σ z ∈ relativeDoubleSampleEvent C c u varianceCap at hσ
      obtain ⟨h, hhC, hgap, hmass⟩ := hσ
      let p : Fin (2 * m) → Bool :=
        fun j ↦ decide (h (mergedPairSample z j) ≠ c (mergedPairSample z j))
      have hpPatterns : p ∈ patterns := by
        apply (mem_restrictionPatterns_iff C c (2 * m) merged p).2
        exact ⟨h, hhC, fun _ ↦ rfl⟩
      have hpMass : pairPatternMass p ≤ varianceCap := by
        rw [show pairPatternMass p = pairErrorMass h c z by
          exact pairPatternMass_realized h c z]
        rw [← pairErrorMass_pairSwap h c z σ]
        exact hmass
      have hpShell : p ∈ shellPatterns :=
        Finset.mem_filter.mpr ⟨hpPatterns, hpMass⟩
      refine ⟨p, hpShell, ?_⟩
      rw [pairGap_pairSwap_eq_rademacher h c z σ] at hgap
      exact hgap
    let common : ℝ :=
      2 * (Fintype.card (SignVector m) : ℝ) *
        Real.exp (-(u ^ 2) / (2 * varianceCap))
    have hshell_card : (shellPatterns.card : ℝ) ≤
        (GrowthFunction Ω C (2 * m) : ℝ) := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (restrictionPatterns_card_le_growth C c (2 * m) merged)
    calc
      ((Finset.univ.filter (fun σ : SignVector m ↦ pairSwap σ z ∈ S)).card : ℝ)
          ≤ ((Finset.univ.filter (fun σ : SignVector m ↦
              ∃ p ∈ shellPatterns,
                u ≤ |∑ i, coeff p i * boolToSign (σ i)|)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsubset
      _ ≤ (shellPatterns.card : ℝ) * common := by
        simpa only [common] using hrad
      _ ≤ (GrowthFunction Ω C (2 * m) : ℝ) * common :=
        mul_le_mul_of_nonneg_right hshell_card (by dsimp [common]; positivity)
      _ = bound * (Fintype.card (SignVector m) : ℝ) := by
        dsimp [bound, common]
        ring
  have hpointwise : ∀ z : Fin m → Ω × Ω,
      (∑ σ : SignVector m,
        ((pairSwap σ ⁻¹' S).indicator (1 : (Fin m → Ω × Ω) → ENNReal)) z) ≤
          ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
    intro z
    have hsum :
        (∑ σ : SignVector m,
          ((pairSwap σ ⁻¹' S).indicator (1 : (Fin m → Ω × Ω) → ENNReal)) z) =
            ((Finset.univ.filter (fun σ : SignVector m ↦ pairSwap σ z ∈ S)).card :
              ENNReal) := by
      simp only [Set.indicator_apply, Pi.one_apply, Set.mem_preimage]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum]
    calc
      ((Finset.univ.filter (fun σ : SignVector m ↦ pairSwap σ z ∈ S)).card :
          ENNReal) ≤ ENNReal.ofReal
            (bound * (Fintype.card (SignVector m) : ℝ)) := by
              exact_mod_cast ENNReal.ofReal_le_ofReal (hper_z z)
      _ = ENNReal.ofReal bound *
          ENNReal.ofReal (Fintype.card (SignVector m) : ℝ) := by
            rw [ENNReal.ofReal_mul hbound_nonneg]
      _ = ENNReal.ofReal bound * (Fintype.card (SignVector m) : ENNReal) := by
            congr 1
            rw [ENNReal.ofReal_natCast]
  have hmp : ∀ σ : SignVector m, MeasurePreserving (pairSwap σ) ν ν := by
    intro σ
    exact measurePreserving_pairSwap P σ
  have hresult := finite_exchangeability_bound
    (fun σ : SignVector m ↦ pairSwap σ) S hmp hnull (ENNReal.ofReal bound) hpointwise
  simpa only [ν, S, bound] using hresult

/-- Product-of-samples form of `doubleSample_relative_vc_bound`. -/
theorem doubleSample_relative_vc_bound_prod [Infinite Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (m : ℕ) (u varianceCap : ℝ) (hu : 0 < u) (hvarianceCap : 0 < varianceCap)
    (hnull : NullMeasurableSet (relativeDoubleSampleEventProd C c u varianceCap)
      ((Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P)))) :
    (Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P))
        (relativeDoubleSampleEventProd C c u varianceCap) ≤
      ENNReal.ofReal
        (2 * (GrowthFunction Ω C (2 * m) : ℝ) *
          Real.exp (-(u ^ 2) / (2 * varianceCap))) := by
  let μ := Measure.pi (fun _ : Fin m ↦ P)
  let ν := Measure.pi (fun _ : Fin m ↦ P.prod P)
  let eqv := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin m)
  have hmp : MeasurePreserving (⇑eqv) ν (μ.prod μ) := by
    dsimp [ν, μ, eqv]
    exact measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin m)
      (fun _ ↦ P) (fun _ ↦ P)
  have hpre : eqv ⁻¹' relativeDoubleSampleEventProd C c u varianceCap =
      relativeDoubleSampleEvent C c u varianceCap :=
    arrowProd_preimage_relativeDoubleSampleEventProd C c u varianceCap
  have hnull_pair : NullMeasurableSet (relativeDoubleSampleEvent C c u varianceCap) ν := by
    rw [← hpre]
    exact hnull.preimage hmp.quasiMeasurePreserving
  have hmeasure : (μ.prod μ) (relativeDoubleSampleEventProd C c u varianceCap) =
      ν (relativeDoubleSampleEvent C c u varianceCap) := by
    rw [← hpre, ← hmp.map_eq]
    exact eqv.map_apply _
  rw [show (Measure.pi (fun _ : Fin m ↦ P)).prod
      (Measure.pi (fun _ : Fin m ↦ P)) = μ.prod μ from rfl, hmeasure]
  exact doubleSample_relative_vc_bound P C c m u varianceCap hu hvarianceCap hnull_pair

/-- A single-sample VC deviation localized simultaneously by population mass and observed error
count. -/
noncomputable def localizedRelativeVCEvent
    (P : Measure Ω) {m : ℕ} (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (x trueMassCap sampleMassCap : ℝ) : Set (Fin m → Ω) :=
  {xs | ∃ h ∈ C,
    P.real (errorSet h c) ≤ trueMassCap ∧
    x ≤ |EmpiricalProcess.empiricalProcess P m xs (indicatorReal (errorSet h c))| ∧
    sampleErrorSum h c xs ≤ sampleMassCap}

/-- Localized relative-VC Bernstein theorem.  The displayed numerical hypothesis is exactly the
fixed-hypothesis Bernstein condition ensuring that the ghost sample is good with probability at
least one half.  The conclusion contains only the VC growth function and the localized variance
cap; no extra witness bundle or finite-class surrogate appears. -/
theorem localized_relative_vc_bernstein [Infinite Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m)
    (x trueMassCap sampleMassCap : ℝ) (hx : 0 < x)
    (hghostBernstein :
      ENNReal.ofReal
        (2 * Real.exp (-((x / 2) ^ 2) /
          (4 * (trueMassCap + (x / 2) / Real.sqrt m)))) ≤ (1 : ENNReal) / 2)
    (hvarianceCap :
      0 < sampleMassCap + (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2))
    (hnull : NullMeasurableSet
      (relativeDoubleSampleEventProd C c (Real.sqrt m * x / 2)
        (sampleMassCap + (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2)))
      ((Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P)))) :
    Measure.pi (fun _ : Fin m ↦ P)
        (localizedRelativeVCEvent P C c x trueMassCap sampleMassCap) ≤
      2 * ENNReal.ofReal
        (2 * (GrowthFunction Ω C (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * x / 2) ^ 2) /
            (2 * (sampleMassCap + (m : ℝ) * trueMassCap +
              Real.sqrt m * (x / 2))))) := by
  classical
  let μ := Measure.pi (fun _ : Fin m ↦ P)
  let A : Set (Fin m → Ω) :=
    localizedRelativeVCEvent (m := m) P C c x trueMassCap sampleMassCap
  let uDouble := Real.sqrt m * x / 2
  let varianceDouble :=
    sampleMassCap + (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2)
  let B : Set ((Fin m → Ω) × (Fin m → Ω)) :=
    relativeDoubleSampleEventProd (m := m) C c uDouble varianceDouble
  have hm_one : 1 ≤ m := hm
  have hxhalf : 0 < x / 2 := by linarith
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.2 (Nat.cast_pos.2 hm)
  have huDouble : 0 < uDouble := by
    dsimp [uDouble]
    positivity
  have hsymm : μ A ≤ 2 * (μ.prod μ) B := by
    apply ghost_half_symmetrization μ A B
    intro xs hxs
    change xs ∈ localizedRelativeVCEvent P C c x trueMassCap sampleMassCap at hxs
    obtain ⟨h, hhC, htrue, hbad, hsample⟩ := hxs
    let H : Set (Fin m → Ω) :=
      {xs' | x / 2 <
        |EmpiricalProcess.empiricalProcess P m xs' (indicatorReal (errorSet h c))|}
    refine ⟨Hᶜ, ?_, ?_⟩
    · have hH_le : μ H ≤ (1 : ENNReal) / 2 := by
        have hbern := centeredIndicator_bernstein_pi_of_mass_le
          P (errorSet h c) (measurableSet_errorSet (hmeas_C h hhC) hc_meas)
          m hm_one hxhalf htrue
        exact hbern.trans hghostBernstein
      exact half_le_measure_compl_of_measure_le_half μ H hH_le
    · intro xs' hxs'
      have hgood :
          |EmpiricalProcess.empiricalProcess P m xs' (indicatorReal (errorSet h c))| ≤
            x / 2 := by
        simpa only [H, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] using hxs'
      change (xs, xs') ∈ relativeDoubleSampleEventProd C c uDouble varianceDouble
      refine ⟨h, hhC, ?_, ?_⟩
      · let e0 := EmpiricalProcess.empiricalProcess P m xs (indicatorReal (errorSet h c))
        let e1 := EmpiricalProcess.empiricalProcess P m xs' (indicatorReal (errorSet h c))
        have hreverse : x / 2 ≤ |e1 - e0| := by
          calc
            x / 2 ≤ |e0| - |e1| := by
              dsimp [e0, e1]
              linarith
            _ ≤ |e0 - e1| := abs_sub_abs_le_abs_sub e0 e1
            _ = |e1 - e0| := abs_sub_comm e0 e1
        change uDouble ≤ |pairGap h c (fun i ↦ (xs i, xs' i))|
        rw [pairGap_zip_eq_sqrt_mul_empiricalProcess_sub P hm h c xs xs']
        dsimp [uDouble, e0, e1] at hreverse ⊢
        rw [abs_mul, abs_of_pos hsqrt_pos]
        nlinarith [mul_le_mul_of_nonneg_left hreverse hsqrt_pos.le]
      · rw [Finset.sum_add_distrib]
        change sampleErrorSum h c xs + sampleErrorSum h c xs' ≤ varianceDouble
        have hs := measurableSet_errorSet (hmeas_C h hhC) hc_meas
        have he1_le :
            EmpiricalProcess.empiricalProcess P m xs' (indicatorReal (errorSet h c)) ≤
              x / 2 := (le_abs_self _).trans hgood
        have hghostMass : sampleErrorSum h c xs' ≤
            (m : ℝ) * trueMassCap + Real.sqrt m * (x / 2) := by
          rw [sampleErrorSum_eq_true_add_empiricalProcess P hm h c hs xs']
          exact add_le_add
            (mul_le_mul_of_nonneg_left htrue (Nat.cast_nonneg m))
            (mul_le_mul_of_nonneg_left he1_le (Real.sqrt_nonneg m))
        calc
          sampleErrorSum h c xs + sampleErrorSum h c xs'
              ≤ sampleMassCap +
                ((m : ℝ) * trueMassCap + Real.sqrt m * (x / 2)) :=
            add_le_add hsample hghostMass
          _ = varianceDouble := by
            dsimp [varianceDouble]
            ring
  have hdouble : (μ.prod μ) B ≤ ENNReal.ofReal
      (2 * (GrowthFunction Ω C (2 * m) : ℝ) *
        Real.exp (-(uDouble ^ 2) / (2 * varianceDouble))) := by
    exact doubleSample_relative_vc_bound_prod P C c m uDouble varianceDouble
      huDouble (by simpa only [varianceDouble] using hvarianceCap) hnull
  refine hsymm.trans ?_
  apply mul_le_mul_right
  simpa only [uDouble, varianceDouble] using hdouble

/-- Finite peeling of the localized relative-VC theorem.  Each shell is an actual population/empirical
mass slice; the conclusion is a sum of explicit VC--Bernstein tails. -/
theorem finite_localized_relative_vc_peeling [Infinite Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (C : ConceptClass Ω Bool) (c : Concept Ω Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (K : ℕ)
    (threshold trueMassCap sampleMassCap : Fin K → ℝ)
    (hthreshold : ∀ k, 0 < threshold k)
    (hghostBernstein : ∀ k,
      ENNReal.ofReal
        (2 * Real.exp (-((threshold k / 2) ^ 2) /
          (4 * (trueMassCap k + (threshold k / 2) / Real.sqrt m)))) ≤
        (1 : ENNReal) / 2)
    (hvarianceCap : ∀ k,
      0 < sampleMassCap k + (m : ℝ) * trueMassCap k +
        Real.sqrt m * (threshold k / 2))
    (hnull : ∀ k, NullMeasurableSet
      (relativeDoubleSampleEventProd C c (Real.sqrt m * threshold k / 2)
        (sampleMassCap k + (m : ℝ) * trueMassCap k +
          Real.sqrt m * (threshold k / 2)))
      ((Measure.pi (fun _ : Fin m ↦ P)).prod (Measure.pi (fun _ : Fin m ↦ P)))) :
    Measure.pi (fun _ : Fin m ↦ P)
        {xs | ∃ k : Fin K,
          xs ∈ localizedRelativeVCEvent P C c (threshold k)
            (trueMassCap k) (sampleMassCap k)} ≤
      ∑ k : Fin K, 2 * ENNReal.ofReal
        (2 * (GrowthFunction Ω C (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
            (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
              Real.sqrt m * (threshold k / 2))))) := by
  let μ := Measure.pi (fun _ : Fin m ↦ P)
  let event : Fin K → Set (Fin m → Ω) := fun k ↦
    localizedRelativeVCEvent P C c (threshold k) (trueMassCap k) (sampleMassCap k)
  have hsubset : {xs | ∃ k : Fin K, xs ∈ event k} ⊆ ⋃ k, event k := by
    rintro xs ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  calc
    μ {xs | ∃ k : Fin K, xs ∈ event k}
        ≤ μ (⋃ k, event k) := measure_mono hsubset
    _ ≤ ∑ k : Fin K, μ (event k) := by
      simpa using measure_iUnion_le (μ := μ) event
    _ ≤ ∑ k : Fin K, 2 * ENNReal.ofReal
        (2 * (GrowthFunction Ω C (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
            (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
              Real.sqrt m * (threshold k / 2))))) := by
      exact Finset.sum_le_sum fun k _ ↦ localized_relative_vc_bernstein
        P C c hmeas_C hc_meas m hm (threshold k) (trueMassCap k) (sampleMassCap k)
        (hthreshold k) (hghostBernstein k) (hvarianceCap k) (hnull k)

/-- Borel-parameterized peeling theorem.  The analytic measurability of every
localized double-sample shell is derived from the joint evaluation map. -/
theorem finite_localized_relative_vc_peeling_of_borelParam
    [Infinite Ω] [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept Ω Bool)
    (he : Measurable (fun p : Θ × Ω ↦ e p.1 p.2))
    (c : Concept Ω Bool) (hc : Measurable c)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (hm : 0 < m) (K : ℕ)
    (threshold trueMassCap sampleMassCap : Fin K → ℝ)
    (hthreshold : ∀ k, 0 < threshold k)
    (hghostBernstein : ∀ k,
      ENNReal.ofReal
        (2 * Real.exp (-((threshold k / 2) ^ 2) /
          (4 * (trueMassCap k + (threshold k / 2) / Real.sqrt m)))) ≤
        (1 : ENNReal) / 2)
    (hvarianceCap : ∀ k,
      0 < sampleMassCap k + (m : ℝ) * trueMassCap k +
        Real.sqrt m * (threshold k / 2)) :
    Measure.pi (fun _ : Fin m ↦ P)
        {xs | ∃ k : Fin K,
          xs ∈ localizedRelativeVCEvent P (Set.range e) c (threshold k)
            (trueMassCap k) (sampleMassCap k)} ≤
      ∑ k : Fin K, 2 * ENNReal.ofReal
        (2 * (GrowthFunction Ω (Set.range e) (2 * m) : ℝ) *
          Real.exp (-((Real.sqrt m * threshold k / 2) ^ 2) /
            (2 * (sampleMassCap k + (m : ℝ) * trueMassCap k +
              Real.sqrt m * (threshold k / 2))))) := by
  have hmeas_range : ∀ h ∈ Set.range e, Measurable h := by
    rintro _ ⟨θ, rfl⟩
    exact he.comp (measurable_const.prodMk measurable_id)
  exact finite_localized_relative_vc_peeling P (Set.range e) c hmeas_range hc
    m hm K threshold trueMassCap sampleMassCap hthreshold hghostBernstein hvarianceCap
    (fun k ↦ relativeDoubleSampleEventProd_nullMeasurable_of_borelParam
      e he c hc P m _ _)

end OTSelector.RelativeVC
