import OTSelector.Probability.CountingProcess.Core

/-!
# Closure under bounded predictable transforms

`HasPredictableIntensity` is stated for bounded transforms with finite range.  The occupation
estimates use transforms of the form `(e^θ - 1) · exp(θ N₋) · exp((1 - e^θ) ∫ Λ)`,
which are bounded and predictable but do not have finite range.  This file closes that gap by
dominated-convergence approximation: the `StronglyMeasurable` approximation sequence of a bounded
predictable process lies in the simple class of `Core`, and pointwise convergence of the pathwise
counting integrals and compensators transfers the martingale property to the limit.

The main entry point is `HasPredictableIntensity.martingale_of_boundedPredictable`.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Bounded predictable processes and their approximations -/

/-- A bounded predictable real process: strongly predictable and uniformly bounded.  Unlike
`IsBoundedSimplePredictable`, no finite-range condition is imposed. -/
def IsBoundedPredictable (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable ℱ H ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |H t ω| ≤ C

/-- Pointwise `n`-th bounded approximation of a predictable process, obtained by evaluating the
`StronglyMeasurable` approximation at each time point. -/
noncomputable def approxProcess {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m} {H : ℝ≥0 → Ω → ℝ}
    (hHpred : StronglyMeasurable[ℱ.predictable] (Function.uncurry H)) (C : ℝ) (n : ℕ) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ (hHpred.approxBounded C n) ⟨t, ω⟩

omit [MeasurableSpace Ω] in
/-- Each bounded approximation is a bounded simple predictable transform. -/
theorem IsBoundedSimplePredictable.approxProcess_spec
    {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m} {H : ℝ≥0 → Ω → ℝ}
    (hHpred : StronglyMeasurable[ℱ.predictable] (Function.uncurry H)) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) :
    IsBoundedSimplePredictable ℱ (approxProcess hHpred C n) := by
  refine ⟨?_, ?_, C, hC, ?_⟩
  · have hcoef : Function.uncurry (approxProcess hHpred C n) =
        ((hHpred.approxBounded C n) : ℝ≥0 × Ω → ℝ) := by
      ext z
      cases z
      rfl
    change StronglyMeasurable[ℱ.predictable] (Function.uncurry (approxProcess hHpred C n))
    rw [hcoef]
    exact SimpleFunc.stronglyMeasurable (hHpred.approxBounded C n)
  · let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    have hcoef2 : Function.uncurry (approxProcess hHpred C n) =
        ((hHpred.approxBounded C n) : ℝ≥0 × Ω → ℝ) := by
      ext z
      cases z
      rfl
    have hrange : (Set.range (Function.uncurry (approxProcess hHpred C n))).Finite := by
      rw [hcoef2]
      exact (hHpred.approxBounded C n).finite_range
    exact hrange
  · intro t ω
    change |(hHpred.approxBounded C n) ⟨t, ω⟩| ≤ C
    have hnorm : ‖(hHpred.approxBounded C n) ⟨t, ω⟩‖ ≤ C :=
      StronglyMeasurable.norm_approxBounded_le hHpred hC n ⟨t, ω⟩
    simpa [Real.norm_eq_abs] using hnorm

/-- Pointwise convergence of the bounded approximations of a bounded predictable process. -/
theorem tendsto_approxProcess
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0 → Ω → ℝ}
    (hHpred : StronglyMeasurable[ℱ.predictable] (Function.uncurry H)) (C : ℝ)
    (hHbound : ∀ t ω, |H t ω| ≤ C) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ approxProcess hHpred C n t ω) atTop (𝓝 (H t ω)) := by
  have hfx : ‖H t ω‖ ≤ C := by
    rw [Real.norm_eq_abs]
    exact hHbound t ω
  simpa [approxProcess, Function.uncurry] using
    StronglyMeasurable.tendsto_approxBounded_of_norm_le hHpred hfx

/-! ## The predictable σ-algebra sits below the ambient product σ-algebra -/

omit [MeasurableSpace Ω] in
/-- The predictable σ-algebra is contained in the ambient product σ-algebra of `ℝ≥0 × Ω`. -/
theorem predictable_le_ambient {m : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 m) :
    ℱ.predictable ≤ (Prod.instMeasurableSpace : MeasurableSpace (ℝ≥0 × Ω)) := by
  apply MeasurableSpace.generateFrom_le
  rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · exact MeasurableSet.prod (measurableSet_singleton (0 : ℝ≥0)) ((ℱ.le ⊥) _ hA)
  · exact MeasurableSet.prod (measurableSet_Ioi : MeasurableSet (Ioi i)) ((ℱ.le i) _ hA)

/-! ## Pathwise convergence and uniform bounds of the approximations -/

/-- The pathwise counting integral of the bounded approximations converges to the counting
integral of the limit process. -/
theorem tendsto_countingIntegral_approx {N : ℝ≥0 → Ω → ℕ} {H : ℝ≥0 → Ω → ℝ}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (hHpred : StronglyMeasurable[ℱ.predictable] (Function.uncurry H)) (C : ℝ)
    (hHbound : ∀ t ω, |H t ω| ≤ C) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ countingIntegral N (approxProcess hHpred C n) t ω) atTop
      (𝓝 (countingIntegral N H t ω)) := by
  unfold countingIntegral
  refine tendsto_finsetSum (s := Finset.range (N t ω))
    (f := fun k n ↦ approxProcess hHpred C n (jumpTime N k ω) ω)
    (a := fun k ↦ H (jumpTime N k ω) ω) ?_
  intro k hk
  have hfx : ‖H (jumpTime N k ω) ω‖ ≤ C := by
    rw [Real.norm_eq_abs]
    exact hHbound (jumpTime N k ω) ω
  simpa [approxProcess, Function.uncurry] using
    StronglyMeasurable.tendsto_approxBounded_of_norm_le hHpred hfx

/-- The pathwise compensator of the bounded approximations converges pointwise to the
compensator of the limit process, by dominated convergence in the time variable. -/
theorem tendsto_integratedIntensity_approx
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ H : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hHpred : StronglyMeasurable[ℱ.predictable] (Function.uncurry H)) (C : ℝ) (hC : 0 ≤ C)
    (hHbound : ∀ t ω, |H t ω| ≤ C) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ integratedIntensity Λ (approxProcess hHpred C n) t ω) atTop
      (𝓝 (integratedIntensity Λ H t ω)) := by
  let μt : Measure ℝ≥0 := timeMeasure.restrict (Ioc (0 : ℝ≥0) t)
  have hpred_le := predictable_le_ambient ℱ
  have hg : Measurable (fun s : ℝ≥0 ↦ (s, ω) : ℝ≥0 → ℝ≥0 × Ω) :=
    measurable_id.prodMk measurable_const
  have hHnsec : ∀ n, Measurable (fun s : ℝ≥0 ↦ approxProcess hHpred C n s ω) := by
    intro n
    have hsf : StronglyMeasurable[Prod.instMeasurableSpace]
        ((hHpred.approxBounded C n) : ℝ≥0 × Ω → ℝ) :=
      (SimpleFunc.stronglyMeasurable (hHpred.approxBounded C n)).mono hpred_le
    have hcomp : Measurable (fun s : ℝ≥0 ↦ (hHpred.approxBounded C n) ⟨s, ω⟩) :=
      hsf.measurable.comp hg
    simpa [approxProcess] using hcomp
  have hLamsec : AEStronglyMeasurable (fun s : ℝ≥0 ↦ Λ s ω) μt :=
    (hΛ.integrableOn t ω).aestronglyMeasurable
  have hboundInt : Integrable (fun s : ℝ≥0 ↦ C * Λ s ω) μt := by
    change Integrable (fun s : ℝ≥0 ↦ C * Λ s ω) (timeMeasure.restrict (Ioc (0 : ℝ≥0) t))
    exact (hΛ.integrableOn t ω).const_mul C
  have hbound : ∀ n, ∀ᵐ s ∂μt, ‖approxProcess hHpred C n s ω * Λ s ω‖ ≤ C * Λ s ω := by
    intro n
    refine Eventually.of_forall fun s ↦ ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |approxProcess hHpred C n s ω| ≤ C := by
      have hnorm : ‖(hHpred.approxBounded C n) ⟨s, ω⟩‖ ≤ C :=
        StronglyMeasurable.norm_approxBounded_le hHpred hC n ⟨s, ω⟩
      simpa [approxProcess, Real.norm_eq_abs] using hnorm
    rw [abs_of_nonneg (hΛ.nonneg s ω)]
    exact mul_le_mul_of_nonneg_right h1 (hΛ.nonneg s ω)
  have hlim : ∀ᵐ s ∂μt, Tendsto (fun n ↦ approxProcess hHpred C n s ω * Λ s ω) atTop
      (𝓝 (H s ω * Λ s ω)) := by
    refine Eventually.of_forall fun s ↦ ?_
    have hlimH : Tendsto (fun n ↦ approxProcess hHpred C n s ω) atTop (𝓝 (H s ω)) :=
      tendsto_approxProcess hHpred C hHbound s ω
    exact hlimH.mul tendsto_const_nhds
  have hDCT := tendsto_integral_of_dominated_convergence (μ := μt)
    (F := fun n s ↦ approxProcess hHpred C n s ω * Λ s ω)
    (f := fun s ↦ H s ω * Λ s ω)
    (bound := fun s ↦ C * Λ s ω)
    (fun n ↦ (hHnsec n).aestronglyMeasurable.mul hLamsec) hboundInt hbound hlim
  simpa [μt, integratedIntensity] using hDCT

/-- Uniform bound on the counting integral of a bounded approximation. -/
theorem abs_countingIntegral_approx_le {N : ℝ≥0 → Ω → ℕ} {H : ℝ≥0 → Ω → ℝ}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (hHpred : StronglyMeasurable[ℱ.predictable] (Function.uncurry H)) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |countingIntegral N (approxProcess hHpred C n) t ω| ≤ C * (N t ω : ℝ) := by
  unfold countingIntegral
  calc
    |∑ k ∈ Finset.range (N t ω), approxProcess hHpred C n (jumpTime N k ω) ω|
        ≤ ∑ k ∈ Finset.range (N t ω), |approxProcess hHpred C n (jumpTime N k ω) ω| :=
      Finset.abs_sum_le_sum_abs (fun k ↦ approxProcess hHpred C n (jumpTime N k ω) ω)
        (Finset.range (N t ω))
    _ ≤ ∑ k ∈ Finset.range (N t ω), C := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hnorm : ‖(hHpred.approxBounded C n) ⟨jumpTime N k ω, ω⟩‖ ≤ C :=
        StronglyMeasurable.norm_approxBounded_le hHpred hC n ⟨jumpTime N k ω, ω⟩
      simpa [approxProcess, Real.norm_eq_abs] using hnorm
    _ = C * (N t ω : ℝ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Uniform bound on the compensator of a bounded approximation. -/
theorem abs_integratedIntensity_approx_le {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hHpred : StronglyMeasurable[ℱ.predictable] (Function.uncurry H)) (C : ℝ) (hC : 0 ≤ C)
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |integratedIntensity Λ (approxProcess hHpred C n) t ω| ≤
      C * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω := by
  let μt : Measure ℝ≥0 := timeMeasure.restrict (Ioc (0 : ℝ≥0) t)
  change |∫ s, approxProcess hHpred C n s ω * Λ s ω ∂μt| ≤
    C * ∫ s, (1 : ℝ) * Λ s ω ∂μt
  simp only [one_mul]
  calc
    |∫ s, approxProcess hHpred C n s ω * Λ s ω ∂μt|
        ≤ ∫ s, |approxProcess hHpred C n s ω * Λ s ω| ∂μt :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, C * Λ s ω ∂μt := by
      refine integral_mono_of_nonneg ?_ ?_ ?_
      · refine Eventually.of_forall fun s ↦ abs_nonneg _
      · change Integrable (fun s : ℝ≥0 ↦ C * Λ s ω) (timeMeasure.restrict (Ioc (0 : ℝ≥0) t))
        exact (hΛ.integrableOn t ω).const_mul C
      · refine Eventually.of_forall fun s ↦ ?_
        change |approxProcess hHpred C n s ω * Λ s ω| ≤ C * Λ s ω
        rw [abs_mul]
        have h1 : |approxProcess hHpred C n s ω| ≤ C := by
          have hnorm : ‖(hHpred.approxBounded C n) ⟨s, ω⟩‖ ≤ C :=
            StronglyMeasurable.norm_approxBounded_le hHpred hC n ⟨s, ω⟩
          simpa [approxProcess, Real.norm_eq_abs] using hnorm
        rw [abs_of_nonneg (hΛ.nonneg s ω)]
        exact mul_le_mul_of_nonneg_right h1 (hΛ.nonneg s ω)
    _ = C * ∫ s, Λ s ω ∂μt := by
      rw [integral_const_mul]

/-! ## Direct compensator bounds for bounded predictable processes -/

/-- A uniformly bounded transform has a compensator bounded by the accumulated unit
compensator.  This is the direct (non-approximation) version of
`abs_integratedIntensity_approx_le`. -/
theorem abs_integratedIntensity_le_of_bound
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (hΛ : HasPredictableIntensity μ ℱ N Λ) (C : ℝ) (_hC : 0 ≤ C)
    (hHbound : ∀ t ω, |H t ω| ≤ C) (t : ℝ≥0) (ω : Ω) :
    |integratedIntensity Λ H t ω| ≤
      C * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω := by
  let μt : Measure ℝ≥0 := timeMeasure.restrict (Ioc (0 : ℝ≥0) t)
  change |∫ s, H s ω * Λ s ω ∂μt| ≤ C * ∫ s, (1 : ℝ) * Λ s ω ∂μt
  simp only [one_mul]
  calc
    |∫ s, H s ω * Λ s ω ∂μt|
        ≤ ∫ s, |H s ω * Λ s ω| ∂μt :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, C * Λ s ω ∂μt := by
      refine integral_mono_of_nonneg ?_ ?_ ?_
      · exact Eventually.of_forall fun s ↦ abs_nonneg _
      · change Integrable (fun s : ℝ≥0 ↦ C * Λ s ω)
          (timeMeasure.restrict (Ioc (0 : ℝ≥0) t))
        exact (hΛ.integrableOn t ω).const_mul C
      · refine Eventually.of_forall fun s ↦ ?_
        change |H s ω * Λ s ω| ≤ C * Λ s ω
        rw [abs_mul]
        have h1 : |H s ω| ≤ C := hHbound s ω
        rw [abs_of_nonneg (hΛ.nonneg s ω)]
        exact mul_le_mul_of_nonneg_right h1 (hΛ.nonneg s ω)
    _ = C * ∫ s, Λ s ω ∂μt := by
      rw [integral_const_mul]

/-- A bounded predictable transform has an integrable compensator whenever the accumulated unit
compensator is integrable. -/
theorem integratedIntensity_integrable_of_boundedPredictable
    {N : ℝ≥0 → Ω → ℕ} {Λ H : ℝ≥0 → Ω → ℝ}
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedPredictable ℱ H)
    (hAint : ∀ t, Integrable
      (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ) (t : ℝ≥0) :
    Integrable (fun ω ↦ integratedIntensity Λ H t ω) μ := by
  rcases hH with ⟨hHpred, C, hC, hHbound⟩
  have hprodPred : StronglyMeasurable[ℱ.predictable]
      (Function.uncurry (fun s ω ↦ H s ω * Λ s ω)) := by
    change StronglyMeasurable[ℱ.predictable]
      (Function.uncurry H * Function.uncurry Λ)
    exact hHpred.mul hΛ.predictable
  have hprod : StronglyMeasurable[Prod.instMeasurableSpace]
      (Function.uncurry (fun s ω ↦ H s ω * Λ s ω)) :=
    hprodPred.mono (predictable_le_ambient ℱ)
  let μt : Measure ℝ≥0 := timeMeasure.restrict (Ioc (0 : ℝ≥0) t)
  let _ : SFinite μt := by
    dsimp [μt]
    unfold timeMeasure
    infer_instance
  have hmeasInt : StronglyMeasurable
      (fun ω ↦ integratedIntensity Λ H t ω) := by
    have hmeas' : StronglyMeasurable
        (fun ω ↦ ∫ s, H s ω * Λ s ω ∂μt) := hprod.integral_prod_left'
    simpa [integratedIntensity, μt] using hmeas'
  have hbound : ∀ ω, |integratedIntensity Λ H t ω| ≤
      C * integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω := by
    intro ω
    exact abs_integratedIntensity_le_of_bound hΛ C hC hHbound t ω
  refine Integrable.mono' ((hAint t).const_mul C) hmeasInt.aestronglyMeasurable ?_
  exact Eventually.of_forall fun ω ↦ by
    simpa [Real.norm_eq_abs] using hbound ω

/-! ## The martingale closure theorem -/

/-- Predictable intensity extends from bounded finite-range transforms to bounded predictable
transforms by approximation: the compensated integral of any bounded predictable transform is
again a martingale, provided the accumulated intensity `∫ Λ` is integrable at each time (which
then also makes the counting process integrable through the centred martingale). -/
theorem HasPredictableIntensity.martingale_of_boundedPredictable
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsBoundedPredictable ℱ H)
    (hAint : ∀ t, Integrable (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ) :
    Martingale (compensatedIntegral N Λ H) ℱ μ := by
  rcases hH with ⟨hHpred, C, hC, hHbound⟩
  let A : ℝ≥0 → Ω → ℝ := fun t ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω
  have hHn : ∀ n, IsBoundedSimplePredictable ℱ (approxProcess hHpred C n) :=
    fun n ↦ IsBoundedSimplePredictable.approxProcess_spec hHpred C hC n
  have hCompConv : ∀ t ω,
      Tendsto (fun n ↦ compensatedIntegral N Λ (approxProcess hHpred C n) t ω) atTop
        (𝓝 (compensatedIntegral N Λ H t ω)) := by
    intro t ω
    have h1 := tendsto_countingIntegral_approx (N := N) (H := H) hHpred C hHbound t ω
    have h2 := tendsto_integratedIntensity_approx (μ := μ) (N := N) hΛ hHpred C hC hHbound t ω
    simpa [compensatedIntegral] using h1.sub h2
  have hNAint : ∀ t, Integrable (fun ω ↦ (N t ω : ℝ) + A t ω) μ := by
    intro t
    have hsub : Integrable (fun ω ↦ (N t ω : ℝ) - A t ω) μ :=
      (hΛ.centered_martingale).integrable t
    have htwo : Integrable (fun ω ↦ 2 * A t ω) μ := (hAint t).const_mul 2
    have hfun : (fun ω ↦ ((N t ω : ℝ) - A t ω) + 2 * A t ω) = fun ω ↦ (N t ω : ℝ) + A t ω := by
      ext ω
      ring
    rw [← hfun]
    exact hsub.add htwo
  have hCompBound : ∀ n t ω, |compensatedIntegral N Λ (approxProcess hHpred C n) t ω| ≤
      C * ((N t ω : ℝ) + A t ω) := by
    intro n t ω
    rw [compensatedIntegral]
    calc
      |countingIntegral N (approxProcess hHpred C n) t ω -
          integratedIntensity Λ (approxProcess hHpred C n) t ω|
          ≤ |countingIntegral N (approxProcess hHpred C n) t ω| +
            |integratedIntensity Λ (approxProcess hHpred C n) t ω| := abs_sub _ _
      _ ≤ C * (N t ω : ℝ) + C * A t ω :=
        add_le_add (abs_countingIntegral_approx_le hHpred C hC n t ω)
          (by simpa [A] using abs_integratedIntensity_approx_le hΛ hHpred C hC n t ω)
      _ = C * ((N t ω : ℝ) + A t ω) := by ring
  have hadaptedApprox : ∀ n t,
      StronglyMeasurable[ℱ t] (compensatedIntegral N Λ (approxProcess hHpred C n) t) :=
    fun n t ↦ (hΛ.martingale (hHn n)).stronglyAdapted t
  have hadapted : StronglyAdapted ℱ (compensatedIntegral N Λ H) := by
    intro t
    have hlim : Tendsto (fun n ω ↦ compensatedIntegral N Λ (approxProcess hHpred C n) t ω)
        atTop (𝓝 (fun ω ↦ compensatedIntegral N Λ H t ω)) := by
      rw [tendsto_pi_nhds]
      intro ω
      exact hCompConv t ω
    have hg : @Measurable Ω ℝ (ℱ t) _ (fun ω ↦ compensatedIntegral N Λ H t ω) := by
      let : MeasurableSpace Ω := ℱ t
      have hf : ∀ n, Measurable
          (fun ω : Ω ↦ compensatedIntegral N Λ (approxProcess hHpred C n) t ω) := by
        intro n
        exact (hadaptedApprox n t).measurable
      exact measurable_of_tendsto_metrizable hf hlim
    have hsm : @StronglyMeasurable Ω ℝ _ (ℱ t) (fun ω ↦ compensatedIntegral N Λ H t ω) := by
      let : MeasurableSpace Ω := ℱ t
      exact hg.stronglyMeasurable
    simpa using hsm
  have hIntLimit : ∀ t, Integrable (fun ω ↦ compensatedIntegral N Λ H t ω) μ := by
    intro t
    have hbnd : ∀ ω, |compensatedIntegral N Λ H t ω| ≤ C * ((N t ω : ℝ) + A t ω) := by
      intro ω
      have habs : Tendsto (fun n ↦ |compensatedIntegral N Λ (approxProcess hHpred C n) t ω|)
          atTop (𝓝 (|compensatedIntegral N Λ H t ω|)) :=
        (continuous_abs.tendsto (compensatedIntegral N Λ H t ω)).comp (hCompConv t ω)
      exact le_of_tendsto habs (Eventually.of_forall fun n ↦ hCompBound n t ω)
    have hmeas : AEStronglyMeasurable (fun ω ↦ compensatedIntegral N Λ H t ω) μ := by
      have hsm : StronglyMeasurable (fun ω ↦ compensatedIntegral N Λ H t ω) :=
        (hadapted t).mono (ℱ.le t)
      exact hsm.measurable.aestronglyMeasurable
    refine Integrable.mono' ((hNAint t).const_mul C) hmeas ?_
    refine Eventually.of_forall fun ω ↦ ?_
    simpa [Real.norm_eq_abs] using hbnd ω
  refine ⟨hadapted, ?_⟩
  intro s t hst
  have hfg : ∀ n, μ[fun ω ↦ compensatedIntegral N Λ (approxProcess hHpred C n) t ω | ℱ s] =ᵐ[μ]
      μ[fun ω ↦ compensatedIntegral N Λ (approxProcess hHpred C n) s ω | ℱ s] := by
    intro n
    have hM := hΛ.martingale (hHn n)
    have hce : μ[compensatedIntegral N Λ (approxProcess hHpred C n) t | ℱ s] =ᵐ[μ]
        compensatedIntegral N Λ (approxProcess hHpred C n) s := hM.condExp_ae_eq hst
    have hgsce : μ[compensatedIntegral N Λ (approxProcess hHpred C n) s | ℱ s] =ᵐ[μ]
        compensatedIntegral N Λ (approxProcess hHpred C n) s := by
      rw [condExp_of_stronglyMeasurable (m := ℱ s) (ℱ.le s) (hM.stronglyAdapted s)
        (hM.integrable s)]
    simpa using (hce.trans hgsce.symm)
  have hcond := tendsto_condExp_unique (m := ℱ s)
    (fs := fun n ω ↦ compensatedIntegral N Λ (approxProcess hHpred C n) t ω)
    (gs := fun n ω ↦ compensatedIntegral N Λ (approxProcess hHpred C n) s ω)
    (f := fun ω ↦ compensatedIntegral N Λ H t ω)
    (g := fun ω ↦ compensatedIntegral N Λ H s ω)
    (hfs_int := fun n ↦ (hΛ.martingale (hHn n)).integrable t)
    (hgs_int := fun n ↦ (hΛ.martingale (hHn n)).integrable s)
    (hfs := Eventually.of_forall fun ω ↦ hCompConv t ω)
    (hgs := Eventually.of_forall fun ω ↦ hCompConv s ω)
    (bound_fs := fun ω ↦ C * ((N t ω : ℝ) + A t ω))
    (h_int_bound_fs := (hNAint t).const_mul C)
    (bound_gs := fun ω ↦ C * ((N s ω : ℝ) + A s ω))
    (h_int_bound_gs := (hNAint s).const_mul C)
    (hfs_bound := fun n ↦ Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using (hCompBound n t ω))
    (hgs_bound := fun n ↦ Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using (hCompBound n s ω))
    (hfg := hfg)
  have hgce : μ[fun ω ↦ compensatedIntegral N Λ H s ω | ℱ s] =ᵐ[μ]
      compensatedIntegral N Λ H s := by
    rw [condExp_of_stronglyMeasurable (m := ℱ s) (ℱ.le s) (hadapted s) (hIntLimit s)]
  simpa using (hcond.trans hgce)

/-! A finite base measure supplies the sigma-finite filtration hypothesis used by the closure
theorem.  Keeping this wrapper separate makes the measure assumption visible at call sites. -/

theorem HasPredictableIntensity.martingale_of_boundedPredictable_of_isFiniteMeasure
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [IsFiniteMeasure μ] {N : ℝ≥0 → Ω → ℕ} {Λ : ℝ≥0 → Ω → ℝ}
    (hΛ : HasPredictableIntensity μ ℱ N Λ) {H : ℝ≥0 → Ω → ℝ}
    (hH : IsBoundedPredictable ℱ H)
    (hAint : ∀ t, Integrable (fun ω ↦ integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) μ) :
    Martingale (compensatedIntegral N Λ H) ℱ μ := by
  let _ : SigmaFiniteFiltration μ ℱ := by
    constructor
    intro i
    infer_instance
  exact hΛ.martingale_of_boundedPredictable hH hAint

end OTSelector.CountingProcess
