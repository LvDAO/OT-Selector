import OTSelector.Probability.CountingProcess.Core

/-!
# Exponential algebra for counting paths

This file separates two facts that require different amounts of stochastic infrastructure.

* Finite-jump exponential products and their one-jump recursions are pathwise identities.
* For a bounded simple predictable exponent, the transformed driver `exp θ - 1` remains in the
  class covered by `HasPredictableIntensity`, so its compensated integral is a martingale.

The full continuous-time counting exponential is defined and its pathwise algebra is proved here.
Showing that this exponential is itself a martingale requires closure under random predictable
integrands that need not have finite range, together with localization and uniform-integrability
arguments; those results do not follow directly from the finite-range transform interface in
`Core`.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Finite-jump products -/

/-- The product of the jump multipliers `1 + H` over all jumps attained by time `t`. -/
noncomputable def jumpMultiplierProduct (N : ℝ≥0 → Ω → ℕ) (H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range (N t ω), (1 + H (jumpTime N k ω) ω)

omit [MeasurableSpace Ω] in
/-- With no attained jumps, the multiplier product is one. -/
@[simp]
theorem jumpMultiplierProduct_of_count_eq_zero (N : ℝ≥0 → Ω → ℕ) (H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (hN : N t ω = 0) :
    jumpMultiplierProduct N H t ω = 1 := by
  simp [jumpMultiplierProduct, hN]

omit [MeasurableSpace Ω] in
/-- Adding one attained jump appends its multiplier to the finite product. -/
theorem jumpMultiplierProduct_of_count_eq_succ (N : ℝ≥0 → Ω → ℕ) (H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (n : ℕ) (hN : N t ω = n + 1) :
    jumpMultiplierProduct N H t ω =
      (∏ k ∈ Finset.range n, (1 + H (jumpTime N k ω) ω)) *
        (1 + H (jumpTime N n ω) ω) := by
  simp [jumpMultiplierProduct, hN, Finset.prod_range_succ]

omit [MeasurableSpace Ω] in
/-- The finite multiplier product is nonnegative when every attained multiplier is nonnegative. -/
theorem jumpMultiplierProduct_nonneg (N : ℝ≥0 → Ω → ℕ) (H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (hH : ∀ k < N t ω, -1 ≤ H (jumpTime N k ω) ω) :
    0 ≤ jumpMultiplierProduct N H t ω := by
  apply Finset.prod_nonneg
  intro k hk
  linarith [hH k (Finset.mem_range.mp hk)]

omit [MeasurableSpace Ω] in
/-- The finite multiplier product is positive when every attained multiplier is positive. -/
theorem jumpMultiplierProduct_pos (N : ℝ≥0 → Ω → ℕ) (H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (hH : ∀ k < N t ω, -1 < H (jumpTime N k ω) ω) :
    0 < jumpMultiplierProduct N H t ω := by
  apply Finset.prod_pos
  intro k hk
  linarith [hH k (Finset.mem_range.mp hk)]

/-! ## The exponential driver stays in the simple predictable class -/

/-- Pointwise exponential tilt of a real process. -/
noncomputable def expSubOne (θ : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ Real.exp (θ t ω) - 1

/-- A bounded finite-valued predictable exponent remains bounded finite-valued and predictable
after applying `x ↦ exp x - 1`. -/
theorem IsBoundedSimplePredictable.expSubOne_process
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {θ : ℝ≥0 → Ω → ℝ}
    (hθ : IsBoundedSimplePredictable ℱ θ) :
    IsBoundedSimplePredictable ℱ (expSubOne θ) := by
  obtain ⟨hθpred, hθfinite, C, hC, hθbound⟩ := hθ
  refine ⟨?_, ?_, Real.exp C + 1, by positivity, ?_⟩
  · change StronglyMeasurable[ℱ.predictable]
      (fun z : ℝ≥0 × Ω ↦ Real.exp (θ z.1 z.2) - 1)
    exact (Real.continuous_exp.sub continuous_const).comp_stronglyMeasurable hθpred
  · have hrange :
        Set.range (Function.uncurry (expSubOne θ)) =
          (fun x : ℝ ↦ Real.exp x - 1) '' Set.range (Function.uncurry θ) := by
      rw [← Set.range_comp']
      rfl
    rw [hrange]
    exact hθfinite.image _
  · intro t ω
    calc
      |expSubOne θ t ω| ≤ |Real.exp (θ t ω)| + |(1 : ℝ)| := abs_sub _ _
      _ = Real.exp (θ t ω) + 1 := by rw [Real.abs_exp, abs_one]
      _ ≤ Real.exp C + 1 := by
        gcongr
        exact (le_abs_self (θ t ω)).trans (hθbound t ω)

/-- The product of two bounded finite-valued predictable real processes remains in the same
class.  This is the exact algebraic closure needed for a product-weighted exponential driver when
the proposed weight is itself bounded and finite-valued. -/
theorem IsBoundedSimplePredictable.mul_process
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {F G : ℝ≥0 → Ω → ℝ}
    (hF : IsBoundedSimplePredictable ℱ F) (hG : IsBoundedSimplePredictable ℱ G) :
    IsBoundedSimplePredictable ℱ (fun t ω ↦ F t ω * G t ω) := by
  obtain ⟨hFpred, hFfinite, C, hC, hFbound⟩ := hF
  obtain ⟨hGpred, hGfinite, D, hD, hGbound⟩ := hG
  refine ⟨hFpred.mul hGpred, ?_, C * D, mul_nonneg hC hD, ?_⟩
  · apply ((hFfinite.prod hGfinite).image fun z : ℝ × ℝ ↦ z.1 * z.2).subset
    rintro x ⟨⟨t, ω⟩, rfl⟩
    exact ⟨(F t ω, G t ω), ⟨⟨⟨t, ω⟩, rfl⟩, ⟨⟨t, ω⟩, rfl⟩⟩, rfl⟩
  · intro t ω
    rw [abs_mul]
    exact mul_le_mul (hFbound t ω) (hGbound t ω) (abs_nonneg _) hC

/-- A bounded finite-valued predictable left weight times `exp θ - 1` is a legal transform for
`HasPredictableIntensity`. -/
theorem IsBoundedSimplePredictable.mul_expSubOne
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {L θ : ℝ≥0 → Ω → ℝ}
    (hL : IsBoundedSimplePredictable ℱ L) (hθ : IsBoundedSimplePredictable ℱ θ) :
    IsBoundedSimplePredictable ℱ (fun t ω ↦ L t ω * expSubOne θ t ω) :=
  hL.mul_process hθ.expSubOne_process

/-- The compensated `exp θ - 1` driver appearing in the stochastic-exponential equation. -/
noncomputable def exponentialDriver (N : ℝ≥0 → Ω → ℕ) (Λ θ : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  compensatedIntegral N Λ (expSubOne θ) t ω

/-- Predictable intensity makes the bounded-simple exponential driver a martingale. -/
theorem HasPredictableIntensity.exponentialDriver_martingale {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ θ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hθ : IsBoundedSimplePredictable ℱ θ) :
    Martingale (exponentialDriver N Λ θ) ℱ μ :=
  hΛ.martingale hθ.expSubOne_process

/-- Conditional mean-zero increments of the bounded-simple exponential driver. -/
theorem HasPredictableIntensity.condExp_exponentialDriver_increment {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ θ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hθ : IsBoundedSimplePredictable ℱ θ) {s t : ℝ≥0} (hst : s ≤ t) :
    μ[(fun ω ↦ exponentialDriver N Λ θ t ω - exponentialDriver N Λ θ s ω) | ℱ s] =ᵐ[μ]
      0 := by
  have hM := hΛ.exponentialDriver_martingale hθ
  calc
    μ[(fun ω ↦ exponentialDriver N Λ θ t ω - exponentialDriver N Λ θ s ω) | ℱ s] =ᵐ[μ]
        μ[exponentialDriver N Λ θ t | ℱ s] - μ[exponentialDriver N Λ θ s | ℱ s] :=
      condExp_sub (hM.integrable t) (hM.integrable s) (ℱ s)
    _ =ᵐ[μ] exponentialDriver N Λ θ s - exponentialDriver N Λ θ s :=
      (hM.condExp_ae_eq hst).sub (hM.condExp_ae_eq le_rfl)
    _ = 0 := by simp

/-- The compensated exponential driver multiplied by a proposed predictable left weight. -/
noncomputable def weightedExponentialDriver (N : ℝ≥0 → Ω → ℕ)
    (Λ L θ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  compensatedIntegral N Λ (fun s ω' ↦ L s ω' * expSubOne θ s ω') t ω

/-- A bounded finite-valued predictable left weight gives a genuine martingale weighted driver.
This closes the stochastic-integral step exactly as far as the transform class in `Core` allows. -/
theorem HasPredictableIntensity.weightedExponentialDriver_martingale {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ L θ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hL : IsBoundedSimplePredictable ℱ L) (hθ : IsBoundedSimplePredictable ℱ θ) :
    Martingale (weightedExponentialDriver N Λ L θ) ℱ μ :=
  hΛ.martingale (hL.mul_expSubOne hθ)

/-- Conditional mean-zero increments of a legal bounded-simple product-weighted driver. -/
theorem HasPredictableIntensity.condExp_weightedExponentialDriver_increment {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ L θ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hL : IsBoundedSimplePredictable ℱ L) (hθ : IsBoundedSimplePredictable ℱ θ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    μ[(fun ω ↦ weightedExponentialDriver N Λ L θ t ω -
      weightedExponentialDriver N Λ L θ s ω) | ℱ s] =ᵐ[μ] 0 := by
  have hM := hΛ.weightedExponentialDriver_martingale hL hθ
  calc
    μ[(fun ω ↦ weightedExponentialDriver N Λ L θ t ω -
      weightedExponentialDriver N Λ L θ s ω) | ℱ s] =ᵐ[μ]
        μ[weightedExponentialDriver N Λ L θ t | ℱ s] -
          μ[weightedExponentialDriver N Λ L θ s | ℱ s] :=
      condExp_sub (hM.integrable t) (hM.integrable s) (ℱ s)
    _ =ᵐ[μ] weightedExponentialDriver N Λ L θ s -
        weightedExponentialDriver N Λ L θ s :=
      (hM.condExp_ae_eq hst).sub (hM.condExp_ae_eq le_rfl)
    _ = 0 := by simp

/-! ## Pathwise counting exponential -/

/-- Product of the exponential jump factors attained by time `t`. -/
noncomputable def jumpExponentialProduct (N : ℝ≥0 → Ω → ℕ) (θ : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range (N t ω), Real.exp (θ (jumpTime N k ω) ω)

omit [MeasurableSpace Ω] in
/-- The jump exponential product is the exponential of the pathwise counting integral. -/
theorem jumpExponentialProduct_eq_exp_countingIntegral (N : ℝ≥0 → Ω → ℕ)
    (θ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    jumpExponentialProduct N θ t ω = Real.exp (countingIntegral N θ t ω) := by
  rw [jumpExponentialProduct, countingIntegral, Real.exp_sum]

omit [MeasurableSpace Ω] in
/-- Exponential jump factors are the special multipliers obtained from `exp θ - 1`. -/
theorem jumpMultiplierProduct_expSubOne (N : ℝ≥0 → Ω → ℕ) (θ : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    jumpMultiplierProduct N (expSubOne θ) t ω = jumpExponentialProduct N θ t ω := by
  simp [jumpMultiplierProduct, jumpExponentialProduct, expSubOne]

omit [MeasurableSpace Ω] in
/-- One additional attained jump appends one exponential factor. -/
theorem jumpExponentialProduct_of_count_eq_succ (N : ℝ≥0 → Ω → ℕ) (θ : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) (n : ℕ) (hN : N t ω = n + 1) :
    jumpExponentialProduct N θ t ω =
      (∏ k ∈ Finset.range n, Real.exp (θ (jumpTime N k ω) ω)) *
        Real.exp (θ (jumpTime N n ω) ω) := by
  simp [jumpExponentialProduct, hN, Finset.prod_range_succ]

/-- The finite-jump counting exponential with compensator `∫ (exp θ - 1) Λ`. -/
noncomputable def countingExponential (N : ℝ≥0 → Ω → ℕ) (Λ θ : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-integratedIntensity Λ (expSubOne θ) t ω) * jumpExponentialProduct N θ t ω

omit [MeasurableSpace Ω] in
/-- Additive-exponent form of the finite-jump counting exponential. -/
theorem countingExponential_eq_exp (N : ℝ≥0 → Ω → ℕ) (Λ θ : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    countingExponential N Λ θ t ω =
      Real.exp (countingIntegral N θ t ω - integratedIntensity Λ (expSubOne θ) t ω) := by
  rw [countingExponential, jumpExponentialProduct_eq_exp_countingIntegral, ← Real.exp_add]
  congr 1
  ring

omit [MeasurableSpace Ω] in
/-- Every finite-jump counting exponential is strictly positive. -/
theorem countingExponential_pos (N : ℝ≥0 → Ω → ℕ) (Λ θ : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : 0 < countingExponential N Λ θ t ω := by
  rw [countingExponential_eq_exp]
  exact Real.exp_pos _

/-- A simple counting process has counting exponential one at time zero. -/
@[simp]
theorem IsSimpleCountingProcess.countingExponential_zero
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    (hN : IsSimpleCountingProcess ℱ N) (Λ θ : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    countingExponential N Λ θ 0 ω = 1 := by
  simp [countingExponential, jumpExponentialProduct, hN.zero, integratedIntensity]

omit [MeasurableSpace Ω] in
/-- Across an interval containing exactly one new attained jump, the counting exponential is
multiplied by the jump factor and by the compensator decrement. -/
theorem countingExponential_oneJump (N : ℝ≥0 → Ω → ℕ) (Λ θ : ℝ≥0 → Ω → ℝ)
    {s t : ℝ≥0} (ω : Ω) (n : ℕ) (hNs : N s ω = n) (hNt : N t ω = n + 1) :
    countingExponential N Λ θ t ω = countingExponential N Λ θ s ω *
      Real.exp (θ (jumpTime N n ω) ω -
        (integratedIntensity Λ (expSubOne θ) t ω -
          integratedIntensity Λ (expSubOne θ) s ω)) := by
  rw [countingExponential, countingExponential, jumpExponentialProduct,
    jumpExponentialProduct, hNs, hNt, Finset.prod_range_succ]
  have hexp :
      Real.exp (-integratedIntensity Λ (expSubOne θ) t ω) *
          Real.exp (θ (jumpTime N n ω) ω) =
        Real.exp (-integratedIntensity Λ (expSubOne θ) s ω) *
          Real.exp (θ (jumpTime N n ω) ω -
            (integratedIntensity Λ (expSubOne θ) t ω -
              integratedIntensity Λ (expSubOne θ) s ω)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-integratedIntensity Λ (expSubOne θ) t ω) *
        ((∏ k ∈ Finset.range n, Real.exp (θ (jumpTime N k ω) ω)) *
          Real.exp (θ (jumpTime N n ω) ω)) =
        (∏ k ∈ Finset.range n, Real.exp (θ (jumpTime N k ω) ω)) *
          (Real.exp (-integratedIntensity Λ (expSubOne θ) t ω) *
            Real.exp (θ (jumpTime N n ω) ω)) := by ring
    _ = (∏ k ∈ Finset.range n, Real.exp (θ (jumpTime N k ω) ω)) *
          (Real.exp (-integratedIntensity Λ (expSubOne θ) s ω) *
            Real.exp (θ (jumpTime N n ω) ω -
              (integratedIntensity Λ (expSubOne θ) t ω -
                integratedIntensity Λ (expSubOne θ) s ω))) := by rw [hexp]
    _ = (Real.exp (-integratedIntensity Λ (expSubOne θ) s ω) *
          ∏ k ∈ Finset.range n, Real.exp (θ (jumpTime N k ω) ω)) *
        Real.exp (θ (jumpTime N n ω) ω -
          (integratedIntensity Λ (expSubOne θ) t ω -
            integratedIntensity Λ (expSubOne θ) s ω)) := by ring

end OTSelector.CountingProcess
