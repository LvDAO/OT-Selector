import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Probability.Martingale.OptionalSampling

/-!
# Counting processes with predictable intensity

This file defines the pathwise counting integral and predictable-intensity martingale property.
The intensity condition is stated for every bounded finite-valued
predictable transform.  In particular, it is stronger than merely assuming that `N - A` is a
martingale and is the form needed to construct exponential counting-process martingales.

The stochastic integral against a counting path is defined pathwise by summing the integrand at
the generalized jump times.  This avoids introducing a general random-measure integral before it
is needed elsewhere in the project.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Paths and their jump integrals -/

/-- The generalized time of jump number `k + 1` of a natural-valued counting path. -/
noncomputable def jumpTime (N : ℝ≥0 → Ω → ℕ) (k : ℕ) (ω : Ω) : ℝ≥0 :=
  sInf {t | k < N t ω}

/-- The pathwise integral of `H` against `N` up to time `t`, obtained by summing `H` over the
generalized jump times of the first `N t` jumps. -/
noncomputable def countingIntegral (N : ℝ≥0 → Ω → ℕ) (H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (N t ω), H (jumpTime N k ω) ω

/-- A natural-valued process is a simple counting process when it starts at zero, is adapted and
has nondecreasing right-continuous paths, and distinct attained jump labels have distinct jump
times.  The last clause rules out simultaneous multiple jumps. -/
def IsSimpleCountingProcess (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (N : ℝ≥0 → Ω → ℕ) : Prop :=
  N 0 = 0 ∧
    StronglyAdapted ℱ (fun t ω ↦ (N t ω : ℝ)) ∧
    (∀ ω, Monotone fun t ↦ N t ω) ∧
    (∀ ω t, ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t) ∧
    ∀ ω t, Set.InjOn (fun k ↦ jumpTime N k ω) (Iio (N t ω))

/-- A simple counting process starts at zero. -/
theorem IsSimpleCountingProcess.zero {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} (hN : IsSimpleCountingProcess ℱ N) : N 0 = 0 :=
  hN.1

/-- A simple counting process is adapted after casting its counts to real numbers. -/
theorem IsSimpleCountingProcess.stronglyAdapted
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    (hN : IsSimpleCountingProcess ℱ N) :
    StronglyAdapted ℱ (fun t ω ↦ (N t ω : ℝ)) :=
  hN.2.1

/-- Every path of a simple counting process is nondecreasing. -/
theorem IsSimpleCountingProcess.monotone {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {N : ℝ≥0 → Ω → ℕ} (hN : IsSimpleCountingProcess ℱ N) (ω : Ω) :
    Monotone fun t ↦ N t ω :=
  hN.2.2.1 ω

/-- Every path of a simple counting process is right-continuous. -/
theorem IsSimpleCountingProcess.rightContinuous
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    (hN : IsSimpleCountingProcess ℱ N) (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ (N s ω : ℝ)) (Ici t) t :=
  hN.2.2.2.1 ω t

/-- Attained jump labels of a simple counting process occur at distinct times. -/
theorem IsSimpleCountingProcess.jumpTime_injOn
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    (hN : IsSimpleCountingProcess ℱ N) (ω : Ω) (t : ℝ≥0) :
    Set.InjOn (fun k ↦ jumpTime N k ω) (Iio (N t ω)) :=
  hN.2.2.2.2 ω t

/-! ## Predictable transforms and intensity -/

/-- Lebesgue time measure on `ℝ≥0`, obtained by restricting real Lebesgue measure to the
nonnegative half-line and mapping along `Real.toNNReal`. -/
noncomputable def timeMeasure : Measure ℝ≥0 :=
  Measure.map Real.toNNReal (volume.restrict (Ici (0 : ℝ)))

/-- A bounded simple predictable real process: it is predictable, has finite range, and comes
with a deterministic uniform bound.  This is an ordinary proposition rather than a witness
bundle; callers pass the bound only when proving the proposition. -/
def IsBoundedSimplePredictable (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (H : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable ℱ H ∧
    (Set.range (Function.uncurry H)).Finite ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ω, |H t ω| ≤ C

/-- The accumulated Lebesgue compensator of a predictable transform `H` at intensity `Λ`. -/
noncomputable def integratedIntensity (Λ H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Ioc (0 : ℝ≥0) t, H s ω * Λ s ω ∂timeMeasure

/-- The compensated pathwise counting integral `∫ H dN - ∫ H Λ ds`. -/
noncomputable def compensatedIntegral (N : ℝ≥0 → Ω → ℕ) (Λ H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  countingIntegral N H t ω - integratedIntensity Λ H t ω

/-- `Λ` is a predictable intensity for `N` when it is nonnegative, locally integrable along
every path, and every bounded simple predictable transform has martingale compensated integral.

The universal transform clause is the operational compensator identity used by later exponential
and stopped-occupation arguments; it deliberately does not package any tail estimate. -/
def HasPredictableIntensity (μ : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (N : ℝ≥0 → Ω → ℕ) (Λ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable ℱ Λ ∧
    (∀ t ω, 0 ≤ Λ t ω) ∧
    (∀ t ω, IntegrableOn (fun s ↦ Λ s ω) (Ioc (0 : ℝ≥0) t) timeMeasure) ∧
    ∀ H, IsBoundedSimplePredictable ℱ H →
      Martingale (compensatedIntegral N Λ H) ℱ μ

/-- An intensity is predictable. -/
theorem HasPredictableIntensity.predictable {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ) :
    IsStronglyPredictable ℱ Λ :=
  hΛ.1

/-- An intensity is pointwise nonnegative. -/
theorem HasPredictableIntensity.nonneg {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ) (t : ℝ≥0) (ω : Ω) :
    0 ≤ Λ t ω :=
  hΛ.2.1 t ω

/-- An intensity is pathwise integrable on every bounded time interval. -/
theorem HasPredictableIntensity.integrableOn {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ) (t : ℝ≥0) (ω : Ω) :
    IntegrableOn (fun s ↦ Λ s ω) (Ioc (0 : ℝ≥0) t) timeMeasure :=
  hΛ.2.2.1 t ω

/-- The compensated integral of every bounded simple predictable transform is a martingale. -/
theorem HasPredictableIntensity.martingale {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsBoundedSimplePredictable ℱ H) :
    Martingale (compensatedIntegral N Λ H) ℱ μ :=
  hΛ.2.2.2 H hH

/-- The constant-one process is a bounded simple predictable transform. -/
theorem boundedSimplePredictable_one (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) :
    IsBoundedSimplePredictable ℱ (fun _ _ ↦ (1 : ℝ)) := by
  refine ⟨?_, Set.finite_range_const, 1, by positivity, ?_⟩
  · change StronglyMeasurable[ℱ.predictable] (fun _ : ℝ≥0 × Ω ↦ (1 : ℝ))
    exact stronglyMeasurable_const
  · simp

omit [MeasurableSpace Ω] in
/-- Integrating the constant-one transform against a counting path returns the count. -/
@[simp]
theorem countingIntegral_one (N : ℝ≥0 → Ω → ℕ) (t : ℝ≥0) (ω : Ω) :
    countingIntegral N (fun _ _ ↦ (1 : ℝ)) t ω = N t ω := by
  simp [countingIntegral]

/-- The ordinary compensated count `N - ∫ Λ` is a martingale.  This is a consequence of the
strong transform formulation of predictable intensity, not its definition. -/
theorem HasPredictableIntensity.centered_martingale {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ) :
    Martingale
      (fun t ω ↦ (N t ω : ℝ) - integratedIntensity Λ (fun _ _ ↦ (1 : ℝ)) t ω) ℱ μ := by
  have h := hΛ.martingale (boundedSimplePredictable_one ℱ)
  convert h using 1
  funext t ω
  rw [compensatedIntegral, countingIntegral_one]

/-- Conditional compensator identity for a bounded simple predictable transform. -/
theorem HasPredictableIntensity.condExp_compensatedIntegral {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ H : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedSimplePredictable ℱ H) {s t : ℝ≥0} (hst : s ≤ t) :
    μ[compensatedIntegral N Λ H t | ℱ s] =ᵐ[μ] compensatedIntegral N Λ H s :=
  (hΛ.martingale hH).condExp_ae_eq hst

/-- Every bounded simple predictable compensated transform is integrable at a fixed time. -/
theorem HasPredictableIntensity.compensatedIntegral_integrable {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ H : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (hH : IsBoundedSimplePredictable ℱ H) (t : ℝ≥0) :
    Integrable (compensatedIntegral N Λ H t) μ :=
  (hΛ.martingale hH).integrable t

/-! ## Stopped transforms -/

/-- Mask an integrand to the stochastic interval strictly before a stopping time. -/
noncomputable def beforeStopping (τ : Ω → WithTop ℝ≥0)
    (H : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω ↦ if (t : WithTop ℝ≥0) < τ ω then H t ω else 0

/-- Stopping preserves the finite-range and uniform-bound parts of a bounded simple predictable
transform.  Thus, once predictability of the stopped mask has been established, the whole stopped
transform is bounded simple predictable. -/
theorem IsBoundedSimplePredictable.beforeStopping
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsBoundedSimplePredictable ℱ H) (τ : Ω → WithTop ℝ≥0)
    (hPredictable : IsStronglyPredictable ℱ (beforeStopping τ H)) :
    IsBoundedSimplePredictable ℱ (beforeStopping τ H) := by
  obtain ⟨_, hHfinite, C, hC, hHbound⟩ := hH
  refine ⟨hPredictable, (Set.finite_singleton 0).union hHfinite |>.subset ?_, C, hC, ?_⟩
  · rintro y ⟨⟨t, ω⟩, rfl⟩
    by_cases ht : (t : WithTop ℝ≥0) < τ ω
    · refine Or.inr ⟨(t, ω), ?_⟩
      change H t ω = if (t : WithTop ℝ≥0) < τ ω then H t ω else 0
      rw [ite_eq_left ht]
    · refine Or.inl ?_
      change (if (t : WithTop ℝ≥0) < τ ω then H t ω else 0) = 0
      rw [ite_eq_right ht]
  · intro t ω
    by_cases ht : (t : WithTop ℝ≥0) < τ ω
    · change |if (t : WithTop ℝ≥0) < τ ω then H t ω else 0| ≤ C
      rw [ite_eq_left ht]
      exact hHbound t ω
    · change |if (t : WithTop ℝ≥0) < τ ω then H t ω else 0| ≤ C
      rw [ite_eq_right ht, abs_zero]
      exact hC

/-- Whenever the stopped mask of a bounded simple predictable transform is predictable, its
compensated stopped transform is a martingale.  Predictability is kept explicit because a general
continuous-time stopping time need not itself be predictable. -/
theorem HasPredictableIntensity.beforeStopping_martingale {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ H : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (τ : Ω → WithTop ℝ≥0) (hH : IsBoundedSimplePredictable ℱ H)
    (hPredictable : IsStronglyPredictable ℱ (beforeStopping τ H)) :
    Martingale (compensatedIntegral N Λ (beforeStopping τ H)) ℱ μ :=
  hΛ.martingale (hH.beforeStopping τ hPredictable)

/-- Conditional compensator identity on a predictable stopped stochastic interval. -/
theorem HasPredictableIntensity.condExp_beforeStopping {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {N : ℝ≥0 → Ω → ℕ}
    {Λ H : ℝ≥0 → Ω → ℝ} (hΛ : HasPredictableIntensity μ ℱ N Λ)
    (τ : Ω → WithTop ℝ≥0) (hH : IsBoundedSimplePredictable ℱ H)
    (hPredictable : IsStronglyPredictable ℱ (beforeStopping τ H))
    {s t : ℝ≥0} (hst : s ≤ t) :
    μ[compensatedIntegral N Λ (beforeStopping τ H) t | ℱ s] =ᵐ[μ]
      compensatedIntegral N Λ (beforeStopping τ H) s :=
  (hΛ.beforeStopping_martingale τ hH hPredictable).condExp_ae_eq hst

end OTSelector.CountingProcess
