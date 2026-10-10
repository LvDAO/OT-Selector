import OTSelector.Probability.CountingProcess.Core

/-!
# Rectangle extension: the conditional-expectation core

This module records the part of the rectangle-to-predictable-transform argument which is
available directly from the `mathlib` conditional-expectation API.  The predictable sigma-algebra
contains the genuine rectangles `(s,t] × B`, with `B ∈ ℱ s`; the first lemma below exposes these
rectangles with their correct predictable measurability.

The main theorem is deliberately a *set-integral* theorem.  It does not introduce a packaged
assumption and it does not turn a universal martingale assertion into an assumption.  Once rectangle
identities have been extended to all `ℱ i`-measurable sections, the conditional-expectation
uniqueness theorem `ae_eq_condExp_of_forall_setIntegral_eq` turns those identities into the
martingale property.  A separate monotone-class argument is still needed to derive the section
identities from rectangle identities for a general pathwise random measure; this file states that
remaining boundary explicitly rather than hiding it in an interface.
-/

open Filter Set
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Genuine predictable rectangles -/

/-- A predictable time-space rectangle.  The convention is the right-closed interval `(s,t]`.
The section `B` is intended to be measurable at the left endpoint `s`. -/
def predictableRectangle (s t : ℝ≥0) (B : Set Ω) : Set (ℝ≥0 × Ω) :=
  Set.Ioc s t ×ˢ B

/-- A genuine predictable rectangle is measurable for the predictable sigma-algebra. -/
theorem measurableSet_predictableRectangle
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {s t : ℝ≥0} {B : Set Ω}
    (hB : MeasurableSet[ℱ s] B) :
    MeasurableSet[ℱ.predictable] (predictableRectangle s t B) := by
  exact measurableSet_predictable_Ioc_prod s t hB

/-- The bounded indicator transform associated with a predictable rectangle. -/
noncomputable def predictableRectangleIndicator (s t : ℝ≥0) (B : Set Ω) : ℝ≥0 → Ω → ℝ :=
  fun u ω ↦ (predictableRectangle s t B).indicator (fun _ ↦ (1 : ℝ)) (u, ω)

/-- The indicator of a genuine predictable rectangle is a strongly predictable transform. -/
theorem predictableRectangleIndicator_predictable
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {s t : ℝ≥0} {B : Set Ω}
    (hB : MeasurableSet[ℱ s] B) :
    IsStronglyPredictable ℱ (predictableRectangleIndicator s t B) := by
  change StronglyMeasurable[ℱ.predictable]
    ((predictableRectangle s t B).indicator (fun _ ↦ (1 : ℝ)))
  exact stronglyMeasurable_const.indicator (measurableSet_predictableRectangle hB)

/-- The rectangle indicator has finite range and is uniformly bounded by one. -/
theorem predictableRectangleIndicator_boundedSimple
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {s t : ℝ≥0} {B : Set Ω}
    (hB : MeasurableSet[ℱ s] B) :
    IsBoundedSimplePredictable ℱ (predictableRectangleIndicator s t B) := by
  refine ⟨predictableRectangleIndicator_predictable hB, ?_, 1, by positivity, ?_⟩
  · have hfin : ({0, 1} : Set ℝ).Finite := (Set.finite_singleton (1 : ℝ)).insert 0
    apply hfin.subset
    rintro y ⟨⟨u, ω⟩, rfl⟩
    by_cases h : (u, ω) ∈ predictableRectangle s t B
    · simp [predictableRectangleIndicator, h]
    · simp [predictableRectangleIndicator, h]
  · intro u ω
    by_cases h : (u, ω) ∈ predictableRectangle s t B
    · simp [predictableRectangleIndicator, h]
    · simp [predictableRectangleIndicator, h]

/-! ## Conditional-expectation uniqueness for adapted processes -/

/--
Set-integral extension lemma.

Suppose `M` is strongly adapted and integrable, and for every deterministic pair `i ≤ j` its
increment has zero integral on every finite `ℱ i`-measurable event.  Then `M` is a martingale.

This is the exact conditional-expectation uniqueness layer needed after a genuine rectangle (or
random-measure) argument has produced section identities.  The assumptions are low-level facts:
adaptedness, integrability, and set-integral equalities.  In particular, no packaged assumption or
universal martingale property is assumed.
-/
theorem martingale_of_all_setIntegral_eq
    {μ : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {M : ℝ≥0 → Ω → ℝ}
    (hAdapted : StronglyAdapted ℱ M)
    (hIntegrable : ∀ i, Integrable (M i) μ)
    (hSetIntegral : ∀ i j, i ≤ j → ∀ B : Set Ω, MeasurableSet[ℱ i] B → μ B < ∞ →
      ∫ ω in B, M j ω ∂μ = ∫ ω in B, M i ω ∂μ) :
    Martingale M ℱ μ := by
  refine ⟨hAdapted, ?_⟩
  intro i j hij
  have hUnique : M i =ᵐ[μ] μ[M j | ℱ i] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i) (hIntegrable j)
    · intro B hB hμB
      exact (hIntegrable i).integrableOn
    · intro B hB hμB
      exact (hSetIntegral i j hij B hB hμB).symm
    · exact (hAdapted i).aestronglyMeasurable
  exact hUnique.symm

/-- Variant with the finite-measure side condition discharged by a globally finite measure. -/
theorem martingale_of_all_setIntegral_eq_of_isFiniteMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ ℱ]
    {M : ℝ≥0 → Ω → ℝ}
    (hAdapted : StronglyAdapted ℱ M)
    (hIntegrable : ∀ i, Integrable (M i) μ)
    (hSetIntegral : ∀ i j, i ≤ j → ∀ B : Set Ω, MeasurableSet[ℱ i] B →
      ∫ ω in B, M j ω ∂μ = ∫ ω in B, M i ω ∂μ) :
    Martingale M ℱ μ := by
  apply martingale_of_all_setIntegral_eq hAdapted hIntegrable
  intro i j hij B hB hμB
  exact hSetIntegral i j hij B hB

end OTSelector.CountingProcess
