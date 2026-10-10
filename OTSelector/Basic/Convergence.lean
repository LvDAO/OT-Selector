import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Probability-convergence interfaces

Mathlib calls convergence in probability `TendstoInMeasure`.  This file gives the project a stable
name and fixes the real-distance formulation used throughout `main.tex`.
-/

open MeasureTheory

namespace OTSelector

/-- Project name for mathlib's convergence-in-measure notion on a probability space. -/
abbrev TendstoInProbability {Ω ι E : Type*} [MeasurableSpace Ω] [EDist E]
    (P : Measure Ω) (X : ι → Ω → E) (l : Filter ι) (Z : Ω → E) : Prop :=
  TendstoInMeasure P X l Z

theorem tendstoInProbability_iff_measureReal_dist {Ω ι E : Type*}
    [MeasurableSpace Ω] [PseudoMetricSpace E] {P : Measure Ω} [IsFiniteMeasure P]
    {X : ι → Ω → E} {l : Filter ι} {Z : Ω → E} :
    TendstoInProbability P X l Z ↔
      ∀ ε, 0 < ε →
        Filter.Tendsto (fun i ↦ P.real {ω | ε ≤ dist (X i ω) (Z ω)}) l (nhds 0) :=
  tendstoInMeasure_iff_measureReal_dist

/-- Weak convergence in probability for random probability measures, expressed through bounded
continuous test integrals.  This avoids choosing a particular compatible metric on the weak
topology. -/
def WeakTendstoInProbability {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E] (P : Measure Ω)
    (M : ι → Ω → ProbabilityMeasure E) (l : Filter ι) (ν : ProbabilityMeasure E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    TendstoInProbability P
      (fun i ω ↦ ∫ x, f x ∂(M i ω : Measure E)) l
      (fun _ ↦ ∫ x, f x ∂(ν : Measure E))

end OTSelector
