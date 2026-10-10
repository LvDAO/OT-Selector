import OTSelector.Assumptions.EFE2
import OTSelector.Reconstruction.DiagonalLift

/-!
# Conditional interface for macroscopic block identification

This named proposition records deterministic reduced-plan convergence for the original conditional
reconstruction interface. The actual iid probability statement is proved independently in
`Matching.FeedbackSelectorBlockConvergence` and consumed by the complete selector in `Main.lean`.
-/

open MeasureTheory

namespace OTSelector

/-- Abstract output of the block-identification argument. -/
def BlockIdentification {ι : Type*} {l : Filter ι} {m : ι → ℕ}
    [∀ k, NeZero (m k)] (sample : ∀ k, FiniteSample (m k))
    (κ : ProbabilityMeasure (UnitMark × UnitMark)) (_hEFE2 : EFE2 κ) : Prop :=
  Filter.Tendsto
    (fun k ↦ (sample k).diagonalPlan (sample k).euclideanOptimizer)
    l (nhds (reconstructedPlan κ))

theorem BlockIdentification.diagonal_tendsto
    {ι : Type*} {l : Filter ι} {m : ι → ℕ} [∀ k, NeZero (m k)]
    {sample : ∀ k, FiniteSample (m k)} {κ : ProbabilityMeasure (UnitMark × UnitMark)}
    {hEFE2 : EFE2 κ} (hBlock : BlockIdentification (l := l) sample κ hEFE2) :
    Filter.Tendsto
      (fun k ↦ (sample k).diagonalPlan (sample k).euclideanOptimizer)
      l (nhds (reconstructedPlan κ)) :=
  hBlock

end OTSelector
