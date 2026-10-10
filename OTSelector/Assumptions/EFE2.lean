import LeanPool.Vlasov.OT.Coupling
import OTSelector.Basic.ModelLaw

/-!
# Projective coupling and diagonal reconstruction

`EFE2` names the uniform-marginal coupling property used by the conditional reconstruction
interface. The complete iid selector constructs such a coupling in `Main.lean`.
The reconstructed macroscopic law is the pushforward of
`dt ⊗ κ∞(du,dv)` under `(t,(u,v)) ↦ ((t,u),(t,v))`.
-/

open MeasureTheory

namespace OTSelector

/-- Insert the common height coordinate into a projective pair of horizontal marks. -/
def diagonalEmbedding (z : UnitMark × (UnitMark × UnitMark)) : PlanPoint :=
  ((z.1, z.2.1), (z.1, z.2.2))

theorem measurable_diagonalEmbedding : Measurable diagonalEmbedding := by
  unfold diagonalEmbedding
  fun_prop

/-- The macroscopic plan `dt δ_t(ds) κ∞(du,dv)` in the macroscopic reconstruction theorem of `main.tex`. -/
noncomputable def reconstructedPlan (κ : ProbabilityMeasure (UnitMark × UnitMark)) :
    ProbabilityMeasure PlanPoint :=
  ProbabilityMeasure.map (unitUniform.prod κ)
    (measurable_diagonalEmbedding.aemeasurable)

/-- The projective mark law couples the two uniform marginals. -/
def EFE2 (κ : ProbabilityMeasure (UnitMark × UnitMark)) : Prop :=
  Vlasov.IsCoupling (κ : Measure (UnitMark × UnitMark))
    (unitUniform : Measure UnitMark) (unitUniform : Measure UnitMark)

end OTSelector
