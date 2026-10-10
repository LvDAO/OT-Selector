import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Finite samples for empirical Euclidean optimal transport

This file fixes the coordinate order used throughout the formalization.  A source point is
`(T, U)`, a target point is `(S, V)`, and a plan point is `((T, U), (S, V))`.  Physical Euclidean
points retain the paper's order `(U, T)` and `(2 + V, S)`.
-/

open Set

namespace OTSelector

/-- The closed unit interval, used for all four sample coordinates. -/
abbrev UnitMark := Set.Icc (0 : ℝ) 1

/-- A vertical coordinate paired with a horizontal mark. -/
abbrev MarkedHeight := UnitMark × UnitMark

/-- The state space of empirical transport plans, ordered as `((T,U),(S,V))`. -/
abbrev PlanPoint := MarkedHeight × MarkedHeight

/-- A finite sample of the four iid coordinate families from `main.tex`. -/
structure FiniteSample (n : ℕ) where
  sourceMark : Fin n → UnitMark
  sourceHeight : Fin n → UnitMark
  targetMark : Fin n → UnitMark
  targetHeight : Fin n → UnitMark

/-- An assignment is a permutation of the target indices. -/
abbrev Assignment (n : ℕ) := Equiv.Perm (Fin n)

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-- Source coordinate in the plan ordering `(T,U)`. -/
def sourcePoint (i : Fin n) : MarkedHeight :=
  (sample.sourceHeight i, sample.sourceMark i)

/-- Target coordinate in the plan ordering `(S,V)`. -/
def targetPoint (j : Fin n) : MarkedHeight :=
  (sample.targetHeight j, sample.targetMark j)

/-- Physical source point `(U,T)` in the Euclidean objective. -/
def physicalSource (i : Fin n) : ℝ × ℝ :=
  (sample.sourceMark i, sample.sourceHeight i)

/-- Physical target point `(2+V,S)` in the Euclidean objective. -/
def physicalTarget (j : Fin n) : ℝ × ℝ :=
  (2 + sample.targetMark j, sample.targetHeight j)

/-- The plan point selected by an assignment. -/
def matchedPoint (σ : Assignment n) (i : Fin n) : PlanPoint :=
  (sample.sourcePoint i, sample.targetPoint (σ i))

/-- Replace the target height by the source height while retaining the two horizontal marks. -/
def diagonalMatchedPoint (σ : Assignment n) (i : Fin n) : PlanPoint :=
  (sample.sourcePoint i, (sample.sourceHeight i, sample.targetMark (σ i)))

/-- Absolute vertical displacement of one matched edge. -/
def verticalDisplacement (σ : Assignment n) (i : Fin n) : ℝ :=
  |(sample.targetHeight (σ i) : ℝ) - sample.sourceHeight i|

/-- Absolute vertical displacement before an assignment is chosen. -/
def verticalEdgeDisplacement (i j : Fin n) : ℝ :=
  |(sample.targetHeight j : ℝ) - sample.sourceHeight i|

/-- Horizontal gap `D = 2 + V - U`, which lies in `[1,3]`. -/
def horizontalGap (i j : Fin n) : ℝ :=
  2 + sample.targetMark j - sample.sourceMark i

/-- Euclidean edge cost in the original finite assignment problem.

This is written explicitly because the default metric on a Lean product is the max metric, not the
Euclidean `ℓ²` metric used in `main.tex`.
-/
noncomputable def euclideanEdgeCost (i j : Fin n) : ℝ :=
  Real.sqrt (sample.horizontalGap i j ^ 2 +
    ((sample.targetHeight j : ℝ) - sample.sourceHeight i) ^ 2)

@[simp]
theorem verticalDisplacement_eq_edge (σ : Assignment n) (i : Fin n) :
    sample.verticalDisplacement σ i = sample.verticalEdgeDisplacement i (σ i) :=
  rfl

theorem horizontalGap_mem (i j : Fin n) : sample.horizontalGap i j ∈ Icc (1 : ℝ) 3 := by
  constructor
  · have hU := (sample.sourceMark i).property.2
    have hV := (sample.targetMark j).property.1
    dsimp [horizontalGap]
    linarith
  · have hU := (sample.sourceMark i).property.1
    have hV := (sample.targetMark j).property.2
    dsimp [horizontalGap]
    linarith

theorem planPoint_dist_diagonalMatchedPoint (σ : Assignment n) (i : Fin n) :
    dist (sample.matchedPoint σ i) (sample.diagonalMatchedPoint σ i) =
      sample.verticalDisplacement σ i := by
  simp [matchedPoint, diagonalMatchedPoint, sourcePoint, targetPoint, verticalDisplacement,
    Prod.dist_eq, Subtype.dist_eq, Real.dist_eq]

end FiniteSample

end OTSelector
