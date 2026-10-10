import OTSelector.Basic.Model
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Finite feedback graph geometry

This module records the rank-scale phase lines and a real-valued Lipschitz contract for the
auxiliary feedback graph.  The latter is deliberately stated without an `NNReal` coercion so that
the constants in `main.tex` remain visible in algebraic estimates.
-/

namespace OTSelector

/-- Real-valued `λ`-Lipschitz condition, written in the orientation used by the swept-set proofs. -/
def RealLipschitz (lam : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x y, |g y - g x| ≤ lam * |y - x|

/-- The predictable graph data used by Sections 1--2. -/
structure FeedbackGraph (lam : ℝ) where
  curve : ℝ → ℝ
  lam_nonneg : 0 ≤ lam
  lam_lt_half : lam < 1 / 2
  lipschitz : RealLipschitz lam curve

namespace FiniteSample

variable {n : ℕ} (sample : FiniteSample n)

/-- Paper notation `aᵢ = 1 - Uᵢ`. -/
def sourceSlope (i : Fin n) : ℝ :=
  1 - sample.sourceMark i

/-- Paper notation `bⱼ = 1 + Vⱼ`. -/
def targetSlope (j : Fin n) : ℝ :=
  1 + sample.targetMark j

/-- Rank-scale source phase line `nTᵢ + aᵢp`. -/
def sourcePhase (i : Fin n) (p : ℝ) : ℝ :=
  n * sample.sourceHeight i + sample.sourceSlope i * p

/-- Rank-scale target phase line `nSⱼ - bⱼp`. -/
def targetPhase (j : Fin n) (p : ℝ) : ℝ :=
  n * sample.targetHeight j - sample.targetSlope j * p

theorem sourceSlope_mem (i : Fin n) : sample.sourceSlope i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> simp only [sourceSlope]
  · exact sub_nonneg.mpr (sample.sourceMark i).property.2
  · linarith [(sample.sourceMark i).property.1]

theorem targetSlope_mem (j : Fin n) : sample.targetSlope j ∈ Set.Icc (1 : ℝ) 2 := by
  constructor <;> simp only [targetSlope]
  · linarith [(sample.targetMark j).property.1]
  · linarith [(sample.targetMark j).property.2]

end FiniteSample

end OTSelector
