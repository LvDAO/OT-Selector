import OTSelector.PointProcess.LocalConfigurationMeasure
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# The s-finite counting kernel of an actual local configuration

The kernel evaluates to the previously constructed counting measure. Its s-finiteness is proved
by splitting each shell according to its finite cardinality: the piece for cardinality `m` is a
kernel with uniform total mass at most `m`. Summing first over cardinalities and then over shells
recovers the counting measure, including all point multiplicities.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [StandardBorelSpace X] {base : X}

/-- The actual atomic measure in a single shell, as a measurable kernel. -/
noncomputable def shellKernel (n : ℕ) : Kernel (LocalConfiguration base) X where
  toFun config := shellMeasure config n
  measurable' := measurable_shellMeasure n

@[simp]
theorem shellKernel_apply (n : ℕ) (config : LocalConfiguration base) :
    shellKernel n config = shellMeasure config n := rfl

@[simp]
theorem shellKernel_apply_univ (n : ℕ) (config : LocalConfiguration base) :
    shellKernel n config univ = ((config n).card : ℝ≥0∞) := by
  rw [shellKernel_apply, shellMeasure_apply _ _ MeasurableSet.univ]
  simp

private noncomputable def shellCardKernel (n m : ℕ) : Kernel (LocalConfiguration base) X :=
  Kernel.piecewise (s := {config | (config n).card = m})
    (measurableSet_eq_fun (measurable_shell_card n) measurable_const)
    (shellKernel n) 0

private theorem shellCardKernel_apply (n m : ℕ) (config : LocalConfiguration base)
    (s : Set X) :
    shellCardKernel n m config s =
      if (config n).card = m then shellKernel n config s else 0 := by
  simp [shellCardKernel, Kernel.piecewise_apply']

private instance (n m : ℕ) : IsFiniteKernel (shellCardKernel (base := base) n m) where
  exists_univ_le := by
    refine ⟨m, ENNReal.natCast_lt_top m, fun config ↦ ?_⟩
    rw [shellCardKernel_apply]
    split_ifs with h
    · rw [shellKernel_apply_univ, h]
    · exact bot_le

private theorem shellKernel_eq_sum (n : ℕ) :
    shellKernel (base := base) n = Kernel.sum (shellCardKernel n) := by
  ext config s hs
  rw [Kernel.sum_apply' _ _ hs]
  simp [shellCardKernel_apply, eq_comm]

instance instIsSFiniteKernelShellKernel (n : ℕ) :
    IsSFiniteKernel (shellKernel (base := base) n) := by
  rw [shellKernel_eq_sum]
  infer_instance

/-- The measurable kernel whose value is exactly the configuration's counting measure. -/
noncomputable def countingKernel : Kernel (LocalConfiguration base) X where
  toFun := countingMeasure
  measurable' := measurable_countingMeasure

@[simp]
theorem countingKernel_apply (config : LocalConfiguration base) :
    countingKernel config = countingMeasure config := rfl

/-- The shell decomposition is an equality of kernels, not just pointwise s-finiteness. -/
theorem countingKernel_eq_sum_shellKernel :
    countingKernel (base := base) = Kernel.sum (shellKernel (base := base)) := by
  ext config s hs
  rw [countingKernel_apply, countingMeasure_apply config hs, Kernel.sum_apply' _ _ hs]
  rfl

instance instIsSFiniteKernelCountingKernel : IsSFiniteKernel (countingKernel (base := base)) := by
  rw [countingKernel_eq_sum_shellKernel]
  infer_instance

/-- A measurable random configuration supplies an s-finite random counting kernel by pullback. -/
noncomputable def randomCountingKernel {Ω : Type*} [MeasurableSpace Ω]
    (config : Ω → LocalConfiguration base) (hconfig : Measurable config) : Kernel Ω X :=
  countingKernel.comap config hconfig

@[simp]
theorem randomCountingKernel_apply {Ω : Type*} [MeasurableSpace Ω]
    (config : Ω → LocalConfiguration base) (hconfig : Measurable config) (ω : Ω) :
    randomCountingKernel config hconfig ω = countingMeasure (config ω) := rfl

instance instIsSFiniteKernelRandomCountingKernel {Ω : Type*} [MeasurableSpace Ω]
    (config : Ω → LocalConfiguration base) (hconfig : Measurable config) :
    IsSFiniteKernel (randomCountingKernel config hconfig) := by
  unfold randomCountingKernel
  infer_instance

end OTSelector.PointProcess.LocalConfiguration
