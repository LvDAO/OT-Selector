import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Kernel, disintegration, and conditional-independence interfaces

These declarations are thin names around mathlib.  In particular, regular conditional laws are the
actual `Measure.condKernel`; no project-local choice principle or disintegration axiom is added.
-/

open MeasureTheory ProbabilityTheory

namespace OTSelector

/-- Project-facing name for a conditionally independent family given a sub-sigma-algebra. -/
abbrev ConditionallyIndependent {Ω ι : Type*} {β : ι → Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [∀ i, MeasurableSpace (β i)]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : ∀ i, Ω → β i) (P : @Measure Ω mΩ) [IsFiniteMeasure P] : Prop :=
  Kernel.iIndepFun X (condExpKernel (mΩ := mΩ) P m) (@Measure.trim Ω m mΩ P hm)

/-- Standard-Borel disintegration supplied by mathlib. -/
theorem condKernel_disintegrates {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] (ρ : Measure (α × β))
    [IsFiniteMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ :=
  ρ.disintegrate ρ.condKernel

end OTSelector
