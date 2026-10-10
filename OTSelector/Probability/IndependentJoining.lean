import OTSelector.Probability.Kernels
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Relative independent joining over a common environment

The joining is the composition product of the environment law with the product of the actual
regular conditional laws. Its two environment/matching marginals recover the input joint laws.
If the matching coordinates agree almost surely under this joining, the joint laws coincide and
the conditional matching laws are almost surely Dirac measures.

The almost-sure agreement is an input to these probability lemmas. Establishing it for the
selector still requires the P5 geometric argument; these declarations do not assert that result.
-/

open MeasureTheory ProbabilityTheory

namespace OTSelector

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Two matching laws sampled independently conditional on their common environment. The second
law has the required marginal only when its environment marginal equals that of the first law. -/
noncomputable def relativeIndependentJoining [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ] [Nonempty γ]
    (ρ : Measure (α × β)) (σ : Measure (α × γ)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] :
    Measure (α × (β × γ)) :=
  ρ.fst ⊗ₘ (ρ.condKernel ×ₖ σ.condKernel)

instance [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace γ] [Nonempty γ]
    (ρ : Measure (α × β)) (σ : Measure (α × γ)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] :
    IsFiniteMeasure (relativeIndependentJoining ρ σ) := by
  unfold relativeIndependentJoining
  infer_instance

instance [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace γ] [Nonempty γ]
    (ρ : Measure (α × β)) (σ : Measure (α × γ))
    [IsProbabilityMeasure ρ] [IsFiniteMeasure σ] :
    IsProbabilityMeasure (relativeIndependentJoining ρ σ) := by
  unfold relativeIndependentJoining
  infer_instance

/-- The first environment/matching marginal of the relative independent joining. -/
theorem relativeIndependentJoining_map_left [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ] [Nonempty γ]
    (ρ : Measure (α × β)) (σ : Measure (α × γ)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ] :
    (relativeIndependentJoining ρ σ).map (fun p ↦ (p.1, p.2.1)) = ρ := by
  change (ρ.fst ⊗ₘ (ρ.condKernel ×ₖ σ.condKernel)).map (Prod.map id Prod.fst) = ρ
  rw [← Measure.compProd_map measurable_fst]
  rw [← Kernel.fst_eq, Kernel.fst_prod, condKernel_disintegrates]

/-- The second marginal is the prescribed joint law when the environment marginals agree. -/
theorem relativeIndependentJoining_map_right [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ] [Nonempty γ]
    (ρ : Measure (α × β)) (σ : Measure (α × γ)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (henv : ρ.fst = σ.fst) :
    (relativeIndependentJoining ρ σ).map (fun p ↦ (p.1, p.2.2)) = σ := by
  change (ρ.fst ⊗ₘ (ρ.condKernel ×ₖ σ.condKernel)).map (Prod.map id Prod.snd) = σ
  rw [← Measure.compProd_map measurable_snd]
  rw [← Kernel.snd_eq, Kernel.snd_prod, henv, condKernel_disintegrates]

/-- Independent probability measures supported on the diagonal must be the same Dirac measure. -/
theorem exists_common_dirac_of_prod_ae_eq (μ ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ᵐ p ∂μ.prod ν, p.1 = p.2) :
    ∃ b, μ = Measure.dirac b ∧ ν = Measure.dirac b := by
  have hμν : μ = ν := by
    simpa using Measure.map_congr h
  obtain ⟨b, hb⟩ := (Measure.ae_ae_of_ae_prod h).exists
  have hν : ν = Measure.dirac b := by
    have hmap : ν.map id = ν.map (fun _ ↦ b) :=
      Measure.map_congr (hb.mono fun _ hx ↦ hx.symm)
    simpa using hmap
  exact ⟨b, hμν.trans hν, hν⟩

/-- Fiberwise version of the independent diagonal criterion. -/
theorem ae_exists_common_dirac_of_compProd_prod_ae_eq (μ : Measure α) [SFinite μ]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (h : ∀ᵐ p ∂μ ⊗ₘ (κ ×ₖ η), p.2.1 = p.2.2) :
    ∀ᵐ a ∂μ, ∃ b, κ a = Measure.dirac b ∧ η a = Measure.dirac b := by
  filter_upwards [Measure.ae_ae_of_ae_compProd h] with a ha
  rw [Kernel.prod_apply] at ha
  exact exists_common_dirac_of_prod_ae_eq (κ a) (η a) ha

/-- Almost-sure matching agreement in the relative independent joining forces both conditional
laws to be the same Dirac measure almost everywhere. The agreement is a geometric input. -/
theorem ae_condKernel_common_dirac_of_relativeIndependentJoining_ae_eq
    [StandardBorelSpace β] [Nonempty β]
    (ρ σ : Measure (α × β)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (h : ∀ᵐ p ∂relativeIndependentJoining ρ σ, p.2.1 = p.2.2) :
    ∀ᵐ a ∂ρ.fst, ∃ b, ρ.condKernel a = Measure.dirac b ∧
      σ.condKernel a = Measure.dirac b :=
  ae_exists_common_dirac_of_compProd_prod_ae_eq ρ.fst ρ.condKernel σ.condKernel h

/-- Agreement of two conditionally independent copies makes the conditional law almost surely
Dirac. This theorem does not supply the required geometric agreement of the copies. -/
theorem ae_condKernel_dirac_of_relativeIndependentJoining_self_ae_eq
    [StandardBorelSpace β] [Nonempty β] (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    (h : ∀ᵐ p ∂relativeIndependentJoining ρ ρ, p.2.1 = p.2.2) :
    ∀ᵐ a ∂ρ.fst, ∃ b, ρ.condKernel a = Measure.dirac b := by
  filter_upwards [ae_condKernel_common_dirac_of_relativeIndependentJoining_ae_eq ρ ρ h]
    with a ha
  exact ha.imp fun _ hb ↦ hb.1

/-- Two joint laws with the same environment marginal coincide if their conditionally independent
matching coordinates agree almost surely. The latter remains the P5 geometric input. -/
theorem eq_of_relativeIndependentJoining_ae_eq [StandardBorelSpace β] [Nonempty β]
    (ρ σ : Measure (α × β)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (henv : ρ.fst = σ.fst)
    (h : ∀ᵐ p ∂relativeIndependentJoining ρ σ, p.2.1 = p.2.2) : ρ = σ := by
  calc
    ρ = (relativeIndependentJoining ρ σ).map (fun p ↦ (p.1, p.2.1)) :=
      (relativeIndependentJoining_map_left ρ σ).symm
    _ = (relativeIndependentJoining ρ σ).map (fun p ↦ (p.1, p.2.2)) :=
      Measure.map_congr (h.mono fun _ hp ↦ congrArg (Prod.mk _) hp)
    _ = σ := relativeIndependentJoining_map_right ρ σ henv

end OTSelector
