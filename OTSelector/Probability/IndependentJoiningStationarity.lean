import OTSelector.Probability.IndependentJoining
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Stationarity of the relative independent joining

For an invertible measurable change of environment and a measurable change of matching, invariance
of each joint law implies almost-everywhere equivariance of its actual conditional kernel.
Disintegration uniqueness supplies this equivariance; it is not assumed. Consequently the relative
independent joining is invariant under the simultaneous change of all three coordinates.

Applied separately to each spatial translation, the last theorem gives stationarity of the joining.
It makes no assertion that its matching coordinates agree; that remains the P5 geometric step.
-/

open MeasureTheory ProbabilityTheory

namespace OTSelector

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Change of coordinates for a measure/kernel composition product. -/
theorem map_compProd_prodMap_equiv (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] (T : α ≃ᵐ α) {f : β → γ} (hf : Measurable f) :
    (μ ⊗ₘ κ).map (Prod.map T f) =
      μ.map T ⊗ₘ ((κ.map f).comap T.symm T.symm.measurable) := by
  ext s hs
  rw [Measure.map_apply (T.measurable.prodMap hf) hs,
    Measure.compProd_apply ((T.measurable.prodMap hf) hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) T.measurable]
  apply lintegral_congr
  intro a
  rw [Kernel.comap_apply, T.symm_apply_apply, Kernel.map_apply _ hf,
    Measure.map_apply hf (measurable_prodMk_left hs)]
  rfl

/-- Invariance of a joint law implies invariance of its environment marginal. -/
theorem fst_map_eq_of_map_prod_eq (ρ : Measure (α × β)) (T : α → α) {f : β → β}
    (hT : Measurable T) (hf : Measurable f) (hρ : ρ.map (Prod.map T f) = ρ) :
    ρ.fst.map T = ρ.fst := by
  have h := congrArg Measure.fst hρ
  change (ρ.map (fun p ↦ (T p.1, (f ∘ Prod.snd) p))).fst = ρ.fst at h
  rw [Measure.fst_map_prodMk (hf.comp measurable_snd)] at h
  simpa only [Measure.fst, Measure.map_map hT measurable_fst, Function.comp_def] using h

/-- Disintegration uniqueness gives the transported conditional kernel almost everywhere.
The environment transformation is invertible, while the matching map need only be measurable. -/
theorem ae_condKernel_map_comap_eq_of_map_prod_eq [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (T : α ≃ᵐ α) {f : β → β}
    (hf : Measurable f) (hρ : ρ.map (Prod.map T f) = ρ) :
    (ρ.condKernel.map f).comap T.symm T.symm.measurable =ᵐ[ρ.fst] ρ.condKernel := by
  apply eq_condKernel_of_measure_eq_compProd
  calc
    ρ = (ρ.fst ⊗ₘ ρ.condKernel).map (Prod.map T f) := by
      rw [condKernel_disintegrates, hρ]
    _ = ρ.fst ⊗ₘ (ρ.condKernel.map f).comap T.symm T.symm.measurable := by
      rw [map_compProd_prodMap_equiv _ _ T hf,
        fst_map_eq_of_map_prod_eq ρ T T.measurable hf hρ]

/-- The actual conditional matching law is equivariant almost everywhere, as a consequence of
joint-law invariance. No pointwise equivariance of the chosen conditional kernel is claimed. -/
theorem ae_condKernel_equivariant_of_map_prod_eq [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ] (T : α ≃ᵐ α) {f : β → β}
    (hf : Measurable f) (hρ : ρ.map (Prod.map T f) = ρ) :
    ∀ᵐ a ∂ρ.fst, ρ.condKernel (T a) = (ρ.condKernel a).map f := by
  have h := ae_condKernel_map_comap_eq_of_map_prod_eq ρ T hf hρ
  have henv := fst_map_eq_of_map_prod_eq ρ T T.measurable hf hρ
  have hmap : ∀ᵐ a ∂ρ.fst.map T,
      ((ρ.condKernel.map f).comap T.symm T.symm.measurable) a = ρ.condKernel a := by
    rwa [henv]
  filter_upwards [ae_of_ae_map T.measurable.aemeasurable hmap] with a ha
  simpa only [Kernel.comap_apply, T.symm_apply_apply, Kernel.map_apply _ hf] using ha.symm

/-- The relative independent joining of two invariant joint laws with a common environment law is
invariant under the simultaneous transformation. Conditional-kernel equivariance is proved from the
input joint-law invariance, rather than being an additional assumption. -/
theorem relativeIndependentJoining_map_eq_of_map_prod_eq
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace γ] [Nonempty γ]
    (ρ : Measure (α × β)) (σ : Measure (α × γ)) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (henv : ρ.fst = σ.fst) (T : α ≃ᵐ α) {f : β → β} {g : γ → γ}
    (hf : Measurable f) (hg : Measurable g)
    (hρ : ρ.map (Prod.map T f) = ρ) (hσ : σ.map (Prod.map T g) = σ) :
    (relativeIndependentJoining ρ σ).map (Prod.map T (Prod.map f g)) =
      relativeIndependentJoining ρ σ := by
  have hκ := ae_condKernel_map_comap_eq_of_map_prod_eq ρ T hf hρ
  have hη := ae_condKernel_map_comap_eq_of_map_prod_eq σ T hg hσ
  rw [← henv] at hη
  unfold relativeIndependentJoining
  rw [map_compProd_prodMap_equiv _ _ T (hf.prodMap hg),
    fst_map_eq_of_map_prod_eq ρ T T.measurable hf hρ,
    ← Kernel.map_prod_map _ _ hf hg, Kernel.comap_prod]
  apply Measure.compProd_congr
  filter_upwards [hκ, hη] with a hκa hηa
  simp only [Kernel.prod_apply, hκa, hηa]

end OTSelector
