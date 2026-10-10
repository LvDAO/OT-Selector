import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Splitting one coordinate of a finite product

This file exposes the coordinate split used by the deferred-decision calculations.  The split is
the measurable version of `Equiv.piSplitAt`; its product-law statement is proved from the
measure-preserving finite-product equivalences in mathlib.
-/

open MeasureTheory Set

namespace OTSelector.Probability

set_option linter.style.haveILetI false

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]

/-- The measurable equivalence which exposes coordinate `i` and retains all other coordinates. -/
def piSplitAt (i : ι) : (ι → α) ≃ᵐ α × ({j : ι // j ≠ i} → α) where
  toEquiv := Equiv.piSplitAt i (fun _ : ι => α)
  measurable_toFun := by
    exact (measurable_pi_apply i).prodMk <| measurable_pi_iff.mpr fun j =>
      measurable_pi_apply (j : ι)
  measurable_invFun := by
    rw [measurable_pi_iff]
    intro j
    by_cases h : j = i
    · subst j
      simpa [Equiv.piSplitAt] using measurable_fst
    · have hfun :
          (fun x : α × ({j : ι // j ≠ i} → α) =>
            (Equiv.piSplitAt i (fun _ : ι => α)).symm x j) =
            (fun x => x.2 ⟨j, h⟩) := by
        funext x
        simp [Equiv.piSplitAt, h]
      rw [hfun]
      exact (measurable_pi_apply (X := fun _ : {j : ι // j ≠ i} => α)
        (show {j : ι // j ≠ i} from ⟨j, h⟩)).comp measurable_snd

omit [Fintype ι] in
@[simp] theorem piSplitAt_apply (i : ι) (x : ι → α) :
    piSplitAt i x = (x i, fun j : {j : ι // j ≠ i} => x j) := rfl

omit [Fintype ι] in
@[simp] theorem piSplitAt_symm_apply (i : ι) (x : α × ({j : ι // j ≠ i} → α)) (j : ι) :
    (piSplitAt i).symm x j = if h : j = i then h.symm.rec x.1 else x.2 ⟨j, h⟩ := rfl

/-! ## Product-law transport -/

theorem measurePreserving_piSplitAt (μ : Measure α) [SigmaFinite μ] (i : ι) :
    MeasurePreserving (piSplitAt i) (Measure.pi fun _ : ι => μ)
      (μ.prod (Measure.pi fun _ : {j : ι // j ≠ i} => μ)) := by
  letI : Unique {j : ι // j = i} :=
    { default := ⟨i, rfl⟩
      uniq := fun j => Subtype.ext j.property }
  letI : Fintype {j : ι // j = i} := Subtype.fintype (fun j => j = i)
  let e₀ := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : ι => α) (fun j : ι => j = i)
  let e₁ := MeasurableEquiv.prodCongr
    (MeasurableEquiv.piUnique (fun _ : {j : ι // j = i} => α))
    (MeasurableEquiv.refl ((j : {j : ι // j ≠ i}) → α))
  have h₀ : MeasurePreserving e₀
      (Measure.pi fun _ : ι => μ)
      ((Measure.pi fun _ : {j : ι // j = i} => μ).prod
        (Measure.pi fun _ : {j : ι // j ≠ i} => μ)) := by
    simpa [e₀] using
      (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun j : ι => j = i))
  have h₁ : MeasurePreserving e₁
      ((Measure.pi fun _ : {j : ι // j = i} => μ).prod
        (Measure.pi fun _ : {j : ι // j ≠ i} => μ))
      (μ.prod (Measure.pi fun _ : {j : ι // j ≠ i} => μ)) := by
    change MeasurePreserving
      (Prod.map (MeasurableEquiv.piUnique (fun _ : {j : ι // j = i} => α)) id)
      ((Measure.pi fun _ : {j : ι // j = i} => μ).prod
        (Measure.pi fun _ : {j : ι // j ≠ i} => μ))
      (μ.prod (Measure.pi fun _ : {j : ι // j ≠ i} => μ))
    simpa using
      (MeasureTheory.MeasurePreserving.prod
        (measurePreserving_piUnique (fun _ : {j : ι // j = i} => μ))
        (MeasureTheory.MeasurePreserving.id
          (Measure.pi fun _ : {j : ι // j ≠ i} => μ)))
  have hcomp := MeasureTheory.MeasurePreserving.comp h₁ h₀
  have heq : (piSplitAt i : (ι → α) → α × ({j : ι // j ≠ i} → α)) =
      (e₁ : _ → _) ∘ e₀ := by
    funext x
    apply Prod.ext
    · rfl
    · funext j
      rfl
  rw [heq]
  exact hcomp

/-- Merge a selected coordinate with a function on all the other coordinates. -/
def piMergeAt (i : ι) (z : α) (rest : {j : ι // j ≠ i} → α) : ι → α :=
  (piSplitAt i).symm (z, rest)

omit [Fintype ι] in
@[simp] theorem piMergeAt_at (i : ι) (z : α) (rest : {j : ι // j ≠ i} → α) :
    piMergeAt i z rest i = z := by
  simp [piMergeAt]

omit [Fintype ι] in
@[simp] theorem piMergeAt_other (i j : ι) (z : α)
    (rest : {j : ι // j ≠ i} → α) (h : j ≠ i) :
    piMergeAt i z rest j = rest ⟨j, h⟩ := by
  simp [piMergeAt, h]

/-- Bochner integral transport through the coordinate split, with the remaining coordinates
integrated by Fubini.  The statement is written for an arbitrary integrable real-valued function;
the same proof works for any Banach-valued Bochner integral. -/
theorem integral_piSplitAt
    (μ : Measure α) [SigmaFinite μ] (i : ι)
    {F : (ι → α) → ℝ} (hF : Integrable F (Measure.pi fun _ : ι => μ)) :
    (∫ x, F x ∂(Measure.pi fun _ : ι => μ)) =
      ∫ z : α, ∫ rest : {j : ι // j ≠ i} → α,
        F (piMergeAt i z rest)
          ∂(Measure.pi fun _ : {j : ι // j ≠ i} => μ) ∂μ := by
  have hmp := measurePreserving_piSplitAt μ i
  have hsymm : MeasurePreserving ((piSplitAt i).symm)
      (μ.prod (Measure.pi fun _ : {j : ι // j ≠ i} => μ))
      (Measure.pi fun _ : ι => μ) :=
    MeasureTheory.MeasurePreserving.symm (piSplitAt i) hmp
  have hg : Integrable (F ∘ (piSplitAt i).symm)
      (μ.prod (Measure.pi fun _ : {j : ι // j ≠ i} => μ)) := by
    exact (hsymm.integrable_comp hF.aestronglyMeasurable).mpr hF
  calc
    (∫ x, F x ∂(Measure.pi fun _ : ι => μ)) =
        ∫ z, F ((piSplitAt i).symm z)
          ∂(μ.prod (Measure.pi fun _ : {j : ι // j ≠ i} => μ)) := by
      exact (hsymm.integral_comp' F).symm
    _ = ∫ z : α, ∫ rest : {j : ι // j ≠ i} → α,
          F (piMergeAt i z rest)
            ∂(Measure.pi fun _ : {j : ι // j ≠ i} => μ) ∂μ := by
      simpa [piMergeAt, Function.comp_def] using
        (integral_prod (F ∘ (piSplitAt i).symm) hg)

end OTSelector.Probability
