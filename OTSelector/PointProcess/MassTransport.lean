import OTSelector.PointProcess.Campbell
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Mass transport on the line

A diagonally translation-invariant transport measure has equal expected outgoing and incoming
mass in a unit window.  Finiteness is assumed only for outgoing mass.  The proof uses displacement
coordinates and the proved Campbell factorization, and does not presuppose a mass-transport identity.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace OTSelector.PointProcess

/-- Change from source and destination to source and displacement. -/
def displacementCoordinates : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun z := (z.1, z.2 - z.1)
  invFun z := (z.1, z.1 + z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.sub measurable_fst)
  measurable_invFun := measurable_fst.prodMk (measurable_fst.add measurable_snd)

/-- In displacement coordinates, moving the receiving window preserves its total mean mass. -/
theorem incoming_eq_outgoing_of_campbell (C : Measure (ℝ × ℝ))
    (hstat : ∀ a : ℝ, MeasurePreserving (fun z : ℝ × ℝ ↦ (a + z.1, z.2)) C C)
    (hunit : C (Ioc 0 1 ×ˢ univ) < ∞) :
    C {z | z.1 + z.2 ∈ Ioc 0 1} = C (Ioc 0 1 ×ˢ univ) := by
  have : IsFiniteMeasure (unitWindowPalm C) := by
    constructor
    rwa [unitWindowPalm_apply C MeasurableSet.univ]
  have hs : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 ∈ Ioc 0 1} :=
    (measurable_fst.add measurable_snd) measurableSet_Ioc
  rw [campbell_eq_volume_prod_palm C hstat hunit, Measure.prod_apply_symm hs]
  have hinner (d : ℝ) :
      volume ((fun x : ℝ ↦ (x, d)) ⁻¹' {z : ℝ × ℝ | z.1 + z.2 ∈ Ioc 0 1}) = 1 := by
    change volume ((fun x : ℝ ↦ x + d) ⁻¹' Ioc 0 1) = 1
    simp
  simp_rw [hinner]
  simp [unitWindowPalm_apply C MeasurableSet.univ]

/-- Stationary mass transport: the expected incoming and outgoing unit-window masses coincide.
The incoming mass is not assumed finite in advance. -/
theorem stationary_mass_transport (T : Measure (ℝ × ℝ))
    (hstat : ∀ a : ℝ, MeasurePreserving (fun z : ℝ × ℝ ↦ (a + z.1, a + z.2)) T T)
    (hout : T (Ioc 0 1 ×ˢ univ) < ∞) :
    T (univ ×ˢ Ioc 0 1) = T (Ioc 0 1 ×ˢ univ) := by
  let C := T.map displacementCoordinates
  have hC (a : ℝ) : MeasurePreserving (fun z : ℝ × ℝ ↦ (a + z.1, z.2)) C C := by
    apply (displacementCoordinates.measurable.measurePreserving T).of_semiconj (hstat a)
    · intro z
      ext <;> simp [displacementCoordinates]
    · exact (measurable_const.add measurable_fst).prodMk measurable_snd
  have houtC : C (Ioc 0 1 ×ˢ univ) = T (Ioc 0 1 ×ˢ univ) := by
    dsimp only [C]
    rw [Measure.map_apply displacementCoordinates.measurable
      (measurableSet_Ioc.prod MeasurableSet.univ)]
    rfl
  have hinC : C {z | z.1 + z.2 ∈ Ioc 0 1} = T (univ ×ˢ Ioc 0 1) := by
    have hs : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 ∈ Ioc 0 1} :=
      (measurable_fst.add measurable_snd) measurableSet_Ioc
    dsimp only [C]
    rw [Measure.map_apply displacementCoordinates.measurable hs]
    congr 1
    ext z
    simp [displacementCoordinates]
  rw [← hinC, incoming_eq_outgoing_of_campbell C hC (houtC ▸ hout), houtC]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The expected incoming and outgoing masses of an actual covariant random transport agree. -/
theorem lintegral_stationary_mass_transport (P : Measure Ω) (T : Ω → Measure (ℝ × ℝ))
    (hT : Measurable T) (shift : ℝ → Ω → Ω)
    (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hcov : ∀ a, ∀ᵐ ω ∂P,
      T (shift a ω) = (T ω).map (fun z ↦ (a + z.1, a + z.2)))
    (hout : (∫⁻ ω, T ω (Ioc 0 1 ×ˢ univ) ∂P) < ∞) :
    (∫⁻ ω, T ω (univ ×ˢ Ioc 0 1) ∂P) = ∫⁻ ω, T ω (Ioc 0 1 ×ˢ univ) ∂P := by
  have hstat (a : ℝ) :
      MeasurePreserving (fun z : ℝ × ℝ ↦ (a + z.1, a + z.2)) (P.bind T) (P.bind T) :=
    measurePreserving_bind_of_covariant P T hT (hshift a)
      ((measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd))
      (hcov a)
  have hfinite : (P.bind T) (Ioc 0 1 ×ˢ univ) < ∞ := by
    rwa [Measure.bind_apply (measurableSet_Ioc.prod MeasurableSet.univ) hT.aemeasurable]
  simpa only [Measure.bind_apply (MeasurableSet.univ.prod measurableSet_Ioc) hT.aemeasurable,
    Measure.bind_apply (measurableSet_Ioc.prod MeasurableSet.univ) hT.aemeasurable] using
    stationary_mass_transport (P.bind T) hstat hfinite

/-- Finite outgoing intensity rules out infinite incoming mass in the unit window almost surely. -/
theorem ae_incoming_unit_lt_top (P : Measure Ω) (T : Ω → Measure (ℝ × ℝ))
    (hT : Measurable T) (shift : ℝ → Ω → Ω)
    (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hcov : ∀ a, ∀ᵐ ω ∂P,
      T (shift a ω) = (T ω).map (fun z ↦ (a + z.1, a + z.2)))
    (hout : (∫⁻ ω, T ω (Ioc 0 1 ×ˢ univ) ∂P) < ∞) :
    ∀ᵐ ω ∂P, T ω (univ ×ˢ Ioc 0 1) < ∞ := by
  apply ae_lt_top ((measurable_coe (MeasurableSet.univ.prod measurableSet_Ioc)).comp hT)
  change (∫⁻ ω, T ω (univ ×ˢ Ioc 0 1) ∂P) ≠ ∞
  rw [lintegral_stationary_mass_transport P T hT shift hshift hcov hout]
  exact hout.ne

end OTSelector.PointProcess
