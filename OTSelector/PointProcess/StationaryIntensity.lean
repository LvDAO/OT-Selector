import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Intensity of a stationary random measure

Equivariance of an actual random measure and preservation of its underlying law imply translation
invariance of its expectation.  A finite expected unit-window mass then identifies that expectation
as a constant multiple of Lebesgue measure.  The unit-window moment is the only finiteness input.
-/

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Topology

namespace OTSelector.PointProcess

/-- A translation-invariant measure with finite mass on one unit interval is locally finite. -/
theorem locallyFinite_of_invariant_unit (ν : Measure ℝ) [ν.IsAddLeftInvariant]
    (hunit : ν (Ioc 0 1) < ∞) : IsLocallyFiniteMeasure ν := by
  constructor
  intro x
  let a : ℝ := 1 / 2 - x
  refine ⟨(fun y : ℝ ↦ a + y) ⁻¹' Ioo 0 1, ?_, ?_⟩
  · apply ((isOpen_Ioo.preimage (continuous_const.add continuous_id)).mem_nhds)
    change 0 < a + x ∧ a + x < 1
    dsimp [a]
    constructor <;> linarith
  · have heq : ν ((fun y : ℝ ↦ a + y) ⁻¹' Ioo 0 1) = ν (Ioo 0 1) := by
      rw [← Measure.map_apply (show Measurable (fun y : ℝ ↦ a + y) from measurable_const.add measurable_id) measurableSet_Ioo,
        IsAddLeftInvariant.map_add_left_eq_self]
    rw [heq]
    exact (measure_mono Ioo_subset_Ioc_self).trans_lt hunit

/-- The coefficient in Haar uniqueness is exactly the mass of `(0,1]`. -/
theorem invariant_eq_unit_smul_volume (ν : Measure ℝ) [ν.IsAddLeftInvariant]
    (hunit : ν (Ioc 0 1) < ∞) : ν = ν (Ioc 0 1) • volume := by
  let := locallyFinite_of_invariant_unit ν hunit
  have h := isAddLeftInvariant_eq_smul ν (volume : Measure ℝ)
  have hc : ν (Ioc 0 1) = (ν.addHaarScalarFactor volume : ℝ≥0∞) := by
    have := congrArg (fun m : Measure ℝ ↦ m (Ioc 0 1)) h
    simpa using this
  simpa only [hc, ENNReal.smul_def] using h

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Covariance of a random measure passes to its expectation under a law-preserving map. -/
theorem measurePreserving_bind_of_covariant {X : Type*} [MeasurableSpace X]
    (P : Measure Ω) (N : Ω → Measure X) (hN : Measurable N)
    {shift : Ω → Ω} (hshift : MeasurePreserving shift P P)
    {f : X → X} (hf : Measurable f)
    (hcov : ∀ᵐ ω ∂P, N (shift ω) = (N ω).map f) :
    MeasurePreserving f (P.bind N) (P.bind N) := by
  refine ⟨hf, ?_⟩
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) hN.aemeasurable,
    Measure.bind_apply hs hN.aemeasurable]
  calc
    (∫⁻ ω, N ω (f ⁻¹' s) ∂P) = ∫⁻ ω, N (shift ω) s ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hcov] with ω hω
      rw [hω, Measure.map_apply hf hs]
    _ = ∫⁻ ω, N ω s ∂P :=
      hshift.lintegral_comp ((measurable_coe hs).comp hN)

/-- Spatial covariance of random measures passes to their expectation under a stationary law. -/
theorem invariant_bind_of_covariant (P : Measure Ω) (N : Ω → Measure ℝ)
    (hN : Measurable N) (shift : ℝ → Ω → Ω)
    (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hcov : ∀ a, ∀ᵐ ω ∂P, N (shift a ω) = (N ω).map (a + ·)) :
    (P.bind N).IsAddLeftInvariant :=
  ⟨fun a ↦ (measurePreserving_bind_of_covariant P N hN (hshift a)
    (measurable_const.add measurable_id) (hcov a)).map_eq⟩

/-- Campbell's spatial first-moment identity for a covariant random measure. -/
theorem lintegral_random_measure_eq_intensity (P : Measure Ω) (N : Ω → Measure ℝ)
    (hN : Measurable N) (shift : ℝ → Ω → Ω)
    (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hcov : ∀ a, ∀ᵐ ω ∂P, N (shift a ω) = (N ω).map (a + ·))
    (hunit : (∫⁻ ω, N ω (Ioc 0 1) ∂P) < ∞) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (∫⁻ ω, N ω s ∂P) = (∫⁻ ω, N ω (Ioc 0 1) ∂P) * volume s := by
  let := invariant_bind_of_covariant P N hN shift hshift hcov
  have hfinite : (P.bind N) (Ioc 0 1) < ∞ := by
    rwa [Measure.bind_apply measurableSet_Ioc hN.aemeasurable]
  have h := congrArg (fun m : Measure ℝ ↦ m s)
    (invariant_eq_unit_smul_volume (P.bind N) hfinite)
  simpa only [Measure.smul_apply, smul_eq_mul,
    Measure.bind_apply hs hN.aemeasurable,
    Measure.bind_apply measurableSet_Ioc hN.aemeasurable] using h

end OTSelector.PointProcess
