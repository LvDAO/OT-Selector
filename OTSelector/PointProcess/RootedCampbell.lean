import OTSelector.PointProcess.CountingKernel
import OTSelector.PointProcess.Campbell
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Actual rooted Campbell measures from random counting kernels

Compose the environment law with its counting kernel and then record the point location and the
environment rerooted at that point. This defines the actual rooted Campbell measure. Its testing
integrals and unit-window Palm measure are computed directly from this construction.

Stationarity is derived from preservation of the environment law, covariance of the counting
kernel, and the rerooting cocycle. The existing Campbell factorization then identifies the measure
as Lebesgue measure times its actual unit-window Palm measure.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace OTSelector.PointProcess

variable {Ω X M : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace M]

/-- The random measure of point locations and the corresponding rooted environments. -/
noncomputable def rootedPointKernel (N : Kernel Ω X) (reroot : Ω × X → M) : Kernel Ω (X × M) :=
  (Kernel.id ×ₖ N).map (fun p ↦ (p.2, reroot p))

/-- Rooting retains each point with its original counting mass. -/
theorem rootedPointKernel_apply (N : Kernel Ω X) [IsSFiniteKernel N]
    (reroot : Ω × X → M) (hr : Measurable reroot) (ω : Ω) :
    rootedPointKernel N reroot ω = (N ω).map (fun x ↦ (x, reroot (ω, x))) := by
  have hω : Measurable (fun x : X ↦ (x, reroot (ω, x))) :=
    measurable_id.prodMk (hr.comp measurable_prodMk_left)
  ext s hs
  unfold rootedPointKernel
  rw [Kernel.map_apply' _ (measurable_snd.prodMk hr) _ hs,
    Kernel.id_prod_apply' N ω ((measurable_snd.prodMk hr) hs),
    Measure.map_apply hω hs]
  rfl

instance instIsSFiniteKernelRootedPointKernel (N : Kernel Ω X) (reroot : Ω × X → M) :
    IsSFiniteKernel (rootedPointKernel N reroot) := by
  unfold rootedPointKernel
  infer_instance

/-- Campbell measure from the actual environment law, counting kernel, and rerooting map. -/
noncomputable def rootedCampbell (P : Measure Ω) (N : Kernel Ω X) (reroot : Ω × X → M) :
    Measure (X × M) :=
  (P ⊗ₘ N).map (fun p ↦ (p.2, reroot p))

/-- Equivalent random-measure representation, used to transfer stationarity. -/
theorem rootedCampbell_eq_bind (P : Measure Ω) [SFinite P]
    (N : Kernel Ω X) [IsSFiniteKernel N] (reroot : Ω × X → M) (hr : Measurable reroot) :
    rootedCampbell P N reroot = P.bind (rootedPointKernel N reroot) := by
  rw [rootedCampbell, Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ (measurable_snd.prodMk hr)]
  rfl

/-- The defining nonnegative test-integral formula for the actual rooted Campbell measure. -/
theorem lintegral_rootedCampbell (P : Measure Ω) [SFinite P]
    (N : Kernel Ω X) [IsSFiniteKernel N] (reroot : Ω × X → M) (hr : Measurable reroot)
    {f : X × M → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂rootedCampbell P N reroot) =
      ∫⁻ ω, ∫⁻ x, f (x, reroot (ω, x)) ∂N ω ∂P := by
  rw [rootedCampbell, lintegral_map hf (measurable_snd.prodMk hr)]
  exact Measure.lintegral_compProd (hf.comp (measurable_snd.prodMk hr))

/-- A Campbell rectangle is the expected number of points in its location window and mark class. -/
theorem rootedCampbell_apply_prod (P : Measure Ω) [SFinite P]
    (N : Kernel Ω X) [IsSFiniteKernel N] (reroot : Ω × X → M) (hr : Measurable reroot)
    {A : Set X} {B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    rootedCampbell P N reroot (A ×ˢ B) =
      ∫⁻ ω, N ω {x | x ∈ A ∧ reroot (ω, x) ∈ B} ∂P := by
  rw [rootedCampbell, Measure.map_apply (measurable_snd.prodMk hr) (hA.prod hB),
    Measure.compProd_apply ((measurable_snd.prodMk hr) (hA.prod hB))]
  rfl

/-- Specialization to the decoded counting measures of actual measurable local configurations. -/
theorem lintegral_rootedCampbell_counting [MetricSpace X] [BorelSpace X]
    [StandardBorelSpace X] {base : X} (P : Measure Ω) [SFinite P]
    (config : Ω → LocalConfiguration base) (hc : Measurable config)
    (reroot : Ω × X → M) (hr : Measurable reroot) {f : X × M → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂rootedCampbell P (LocalConfiguration.randomCountingKernel config hc) reroot) =
      ∫⁻ ω, ∫⁻ x, f (x, reroot (ω, x)) ∂LocalConfiguration.countingMeasure (config ω) ∂P :=
  lintegral_rootedCampbell P (LocalConfiguration.randomCountingKernel config hc) reroot hr hf

/-- The unit-window Palm measure is the actual point-rooting measure inside `(0,1]`. -/
theorem unitWindowPalm_rootedCampbell_eq (P : Measure Ω) [SFinite P]
    (N : Kernel Ω ℝ) [IsSFiniteKernel N] (reroot : Ω × ℝ → M) (hr : Measurable reroot) :
    unitWindowPalm (rootedCampbell P N reroot) =
      ((P ⊗ₘ N).restrict (univ ×ˢ Ioc 0 1)).map reroot := by
  ext B hB
  rw [unitWindowPalm_apply _ hB, rootedCampbell_apply_prod P N reroot hr measurableSet_Ioc hB,
    Measure.map_apply hr hB, Measure.restrict_apply (hr hB),
    Measure.compProd_apply ((hr hB).inter (MeasurableSet.univ.prod measurableSet_Ioc))]
  congr 1
  funext ω
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_prod, mem_univ, true_and]
  exact and_comm

/-- Palm testing is expected point summation over the spatial unit window. -/
theorem lintegral_unitWindowPalm_rootedCampbell (P : Measure Ω) [SFinite P]
    (N : Kernel Ω ℝ) [IsSFiniteKernel N] (reroot : Ω × ℝ → M) (hr : Measurable reroot)
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ m, f m ∂unitWindowPalm (rootedCampbell P N reroot)) =
      ∫⁻ ω, ∫⁻ x in Ioc 0 1, f (reroot (ω, x)) ∂N ω ∂P := by
  rw [unitWindowPalm_rootedCampbell_eq P N reroot hr, lintegral_map hf hr]
  simpa only [Measure.restrict_univ, Function.comp_def] using
    (Measure.setLIntegral_compProd (hf.comp hr) MeasurableSet.univ measurableSet_Ioc)

/-- The mass of the unnormalized Palm measure is the expected unit-window point count. -/
theorem unitWindowPalm_rootedCampbell_univ (P : Measure Ω) [SFinite P]
    (N : Kernel Ω ℝ) [IsSFiniteKernel N] (reroot : Ω × ℝ → M) (hr : Measurable reroot) :
    unitWindowPalm (rootedCampbell P N reroot) univ = ∫⁻ ω, N ω (Ioc 0 1) ∂P := by
  rw [unitWindowPalm_apply _ MeasurableSet.univ,
    rootedCampbell_apply_prod P N reroot hr measurableSet_Ioc MeasurableSet.univ]
  simp only [mem_univ, and_true, ofPred_mem_eq]

/-- Environment stationarity and the counting/rerooting covariance imply stationarity in the
location coordinate of the actual Campbell measure. The cocycle need only hold at almost every
counted point of almost every environment. -/
theorem measurePreserving_rootedCampbell_of_covariant (P : Measure Ω) [SFinite P]
    (N : Kernel Ω ℝ) [IsSFiniteKernel N] (reroot : Ω × ℝ → M) (hr : Measurable reroot)
    (a : ℝ) {shift : Ω → Ω} (hshift : MeasurePreserving shift P P)
    (hN : ∀ᵐ ω ∂P, N (shift ω) = (N ω).map (a + ·))
    (hrcov : ∀ᵐ ω ∂P, ∀ᵐ x ∂N ω, reroot (shift ω, a + x) = reroot (ω, x)) :
    MeasurePreserving (fun p : ℝ × M ↦ (a + p.1, p.2))
      (rootedCampbell P N reroot) (rootedCampbell P N reroot) := by
  have hpoint (ω : Ω) : Measurable (fun x : ℝ ↦ (x, reroot (ω, x))) :=
    measurable_id.prodMk (hr.comp measurable_prodMk_left)
  have hadd : Measurable (fun x : ℝ ↦ a + x) := measurable_const.add measurable_id
  have hloc : Measurable (fun p : ℝ × M ↦ (a + p.1, p.2)) :=
    (measurable_const.add measurable_fst).prodMk measurable_snd
  rw [rootedCampbell_eq_bind P N reroot hr]
  apply measurePreserving_bind_of_covariant P (rootedPointKernel N reroot)
    (Kernel.measurable _) hshift hloc
  filter_upwards [hN, hrcov] with ω hNω hrω
  rw [rootedPointKernel_apply N reroot hr, rootedPointKernel_apply N reroot hr, hNω,
    Measure.map_map (hpoint (shift ω)) hadd, Measure.map_map hloc (hpoint ω)]
  apply Measure.map_congr
  filter_upwards [hrω] with x hx
  exact Prod.ext rfl hx

/-- Factorization of an actual stationary rooted Campbell measure by its unit-window Palm law.
The sole moment assumption is the finite expected number of points in `(0,1]`. -/
theorem rootedCampbell_eq_volume_prod_unitWindowPalm (P : Measure Ω) [SFinite P]
    (N : Kernel Ω ℝ) [IsSFiniteKernel N] (reroot : Ω × ℝ → M) (hr : Measurable reroot)
    (shift : ℝ → Ω → Ω) (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hN : ∀ a, ∀ᵐ ω ∂P, N (shift a ω) = (N ω).map (a + ·))
    (hrcov : ∀ a, ∀ᵐ ω ∂P, ∀ᵐ x ∂N ω,
      reroot (shift a ω, a + x) = reroot (ω, x))
    (hunit : (∫⁻ ω, N ω (Ioc 0 1) ∂P) < ∞) :
    rootedCampbell P N reroot =
      (volume : Measure ℝ).prod (unitWindowPalm (rootedCampbell P N reroot)) := by
  apply campbell_eq_volume_prod_palm
  · intro a
    exact measurePreserving_rootedCampbell_of_covariant P N reroot hr a (hshift a) (hN a)
      (hrcov a)
  · rw [rootedCampbell_apply_prod P N reroot hr measurableSet_Ioc MeasurableSet.univ]
    simpa only [mem_univ, and_true, ofPred_mem_eq] using hunit

/-- Actual random local configurations satisfy Campbell factorization under their counting-measure
covariance and rerooting cocycle. S-finiteness comes from the proved shell decomposition. -/
theorem rootedCampbell_counting_eq_volume_prod_unitWindowPalm {base : ℝ}
    (P : Measure Ω) [SFinite P] (config : Ω → LocalConfiguration base)
    (hc : Measurable config) (reroot : Ω × ℝ → M) (hr : Measurable reroot)
    (shift : ℝ → Ω → Ω) (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hN : ∀ a, ∀ᵐ ω ∂P, LocalConfiguration.countingMeasure (config (shift a ω)) =
      (LocalConfiguration.countingMeasure (config ω)).map (a + ·))
    (hrcov : ∀ a, ∀ᵐ ω ∂P, ∀ᵐ x ∂LocalConfiguration.countingMeasure (config ω),
      reroot (shift a ω, a + x) = reroot (ω, x))
    (hunit : (∫⁻ ω, LocalConfiguration.countingMeasure (config ω) (Ioc 0 1) ∂P) < ∞) :
    rootedCampbell P (LocalConfiguration.randomCountingKernel config hc) reroot =
      (volume : Measure ℝ).prod (unitWindowPalm
        (rootedCampbell P (LocalConfiguration.randomCountingKernel config hc) reroot)) :=
  rootedCampbell_eq_volume_prod_unitWindowPalm P
    (LocalConfiguration.randomCountingKernel config hc) reroot hr shift hshift hN hrcov hunit

end OTSelector.PointProcess
