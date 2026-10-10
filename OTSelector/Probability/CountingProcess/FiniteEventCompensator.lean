import OTSelector.Probability.CountingProcess.FiniteEventIntegral
import OTSelector.Probability.CountingProcess.FiniteEventPredictableMeasure
import OTSelector.Probability.CountingProcess.RectangleExtension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Honest finite-event compensator identities

This file records the measure-theoretic bridge for a finite family of event labels.  The
statements are deliberately phrased as identities for ordinary measures and ordinary
integrals.  In particular, no ``certificate`` or martingale identity is introduced as an
assumption: a martingale conclusion below is obtained only after a set-integral identity has
been supplied.
-/

open Filter Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

set_option linter.style.haveILetI false

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def finiteEventMap {m : Nat}
    (ξ : Fin m → Ω → WithTop NNReal) (i : Fin m) : Ω → NNReal × Ω :=
  fun ω => (WithTop.untopD 0 (ξ i ω), ω)

noncomputable def finiteEventMeasure {m : Nat}
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (ξ : Fin m → Ω → WithTop NNReal) (i : Fin m) (T : NNReal) :
    @Measure (NNReal × Ω) F.predictable :=
  @Measure.map Ω (NNReal × Ω)
    (inferInstance : MeasurableSpace Ω) F.predictable (finiteEventMap ξ i)
    (μ.restrict {ω | ξ i ω ≤ (T : WithTop NNReal)})

private theorem measurable_finiteEventMap
    {m : Nat} (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal) (hξ : ∀ i, IsStoppingTime F (ξ i))
    (i : Fin m) :
    Measurable[‹MeasurableSpace Ω›, F.predictable] (finiteEventMap ξ i) := by
  change Measurable[‹MeasurableSpace Ω›, F.predictable]
    (fun ω => (WithTop.untopD 0 (ξ i ω), ω))
  exact measurable_stoppingTime_untopD_pair_predictable F (hξ i)

/-! ## The jump measure -/

theorem finiteEventJumpMeasure_setIntegral_eq_sum
    {m : Nat} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i)) (T : NNReal)
    {P : Set (NNReal × Ω)} (hP : MeasurableSet[F.predictable] P)
    {G : NNReal × Ω → ℝ}
    (hG : ∀ i : Fin m,
      Integrable G (finiteEventMeasure F μ ξ i T)) :
    (∫ z in P, G z ∂finiteEventJumpMeasure μ F ξ hξ T) =
      ∑ i : Fin m, ∫ ω in (finiteEventMap ξ i ⁻¹' P),
        G (finiteEventMap ξ i ω) ∂(μ.restrict {ω | ξ i ω ≤ (T : WithTop NNReal)}) := by
  classical
  let ν : Fin m → @Measure (NNReal × Ω) F.predictable := fun i =>
    finiteEventMeasure F μ ξ i T
  have hν : finiteEventJumpMeasure μ F ξ hξ T = ∑ i : Fin m, ν i := by
    rfl
  have hG' : ∀ i : Fin m, Integrable G ((ν i).restrict P) := by
    intro i
    exact (hG i).mono_measure Measure.restrict_le_self
  have hGind : ∀ i : Fin m, Integrable (P.indicator G) (ν i) := by
    intro i
    exact (hG i).indicator hP
  have hsum := integral_finsetSum_measure
    (s := (Finset.univ : Finset (Fin m)))
    (f := P.indicator G) (μ := ν) (fun i _ => hGind i)
  change ∫ z, G z ∂(finiteEventJumpMeasure μ F ξ hξ T).restrict P = _
  conv_lhs => rw [← integral_indicator (mX := F.predictable) hP]
  rw [hν]
  rw [hsum]
  simp_rw [integral_indicator (mX := F.predictable) hP]
  apply Finset.sum_congr rfl
  intro i hi
  change (∫ z in P, G z ∂ν i) = _
  change (∫ z in P, G z ∂
      @Measure.map Ω (NNReal × Ω) (inferInstance : MeasurableSpace Ω)
        F.predictable (finiteEventMap ξ i)
        (μ.restrict {ω | ξ i ω ≤ (T : WithTop NNReal)})) = _
  have hφ : @AEMeasurable Ω (NNReal × Ω) F.predictable
      (inferInstance : MeasurableSpace Ω) (finiteEventMap ξ i)
      (μ.restrict {ω | ξ i ω ≤ (T : WithTop NNReal)}) :=
    @Measurable.aemeasurable Ω (NNReal × Ω)
      (inferInstance : MeasurableSpace Ω) F.predictable (finiteEventMap ξ i)
      (μ.restrict {ω | ξ i ω ≤ (T : WithTop NNReal)})
      (measurable_finiteEventMap F ξ hξ i)
  exact @setIntegral_map Ω ℝ (inferInstance : MeasurableSpace Ω) _ _
    (μ.restrict {ω | ξ i ω ≤ (T : WithTop NNReal)})
    (NNReal × Ω) F.predictable (finiteEventMap ξ i) G P hP
    ((hG i).aestronglyMeasurable)
    hφ

theorem finiteEventJumpMeasure_integral_eq_sum
    {m : Nat} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i)) (T : NNReal)
    {G : NNReal × Ω → ℝ}
    (hG : ∀ i : Fin m,
      Integrable G (finiteEventMeasure F μ ξ i T)) :
    (∫ z, G z ∂finiteEventJumpMeasure μ F ξ hξ T) =
      ∑ i : Fin m, ∫ ω in (finiteEventMap ξ i ⁻¹' Set.univ),
        G (finiteEventMap ξ i ω) ∂(μ.restrict {ω | ξ i ω ≤ (T : WithTop NNReal)}) := by
  simpa using
    (finiteEventJumpMeasure_setIntegral_eq_sum μ F ξ hξ T
      (P := Set.univ) MeasurableSet.univ hG)

/-- The same jump-measure identity for a bounded simple predictable transform.  The only
    integrability input needed here is finiteness of the sample measure; boundedness supplies
    integrability on every finite pushforward component. -/
theorem finiteEventJumpMeasure_setIntegral_eq_sum_of_boundedSimplePredictable
    {m : Nat} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i)) (T : NNReal)
    {P : Set (NNReal × Ω)} (hP : MeasurableSet[F.predictable] P)
    {H : NNReal → Ω → ℝ}
    (hH : IsBoundedSimplePredictable F H) :
    (∫ z in P, (fun z => H z.1 z.2) z
        ∂finiteEventJumpMeasure μ F ξ hξ T) =
      ∑ i : Fin m, ∫ ω in (finiteEventMap ξ i ⁻¹' P),
        H (finiteEventMap ξ i ω).1 (finiteEventMap ξ i ω).2
          ∂(μ.restrict {ω | ξ i ω ≤ (T : WithTop NNReal)}) := by
  rcases hH with ⟨hHp, _, C, _, hHC⟩
  apply finiteEventJumpMeasure_setIntegral_eq_sum μ F ξ hξ T hP
  intro i
  let E : Set Ω := {ω | ξ i ω ≤ (T : WithTop NNReal)}
  letI : IsFiniteMeasure (μ.restrict E) :=
    isFiniteMeasure_restrict.mpr (measure_lt_top μ E).ne
  letI : IsFiniteMeasure (finiteEventMeasure F μ ξ i T) := by
    dsimp [finiteEventMeasure]
    exact Measure.isFiniteMeasure_map
      (β := NNReal × Ω) (mβ := F.predictable)
      (μ.restrict E) (finiteEventMap ξ i)
  apply Integrable.of_bound
    ((show StronglyMeasurable[F.predictable] (fun z : NNReal × Ω => H z.1 z.2) from hHp).aestronglyMeasurable)
    C
  exact ae_of_all _ (fun z => by simpa using hHC z.1 z.2)

omit [MeasurableSpace Ω] in
/-- Pathwise increment of the finite-event counting integral.  The endpoint convention is
    `(s,t]`: labels at `s` cancel and labels at `t` remain. -/
theorem countingIntegral_finiteEventCountTop_sub_eq_sum_Ioc
    {m : Nat} (ξ : Fin m → Ω → WithTop NNReal)
    (H : NNReal → Ω → ℝ) (ω : Ω) {s t : NNReal} (hst : s ≤ t)
    (hξ : ∀ j l, ξ j ω ≠ ⊤ → ξ l ω ≠ ⊤ → ξ j ω = ξ l ω → j = l) :
    countingIntegral (fun u ω' => finiteEventCountTop ξ u ω') H t ω -
        countingIntegral (fun u ω' => finiteEventCountTop ξ u ω') H s ω =
      ∑ i : Fin m, if (s : WithTop NNReal) < ξ i ω ∧
          ξ i ω ≤ (t : WithTop NNReal) then
        H (finiteEventTimeValue ξ ω i) ω else 0 := by
  classical
  rw [countingIntegral_finiteEventCountTop_eq_sum ξ H ω t hξ,
    countingIntegral_finiteEventCountTop_eq_sum ξ H ω s hξ]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hti : ξ i ω ≤ (t : WithTop NNReal)
  · by_cases hsi : ξ i ω ≤ (s : WithTop NNReal)
    · have hcond : ¬((s : WithTop NNReal) < ξ i ω ∧
          ξ i ω ≤ (t : WithTop NNReal)) := by
        exact fun h => (not_lt_of_ge hsi) h.1
      rw [ite_eq_left hti, ite_eq_left hsi, ite_eq_right hcond, sub_self]
    · have hcond : (s : WithTop NNReal) < ξ i ω ∧
          ξ i ω ≤ (t : WithTop NNReal) :=
        ⟨lt_of_not_ge hsi, hti⟩
      rw [ite_eq_left hti, ite_eq_right hsi, ite_eq_left hcond, sub_zero]
  · have hsi : ¬ ξ i ω ≤ (s : WithTop NNReal) := by
      intro hsi
      exact hti (hsi.trans (WithTop.coe_le_coe.mpr hst))
    have hcond : ¬((s : WithTop NNReal) < ξ i ω ∧
          ξ i ω ≤ (t : WithTop NNReal)) := fun h => hti h.2
    rw [ite_eq_right hti, ite_eq_right hsi, ite_eq_right hcond]
    ring

/-! ## Fubini on genuine predictable rectangles -/

theorem predictableTimeSampleMeasure_rectangle_setIntegral_eq
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    {s t : NNReal} {B : Set Ω} (hB : MeasurableSet[F s] B)
    {g : NNReal × Ω → ℝ}
    (hg : StronglyMeasurable[F.predictable] g)
    (hgi : Integrable g (timeMeasure.prod μ)) :
    (∫ z in predictableRectangle s t B, g z
        ∂predictableTimeSampleMeasure μ F) =
      ∫ ω in B, ∫ u in Ioc s t, g (u, ω) ∂timeMeasure ∂μ := by
  let P : Set (NNReal × Ω) := predictableRectangle s t B
  letI : SFinite timeMeasure := by
    dsimp [timeMeasure]
    infer_instance
  have hP : MeasurableSet[F.predictable] P := by
    exact measurableSet_predictableRectangle hB
  have hB0 : MeasurableSet B := F.le s B hB
  have hP0 : MeasurableSet[
      (inferInstance : MeasurableSpace NNReal).prod
        (inferInstance : MeasurableSpace Ω)] P := by
    exact (measurableSet_Ioc.prod hB0)
  have htrim := setIntegral_trim (μ := timeMeasure.prod μ)
    (predictable_le_prod F) hg hP
  have hprod := integral_prod_symm (P.indicator g)
    ((hgi.indicator hP0))
  calc
    (∫ z in predictableRectangle s t B, g z
        ∂predictableTimeSampleMeasure μ F) =
        ∫ z in P, g z
          ∂(predictableTimeSampleMeasure μ F) := by rfl
    _ = ∫ z in P, g z ∂(timeMeasure.prod μ) := htrim.symm
    _ = ∫ z, P.indicator g z ∂(timeMeasure.prod μ) :=
      (integral_indicator hP0).symm
    _ = ∫ ω, ∫ u, P.indicator g (u, ω) ∂timeMeasure ∂μ := hprod
    _ = ∫ ω in B, ∫ u in Ioc s t, g (u, ω) ∂timeMeasure ∂μ := by
      rw [← integral_indicator hB0]
      apply integral_congr_ae
      filter_upwards [] with ω
      by_cases hω : ω ∈ B
      · simp only [Set.indicator_of_mem hω]
        have hinner :
            (∫ u, P.indicator g (u, ω) ∂timeMeasure) =
              ∫ u in Ioc s t, g (u, ω) ∂timeMeasure := by
          rw [← integral_indicator measurableSet_Ioc]
          apply integral_congr_ae
          filter_upwards [] with u
          by_cases hu : u ∈ Ioc s t <;>
            simp [P, predictableRectangle, hω, hu]
        exact hinner
      · simp [P, predictableRectangle, hω]

/-! ## Endpoint bookkeeping for an event map -/

omit [MeasurableSpace Ω] in
theorem finiteEventMap_time_eq_finiteEventTimeValue
    {m : Nat} (ξ : Fin m → Ω → WithTop NNReal) (ω : Ω) (i : Fin m)
    (hne : ξ i ω ≠ ⊤) :
    (finiteEventMap ξ i ω).1 = finiteEventTimeValue ξ ω i := by
  apply WithTop.coe_eq_coe.mp
  calc
    ((finiteEventMap ξ i ω).1 : WithTop NNReal) = ξ i ω := by
      exact (WithTop.untopD_eq_iff (d := (0 : NNReal))
        (y := WithTop.untopD 0 (ξ i ω)) (x := ξ i ω)).mp rfl |>.resolve_right
          (fun h => hne h.1) |>.symm
    _ = (finiteEventTimeValue ξ ω i : WithTop NNReal) :=
      (finiteEventTimeValue_coe ξ ω i hne).symm

omit [MeasurableSpace Ω] in
theorem finiteEventMap_preimage_predictableRectangle_eq
    {m : Nat} (ξ : Fin m → Ω → WithTop NNReal) (i : Fin m)
    {s t : NNReal} {B : Set Ω} :
    finiteEventMap ξ i ⁻¹' predictableRectangle s t B =
      B ∩ {ω | (s : WithTop NNReal) < ξ i ω ∧
        ξ i ω ≤ (t : WithTop NNReal)} := by
  ext ω
  constructor
  · intro hω
    change (s < WithTop.untopD 0 (ξ i ω) ∧
        WithTop.untopD 0 (ξ i ω) ≤ t) ∧ ω ∈ B at hω
    have hne : ξ i ω ≠ ⊤ := by
      intro htop
      have hlt : s < (0 : NNReal) := by simpa [htop] using hω.1.1
      exact (not_lt_of_ge bot_le) hlt
    have hcoe : (↑(WithTop.untopD 0 (ξ i ω)) : WithTop NNReal) = ξ i ω := by
      have hc := (WithTop.untopD_eq_iff (d := (0 : NNReal))
        (y := WithTop.untopD 0 (ξ i ω)) (x := ξ i ω)).mp rfl
      exact (hc.resolve_right (fun h => hne h.1)).symm
    have hslt : (s : WithTop NNReal) < ξ i ω := by
      have hslt' : (s : WithTop NNReal) <
          (↑(WithTop.untopD 0 (ξ i ω)) : WithTop NNReal) :=
        (WithTop.coe_lt_coe).mpr hω.1.1
      rwa [hcoe] at hslt'
    have htle : ξ i ω ≤ (t : WithTop NNReal) := by
      have htle' : (↑(WithTop.untopD 0 (ξ i ω)) : WithTop NNReal) ≤
          (t : WithTop NNReal) := (WithTop.coe_le_coe).mpr hω.1.2
      rwa [hcoe] at htle'
    refine ⟨hω.2, ?_⟩
    exact ⟨hslt, htle⟩
  · intro hω
    rcases hω with ⟨hB, hω⟩
    rcases hω with ⟨hslt, htle⟩
    have hne : ξ i ω ≠ ⊤ := by
      intro htop
      apply WithTop.not_top_le_coe t
      rw [← htop]
      exact htle
    have hcoe : (↑(WithTop.untopD 0 (ξ i ω)) : WithTop NNReal) = ξ i ω := by
      have hc := (WithTop.untopD_eq_iff (d := (0 : NNReal))
        (y := WithTop.untopD 0 (ξ i ω)) (x := ξ i ω)).mp rfl
      exact (hc.resolve_right (fun h => hne h.1)).symm
    have hslt' : (s : WithTop NNReal) <
        (↑(WithTop.untopD 0 (ξ i ω)) : WithTop NNReal) := by
      rwa [hcoe]
    have htle' : (↑(WithTop.untopD 0 (ξ i ω)) : WithTop NNReal) ≤
        (t : WithTop NNReal) := by
      rwa [hcoe]
    change (s < WithTop.untopD 0 (ξ i ω) ∧
        WithTop.untopD 0 (ξ i ω) ≤ t) ∧ ω ∈ B
    exact ⟨⟨(WithTop.coe_lt_coe).mp hslt',
      (WithTop.coe_le_coe).mp htle'⟩, hB⟩

/-- The finite-event jump measure evaluated on a predictable rectangle is the expected
    increment of the pathwise counting integral.  This is the endpoint-sensitive bridge used
    below; its proof is only finite-sum bookkeeping plus the map integral formula. -/
theorem finiteEventJumpMeasure_rectangle_setIntegral_eq_countingIncrement
    {m : Nat} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i))
    (hdist : ∀ ω j l, ξ j ω ≠ ⊤ → ξ l ω ≠ ⊤ → ξ j ω = ξ l ω → j = l)
    {s t : NNReal} (hst : s ≤ t)
    {B : Set Ω} (hB : MeasurableSet[F s] B)
    {H : NNReal → Ω → ℝ} (hH : IsBoundedSimplePredictable F H) :
    (∫ z in predictableRectangle s t B,
        H z.1 z.2 ∂finiteEventJumpMeasure μ F ξ hξ t) =
      ∫ ω in B,
        (countingIntegral (fun u ω' => finiteEventCountTop ξ u ω') H t ω -
          countingIntegral (fun u ω' => finiteEventCountTop ξ u ω') H s ω) ∂μ := by
  classical
  let E : Fin m → Set Ω := fun i => {ω | ξ i ω ≤ (t : WithTop NNReal)}
  let Q : Fin m → Set Ω := fun i =>
    finiteEventMap ξ i ⁻¹' predictableRectangle s t B
  let D : Fin m → Set Ω := fun i =>
    {ω | (s : WithTop NNReal) < ξ i ω ∧ ξ i ω ≤ (t : WithTop NNReal)}
  let G : Fin m → Ω → ℝ := fun i ω =>
    H (finiteEventMap ξ i ω).1 (finiteEventMap ξ i ω).2
  let K : Fin m → Ω → ℝ := fun i ω =>
    if ω ∈ D i then H (finiteEventTimeValue ξ ω i) ω else 0
  have hB0 : MeasurableSet B := F.le s B hB
  have hP : MeasurableSet[F.predictable] (predictableRectangle s t B) :=
    measurableSet_predictableRectangle hB
  have hE : ∀ i, MeasurableSet (E i) := by
    intro i
    change MeasurableSet {ω | ξ i ω ≤ (t : WithTop NNReal)}
    exact F.le t _ ((hξ i).measurableSet_le t)
  have hD : ∀ i, MeasurableSet (D i) := by
    intro i
    have hle : MeasurableSet[F s] {ω | ξ i ω ≤ (s : WithTop NNReal)} :=
      (hξ i).measurableSet_le s
    have hltF : MeasurableSet[F s]
        {ω | (s : WithTop NNReal) < ξ i ω} := by
      convert hle.compl using 1
      ext ω
      exact (lt_iff_not_ge :
        ((s : WithTop NNReal) < ξ i ω ↔ ¬ ξ i ω ≤ (s : WithTop NNReal)))
    have hlt : MeasurableSet {ω | (s : WithTop NNReal) < ξ i ω} := by
      exact F.le s _ hltF
    change MeasurableSet
      {ω | (s : WithTop NNReal) < ξ i ω ∧ ξ i ω ≤ (t : WithTop NNReal)}
    exact hlt.inter (hE i)
  have hQ : ∀ i, MeasurableSet (Q i) := by
    intro i
    exact hP.preimage (measurable_finiteEventMap F ξ hξ i)
  have hQeq : ∀ i, Q i = B ∩ D i := by
    intro i
    dsimp [Q, D]
    exact finiteEventMap_preimage_predictableRectangle_eq ξ i
  have hDQ : ∀ i, Q i ⊆ E i := by
    intro i ω hω
    rw [hQeq i] at hω
    exact hω.2.2
  have hGmeasure : ∀ i, Integrable
      (fun z : NNReal × Ω => H z.1 z.2) (finiteEventMeasure F μ ξ i t) := by
    rcases hH with ⟨hHp, _, C, _, hHC⟩
    intro i
    letI : IsFiniteMeasure (μ.restrict (E i)) :=
      isFiniteMeasure_restrict.mpr (measure_lt_top μ (E i)).ne
    letI : IsFiniteMeasure (finiteEventMeasure F μ ξ i t) := by
      dsimp [finiteEventMeasure, E]
      exact Measure.isFiniteMeasure_map
        (β := NNReal × Ω) (mβ := F.predictable)
        (μ.restrict (E i)) (finiteEventMap ξ i)
    apply Integrable.of_bound
      ((show StronglyMeasurable[F.predictable]
        (fun z : NNReal × Ω => H z.1 z.2) from hHp).aestronglyMeasurable) C
    exact ae_of_all _ (fun z => by simpa using hHC z.1 z.2)
  have hjump :
      (∫ z in predictableRectangle s t B,
          H z.1 z.2 ∂finiteEventJumpMeasure μ F ξ hξ t) =
        ∑ i : Fin m, ∫ ω in Q i, G i ω ∂(μ.restrict (E i)) := by
    simpa [Q, G, E] using
      (finiteEventJumpMeasure_setIntegral_eq_sum_of_boundedSimplePredictable
        μ F ξ hξ t hP hH)
  have hGcomp : ∀ i, Integrable (G i) (μ.restrict (E i)) := by
    intro i
    have hφ : @AEMeasurable Ω (NNReal × Ω) F.predictable
        (inferInstance : MeasurableSpace Ω) (finiteEventMap ξ i)
        (μ.restrict (E i)) :=
      @Measurable.aemeasurable Ω (NNReal × Ω)
        (inferInstance : MeasurableSpace Ω) F.predictable (finiteEventMap ξ i)
        (μ.restrict (E i)) (measurable_finiteEventMap F ξ hξ i)
    have hGi : Integrable (fun z : NNReal × Ω => H z.1 z.2)
        (@Measure.map Ω (NNReal × Ω) (inferInstance : MeasurableSpace Ω)
          F.predictable (finiteEventMap ξ i) (μ.restrict (E i))) := by
      simpa [finiteEventMeasure, E] using hGmeasure i
    have hcomp := @Integrable.comp_aemeasurable Ω ℝ
      (inferInstance : MeasurableSpace Ω) (μ.restrict (E i))
      _ _ (NNReal × Ω) F.predictable (finiteEventMap ξ i)
      (fun z : NNReal × Ω => H z.1 z.2) hGi hφ
    simpa [G, E, Function.comp_def] using hcomp
  have hKint : ∀ i, Integrable (K i) μ := by
    intro i
    have hbase : Integrable ((D i).indicator (G i)) μ :=
      (show IntegrableOn (G i) (E i) μ from hGcomp i).mono_set (by
        intro ω hω
        exact hω.2) |>.integrable_indicator (hD i)
    apply hbase.congr
    filter_upwards [] with ω
    by_cases hDω : ω ∈ D i
    · have hne : ξ i ω ≠ ⊤ := by
        intro htop
        apply WithTop.not_top_le_coe t
        rw [← htop]
        exact hDω.2
      have htime := finiteEventMap_time_eq_finiteEventTimeValue ξ ω i hne
      simp only [Set.indicator_of_mem hDω, K, hDω, G]
      change H (finiteEventMap ξ i ω).1 ω =
        H (finiteEventTimeValue ξ ω i) ω
      rw [htime]
    · simp [K, hDω]
  have hterm : ∀ i,
      (∫ ω in Q i, G i ω ∂(μ.restrict (E i))) =
        ∫ ω in B, K i ω ∂μ := by
    intro i
    have hrestrict :
        (μ.restrict (E i)).restrict (Q i) = μ.restrict (Q i) :=
      Measure.restrict_restrict_of_subset (hDQ i)
    have hGtime : ∀ ω, ω ∈ D i →
        G i ω = H (finiteEventTimeValue ξ ω i) ω := by
      intro ω hDω
      have hne : ξ i ω ≠ ⊤ := by
        intro htop
        apply WithTop.not_top_le_coe t
        rw [← htop]
        exact hDω.2
      change H (finiteEventMap ξ i ω).1 ω =
        H (finiteEventTimeValue ξ ω i) ω
      rw [finiteEventMap_time_eq_finiteEventTimeValue ξ ω i hne]
    calc
      (∫ ω in Q i, G i ω ∂(μ.restrict (E i))) =
          ∫ ω in Q i, G i ω ∂μ := by
        rw [hrestrict]
      _ = ∫ ω, (Q i).indicator (G i) ω ∂μ :=
        (integral_indicator (hQ i)).symm
      _ = ∫ ω, B.indicator (K i) ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        by_cases hBω : ω ∈ B <;> by_cases hDω : ω ∈ D i
        · have hQω : ω ∈ Q i := by rw [hQeq i]; exact ⟨hBω, hDω⟩
          simp [hQω, hBω, K, hDω, hGtime ω hDω]
        · have hQω : ω ∉ Q i := by
            rw [hQeq i]
            exact fun h => hDω h.2
          simp [hQω, hBω, K, hDω]
        · have hQω : ω ∉ Q i := by
            rw [hQeq i]
            exact fun h => hBω h.1
          simp [hQω, hBω, K]
        · have hQω : ω ∉ Q i := by
            rw [hQeq i]
            exact fun h => hBω h.1
          simp [hQω, hBω, K]
      _ = ∫ ω in B, K i ω ∂μ := integral_indicator hB0
  have hsum :
      (∑ i : Fin m, ∫ ω in B, K i ω ∂μ) =
        ∫ ω in B, ∑ i : Fin m, K i ω ∂μ := by
    have h := integral_finsetSum (μ := μ.restrict B)
      (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => (hKint i).mono_measure Measure.restrict_le_self)
    simpa using h.symm
  have hpath : ∀ ω,
      (∑ i : Fin m, K i ω) =
        countingIntegral (fun u ω' => finiteEventCountTop ξ u ω') H t ω -
          countingIntegral (fun u ω' => finiteEventCountTop ξ u ω') H s ω := by
    intro ω
    simpa [K, D] using
      (countingIntegral_finiteEventCountTop_sub_eq_sum_Ioc ξ H ω hst (hdist ω)).symm
  calc
    (∫ z in predictableRectangle s t B,
        H z.1 z.2 ∂finiteEventJumpMeasure μ F ξ hξ t) =
        ∑ i : Fin m, ∫ ω in Q i, G i ω ∂(μ.restrict (E i)) := hjump
    _ = ∑ i : Fin m, ∫ ω in B, K i ω ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i
    _ = ∫ ω in B, ∑ i : Fin m, K i ω ∂μ := hsum
    _ = ∫ ω in B,
        (countingIntegral (fun u ω' => finiteEventCountTop ξ u ω') H t ω -
          countingIntegral (fun u ω' => finiteEventCountTop ξ u ω') H s ω) ∂μ := by
      apply setIntegral_congr_fun hB0
      intro ω hω
      simpa using hpath ω

/-- The density formula on a predictable rectangle, followed by product Fubini.  The two
    integrability hypotheses are ordinary measure-theoretic conditions: one makes the density
    identity a Bochner identity on the finite horizon, and the other is the product-Fubini
    condition.  Neither hypothesis mentions a martingale or a compensated transform. -/
theorem finiteHorizonIntensityMeasure_rectangle_setIntegral_eq
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (Λ : NNReal → Ω → ℝ)
    (hΛ : IsStronglyPredictable F Λ)
    (hΛ_nonneg : ∀ u ω, 0 ≤ Λ u ω)
    {s t T : NNReal} (htT : t ≤ T)
    {B : Set Ω} (hB : MeasurableSet[F s] B)
    {H : NNReal → Ω → ℝ} (hH : IsBoundedSimplePredictable F H)
    (hProd : Integrable
      (fun z : NNReal × Ω => Λ z.1 z.2 * H z.1 z.2)
      (timeMeasure.prod μ)) :
    (∫ z in predictableRectangle s t B,
        H z.1 z.2 ∂finiteHorizonIntensityMeasure μ F Λ T) =
      ∫ ω in B, ∫ u in Ioc s t, H u ω * Λ u ω ∂timeMeasure ∂μ := by
  let P : Set (NNReal × Ω) := predictableRectangle s t B
  let R : Set (NNReal × Ω) := Ioc (0 : NNReal) T ×ˢ (univ : Set Ω)
  have hP : MeasurableSet[F.predictable] P := by
    exact measurableSet_predictableRectangle hB
  have hΛp : StronglyMeasurable[F.predictable]
      (fun z : NNReal × Ω => Λ z.1 z.2) := hΛ
  have hHp : StronglyMeasurable[F.predictable]
      (fun z : NNReal × Ω => H z.1 z.2) := hH.1
  have hΛm : Measurable[F.predictable]
      (fun z : NNReal × Ω => Λ z.1 z.2) := hΛp.measurable
  have hρ : Measurable[F.predictable]
      (fun z : NNReal × Ω => ENNReal.ofReal (Λ z.1 z.2)) :=
    hΛm.ennreal_ofReal
  have hρtop : ∀ᵐ z ∂((predictableTimeSampleMeasure μ F).restrict R).restrict P,
      ENNReal.ofReal (Λ z.1 z.2) < ∞ := by
    exact ae_of_all _ (fun z => ENNReal.ofReal_lt_top)
  have hdens0 :
      (∫ z in P, H z.1 z.2 ∂
        ((predictableTimeSampleMeasure μ F).restrict R).withDensity
          (fun z => ENNReal.ofReal (Λ z.1 z.2))) =
      ∫ z in P, (ENNReal.ofReal (Λ z.1 z.2)).toReal • H z.1 z.2
        ∂((predictableTimeSampleMeasure μ F).restrict R) :=
    @setIntegral_withDensity_eq_setIntegral_toReal_smul
      (NNReal × Ω) ℝ F.predictable
      ((predictableTimeSampleMeasure μ F).restrict R) _ _
      (fun z => ENNReal.ofReal (Λ z.1 z.2)) P hρ hρtop
      (fun z => H z.1 z.2) hP
  have hdens :
      (∫ z in P, H z.1 z.2
        ∂finiteHorizonIntensityMeasure μ F Λ T) =
      ∫ z in P, (ENNReal.ofReal (Λ z.1 z.2)).toReal • H z.1 z.2
        ∂((predictableTimeSampleMeasure μ F).restrict R) := by
    simpa [finiteHorizonIntensityMeasure, R] using hdens0
  have hPR : P ⊆ R := by
    intro z hz
    rcases hz with ⟨hzst, hzB⟩
    exact ⟨⟨bot_lt_iff_ne_bot.mpr (ne_of_gt (lt_of_le_of_lt bot_le hzst.1)),
      hzst.2.trans htT⟩, Set.mem_univ _⟩
  have hrestrict :
      ((predictableTimeSampleMeasure μ F).restrict R).restrict P =
        (predictableTimeSampleMeasure μ F).restrict P :=
    Measure.restrict_restrict_of_subset hPR
  have hdens_eq :
      (∫ z in P, (ENNReal.ofReal (Λ z.1 z.2)).toReal • H z.1 z.2
        ∂((predictableTimeSampleMeasure μ F).restrict R)) =
      ∫ z in P, Λ z.1 z.2 * H z.1 z.2
        ∂predictableTimeSampleMeasure μ F := by
    rw [show (∫ z in P, (ENNReal.ofReal (Λ z.1 z.2)).toReal • H z.1 z.2
          ∂((predictableTimeSampleMeasure μ F).restrict R)) =
        ∫ z in P, (ENNReal.ofReal (Λ z.1 z.2)).toReal • H z.1 z.2
          ∂((predictableTimeSampleMeasure μ F).restrict R) from rfl]
    rw [hrestrict]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [ENNReal.toReal_ofReal (hΛ_nonneg z.1 z.2), smul_eq_mul]
  have hprodstrong : StronglyMeasurable[F.predictable]
      (fun z : NNReal × Ω => Λ z.1 z.2 * H z.1 z.2) := hΛp.mul hHp
  calc
    (∫ z in predictableRectangle s t B,
        H z.1 z.2 ∂finiteHorizonIntensityMeasure μ F Λ T) =
      ∫ z in P, H z.1 z.2
        ∂finiteHorizonIntensityMeasure μ F Λ T := by rfl
    _ = ∫ z in P, (ENNReal.ofReal (Λ z.1 z.2)).toReal • H z.1 z.2
        ∂((predictableTimeSampleMeasure μ F).restrict R) := hdens
    _ = ∫ z in P, Λ z.1 z.2 * H z.1 z.2
        ∂predictableTimeSampleMeasure μ F := hdens_eq
    _ = ∫ ω in B, ∫ u in Ioc s t, Λ u ω * H u ω ∂timeMeasure ∂μ := by
      exact predictableTimeSampleMeasure_rectangle_setIntegral_eq μ F hB hprodstrong hProd
    _ = ∫ ω in B, ∫ u in Ioc s t, H u ω * Λ u ω ∂timeMeasure ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      apply integral_congr_ae
      filter_upwards [] with u
      rw [mul_comm]

/-! ## The intensity measure -/

set_option linter.unusedVariables false in
theorem finiteHorizonIntensityMeasure_setIntegral_eq_withDensity
    (μ : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (Λ : NNReal → Ω → ℝ) (hΛ : Measurable[F.predictable]
      (fun z : NNReal × Ω => Λ z.1 z.2)) (T : NNReal)
    {P : Set (NNReal × Ω)} (hP : MeasurableSet[F.predictable] P)
    {G : NNReal × Ω → ℝ}
    (hG : Integrable G
      ((predictableTimeSampleMeasure μ F).restrict
        (Ioc (0 : NNReal) T ×ˢ (univ : Set Ω)))) :
    (∫ z in P, G z ∂finiteHorizonIntensityMeasure μ F Λ T) =
      ∫ z in P, (ENNReal.ofReal (Λ z.1 z.2)).toReal • G z
        ∂((predictableTimeSampleMeasure μ F).restrict
          (Ioc (0 : NNReal) T ×ˢ (univ : Set Ω))) := by
  let R : Set (NNReal × Ω) := Ioc (0 : NNReal) T ×ˢ (univ : Set Ω)
  let ν : @Measure (NNReal × Ω) F.predictable := predictableTimeSampleMeasure μ F
  have hρ : Measurable[F.predictable]
      (fun z : NNReal × Ω => ENNReal.ofReal (Λ z.1 z.2)) := by
    exact hΛ.ennreal_ofReal
  have hρtop : ∀ᵐ z ∂(ν.restrict R).restrict P,
      ENNReal.ofReal (Λ z.1 z.2) < ∞ := by
    exact ae_of_all _ (fun z => ENNReal.ofReal_lt_top)
  have hmain :
      (∫ z in P, G z ∂(ν.restrict R).withDensity
        (fun z => ENNReal.ofReal (Λ z.1 z.2))) =
        ∫ z in P, (ENNReal.ofReal (Λ z.1 z.2)).toReal • G z ∂(ν.restrict R) :=
    @setIntegral_withDensity_eq_setIntegral_toReal_smul
      (NNReal × Ω) ℝ F.predictable
      (ν.restrict R) _ _ (fun z => ENNReal.ofReal (Λ z.1 z.2)) P
      hρ hρtop G hP
  simpa [finiteHorizonIntensityMeasure, R, ν] using hmain

end OTSelector.CountingProcess
