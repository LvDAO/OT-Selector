import OTSelector.Probability.CountingProcess.FiniteEventIntegral
import OTSelector.Probability.CountingProcess.Closure

/-!
# Side conditions for the finite-event intensity bridge

This file supplies the ordinary measurability and integrability facts needed by
`hasPredictableIntensity_of_finiteEvent_rectangle_measures`.  No martingale,
intensity, or rectangle identity is used here.

The counting-integral statements use the finite-label representation of a
finite-event path.  The accumulated-intensity statements use the predictable
sigma-algebra only; the fixed-time integral is measurable at the current
filtration level because a predictable set restricted to `Iic t` is measurable
for the product of time and `F t`.
-/

open Filter Set
open MeasureTheory
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory Topology

namespace OTSelector.CountingProcess

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Counting-integral side conditions -/

private theorem stronglyMeasurable_finiteEventTerm
    {m : Nat} (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i))
    {H : NNReal → Ω → ℝ} (hH : IsBoundedSimplePredictable F H)
    (i : Fin m) (t : NNReal) :
    StronglyMeasurable[F t]
      (fun ω => if ξ i ω ≤ (t : WithTop NNReal) then
        H (finiteEventTimeValue ξ ω i) ω else 0) := by
  let τ : Ω → WithTop NNReal := ξ i
  let U : NNReal → Ω → ℝ := fun s ω => H s ω
  have hprog : IsStronglyProgressive F U := hH.1.isStronglyProgressive
  have hstop : StronglyAdapted F (MeasureTheory.stoppedProcess U τ) :=
    hprog.stronglyAdapted_stoppedProcess (hξ i)
  have hstopt : StronglyMeasurable[F t] (MeasureTheory.stoppedProcess U τ t) :=
    hstop t
  have hE : MeasurableSet[F t] {ω | τ ω ≤ (t : WithTop NNReal)} :=
    (hξ i).measurableSet_le t
  have hterm : StronglyMeasurable[F t]
      ({ω | τ ω ≤ (t : WithTop NNReal)}.indicator
        (MeasureTheory.stoppedProcess U τ t)) :=
    hstopt.indicator hE
  have heq : {ω | τ ω ≤ (t : WithTop NNReal)}.indicator
      (MeasureTheory.stoppedProcess U τ t) =
      (fun ω => if ξ i ω ≤ (t : WithTop NNReal) then
        H (finiteEventTimeValue ξ ω i) ω else 0) := by
    funext ω
    by_cases hω : τ ω ≤ (t : WithTop NNReal)
    · have hne : τ ω ≠ ⊤ := by
        intro htop
        rw [htop] at hω
        exact (WithTop.not_top_le_coe t) hω
      have hcoe : (finiteEventTimeValue ξ ω i : WithTop NNReal) = τ ω := by
        simpa [τ] using finiteEventTimeValue_coe ξ ω i hne
      have hstop_eq : MeasureTheory.stoppedProcess U τ t ω = H
          (finiteEventTimeValue ξ ω i) ω := by
        change H (min (t : WithTop NNReal) (τ ω)).untopA ω = _
        have hmin : min (t : WithTop NNReal) (τ ω) = τ ω :=
          min_eq_right hω
        rw [hmin]
        rw [WithTop.untopA_eq_untop hne]
        have hval : (τ ω).untop hne = finiteEventTimeValue ξ ω i :=
          (WithTop.untop_eq_iff hne).2 hcoe.symm
        exact congrArg (fun q => H q ω) hval
      simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_left hω]
      rw [ite_eq_left (show ξ i ω ≤ (t : WithTop NNReal) by simpa [τ] using hω)]
      exact hstop_eq
    · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_right hω]
      rw [ite_eq_right (show ¬ξ i ω ≤ (t : WithTop NNReal) by simpa [τ] using hω)]
  rw [← heq]
  exact hterm

theorem finiteEvent_countingIntegral_stronglyAdapted
    {m : Nat} (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i))
    (hdist : ∀ ω j l, ξ j ω ≠ ⊤ → ξ l ω ≠ ⊤ → ξ j ω = ξ l ω → j = l)
    {H : NNReal → Ω → ℝ} (hH : IsBoundedSimplePredictable F H) :
    StronglyAdapted F
      (fun t ω => countingIntegral
        (fun u ω' => finiteEventCountTop ξ u ω') H t ω) := by
  intro t
  have hterm : ∀ i : Fin m, StronglyMeasurable[F t]
      (fun ω => if ξ i ω ≤ (t : WithTop NNReal) then
        H (finiteEventTimeValue ξ ω i) ω else 0) := by
    intro i
    exact stronglyMeasurable_finiteEventTerm F ξ hξ hH i t
  have hsum : StronglyMeasurable[F t]
      (fun ω => ∑ i : Fin m, if ξ i ω ≤ (t : WithTop NNReal) then
        H (finiteEventTimeValue ξ ω i) ω else 0) := by
    have hsum' := Finset.stronglyMeasurable_sum Finset.univ (fun i _ => hterm i)
    convert hsum' using 1
    funext ω
    simp only [Finset.sum_apply]
  have heq : (fun ω => ∑ i : Fin m, if ξ i ω ≤ (t : WithTop NNReal) then
      H (finiteEventTimeValue ξ ω i) ω else 0) =
      (fun ω => countingIntegral
        (fun u ω' => finiteEventCountTop ξ u ω') H t ω) := by
    funext ω
    exact (countingIntegral_finiteEventCountTop_eq_sum ξ H ω t (hdist ω)).symm
  simpa using heq ▸ hsum

theorem finiteEvent_countingIntegral_integrable
    {m : Nat} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i))
    (hdist : ∀ ω j l, ξ j ω ≠ ⊤ → ξ l ω ≠ ⊤ → ξ j ω = ξ l ω → j = l)
    {H : NNReal → Ω → ℝ} (hH : IsBoundedSimplePredictable F H) :
    ∀ t, Integrable
      (fun ω => countingIntegral
        (fun u ω' => finiteEventCountTop ξ u ω') H t ω) μ := by
  intro t
  have hstrong : StronglyMeasurable[F t]
      (fun ω => countingIntegral
        (fun u ω' => finiteEventCountTop ξ u ω') H t ω) :=
    finiteEvent_countingIntegral_stronglyAdapted F ξ hξ hdist hH t
  have hstrong' : AEStronglyMeasurable
      (fun ω => countingIntegral
        (fun u ω' => finiteEventCountTop ξ u ω') H t ω) μ :=
    (hstrong.mono (F.le t)).measurable.aestronglyMeasurable
  rcases hH with ⟨_, _, C, hC, hHbound⟩
  refine Integrable.of_bound hstrong' (C * (m : ℝ)) ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  rw [countingIntegral_finiteEventCountTop_eq_sum ξ H ω t (hdist ω)]
  calc
    |∑ i : Fin m, if ξ i ω ≤ (t : WithTop NNReal) then
        H (finiteEventTimeValue ξ ω i) ω else 0| ≤
        ∑ i : Fin m, |if ξ i ω ≤ (t : WithTop NNReal) then
          H (finiteEventTimeValue ξ ω i) ω else 0| :=
      Finset.abs_sum_le_sum_abs (fun i : Fin m =>
        if ξ i ω ≤ (t : WithTop NNReal) then
          H (finiteEventTimeValue ξ ω i) ω else 0) Finset.univ
    _ ≤ ∑ _i : Fin m, C := by
      refine Finset.sum_le_sum ?_
      intro i hi
      by_cases hω : ξ i ω ≤ (t : WithTop NNReal)
      · simp only [ite_eq_left hω]
        exact hHbound _ _
      · simp only [ite_eq_right hω, abs_zero]
        exact hC
    _ = C * (m : ℝ) := by
      simp [nsmul_eq_mul, mul_comm]

/-! ## Product and path integrability of the accumulated intensity -/

theorem finiteEvent_pathProduct_integrable_of_bounded
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    {Λ H : NNReal → Ω → ℝ}
    (_hΛ : IsStronglyPredictable F Λ)
    (hΛ_nonneg : ∀ u ω, 0 ≤ Λ u ω)
    (hΛ_int : ∀ t ω, IntegrableOn (fun s => Λ s ω)
      (Ioc (0 : NNReal) t) timeMeasure)
    {C : ℝ} (_hC : 0 ≤ C)
    (hH : IsBoundedSimplePredictable F H)
    (hHbound : ∀ t ω, |H t ω| ≤ C) :
    ∀ t ω, IntegrableOn (fun s => H s ω * Λ s ω)
      (Ioc (0 : NNReal) t) timeMeasure := by
  intro t ω
  let μt : Measure NNReal := timeMeasure.restrict (Ioc (0 : NNReal) t)
  have hHsec : StronglyMeasurable (fun s : NNReal => H s ω) := by
    have hHp : StronglyMeasurable[Prod.instMeasurableSpace]
        (Function.uncurry H) :=
      hH.1.mono (predictable_le_ambient F)
    have hg : Measurable (fun s : NNReal => (s, ω) : NNReal → NNReal × Ω) :=
      measurable_id.prodMk measurable_const
    exact (hHp.measurable.comp hg).stronglyMeasurable
  have hΛsec : AEStronglyMeasurable (fun s : NNReal => Λ s ω) μt :=
    (hΛ_int t ω).aestronglyMeasurable
  have hprodmeas : AEStronglyMeasurable
      (fun s : NNReal => H s ω * Λ s ω) μt :=
    hHsec.aestronglyMeasurable.mul hΛsec
  have hbound : ∀ᵐ s ∂μt, ‖H s ω * Λ s ω‖ ≤ C * Λ s ω := by
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΛ_nonneg s ω)]
    exact mul_le_mul_of_nonneg_right (hHbound s ω) (hΛ_nonneg s ω)
  have hdom : Integrable (fun s : NNReal => C * Λ s ω) μt :=
    (hΛ_int t ω).const_mul C
  have hp : Integrable (fun s : NNReal => H s ω * Λ s ω) μt :=
    Integrable.mono' hdom hprodmeas hbound
  simpa [IntegrableOn, μt] using hp

/-! A global product hypothesis can be obtained from global integrability of the
rate and a deterministic bound on the predictable transform.  This is kept
separate from the local pathwise lemma above: `timeMeasure` is infinite on the
whole half-line, so local pathwise integrability alone cannot imply this
global product statement. -/

theorem finiteEvent_product_integrable_of_global_rate_integrable
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    {Λ H : NNReal → Ω → ℝ}
    (hΛprod : Integrable
      (fun z : NNReal × Ω => Λ z.1 z.2)
      (timeMeasure.prod μ))
    {C : ℝ} (hC : 0 ≤ C)
    (hH : IsBoundedSimplePredictable F H)
    (hHbound : ∀ t ω, |H t ω| ≤ C)
    (hΛ_nonneg : ∀ t ω, 0 ≤ Λ t ω) :
    Integrable
      (fun z : NNReal × Ω => Λ z.1 z.2 * H z.1 z.2)
      (timeMeasure.prod μ) := by
  have hHp : StronglyMeasurable[Prod.instMeasurableSpace]
      (Function.uncurry H) :=
    hH.1.mono (predictable_le_ambient F)
  have hmeas : AEStronglyMeasurable
      (fun z : NNReal × Ω => Λ z.1 z.2 * H z.1 z.2)
      (timeMeasure.prod μ) := by
    exact hΛprod.aestronglyMeasurable.mul hHp.aestronglyMeasurable
  have hdom : Integrable
      (fun z : NNReal × Ω => |C| * Λ z.1 z.2)
      (timeMeasure.prod μ) := hΛprod.const_mul |C|
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΛ_nonneg z.1 z.2)]
  calc
    Λ z.1 z.2 * |H z.1 z.2| ≤ Λ z.1 z.2 * C := by
      exact mul_le_mul_of_nonneg_left
        (hHbound z.1 z.2) (hΛ_nonneg z.1 z.2)
    _ = |C| * Λ z.1 z.2 := by
      rw [abs_of_nonneg hC]
      ring

/-! ## Accumulated-intensity adaptation and integrability -/

private theorem stronglyMeasurable_integratedIntensity_at
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    {Λ H : NNReal → Ω → ℝ}
    (hG : IsStronglyPredictable F (fun s ω => H s ω * Λ s ω))
    (_hPath : ∀ t ω, IntegrableOn (fun s => H s ω * Λ s ω)
      (Ioc (0 : NNReal) t) timeMeasure)
    (t : NNReal) :
    StronglyMeasurable[F t]
      (fun ω => integratedIntensity Λ H t ω) := by
  let mprod : MeasurableSpace (Set.Iic t × Ω) :=
    Subtype.instMeasurableSpace.prod (F t)
  let incl : Set.Iic t × Ω → NNReal × Ω := fun p => (p.1, p.2)
  let gsub : Set.Iic t × Ω → ℝ := fun p => H p.1 p.2 * Λ p.1 p.2
  have hincl : Measurable[mprod, F.predictable] incl := by
    exact measurable_inclusion_predictable (𝓕 := F) (i := t)
  have hGsub : StronglyMeasurable[mprod]
      gsub := by
    change StronglyMeasurable[mprod]
      ((Function.uncurry (fun s ω => H s ω * Λ s ω)) ∘ incl)
    exact hG.comp_measurable hincl
  let S : Set (NNReal × Ω) := Iic t ×ˢ (univ : Set Ω)
  have hS : MeasurableSet[(inferInstance : MeasurableSpace NNReal).prod (F t)] S := by
    exact measurableSet_Iic.prod MeasurableSet.univ
  have hemb : @MeasurableEmbedding (Set.Iic t × Ω) (NNReal × Ω)
      (Subtype.instMeasurableSpace.prod (F t))
      ((inferInstance : MeasurableSpace NNReal).prod (F t))
      incl := by
    dsimp [incl]
    exact (MeasurableEmbedding.subtype_coe (s := Set.Iic t) measurableSet_Iic).prodMap
      MeasurableEmbedding.id
  have hinj : Function.Injective incl :=
    @MeasurableEmbedding.injective (Set.Iic t × Ω) (NNReal × Ω)
      (Subtype.instMeasurableSpace.prod (F t))
      ((inferInstance : MeasurableSpace NNReal).prod (F t))
      incl hemb
  have hGext : StronglyMeasurable[
      (inferInstance : MeasurableSpace NNReal).prod (F t)]
      (Function.extend incl gsub (fun _ : NNReal × Ω => (0 : ℝ))) := by
    exact hemb.stronglyMeasurable_extend hGsub stronglyMeasurable_const
  let g : NNReal × Ω → ℝ := fun z =>
    (Ioc (0 : NNReal) t ×ˢ (univ : Set Ω)).indicator
      (Function.extend incl gsub (fun _ : NNReal × Ω => (0 : ℝ))) z
  have hg : StronglyMeasurable[
      (inferInstance : MeasurableSpace NNReal).prod (F t)] g := by
    exact hGext.indicator (measurableSet_Ioc.prod MeasurableSet.univ)
  let htimeSFinite : SFinite timeMeasure := by
    unfold timeMeasure
    infer_instance
  have hint : StronglyMeasurable[F t]
      (fun ω => ∫ s, g (s, ω) ∂timeMeasure) := by
    exact @MeasureTheory.StronglyMeasurable.integral_prod_left'
      NNReal Ω ℝ (inferInstance : MeasurableSpace NNReal) (F t)
      timeMeasure _ _ htimeSFinite g hg
  have heq : (fun ω => ∫ s, g (s, ω) ∂timeMeasure) =
      (fun ω => integratedIntensity Λ H t ω) := by
    funext ω
    have hsection : (fun s => g (s, ω)) =
        (Ioc (0 : NNReal) t).indicator (fun u => H u ω * Λ u ω) := by
      funext s
      by_cases hs : s ∈ Ioc (0 : NNReal) t
      · have hext : Function.extend incl gsub
            (fun _ : NNReal × Ω => (0 : ℝ)) (s, ω) =
            H s ω * Λ s ω := by
          have h := hinj.extend_apply gsub
            (fun _ : NNReal × Ω => (0 : ℝ)) (⟨⟨s, hs.2⟩, ω⟩)
          simpa only [incl] using h
        simp [g, hs, hext]
      · simp [g, hs]
    rw [hsection, integral_indicator measurableSet_Ioc]
    change (∫ s in Ioc (0 : NNReal) t, H s ω * Λ s ω ∂timeMeasure) = _
    rfl
  rw [← heq]
  exact hint

theorem finiteEvent_integratedIntensity_stronglyAdapted
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    {Λ H : NNReal → Ω → ℝ}
    (hΛ : IsStronglyPredictable F Λ)
    (hH : IsBoundedSimplePredictable F H)
    (hPath : ∀ t ω, IntegrableOn (fun s => H s ω * Λ s ω)
      (Ioc (0 : NNReal) t) timeMeasure) :
    StronglyAdapted F (fun t ω => integratedIntensity Λ H t ω) := by
  intro t
  exact stronglyMeasurable_integratedIntensity_at F
    (hH.1.mul hΛ) hPath t

theorem finiteEvent_integratedIntensity_integrable
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    {Λ H : NNReal → Ω → ℝ}
    (_hΛ : IsStronglyPredictable F Λ)
    (_hH : IsBoundedSimplePredictable F H)
    (hProd : Integrable
      (fun z : NNReal × Ω => Λ z.1 z.2 * H z.1 z.2)
      (timeMeasure.prod μ)) :
    ∀ t, Integrable (integratedIntensity Λ H t) μ := by
  intro t
  let g : NNReal × Ω → ℝ := fun z => Λ z.1 z.2 * H z.1 z.2
  let S : Set (NNReal × Ω) := Ioc (0 : NNReal) t ×ˢ (univ : Set Ω)
  have hS : MeasurableSet S := measurableSet_Ioc.prod MeasurableSet.univ
  have hg : Integrable (S.indicator g) (timeMeasure.prod μ) :=
    hProd.indicator hS
  let htimeSFinite : SFinite timeMeasure := by
    unfold timeMeasure
    infer_instance
  have hinner : Integrable
      (fun ω => ∫ s, S.indicator g (s, ω) ∂timeMeasure) μ :=
    @Integrable.integral_prod_right NNReal Ω ℝ
      (inferInstance : MeasurableSpace NNReal) (inferInstance : MeasurableSpace Ω)
      timeMeasure μ _ _ _ htimeSFinite (S.indicator g) hg
  have heq : (fun ω => ∫ s, S.indicator g (s, ω) ∂timeMeasure) =
      integratedIntensity Λ H t := by
    funext ω
    have hsection : (fun s => S.indicator g (s, ω)) =
        (Ioc (0 : NNReal) t).indicator
          (fun s => Λ s ω * H s ω) := by
      funext s
      by_cases hs : s ∈ Ioc (0 : NNReal) t <;> simp [S, g, hs]
    rw [hsection, integral_indicator measurableSet_Ioc]
    change (∫ s in Ioc (0 : NNReal) t, Λ s ω * H s ω ∂timeMeasure) = _
    simp only [integratedIntensity]
    congr 1
    funext s
    ring
  rw [← heq]
  exact hinner

/-! ## Bundles for the generic rectangle-to-intensity theorem -/

theorem finiteEvent_countingIntegral_sideConditions
    {m : Nat} (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ξ : Fin m → Ω → WithTop NNReal)
    (hξ : ∀ i, IsStoppingTime F (ξ i))
    (hdist : ∀ ω j l, ξ j ω ≠ ⊤ → ξ l ω ≠ ⊤ → ξ j ω = ξ l ω → j = l)
    {H : NNReal → Ω → ℝ} (hH : IsBoundedSimplePredictable F H) :
    StronglyAdapted F
      (fun t ω => countingIntegral
        (fun u ω' => finiteEventCountTop ξ u ω') H t ω) ∧
      (∀ t, Integrable
        (fun ω => countingIntegral
          (fun u ω' => finiteEventCountTop ξ u ω') H t ω) μ) := by
  exact ⟨finiteEvent_countingIntegral_stronglyAdapted F ξ hξ hdist hH,
    finiteEvent_countingIntegral_integrable μ F ξ hξ hdist hH⟩

theorem finiteEvent_integratedIntensity_sideConditions
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    {Λ H : NNReal → Ω → ℝ}
    (hΛ : IsStronglyPredictable F Λ)
    (hH : IsBoundedSimplePredictable F H)
    (hPath : ∀ t ω, IntegrableOn (fun s => H s ω * Λ s ω)
      (Ioc (0 : NNReal) t) timeMeasure)
    (hProd : Integrable
      (fun z : NNReal × Ω => Λ z.1 z.2 * H z.1 z.2)
      (timeMeasure.prod μ)) :
    StronglyAdapted F (fun t ω => integratedIntensity Λ H t ω) ∧
      (∀ t, Integrable (integratedIntensity Λ H t) μ) := by
  exact ⟨finiteEvent_integratedIntensity_stronglyAdapted F hΛ hH hPath,
    finiteEvent_integratedIntensity_integrable μ F hΛ hH hProd⟩

end OTSelector.CountingProcess
